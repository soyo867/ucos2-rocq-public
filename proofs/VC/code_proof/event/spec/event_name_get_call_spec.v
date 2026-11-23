Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.VC.code.event.spec.event_name_get_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
(* Bind the external declaration to the current checked source proof, including
   its general modulo result and the derived old bounded contract. *)
Require Import Ucos2Verify.VC.code.core.OS_StrLen_goal_check.

Import UCOS2_C_Rules ListNotations.
Import KernelHeapStorage KernelHeapObservation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Public ordered guards. Neither the cold branches nor an unsupported type
    dereference the output pointer. Its cell is borrowed only on success. *)
Definition event_name_get_after_type (name_addr pname name : addr)
  (type_byte output_old : Z) (chars : list Z) : Assertion :=
  if event_name_type_allowed type_byte
  then event_name_get_success_focus name_addr pname name output_old chars
  else emp.

Definition event_name_get_access (pevent pname type_addr name_addr name : addr)
  (nesting type_byte output_old : Z) (chars : list Z) : Assertion :=
  if Z.eqb pevent 0 then emp else
  if Z.eqb pname 0 then emp else
  if Z.ltb 0 nesting then emp else
  type_addr # UChar |-> type_byte **
    event_name_get_after_type name_addr pname name type_byte output_old chars.

Definition event_name_get_request (names : NameResourceState)
  (pevent pname nesting type_byte name : Z) (chars : list Z) : Prop :=
  event_name_get_error pevent pname nesting type_byte = None ->
  event_name_get_readable names name chars.

Definition event_name_get_final_output
  (pevent pname nesting type_byte name output_old : Z) : Z :=
  match event_name_get_error pevent pname nesting type_byte with
  | Some _ => output_old
  | None => name
  end.

Definition event_name_get_output (pevent pname nesting type_byte name : Z)
  : option addr :=
  match event_name_get_error pevent pname nesting type_byte with
  | Some _ => None
  | None => Some name
  end.

Lemma event_name_get_type_allowed_range : forall ty,
  event_name_type_allowed ty = true <-> 1 <= ty <= 4.
Proof.
  intros; unfold event_name_type_allowed; cbn [encode_event_type].
  rewrite !orb_true_iff, !Z.eqb_eq; lia.
Qed.

(** This is a restriction of the existing byte map, not another owner. The
    removed interval is lent to the checked StrLen loop and then rejoined. *)
Definition event_name_get_remove_byte (bytes : addr -> option Z) (p : addr)
  : addr -> option Z := fun q => if Z.eqb q p then None else bytes q.

Fixpoint event_name_get_remove_bytes (bytes : addr -> option Z)
  (p : addr) (count : nat) : addr -> option Z :=
  match count with
  | O => bytes
  | S rest => event_name_get_remove_bytes (event_name_get_remove_byte bytes p) (p + 1) rest
  end.

Definition event_name_get_name_residual (names : NameResourceState)
  (p : addr) (chars : list Z) : Assertion :=
  store_map name_byte_rep
    (event_name_get_remove_bytes names.(nameBytes) p (S (List.length chars))).

Lemma event_name_get_missing_byte_eq : forall bytes p,
  store_map_missing_i name_byte_rep bytes p --||--
  store_map name_byte_rep (event_name_get_remove_byte bytes p).
Proof.
  intros bytes p.
  assert (Houtside : forall q, q <> p -> bytes q = event_name_get_remove_byte bytes p q).
  { intros q Hq; unfold event_name_get_remove_byte.
    rewrite (proj2 (Z.eqb_neq q p) Hq); reflexivity. }
  assert (Hnone : event_name_get_remove_byte bytes p p = None).
  { unfold event_name_get_remove_byte; rewrite Z.eqb_refl; reflexivity. }
  split.
  - rewrite (store_map_missing_i_equiv name_byte_rep bytes
      (event_name_get_remove_byte bytes p) p Houtside).
    apply store_map_missing_equiv_store_map; exact Hnone.
  - eapply derivable1_trans; [apply store_map_equiv_store_map_missing; exact Hnone|].
    apply (proj2 (store_map_missing_i_equiv name_byte_rep bytes
      (event_name_get_remove_byte bytes p) p Houtside)).
Qed.

Lemma event_name_get_byte_split : forall bytes p value,
  bytes p = Some value ->
  store_map name_byte_rep bytes --||--
    p # UChar |-> value ** store_map name_byte_rep (event_name_get_remove_byte bytes p).
Proof.
  intros bytes p value Hbyte; rewrite <- event_name_get_missing_byte_eq.
  split.
  - sep_apply_l_atomic (store_map_split name_byte_rep p value bytes Hbyte).
    unfold name_byte_rep; entailer!.
  - unfold name_byte_rep in *.
    sep_apply_l_atomic (store_map_merge (fun q b => q # UChar |-> b) p value bytes Hbyte).
    entailer!.
Qed.

Lemma event_name_get_array_split : forall values bytes base lo,
  (forall i c, nth_error values i = Some c -> bytes (base + lo + Z.of_nat i) = Some c) ->
  store_map name_byte_rep bytes --||--
    UCharArray.seg base lo (lo + Zlength values) values **
    store_map name_byte_rep (event_name_get_remove_bytes bytes (base + lo) (List.length values)).
Proof.
  induction values as [|value values IH]; intros bytes base lo Hbytes.
  - cbn [List.length event_name_get_remove_bytes].
    change (Zlength (@nil Z)) with 0; rewrite Z.add_0_r, UCharArray.seg_empty.
    split; entailer!.
  - assert (Hhead : bytes (base + lo) = Some value).
    { specialize (Hbytes O value eq_refl); cbn in Hbytes; rewrite Z.add_0_r in Hbytes; exact Hbytes. }
    assert (Htail : forall i c, nth_error values i = Some c ->
      event_name_get_remove_byte bytes (base + lo) (base + (lo + 1) + Z.of_nat i) = Some c).
    { intros i c Hi; unfold event_name_get_remove_byte.
      rewrite (proj2 (Z.eqb_neq (base + (lo + 1) + Z.of_nat i) (base + lo)) ltac:(lia)).
      replace (base + (lo + 1) + Z.of_nat i) with (base + lo + Z.of_nat (S i)) by lia.
      apply Hbytes; exact Hi. }
    rewrite (event_name_get_byte_split bytes (base + lo) value Hhead).
    rewrite (IH (event_name_get_remove_byte bytes (base + lo)) base (lo + 1) Htail).
    rewrite UCharArray.seg_unfold.
    cbn [List.length event_name_get_remove_bytes].
    rewrite Zlength_cons.
    replace (Z.succ (Zlength values)) with (Zlength values + 1) by lia.
    replace (lo + (Zlength values + 1)) with (lo + 1 + Zlength values) by lia.
    replace (base + lo + 1) with (base + (lo + 1)) by lia.
    change (sizeof(UCHAR)) with 1; rewrite Z.mul_1_r.
    split; entailer!.
Qed.

Lemma event_name_get_readable_source : forall names p chars,
  readable_name names p chars ->
  forall i c, nth_error (chars ++ [0]) i = Some c ->
    names.(nameBytes) (p + Z.of_nat i) = Some c.
Proof.
  intros names p chars [_ [Hchars Hnul]] i c Hi.
  destruct (lt_dec i (List.length chars)) as [Hlt|Hge].
  - rewrite nth_error_app1 in Hi by exact Hlt; apply Hchars; exact Hi.
  - rewrite nth_error_app2 in Hi by lia.
    destruct (i - List.length chars)%nat eqn:Hdiff; [|destruct n; discriminate].
    cbn in Hi; inversion Hi; subst c.
    assert (i = List.length chars) by lia; subst i; exact Hnul.
Qed.

Lemma event_name_get_name_split : forall names p chars,
  readable_name names p chars ->
  store_name_bytes names --||-- os_strlen_bytes p chars **
    event_name_get_name_residual names p chars.
Proof.
  intros names p chars Hread; unfold store_name_bytes, os_strlen_bytes, event_name_get_name_residual.
  rewrite (event_name_get_array_split (chars ++ [0]) names.(nameBytes) p 0).
  - unfold UCharArray.full, store_array, UCharArray.seg.
    rewrite Z.add_0_r, app_length; cbn [List.length].
    replace (List.length chars + 1)%nat with (S (List.length chars)) by lia.
    rewrite Z.add_0_l, Zlength_app_cons, Zlength_correct.
    replace (Z.of_nat (List.length chars) + 1) with (Z.of_nat (S (List.length chars))) by lia.
    split; reflexivity.
  - intros i c Hi; rewrite Z.add_0_r; eapply event_name_get_readable_source; eassumption.
Qed.

Lemma event_name_get_access_type_split :
  forall pevent pname type_addr name_addr name nesting ty output_old chars,
  pevent <> 0 -> pname <> 0 -> nesting <= 0 ->
  event_name_get_access pevent pname type_addr name_addr name nesting ty output_old chars
  --||-- type_addr # UChar |-> ty **
    event_name_get_after_type name_addr pname name ty output_old chars.
Proof.
  intros pevent pname type_addr name_addr name nesting ty output_old chars He Hp Hi.
  unfold event_name_get_access.
  rewrite (proj2 (Z.eqb_neq pevent 0) He), (proj2 (Z.eqb_neq pname 0) Hp),
    (proj2 (Z.ltb_ge 0 nesting) Hi); split; reflexivity.
Qed.

Lemma event_name_get_after_type_success :
  forall name_addr pname name ty output_old chars,
  event_name_type_allowed ty = true ->
  event_name_get_after_type name_addr pname name ty output_old chars --||--
    name_addr # Ptr |-> name ** pname # Ptr |-> output_old **
    event_name_get_name_bytes name chars.
Proof.
  intros; unfold event_name_get_after_type, event_name_get_success_focus.
  rewrite H; split; reflexivity.
Qed.

Lemma event_name_get_null_event_error : forall pname nesting ty,
  event_name_get_error 0 pname nesting ty = Some OS_ERR_PEVENT_NULL.
Proof. reflexivity. Qed.

Lemma event_name_get_null_output_error : forall pevent nesting ty,
  pevent <> 0 -> event_name_get_error pevent 0 nesting ty = Some OS_ERR_PNAME_NULL.
Proof.
  intros; unfold event_name_get_error.
  rewrite (proj2 (Z.eqb_neq pevent 0) H); reflexivity.
Qed.

Lemma event_name_get_isr_error : forall pevent pname nesting ty,
  pevent <> 0 -> pname <> 0 -> 0 < nesting ->
  event_name_get_error pevent pname nesting ty = Some OS_ERR_NAME_GET_ISR.
Proof.
  intros pevent pname nesting ty He Hp Hi; unfold event_name_get_error.
  rewrite (proj2 (Z.eqb_neq pevent 0) He), (proj2 (Z.eqb_neq pname 0) Hp),
    (proj2 (Z.ltb_lt 0 nesting) Hi); reflexivity.
Qed.

Lemma event_name_get_invalid_type_error : forall pevent pname nesting ty,
  pevent <> 0 -> pname <> 0 -> nesting <= 0 ->
  event_name_type_allowed ty = false ->
  event_name_get_error pevent pname nesting ty = Some OS_ERR_EVENT_TYPE.
Proof.
  intros pevent pname nesting ty He Hp Hi Hty; unfold event_name_get_error.
  rewrite (proj2 (Z.eqb_neq pevent 0) He), (proj2 (Z.eqb_neq pname 0) Hp),
    (proj2 (Z.ltb_ge 0 nesting) Hi), Hty; reflexivity.
Qed.

Definition event_name_get_name_frame (names : NameResourceState)
  (p : addr) (chars : list Z) : Assertion :=
  if Z.eqb p 0 then store_name_bytes names
  else event_name_get_name_residual names p chars.

Lemma event_name_get_name_borrow : forall names p chars,
  event_name_get_readable names p chars ->
  store_name_bytes names --||--
    event_name_get_name_bytes p chars ** event_name_get_name_frame names p chars.
Proof.
  intros names p chars Hread.
  unfold event_name_get_name_bytes, event_name_get_name_frame.
  destruct (Z.eqb p 0) eqn:Hp.
  - split; entailer!.
  - apply event_name_get_name_split; apply Hread; apply Z.eqb_neq; exact Hp.
Qed.

(** This consumes the concrete bytes returned by the actual StrLen contract.
    No byte permission or reader lease survives in the returned pointer. *)
Lemma event_name_get_strlen_last_access_return : forall names p chars len,
  coq_prop (event_name_get_result names p chars len) **
    event_name_get_name_bytes p chars ** event_name_get_name_frame names p chars |--
  coq_prop (event_name_get_result names p chars len) ** store_name_bytes names.
Proof.
  intros; Intros.
  match goal with H : event_name_get_result names p chars len |- _ =>
    pose proof (proj1 H) as Hread end.
  sep_apply_l_atomic (proj2 (event_name_get_name_borrow names p chars Hread)); entailer!.
Qed.

Definition event_name_get_other_modules (sg : StableGlobVars)
  (state : UCOS2_Verify_State) : Assertion :=
  UCOS2_selected_rep sg state
    (fun module => match module with
      | EventModule | QueueModule | InterruptModule | NamesModule => false
      | _ => true end).

Definition event_name_get_full_call_frame (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (eid : EventID) (old : OSEventAbstractState)
  (chars : list Z) : Assertion :=
  event_name_set_raw_residual sg state.(TskState) state.(EventState) eid old **
  queue_storage_rep sg state.(EventState) **
  interrupt_inv_no_int_nesting sg state.(IntrState) **
  event_name_get_name_frame state.(NameState) old.(eventName) chars **
  event_name_get_other_modules sg state.

Lemma event_name_get_full_profile_names : forall sg state,
  UCOS2_full_state_inv sg state -> sg.(osKernelConfig).(cfgEventNames) = true.
Proof.
  intros sg state H; unfold UCOS2_full_state_inv, UCOS2_full_state_inv_with_ready,
    full_features_kernel_profile in H; tauto.
Qed.

Lemma event_name_get_full_name_readable : forall sg state eid old,
  UCOS2_full_state_inv sg state ->
  state.(EventState).(inUsedEventStates) eid = Some old ->
  exists chars, event_name_get_readable state.(NameState) old.(eventName) chars.
Proof.
  intros sg state eid old Hvalid Hget.
  destruct (UCOS2_full_state_inv_names_valid sg state Hvalid old.(eventName)) as [chars Hread].
  - right; left; split; [eapply event_name_get_full_profile_names; eassumption|].
    exists eid, old; auto.
  - exists chars; intros Hnonnull; exact Hread.
Qed.

Lemma event_name_get_full_call_split : forall sg state eid old chars,
  state.(EventState).(inUsedEventStates) eid = Some old ->
  event_name_get_readable state.(NameState) old.(eventName) chars ->
  UCOS2_full_inv sg state |--
    coq_prop (UCOS2_full_state_inv sg state) &&
    (sg.(g_OSIntNesting) # UChar |-> state.(IntrState).(intNesting) **
     event_cell (event_addr sg eid) EventTypeField (Some (encode_event_type old.(eventType))) **
     event_cell (event_addr sg eid) EventNameField (Some old.(eventName)) **
     event_name_get_name_bytes old.(eventName) chars **
     event_name_get_full_call_frame sg state eid old chars).
Proof.
  intros sg state eid old chars Hget Hread.
  unfold UCOS2_full_inv; Intros.
  unfold UCOS2_raw_rep.
  sep_apply_l_atomic (event_name_set_raw_split sg state.(TskState) state.(EventState) eid old
    (event_name_get_full_profile_names sg state H) Hget).
  rewrite (event_name_get_name_borrow state.(NameState) old.(eventName) chars Hread).
  unfold event_name_get_full_call_frame, event_name_get_other_modules, UCOS2_selected_rep.
  cbn [UCOS2_module_rep].
  unfold interrupt_inv, interrupt_inv_no_int_nesting, store_int_state; entailer!.
Qed.

Lemma event_name_get_full_call_merge : forall sg state eid old chars,
  UCOS2_full_state_inv sg state ->
  state.(EventState).(inUsedEventStates) eid = Some old ->
  event_name_get_readable state.(NameState) old.(eventName) chars ->
  sg.(g_OSIntNesting) # UChar |-> state.(IntrState).(intNesting) **
    event_cell (event_addr sg eid) EventTypeField (Some (encode_event_type old.(eventType))) **
    event_cell (event_addr sg eid) EventNameField (Some old.(eventName)) **
    event_name_get_name_bytes old.(eventName) chars **
    event_name_get_full_call_frame sg state eid old chars |-- UCOS2_full_inv sg state.
Proof.
  intros sg state eid old chars Hvalid Hget Hread.
  unfold event_name_get_full_call_frame.
  eapply derivable1_trans with (y :=
    (event_cell (event_addr sg eid) EventTypeField (Some (encode_event_type old.(eventType))) **
     event_cell (event_addr sg eid) EventNameField (Some old.(eventName)) **
     event_name_set_raw_residual sg state.(TskState) state.(EventState) eid old) **
    (event_name_get_name_bytes old.(eventName) chars **
      event_name_get_name_frame state.(NameState) old.(eventName) chars) **
    (sg.(g_OSIntNesting) # UChar |-> state.(IntrState).(intNesting) **
     queue_storage_rep sg state.(EventState) **
     interrupt_inv_no_int_nesting sg state.(IntrState) ** event_name_get_other_modules sg state)).
  { entailer!. }
  sep_apply_l_atomic (event_name_set_raw_merge sg state.(TskState) state.(EventState) eid old
    (event_name_get_full_profile_names sg state Hvalid) Hget).
  sep_apply_l_atomic (proj2 (event_name_get_name_borrow state.(NameState) old.(eventName) chars Hread)).
  unfold UCOS2_full_inv, UCOS2_raw_rep, event_name_get_other_modules, UCOS2_selected_rep.
  cbn [UCOS2_module_rep].
  unfold interrupt_inv, interrupt_inv_no_int_nesting, store_int_state; entailer!.
Qed.

(** A real read-only source client, with the public error/result semantics.
    It changes neither the kernel name map nor its existing allocation owners.
    Its caller output cells are outside the kernel raw owner. *)
Definition event_name_get_client (invocation : nat) (eid : EventID)
  (pevent pname nesting ty : Z) : KernelClientAction :=
  {| kernel_client_actor := Some invocation;
     kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       exists result, event_name_get_sem sg eid pevent pname nesting ty before result after |}.

Lemma event_name_get_client_preserves_full_resources : forall invocation eid pevent pname nesting ty,
  kernel_client_preserves_resources UCOS2_full_state_inv
    (event_name_get_client invocation eid pevent pname nesting ty).
Proof.
  intros invocation eid pevent pname nesting ty sg before after Hvalid [result Hstep].
  pose proof (event_name_get_sem_state_eq sg eid pevent pname nesting ty before result after Hstep).
  subst after; split; [exact Hvalid|]. split; [intros; reflexivity|].
  split; [intros; reflexivity|intros; assumption].
Qed.

(** The global producer supplies the string permission needed by the public
    C context. The caller supplies only its actual output/error cells and the
    existing conditional CPU token. This is a checkpoint, not a rule allowing
    the checkpoint to be framed through an arbitrary unmasked interval. *)
Lemma event_name_get_full_entry_context :
  forall sg state eid old pname perr output_old error_old type_addr name_addr
    platform invocation origin mask,
  UCOS2_full_state_inv sg state ->
  state.(EventState).(inUsedEventStates) eid = Some old ->
  event_addr sg eid <> 0 -> pname <> 0 -> state.(IntrState).(intNesting) <= 0 ->
  event_name_type_allowed (encode_event_type old.(eventType)) = true ->
  type_addr = event_addr sg eid -> name_addr = event_addr sg eid + 20 ->
  UCOS2_full_inv sg state ** pname # Ptr |-> output_old ** perr # UChar |-> error_old **
    interrupt_platform_running platform invocation origin mask |--
  EX chars,
    coq_prop (event_name_get_request state.(NameState) (event_addr sg eid) pname
      state.(IntrState).(intNesting) (encode_event_type old.(eventType)) old.(eventName) chars) **
    perr # UChar |-> error_old **
    sg.(g_OSIntNesting) # UChar |-> state.(IntrState).(intNesting) **
    interrupt_platform_running platform invocation origin mask **
    event_name_get_full_call_frame sg state eid old chars **
    event_name_get_access (event_addr sg eid) pname type_addr name_addr old.(eventName)
      state.(IntrState).(intNesting) (encode_event_type old.(eventType)) output_old chars.
Proof.
  intros sg state eid old pname perr output_old error_old type_addr name_addr
    platform invocation origin mask Hvalid Hget He Hp Hi Hty -> ->.
  destruct (event_name_get_full_name_readable sg state eid old Hvalid Hget) as [chars Hread].
  Exists chars.
  sep_apply_l_atomic (event_name_get_full_call_split sg state eid old chars Hget Hread).
  rewrite event_name_get_access_type_split by assumption.
  rewrite event_name_get_after_type_success by exact Hty.
  cbn [event_cell event_field_offset]; replace (event_addr sg eid + 0) with (event_addr sg eid) by lia.
  unfold event_name_get_request; entailer!.
  apply derivable1_truep_intros.
Qed.

(** Actual source-return consumer. It rejoins the byte loan and every other
    kernel owner, while retaining the caller's written name pointer/error and
    exact modulo result. No post-validity or post-heap premise is used. *)
Lemma event_name_get_success_return_merge_full :
  forall sg state eid old pname perr type_addr name_addr output_old error len chars
    platform invocation origin mask,
  UCOS2_full_state_inv sg state ->
  state.(EventState).(inUsedEventStates) eid = Some old ->
  event_addr sg eid <> 0 -> pname <> 0 -> state.(IntrState).(intNesting) <= 0 ->
  event_name_type_allowed (encode_event_type old.(eventType)) = true ->
  type_addr = event_addr sg eid -> name_addr = event_addr sg eid + 20 ->
  coq_prop (event_name_get_observation state.(NameState) (event_addr sg eid) pname
      state.(IntrState).(intNesting) (encode_event_type old.(eventType)) old.(eventName) chars error len
      (event_name_get_output (event_addr sg eid) pname state.(IntrState).(intNesting)
        (encode_event_type old.(eventType)) old.(eventName))) **
    perr # UChar |-> error **
    sg.(g_OSIntNesting) # UChar |-> state.(IntrState).(intNesting) **
    interrupt_platform_running platform invocation origin mask **
    event_name_get_full_call_frame sg state eid old chars **
    event_name_get_access (event_addr sg eid) pname type_addr name_addr old.(eventName)
      state.(IntrState).(intNesting) (encode_event_type old.(eventType))
      (event_name_get_final_output (event_addr sg eid) pname state.(IntrState).(intNesting)
        (encode_event_type old.(eventType)) old.(eventName) output_old) chars |--
  coq_prop (error = 0 /\ len = event_name_get_length old.(eventName) chars) **
    pname # Ptr |-> old.(eventName) ** perr # UChar |-> error **
    interrupt_platform_running platform invocation origin mask ** UCOS2_full_inv sg state.
Proof.
  intros sg state eid old pname perr type_addr name_addr output_old error len chars
    platform invocation origin mask Hvalid Hget He Hp Hi Hty -> ->.
  assert (Herr := event_name_get_success_guard (event_addr sg eid) pname
    state.(IntrState).(intNesting) (encode_event_type old.(eventType)) He Hp Hi Hty).
  unfold event_name_get_final_output, event_name_get_output, event_name_get_observation.
  rewrite Herr; Intros.
  match goal with H : _ /\ event_name_get_result _ _ _ _ /\ _ |- _ =>
    destruct H as [Herror [[Hread Hlen] Houtput]] end.
  rewrite event_name_get_access_type_split by assumption.
  rewrite event_name_get_after_type_success by exact Hty.
  assert (Hmerge := event_name_get_full_call_merge sg state eid old chars Hvalid Hget Hread).
  cbn [event_cell event_field_offset] in Hmerge.
  replace (event_addr sg eid + 0) with (event_addr sg eid) in Hmerge by lia.
  sep_apply_l_atomic Hmerge.
  cbn [encode_os_err_code] in Herror; entailer!.
Qed.

(** The source copies the POINTER, not its bytes: one actual 32-bit
    little-endian pointer load followed by one typed pointer-store block.
    There is no inserted scheduling cut inside that block's byte expansion. *)
Lemma event_name_get_output_store_execution : forall name_addr pname name output_old frame heap,
  (name_addr # Ptr |-> name ** pname # Ptr |-> output_old ** frame) heap ->
  pointer_load name_addr name heap /\
  exists after,
    kernel_heap_execution (pointer_store_writes pname name) heap after /\
    (name_addr # Ptr |-> name ** pname # Ptr |-> name ** frame) after.
Proof.
  intros name_addr pname name output_old frame heap Hheap.
  assert (Hload : pointer_load name_addr name heap).
  { assert (Hfocus : name_addr # Ptr |-> name ** pname # Ptr |-> output_old ** frame |--
        name_addr # Ptr |-> name ** (pname # Ptr |-> output_old ** frame)) by entailer!.
    eapply framed_pointer_store_load; exact (Hfocus heap Hheap). }
  split; [exact Hload|].
  assert (Hsplit : name_addr # Ptr |-> name ** pname # Ptr |-> output_old ** frame |--
      pname # Ptr |->_ ** (name_addr # Ptr |-> name ** frame)).
  { sep_apply_l_atomic (store_ptr_undef_store_ptr pname output_old); entailer!. }
  destruct (framed_pointer_store_execution pname name _ heap (proj1 Hload) (Hsplit heap Hheap))
    as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  assert (Hreorder : pname # Ptr |-> name ** (name_addr # Ptr |-> name ** frame) |--
    name_addr # Ptr |-> name ** pname # Ptr |-> name ** frame) by entailer!.
  exact (Hreorder after Hafter).
Qed.

Lemma event_name_get_source_output_execution :
  forall pevent pname type_addr name_addr name nesting ty output_old chars frame heap,
  pevent <> 0 -> pname <> 0 -> nesting <= 0 -> event_name_type_allowed ty = true ->
  (event_name_get_access pevent pname type_addr name_addr name nesting ty output_old chars ** frame) heap ->
  pointer_load name_addr name heap /\
  exists after,
    kernel_heap_execution (pointer_store_writes pname name) heap after /\
    (event_name_get_access pevent pname type_addr name_addr name nesting ty name chars ** frame) after.
Proof.
  intros pevent pname type_addr name_addr name nesting ty output_old chars frame heap He Hp Hi Hty Hheap.
  assert (Hsplit : event_name_get_access pevent pname type_addr name_addr name nesting ty output_old chars ** frame |--
    name_addr # Ptr |-> name ** pname # Ptr |-> output_old **
      (type_addr # UChar |-> ty ** event_name_get_name_bytes name chars ** frame)).
  { rewrite event_name_get_access_type_split by assumption.
    rewrite event_name_get_after_type_success by exact Hty; entailer!. }
  destruct (event_name_get_output_store_execution name_addr pname name output_old _ heap (Hsplit heap Hheap))
    as [Hload [after [Hrun Hafter]]].
  split; [exact Hload|]; exists after; split; [exact Hrun|].
  assert (Hmerge : name_addr # Ptr |-> name ** pname # Ptr |-> name **
      (type_addr # UChar |-> ty ** event_name_get_name_bytes name chars ** frame) |--
    event_name_get_access pevent pname type_addr name_addr name nesting ty name chars ** frame).
  { rewrite event_name_get_access_type_split by assumption.
    rewrite event_name_get_after_type_success by exact Hty; entailer!. }
  exact (Hmerge after Hafter).
Qed.

Lemma event_name_get_source_output_execution_post :
  forall pevent pname type_addr name_addr name nesting ty output_old chars frame heap after,
  pevent <> 0 -> pname <> 0 -> nesting <= 0 -> event_name_type_allowed ty = true ->
  (event_name_get_access pevent pname type_addr name_addr name nesting ty output_old chars ** frame) heap ->
  kernel_heap_execution (pointer_store_writes pname name) heap after ->
  (event_name_get_access pevent pname type_addr name_addr name nesting ty name chars ** frame) after.
Proof.
  intros pevent pname type_addr name_addr name nesting ty output_old chars frame heap after He Hp Hi Hty Hheap Hrun.
  destruct (event_name_get_source_output_execution pevent pname type_addr name_addr name nesting ty output_old chars frame heap
    He Hp Hi Hty Hheap) as [_ [made [Hmade Hpost]]].
  assert (made = after) by (eapply kernel_heap_execution_deterministic; eassumption).
  subst made; exact Hpost.
Qed.
