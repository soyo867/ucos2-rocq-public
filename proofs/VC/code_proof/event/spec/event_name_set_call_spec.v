Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.VC.code.event.spec.event_name_set_spec.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.event_registration.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_client_invariants.

Import UCOS2_C_Rules EventStateDef ListNotations.
Import KernelHeapStorage.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The concrete public guard domain is not restricted to live Events.
    Null event/name and ISR branches require no Event cells. The type read
    accepts every byte; the name cell is needed only for a supported type.
    These selectors stay opaque to QCP until their actual source guard. *)
Definition event_name_set_access
  (pevent pname type_addr name_addr : addr) (nesting type_byte name_old : Z)
  : Assertion :=
  if Z.eqb pevent 0 then emp else
  if Z.eqb pname 0 then emp else
  if Z.ltb 0 nesting then emp else
  event_name_set_branch_focus type_addr name_addr type_byte name_old.

Definition event_name_set_after_type (name_addr : addr)
  (type_byte name_old : Z) : Assertion :=
  if event_name_type_allowed type_byte
  then name_addr # Ptr |-> name_old else emp.

Definition event_name_set_final_name
  (pevent pname : addr) (nesting type_byte name_old : Z) : Z :=
  match event_name_set_error pevent pname nesting type_byte with
  | Some _ => name_old
  | None => pname
  end.

Definition event_name_type_supported (type_byte : Z) : Prop :=
  event_name_type_allowed type_byte = true.

Lemma event_name_type_allowed_true_iff : forall type_byte,
  event_name_type_allowed type_byte = true <->
  type_byte = 3 \/ type_byte = 4 \/ type_byte = 1 \/ type_byte = 2.
Proof.
  intros; unfold event_name_type_allowed; cbn [encode_event_type].
  rewrite !orb_true_iff, !Z.eqb_eq; tauto.
Qed.

Lemma event_name_type_allowed_false_iff : forall type_byte,
  event_name_type_allowed type_byte = false <->
  type_byte <> 3 /\ type_byte <> 4 /\ type_byte <> 1 /\ type_byte <> 2.
Proof.
  intros; unfold event_name_type_allowed; cbn [encode_event_type].
  rewrite !orb_false_iff, !Z.eqb_neq; tauto.
Qed.

Lemma event_name_set_access_type_split :
  forall pevent pname type_addr name_addr nesting type_byte name_old,
  pevent <> 0 -> pname <> 0 -> nesting <= 0 ->
  event_name_set_access pevent pname type_addr name_addr nesting type_byte name_old --||--
    type_addr # UChar |-> type_byte **
      event_name_set_after_type name_addr type_byte name_old.
Proof.
  intros pevent pname type_addr name_addr nesting type_byte name_old Hevent Hname Hnest.
  assert (He : Z.eqb pevent 0 = false) by (apply Z.eqb_neq; exact Hevent).
  assert (Hn : Z.eqb pname 0 = false) by (apply Z.eqb_neq; exact Hname).
  assert (Hi : Z.ltb 0 nesting = false) by (apply Z.ltb_ge; exact Hnest).
  unfold event_name_set_access, event_name_set_branch_focus, event_name_set_type_focus,
    event_name_set_after_type; rewrite He, Hn, Hi; split; reflexivity.
Qed.

Lemma event_name_set_after_type_supported : forall name_addr type_byte name_old,
  event_name_type_allowed type_byte = true ->
  event_name_set_after_type name_addr type_byte name_old --||--
    name_addr # Ptr |-> name_old.
Proof. intros; unfold event_name_set_after_type; rewrite H; split; reflexivity. Qed.

Lemma event_name_set_after_type_invalid : forall name_addr type_byte name_old,
  event_name_type_allowed type_byte = false ->
  event_name_set_after_type name_addr type_byte name_old --||-- emp.
Proof. intros; unfold event_name_set_after_type; rewrite H; split; reflexivity. Qed.

Lemma event_name_set_null_event_error : forall pname nesting type_byte,
  event_name_set_error 0 pname nesting type_byte = Some OS_ERR_PEVENT_NULL.
Proof. reflexivity. Qed.

Lemma event_name_set_null_name_error : forall pevent nesting type_byte,
  pevent <> 0 ->
  event_name_set_error pevent 0 nesting type_byte = Some OS_ERR_PNAME_NULL.
Proof.
  intros; unfold event_name_set_error.
  assert (Htest : Z.eqb pevent 0 = false) by (apply Z.eqb_neq; exact H).
  rewrite Htest; reflexivity.
Qed.

Lemma event_name_set_isr_error : forall pevent pname nesting type_byte,
  pevent <> 0 -> pname <> 0 -> 0 < nesting ->
  event_name_set_error pevent pname nesting type_byte = Some OS_ERR_NAME_SET_ISR.
Proof.
  intros pevent pname nesting type_byte Hevent Hname Hnest.
  unfold event_name_set_error.
  assert (He : Z.eqb pevent 0 = false) by (apply Z.eqb_neq; exact Hevent).
  assert (Hn : Z.eqb pname 0 = false) by (apply Z.eqb_neq; exact Hname).
  assert (Hi : Z.ltb 0 nesting = true) by (apply Z.ltb_lt; exact Hnest).
  rewrite He, Hn, Hi; reflexivity.
Qed.

Lemma event_name_set_invalid_type_error : forall pevent pname nesting type_byte,
  pevent <> 0 -> pname <> 0 -> nesting <= 0 ->
  event_name_type_allowed type_byte = false ->
  event_name_set_error pevent pname nesting type_byte = Some OS_ERR_EVENT_TYPE.
Proof.
  intros pevent pname nesting type_byte Hevent Hname Hnest Htype.
  unfold event_name_set_error.
  assert (He : Z.eqb pevent 0 = false) by (apply Z.eqb_neq; exact Hevent).
  assert (Hn : Z.eqb pname 0 = false) by (apply Z.eqb_neq; exact Hname).
  assert (Hi : Z.ltb 0 nesting = false) by (apply Z.ltb_ge; exact Hnest).
  rewrite He, Hn, Hi, Htype; reflexivity.
Qed.

(** Names-enabled full-global reconstruction. The old validity is an input;
    after validity is proved from the existing Event update and registered
    readable name. This does not provide a full-profile environment rule. *)
Definition event_name_set_full_frame (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (eid : EventID) (old : OSEventAbstractState)
  : Assertion :=
  event_name_set_raw_residual sg state.(TskState) state.(EventState) eid old **
  queue_storage_rep sg state.(EventState) **
  UCOS2_raw_rep_missing_event_queue sg state.

Lemma event_name_set_full_profile_names : forall sg state,
  UCOS2_full_state_inv sg state -> sg.(osKernelConfig).(cfgEventNames) = true.
Proof.
  intros sg state Hvalid.
  unfold UCOS2_full_state_inv, UCOS2_full_state_inv_with_ready,
    full_features_kernel_profile in Hvalid; tauto.
Qed.

Lemma event_name_set_preserves_full_validity : forall sg state eid old name chars,
  UCOS2_full_state_inv sg state ->
  state.(EventState).(inUsedEventStates) eid = Some old ->
  readable_name state.(NameState) name chars ->
  UCOS2_full_state_inv sg (event_name_set_post state eid old name).
Proof.
  intros sg state eid old name chars Hvalid Hget Hread.
  pose proof Hvalid as Hparts.
  unfold UCOS2_full_state_inv, UCOS2_full_state_inv_with_ready in Hparts.
  destruct Hparts as [_ [_ [_ [Hevents _]]]].
  eapply UCOS2_full_state_inv_event_name_set_bridge; try eassumption.
  eapply event_set_name_preserves_registered_in_range; eassumption.
Qed.

Lemma event_name_set_full_split_type_name : forall sg state eid old,
  state.(EventState).(inUsedEventStates) eid = Some old ->
  UCOS2_full_inv sg state |--
  coq_prop (UCOS2_full_state_inv sg state) &&
    (event_cell (event_addr sg eid) EventTypeField (Some (encode_event_type old.(eventType))) **
     event_cell (event_addr sg eid) EventNameField (Some old.(eventName)) **
     event_name_set_full_frame sg state eid old).
Proof.
  intros sg state eid old Hget.
  rewrite UCOS2_full_inv_split_event_queue; Intros.
  match goal with H : UCOS2_full_state_inv sg state |- _ => rename H into Hvalid end.
  unfold event_name_set_full_frame.
  sep_apply_l_atomic (event_name_set_raw_split sg state.(TskState) state.(EventState) eid old
    (event_name_set_full_profile_names sg state Hvalid) Hget).
  entailer!.
Qed.

Lemma event_name_set_full_merge_type_name : forall sg state eid old,
  UCOS2_full_state_inv sg state ->
  state.(EventState).(inUsedEventStates) eid = Some old ->
  event_cell (event_addr sg eid) EventTypeField (Some (encode_event_type old.(eventType))) **
    event_cell (event_addr sg eid) EventNameField (Some old.(eventName)) **
    event_name_set_full_frame sg state eid old |-- UCOS2_full_inv sg state.
Proof.
  intros sg state eid old Hvalid Hget.
  unfold event_name_set_full_frame.
  sep_apply_l_atomic (event_name_set_raw_merge sg state.(TskState) state.(EventState) eid old
    (event_name_set_full_profile_names sg state Hvalid) Hget).
  rewrite UCOS2_full_inv_split_event_queue; entailer!.
Qed.

Lemma event_name_set_full_merge_updated_name : forall sg state eid old name chars,
  UCOS2_full_state_inv sg state ->
  state.(EventState).(inUsedEventStates) eid = Some old ->
  readable_name state.(NameState) name chars ->
  event_cell (event_addr sg eid) EventTypeField (Some (encode_event_type old.(eventType))) **
    event_cell (event_addr sg eid) EventNameField (Some name) **
    event_name_set_full_frame sg state eid old |--
  UCOS2_full_inv sg (event_name_set_post state eid old name).
Proof.
  intros sg state eid old name chars Hvalid Hget Hread.
  pose proof (event_name_set_preserves_full_validity sg state eid old name chars Hvalid Hget Hread)
    as Hafter.
  unfold event_name_set_full_frame.
  sep_apply_l_atomic (event_name_set_raw_merge_updated sg state.(TskState) state.(EventState) eid old name
    (event_name_set_full_profile_names sg state Hvalid) Hget).
  sep_apply_l_atomic (event_name_set_queue_storage_frame sg state.(EventState) eid old name Hget).
  rewrite UCOS2_full_inv_split_event_queue.
  unfold event_name_set_post in *; cbn [replace_EventS TskState EventState].
  rewrite UCOS2_raw_rep_missing_event_queue_replace_event_eq; entailer!.
Qed.

Lemma event_name_set_post_name_state_eq : forall state eid old name,
  (event_name_set_post state eid old name).(NameState) = state.(NameState).
Proof. reflexivity. Qed.

Lemma event_name_set_post_name_root : forall sg state eid old name,
  sg.(osKernelConfig).(cfgEventNames) = true ->
  kernel_name_root sg (event_name_set_post state eid old name) name.
Proof.
  intros sg state eid old name Hnames.
  unfold kernel_name_root; right; left; split; [exact Hnames|].
  exists eid, (event_set_name old name); split; [|reflexivity].
  cbn [event_name_set_post replace_EventS EventState update_event_field_raw inUsedEventStates].
  rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma event_name_set_post_protects_name_byte : forall sg state eid old name chars i,
  sg.(osKernelConfig).(cfgEventNames) = true ->
  readable_name state.(NameState) name chars ->
  (i <= List.length chars)%nat ->
  kernel_name_byte_protected sg (event_name_set_post state eid old name) (name + Z.of_nat i).
Proof.
  intros; eapply kernel_name_referenced_byte_protected;
    [apply event_name_set_post_name_root; exact H|exact H0|exact H1].
Qed.

Lemma event_name_set_post_excludes_name_source_release :
  forall sg state eid old name chars i source src,
  sg.(osKernelConfig).(cfgEventNames) = true ->
  readable_name state.(NameState) name chars ->
  (i <= List.length chars)%nat ->
  In (name + Z.of_nat i) src.(nameStorageDomain) ->
  ~ name_source_releasable state.(NameState) source src
      (kernel_name_byte_protected sg (event_name_set_post state eid old name)).
Proof.
  intros sg state eid old name chars i source src Hnames Hread Hi Hin [_ [_ [Hprotected _]]].
  exact (Hprotected (name + Z.of_nat i)
    (event_name_set_post_protects_name_byte sg state eid old name chars i Hnames Hread Hi) Hin).
Qed.

(** One real names-enabled source client. The ordered public guards are
    still the canonical [event_name_set_sem]; the name lifetime obligation
    is needed only when the source publishes a pointer. Nothing tests or
    assumes validity of the post-state. The action retires no invocation
    and does not modify either allocator's private allocation map. *)
Definition event_name_set_name_protocol (state : UCOS2_Verify_State)
  (pevent pname : addr) (nesting type_byte : Z) : Prop :=
  event_name_set_error pevent pname nesting type_byte = None ->
  exists chars, readable_name state.(NameState) pname chars.

Definition event_name_set_client (invocation : nat) (eid : EventID)
  (pevent pname : addr) (nesting type_byte : Z) : KernelClientAction :=
  {| kernel_client_actor := Some invocation;
     kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       event_name_set_name_protocol before pevent pname nesting type_byte /\
       exists error, event_name_set_sem sg eid pevent pname nesting type_byte before error after |}.

Lemma event_name_set_client_preserves_full_resources :
  forall invocation eid pevent pname nesting type_byte,
  kernel_client_preserves_resources UCOS2_full_state_inv
    (event_name_set_client invocation eid pevent pname nesting type_byte).
Proof.
  intros invocation eid pevent pname nesting type_byte sg before after Hvalid
    [Hprotocol [error Hstep]].
  unfold event_name_set_sem in Hstep.
  destruct (event_name_set_error pevent pname nesting type_byte) as [expected|] eqn:Herror.
  - destruct Hstep as [_ ->].
    split; [exact Hvalid|]. split; [intros; reflexivity|].
    split; [intros; reflexivity|intros; assumption].
  - destruct Hstep as [old [Hget [_ [_ [_ ->]]]]].
    destruct (Hprotocol Herror) as [chars Hread].
    split.
    + eapply event_name_set_preserves_full_validity; eassumption.
    + split; [intros; reflexivity|].
      split; [intros; reflexivity|intros; assumption].
Qed.

(** Physical producer for the one pointer store in the critical segment.
    The four-byte little-endian expansion is ONE typed-store block; this
    theorem does not introduce interruptible cuts between its bytes. The
    initial heap owns the actual old name pointer. The same full frame is
    returned with only EventName changed, including the name bytes owned by
    NamesModule and all non-Event module owners. *)
Lemma event_name_set_name_store_execution : forall sg state eid old name chars heap,
  UCOS2_full_state_inv sg state ->
  state.(EventState).(inUsedEventStates) eid = Some old ->
  readable_name state.(NameState) name chars ->
  0 <= name < 4294967296 ->
  UCOS2_raw_rep sg state heap ->
  exists final,
    kernel_heap_execution (pointer_store_writes (event_addr sg eid + 20) name) heap final /\
    UCOS2_full_inv sg (event_name_set_post state eid old name) final.
Proof.
  intros sg state eid old name chars heap Hvalid Hget Hread Hrange Hraw.
  let residual := constr:(event_cell (event_addr sg eid) EventTypeField
      (Some (encode_event_type old.(eventType))) ** event_name_set_full_frame sg state eid old) in
  assert (Hsplit : UCOS2_raw_rep sg state |--
    (event_addr sg eid + 20) # Ptr |->_ ** residual).
  { eapply derivable1_trans with (UCOS2_full_inv sg state).
    - unfold UCOS2_full_inv; entailer!.
    - sep_apply_l_atomic (event_name_set_full_split_type_name sg state eid old Hget).
      Intros.
      cbn [event_cell event_field_offset].
      sep_apply_l_atomic (store_ptr_undef_store_ptr (event_addr sg eid + 20) old.(eventName)).
      entailer!. }
  destruct (framed_pointer_store_execution (event_addr sg eid + 20) name _ heap Hrange
    (Hsplit heap Hraw)) as [final [Hrun Hfinal]].
  exists final; split; [exact Hrun|].
  assert (Hmerge : (event_addr sg eid + 20) # Ptr |-> name **
    (event_cell (event_addr sg eid) EventTypeField
      (Some (encode_event_type old.(eventType))) ** event_name_set_full_frame sg state eid old) |--
    UCOS2_full_inv sg (event_name_set_post state eid old name)).
  { eapply derivable1_trans; [|apply event_name_set_full_merge_updated_name with (chars := chars);
      assumption].
    cbn [event_cell event_field_offset]; entailer!. }
  exact (Hmerge final Hfinal).
Qed.

Lemma event_name_set_name_store_execution_post : forall sg state eid old name chars heap final,
  UCOS2_full_state_inv sg state ->
  state.(EventState).(inUsedEventStates) eid = Some old ->
  readable_name state.(NameState) name chars ->
  0 <= name < 4294967296 ->
  UCOS2_raw_rep sg state heap ->
  kernel_heap_execution (pointer_store_writes (event_addr sg eid + 20) name) heap final ->
  UCOS2_full_inv sg (event_name_set_post state eid old name) final.
Proof.
  intros sg state eid old name chars heap final Hvalid Hget Hread Hrange Hraw Hrun.
  destruct (event_name_set_name_store_execution sg state eid old name chars heap
    Hvalid Hget Hread Hrange Hraw) as [actual [Hactual Hpost]].
  assert (final = actual) by (eapply kernel_heap_execution_deterministic; eassumption).
  subst; exact Hpost.
Qed.

Lemma event_name_set_name_store_establishes_client_step :
  forall invocation sg state eid old pevent name nesting type_byte chars heap,
  UCOS2_full_state_inv sg state ->
  state.(EventState).(inUsedEventStates) eid = Some old ->
  pevent = event_addr sg eid -> type_byte = encode_event_type old.(eventType) ->
  event_name_set_error pevent name nesting type_byte = None ->
  readable_name state.(NameState) name chars ->
  0 <= name < 4294967296 -> UCOS2_raw_rep sg state heap ->
  exists final,
    kernel_heap_execution (pointer_store_writes (event_addr sg eid + 20) name) heap final /\
    kernel_client_step (event_name_set_client invocation eid pevent name nesting type_byte)
      sg state (event_name_set_post state eid old name) /\
    UCOS2_full_inv sg (event_name_set_post state eid old name) final.
Proof.
  intros invocation sg state eid old pevent name nesting type_byte chars heap
    Hvalid Hget Haddr Htype Hguard Hread Hrange Hraw.
  destruct (event_name_set_name_store_execution sg state eid old name chars heap
    Hvalid Hget Hread Hrange Hraw) as [final [Hrun Hpost]].
  exists final; split; [exact Hrun|]. split; [|exact Hpost].
  split.
  - intros _; exists chars; exact Hread.
  - exists OS_ERR_NONE; unfold event_name_set_sem; rewrite Hguard.
    exists old; repeat split; assumption.
Qed.

(** This consumes the proved full-profile instance for this actual source
    step. It does not assert that every other registered environment client
    preserves the full profile, nor construct a complete interrupt return. *)
Lemma event_name_set_client_step_frames_resources :
  forall invocation eid pevent pname nesting type_byte sg before after observer origin,
  UCOS2_full_state_inv sg before ->
  kernel_client_step (event_name_set_client invocation eid pevent pname nesting type_byte)
    sg before after ->
  invocation <> observer ->
  task_invocation_active before.(TskState) observer origin ->
  UCOS2_full_state_inv sg after /\
  task_creation_frame observer before.(TskState) after.(TskState) /\
  event_creation_frame observer before.(EventState) after.(EventState) /\
  task_invocation_active after.(TskState) observer origin.
Proof.
  intros invocation eid pevent pname nesting type_byte sg before after observer origin
    Hvalid Hstep Hforeign Hactive.
  destruct (event_name_set_client_preserves_full_resources invocation eid pevent pname nesting type_byte
    sg before after Hvalid Hstep) as [Hafter [Htask [Hevent Hresume]]].
  split; [exact Hafter|]. split.
  - apply Htask; cbn; congruence.
  - split; [apply Hevent; discriminate|].
    apply Hresume; [reflexivity|exact Hactive].
Qed.

(** A specialization of the C contract's arbitrary frame to the real
    full-global owner. OSIntNesting is outside the C frame because the
    public C contract reads it explicitly. No owner is duplicated. *)
Definition event_name_set_other_modules (sg : StableGlobVars)
  (state : UCOS2_Verify_State) : Assertion :=
  UCOS2_selected_rep sg state
    (fun module => match module with
      | EventModule | QueueModule | InterruptModule => false
      | _ => true
      end).

Definition event_name_set_full_call_frame (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (eid : EventID) (old : OSEventAbstractState)
  : Assertion :=
  event_name_set_raw_residual sg state.(TskState) state.(EventState) eid old **
  queue_storage_rep sg state.(EventState) **
  interrupt_inv_no_int_nesting sg state.(IntrState) **
  event_name_set_other_modules sg state.

Lemma event_name_set_full_frame_split_nesting : forall sg state eid old,
  event_name_set_full_frame sg state eid old --||--
    sg.(g_OSIntNesting) # UChar |-> state.(IntrState).(intNesting) **
    event_name_set_full_call_frame sg state eid old.
Proof.
  intros; unfold event_name_set_full_frame, event_name_set_full_call_frame,
    event_name_set_other_modules, UCOS2_raw_rep_missing_event_queue,
    UCOS2_raw_rep_missing_two, UCOS2_selected_rep.
  cbn [UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect UCOS2_module_rep].
  unfold interrupt_inv, interrupt_inv_no_int_nesting, store_int_state.
  split; entailer!.
Qed.

Lemma event_name_set_full_call_split : forall sg state eid old,
  state.(EventState).(inUsedEventStates) eid = Some old ->
  UCOS2_full_inv sg state |--
    coq_prop (UCOS2_full_state_inv sg state) &&
    (sg.(g_OSIntNesting) # UChar |-> state.(IntrState).(intNesting) **
     event_cell (event_addr sg eid) EventTypeField (Some (encode_event_type old.(eventType))) **
     event_cell (event_addr sg eid) EventNameField (Some old.(eventName)) **
     event_name_set_full_call_frame sg state eid old).
Proof.
  intros sg state eid old Hget.
  sep_apply_l_atomic (event_name_set_full_split_type_name sg state eid old Hget).
  rewrite event_name_set_full_frame_split_nesting; entailer!.
Qed.

Lemma event_name_set_full_call_merge_updated_name : forall sg state eid old name chars,
  UCOS2_full_state_inv sg state ->
  state.(EventState).(inUsedEventStates) eid = Some old ->
  readable_name state.(NameState) name chars ->
  sg.(g_OSIntNesting) # UChar |-> state.(IntrState).(intNesting) **
    event_cell (event_addr sg eid) EventTypeField (Some (encode_event_type old.(eventType))) **
    event_cell (event_addr sg eid) EventNameField (Some name) **
    event_name_set_full_call_frame sg state eid old |--
  UCOS2_full_inv sg (event_name_set_post state eid old name).
Proof.
  intros sg state eid old name chars Hvalid Hget Hread.
  eapply derivable1_trans; [|eapply event_name_set_full_merge_updated_name; eassumption].
  rewrite event_name_set_full_frame_split_nesting; entailer!.
Qed.

(** A consumer of the ACTUAL C return assertion, not a premise asserting
    that the desired global post holds. The source-layout equalities identify
    the two native ECB addresses; the native-header ABI probe checks those
    offsets. This is a checkpoint reconstruction, not stability of the old
    checkpoint across an unmasked source/CPU/CSL environment interval. *)
Lemma event_name_set_success_return_merge_full :
  forall sg state eid old pevent name type_addr name_addr perr error chars
    platform invocation origin mask (caller_frame : Assertion),
  UCOS2_full_state_inv sg state ->
  state.(EventState).(inUsedEventStates) eid = Some old ->
  pevent <> 0 -> name <> 0 -> state.(IntrState).(intNesting) <= 0 ->
  event_name_type_allowed (encode_event_type old.(eventType)) = true ->
  type_addr = event_addr sg eid -> name_addr = event_addr sg eid + 20 ->
  readable_name state.(NameState) name chars ->
  coq_prop (event_name_set_observation pevent name state.(IntrState).(intNesting)
    (encode_event_type old.(eventType)) error) **
    perr # UChar |-> error **
    sg.(g_OSIntNesting) # UChar |-> state.(IntrState).(intNesting) **
    interrupt_platform_running platform invocation origin mask ** caller_frame **
    event_name_set_full_call_frame sg state eid old **
    event_name_set_access pevent name type_addr name_addr state.(IntrState).(intNesting)
      (encode_event_type old.(eventType))
      (event_name_set_final_name pevent name state.(IntrState).(intNesting)
        (encode_event_type old.(eventType)) old.(eventName)) |--
  coq_prop (error = 0) **
    (perr # UChar |-> error ** interrupt_platform_running platform invocation origin mask **
     caller_frame ** UCOS2_full_inv sg (event_name_set_post state eid old name)).
Proof.
  intros sg state eid old pevent name type_addr name_addr perr error chars
    platform invocation origin mask caller_frame Hvalid Hget Hevent Hname Hnest Htype
    Htypeaddr Hnameaddr Hread; subst type_addr name_addr.
  pose proof (event_name_set_success_guard pevent name state.(IntrState).(intNesting)
    (encode_event_type old.(eventType)) Hevent Hname Hnest Htype) as Hguard.
  unfold event_name_set_observation, event_name_set_final_name; rewrite Hguard.
  Intros.
  rewrite (event_name_set_access_type_split _ _ _ _ _ _ _ Hevent Hname Hnest).
  rewrite (event_name_set_after_type_supported _ _ _ Htype).
  assert (Hmerge : sg.(g_OSIntNesting) # UChar |-> state.(IntrState).(intNesting) **
    event_addr sg eid # UChar |-> encode_event_type old.(eventType) **
    (event_addr sg eid + 20) # Ptr |-> name **
    event_name_set_full_call_frame sg state eid old |--
    UCOS2_full_inv sg (event_name_set_post state eid old name)).
  { pose proof (event_name_set_full_call_merge_updated_name sg state eid old name chars
      Hvalid Hget Hread) as Hmerge.
    cbn [event_cell event_field_offset] in Hmerge.
    rewrite Z.add_0_r in Hmerge; exact Hmerge. }
  sep_apply_l_atomic Hmerge; entailer!; try apply derivable1_truep_intros.
Qed.
