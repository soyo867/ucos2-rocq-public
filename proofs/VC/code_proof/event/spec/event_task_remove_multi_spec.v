Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Strings.String Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.helpers.
Require Export Ucos2Verify.lib.task Ucos2Verify.lib.task_storage.
Require Export Ucos2Verify.lib.event Ucos2Verify.lib.event_pool.
Require Export Ucos2Verify.lib.event_wait Ucos2Verify.lib.event_multi.
Require Export Ucos2Verify.VC.code.event.spec.event_task_remove_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

Definition EventTaskRemoveMultiInstances := list (EventID * nat).
Definition event_task_remove_multi_pointer (pointers : list addr) (index : Z) : addr :=
  Znth index (pointers ++ [0]) 0.

Definition event_task_remove_multi_cursor (cursor base index : Z) : Prop :=
  cursor = base + index * 4.
Definition event_task_remove_multi_value (value : Z) (pointers : list addr) (index : Z) : Prop :=
  value = event_task_remove_multi_pointer pointers index.
Definition event_task_remove_multi_array_missing (base : addr) (pointers : list addr) (index : Z) : Assertion :=
  PtrArray.missing_i base index 0 (Zlength pointers + 1) (pointers ++ [0]).

(** Internal protected traversal. Its callers may already have changed
    Stat/Pend/Dly/ready membership. Only the existing priority encoding,
    borrowed array and actual used ECBs are needed. No nonempty/NoDup
    condition is added; duplicate clearing is proved idempotent. *)
Definition event_task_remove_multi_input (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (events : Glob_EventAbstractState)
  (tid : TaskID) (t : TaskAbstractState) (pointers : list addr)
  (instances : EventTaskRemoveMultiInstances) : Prop :=
  valid_stable_glob_vars sg /\ task_priority_unique tasks /\
  valid_task_prio sg t.(curPrio) /\ tasks.(inUsedTaskStates) tid = Some t /\
  0 <= t.(curPrio) / 8 < 8 /\
  event_multi_array_binding sg events pointers instances /\
  Forall (fun instance => event_object_layout_prop sg (fst instance)) instances /\
  (forall eid e, events.(inUsedEventStates) eid = Some e ->
    event_waitList_canonical sg tasks e.(waitList)).

Definition event_task_remove_multi_events (events : Glob_EventAbstractState)
  (tid : TaskID) (instances : EventTaskRemoveMultiInstances) : Glob_EventAbstractState :=
  event_multi_remove_waiters events tid (map fst instances).

Definition event_task_remove_multi_loop (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (entry : Glob_EventAbstractState)
  (tid : TaskID) (pointers : list addr) (instances : EventTaskRemoveMultiInstances)
  (index : Z) (events : Glob_EventAbstractState) : Prop :=
  0 <= index <= Zlength pointers /\
  event_multi_array_binding sg events pointers instances /\
  (forall eid e, events.(inUsedEventStates) eid = Some e ->
    event_waitList_canonical sg tasks e.(waitList)) /\
  event_task_remove_multi_events events tid (skipn (Z.to_nat index) instances) =
    event_task_remove_multi_events entry tid instances.

Definition event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events : Assertion :=
  coq_prop (event_task_remove_multi_loop sg tasks entry tid pointers instances index events) && emp.

Definition event_task_remove_multi_selected (sg : StableGlobVars)
  (events : Glob_EventAbstractState) (pointers : list addr)
  (instances : EventTaskRemoveMultiInstances) (index eid : Z) (e : OSEventAbstractState) : Prop :=
  eid = fst (Znth index instances (0, 0%nat)) /\
  event_task_remove_multi_pointer pointers index = event_addr sg eid /\
  events.(inUsedEventStates) eid = Some e /\ event_object_layout_prop sg eid /\
  index < Zlength pointers.

Definition event_task_remove_multi_event_frame (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (events : Glob_EventAbstractState)
  (eid : EventID) (e : OSEventAbstractState) (row : Z) : Assertion :=
  event_task_remove_ecb_frame sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg tasks e) row **
  event_raw_rep_no_eid sg tasks events eid.

Definition event_task_remove_multi_tcb_reads (tcb : addr) (t : TaskAbstractState) : Assertion :=
  &(tcb # "os_tcb" ->ₛ "OSTCBY") # UChar |-> (t.(curPrio) / 8) **
  &(tcb # "os_tcb" ->ₛ "OSTCBBitX") # UChar |-> tcb_bit_x_of_prio t.(curPrio) **
  &(tcb # "os_tcb" ->ₛ "OSTCBBitY") # UChar |-> tcb_bit_y_of_prio t.(curPrio).

Definition event_task_remove_multi_post (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (events : Glob_EventAbstractState)
  (tid : TaskID) (t : TaskAbstractState) (pointers : list addr)
  (instances : EventTaskRemoveMultiInstances) (tcb base : addr) : Assertion :=
  event_task_remove_multi_tcb_reads tcb t ** event_multi_array_rep base pointers **
  event_raw_rep sg tasks (event_task_remove_multi_events events tid instances).

Lemma event_task_remove_multi_loop_start : forall sg tasks events tid t pointers instances,
  event_task_remove_multi_input sg tasks events tid t pointers instances ->
  event_task_remove_multi_loop sg tasks events tid pointers instances 0 events.
Proof.
  intros sg tasks events tid t pointers instances [_ [_ [_ [_ [_ [Hbinding [_ Hcanonical]]]]]]].
  split; [pose proof (Zlength_nonneg pointers); lia|].
  split; [exact Hbinding|]; split; [exact Hcanonical|reflexivity].
Qed.

Lemma event_task_remove_multi_skipn_head : forall (instances : EventTaskRemoveMultiInstances) index,
  0 <= index < Zlength instances ->
  skipn (Z.to_nat index) instances =
    Znth index instances (0, 0%nat) :: skipn (Z.to_nat (index + 1)) instances.
Proof.
  intros instances index Hindex.
  replace (Z.to_nat (index + 1)) with (S (Z.to_nat index)) by lia.
  assert (Hn : (Z.to_nat index < List.length instances)%nat).
  { rewrite Zlength_correct in Hindex; lia. }
  unfold Znth; remember (Z.to_nat index) as n; clear Heqn Hindex index.
  revert instances Hn; induction n; intros [|head tail] Hn; simpl in *;
    try lia; [reflexivity|apply IHn; lia].
Qed.

Lemma event_task_remove_multi_loop_step : forall sg tasks entry tid pointers instances index events eid e,
  event_task_remove_multi_loop sg tasks entry tid pointers instances index events ->
  index < Zlength pointers -> eid = fst (Znth index instances (0, 0%nat)) ->
  events.(inUsedEventStates) eid = Some e ->
  event_task_remove_multi_loop sg tasks entry tid pointers instances (index + 1)
    (update_event_field_raw events eid (event_set_wait_list e (remove_Z_eqb tid e.(waitList)))).
Proof.
  intros sg tasks entry tid pointers instances index events eid e
    [Hindex [Hbinding [Hcanonical Hcontinuation]]] Hlt Heid Hlookup.
  pose proof (Forall2_length Hbinding) as Hlength.
  assert (HlengthZ : Zlength pointers = Zlength instances) by
    (rewrite !Zlength_correct, Hlength; reflexivity).
  split; [lia|]; split.
  - rewrite <- (event_multi_remove_waiters_singleton events tid eid e Hlookup).
    apply event_multi_remove_waiters_preserves_binding; exact Hbinding.
  - split.
    + rewrite <- (event_multi_remove_waiters_singleton events tid eid e Hlookup).
      apply event_multi_remove_waiters_preserves_canonical; exact Hcanonical.
    + unfold event_task_remove_multi_events in *.
      rewrite (event_task_remove_multi_skipn_head instances index ltac:(lia)) in Hcontinuation.
      cbn [map] in Hcontinuation; rewrite <- Heid in Hcontinuation.
      rewrite (event_multi_remove_waiters_source_order events tid eid
        (map fst (skipn (Z.to_nat (index + 1)) instances)) e Hlookup) in Hcontinuation.
      exact Hcontinuation.
Qed.

Lemma event_task_remove_multi_loop_end : forall sg tasks entry tid pointers instances index events,
  event_task_remove_multi_loop sg tasks entry tid pointers instances index events ->
  index = Zlength pointers -> events = event_task_remove_multi_events entry tid instances.
Proof.
  intros sg tasks entry tid pointers instances index events [_ [Hbinding [_ Hcontinuation]]] ->.
  pose proof (Forall2_length Hbinding) as Hlength.
  rewrite Zlength_correct, Nat2Z.id, Hlength, skipn_all in Hcontinuation.
  unfold event_task_remove_multi_events in Hcontinuation; cbn [map] in Hcontinuation.
  rewrite event_multi_remove_waiters_nil in Hcontinuation; exact Hcontinuation.
Qed.

Lemma event_task_remove_multi_current_entry : forall sg tasks entry tid t base pointers instances index events,
  event_task_remove_multi_input sg tasks entry tid t pointers instances ->
  event_task_remove_multi_loop sg tasks entry tid pointers instances index events ->
  event_multi_array_valid base pointers -> Znth index (pointers ++ [0]) 0 <> 0 ->
  exists eid e, event_task_remove_multi_selected sg events pointers instances index eid e.
Proof.
  intros sg tasks entry tid t base pointers instances index events
    (_ & _ & _ & _ & _ & _ & Hlayouts & _) [Hindex [Hbinding _]] Hvalid Hnonzero.
  assert (Hlt : index < Zlength pointers).
  { destruct (Z.eq_dec index (Zlength pointers));
      [subst; rewrite event_multi_array_terminator in Hnonzero; contradiction|lia]. }
  destruct (event_multi_array_binding_index sg events pointers instances index Hbinding ltac:(lia))
    as [Haddress [e [Hlookup Hgeneration]]].
  exists (fst (Znth index instances (0, 0%nat))), e.
  split; [reflexivity|]; split; [exact Haddress|]; split; [exact Hlookup|]; split; [|exact Hlt].
  rewrite Forall_forall in Hlayouts; apply Hlayouts.
  unfold Znth; apply nth_In.
  pose proof (Forall2_length Hbinding) as Hlength.
  rewrite Zlength_correct in Hlt; lia.
Qed.

Lemma event_task_remove_multi_split_event : forall sg tasks events eid e row,
  events.(inUsedEventStates) eid = Some e -> event_object_layout_prop sg eid -> 0 <= row < 8 ->
  event_raw_rep sg tasks events |--
  (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl") + row * sizeof(UCHAR)) # UChar |->
    encode_event_wait_tbl_at_or e.(waitList) tasks row **
  &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp") # UChar |->
    encode_event_wait_grp e.(waitList) tasks **
  event_task_remove_multi_event_frame sg tasks events eid e row.
Proof.
  intros sg tasks events eid e row Hlookup [_ [Hgroup Htable]] Hrow.
  sep_apply_l_atomic (event_raw_rep_split_eid sg tasks events eid e Hlookup).
  unfold used_event_rep.
  sep_apply_l_atomic (event_task_remove_ecb_split sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg tasks e) row
    (encode_event_wait_tbl_at_or e.(waitList) tasks row)
    (encode_event_wait_grp e.(waitList) tasks) Hrow
    (event_table_image_eq sg tasks e row Hrow) eq_refl).
  unfold OSEventGrp_off, OSEventTbl_off in Hgroup, Htable.
  rewrite Hgroup, Htable, sizeof_uchar, Z.mul_1_r.
  unfold event_task_remove_multi_event_frame; entailer!.
Qed.

Lemma event_task_remove_multi_merge_event : forall sg tasks events eid e tid t,
  valid_stable_glob_vars sg -> task_priority_unique tasks ->
  event_waitList_canonical sg tasks e.(waitList) -> valid_task_prio sg t.(curPrio) ->
  tasks.(inUsedTaskStates) tid = Some t -> event_object_layout_prop sg eid -> 0 <= t.(curPrio) / 8 < 8 ->
  (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl") + t.(curPrio) / 8 * sizeof(UCHAR)) # UChar |->
    event_task_remove_cleared (encode_event_wait_tbl_at_or e.(waitList) tasks (t.(curPrio) / 8))
      (tcb_bit_x_of_prio t.(curPrio)) **
  &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp") # UChar |->
    event_task_remove_group (encode_event_wait_tbl_at_or e.(waitList) tasks (t.(curPrio) / 8))
      (encode_event_wait_grp e.(waitList) tasks)
      (tcb_bit_x_of_prio t.(curPrio)) (tcb_bit_y_of_prio t.(curPrio)) **
  event_task_remove_multi_event_frame sg tasks events eid e (t.(curPrio) / 8) |--
  event_raw_rep sg tasks
    (update_event_field_raw events eid (event_set_wait_list e (remove_Z_eqb tid e.(waitList)))).
Proof.
  intros sg tasks events eid e tid t Hsg Hunique Hcanonical Hprio Hlookup [_ [Hgroup Htable]] Hrow.
  unfold OSEventGrp_off, OSEventTbl_off in Hgroup, Htable.
  rewrite Hgroup, Htable, sizeof_uchar, Z.mul_1_r.
  unfold event_task_remove_multi_event_frame.
  pose proof (event_task_remove_ecb_merge_updated sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg tasks e) (t.(curPrio) / 8)
    (encode_event_wait_tbl_at_or e.(waitList) tasks (t.(curPrio) / 8))
    (encode_event_wait_grp e.(waitList) tasks)
    (tcb_bit_x_of_prio t.(curPrio)) (tcb_bit_y_of_prio t.(curPrio)) Hrow eq_refl) as Hmerge.
  change (tcb_bit_x_of_prio t.(curPrio)) with (Z.shiftl 1 (t.(curPrio) mod 8)) in Hmerge.
  change (tcb_bit_y_of_prio t.(curPrio)) with (Z.shiftl 1 (t.(curPrio) / 8)) in Hmerge.
  rewrite <- (event_remove_waiter_image_eq sg tasks e tid t Hsg Hunique Hcanonical Hprio Hlookup) in Hmerge.
  set (updated := event_set_wait_list e (remove_Z_eqb tid e.(waitList))).
  sep_apply_r_atomic (event_raw_rep_merge_updated_eid sg tasks events eid updated).
  unfold used_event_rep.
  sep_apply_r_atomic Hmerge.
  unfold tcb_bit_x_of_prio, tcb_bit_y_of_prio, tcb_x_of_prio, tcb_y_of_prio; entailer!.
Qed.

(** The old annotation exposed redundant logical addresses [tcb] and [base].
    Existentially hiding those exact aliases gives precisely the direct
    parameter-indexed physical footprint; no caller assumption is added. *)
Lemma event_task_remove_multi_entry_aliases_eliminate :
  forall sg tasks entry tid t pointers instances ptcb pevents_multi frame,
  (EX tcb base,
    coq_prop (ptcb = tcb /\ pevents_multi = base /\
      event_task_remove_multi_input sg tasks entry tid t pointers instances) &&
    (event_multi_array_rep base pointers ** event_raw_rep sg tasks entry **
     event_task_remove_multi_tcb_reads tcb t ** frame)) |--
  coq_prop (event_task_remove_multi_input sg tasks entry tid t pointers instances) &&
    (event_multi_array_rep pevents_multi pointers ** event_raw_rep sg tasks entry **
     event_task_remove_multi_tcb_reads ptcb t ** frame).
Proof.
  intros; Intros tcb base; Intros.
  match goal with H : ptcb = tcb /\ pevents_multi = base /\ _ |- _ =>
    destruct H as [-> [-> Hinput]] end.
  entailer!.
Qed.

Lemma event_task_remove_multi_entry_aliases_introduce :
  forall sg tasks entry tid t pointers instances ptcb pevents_multi frame,
  coq_prop (event_task_remove_multi_input sg tasks entry tid t pointers instances) &&
    (event_multi_array_rep pevents_multi pointers ** event_raw_rep sg tasks entry **
     event_task_remove_multi_tcb_reads ptcb t ** frame) |--
  (EX tcb base,
    coq_prop (ptcb = tcb /\ pevents_multi = base /\
      event_task_remove_multi_input sg tasks entry tid t pointers instances) &&
    (event_multi_array_rep base pointers ** event_raw_rep sg tasks entry **
     event_task_remove_multi_tcb_reads tcb t ** frame)).
Proof.
  intros; Exists ptcb pevents_multi; entailer!.
Qed.

Lemma event_task_remove_multi_cleared_eq_land : forall value mask,
  0 <= value < 256 ->
  event_task_remove_cleared value mask = Z.land value (Z.lnot mask).
Proof.
  intros value mask Hrange; unfold event_task_remove_cleared.
  pose proof (unsigned_last_nbits_land_distr value (Z.lnot mask) 8 ltac:(lia)) as Heq.
  rewrite (unsigned_last_nbits_eq value 8 Hrange) in Heq.
  rewrite (unsigned_last_nbits_land_missing_l value (Z.lnot mask) 8 ltac:(lia) Hrange) in Heq.
  symmetry; exact Heq.
Qed.
