Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.VC.code.event.spec.event_pend_multi_task_storage_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** The C tail does not store Dly, EventPtr, stack fields or profiling fields.
    They remain in the configured TCB residual with their original values. *)
Lemma event_pend_multi_cleanup_rest_unchanged : forall sg tid task,
  event_pend_multi_tcb_rest sg tid task event_pend_multi_resume_fields =
  event_pend_multi_tcb_rest sg tid (task_multi_cleanup task) event_pend_multi_resume_fields.
Proof.
  intros; unfold event_pend_multi_tcb_rest, TaskFieldStorage.store_fields.
  f_equal; apply functional_extensionality; intros [field| | | | | | |];
    try destruct field; reflexivity.
Qed.

Lemma event_pend_multi_cleanup_storage_merge : forall sg tid task,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = true ->
  sg.(osKernelConfig).(cfgTaskProfile) = true ->
  let tcb := task_slot_addr sg tid in
  &(tcb # "os_tcb" ->ₛ "OSTCBStat") # UChar |-> 0 **
  &(tcb # "os_tcb" ->ₛ "OSTCBStatPend") # UChar |-> 0 **
  &(tcb # "os_tcb" ->ₛ "OSTCBEventMultiPtr") # Ptr |-> 0 **
  &(tcb # "os_tcb" ->ₛ "OSTCBEventMultiRdy") # Ptr |-> 0 **
  &(tcb # "os_tcb" ->ₛ "OSTCBMsg") # Ptr |-> 0 **
  event_task_remove_multi_tcb_reads tcb task **
  event_pend_multi_tcb_rest sg tid task event_pend_multi_resume_fields |--
  used_task_rep sg tid (task_multi_cleanup task).
Proof.
  intros sg tid task Hmulti Hprofile; cbn zeta.
  rewrite event_pend_multi_cleanup_rest_unchanged.
  rewrite (event_pend_multi_task_storage_resume_equiv sg tid
    (task_multi_cleanup task) Hmulti Hprofile).
  unfold event_pend_multi_resume_deferred_cells,
    event_pend_multi_resume_deferred_without_message,
    event_pend_multi_task_pend_status, event_pend_multi_task_status,
    event_pend_multi_task_multi_pointer, event_pend_multi_task_ready_pointer,
    event_pend_multi_task_message.
  change (event_task_remove_multi_tcb_reads (task_slot_addr sg tid) (task_multi_cleanup task))
    with (event_task_remove_multi_tcb_reads (task_slot_addr sg tid) task).
  cbn [task_multi_cleanup task_set_multi_fields task_clear_pend_status_message
    task_clear_pend_status stat statPend tcbEventMultiPtr eventMultiRdy msg
    encode_pend_status encode_task_status encode_event_link encode_msg].
  change (encode_task_status Byte.zero) with 0.
  entailer!.
Qed.

(** Only the abstract update of a missing logical slot is an identity here.
    This does not authorize the C helper to dereference a private/free slot. *)
Lemma event_pend_multi_remove_missing_head_eq : forall events tid eid ids,
  events.(inUsedEventStates) eid = None ->
  event_multi_remove_waiters events tid (eid :: ids) =
  event_multi_remove_waiters events tid ids.
Proof.
  intros [used free bytes life] tid eid ids Hmissing.
  cbn [inUsedEventStates] in Hmissing.
  unfold event_multi_remove_waiters;
    cbn [inUsedEventStates eventLifecycle publishedQueueBytes unUsedEventStates].
  f_equal; apply functional_extensionality; intro slot.
  destruct (Z.eq_dec slot eid) as [-> | Hne]; [rewrite Hmissing; reflexivity|].
  destruct (used slot); [|reflexivity].
  destruct (in_dec Z.eq_dec slot (eid :: ids)); destruct (in_dec Z.eq_dec slot ids);
    try reflexivity; exfalso; cbn in *; intuition congruence.
Qed.

Lemma event_pend_multi_remove_waiters_queue_storage : forall sg events tid ids,
  queue_storage_rep sg events |--
  queue_storage_rep sg (event_multi_remove_waiters events tid ids).
Proof.
  intros sg events tid ids; revert events.
  induction ids as [|eid ids IH]; intro events.
  - rewrite event_multi_remove_waiters_nil; entailer!.
  - destruct (events.(inUsedEventStates) eid) as [node|] eqn:Hnode.
    + rewrite (event_multi_remove_waiters_source_order events tid eid ids node Hnode).
      sep_apply_l_atomic (queue_event_update_preserves_storage sg events eid node
        (event_set_wait_list node (remove_Z_eqb tid node.(waitList))) Hnode eq_refl eq_refl).
      apply IH.
    + rewrite (event_pend_multi_remove_missing_head_eq events tid eid ids Hnode); apply IH.
Qed.

(** Complete raw heap from the final source stores. Invariant closure is a
    separate obligation: no Dly, readiness or registration fact is assumed. *)
Lemma event_pend_multi_cleanup_raw_merge : forall sg state tid task ids,
  UCOS2_full_state_inv sg state ->
  event_pend_multi_task_selected sg state tid task ->
  event_pend_multi_resumed_error sg state task <> 1 ->
  let tcb := task_slot_addr sg tid in
  sg.(g_OSTCBCur) # Ptr |-> tcb **
  &(tcb # "os_tcb" ->ₛ "OSTCBStat") # UChar |-> 0 **
  &(tcb # "os_tcb" ->ₛ "OSTCBStatPend") # UChar |-> 0 **
  &(tcb # "os_tcb" ->ₛ "OSTCBEventMultiPtr") # Ptr |-> 0 **
  &(tcb # "os_tcb" ->ₛ "OSTCBEventMultiRdy") # Ptr |-> 0 **
  &(tcb # "os_tcb" ->ₛ "OSTCBMsg") # Ptr |-> 0 **
  event_task_remove_multi_tcb_reads tcb task **
  event_pend_multi_task_frame sg state tid task event_pend_multi_resume_fields **
  event_raw_rep sg state.(TskState) (event_pend_multi_resumed_events sg state tid task ids) |--
  UCOS2_raw_rep sg (event_pend_multi_resumed_state sg state tid task ids).
Proof.
  intros sg state tid task ids Hvalid [Hcurrent [Htask Hrow]] Herror; cbn zeta.
  pose proof Hvalid as [Hprofile _].
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = true)
    by (unfold full_features_kernel_profile in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = true)
    by (unfold full_features_kernel_profile in Hprofile; tauto).
  set (tasks := glob_task_set_usedtask state.(TskState) tid (task_multi_cleanup task)).
  assert (Hpriority : forall slot, option_map curPrio (state.(TskState).(inUsedTaskStates) slot) =
    option_map curPrio (tasks.(inUsedTaskStates) slot)).
  { intro slot; symmetry; apply (glob_task_set_usedtask_observation _ curPrio _ tid task);
      [exact Htask|reflexivity]. }
  assert (Hevent : event_raw_rep sg state.(TskState) (event_pend_multi_resumed_events sg state tid task ids) =
    event_raw_rep sg tasks (event_pend_multi_resumed_events sg state tid task ids)).
  { apply event_raw_rep_change_task_index, event_wait_priority_agreement_encodes.
    intros eid node slot Hnode Hin; apply Hpriority. }
  assert (Hsched : sched_raw_rep sg state.(TskState) state.(SchedState) =
    sched_raw_rep sg tasks state.(SchedState)).
  { apply sched_raw_rep_priority_ext; intros slot Hin; apply Hpriority. }
  assert (Hcurrent_merge : sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
      event_pend_multi_sched_without_current sg state |--
      sched_raw_rep sg state.(TskState) state.(SchedState)).
  { unfold event_pend_multi_sched_without_current, sched_raw_rep, sched_physical_rep.
    rewrite Hcurrent; cbn [encode_task_link]; entailer!. }
  assert (Hqueue : queue_storage_rep sg state.(EventState) |--
    queue_storage_rep sg (event_pend_multi_resumed_events sg state tid task ids)).
  { unfold event_pend_multi_resumed_events; destruct (event_pend_multi_remove_needed sg task);
      [apply event_pend_multi_remove_waiters_queue_storage|entailer!]. }
  unfold event_pend_multi_task_frame, UCOS2_raw_rep_missing_task_storage_sched_event.
  sepcon_right_assoc.
  pose proof (event_pend_multi_cleanup_storage_merge sg tid task Hmulti Hprofiling) as Hstorage.
  cbn zeta in Hstorage; sep_apply_l_atomic Hstorage.
  sep_apply_l_atomic (task_public_storage_merge_updated_task sg state.(TskState) tid
    (task_multi_cleanup task)).
  sep_apply_l_atomic Hcurrent_merge; sep_apply_l_atomic Hqueue.
  rewrite Hevent, Hsched.
  unfold event_pend_multi_resumed_state; rewrite (proj2 (Z.eqb_neq _ _) Herror).
  unfold UCOS2_raw_rep, task_shared_rep; fold (event_pend_multi_resumed_events sg state tid task ids).
  cbn [replace_TskS replace_EventS TskState SchedState EventState IntrState TickState
    FlagState MemoryState TimerState StatsState ControlState NameState glob_task_set_usedtask parkedTaskStacks].
  fold tasks; entailer!.
Qed.
