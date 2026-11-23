Require Import Coq.Lists.List Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.VC.code.event.spec.event_pend_multi_wake_full_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_full_spec.
Require Import Ucos2Verify.lib.atomic_ops_lib Ucos2Verify.lib.event_registration.
Import ListNotations TaskStateDef EventStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma event_pend_multi_wake_preserves_residual :
  forall sg state tid task selected kind message result,
  UCOS2_raw_rep_missing_task_storage_sched_event sg state |--
  UCOS2_raw_rep_missing_task_storage_sched_event sg
    (event_multi_wake_state sg state tid task selected kind message result
      (event_multi_remove_waiters state.(EventState) tid (selected :: task.(eventMultiWaitEvents)))).
Proof.
  intros; unfold UCOS2_raw_rep_missing_task_storage_sched_event, event_multi_wake_state.
  cbn [replace_SchedS replace_TskS replace_EventS IntrState EventState TickState FlagState
    MemoryState TimerState StatsState ControlState NameState TskState glob_task_set_usedtask parkedTaskStacks].
  sep_apply_l_atomic (event_pend_multi_remove_waiters_queue_storage sg state.(EventState)
    tid (selected :: task.(eventMultiWaitEvents))); entailer!.
Qed.

(** Frame of the actual internal callee: its selected TCB, all ECBs,
    priority table and ready bitmap are absent here. The borrowed array
    and read-only unmap table are supplied and returned by its caller. *)
Definition event_pend_multi_wake_callee_frame sg state tid : Assertion :=
  store_map_missing_i (used_task_rep sg) state.(TskState).(inUsedTaskStates) tid **
  task_free_storage_rep sg state.(TskState).(taskLifecycle).(taskFreeStorage)
    state.(TskState).(unUsedTaskStates) **
  sg.(g_OSTCBFreeList) # Ptr |-> encode_task_link sg (hd_error state.(TskState).(unUsedTaskStates)) **
  sg.(g_OSTCBList) # Ptr |-> encode_task_link sg state.(TskState).(tcbListHead) **
  sg.(g_OSTaskCtr) # UChar |-> state.(TskState).(taskCount) **
  task_reg_allocator_rep sg state.(TskState) **
  sched_physical_rep sg state.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg state.

Lemma event_pend_multi_wake_callee_frame_split : forall sg state tid task,
  full_features_kernel_profile sg -> state.(TskState).(inUsedTaskStates) tid = Some task ->
  UCOS2_raw_rep sg state |--
  tcb_configured_storage_rep true true (task_slot_addr sg tid) (task_layout_image sg task) **
  event_raw_rep sg state.(TskState) state.(EventState) **
  store_prio_tbl sg state.(TskState).(prioTbl) **
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
  UCharArray.full sg.(g_OSRdyTbl) 8 (sched_row_values state.(TskState) state.(SchedState).(readyList)) **
  event_pend_multi_wake_callee_frame sg state tid.
Proof.
  intros sg state tid task Hprofile Htask.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = true)
    by (unfold full_features_kernel_profile in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = true)
    by (unfold full_features_kernel_profile in Hprofile; tauto).
  unfold UCOS2_raw_rep, task_shared_rep.
  sep_apply_l_atomic (task_public_storage_split_task sg state.(TskState) tid task Htask).
  unfold used_task_rep, task_slot_storage_rep; rewrite Hmulti, Hprofiling.
  unfold sched_raw_rep; rewrite sched_rows_array_equiv.
  unfold event_pend_multi_wake_callee_frame, task_public_storage_without_task,
    task_public_storage_without_used_map, UCOS2_raw_rep_missing_task_storage_sched_event.
  entailer!.
Qed.

Lemma event_pend_multi_wake_callee_frame_task_merge : forall sg state tid written,
  full_features_kernel_profile sg ->
  tcb_configured_storage_rep true true (task_slot_addr sg tid) (task_layout_image sg written) **
  store_prio_tbl sg state.(TskState).(prioTbl) **
  event_pend_multi_wake_callee_frame sg state tid |--
  task_public_storage sg (glob_task_set_usedtask state.(TskState) tid written) **
  sched_physical_rep sg state.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg state.
Proof.
  intros sg state tid written Hprofile.
  assert (Hstorage : tcb_configured_storage_rep true true (task_slot_addr sg tid)
      (task_layout_image sg written) = used_task_rep sg tid written).
  { unfold used_task_rep, task_slot_storage_rep.
    assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = true)
      by (unfold full_features_kernel_profile in Hprofile; tauto).
    assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = true)
      by (unfold full_features_kernel_profile in Hprofile; tauto).
    rewrite Hmulti, Hprofiling; reflexivity. }
  rewrite Hstorage; unfold event_pend_multi_wake_callee_frame.
  sepcon_assoc_change.
  sep_apply_r_atomic (task_public_storage_merge_updated_task sg state.(TskState) tid written).
  unfold task_public_storage_without_task, task_public_storage_without_used_map; entailer!.
Qed.

(** The updated Task/Scheduler heaps are real inputs to this merge. The
    pure theorem above is not used to synthesize their bytes. ECB bitmaps
    may still be indexed by the pre-wake Task map because priority is
    unchanged by these source stores. *)
Lemma event_pend_multi_wake_full_merge :
  forall sg state tid task selected node kind message result,
  UCOS2_full_state_inv sg state ->
  state.(TskState).(inUsedTaskStates) tid = Some task -> task.(tcbEventMultiPtr) <> 0 ->
  state.(EventState).(inUsedEventStates) selected = Some node -> In tid node.(waitList) ->
  event_type_to_pend_type node.(eventType) = Some kind ->
  (result = PendOK \/ result = PendAbort) ->
  let after := event_multi_wake_state sg state tid task selected kind message result
    (event_multi_remove_waiters state.(EventState) tid (selected :: task.(eventMultiWaitEvents))) in
  task_public_storage sg after.(TskState) **
  sched_raw_rep sg after.(TskState) after.(SchedState) **
  event_raw_rep sg state.(TskState) after.(EventState) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg state |-- UCOS2_full_inv sg after.
Proof.
  intros sg state tid task selected node kind message result Hvalid Htask Hlinked Hnode Hin Hkind Hresult after.
  pose proof (event_pend_multi_wake_preserves_full_state sg state tid task selected node kind message result
    Hvalid Htask Hlinked Hnode Hin Hkind Hresult) as Hafter; fold after in Hafter.
  assert (Hindex : event_raw_rep sg state.(TskState) after.(EventState) =
    event_raw_rep sg after.(TskState) after.(EventState)).
  { apply event_raw_rep_change_task_index, event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Htask|reflexivity]. }
  rewrite Hindex.
  sep_apply_l_atomic (event_pend_multi_wake_preserves_residual sg state tid task selected kind message result).
  fold after.
  unfold UCOS2_full_inv, UCOS2_raw_rep, UCOS2_raw_rep_missing_task_storage_sched,
    UCOS2_raw_rep_missing_task_storage_sched_event, task_shared_rep; entailer!.
Qed.

Lemma event_pend_multi_wake_ready_merge : forall sg tasks sched tid task selected kind message result,
  tasks.(inUsedTaskStates) tid = Some task -> 0 <= task.(curPrio) < 64 ->
  event_task_rdy_full_ready sg task (task_pend_mask kind)
    (encode_ready_grp sched.(readyList) tasks) (sched_row_values tasks sched.(readyList)) **
  sched_physical_rep sg sched |--
  sched_raw_rep sg
    (glob_task_set_usedtask tasks tid (task_multi_wake task kind message result selected))
    (sched_wake_by_status sg tasks sched tid
      (encode_task_status (task_multi_wake task kind message result selected).(stat))).
Proof.
  intros sg tasks sched tid task selected kind message result Htask Hpriority.
  set (written := task_multi_wake task kind message result selected).
  set (after := sched_wake_by_status sg tasks sched tid
    (encode_task_status written.(stat))).
  assert (HpriorityIndex : sched_raw_rep sg tasks after =
    sched_raw_rep sg (glob_task_set_usedtask tasks tid written) after).
  { apply sched_raw_rep_priority_ext; intros slot Hin.
    symmetry; apply (glob_task_set_usedtask_observation _ curPrio _ tid task);
      [exact Htask|reflexivity]. }
  rewrite <- HpriorityIndex.
  assert (Hstatus : encode_task_status written.(stat) =
    task_status_clear_wait (encode_task_status task.(stat)) (task_pend_mask kind)).
  { apply task_clear_pending_status_encoding. }
  unfold event_task_rdy_full_ready.
  rewrite (event_task_rdy_scheduler_group_eq sg tasks sched tid task _ Htask),
    (event_task_rdy_scheduler_rows_eq sg tasks sched tid task _ Htask Hpriority).
  unfold after; rewrite Hstatus.
  unfold sched_raw_rep; rewrite sched_wake_by_status_physical_rep_eq, sched_rows_array_equiv.
  entailer!.
Qed.

(** Consume the verified full-layout callee's exact post, not a desired
    whole-kernel postcondition. Names/Profile bytes stay in the configured
    owner; the unchanged borrowed array and unmap table are returned. *)
Lemma event_pend_multi_wake_callee_post_merge :
  forall sg state selected node tid task pointers instances kind message result returned,
  UCOS2_full_state_inv sg state ->
  event_task_rdy_full_entry sg state.(TskState) state.(EventState)
    selected node tid task pointers instances ->
  task.(tcbEventMultiPtr) <> 0 -> task.(eventMultiWaitEvents) = map fst instances ->
  event_type_to_pend_type node.(eventType) = Some kind ->
  (result = PendOK \/ result = PendAbort) ->
  let after := event_multi_wake_state sg state tid task selected kind message result
    (event_multi_remove_waiters state.(EventState) tid (selected :: task.(eventMultiWaitEvents))) in
  event_task_rdy_full_post sg state.(TskState) state.(EventState) selected node tid task
    pointers instances message (task_pend_mask kind) (encode_pend_status result)
    (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
    (sched_row_values state.(TskState) state.(SchedState).(readyList)) returned **
  event_pend_multi_wake_callee_frame sg state tid |--
  coq_prop (returned = task.(curPrio)) &&
  (UCOS2_full_inv sg after ** event_multi_array_rep task.(tcbEventMultiPtr) pointers ** unmap_table_rep sg).
Proof.
  intros sg state selected node tid task pointers instances kind message result returned
    Hvalid Hentry Hlinked Hids Hkind Hresult after.
  pose proof Hentry as [Hprofile [_ [Hnode [_ [_ [Hhead [Htask _]]]]]]].
  pose proof (event_task_rdy_full_selection sg state.(TskState) state.(EventState)
    selected node tid task pointers instances Hentry) as [_ [_ [_ [Hpriority _]]]].
  assert (Hin : In tid node.(waitList)).
  { destruct node.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
    injection Hhead as <-; left; reflexivity. }
  sep_apply_l_atomic (event_pend_multi_wake_source_post_image sg state.(TskState) state.(EventState)
    selected node tid task pointers instances kind message result
    (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
    (sched_row_values state.(TskState) state.(SchedState).(readyList)) returned Hnode Hlinked Hids).
  Intros; sepcon_right_assoc.
  sep_apply_l_atomic (event_pend_multi_wake_callee_frame_task_merge sg state tid
    (task_multi_wake task kind message result selected) Hprofile).
  sep_apply_l_atomic (event_pend_multi_wake_ready_merge sg state.(TskState) state.(SchedState)
    tid task selected kind message result Htask Hpriority).
  pose proof (event_pend_multi_wake_full_merge sg state tid task selected node kind message result
    Hvalid Htask Hlinked Hnode Hin Hkind Hresult) as Hmerge; cbn zeta in Hmerge.
  cbn [event_multi_wake_state replace_SchedS replace_TskS replace_EventS
    TskState SchedState EventState] in Hmerge.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.
