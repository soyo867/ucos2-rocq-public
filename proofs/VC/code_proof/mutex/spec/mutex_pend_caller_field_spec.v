Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_storage Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSMutexPend compares the owner's base priority with OSTCBCur->OSTCBPrio
    while the owner's complete TCB is already focused.  This residual moves
    only the distinct caller's priority byte out of that existing frame.
    It changes neither the abstract Task state nor the owned owner TCB. *)
Definition mutex_pend_caller_priority_frame (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) (owner caller : TaskID)
  (node : TaskAbstractState) : Assertion :=
  tcb64_storage_without (task_slot_addr sg caller) TCBPrio (task_tcb64_image sg node) **
  store_map_missing_i (used_task_rep sg)
    (kernel_map_set entry.(TskState).(inUsedTaskStates) owner None) caller **
  task_free_storage_rep sg entry.(TskState).(taskLifecycle).(taskFreeStorage)
    entry.(TskState).(unUsedTaskStates) **
  sg.(g_OSTCBFreeList) # Ptr |-> encode_task_link sg (hd_error entry.(TskState).(unUsedTaskStates)) **
  sg.(g_OSTCBList) # Ptr |-> encode_task_link sg entry.(TskState).(tcbListHead) **
  sg.(g_OSTaskCtr) # UChar |-> entry.(TskState).(taskCount) **
  task_reg_allocator_rep sg entry.(TskState) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte entry.(SchedState).(highRdyPrio) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg entry.(SchedState).(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> entry.(SchedState).(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if entry.(SchedState).(isRunning) then 1 else 0) **
  UCOS2_raw_rep_missing_task_storage_sched sg entry.

Lemma mutex_pend_non_owner_of_holds_no_mutex : forall events caller eid event mutex owner,
  task_holds_no_mutex events caller ->
  events.(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> caller <> owner.
Proof.
  intros events caller eid event mutex owner Hnone He Htype Hfields Howner Heq.
  subst owner; exact (Hnone eid event mutex He Htype Hfields Howner).
Qed.

Lemma mutex_del_priority_frame_split_caller_prio : forall sg entry owner caller node,
  selected_kernel_profile sg -> caller <> owner ->
  entry.(TskState).(inUsedTaskStates) caller = Some node ->
  mutex_del_priority_frame sg entry owner |--
    tcb_field_address (task_slot_addr sg caller) TCBPrio # UChar |-> node.(curPrio) **
    mutex_pend_caller_priority_frame sg entry owner caller node.
Proof.
  intros sg entry owner caller node Hprofile Hdifferent Hnode.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hoff : forall tid, tid <> owner ->
    entry.(TskState).(inUsedTaskStates) tid =
    kernel_map_set entry.(TskState).(inUsedTaskStates) owner None tid).
  { intros tid Hne; rewrite kernel_map_set_other by exact Hne; reflexivity. }
  assert (Hcaller : kernel_map_set entry.(TskState).(inUsedTaskStates) owner None caller = Some node).
  { rewrite kernel_map_set_other by exact Hdifferent; exact Hnode. }
  unfold mutex_del_priority_frame.
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv (used_task_rep sg) _ _ owner Hoff)).
  sep_apply_l_atomic (store_map_missing_equiv_store_map (used_task_rep sg) _ owner
    (kernel_map_set_same _ entry.(TskState).(inUsedTaskStates) owner None)).
  sep_apply_l_atomic (store_map_split (used_task_rep sg) caller node _ Hcaller).
  rewrite used_task_rep_tcb64, <- task_slot_addr_tcb64 by assumption.
  sep_apply_l_atomic (tcb64_storage_split (task_slot_addr sg caller)
    (task_tcb64_image sg node) TCBPrio).
  unfold mutex_pend_caller_priority_frame; cbn [tcb_cell task_tcb64_image].
  entailer!.
Qed.

Lemma mutex_del_priority_frame_merge_caller_prio : forall sg entry owner caller node,
  selected_kernel_profile sg -> caller <> owner ->
  entry.(TskState).(inUsedTaskStates) caller = Some node ->
  tcb_field_address (task_slot_addr sg caller) TCBPrio # UChar |-> node.(curPrio) **
    mutex_pend_caller_priority_frame sg entry owner caller node |--
  mutex_del_priority_frame sg entry owner.
Proof.
  intros sg entry owner caller node Hprofile Hdifferent Hnode.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hoff : forall tid, tid <> owner ->
    entry.(TskState).(inUsedTaskStates) tid =
    kernel_map_set entry.(TskState).(inUsedTaskStates) owner None tid).
  { intros tid Hne; rewrite kernel_map_set_other by exact Hne; reflexivity. }
  assert (Hcaller : kernel_map_set entry.(TskState).(inUsedTaskStates) owner None caller = Some node).
  { rewrite kernel_map_set_other by exact Hdifferent; exact Hnode. }
  unfold mutex_pend_caller_priority_frame.
  pose proof (tcb64_storage_merge (task_slot_addr sg caller)
    (task_tcb64_image sg node) TCBPrio) as Hmerge.
  cbn [tcb_cell task_tcb64_image] in Hmerge.
  sep_apply_l_atomic Hmerge.
  rewrite task_slot_addr_tcb64 by assumption.
  rewrite <- used_task_rep_tcb64 by assumption.
  sep_apply_l_atomic (store_map_merge (used_task_rep sg) caller node _ Hcaller).
  sep_apply_l_atomic (store_map_equiv_store_map_missing (used_task_rep sg) _ owner
    (kernel_map_set_same _ entry.(TskState).(inUsedTaskStates) owner None)).
  sep_apply_l_atomic (proj2 (store_map_missing_i_equiv (used_task_rep sg) _ _ owner Hoff)).
  unfold mutex_del_priority_frame; entailer!.
Qed.
