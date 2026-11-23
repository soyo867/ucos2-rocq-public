Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSSemPost's OS_EventTaskRdy call updates Dly, Msg, Stat, StatPend,
    EventPtr and the wait/ready bitmaps. It does not write a task's saved
    SP, generation or parked stack bytes. Retain the existing focused map;
    do not erase its suspended-call owner into an existential stack view.
    [active] remains explicit, so this works both in a task and in an ISR. *)
Lemma sem_post_wake_preserves_call_stacks : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg entry eid event tid old focus active,
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  task_stack_live_coverage entry.(TskState) active ->
  let after := event_wake_state sg entry eid event tid old PendSem 0 PendOK in
  armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) |--
  coq_prop (task_stack_live_coverage after.(TskState) active) &&
  armv7a_task_call_stacks abi after.(TskState) focus after.(TskState).(parkedTaskStacks).
Proof.
  intros external platform port abi sg entry eid event tid old focus active Hold Hcoverage after.
  assert (Hnodes : forall slot node, after.(TskState).(inUsedTaskStates) slot = Some node ->
    exists previous, entry.(TskState).(inUsedTaskStates) slot = Some previous /\
      previous.(taskGeneration) = node.(taskGeneration) /\ previous.(tcbStkPtr) = node.(tcbStkPtr)).
  { intros slot node Hnode.
    change ((if Z.eqb slot tid then Some (task_event_wake_single old PendSem 0 PendOK)
      else entry.(TskState).(inUsedTaskStates) slot) = Some node) in Hnode.
    destruct (Z.eqb slot tid) eqn:Hslot.
    - apply Z.eqb_eq in Hslot; subst slot; injection Hnode as Hnode; subst node.
      exists old; repeat split; assumption || reflexivity.
    - exists node; repeat split; assumption || reflexivity. }
  assert (Hcovered : task_stack_live_coverage after.(TskState) active).
  { eapply task_stack_live_coverage_used_map_frame with (before := entry.(TskState));
      [|reflexivity|exact Hcoverage].
    intros slot node Hnode; destruct (Hnodes slot node Hnode) as [previous [Hprevious [Hgen Hsp]]].
    exists previous; auto. }
  assert (Htransport : armv7a_task_call_stacks abi entry.(TskState) focus
    entry.(TskState).(parkedTaskStacks) |--
    armv7a_task_call_stacks abi after.(TskState) focus after.(TskState).(parkedTaskStacks)).
  { change (armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) |--
      armv7a_task_call_stacks abi after.(TskState) focus entry.(TskState).(parkedTaskStacks)).
    apply armv7a_task_call_stacks_reindex.
    intros key payload node Hpayload Hnode Hgen; apply Hnodes; exact Hnode. }
  sep_apply_l_atomic Htransport; entailer!.
Qed.

(** Consume the actual callee postcondition and its caller-owned frame.
    This is the join immediately after OS_EventTaskRdy returns, before
    OSSemPost's Restore/OS_Sched. It does not install a stronger, unproved
    public callee contract, or assert that the woken task is running. *)
Lemma sem_post_wake_merge_call_stacks : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg entry eid event tid old priority focus active,
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid event ->
  event.(eventType) = OS_EVENT_TYPE_SEM ->
  event_task_rdy_entry sg entry.(TskState) eid event tid old ->
  task_stack_live_coverage entry.(TskState) active ->
  event_task_rdy_post sg entry.(TskState) eid event tid old 0 1 0
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
  sem_post_wake_frame sg entry eid tid **
  armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) |--
  EX after, coq_prop (sem_post_wake_result sg eid entry after priority /\
    task_stack_live_coverage after.(TskState) active) &&
  (kernel_program_inv sg after **
   armv7a_task_call_stacks abi after.(TskState) focus after.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi sg entry eid event tid old priority focus active
    Hvalid Hlookup Htype Hentry Hcoverage.
  pose proof Hentry as [_ [_ [_ [_ [_ [Hhead Hold]]]]]].
  assert (Hkind : event_type_to_pend_type event.(eventType) = Some PendSem)
    by (rewrite Htype; reflexivity).
  destruct event.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
  inversion Hhead; subst head.
  destruct (event_wake_head sg entry eid event tid tail PendSem 0 PendOK
    Hvalid Hlookup Hkind Hlist) as [found [Hfound [Hstep Hrest]]].
  assert (found = old) by congruence; subst found.
  sep_apply_l_atomic (sem_post_wake_merge_full sg entry eid event tid old priority
    Hvalid Hlookup Htype Hentry); Intros after.
  assert (Hresult : sem_post_wake_result sg eid entry after priority) by tauto.
  unfold sem_post_wake_result in Hresult; rewrite Hstep in Hresult.
  injection Hresult as Hpriority Hafter; subst after.
  pose proof (sem_post_wake_preserves_call_stacks external platform port abi sg entry eid event
    tid old focus active Hold Hcoverage) as Hstacks.
  cbn zeta in Hstacks; sep_apply_l_atomic Hstacks.
  Exists (event_wake_state sg entry eid event tid old PendSem 0 PendOK).
  rewrite kernel_program_inv_split_unmap; unfold sem_post_wake_result; entailer!.
Qed.

(** The waiting invocation need not be the waiter selected by this Post:
    another waiter may now have higher priority. Its observation follows
    the actual callee result, while its linear saved-call resource is
    retained by the preceding merge on the same heap. *)
Lemma sem_post_wake_preserves_pending_call : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg entry eid event tid old priority focus active
  waiting_id waiting waiting_event generation,
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid event ->
  event.(eventType) = OS_EVENT_TYPE_SEM ->
  event_task_rdy_entry sg entry.(TskState) eid event tid old ->
  task_stack_live_coverage entry.(TskState) active ->
  entry.(TskState).(inUsedTaskStates) waiting_id = Some waiting ->
  sem_pend_wait_continuation waiting_event generation waiting ->
  event_task_rdy_post sg entry.(TskState) eid event tid old 0 1 0
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
  sem_post_wake_frame sg entry eid tid **
  armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) |--
  EX after, EX current,
    coq_prop (sem_post_wake_result sg eid entry after priority /\
      task_stack_live_coverage after.(TskState) active /\
      after.(TskState).(inUsedTaskStates) waiting_id = Some current /\
      sem_pend_wait_continuation waiting_event generation current) &&
    (kernel_program_inv sg after **
     armv7a_task_call_stacks abi after.(TskState) focus after.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi sg entry eid event tid old priority focus active
    waiting_id waiting waiting_event generation Hvalid Hlookup Htype Hentry Hcoverage Hwaiting Hcont.
  sep_apply_l_atomic (sem_post_wake_merge_call_stacks external platform port abi sg entry eid event
    tid old priority focus active Hvalid Hlookup Htype Hentry Hcoverage); Intros after.
  assert (Hstep : event_task_rdy sg entry eid PendSem 0 PendOK = Some (priority, after)) by tauto.
  destruct (sem_pend_event_task_rdy_projection sg entry eid PendOK priority after waiting_id waiting
    Hstep ltac:(discriminate) Hwaiting) as [current [Hcurrent Htrace]].
  assert (Hcontinuation : sem_pend_wait_continuation waiting_event generation current)
    by (eapply sem_pend_wait_trace_preserves_continuation; eassumption).
  Exists after current; entailer!.
Qed.
