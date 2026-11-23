Require Import Coq.ZArith.ZArith.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_entry_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_unlock_fields_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_callback_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_return_facts_spec.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.kernel_runtime_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.timer.
Import TaskStateDef.
Local Open Scope Z_scope.

(** Current observations at an actual iteration boundary.  The signal may
    be NULL, FREE or of another public type, as in sem_pend_call_input.
    This predicate does not quantify over future calls or callback outcomes.
    The loop must re-establish it after its actual Unlock return. *)
Definition tmr_task_fields_iteration_entry critical sg call state : Prop :=
  tmr_task_unlock_entry sg call state /\
  os_sched_task_current_ready call state /\
  exists eid observed,
    sem_pend_call_input critical sg call.(os_sched_call_invocation)
      state.(TimerState).(timerSignalSem) state eid observed.

Lemma tmr_task_fields_iteration_pend_entry : forall environment critical sg call state,
  tmr_task_fields_iteration_entry critical sg call state ->
  exists eid observed, tmr_task_fields_entry environment critical sg call state eid observed.
Proof.
  intros environment critical sg call state
    [[Hsource [Havailable [Hrunning [Hcurrent [Hidle Hclear]]]]]
     [Hready [eid [observed Hsignal]]]].
  exists eid, observed; eapply tmr_task_fields_entry_task_boundary.
  - exact Hsignal.
  - eapply tmr_task_fields_caller_clear_pend_stage; eassumption.
  - intros _; exact Hidle.
  - exact Havailable.
Qed.

(** Initial publication/start and the actual Pend return already produce
    a task stage.  Its live node and generation supply current readiness;
    the multi-pointer observation comes from that node's C representation. *)
Lemma tmr_task_fields_iteration_entry_from_task_stage :
  forall critical sg call state eid observed,
  sem_pend_task_call_stage sg call state ->
  kernel_running_idle_ready sg state -> kernel_call_stack_available call state ->
  (forall node, state.(TskState).(inUsedTaskStates)
      call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
      node.(tcbEventMultiPtr) = 0) ->
  sem_pend_call_input critical sg call.(os_sched_call_invocation)
    state.(TimerState).(timerSignalSem) state eid observed ->
  tmr_task_fields_iteration_entry critical sg call state.
Proof.
  intros critical sg call state eid observed Hstage Hidle Havailable Hpointer Hsignal.
  pose proof (tmr_task_fields_caller_clear_from_pend sg call state Hstage Hpointer) as Hclear.
  destruct Hstage as [Hsource [Hrunning [node [Hready [Hgeneration Hrest]]]]].
  assert (Hcurrent : os_sched_task_current_ready call state).
  { exists node; exact (conj Hready Hgeneration). }
  split.
  - unfold tmr_task_unlock_entry.
    split; [exact Hsource|]. split; [exact Havailable|].
    split; [exact Hrunning|].
    split.
    + exact (SchedulerReturnFacts.os_sched_task_current_ready_current_consistency
        call state Hcurrent).
    + split; [apply Hidle; exact Hrunning|exact Hclear].
  - split; [exact Hcurrent|]. exists eid, observed; exact Hsignal.
Qed.

(** This consumes the observations of one completed call, including its
    actual public signal slot.  It does not assert that a generic history
    or a callback supplies those observations; their source proofs remain
    obligations at the corresponding C return. *)
Lemma tmr_task_fields_iteration_entry_from_return :
  forall critical sg original before returned current eid observed,
  kernel_call_normal_return original before returned current ->
  kernel_call_stack_available original before ->
  kernel_call_task_source returned current ->
  current.(SchedState).(isRunning) = true ->
  os_sched_task_current_ready returned current ->
  task_idle_ready sg current.(TskState) ->
  tmr_task_fields_caller_clear sg returned current ->
  sem_pend_call_input critical sg returned.(os_sched_call_invocation)
    current.(TimerState).(timerSignalSem) current eid observed ->
  tmr_task_fields_iteration_entry critical sg returned current.
Proof.
  intros critical sg original before returned current eid observed Hnormal
    Havailable Hsource Hrunning Hready Hidle Hclear Hsignal.
  split.
  - unfold tmr_task_unlock_entry.
    split; [exact Hsource|].
    split; [apply (proj2 Hnormal); exact Havailable|].
    split; [exact Hrunning|].
    split.
    + exact (SchedulerReturnFacts.os_sched_task_current_ready_current_consistency
        returned current Hready).
    + exact (conj Hidle Hclear).
  - split; [exact Hready|]. exists eid, observed; exact Hsignal.
Qed.
