Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_wrapper_completion_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_returned_c_segment_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Import SelectedIRQWrapperCompletion SelectedIRQWrapperSegment OSIntExitReturnedC.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** These are consequences of the existing post-acquire C/port modules.
    They do not describe the earlier interruptible acquisition interval,
    and deliberately omit the parked map, high cache and interrupt counters. *)
Record sem_pend_irq_structural_frame (entry current : UCOS2_Verify_State) : Prop := {
  sem_pend_irq_cut_tasks : current.(TskState).(inUsedTaskStates) = entry.(TskState).(inUsedTaskStates);
  sem_pend_irq_cut_lifecycle : current.(TskState).(taskLifecycle) = entry.(TskState).(taskLifecycle);
  sem_pend_irq_cut_events : current.(EventState) = entry.(EventState);
  sem_pend_irq_cut_names : current.(NameState) = entry.(NameState);
  sem_pend_irq_cut_timers : current.(TimerState) = entry.(TimerState);
  sem_pend_irq_cut_running : current.(SchedState).(isRunning) = entry.(SchedState).(isRunning);
  sem_pend_irq_cut_current : current.(SchedState).(curTaskID) = entry.(SchedState).(curTaskID);
  sem_pend_irq_cut_priority : current.(SchedState).(curSchedPrio) = entry.(SchedState).(curSchedPrio)
}.

Definition sem_pend_irq_cut_preserves (property : UCOS2_Verify_State -> Prop) : Prop :=
  forall entry current, sem_pend_irq_structural_frame entry current ->
    property entry -> property current.

(** Each constructor retains the actual completion and its original heaps,
    input/output resources, descriptor and acquired cut. The Returned module
    starts at [entry]; its earlier observed-to-entry run must still be composed
    by the caller. No architecture-source field is added to the existing ABI. *)
Inductive sem_pend_irq_completion_source environment critical sg :
  TaskInvocationOrigin -> UCOS2_Verify_State -> model -> Assertion ->
  TaskInvocationOrigin -> UCOS2_Verify_State -> model -> Assertion -> Prop :=
| SemPendIRQWrapperCompletion : forall first state local suspended receipt original node handler frame before after,
    irq_wrapper_c_completion environment sg state local suspended receipt original node handler frame before after ->
    sem_pend_irq_completion_source environment critical sg first state before
      (irq_wrapper_c_input environment sg state local suspended receipt handler frame)
      (RunningInvocation suspended.(armv7a_continuation_stack).(stackLeaseSlot)
        suspended.(armv7a_continuation_stack).(stackLeaseGeneration))
      (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) after
      (irq_wrapper_c_output environment sg state local suspended receipt original handler frame)
| SemPendIRQReturnedCompletion : forall first observed read_heap observation_frame entry local suspended receipt
    original node handler frame before middle after,
    os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
      entry local suspended receipt original node handler frame before middle after ->
    sem_pend_irq_completion_source environment critical sg first entry before
      (os_int_exit_returned_c_input environment sg entry local suspended receipt handler frame)
      (RunningInvocation suspended.(armv7a_continuation_stack).(stackLeaseSlot)
        suspended.(armv7a_continuation_stack).(stackLeaseGeneration))
      (os_int_exit_wrapper_restored_state (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
        suspended.(armv7a_continuation_stack)) after
      (irq_wrapper_c_output environment sg (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
        local suspended receipt original handler (unmap_table_rep sg ** frame)).

Lemma sem_pend_irq_completion_source_resources : forall environment critical sg first state before input last current after output,
  sem_pend_irq_completion_source environment critical sg first state before input last current after output ->
  input before /\ output after.
Proof.
  intros until output; intro Hcompletion; destruct Hcompletion.
  - eapply irq_wrapper_c_completion_resources; exact H.
  - eapply os_int_exit_returned_c_completion_resources; exact H.
Qed.

Lemma sem_pend_irq_wrapper_step_source : forall environment critical sg state before input stopped current after output
  (step : irq_wrapper_c_step environment sg state before input stopped current after output) first,
  stopped = false /\ exists last,
    sem_pend_irq_completion_source environment critical sg first state before input last current after output.
Proof.
  intros until first; destruct step; split; [reflexivity|].
  eexists; eapply SemPendIRQWrapperCompletion; exact H.
Qed.

Lemma sem_pend_irq_returned_step_source : forall environment critical sg state before input stopped current after output
  (step : os_int_exit_returned_c_step environment critical sg state before input stopped current after output) first,
  stopped = false /\ exists last,
    sem_pend_irq_completion_source environment critical sg first state before input last current after output.
Proof.
  intros until first; destruct step; split; [reflexivity|].
  eexists; eapply SemPendIRQReturnedCompletion; exact H.
Qed.

Lemma sem_pend_irq_completion_source_frame : forall environment critical sg first state before input last current after output,
  sem_pend_irq_completion_source environment critical sg first state before input last current after output ->
  sem_pend_irq_structural_frame state current.
Proof.
  intros until output; intro Hcompletion; destruct Hcompletion.
  - constructor; reflexivity.
  - destruct (os_int_exit_checkpoint_current_frame observed.(SchedState).(isRunning) entry)
      as [Hcurrent [Hpriority Hrunning]].
    constructor; try exact Hcurrent; try exact Hpriority; try exact Hrunning;
      destruct observed.(SchedState).(isRunning); reflexivity.
Qed.

Lemma sem_pend_irq_completion_source_preserves_current :
  forall environment critical sg first state before input last current after output,
  sem_pend_irq_completion_source environment critical sg first state before input last current after output ->
  task_execution_current last current.
Proof.
  intros until output; intro Hcompletion; destruct Hcompletion.
  - exact (irq_wrapper_c_current _ _ _ _ _ _ _ _ _ _ _ _ H).
  - pose proof (os_int_exit_returned_c_completion_wrapper _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as Hwrapper.
    exact (irq_wrapper_c_current _ _ _ _ _ _ _ _ _ _ _ _ Hwrapper).
Qed.

Lemma sem_pend_irq_completion_source_preserves_validity :
  forall environment critical sg first state before input last current after output,
  sem_pend_irq_completion_source environment critical sg first state before input last current after output ->
  UCOS2_state_inv sg state -> UCOS2_state_inv sg current.
Proof.
  intros until output; intro Hcompletion; destruct Hcompletion; intro Hvalid.
  - unfold os_int_exit_wrapper_restored_state.
    apply UCOS2_replace_parked_stacks_preserves_validity; [exact Hvalid|].
    apply task_stack_take_preserves_consistency.
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto.
  - pose proof (os_int_exit_ready_checkpoint_preserves_validity sg
      observed.(SchedState).(isRunning) entry Hvalid) as Hcheckpoint.
    unfold os_int_exit_wrapper_restored_state.
    apply UCOS2_replace_parked_stacks_preserves_validity; [exact Hcheckpoint|].
    apply task_stack_take_preserves_consistency.
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hcheckpoint; tauto.
Qed.

Lemma sem_pend_irq_structural_frame_resources : forall entry current,
  sem_pend_irq_structural_frame entry current ->
  (forall observer, task_creation_frame observer entry.(TskState) current.(TskState)) /\
  (forall observer, event_creation_frame observer entry.(EventState) current.(EventState)) /\
  (forall observer origin, task_invocation_active entry.(TskState) observer origin ->
    task_invocation_active current.(TskState) observer origin).
Proof.
  intros entry current Hframe; destruct Hframe as [Htasks Hlife Hevents Hnames Htimers Hrunning Hcurrent Hpriority].
  split.
  - intro observer; unfold task_creation_frame, task_creation_view; rewrite Hlife; reflexivity.
  - split.
    + intro observer; rewrite Hevents; reflexivity.
    + intros observer origin; unfold task_invocation_active, task_invocation_origin_live;
        rewrite Hlife; destruct origin; simpl; [trivial|rewrite Htasks; trivial].
Qed.
