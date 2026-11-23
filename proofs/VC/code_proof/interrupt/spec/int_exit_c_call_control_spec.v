Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_execution.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_control_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_critical_control_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_program_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_masked_c_step_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_wrapper_completion_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_returned_c_segment_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_return_view_control_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module OSIntExitCCallControl.
Import CriticalComponent BuiltinComponent SelectedControlFrames SelectedCriticalControl
  SelectedReturnPrimitive SelectedCProgram SelectedIRQWrapperSegment SelectedReturnedCProgram
  TaskSuspendMaskedC SelectedIRQWrapperCompletion OSIntExitReturnedC OSIntExitReturnView.

(** A classification of the actual original C constructor, not a requested
    endpoint property. Raw Enter/Exit and TaskDel's own lock/release phases
    do not become ordinary ISR body calls through this classification. *)
Section OriginalBodySources.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (observer : nat) (origin : TaskInvocationOrigin).

Inductive kernel_program_c_body_source :
  forall state before input stopped current after output,
  kernel_program_c_step environment critical sg observer origin
    state before input stopped current after output -> Prop :=
| KernelCBodyCritical : forall local frame call before after actual,
    kernel_program_c_body_source _ _ _ _ _ _ _
      (@KernelProgramCCritical environment critical sg observer origin local frame call before after actual)
| KernelCBodyPublication : forall local publication state frame before after code effect actual,
    kernel_program_c_body_source _ _ _ _ _ _ _
      (@KernelProgramCBuiltin environment critical sg observer origin local _ _ _ _ _ _
        (@KernelBuiltinCPublication environment critical local sg
          publication state frame before after code effect actual))
| KernelCBodyIRQTransfer : forall local handler saved entry transfer frame before after actual,
    kernel_program_c_body_source _ _ _ _ _ _ _
      (@KernelProgramCBuiltin environment critical sg observer origin local _ _ _ _ _ _
        (@KernelBuiltinCIRQTransfer environment critical local sg
          handler saved entry transfer frame before after actual))
| KernelCBodyInstall : forall local state before input stopped current after output actual,
    kernel_program_c_body_source _ _ _ _ _ _ _
      (@KernelProgramCInstall environment critical sg observer origin local
        state before input stopped current after output actual)
| KernelCBodyWake : forall state before input current after output actual,
    kernel_program_c_body_source _ _ _ _ _ _ _
      (@KernelProgramCWake environment critical sg observer origin
        state before input current after output actual)
| KernelCBodyStatus : forall state before current after frame actual,
    kernel_program_c_body_source _ _ _ _ _ _ _
      (@KernelProgramCStatus environment critical sg observer origin
        state before current after frame actual)
| KernelCBodyTaskCreation : forall state before input current after output actual,
    kernel_program_c_body_source _ _ _ _ _ _ _
      (@KernelProgramCTaskCreation environment critical sg observer origin
        state before input current after output actual)
| KernelCBodyEventCreation : forall state before input current after output actual,
    kernel_program_c_body_source _ _ _ _ _ _ _
      (@KernelProgramCEventCreation environment critical sg observer origin
        state before input current after output actual)
| KernelCBodyQueueCreation : forall state before input current after output actual,
    kernel_program_c_body_source _ _ _ _ _ _ _
      (@KernelProgramCQueueCreation environment critical sg observer origin
        state before input current after output actual)
| KernelCBodyMutexPend : forall local frame call before after actual,
    kernel_program_c_body_source _ _ _ _ _ _ _
      (@KernelProgramCMutexPend environment critical sg observer origin local frame call before after actual)
| KernelCBodyMutexPost : forall source_env local frame call before after actual,
    kernel_program_c_body_source _ _ _ _ _ _ _
      (@KernelProgramCMutexPost environment critical sg observer origin
        source_env local frame call before after actual)
| KernelCBodyDeletePrimitive : forall state before input stopped current after output actual,
    kernel_program_c_body_source _ _ _ _ _ _ _
      (@KernelProgramCDeletePrimitive environment critical sg observer origin
        state before input stopped current after output actual)
| KernelCBodyPairedPrimitive : forall state before input stopped current after output actual,
    kernel_program_c_body_source _ _ _ _ _ _ _
      (@KernelProgramCPairedPrimitive environment critical sg observer origin
        state before input stopped current after output actual).
End OriginalBodySources.

Lemma kernel_program_c_body_source_control :
  forall environment critical sg observer origin state before input stopped current after output
    (step : kernel_program_c_step environment critical sg observer origin
      state before input stopped current after output),
  kernel_program_c_body_source environment critical sg observer origin
    state before input stopped current after output step ->
  kernel_call_control_rely sg state current.
Proof.
  intros until step; intro Hsource; destruct Hsource.
  - eapply kernel_critical_c_segment_control_fields; eassumption.
  - split; reflexivity.
  - split.
    + exact (kernel_builtin_c_segment_running environment critical local sg _ _ _ _ _ _
        (@KernelBuiltinCIRQTransfer environment critical local sg
          handler saved entry transfer frame before after actual)).
    + eapply kernel_irq_transfer_c_completion_interrupt; eassumption.
  - eapply task_install_c_step_control; eassumption.
  - eapply kernel_wake_c_segment_control; eassumption.
  - eapply kernel_status_c_segment_control; eassumption.
  - eapply kernel_task_creation_c_segment_control; eassumption.
  - eapply kernel_event_creation_c_segment_control; eassumption.
  - eapply kernel_queue_creation_c_segment_control; eassumption.
  - eapply mutex_pend_inheritance_c_segment_control_fields; eassumption.
  - split.
    + eapply mutex_post_critical_c_segment_running; eassumption.
    + eapply mutex_post_critical_c_segment_interrupt; eassumption.
  - eapply task_delete_primitive_c_segment_control; eassumption.
  - eapply flag_pend_task_primitive_c_step_control; eassumption.
Qed.

(** The injection retains the original Hstep, including its physical
    fragment and module owners. It is the existing union's constructors. *)
Definition kernel_returned_c_original_step environment critical sg observer origin
  state before input stopped current after output
  (step : kernel_program_c_step environment critical sg observer origin
    state before input stopped current after output) :
  kernel_program_returned_c_step environment critical sg observer origin
    state before input stopped current after output :=
  @KernelProgramReturnedWrapper environment critical sg observer origin
    state before input stopped current after output
    (@KernelProgramWrapperOriginal environment critical sg observer origin
      state before input stopped current after output
      (@KernelSelectedProgramReturn critical sg observer origin environment
        state before input stopped current after output
        (@KernelProgramReturnOriginal environment critical sg observer origin
          state before input stopped current after output step))).

Definition kernel_returned_c_suspend_step environment critical sg observer origin
  state before input stopped current after output
  (step : task_suspend_masked_c_step environment critical sg
    state before input stopped current after output) :
  kernel_program_returned_c_step environment critical sg observer origin
    state before input stopped current after output :=
  @KernelProgramReturnedWrapper environment critical sg observer origin
    state before input stopped current after output
    (@KernelProgramWrapperOriginal environment critical sg observer origin
      state before input stopped current after output
      (@KernelSelectedProgramSuspend critical sg observer origin environment
        state before input stopped current after output step)).

Inductive kernel_returned_c_body_source environment critical sg observer origin :
  forall state before input stopped current after output,
  kernel_program_returned_c_step environment critical sg observer origin
    state before input stopped current after output -> Prop :=
| KernelReturnedCBodyOriginal : forall state before input stopped current after output step,
  kernel_program_c_body_source environment critical sg observer origin
    state before input stopped current after output step ->
  kernel_returned_c_body_source environment critical sg observer origin
    state before input stopped current after output
    (kernel_returned_c_original_step environment critical sg observer origin
      state before input stopped current after output step)
| KernelReturnedCBodySuspend : forall state before input stopped current after output step,
  kernel_returned_c_body_source environment critical sg observer origin
    state before input stopped current after output
    (kernel_returned_c_suspend_step environment critical sg observer origin
      state before input stopped current after output step).

Definition kernel_returned_c_body_sequence_source environment critical sg observer origin
  state before input stopped current after output
  (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
    state before input stopped current after output) : Prop :=
  kernel_c_sequence_has_source (kernel_program_returned_c_step environment critical sg observer origin)
    (kernel_returned_c_body_source environment critical sg observer origin)
    state before input stopped current after output run.

Lemma kernel_returned_c_body_source_control :
  forall environment critical sg observer origin state before input stopped current after output
    (step : kernel_program_returned_c_step environment critical sg observer origin
      state before input stopped current after output),
  kernel_returned_c_body_source environment critical sg observer origin
    state before input stopped current after output step ->
  kernel_call_control_rely sg state current.
Proof.
  intros until step; intro Hsource; destruct Hsource.
  - eapply kernel_program_c_body_source_control; exact H.
  - eapply task_suspend_masked_c_step_control_fields; exact step.
Qed.

Lemma kernel_returned_c_body_sequence_control :
  forall environment critical sg observer origin state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
      state before input stopped current after output),
  kernel_returned_c_body_sequence_source environment critical sg observer origin
    state before input stopped current after output run ->
  kernel_call_control_rely sg state current.
Proof.
  intros until run; intro Hsource.
  eapply (kernel_c_sequence_source_relation
    (kernel_program_returned_c_step environment critical sg observer origin)
    (kernel_returned_c_body_source environment critical sg observer origin)
    (kernel_call_control_rely sg)).
  - intro entry; split; reflexivity.
  - intros first middle last [Hr1 Hi1] [Hr2 Hi2]; split; congruence.
  - intros; eapply kernel_returned_c_body_source_control; eassumption.
  - exact Hsource.
Qed.

Lemma kernel_returned_c_body_sequence_nesting_agrees :
  forall environment critical sg observer origin state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
      state before input stopped current after output) context,
  kernel_returned_c_body_sequence_source environment critical sg observer origin
    state before input stopped current after output run ->
  kernel_interrupt_nesting_agrees state.(SchedState).(isRunning) context state.(IntrState) ->
  kernel_interrupt_nesting_agrees current.(SchedState).(isRunning) context current.(IntrState).
Proof.
  intros until context; intros Hsource Hagrees.
  destruct (kernel_returned_c_body_sequence_control _ _ _ _ _ _ _ _ _ _ _ _ run Hsource)
    as [Hr Hi].
  rewrite Hr, Hi; exact Hagrees.
Qed.

(** The read cut and acquired cut belong to these very C executions.
    No equality with a different execution or an endpoint-only trace is used. *)
Lemma os_int_exit_first_level_body_acquired_control :
  forall environment critical sg observer origin initial handler suspended
    body_heap body_input prefix_stop observed read_heap prefix_output read_input
    acquire_stop entry before acquire_output
    (prefix : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
      (armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
        suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments))
      body_heap body_input prefix_stop observed read_heap prefix_output)
    (acquire : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
      observed read_heap read_input acquire_stop entry before acquire_output),
  kernel_returned_c_body_sequence_source environment critical sg observer origin
    _ _ _ _ _ _ _ prefix ->
  kernel_returned_c_body_sequence_source environment critical sg observer origin
    _ _ _ _ _ _ _ acquire ->
  initial.(SchedState).(isRunning) = true -> initial.(IntrState).(intNesting) = 0 ->
  observed.(SchedState).(isRunning) = true /\
  entry.(SchedState).(isRunning) = true /\
  kernel_interrupt_nesting_agrees observed.(SchedState).(isRunning)
    (os_int_exit_execution_view handler).(os_execution_context) entry.(IntrState) /\
  entry.(IntrState).(lockNesting) = initial.(IntrState).(lockNesting).
Proof.
  intros until acquire; intros Hprefix Hacquire Hrunning Hzero.
  destruct (kernel_returned_c_body_sequence_control _ _ _ _ _ _ _ _ _ _ _ _ prefix Hprefix)
    as [Hpr Hpi].
  destruct (kernel_returned_c_body_sequence_control _ _ _ _ _ _ _ _ _ _ _ _ acquire Hacquire)
    as [Har Hai].
  assert (Hparked : (armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
    suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments)).(SchedState).(isRunning) =
    initial.(SchedState).(isRunning)).
  { unfold armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      os_sched_save_current_sp, armv7a_irq_entry_counter_state.
    destruct initial.(SchedState).(isRunning) eqn:Hr; cbn [replace_IntrS TskState];
      destruct (initial.(TskState).(inUsedTaskStates)
        handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot));
      cbn [replace_TskS replace_IntrS SchedState]; exact Hr. }
  assert (Hobserved : observed.(SchedState).(isRunning) = true) by congruence.
  split; [exact Hobserved|]; split; [congruence|]; split.
  - rewrite Hobserved, Hai, Hpi.
    eapply os_int_exit_first_level_entry_nesting_agrees; eassumption.
  - rewrite Hai, Hpi; apply os_int_exit_first_level_entry_lock_nesting.
Qed.

(** Complete no-selection Task return. The two control counters are
    derived from actual entry + these body calls + this descriptor return.
    Initial lock need not be zero: locked Task returns remain supported. *)
Lemma os_int_exit_first_level_returned_control :
  forall environment critical sg observer origin initial handler suspended
    body_heap body_input prefix_stop observed read_heap prefix_output read_input
    acquire_stop entry before acquire_output
    (prefix : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
      (armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
        suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments))
      body_heap body_input prefix_stop observed read_heap prefix_output)
    (acquire : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
      observed read_heap read_input acquire_stop entry before acquire_output)
    observation_frame local receipt original node frame middle after save_before save_after,
  kernel_returned_c_body_sequence_source environment critical sg observer origin
    _ _ _ _ _ _ _ prefix ->
  kernel_returned_c_body_sequence_source environment critical sg observer origin
    _ _ _ _ _ _ _ acquire ->
  initial.(SchedState).(isRunning) = true -> initial.(IntrState).(intNesting) = 0 ->
  os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
    entry local suspended receipt original node handler frame before middle after ->
  armv7a_save_transition environment.(task_stack_call_continuations) handler suspended save_before save_after ->
  kernel_call_control_rely sg initial
    (os_int_exit_wrapper_restored_state
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
      suspended.(armv7a_continuation_stack)).
Proof.
  intros until save_after; intros Hprefix Hacquire Hrunning Hzero Hcomplete Hsave.
  destruct (os_int_exit_first_level_body_acquired_control _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    prefix acquire Hprefix Hacquire Hrunning Hzero) as [Hobserved [Hentry [Hagrees Hlocks]]].
  pose proof (os_int_exit_returned_c_completion_task_nesting_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hcomplete Hsave Hagrees Hobserved) as Hfinalzero.
  pose proof (os_int_exit_returned_c_step_running _ _ _ _ _ _ _ _ _ _
    (@OSIntExitReturnedCStep environment critical sg observed read_heap observation_frame
      entry local suspended receipt original node handler frame before middle after Hcomplete)) as Hfinalrunning.
  pose proof (os_int_exit_returned_c_step_lock_nesting _ _ _ _ _ _ _ _ _ _
    (@OSIntExitReturnedCStep environment critical sg observed read_heap observation_frame
      entry local suspended receipt original node handler frame before middle after Hcomplete)) as Hfinallocks.
  split; [congruence|].
  destruct (initial.(IntrState)) as [initial_ints initial_locks] eqn:Hinitial.
  destruct ((os_int_exit_wrapper_restored_state
    (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
    suspended.(armv7a_continuation_stack)).(IntrState)) as [final_ints final_locks] eqn:Hfinal.
  cbn in Hzero, Hfinalzero, Hfinallocks, Hlocks; f_equal; congruence.
Qed.

End OSIntExitCCallControl.
