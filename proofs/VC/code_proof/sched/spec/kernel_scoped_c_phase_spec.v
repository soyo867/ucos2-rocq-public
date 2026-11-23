(* Report candidate: actual module completions; staged only by the parent. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_effect_properties_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_environment_spec.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module SelectedEnvironmentPhaseEffects.
Import PrimitiveComponent SelectedEnvironmentCProgram SelectedEnvironmentCSource SelectedEnvironmentCache.
Import SelectedEnvironmentScopedSource SelectedEnvironmentScopedEnvironment.

(** These constructors retain the selected middle C execution and the
    actual local ABI transition.  Caller heaps are its real boundary
    subheaps.  The two producers below derive the final split from that
    same execution; no future receipt or preservation premise is added. *)
Inductive os_sched_continuation_c_save_execution environment critical local next_local active sg
  original mask before first_heap :
  Z -> bool -> OsSchedCallContext -> UCOS2_Verify_State -> model -> Prop :=
| OsSchedContinuationCSave :
  forall private_input private_output private_before whole_before stopped returned current environment_heap arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers final_registers whole_after private_after last_heap
    (run : flag_pend_scoped_environment_run environment critical local next_local active sg
      original mask before whole_before private_input stopped returned current environment_heap private_output),
  flag_pend_scoped_environment_source environment critical local next_local active sg None
    original mask before whole_before private_input stopped returned current environment_heap private_output run ->
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller original) original mask before first_heap ->
  private_input private_before -> join first_heap private_before whole_before ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current environment_heap
    final_registers current whole_after ->
  (coq_prop (flag_pend_call_endpoint_observations environment sg
     (FlagPendTaskCaller original) original before returned current) &&
   flag_pend_caller_restore_input environment critical next_local active sg
     (FlagPendTaskCaller returned) returned final_registers.(kernel_save_r0) current current) last_heap ->
  private_output private_after -> join last_heap private_after whole_after ->
  os_sched_continuation_c_save_execution environment critical local next_local active sg
    original mask before first_heap final_registers.(kernel_save_r0) stopped returned current last_heap.

Inductive os_sched_continuation_c_restore_execution environment critical local next_local active sg
  original saved acquired before first_heap :
  bool -> OsSchedCallContext -> UCOS2_Verify_State -> model -> Prop :=
| OsSchedContinuationCRestore :
  forall private_input private_output private_before whole_before stopped returned current environment_heap arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written prefix_heap final_cursor whole_after private_after last_heap
    (run : flag_pend_scoped_environment_run environment critical local next_local active sg
      original (armv7a_irq_fiq_mask saved) before prefix_heap private_input
      stopped returned current environment_heap private_output),
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before first_heap ->
  private_input private_before -> join first_heap private_before whole_before ->
  armv7a_restore_prefix_transition restore cursor whole_before written prefix_heap ->
  flag_pend_scoped_environment_source environment critical local next_local active sg None
    original (armv7a_irq_fiq_mask saved) before prefix_heap private_input
    stopped returned current environment_heap private_output run ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor whole_after ->
  (coq_prop (flag_pend_call_endpoint_observations environment sg
     (FlagPendTaskCaller original) original before returned current) &&
   flag_pend_caller_save_input environment critical next_local active sg
     (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current) last_heap ->
  private_output private_after -> join last_heap private_after whole_after ->
  os_sched_continuation_c_restore_execution environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap.

Lemma os_sched_continuation_c_save_execution_from_environment :
  forall environment critical local next_local active sg original mask before first_heap
    private_input private_output private_before whole_before stopped returned current environment_heap arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers final_registers whole_after
    (run : flag_pend_scoped_environment_run environment critical local next_local active sg
      original mask before whole_before private_input stopped returned current environment_heap private_output),
  flag_pend_scoped_environment_source environment critical local next_local active sg None
    original mask before whole_before private_input stopped returned current environment_heap private_output run ->
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller original) original mask before first_heap ->
  private_input private_before -> join first_heap private_before whole_before ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current environment_heap
    final_registers current whole_after ->
  exists last_heap,
  os_sched_continuation_c_save_execution environment critical local next_local active sg
    original mask before first_heap final_registers.(kernel_save_r0) stopped returned current last_heap.
Proof.
  intros environment critical local next_local active sg original mask before first_heap
    private_input private_output private_before whole_before stopped returned current environment_heap arch save
    registers final_registers whole_after run Hsource Hinput Hprivate Hjoin Hreturn Hvalid Hmask Hsuffix.
  destruct (flag_pend_scoped_environment_save_sequence environment critical local next_local active sg None
    original mask before whole_before private_input stopped returned current environment_heap private_output
    arch save registers final_registers whole_after run Hsource Hreturn Hvalid Hmask Hsuffix)
    as [Hsaved [completed Hcompleted_source]].
  pose proof (proj2 (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ completed)) as Houtput.
  destruct Houtput as [last_heap [private_after [Hjoin_after [Hcaller_after Hprivate_after]]]].
  exists last_heap.
  eapply OsSchedContinuationCSave with
    (private_input := private_input) (private_output := private_output)
    (private_before := private_before) (whole_before := whole_before)
    (environment_heap := environment_heap) (save := save)
    (registers := registers) (final_registers := final_registers)
    (whole_after := whole_after) (private_after := private_after) (run := run); eassumption.
Qed.

Lemma os_sched_continuation_c_restore_execution_from_environment :
  forall environment critical local next_local active sg original saved acquired before first_heap
    private_input private_output private_before whole_before stopped returned current environment_heap arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written prefix_heap final_cursor whole_after
    (run : flag_pend_scoped_environment_run environment critical local next_local active sg
      original (armv7a_irq_fiq_mask saved) before prefix_heap private_input
      stopped returned current environment_heap private_output),
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before first_heap ->
  private_input private_before -> join first_heap private_before whole_before ->
  armv7a_restore_prefix_transition restore cursor whole_before written prefix_heap ->
  flag_pend_scoped_environment_source environment critical local next_local active sg None
    original (armv7a_irq_fiq_mask saved) before prefix_heap private_input
    stopped returned current environment_heap private_output run ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor whole_after ->
  exists last_heap,
  os_sched_continuation_c_restore_execution environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap.
Proof.
  intros environment critical local next_local active sg original saved acquired before first_heap
    private_input private_output private_before whole_before stopped returned current environment_heap arch restore
    cursor written prefix_heap final_cursor whole_after run Hr0 Hmask Hinput Hprivate Hjoin Hprefix Hsource Hsuffix.
  assert (Hwhole :
    (flag_pend_caller_restore_input environment critical local active sg
      (FlagPendTaskCaller original) original saved acquired before ** private_input) whole_before).
  { exists first_heap, private_before; exact (conj Hjoin (conj Hinput Hprivate)). }
  destruct (flag_pend_scoped_environment_restore_sequence environment critical local next_local active sg None
    original saved acquired before whole_before private_input stopped returned current environment_heap private_output
    arch restore cursor written prefix_heap final_cursor whole_after run Hr0 Hmask Hwhole Hprefix Hsource Hsuffix)
    as [completed Hcompleted_source].
  pose proof (proj2 (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ completed)) as Houtput.
  destruct Houtput as [last_heap [private_after [Hjoin_after [Hcaller_after Hprivate_after]]]].
  exists last_heap.
  eapply OsSchedContinuationCRestore with
    (private_input := private_input) (private_output := private_output)
    (private_before := private_before) (whole_before := whole_before)
    (environment_heap := environment_heap) (restore := restore)
    (cursor := cursor) (written := written) (prefix_heap := prefix_heap)
    (final_cursor := final_cursor) (whole_after := whole_after)
    (private_after := private_after) (run := run); eassumption.
Qed.

Local Lemma kernel_call_scoped_source_at_boundaries :
  forall environment critical sg observer origin event_observer initial caller_before input stopped current caller_after output
    private_input private_output whole_before whole_after private_before private_after
    (run : kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer origin)
      initial whole_before (input ** private_input) stopped current whole_after (output ** private_output)),
  kernel_program_environment_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ run ->
  input caller_before -> private_input private_before -> join caller_before private_before whole_before ->
  output caller_after -> private_output private_after -> join caller_after private_after whole_after ->
  exists (actual : kernel_call_scoped_c_execution environment critical sg observer origin
    initial caller_before input stopped current caller_after output),
  kernel_call_scoped_c_execution_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ actual.
Proof.
  intros environment critical sg observer origin event_observer initial caller_before input stopped current caller_after output
    private_input private_output whole_before whole_after private_before private_after run Hsource
    Hin Hprivate Hinjoin Hout Hprivateout Houtjoin.
  exists (@KernelCallScopedCExecution environment critical sg observer origin initial caller_before input
    stopped current caller_after output private_input private_output whole_before whole_after private_before private_after
    run Hin Hprivate Hinjoin Hout Hprivateout Houtjoin).
  constructor; exact Hsource.
Qed.

Lemma os_sched_continuation_c_save_execution_sequence_source :
  forall environment critical local next_local active sg original mask before first_heap saved stopped returned current last_heap,
  os_sched_continuation_c_save_execution environment critical local next_local active sg
    original mask before first_heap saved stopped returned current last_heap ->
  interrupt_saved_value mask saved /\
  exists (completed : kernel_call_scoped_c_execution environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    before first_heap
    (flag_pend_caller_save_input environment critical local active sg
      (FlagPendTaskCaller original) original mask before)
    stopped current last_heap
    (coq_prop (flag_pend_call_endpoint_observations environment sg
       (FlagPendTaskCaller original) original before returned current) &&
     flag_pend_caller_restore_input environment critical next_local active sg
       (FlagPendTaskCaller returned) returned saved current current)),
  kernel_call_scoped_c_execution_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ completed.
Proof.
  intros until last_heap; intro Hactual; destruct Hactual.
  assert (Hfull : interrupt_saved_value mask final_registers.(kernel_save_r0) /\
    exists (completed : kernel_c_sequence
      (kernel_program_environment_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
      before whole_before
      (flag_pend_caller_save_input environment critical local active sg
        (FlagPendTaskCaller original) original mask before ** private_input)
      stopped current whole_after
      ((coq_prop (flag_pend_call_endpoint_observations environment sg
          (FlagPendTaskCaller original) original before returned current) &&
        flag_pend_caller_restore_input environment critical next_local active sg
          (FlagPendTaskCaller returned) returned final_registers.(kernel_save_r0) current current) ** private_output)),
    kernel_program_environment_c_sequence_source environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ completed).
  { eapply flag_pend_scoped_environment_save_sequence; eassumption. }
  destruct Hfull as [Hsaved [completed Hsource]].
  split; [exact Hsaved|].
  eapply kernel_call_scoped_source_at_boundaries; eassumption.
Qed.

Lemma os_sched_continuation_c_restore_execution_sequence_source :
  forall environment critical local next_local active sg original saved acquired before first_heap
    stopped returned current last_heap,
  os_sched_continuation_c_restore_execution environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap ->
  exists (completed : kernel_call_scoped_c_execution environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    before first_heap
    (flag_pend_caller_restore_input environment critical local active sg
      (FlagPendTaskCaller original) original saved acquired before)
    stopped current last_heap
    (coq_prop (flag_pend_call_endpoint_observations environment sg
       (FlagPendTaskCaller original) original before returned current) &&
     flag_pend_caller_save_input environment critical next_local active sg
       (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current)),
  kernel_call_scoped_c_execution_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ completed.
Proof.
  intros until last_heap; intro Hactual; destruct Hactual.
  assert (Hwhole :
    (flag_pend_caller_restore_input environment critical local active sg
      (FlagPendTaskCaller original) original saved acquired before ** private_input) whole_before).
  { exists first_heap, private_before; split; [assumption|split; assumption]. }
  destruct (flag_pend_scoped_environment_restore_sequence environment critical local next_local active sg None
    original saved acquired before whole_before private_input stopped returned current environment_heap private_output
    arch restore cursor written prefix_heap final_cursor whole_after run) as [completed Hsource]; try eassumption.
  eapply kernel_call_scoped_source_at_boundaries; eassumption.
Qed.

Definition flag_pend_program_c_event environment critical sg event : Prop :=
  exists stopped (actual : kernel_call_scoped_c_execution environment critical sg
    (flag_pend_program_c_observer event) (flag_pend_program_c_origin event)
    event.(flag_pend_event_before) event.(flag_pend_event_first_heap) event.(flag_pend_event_input)
    stopped event.(flag_pend_event_current) event.(flag_pend_event_last_heap) event.(flag_pend_event_output)),
  kernel_call_scoped_c_execution_source environment critical sg
    (flag_pend_program_c_observer event) (flag_pend_program_c_origin event) None _ _ _ _ _ _ _ actual.

Lemma flag_pend_program_c_event_resources : forall environment critical sg event,
  flag_pend_program_c_event environment critical sg event ->
  event.(flag_pend_event_input) event.(flag_pend_event_first_heap) /\
  event.(flag_pend_event_output) event.(flag_pend_event_last_heap).
Proof.
  intros environment critical sg event [stopped [actual Hsource]].
  eapply kernel_call_scoped_c_execution_resources; exact actual.
Qed.

Definition os_sched_continuation_phase_save_effect environment critical sg original mask saved before returned acquired : Prop :=
  os_sched_continuation_save_effect environment critical sg original mask saved before returned acquired \/
  exists local next_local active first_heap stopped last_heap,
    os_sched_continuation_c_save_execution environment critical local next_local active sg
      original mask before first_heap saved stopped returned acquired last_heap.

Definition os_sched_continuation_phase_restore_effect environment critical sg original released returned current : Prop :=
  os_sched_continuation_restore_effect environment critical sg original released returned current \/
  exists local next_local active saved acquired first_heap stopped last_heap,
    os_sched_continuation_c_restore_execution environment critical local next_local active sg
      original saved acquired released first_heap stopped returned current last_heap.

Definition os_sched_continuation_phase_save_program environment critical sg original mask :
  program UCOS2_Verify_State (OsSchedCallContext * Z) :=
  fun before result acquired => os_sched_continuation_phase_save_effect environment critical sg
    original mask (snd result) before (fst result) acquired.

Definition os_sched_continuation_phase_restore_program environment critical sg resumed :
  program UCOS2_Verify_State OsSchedCallContext :=
  fun released returned current => os_sched_continuation_phase_restore_effect environment critical sg resumed released returned current.

Lemma os_sched_continuation_save_effect_implies_phase : forall environment critical sg original mask saved before returned acquired,
  os_sched_continuation_save_effect environment critical sg original mask saved before returned acquired ->
  os_sched_continuation_phase_save_effect environment critical sg original mask saved before returned acquired.
Proof. intros; left; assumption. Qed.

Lemma os_sched_continuation_restore_effect_implies_phase : forall environment critical sg original released returned current,
  os_sched_continuation_restore_effect environment critical sg original released returned current ->
  os_sched_continuation_phase_restore_effect environment critical sg original released returned current.
Proof. intros; left; assumption. Qed.

Lemma os_sched_continuation_c_save_execution_effect_source :
  forall environment critical local next_local active sg original mask before first_heap saved stopped returned current last_heap,
  os_sched_continuation_c_save_execution environment critical local next_local active sg
    original mask before first_heap saved stopped returned current last_heap ->
  os_sched_continuation_phase_save_effect environment critical sg original mask saved before returned current /\
  interrupt_saved_value mask saved /\
  flag_pend_program_c_event environment critical sg
    (flag_pend_task_save_completed_c_event environment critical local next_local active sg
      original mask saved before first_heap returned current last_heap).
Proof.
  intros until last_heap; intro Hactual.
  split; [right; exists local, next_local, active, first_heap, stopped, last_heap; exact Hactual|].
  destruct (os_sched_continuation_c_save_execution_sequence_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual)
    as [Hsaved [completed Hsource]].
  split; [exact Hsaved|]. exists stopped, completed; exact Hsource.
Qed.

Lemma os_sched_continuation_c_restore_execution_effect_source :
  forall environment critical local next_local active sg original saved acquired before first_heap stopped returned current last_heap,
  os_sched_continuation_c_restore_execution environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap ->
  os_sched_continuation_phase_restore_effect environment critical sg original before returned current /\
  flag_pend_program_c_event environment critical sg
    (flag_pend_task_restore_completed_c_event environment critical local next_local active sg
      original saved acquired before first_heap returned current last_heap).
Proof.
  intros until last_heap; intro Hactual.
  split; [right; exists local, next_local, active, saved, acquired, first_heap, stopped, last_heap; exact Hactual|].
  destruct (os_sched_continuation_c_restore_execution_sequence_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual)
    as [completed Hsource].
  exists stopped, completed; exact Hsource.
Qed.

Lemma os_sched_continuation_c_save_execution_endpoints :
  forall environment critical local next_local active sg original mask before first_heap saved stopped returned current last_heap,
  os_sched_continuation_c_save_execution environment critical local next_local active sg
    original mask before first_heap saved stopped returned current last_heap ->
  flag_pend_call_endpoint_observations environment sg
    (FlagPendTaskCaller original) original before returned current.
Proof.
  intros until last_heap; intro Hactual; destruct Hactual.
  match goal with Howner : (coq_prop _ && _) _ |- _ => exact (proj1 Howner) end.
Qed.

Lemma os_sched_continuation_c_restore_execution_endpoints :
  forall environment critical local next_local active sg original saved acquired before first_heap stopped returned current last_heap,
  os_sched_continuation_c_restore_execution environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap ->
  flag_pend_call_endpoint_observations environment sg
    (FlagPendTaskCaller original) original before returned current.
Proof.
  intros until last_heap; intro Hactual; destruct Hactual.
  match goal with Howner : (coq_prop _ && _) _ |- _ => exact (proj1 Howner) end.
Qed.

Lemma os_sched_continuation_phase_save_effect_same_call :
  forall environment critical sg original mask saved before returned acquired,
  os_sched_continuation_phase_save_effect environment critical sg original mask saved before returned acquired ->
  task_tcb_init_stack_same_call returned original.
Proof.
  intros environment critical sg original mask saved before returned acquired [Hold|Hnew].
  - eapply os_sched_continuation_save_effect_same_call; exact Hold.
  - destruct Hnew as [local [next_local [active [first_heap [stopped [last_heap Hactual]]]]]].
    pose proof (os_sched_continuation_c_save_execution_endpoints _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual)
      as [Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]].
    exact (proj1 Hnormal).
Qed.

Lemma os_sched_continuation_phase_restore_effect_same_call :
  forall environment critical sg original released returned current,
  os_sched_continuation_phase_restore_effect environment critical sg original released returned current ->
  task_tcb_init_stack_same_call returned original.
Proof.
  intros environment critical sg original released returned current [Hold|Hnew].
  - eapply os_sched_continuation_restore_effect_same_call; exact Hold.
  - destruct Hnew as [local [next_local [active [saved [acquired [first_heap [stopped [last_heap Hactual]]]]]]]].
    pose proof (os_sched_continuation_c_restore_execution_endpoints _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual)
      as [Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]].
    exact (proj1 Hnormal).
Qed.

End SelectedEnvironmentPhaseEffects.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module SelectedEnvironmentPhaseProperties.
Import PrimitiveComponent SelectedEnvironmentCProgram SelectedEnvironmentCSource SelectedEnvironmentPrimitiveSupport SelectedEnvironmentCache.
Import SelectedEnvironmentScopedSource SelectedEnvironmentPhaseEffects.

Lemma kernel_call_scoped_c_execution_unframed :
  forall environment critical sg observer origin event_observer initial before input stopped current after output
    (run : kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer origin)
      initial before input stopped current after output),
  kernel_program_environment_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ run ->
  exists (actual : kernel_call_scoped_c_execution environment critical sg observer origin
    initial before input stopped current after output),
  kernel_call_scoped_c_execution_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ actual.
Proof.
  intros environment critical sg observer origin event_observer initial before input stopped current after output run Hsource.
  destruct (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ run) as [Hin Hout].
  destruct (unit_join before) as [private_before [Hempty_before Hjoin_before]].
  destruct (unit_join after) as [private_after [Hempty_after Hjoin_after]].
  assert (Hwhole : (input ** emp) before).
  { exists before, private_before; exact (conj Hjoin_before (conj Hin Hempty_before)). }
  assert (Hpre : input ** emp |-- input) by entailer!.
  assert (Hpost : output |-- output ** emp) by entailer!.
  pose (whole := KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hwhole Hpre run Hpost).
  exists (@KernelCallScopedCExecution environment critical sg observer origin initial before input
    stopped current after output emp emp before after private_before private_after
    whole Hin Hempty_before Hjoin_before Hout Hempty_after Hjoin_after).
  apply KernelCallScopedCExecutionSource.
  unfold whole, kernel_program_environment_c_sequence_source.
  apply KernelCSourceAdapt; exact Hsource.
Qed.

Lemma flag_pend_program_c_event_primitive :
  forall environment critical sg event,
  flag_pend_task_primitive_c_event environment critical sg event ->
  flag_pend_program_c_event environment critical sg event.
Proof.
  intros environment critical sg event Hprimitive.
  pose (step := kernel_program_environment_paired_primitive environment critical sg
    (flag_pend_program_c_observer event) (flag_pend_program_c_origin event)
    _ _ _ _ _ _ _ (FlagPendTaskPrimitiveCStep environment critical sg event Hprimitive)).
  pose (run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step).
  assert (Hsource : kernel_program_environment_c_sequence_source environment critical sg
    (flag_pend_program_c_observer event) (flag_pend_program_c_origin event) None _ _ _ _ _ _ _ run).
  { unfold run, kernel_program_environment_c_sequence_source.
    apply KernelCSourceAtom; unfold step; apply kernel_program_environment_paired_primitive_source. }
  destruct (kernel_call_scoped_c_execution_unframed _ _ _ _ _ _ _ _ _ _ _ _ _ run Hsource)
    as [actual Hactual_source].
  exists false, actual; exact Hactual_source.
Qed.

Lemma flag_pend_program_c_event_current_cache : forall environment critical sg event,
  flag_pend_program_c_event environment critical sg event ->
  event.(flag_pend_event_caller) = FlagPendTaskCaller event.(flag_pend_event_original) ->
  task_in_range sg event.(flag_pend_event_before).(TskState) ->
  kernel_call_task_source event.(flag_pend_event_original) event.(flag_pend_event_before) ->
  sched_current_consistency event.(flag_pend_event_before).(TskState) event.(flag_pend_event_before).(SchedState) ->
  kernel_call_normal_return event.(flag_pend_event_original) event.(flag_pend_event_before)
    event.(flag_pend_event_returned) event.(flag_pend_event_current) ->
  kernel_call_task_source event.(flag_pend_event_returned) event.(flag_pend_event_current) ->
  sched_current_consistency event.(flag_pend_event_current).(TskState) event.(flag_pend_event_current).(SchedState).
Proof.
  intros environment critical sg event [stopped [actual Hactual_source]]
    Hcaller Hrange Horiginal Hcache Hnormal Hreturned.
  clear Hactual_source.
  unfold flag_pend_program_c_observer, flag_pend_program_c_origin in actual.
  rewrite Hcaller in actual; cbn in actual.
  destruct actual.
  exact (proj2 (kernel_program_environment_c_sequence_completed_current_cache environment critical sg
    event.(flag_pend_event_original) event.(flag_pend_event_returned)
    _ _ _ _ _ _ _ run Hrange Horiginal Hcache Hnormal Hreturned)).
Qed.

Lemma os_sched_continuation_save_program_implies_phase :
  forall environment critical sg original mask before result acquired,
  os_sched_continuation_save_program environment critical sg original mask before result acquired ->
  os_sched_continuation_phase_save_program environment critical sg original mask before result acquired.
Proof. intros; apply os_sched_continuation_save_effect_implies_phase; assumption. Qed.

Lemma os_sched_continuation_restore_program_implies_phase :
  forall environment critical sg resumed released returned current,
  os_sched_continuation_restore_program environment critical sg resumed released returned current ->
  os_sched_continuation_phase_restore_program environment critical sg resumed released returned current.
Proof. intros; apply os_sched_continuation_restore_effect_implies_phase; assumption. Qed.

Lemma os_sched_continuation_phase_save_effect_saved_value :
  forall environment critical sg original mask saved before returned acquired,
  os_sched_continuation_phase_save_effect environment critical sg original mask saved before returned acquired ->
  interrupt_saved_value mask saved.
Proof.
  intros environment critical sg original mask saved before returned acquired [Hold|Hnew].
  - destruct Hold as [[Htrace [Hinv [Horigin [Hstack Hsaved]]]]|[Hhistory Hsaved]]; exact Hsaved.
  - destruct Hnew as [local [next_local [active [first_heap [stopped [last_heap Hactual]]]]]].
    exact (proj1 (os_sched_continuation_c_save_execution_sequence_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual)).
Qed.

Lemma os_sched_continuation_c_save_execution_resources :
  forall environment critical local next_local active sg original mask before first_heap saved stopped returned current last_heap,
  os_sched_continuation_c_save_execution environment critical local next_local active sg
    original mask before first_heap saved stopped returned current last_heap ->
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller original) original mask before first_heap /\
  (coq_prop (flag_pend_call_endpoint_observations environment sg
      (FlagPendTaskCaller original) original before returned current) &&
    flag_pend_caller_restore_input environment critical next_local active sg
      (FlagPendTaskCaller returned) returned saved current current) last_heap.
Proof.
  intros until last_heap; intro Hactual; destruct Hactual; split; assumption.
Qed.

Lemma os_sched_continuation_c_restore_execution_resources :
  forall environment critical local next_local active sg original saved acquired before first_heap stopped returned current last_heap,
  os_sched_continuation_c_restore_execution environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap ->
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before first_heap /\
  (coq_prop (flag_pend_call_endpoint_observations environment sg
      (FlagPendTaskCaller original) original before returned current) &&
    flag_pend_caller_save_input environment critical next_local active sg
      (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current) last_heap.
Proof.
  intros until last_heap; intro Hactual; destruct Hactual; split; assumption.
Qed.

Lemma os_sched_continuation_c_save_execution_creation_name_timer :
  forall environment critical local next_local active sg original mask before first_heap saved stopped returned current last_heap,
  os_sched_continuation_c_save_execution environment critical local next_local active sg
    original mask before first_heap saved stopped returned current last_heap ->
  task_creation_frame original.(os_sched_call_invocation) before.(TskState) current.(TskState) /\
  before.(NameState) = current.(NameState) /\ timer_public_trace sg before.(TimerState) current.(TimerState).
Proof.
  intros until last_heap; intro Hactual.
  destruct (os_sched_continuation_c_save_execution_sequence_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual)
    as [Hsaved [completed Hsource]].
  destruct (kernel_call_scoped_c_execution_source_frames _ _ _ _ _ _ _ _ _ _ _ _ _ completed Hsource)
    as [Htask [_ Hrest]]; exact (conj Htask Hrest).
Qed.

Lemma os_sched_continuation_c_restore_execution_creation_name_timer :
  forall environment critical local next_local active sg original saved acquired before first_heap stopped returned current last_heap,
  os_sched_continuation_c_restore_execution environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap ->
  task_creation_frame original.(os_sched_call_invocation) before.(TskState) current.(TskState) /\
  before.(NameState) = current.(NameState) /\ timer_public_trace sg before.(TimerState) current.(TimerState).
Proof.
  intros until last_heap; intro Hactual.
  destruct (os_sched_continuation_c_restore_execution_sequence_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual)
    as [completed Hsource].
  destruct (kernel_call_scoped_c_execution_source_frames _ _ _ _ _ _ _ _ _ _ _ _ _ completed Hsource)
    as [Htask [_ Hrest]]; exact (conj Htask Hrest).
Qed.

Lemma os_sched_continuation_phase_save_effect_name_timer :
  forall environment critical sg original mask saved before returned acquired,
  os_sched_continuation_phase_save_effect environment critical sg original mask saved before returned acquired ->
  before.(NameState) = acquired.(NameState) /\ timer_public_trace sg before.(TimerState) acquired.(TimerState).
Proof.
  intros environment critical sg original mask saved before returned acquired [Hold|Hnew].
  - eapply ContinuationEffectProjections.os_sched_continuation_save_effect_name_timer; exact Hold.
  - destruct Hnew as [local [next_local [active [first_heap [stopped [last_heap Hactual]]]]]].
    exact (proj2 (os_sched_continuation_c_save_execution_creation_name_timer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual)).
Qed.

Lemma os_sched_continuation_phase_restore_effect_name_timer :
  forall environment critical sg original released returned current,
  os_sched_continuation_phase_restore_effect environment critical sg original released returned current ->
  released.(NameState) = current.(NameState) /\ timer_public_trace sg released.(TimerState) current.(TimerState).
Proof.
  intros environment critical sg original released returned current [Hold|Hnew].
  - eapply ContinuationEffectProjections.os_sched_continuation_restore_effect_name_timer; exact Hold.
  - destruct Hnew as [local [next_local [active [saved [acquired [first_heap [stopped [last_heap Hactual]]]]]]]].
    exact (proj2 (os_sched_continuation_c_restore_execution_creation_name_timer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual)).
Qed.

Lemma os_sched_continuation_c_save_execution_not_stopped :
  forall environment critical local next_local active sg original mask before first_heap saved stopped returned current last_heap,
  os_sched_continuation_c_save_execution environment critical local next_local active sg
    original mask before first_heap saved stopped returned current last_heap ->
  kernel_call_task_source original before -> kernel_call_task_source returned current -> stopped = false.
Proof.
  intros until last_heap; intros Hactual Horiginal Hreturned.
  destruct (os_sched_continuation_c_save_execution_sequence_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual)
    as [Hsaved [completed Hsource]].
  destruct (kernel_call_scoped_c_execution_resources _ _ _ _ _ _ _ _ _ _ _ _ completed)
    as [Hinput [Hendpoints Houtput]].
  destruct Hendpoints as [Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]].
  pose proof (flag_pend_caller_save_input_task_in_range environment critical local active sg
    (FlagPendTaskCaller original) original mask before first_heap Hinput) as Hrange.
  pose proof (kernel_call_scoped_c_execution_observer_lifetime _ _ _ _ _ _ _ _ _ _ _ _ completed) as Hlife.
  eapply kernel_call_completed_task_source_not_stopped; eassumption.
Qed.

Lemma os_sched_continuation_c_restore_execution_not_stopped :
  forall environment critical local next_local active sg original saved acquired before first_heap stopped returned current last_heap,
  os_sched_continuation_c_restore_execution environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap ->
  kernel_call_task_source original before -> kernel_call_task_source returned current -> stopped = false.
Proof.
  intros until last_heap; intros Hactual Horiginal Hreturned.
  destruct (os_sched_continuation_c_restore_execution_sequence_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual)
    as [completed Hsource].
  destruct (kernel_call_scoped_c_execution_resources _ _ _ _ _ _ _ _ _ _ _ _ completed)
    as [Hinput [Hendpoints Houtput]].
  destruct Hendpoints as [Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]].
  pose proof (flag_pend_caller_restore_input_task_in_range environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before first_heap Hinput) as Hrange.
  pose proof (kernel_call_scoped_c_execution_observer_lifetime _ _ _ _ _ _ _ _ _ _ _ _ completed) as Hlife.
  eapply kernel_call_completed_task_source_not_stopped; eassumption.
Qed.

End SelectedEnvironmentPhaseProperties.
