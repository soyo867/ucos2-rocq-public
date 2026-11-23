(** Extracted from a passed fixed check; ordinary integration is pending. *)
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import SimpleC.SL.Mem.
Require Import SimpleC.SL.ConAssertion.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.micromega.Lia.
From SimpleC.SL Require Import ArrayLib.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import AUXLib.ListLib.
From MonadLib Require Import Monad.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.VC.code.core.spec.kernel_idle_ready_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_api_entry_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_fields_resources_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_resources_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_unlink_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_unlink_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_always_nonswitch_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_wake_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_inherit_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_api_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_region_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_fields_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_local_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_sched_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_save_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_wake_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_client_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_irq_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_disabled_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_delete_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_nontimer_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_irq_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Import Ucos2Verify.VC.code.task.spec.flag_fields_publication_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_return_stage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_api_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_idle_guard_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.flag_node_fields.
Require Import Ucos2Verify.lib.flag_stack.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_execution.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.task_retirement.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_c_control_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_del_c_idle_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_idle_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_critical_idle_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_idle_frames_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_wake_status_idle_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_c_idle_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_return_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_suspend_masked_c_step_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_del_c_segment_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_create_c_segment_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_priority_c_segment_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Export Ucos2Verify.VC.code.queue.spec.q_create_c_segment_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_c_segment_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


(** The Suspend marker retains the real protected Idle guard and the same
    status-source proof.  Every other leaf uses its original source.  This
    is additional provenance of this execution, not an Idle postcondition
    used as a source premise. *)
Module SelectedIdleComposition.
Import CriticalComponent PrimitiveComponent SelectedCProgram SelectedCSource SelectedReturnPrimitive.
Import SelectedIdleFrames SelectedIdleWakeStatus SelectedIdleBuiltin SelectedMutexIdle.
Import SelectedIdleCritical SelectedDeleteIdle.
Import SelectedControlComposition.

Inductive kernel_program_original_idle_source environment critical sg observer origin :
  forall state before input stopped current after output,
  kernel_program_c_step environment critical sg observer origin state before input stopped current after output -> Prop :=
| KernelOriginalCriticalIdleSource : forall local frame call before after
    (actual : kernel_critical_c_segment environment critical local sg frame call before after),
    kernel_program_original_idle_source environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCCritical environment critical sg observer origin local frame call before after actual)
| KernelOriginalBuiltinIdleSource : forall local state before current after input output
    (actual : BuiltinComponent.kernel_builtin_c_segment environment critical local sg state before current after input output),
    kernel_program_original_idle_source environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCBuiltin environment critical sg observer origin local state before current after input output actual)
| KernelOriginalInstallIdleSource : forall local state before input stopped current after output
    (actual : InstallComponent.task_install_c_step environment local sg state before input stopped current after output),
    kernel_program_original_idle_source environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCInstall environment critical sg observer origin local state before input stopped current after output actual)
| KernelOriginalWakeIdleSource : forall state before input current after output
    (actual : WakeComponent.kernel_wake_c_segment sg state before input current after output),
    kernel_program_original_idle_source environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCWake environment critical sg observer origin state before input current after output actual)
| KernelOriginalStatusIdleSource : forall state before current after frame
    (actual : StatusComponent.kernel_status_c_segment sg state before current after frame),
    kernel_status_c_idle_source sg state current (StatusComponent.kernel_status_c_segment_code _ _ _ _ _ _ actual) ->
    kernel_program_original_idle_source environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCStatus environment critical sg observer origin state before current after frame actual)
| KernelOriginalTaskCreationIdleSource : forall state before input current after output
    (actual : CreationComponent.kernel_task_creation_c_segment sg state before input current after output),
    kernel_program_original_idle_source environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCTaskCreation environment critical sg observer origin state before input current after output actual)
| KernelOriginalEventCreationIdleSource : forall state before input current after output
    (actual : EventCreationComponent.kernel_event_creation_c_segment sg state before input current after output),
    kernel_program_original_idle_source environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCEventCreation environment critical sg observer origin state before input current after output actual)
| KernelOriginalQueueCreationIdleSource : forall state before input current after output
    (actual : QueueCreationComponent.kernel_queue_creation_c_segment sg state before input current after output),
    kernel_program_original_idle_source environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCQueueCreation environment critical sg observer origin state before input current after output actual)
| KernelOriginalMutexPendIdleSource : forall local frame call before after
    (actual : PendComponent.mutex_pend_inheritance_c_segment environment critical local sg frame call before after),
    kernel_program_original_idle_source environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCMutexPend environment critical sg observer origin local frame call before after actual)
| KernelOriginalMutexPostIdleSource : forall source_env local frame call before after
    (actual : PostComponent.mutex_post_critical_c_segment source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg frame call before after),
    kernel_program_original_idle_source environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCMutexPost environment critical sg observer origin source_env local frame call before after actual)
| KernelOriginalDeletePrimitiveIdleSource : forall state before input stopped current after output
    (actual : DeleteComponent.task_delete_primitive_c_segment environment critical sg state before input stopped current after output),
    kernel_program_original_idle_source environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCDeletePrimitive environment critical sg observer origin state before input stopped current after output actual)
| KernelOriginalPairedPrimitiveIdleSource : forall state before input stopped current after output
    (actual : flag_pend_task_primitive_c_step environment critical sg state before input stopped current after output),
    kernel_program_original_idle_source environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCPairedPrimitive environment critical sg observer origin state before input stopped current after output actual)
| KernelOriginalDeleteIdleSource : forall state before input stopped current after output
    (actual : DeleteComponent.task_delete_own_c_segment environment critical sg observer origin state before input stopped current after output),
    kernel_program_original_idle_source environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCDelete environment critical sg observer origin state before input stopped current after output actual).

Inductive kernel_program_return_idle_source environment critical sg observer origin :
  forall state before input stopped current after output,
  kernel_program_return_c_step environment critical sg observer origin state before input stopped current after output -> Prop :=
| KernelReturnOriginalIdleSource : forall state before input stopped current after output actual,
    kernel_program_original_idle_source environment critical sg observer origin state before input stopped current after output actual ->
    kernel_program_return_idle_source environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramReturnOriginal environment critical sg observer origin state before input stopped current after output actual)
| KernelReturnPrimitiveIdleSource : forall state before input stopped current after output actual,
    kernel_program_return_idle_source environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramReturnSelected environment critical sg observer origin state before input stopped current after output actual)
| KernelReturnInstallIdleSource : forall local frame call before installed sp actual complete selected terminal owner,
    kernel_program_return_idle_source environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramReturnTaskSelectedInstall environment critical sg observer origin local frame call before installed sp actual
        complete selected terminal owner)
| KernelReturnIRQIdleSource : forall handler entry transfer original saved acquired receipt other frame before installed selected after
    source install restore complete,
    kernel_program_return_idle_source environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramReturnIRQSelectedSuffix environment critical sg observer origin handler entry transfer original saved acquired
        receipt other frame before installed selected after source install restore complete).

Inductive kernel_program_selected_idle_source_index critical sg observer origin :
  forall environment state before input stopped current after output,
  kernel_program_selected_c_step environment critical sg observer origin state before input stopped current after output -> Prop :=
| KernelSelectedReturnIdleSource : forall environment state before input stopped current after output actual,
    kernel_program_return_idle_source environment critical sg observer origin state before input stopped current after output actual ->
    kernel_program_selected_idle_source_index critical sg observer origin environment _ _ _ _ _ _ _
      (@KernelSelectedProgramReturn critical sg observer origin environment state before input stopped current after output actual)
| KernelSelectedIRQIdleSource : forall environment state before input stopped current after output actual,
    kernel_program_selected_idle_source_index critical sg observer origin (task_sw_hook_call_environment environment) _ _ _ _ _ _ _
      (@KernelSelectedProgramIRQ critical sg observer origin environment state before input stopped current after output actual)
| KernelSelectedSuspendIdleSource : forall environment state before input stopped current after output actual,
    kernel_program_selected_idle_source_index critical sg observer origin environment _ _ _ _ _ _ _
      (@KernelSelectedProgramSuspend critical sg observer origin environment state before input stopped current after output actual).

Definition kernel_program_selected_idle_source environment critical sg observer origin :=
  kernel_program_selected_idle_source_index critical sg observer origin environment.

Definition kernel_program_selected_sequence_idle_source environment critical sg observer origin
  state before input stopped current after output
  (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    state before input stopped current after output) : Prop :=
  kernel_c_sequence_has_source (kernel_program_selected_c_step environment critical sg observer origin)
    (kernel_program_selected_idle_source environment critical sg observer origin)
    state before input stopped current after output run.

Lemma kernel_program_original_idle_source_transport :
  forall environment critical sg observed state before input stopped current after output
    (step : kernel_program_c_step environment critical sg observed.(os_sched_call_invocation)
      observed.(os_sched_call_origin) state before input stopped current after output),
  kernel_program_original_idle_source environment critical sg observed.(os_sched_call_invocation)
    observed.(os_sched_call_origin) _ _ _ _ _ _ _ step ->
  observed.(os_sched_call_origin) = RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot)
    observed.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(SchedState).(isRunning) = true -> stopped = false ->
  (task_idle_ready sg state.(TskState) -> task_idle_ready sg current.(TskState)) /\
  (flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed current).
Proof.
  intros environment critical sg observed state before input stopped current after output step Hsource Horigin Hrunning Hstop.
  destruct Hsource.
  - eapply kernel_critical_c_segment_idle_non_idle; eassumption.
  - eapply kernel_builtin_c_segment_idle_non_idle; eassumption.
  - eapply task_install_c_step_idle_non_idle; eassumption.
  - eapply kernel_wake_c_segment_idle_non_idle; eassumption.
  - eapply kernel_status_c_segment_idle_non_idle; eassumption.
  - eapply kernel_task_creation_c_segment_idle_non_idle; eassumption.
  - eapply kernel_event_creation_c_segment_idle_non_idle; eassumption.
  - eapply kernel_queue_creation_c_segment_idle_non_idle; eassumption.
  - eapply mutex_pend_inheritance_c_segment_idle_non_idle; eassumption.
  - eapply mutex_post_critical_c_segment_idle_non_idle; eassumption.
  - eapply task_delete_primitive_c_segment_idle_non_idle; eassumption.
  - eapply flag_pend_task_primitive_c_step_idle_non_idle; eassumption.
  - eapply task_delete_own_c_segment_idle_non_idle; eassumption.
Qed.

Lemma kernel_program_return_idle_source_transport :
  forall environment critical sg observed state before input stopped current after output
    (step : kernel_program_return_c_step environment critical sg observed.(os_sched_call_invocation)
      observed.(os_sched_call_origin) state before input stopped current after output),
  kernel_program_return_idle_source environment critical sg observed.(os_sched_call_invocation)
    observed.(os_sched_call_origin) _ _ _ _ _ _ _ step ->
  observed.(os_sched_call_origin) = RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot)
    observed.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(SchedState).(isRunning) = true -> stopped = false ->
  (task_idle_ready sg state.(TskState) -> task_idle_ready sg current.(TskState)) /\
  (flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed current).
Proof.
  intros environment critical sg observed state before input stopped current after output step Hsource Horigin Hrunning Hstop.
  destruct Hsource.
  - eapply kernel_program_original_idle_source_transport; eassumption.
  - destruct (kernel_selected_return_c_step_state_stop _ _ _ _ _ _ _ _ actual) as [-> _]; split; trivial.
  - apply task_used_map_eq_idle_non_idle; reflexivity.
  - apply task_used_map_eq_idle_non_idle; reflexivity.
Qed.

Lemma kernel_program_selected_idle_source_transport :
  forall environment critical sg observed state before input stopped current after output
    (step : kernel_program_selected_c_step environment critical sg observed.(os_sched_call_invocation)
      observed.(os_sched_call_origin) state before input stopped current after output),
  kernel_program_selected_idle_source environment critical sg observed.(os_sched_call_invocation)
    observed.(os_sched_call_origin) _ _ _ _ _ _ _ step ->
  observed.(os_sched_call_origin) = RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot)
    observed.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(SchedState).(isRunning) = true -> stopped = false ->
  (task_idle_ready sg state.(TskState) -> task_idle_ready sg current.(TskState)) /\
  (flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed current).
Proof.
  intros environment critical sg observed state before input stopped current after output step Hsource Horigin Hrunning Hstop.
  destruct Hsource.
  - eapply kernel_program_return_idle_source_transport; eassumption.
  - destruct actual.
    apply task_used_map_eq_idle_non_idle.
    exact (proj1 (BuiltinComponent.os_int_exit_configured_transfer_state_frame environment sg handler entry transfer source)).
  - eapply TaskSuspendMaskedC.task_suspend_masked_c_step_idle_non_idle; exact actual.
Qed.

Lemma kernel_program_selected_sequence_idle_source_transport :
  forall environment critical sg observed state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observed.(os_sched_call_invocation)
      observed.(os_sched_call_origin)) state before input stopped current after output),
  kernel_program_selected_sequence_idle_source environment critical sg observed.(os_sched_call_invocation)
    observed.(os_sched_call_origin) _ _ _ _ _ _ _ run ->
  observed.(os_sched_call_origin) = RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot)
    observed.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(SchedState).(isRunning) = true -> stopped = false ->
  (task_idle_ready sg state.(TskState) -> task_idle_ready sg current.(TskState)) /\
  (flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed current).
Proof.
  intros environment critical sg observed state before input stopped current after output run Hsource Horigin.
  induction Hsource; intros Hrunning Hstop.
  - split; trivial.
  - eapply kernel_program_selected_idle_source_transport; eassumption.
  - apply Bool.orb_false_iff in Hstop; destruct Hstop as [Hfirst_stop Hlast_stop].
    destruct (IHHsource1 Hrunning Hfirst_stop) as [Hfirst_idle Hfirst_non_idle].
    assert (Hmiddle_running : middle.(SchedState).(isRunning) = true).
    { rewrite (kernel_program_selected_c_sequence_running environment critical sg
        observed.(os_sched_call_invocation) observed.(os_sched_call_origin) _ _ _ _ _ _ _ first).
      exact Hrunning. }
    destruct (IHHsource2 Hmiddle_running Hlast_stop) as [Hlast_idle Hlast_non_idle].
    split; auto.
  - apply IHHsource; assumption.
Qed.

(** The stop bit is computed by the same run's lifecycle.  The actual
    selected return supplies normal/source, so no stopped=false assumption
    is added to the completed-call consumer. *)
Lemma kernel_program_selected_completed_sequence_idle_non_idle :
  forall environment critical sg original returned state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin)) state before input stopped current after output),
  kernel_program_selected_sequence_idle_source environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) _ _ _ _ _ _ _ run ->
  task_in_range sg state.(TskState) -> kernel_call_task_source original state ->
  state.(SchedState).(isRunning) = true ->
  kernel_call_normal_return original state returned current -> kernel_call_task_source returned current ->
  stopped = false /\
  (task_idle_ready sg state.(TskState) -> task_idle_ready sg current.(TskState)) /\
  (flag_pend_non_idle_at sg original state -> flag_pend_non_idle_at sg returned current).
Proof.
  intros environment critical sg original returned state before input stopped current after output run
    Hsource Hrange Horiginal Hrunning Hnormal Hreturned.
  assert (Hstop : stopped = false).
  { eapply sched_observer_spec.kernel_call_completed_task_source_not_stopped;
      [exact Hrange|exact Horiginal| |exact Hnormal|exact Hreturned].
    eapply kernel_program_selected_c_sequence_observer_lifetime; exact run. }
  destruct (kernel_program_selected_sequence_idle_source_transport environment critical sg original
    _ _ _ _ _ _ _ run Hsource (proj1 Horiginal) Hrunning Hstop) as [Hidle Hnonidle].
  split; [exact Hstop|]. split; [exact Hidle|].
  intro Hinitial; specialize (Hnonidle Hinitial).
  unfold flag_pend_non_idle_at in *.
  rewrite (proj2 (proj2 (proj1 Hnormal))); exact Hnonidle.
Qed.

End SelectedIdleComposition.
