(** Report-only ordinary module extracted from the frozen checked C context.
    The original proof bodies are retained under the recorded shared-reference map. *)
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
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_always_nonswitch_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_wake_source_spec.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_region_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_nontimer_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.flag_fields_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.lib.kernel_execution.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_local_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_irq_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.lib.task_retirement.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_sched_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_inherit_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_client_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_return_spec.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_api_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_disabled_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.lib.flag_stack.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_unlink_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_source_call_spec.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.lib.flag_node_fields.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_unlink_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_fields_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_fields_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_api_entry_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_return_stage_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_idle_ready_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_call_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_save_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_wake_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_irq_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_delete_source_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_c_segment_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_create_c_segment_spec.
Require Export Ucos2Verify.VC.code.queue.spec.q_create_c_segment_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_priority_c_segment_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_del_c_segment_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.interrupt.spec.interrupt_call_c_primitive_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
(** Finite module C leaves.  The selected environment, critical region and
    configuration are fixed.  A leaf retains its own local owner and frame;
    their adaptation occurs at the same heap in kernel_c_sequence. *)
Section KernelProgramCSegments.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (observer : nat) (observer_origin : TaskInvocationOrigin).

Inductive kernel_program_c_step : kernel_c_sequence_spec.KernelCSegmentRelation :=
| KernelProgramCCritical : forall local frame call before after,
    CriticalComponent.kernel_critical_c_segment environment critical local sg frame call before after ->
    kernel_program_c_step (CriticalComponent.kernel_critical_c_entry call) before
      (CriticalComponent.kernel_critical_c_owner environment critical local sg call
        (CriticalComponent.kernel_critical_c_entry call) ** frame) false
      (CriticalComponent.kernel_critical_c_returned call) after
      (CriticalComponent.kernel_critical_c_owner environment critical local sg call
        (CriticalComponent.kernel_critical_c_returned call) ** frame)
| KernelProgramCBuiltin : forall local state before returned after input output,
    BuiltinComponent.kernel_builtin_c_segment environment critical local sg
      state before returned after input output ->
    kernel_program_c_step state before input false returned after output
| KernelProgramCInstall : forall local state before input stopped returned after output,
    InstallComponent.task_install_c_step environment local sg
      state before input stopped returned after output ->
    kernel_program_c_step state before input stopped returned after output
| KernelProgramCWake : forall state before input returned after output,
    WakeComponent.kernel_wake_c_segment sg state before input returned after output ->
    kernel_program_c_step state before input false returned after output
| KernelProgramCStatus : forall state before returned after frame,
    StatusComponent.kernel_status_c_segment sg state before returned after frame ->
    kernel_program_c_step state before (UCOS2_inv sg state ** frame) false
      returned after (UCOS2_inv sg returned ** frame)
| KernelProgramCTaskCreation : forall state before input returned after output,
    CreationComponent.kernel_task_creation_c_segment sg state before input returned after output ->
    kernel_program_c_step state before input false returned after output
| KernelProgramCEventCreation : forall state before input returned after output,
    EventCreationComponent.kernel_event_creation_c_segment sg state before input returned after output ->
    kernel_program_c_step state before input false returned after output
| KernelProgramCQueueCreation : forall state before input returned after output,
    QueueCreationComponent.kernel_queue_creation_c_segment sg state before input returned after output ->
    kernel_program_c_step state before input false returned after output
| KernelProgramCMutexPend : forall local frame call before after,
    PendComponent.mutex_pend_inheritance_c_segment environment critical local sg frame call before after ->
    kernel_program_c_step call.(PendComponent.mutex_pend_inheritance_entry) before
      (PendComponent.mutex_pend_inheritance_c_owner environment critical local sg call
        call.(PendComponent.mutex_pend_inheritance_entry) ** frame) false
      call.(PendComponent.mutex_pend_inheritance_returned) after
      (PendComponent.mutex_pend_inheritance_c_owner environment critical local sg call
        call.(PendComponent.mutex_pend_inheritance_returned) ** frame)
| KernelProgramCMutexPost : forall source_env local frame call before after,
    PostComponent.mutex_post_critical_c_segment source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg frame call before after ->
    kernel_program_c_step call.(PostComponent.mutex_post_critical_entry) before
      (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
        environment.(task_stack_call_platform) critical local sg call
        call.(PostComponent.mutex_post_critical_entry) ** frame) false
      call.(PostComponent.mutex_post_critical_checkpoint) after
      (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
        environment.(task_stack_call_platform) critical local sg call
        call.(PostComponent.mutex_post_critical_checkpoint) ** frame)
| KernelProgramCDeletePrimitive : forall state before input stopped returned after output,
    DeleteComponent.task_delete_primitive_c_segment environment critical sg
      state before input stopped returned after output ->
    kernel_program_c_step state before input stopped returned after output
| KernelProgramCPairedPrimitive : forall state before input stopped returned after output,
    PrimitiveComponent.flag_pend_task_primitive_c_step environment critical sg
      state before input stopped returned after output ->
    kernel_program_c_step state before input stopped returned after output
| KernelProgramCDelete : forall state before input stopped returned after output,
    DeleteComponent.task_delete_own_c_segment environment critical sg observer observer_origin
      state before input stopped returned after output ->
    kernel_program_c_step state before input stopped returned after output.

Lemma kernel_program_c_step_resources : forall state before input stopped returned after output,
  kernel_program_c_step state before input stopped returned after output ->
  input before /\ output after.
Proof.
  intros state before input stopped returned after output Hstep; destruct Hstep.
  - eapply CriticalComponent.kernel_critical_c_segment_resources; eassumption.
  - eapply BuiltinComponent.kernel_builtin_c_segment_resources; eassumption.
  - eapply InstallComponent.task_install_c_step_resources; eassumption.
  - eapply WakeComponent.kernel_wake_c_segment_resources; eassumption.
  - eapply StatusComponent.kernel_status_c_segment_resources; eassumption.
  - eapply CreationComponent.kernel_task_creation_c_segment_resources; eassumption.
  - eapply EventCreationComponent.kernel_event_creation_c_segment_resources; eassumption.
  - eapply QueueCreationComponent.kernel_queue_creation_c_segment_resources; eassumption.
  - eapply PendComponent.mutex_pend_inheritance_c_segment_resources; eassumption.
  - eapply PostComponent.mutex_post_critical_c_segment_resources; eassumption.
  - eapply DeleteComponent.task_delete_primitive_c_segment_resources; eassumption.
  - eapply PrimitiveComponent.flag_pend_task_primitive_c_step_resources; eassumption.
  - eapply DeleteComponent.task_delete_own_c_segment_resources; eassumption.
Qed.

Lemma kernel_program_c_step_preserves_observer : forall state before input stopped returned after output,
  kernel_program_c_step state before input stopped returned after output -> stopped = false ->
  task_invocation_active state.(TskState) observer observer_origin /\
    sched_observer_spec.sched_observer_current_cache observer_origin state ->
  task_invocation_active returned.(TskState) observer observer_origin /\
    sched_observer_spec.sched_observer_current_cache observer_origin returned.
Proof.
  intros state before input stopped returned after output Hstep Hstop Hinitial; destruct Hstep.
  - eapply CriticalComponent.kernel_critical_c_segment_preserves_observer; eassumption.
  - destruct Hinitial as [Hactive Hcache].
    eapply BuiltinComponent.kernel_builtin_c_segment_preserves_observer; eassumption.
  - eapply InstallComponent.task_install_c_step_preserves_observer; eassumption.
  - eapply WakeComponent.kernel_wake_c_segment_preserves_observer; eassumption.
  - eapply StatusComponent.kernel_status_c_segment_preserves_observer; eassumption.
  - eapply CreationComponent.kernel_task_creation_c_segment_preserves_observer; eassumption.
  - eapply EventCreationComponent.kernel_event_creation_c_segment_preserves_observer; eassumption.
  - eapply QueueCreationComponent.kernel_queue_creation_c_segment_preserves_observer; eassumption.
  - eapply PendComponent.mutex_pend_inheritance_c_segment_preserves_observer; eassumption.
  - eapply PostComponent.mutex_post_critical_c_segment_preserves_observer; eassumption.
  - eapply DeleteComponent.task_delete_primitive_c_segment_preserves_observer; eassumption.
  - eapply PrimitiveComponent.flag_pend_task_primitive_c_step_preserves_observer; eassumption.
  - eapply DeleteComponent.task_delete_own_c_segment_preserves_observer; eassumption.
Qed.

Lemma kernel_program_c_step_observer_lifetime : forall state before input stopped returned after output,
  kernel_program_c_step state before input stopped returned after output ->
  sched_observer_spec.task_observer_lifetime_result observer observer_origin
    state.(TskState) returned.(TskState) stopped.
Proof.
  intros state before input stopped returned after output Hstep; destruct Hstep.
  - eapply CriticalComponent.kernel_critical_c_segment_observer_lifetime_result; eassumption.
  - eapply BuiltinComponent.kernel_builtin_c_segment_lifetime_result; eassumption.
  - eapply InstallComponent.task_install_c_step_observer_lifetime_result; eassumption.
  - eapply WakeComponent.kernel_wake_c_segment_lifetime_result; eassumption.
  - eapply StatusComponent.kernel_status_c_segment_lifetime_result; eassumption.
  - eapply CreationComponent.kernel_task_creation_c_segment_lifetime_result; eassumption.
  - eapply EventCreationComponent.kernel_event_creation_c_segment_lifetime_result; eassumption.
  - eapply QueueCreationComponent.kernel_queue_creation_c_segment_lifetime_result; eassumption.
  - eapply PendComponent.mutex_pend_inheritance_c_segment_lifetime_result; eassumption.
  - eapply PostComponent.mutex_post_critical_c_segment_lifetime_result; eassumption.
  - eapply DeleteComponent.task_delete_primitive_c_segment_observer_lifetime; eassumption.
  - eapply PrimitiveComponent.flag_pend_task_primitive_c_step_observer_lifetime; eassumption.
  - eapply DeleteComponent.task_delete_own_c_segment_observer_lifetime; eassumption.
Qed.

Lemma kernel_program_c_sequence_resources : forall state before input stopped returned after output,
  kernel_c_sequence_spec.kernel_c_sequence kernel_program_c_step state before input stopped returned after output ->
  input before /\ output after.
Proof.
  apply kernel_c_sequence_spec.kernel_c_sequence_resources.
  exact kernel_program_c_step_resources.
Qed.

Lemma kernel_program_c_sequence_preserves_observer : forall state before input stopped returned after output,
  kernel_c_sequence_spec.kernel_c_sequence kernel_program_c_step state before input stopped returned after output ->
  stopped = false ->
  task_invocation_active state.(TskState) observer observer_origin /\
    sched_observer_spec.sched_observer_current_cache observer_origin state ->
  task_invocation_active returned.(TskState) observer observer_origin /\
    sched_observer_spec.sched_observer_current_cache observer_origin returned.
Proof.
  apply kernel_c_sequence_spec.kernel_c_sequence_preserves_observer.
  exact kernel_program_c_step_preserves_observer.
Qed.

Lemma kernel_program_c_sequence_observer_lifetime : forall state before input stopped returned after output,
  kernel_c_sequence_spec.kernel_c_sequence kernel_program_c_step state before input stopped returned after output ->
  sched_observer_spec.task_observer_lifetime_result observer observer_origin
    state.(TskState) returned.(TskState) stopped.
Proof.
  apply kernel_c_sequence_spec.kernel_c_sequence_observer_lifetime.
  exact kernel_program_c_step_observer_lifetime.
Qed.
End KernelProgramCSegments.

(** This return consumer uses the original caller's observer throughout the
    actual C sequence, even while a different task or IRQ executes.  It
    neither classifies an arbitrary old generic source nor adds a cache law
    to a callee declaration.  The C producer must supply this very sequence. *)
Lemma kernel_program_c_sequence_completed_current_cache :
  forall environment critical sg original returned initial before input stopped current after output,
  kernel_c_sequence_spec.kernel_c_sequence
    (kernel_program_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial before input stopped current after output ->
  task_in_range sg initial.(TskState) -> kernel_call_task_source original initial ->
  sched_current_consistency initial.(TskState) initial.(SchedState) ->
  kernel_call_normal_return original initial returned current -> kernel_call_task_source returned current ->
  stopped = false /\ sched_current_consistency current.(TskState) current.(SchedState).
Proof.
  intros environment critical sg original returned.
  apply (kernel_c_sequence_spec.kernel_c_sequence_completed_current_cache
    (kernel_program_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin)) sg original returned).
  - exact (kernel_program_c_step_preserves_observer environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  - exact (kernel_program_c_step_observer_lifetime environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin)).
Qed.

(** Instantiate the TaskDel composite with the concrete program union.
    Both syntactic inclusions are discharged by its actual constructors.
    The original two captured sources, local frames and five heaps remain
    those of the checked body producer. *)
Import DeleteComponent CriticalComponent.

Definition task_delete_program_segment observer origin capture :=
  kernel_program_c_step
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_environment)
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_critical)
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_globals)
    observer origin.

Lemma kernel_program_task_delete_body_sequence :
  forall observer origin capture after_heap restore_selected restore_rely save_selected save_rely
    restore_stopped save_stopped,
  let segment := task_delete_program_segment observer origin capture in
  let restore := capture.(delete_save_restore) in
  let inputs := restore.(delete_restore_inputs) in
  task_delete_restore_capture_c_window segment restore restore_selected restore_rely restore_stopped ->
  task_delete_save_capture_c_window segment capture save_selected save_rely save_stopped ->
  task_delete_capture_completed capture after_heap ->
  kernel_c_sequence segment inputs.(delete_capture_acquired) restore.(delete_restore_before_heap)
    (task_delete_capture_before_owner inputs)
    (task_delete_capture_observer_stopped capture origin restore_stopped save_stopped)
    (task_delete_capture_cut capture) after_heap (task_delete_capture_recycled_owner capture).
Proof.
  intros observer origin capture after_heap restore_selected restore_rely save_selected save_rely
    restore_stopped save_stopped segment restore inputs Hrestore Hsave Hcompleted.
  eapply (task_delete_capture_c_body_sequence segment observer origin capture after_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped).
  - intros; apply KernelProgramCDelete; assumption.
  - intros; apply KernelProgramCDeletePrimitive; assumption.
  - exact Hrestore.
  - exact Hsave.
  - exact Hcompleted.
Qed.

(** This is a fixed C interpretation, not a law asserted about an arbitrary
    old linked predicate.  Its producer must supply the same actual C run;
    the raw endpoint observations are part of that run's original output. *)
Import CriticalComponent PrimitiveComponent.

Definition flag_pend_program_c_observer event : nat :=
  match event.(flag_pend_event_caller) with
  | FlagPendTaskCaller call => call.(os_sched_call_invocation)
  | FlagPendInterruptCaller view _ => view.(os_execution_invocation)
  end.

Definition flag_pend_program_c_origin event : TaskInvocationOrigin :=
  match event.(flag_pend_event_caller) with
  | FlagPendTaskCaller call => call.(os_sched_call_origin)
  | FlagPendInterruptCaller view _ => view.(os_execution_origin)
  end.

Definition flag_pend_program_c_event environment critical sg event : Prop :=
  exists stopped,
    kernel_c_sequence (kernel_program_c_step environment critical sg
      (flag_pend_program_c_observer event) (flag_pend_program_c_origin event))
      event.(flag_pend_event_before) event.(flag_pend_event_first_heap)
      event.(flag_pend_event_input) stopped event.(flag_pend_event_current)
      event.(flag_pend_event_last_heap) event.(flag_pend_event_output).

Definition flag_pend_task_save_completed_c_event environment critical local next_local active sg
  original mask saved before first_heap returned current last_heap : FlagPendLinkedEvent :=
  {| flag_pend_event_operation := FlagPendSaveSource;
     flag_pend_event_caller := FlagPendTaskCaller original;
     flag_pend_event_original := original;
     flag_pend_event_returned_caller := FlagPendTaskCaller returned;
     flag_pend_event_returned := returned;
     flag_pend_event_before := before;
     flag_pend_event_current := current;
     flag_pend_event_first_heap := first_heap;
     flag_pend_event_last_heap := last_heap;
     flag_pend_event_input := flag_pend_caller_save_input environment critical local active sg
       (FlagPendTaskCaller original) original mask before;
     flag_pend_event_output :=
       coq_prop (flag_pend_call_endpoint_observations environment sg
         (FlagPendTaskCaller original) original before returned current) &&
       flag_pend_caller_restore_input environment critical next_local active sg
         (FlagPendTaskCaller returned) returned saved current current |}.

Definition flag_pend_task_restore_completed_c_event environment critical local next_local active sg
  original saved acquired before first_heap returned current last_heap : FlagPendLinkedEvent :=
  {| flag_pend_event_operation := FlagPendRestoreSource;
     flag_pend_event_caller := FlagPendTaskCaller original;
     flag_pend_event_original := original;
     flag_pend_event_returned_caller := FlagPendTaskCaller returned;
     flag_pend_event_returned := returned;
     flag_pend_event_before := before;
     flag_pend_event_current := current;
     flag_pend_event_first_heap := first_heap;
     flag_pend_event_last_heap := last_heap;
     flag_pend_event_input := flag_pend_caller_restore_input environment critical local active sg
       (FlagPendTaskCaller original) original saved acquired before;
     flag_pend_event_output :=
       coq_prop (flag_pend_call_endpoint_observations environment sg
         (FlagPendTaskCaller original) original before returned current) &&
       flag_pend_caller_save_input environment critical next_local active sg
         (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current |}.

Lemma flag_pend_program_c_event_resources : forall environment critical sg event,
  flag_pend_program_c_event environment critical sg event ->
  event.(flag_pend_event_input) event.(flag_pend_event_first_heap) /\
    event.(flag_pend_event_output) event.(flag_pend_event_last_heap).
Proof.
  intros environment critical sg event [stopped Hrun].
  eapply kernel_program_c_sequence_resources; exact Hrun.
Qed.

Lemma flag_pend_program_c_event_primitive : forall environment critical sg event,
  flag_pend_task_primitive_c_event environment critical sg event ->
  flag_pend_program_c_event environment critical sg event.
Proof.
  intros environment critical sg event Hactual.
  exists false; apply KernelCSequenceAtom, KernelProgramCPairedPrimitive,
    FlagPendTaskPrimitiveCStep; exact Hactual.
Qed.

Lemma flag_pend_program_c_event_current_cache : forall environment critical sg event,
  flag_pend_program_c_event environment critical sg event ->
  event.(flag_pend_event_caller) = FlagPendTaskCaller event.(flag_pend_event_original) ->
  task_in_range sg event.(flag_pend_event_before).(TskState) ->
  kernel_call_task_source event.(flag_pend_event_original) event.(flag_pend_event_before) ->
  sched_current_consistency event.(flag_pend_event_before).(TskState)
    event.(flag_pend_event_before).(SchedState) ->
  kernel_call_normal_return event.(flag_pend_event_original) event.(flag_pend_event_before)
    event.(flag_pend_event_returned) event.(flag_pend_event_current) ->
  kernel_call_task_source event.(flag_pend_event_returned) event.(flag_pend_event_current) ->
  sched_current_consistency event.(flag_pend_event_current).(TskState)
    event.(flag_pend_event_current).(SchedState).
Proof.
  intros environment critical sg event [stopped Hrun] Hcaller Hrange Hsource Hcache Hnormal Hreturned.
  unfold flag_pend_program_c_observer, flag_pend_program_c_origin in Hrun.
  rewrite Hcaller in Hrun; cbn in Hrun.
  exact (proj2 (kernel_program_c_sequence_completed_current_cache environment critical sg
    event.(flag_pend_event_original) event.(flag_pend_event_returned)
    event.(flag_pend_event_before) event.(flag_pend_event_first_heap) event.(flag_pend_event_input)
    stopped event.(flag_pend_event_current) event.(flag_pend_event_last_heap) event.(flag_pend_event_output)
    Hrun Hrange Hsource Hcache Hnormal Hreturned)).
Qed.

Lemma flag_pend_program_c_save_event_input_range :
  forall environment critical local next_local active sg original mask saved before first_heap returned current last_heap,
  flag_pend_program_c_event environment critical sg
    (flag_pend_task_save_completed_c_event environment critical local next_local active sg
      original mask saved before first_heap returned current last_heap) ->
  task_in_range sg before.(TskState).
Proof.
  intros environment critical local next_local active sg original mask saved before first_heap returned current last_heap Hactual.
  pose proof (proj1 (flag_pend_program_c_event_resources _ _ _ _ Hactual)) as Hinput.
  exact (flag_pend_caller_save_input_task_in_range environment critical local active sg
    (FlagPendTaskCaller original) original mask before first_heap Hinput).
Qed.

Lemma flag_pend_program_c_restore_event_input_range :
  forall environment critical local next_local active sg original saved acquired before first_heap returned current last_heap,
  flag_pend_program_c_event environment critical sg
    (flag_pend_task_restore_completed_c_event environment critical local next_local active sg
      original saved acquired before first_heap returned current last_heap) ->
  task_in_range sg before.(TskState).
Proof.
  intros environment critical local next_local active sg original saved acquired before first_heap returned current last_heap Hactual.
  pose proof (proj1 (flag_pend_program_c_event_resources _ _ _ _ Hactual)) as Hinput.
  exact (flag_pend_caller_restore_input_task_in_range environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before first_heap Hinput).
Qed.

(** The same event gives its input range and output normal return.  Only
    the existing entry and returned Task-source observations are consumed.
    No public cache/ready/false-stop premise is added. *)
Lemma flag_pend_program_c_save_current_cache :
  forall environment critical local next_local active sg original mask saved before first_heap returned current last_heap,
  flag_pend_program_c_event environment critical sg
    (flag_pend_task_save_completed_c_event environment critical local next_local active sg
      original mask saved before first_heap returned current last_heap) ->
  kernel_call_task_source original before ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  kernel_call_task_source returned current ->
  sched_current_consistency current.(TskState) current.(SchedState).
Proof.
  intros environment critical local next_local active sg original mask saved before first_heap returned current last_heap
    Hactual Hsource Hcache Hreturned.
  pose proof (proj2 (flag_pend_program_c_event_resources _ _ _ _ Hactual)) as Houtput.
  destruct Houtput as [[Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]] Howned].
  eapply (flag_pend_program_c_event_current_cache environment critical sg
    (flag_pend_task_save_completed_c_event environment critical local next_local active sg
      original mask saved before first_heap returned current last_heap)); try eassumption; try reflexivity.
  exact (flag_pend_program_c_save_event_input_range environment critical local next_local active sg
    original mask saved before first_heap returned current last_heap Hactual).
Qed.

Lemma flag_pend_program_c_restore_current_cache :
  forall environment critical local next_local active sg original saved acquired before first_heap returned current last_heap,
  flag_pend_program_c_event environment critical sg
    (flag_pend_task_restore_completed_c_event environment critical local next_local active sg
      original saved acquired before first_heap returned current last_heap) ->
  kernel_call_task_source original before ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  kernel_call_task_source returned current ->
  sched_current_consistency current.(TskState) current.(SchedState).
Proof.
  intros environment critical local next_local active sg original saved acquired before first_heap returned current last_heap
    Hactual Hsource Hcache Hreturned.
  pose proof (proj2 (flag_pend_program_c_event_resources _ _ _ _ Hactual)) as Houtput.
  destruct Houtput as [[Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]] Howned].
  eapply (flag_pend_program_c_event_current_cache environment critical sg
    (flag_pend_task_restore_completed_c_event environment critical local next_local active sg
      original saved acquired before first_heap returned current last_heap)); try eassumption; try reflexivity.
  exact (flag_pend_program_c_restore_event_input_range environment critical local next_local active sg
    original saved acquired before first_heap returned current last_heap Hactual).
Qed.

(** The selected source has a concrete interpretation for each original
    caller kind.  Task execution uses the proved C program.  IRQ execution
    additionally admits the already explicit view primitive contract; that
    contract is not promoted to a Task cache-preservation law. *)
Import CriticalComponent PrimitiveComponent.

Lemma kernel_c_sequence_map : forall (source target : KernelCSegmentRelation),
  (forall state before input stopped returned after output,
    source state before input stopped returned after output ->
    target state before input stopped returned after output) ->
  forall state before input stopped returned after output,
  kernel_c_sequence source state before input stopped returned after output ->
  kernel_c_sequence target state before input stopped returned after output.
Proof.
  intros source target Hinclusion state before input stopped returned after output Hsequence.
  induction Hsequence.
  - apply KernelCSequenceRefl; assumption.
  - apply KernelCSequenceAtom; apply Hinclusion; assumption.
  - eapply KernelCSequenceThen; eassumption.
  - eapply KernelCSequenceAdapt; eassumption.
Qed.

Section FlagPendInterruptProgram.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (view : OsExecutionView).

Inductive flag_pend_interrupt_program_c_step : KernelCSegmentRelation :=
| FlagPendInterruptProgramC : forall state before input stopped returned after output,
    kernel_program_c_step environment critical sg
      view.(os_execution_invocation) view.(os_execution_origin)
      state before input stopped returned after output ->
    flag_pend_interrupt_program_c_step state before input stopped returned after output
| FlagPendInterruptViewPrimitiveC : forall state before input stopped returned after output,
    ViewPrimitiveComponent.flag_pend_view_primitive_c_step environment critical sg
      view.(os_execution_invocation) view.(os_execution_origin)
      state before input stopped returned after output ->
    flag_pend_interrupt_program_c_step state before input stopped returned after output.

Lemma flag_pend_interrupt_program_c_step_resources :
  forall state before input stopped returned after output,
  flag_pend_interrupt_program_c_step state before input stopped returned after output ->
  input before /\ output after.
Proof.
  intros state before input stopped returned after output Hstep; destruct Hstep.
  - eapply kernel_program_c_step_resources; eassumption.
  - eapply ViewPrimitiveComponent.flag_pend_view_primitive_c_step_resources; eassumption.
Qed.
End FlagPendInterruptProgram.

Definition flag_pend_selected_c_step environment critical sg caller : KernelCSegmentRelation :=
  match caller with
  | FlagPendTaskCaller call => kernel_program_c_step environment critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin)
  | FlagPendInterruptCaller view _ => flag_pend_interrupt_program_c_step environment critical sg view
  end.

Definition flag_pend_selected_event_source environment critical sg event : Prop :=
  exists stopped,
    kernel_c_sequence
      (flag_pend_selected_c_step environment critical sg event.(flag_pend_event_caller))
      event.(flag_pend_event_before) event.(flag_pend_event_first_heap)
      event.(flag_pend_event_input) stopped event.(flag_pend_event_current)
      event.(flag_pend_event_last_heap) event.(flag_pend_event_output).

Lemma flag_pend_selected_event_source_resources : forall environment critical sg event,
  flag_pend_selected_event_source environment critical sg event ->
  event.(flag_pend_event_input) event.(flag_pend_event_first_heap) /\
  event.(flag_pend_event_output) event.(flag_pend_event_last_heap).
Proof.
  intros environment critical sg event [stopped Hsequence].
  eapply kernel_c_sequence_resources; [|exact Hsequence].
  unfold flag_pend_selected_c_step; destruct event.(flag_pend_event_caller) as [call|view key].
  - exact (kernel_program_c_step_resources environment critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin)).
  - apply flag_pend_interrupt_program_c_step_resources.
Qed.

(** Existing actual C executions remain admitted on both Task and IRQ
    paths.  This inclusion retains every state, heap, owner and stop bit. *)
Lemma flag_pend_selected_event_source_from_program : forall environment critical sg event,
  flag_pend_program_c_event environment critical sg event ->
  flag_pend_selected_event_source environment critical sg event.
Proof.
  intros environment critical sg event [stopped Hsequence].
  exists stopped; unfold flag_pend_selected_c_step.
  unfold flag_pend_program_c_observer, flag_pend_program_c_origin in Hsequence.
  destruct event.(flag_pend_event_caller) as [call|view key]; cbn in *.
  - exact Hsequence.
  - eapply kernel_c_sequence_map; [|exact Hsequence].
    intros; apply FlagPendInterruptProgramC; assumption.
Qed.

Lemma flag_pend_selected_event_source_from_view : forall environment critical sg view key event,
  event.(flag_pend_event_caller) = FlagPendInterruptCaller view key ->
  ViewPrimitiveComponent.flag_pend_view_primitive_completion environment critical sg event ->
  flag_pend_selected_event_source environment critical sg event.
Proof.
  intros environment critical sg view key event Hcaller Hactual.
  exists false; unfold flag_pend_selected_c_step; rewrite Hcaller.
  apply KernelCSequenceAtom, FlagPendInterruptViewPrimitiveC.
  eapply (ViewPrimitiveComponent.FlagPendViewPrimitiveCStep environment critical sg
    view.(os_execution_invocation) view.(os_execution_origin) view key event);
    [exact Hcaller|reflexivity|reflexivity|exact Hactual].
Qed.

(** This indexed interface exports only resources from the same source.
    Its concrete value below is a definition with a proved field, not an
    arbitrary callee parameter or a new platform assumption.  Cache follows
    from its Task interpretation in a separate proved consumer. *)
Record FlagPendProgramSources (environment : TaskStackCallEnvironment)
  (critical : CriticalRegionResources) (sg : StableGlobVars) : Type := {
  flag_pend_program_event_source : FlagPendLinkedEvent -> Prop;
  flag_pend_program_event_resources : forall event,
    flag_pend_program_event_source event ->
    event.(flag_pend_event_input) event.(flag_pend_event_first_heap) /\
    event.(flag_pend_event_output) event.(flag_pend_event_last_heap)
}.

Definition flag_pend_selected_linked_sources environment critical sg :
  FlagPendProgramSources environment critical sg :=
  {| flag_pend_program_event_source := flag_pend_selected_event_source environment critical sg;
     flag_pend_program_event_resources := flag_pend_selected_event_source_resources environment critical sg |}.

Definition flag_pend_selected_linked_prefix environment critical sg operation caller original before
  returned_caller returned current (input : Assertion) first_heap (output : Assertion) last_heap : Prop :=
  flag_pend_program_event_source environment critical sg
    (flag_pend_selected_linked_sources environment critical sg)
    {| flag_pend_event_operation := operation;
       flag_pend_event_caller := caller;
       flag_pend_event_original := original;
       flag_pend_event_returned_caller := returned_caller;
       flag_pend_event_returned := returned;
       flag_pend_event_before := before;
       flag_pend_event_current := current;
       flag_pend_event_first_heap := first_heap;
       flag_pend_event_last_heap := last_heap;
       flag_pend_event_input := input;
       flag_pend_event_output := output |}.

Lemma flag_pend_selected_linked_prefix_resources : forall environment critical sg operation caller original before
  returned_caller returned current input first_heap output last_heap,
  flag_pend_selected_linked_prefix environment critical sg operation caller original before
    returned_caller returned current input first_heap output last_heap ->
  input first_heap /\ output last_heap.
Proof.
  intros; exact (flag_pend_program_event_resources environment critical sg
    (flag_pend_selected_linked_sources environment critical sg) _ H).
Qed.

Definition flag_pend_selected_completed_source operation environment critical sg caller original before
  (input : Assertion) first_heap returned_caller returned current last_heap (output : Assertion) : Prop :=
  flag_pend_selected_linked_prefix environment critical sg operation caller original before
    returned_caller returned current input first_heap
    (coq_prop (flag_pend_call_endpoint_observations environment sg caller original before returned current) && output)
    last_heap.

Lemma flag_pend_selected_completed_source_endpoints : forall operation environment critical sg caller original before
  input first_heap returned_caller returned current last_heap output,
  flag_pend_selected_completed_source operation environment critical sg caller original before
    input first_heap returned_caller returned current last_heap output ->
  flag_pend_call_endpoint_observations environment sg caller original before returned current /\
    input first_heap /\ output last_heap.
Proof.
  intros operation environment critical sg caller original before input first_heap
    returned_caller returned current last_heap output Hactual.
  destruct (flag_pend_selected_linked_prefix_resources environment critical sg operation caller original before
    returned_caller returned current input first_heap _ last_heap Hactual) as [Hinput [Hendpoints Houtput]].
  exact (conj Hendpoints (conj Hinput Houtput)).
Qed.

Lemma flag_pend_selected_event_source_current_cache : forall environment critical sg event,
  flag_pend_selected_event_source environment critical sg event ->
  event.(flag_pend_event_caller) = FlagPendTaskCaller event.(flag_pend_event_original) ->
  task_in_range sg event.(flag_pend_event_before).(TskState) ->
  kernel_call_task_source event.(flag_pend_event_original) event.(flag_pend_event_before) ->
  sched_current_consistency event.(flag_pend_event_before).(TskState)
    event.(flag_pend_event_before).(SchedState) ->
  kernel_call_normal_return event.(flag_pend_event_original) event.(flag_pend_event_before)
    event.(flag_pend_event_returned) event.(flag_pend_event_current) ->
  kernel_call_task_source event.(flag_pend_event_returned) event.(flag_pend_event_current) ->
  sched_current_consistency event.(flag_pend_event_current).(TskState)
    event.(flag_pend_event_current).(SchedState).
Proof.
  intros environment critical sg event [stopped Hsequence] Hcaller Hrange Hsource Hcache Hnormal Hreturned.
  unfold flag_pend_selected_c_step in Hsequence; rewrite Hcaller in Hsequence; cbn in Hsequence.
  exact (proj2 (kernel_program_c_sequence_completed_current_cache environment critical sg
    event.(flag_pend_event_original) event.(flag_pend_event_returned)
    event.(flag_pend_event_before) event.(flag_pend_event_first_heap) event.(flag_pend_event_input)
    stopped event.(flag_pend_event_current) event.(flag_pend_event_last_heap) event.(flag_pend_event_output)
    Hsequence Hrange Hsource Hcache Hnormal Hreturned)).
Qed.

Lemma flag_pend_selected_save_current_cache :
  forall environment critical local next_local active sg original mask saved before first_heap returned current last_heap,
  flag_pend_selected_event_source environment critical sg
    (flag_pend_task_save_completed_c_event environment critical local next_local active sg
      original mask saved before first_heap returned current last_heap) ->
  kernel_call_task_source original before ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  kernel_call_task_source returned current ->
  sched_current_consistency current.(TskState) current.(SchedState).
Proof.
  intros environment critical local next_local active sg original mask saved before first_heap returned current last_heap
    Hactual Hsource Hcache Hreturned.
  apply (flag_pend_program_c_save_current_cache environment critical local next_local active sg
    original mask saved before first_heap returned current last_heap); assumption.
Qed.

Lemma flag_pend_selected_restore_current_cache :
  forall environment critical local next_local active sg original saved acquired before first_heap returned current last_heap,
  flag_pend_selected_event_source environment critical sg
    (flag_pend_task_restore_completed_c_event environment critical local next_local active sg
      original saved acquired before first_heap returned current last_heap) ->
  kernel_call_task_source original before ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  kernel_call_task_source returned current ->
  sched_current_consistency current.(TskState) current.(SchedState).
Proof.
  intros environment critical local next_local active sg original saved acquired before first_heap returned current last_heap
    Hactual Hsource Hcache Hreturned.
  apply (flag_pend_program_c_restore_current_cache environment critical local next_local active sg
    original saved acquired before first_heap returned current last_heap); assumption.
Qed.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
(** Sources decorate the original C completion proof.  They retain the
    invocation/allocation from that completion; no constructor assumes any
    creation-frame, cache, ready or future-return conclusion. *)
Import EventStateDef.
Import EventStateDef.












(** Provenance follows the existing execution proof.  An atomic marker is
    supplied by that C module's actual call/allocation protocol.  In
    particular, it may retain a foreign invocation condition; it is not a
    second execution picked for its endpoints. *)
Import CriticalComponent.



(** A selected environment is an actual sequence of the fixed C program.
    Its existing return owner contains the original C endpoint contract.
    The ABI suffix/prefix below is composed with that very sequence; there
    is no independently supplied old source or endpoint-equal replacement
    tree.  State, caller, local resources and heaps may all change in the
    environment.  Its stopped bit is retained, not assumed false. *)
Import PrimitiveComponent.
