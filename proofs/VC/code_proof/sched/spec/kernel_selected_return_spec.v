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
Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_selected_completion_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_terminal_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


(** The missing C primitive is the actual selected return, after the C
    current/SP installation.  Its state is unchanged, but its two heaps
    need not be equal.  Both branches use the existing approved platform
    resource contract.  Initial task entry remains a real branch of that
    contract; it is not relabelled as a return of an earlier invocation. *)
Module SelectedReturnPrimitive.
Import CriticalComponent PrimitiveComponent TerminalReturn IRQSelectedCompletion.

Definition task_selected_return_input environment
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations)) outgoing selected (frame : Assertion) : Assertion :=
  armv7a_task_switch_control task_abi outgoing **
  task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
    selected.(armv7a_continuation_fragments) **
  armv7a_task_continuation_resource environment.(task_stack_call_continuations) selected ** frame.

Definition task_selected_return_output environment selected (frame : Assertion) : Assertion :=
  armv7a_task_restored_execution environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) selected ** frame.

Definition irq_selected_return_input environment handler selected (frame : Assertion) : Assertion :=
  interrupt_platform_running environment.(task_stack_call_platform)
    handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
  os_int_exit_context_resources environment.(task_stack_call_port) handler **
  task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
    selected.(armv7a_continuation_fragments) **
  armv7a_dormant_continuation environment.(task_stack_call_continuations) selected ** frame.

Definition irq_selected_return_output environment handler selected (frame : Assertion) : Assertion :=
  armv7a_task_restored_execution environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) selected **
  task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame.

Inductive kernel_selected_return_c_step (environment : TaskStackCallEnvironment) : KernelCSegmentRelation :=
| KernelSelectedReturnTask : forall task_abi state outgoing selected frame before after,
    armv7a_continuation_restore_reads selected before ->
    task_selected_return_input environment task_abi outgoing selected frame before ->
    armv7a_task_restore_transition task_abi outgoing selected before after ->
    kernel_selected_return_c_step environment state before
      (task_selected_return_input environment task_abi outgoing selected frame) false state after
      (task_selected_return_output environment selected frame)
| KernelSelectedReturnIRQ : forall state handler selected frame before after,
    armv7a_continuation_restore_reads selected before ->
    irq_selected_return_input environment handler selected frame before ->
    armv7a_restore_transition environment.(task_stack_call_continuations) handler selected before after ->
    kernel_selected_return_c_step environment state before
      (irq_selected_return_input environment handler selected frame) false state after
      (irq_selected_return_output environment handler selected frame).

Lemma kernel_selected_return_c_step_resources :
  forall environment state before input stopped returned after output,
  kernel_selected_return_c_step environment state before input stopped returned after output ->
  input before /\ output after.
Proof.
  intros environment state before input stopped returned after output Hstep; destruct Hstep.
  - split; [exact H0|].
    exact (proj2 (proj2 (armv7a_task_restore_resources _ _ _ _ task_abi
      outgoing selected frame before after H H0 H1))).
  - split; [exact H0|].
    exact (proj2 (armv7a_restore_transition_resources _ _ _
      environment.(task_stack_call_continuations) handler selected frame before after H H0 H1)).
Qed.

Lemma kernel_selected_return_c_step_state_stop :
  forall environment state before input stopped returned after output,
  kernel_selected_return_c_step environment state before input stopped returned after output ->
  returned = state /\ stopped = false.
Proof. intros; destruct H; split; reflexivity. Qed.

Lemma kernel_selected_return_c_step_creation_name_timer :
  forall environment state before input stopped returned after output,
  kernel_selected_return_c_step environment state before input stopped returned after output ->
  (forall observer, task_creation_frame observer state.(TskState) returned.(TskState)) /\
  (forall observer, event_creation_frame observer state.(EventState) returned.(EventState)) /\
  returned.(NameState) = state.(NameState) /\ returned.(TimerState) = state.(TimerState).
Proof.
  intros environment state before input stopped returned after output Hstep.
  destruct (kernel_selected_return_c_step_state_stop _ _ _ _ _ _ _ _ Hstep) as [-> _].
  repeat split; reflexivity.
Qed.

(** The old thirteen C families are retained literally.  This sum is the
    minimal report candidate for replacing the program's primitive union;
    it does not coerce an old flat trace into a classified execution. *)
Inductive kernel_program_return_c_step environment critical sg observer origin : KernelCSegmentRelation :=
| KernelProgramReturnOriginal : forall state before input stopped returned after output,
    kernel_program_c_step environment critical sg observer origin
      state before input stopped returned after output ->
    kernel_program_return_c_step environment critical sg observer origin
      state before input stopped returned after output
| KernelProgramReturnSelected : forall state before input stopped returned after output,
    kernel_selected_return_c_step environment state before input stopped returned after output ->
    kernel_program_return_c_step environment critical sg observer origin
      state before input stopped returned after output
| KernelProgramReturnTaskSelectedInstall : forall local frame call before installed sp actual complete selected,
    @task_install_c_terminal_return environment local sg frame call before installed sp actual complete
      (kernel_selected_call selected (InstallComponent.task_install_fields_current call)) ->
    task_install_selected_owner environment local sg frame call selected installed ->
    kernel_program_return_c_step environment critical sg observer origin
      call.(InstallComponent.task_install_fields_entry) before
      (InstallComponent.task_install_fields_entry_owner environment local sg call ** frame) false
      (InstallComponent.task_install_fields_current call) installed
      (task_install_selected_owner environment local sg frame call selected)
| KernelProgramReturnIRQSelectedSuffix :
    forall handler entry transfer original saved acquired receipt other frame before installed selected after source install restore,
    kernel_irq_selected_suffix_c_completion environment critical sg handler entry transfer original saved acquired receipt other
      frame before installed selected after source install restore ->
    kernel_program_return_c_step environment critical sg observer origin
      transfer.(os_int_exit_hooked_state) before
      (irq_selected_suffix_input environment critical sg handler transfer original saved acquired receipt other frame)
      false (os_int_exit_installed_state transfer) after
      (irq_selected_suffix_output environment critical sg handler transfer original saved acquired receipt other frame).

Lemma kernel_program_return_c_step_resources :
  forall environment critical sg observer origin state before input stopped returned after output,
  kernel_program_return_c_step environment critical sg observer origin
    state before input stopped returned after output -> input before /\ output after.
Proof.
  intros environment critical sg observer origin state before input stopped returned after output Hstep.
  destruct Hstep.
  - eapply kernel_program_c_step_resources; eassumption.
  - eapply kernel_selected_return_c_step_resources; eassumption.
  - split.
    + exact (proj1 (InstallComponent.task_install_c_segment_resources _ _ _ _ _ _ _ _ _ complete)).
    + exact H0.
  - eapply kernel_irq_selected_suffix_c_completion_resources; eassumption.
Qed.

Lemma kernel_program_return_c_step_preserves_observer :
  forall environment critical sg observer origin state before input stopped returned after output,
  kernel_program_return_c_step environment critical sg observer origin
    state before input stopped returned after output -> stopped = false ->
  task_invocation_active state.(TskState) observer origin /\ sched_observer_current_cache origin state ->
  task_invocation_active returned.(TskState) observer origin /\ sched_observer_current_cache origin returned.
Proof.
  intros environment critical sg observer origin state before input stopped returned after output Hstep Hstop Hinitial.
  destruct Hstep.
  - eapply kernel_program_c_step_preserves_observer; eassumption.
  - destruct (kernel_selected_return_c_step_state_stop _ _ _ _ _ _ _ _ H) as [-> _]; exact Hinitial.
  - eapply InstallComponent.task_install_c_segment_preserves_observer; [exact complete|exact (proj1 Hinitial)].
  - eapply kernel_irq_selected_suffix_c_completion_preserves_observer; [exact H|exact (proj1 Hinitial)].
Qed.

Lemma kernel_program_return_c_step_observer_lifetime :
  forall environment critical sg observer origin state before input stopped returned after output,
  kernel_program_return_c_step environment critical sg observer origin
    state before input stopped returned after output ->
  task_observer_lifetime_result observer origin state.(TskState) returned.(TskState) stopped.
Proof.
  intros environment critical sg observer origin state before input stopped returned after output Hstep.
  destruct Hstep.
  - eapply kernel_program_c_step_observer_lifetime; eassumption.
  - destruct (kernel_selected_return_c_step_state_stop _ _ _ _ _ _ _ _ H) as [-> ->].
    apply task_observer_lifetime_result_not_stopped, task_observer_lifetime_transport_refl.
  - eapply InstallComponent.task_install_c_segment_observer_lifetime_result; exact complete.
  - eapply kernel_irq_selected_suffix_c_completion_lifetime; exact H.
Qed.

Lemma kernel_program_c_sequence_include_selected_returns :
  forall environment critical sg observer origin state before input stopped returned after output,
  kernel_c_sequence (kernel_program_c_step environment critical sg observer origin)
    state before input stopped returned after output ->
  kernel_c_sequence (kernel_program_return_c_step environment critical sg observer origin)
    state before input stopped returned after output.
Proof.
  intros environment critical sg observer origin state before input stopped returned after output Hrun.
  induction Hrun.
  - constructor; exact H.
  - apply KernelCSequenceAtom, KernelProgramReturnOriginal; exact H.
  - eapply KernelCSequenceThen; eassumption.
  - eapply KernelCSequenceAdapt; eassumption.
Qed.

End SelectedReturnPrimitive.
