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
Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_acquired_return_spec.
Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_fields_prefix_spec.
Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_selected_completion_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_source_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_endpoint_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_environment_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_return_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_call_value_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_terminal_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


(** Actual selected completions enter the same selected C sequence.  The
    pure packet below is extracted from that completion's own resources;
    subsequent Save/Restore primitives retain it at their actual heaps. *)
Module SelectedCompletionComposition.
Import CriticalComponent PrimitiveComponent TerminalReturn TerminalCallValue FlagPendSchedulerResources.
Import SelectedCProgram SelectedCSource SelectedReturnPrimitive SelectedCompletionSource.
Import SelectedEnvironmentBuilder IRQAcquiredReturn IRQSelectedCompletion SelectedEndpointObservations.

Lemma task_selected_completion_environment_sequence :
  forall environment critical
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    sg observer origin event_observer frame call original saved acquired receipt other
    before installed sp actual,
  let local := kernel_sched_saved_local_resource_at environment.(task_stack_call_platform) critical sg
    call.(InstallComponent.task_install_fields_entry).(TskState) original saved acquired receipt other in
  let rest := armv7a_task_switch_control task_abi call.(InstallComponent.task_install_fields_context) **
    unmap_table_rep sg ** frame in
  forall (complete : InstallComponent.task_install_c_segment environment local sg rest call before installed sp actual),
  call.(InstallComponent.task_install_fields_incoming) = original.(os_sched_call_stack) ->
  task_stack_live_coverage call.(InstallComponent.task_install_fields_entry).(TskState)
    (Some (task_stack_key call.(InstallComponent.task_install_fields_context).(os_sched_call_stack))) ->
  exists selected, forall restored,
  armv7a_task_restore_transition task_abi call.(InstallComponent.task_install_fields_context) selected installed restored ->
  let current := InstallComponent.task_install_fields_current call in
  let returned := kernel_selected_call selected current in
  exists (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    call.(InstallComponent.task_install_fields_entry) before
    (InstallComponent.task_install_fields_entry_owner environment local sg call ** rest) false current restored
    (coq_prop (flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller original) original
       call.(InstallComponent.task_install_fields_entry) returned current) &&
     flag_pend_caller_restore_input environment critical other (fun _ _ => receipt ** frame) sg
       (FlagPendTaskCaller returned) returned saved acquired current)),
  kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ run /\ kernel_call_task_source returned current /\ task_tcb_init_stack_same_call returned original.
Proof.
  intros environment critical task_abi sg observer origin event_observer frame call original saved acquired receipt other
    before installed sp actual local rest complete Hincoming Hcoverage.
  pose proof (proj2 (InstallComponent.task_install_c_segment_resources
    environment local sg rest call before installed sp actual complete)) as Hpost.
  destruct (task_install_fields_installed_owner_selected environment local sg rest call installed Hpost)
    as [selected Hselected].
  exists selected; intros restored Hrestore current returned.
  destruct (task_selected_c_environment_return environment critical task_abi sg observer origin event_observer
    frame call original saved acquired receipt other before installed sp actual selected restored complete
    Hselected Hincoming Hcoverage Hrestore) as [old_run [Hold [Hreturned Hsame]]].
  destruct (kernel_program_return_sequence_include_acquired_irq_source environment critical sg observer origin
    event_observer _ _ _ _ _ _ _ old_run Hold) as [included Hincluded].
  pose proof (task_selected_c_completion_endpoints environment critical task_abi sg frame call original saved acquired
    receipt other before installed sp actual selected restored complete Hselected Hincoming Hcoverage Hrestore) as Hendpoint.
  pose proof (proj1 (kernel_program_selected_c_sequence_resources environment critical sg observer origin
    _ _ _ _ _ _ _ included)) as Hinput.
  pose (close := fun heap (Howner : flag_pend_caller_restore_input environment critical other
    (fun _ _ => receipt ** frame) sg (FlagPendTaskCaller returned) returned saved acquired current heap) =>
      conj Hendpoint Howner).
  exists (KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput (fun heap Howner => Howner) included close).
  split; [apply KernelCSourceAdapt; exact Hincluded|exact (conj Hreturned Hsame)].
Qed.

Lemma irq_acquired_completion_environment_sequence :
  forall environment critical sg observer origin event_observer handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap installed selected after source prefix hook install restore,
  kernel_irq_acquired_c_completion environment critical sg handler entry transfer original saved acquired receipt other
    frame before prepared hooked_heap installed selected after source prefix hook install restore ->
  let returned := kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack) transfer.(os_int_exit_incoming_fragments) in
  let current := os_int_exit_installed_state transfer in
  exists (run : kernel_c_sequence (kernel_program_selected_c_step (task_sw_hook_call_environment environment)
    critical sg observer origin) entry before
    (IRQCPrefix.os_int_exit_prefix_fields_owner (task_sw_hook_call_environment environment) critical sg handler entry
      original saved acquired receipt other frame) false current after
    (irq_selected_suffix_output (task_sw_hook_call_environment environment) critical sg handler transfer
      original saved acquired receipt other frame)),
  kernel_program_selected_c_sequence_source (task_sw_hook_call_environment environment) critical sg observer origin event_observer
    _ _ _ _ _ _ _ run /\ kernel_call_task_source returned current /\ task_tcb_init_stack_same_call returned original /\
  flag_pend_current_ready returned current /\
  (task_idle_ready sg entry.(TskState) -> task_idle_ready sg current.(TskState)) /\
  (flag_pend_non_idle_at sg original entry -> flag_pend_non_idle_at sg returned current) /\
  (forall initial, kernel_call_normal_return original initial returned current) /\
  current.(SchedState).(isRunning) = entry.(SchedState).(isRunning) /\
  os_sched_selection_enabled current = true.
Proof.
  intros environment critical sg observer origin event_observer handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap installed selected after source prefix hook install restore complete returned current.
  pose (primitive := @KernelIRQAcquiredReturnCStep environment critical sg handler entry transfer original saved acquired
    receipt other frame before prepared hooked_heap installed selected after source prefix hook install restore complete).
  pose (step := @KernelSelectedProgramIRQ critical sg observer origin environment _ _ _ _ _ _ _ primitive).
  exists (KernelCSequenceAtom _ _ _ _ _ _ _ _ step).
  split; [apply KernelCSourceAtom; unfold step; apply KernelSelectedProgramIRQSource|].
  destruct (kernel_irq_acquired_c_completion_task_source environment critical sg handler entry transfer original saved acquired
    receipt other frame before prepared hooked_heap installed selected after source prefix hook install restore complete)
    as [Hreturned Hsame].
  split; [exact Hreturned|]. split; [exact Hsame|].
  eapply irq_acquired_c_completion_endpoint_facts; exact complete.
Qed.

Lemma selected_c_sequence_after_original_prefix :
  forall environment critical sg observer origin event_observer initial first_heap first_input first_stop middle middle_heap
    first_output next_input last_stop current last_heap output
    (prefix : kernel_c_sequence (kernel_program_c_step environment critical sg observer origin)
      initial first_heap first_input first_stop middle middle_heap first_output)
    (bridge : first_output |-- next_input)
    (suffix : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      middle middle_heap next_input last_stop current last_heap output),
  kernel_program_c_sequence_call_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ prefix ->
  kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ suffix ->
  exists (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    initial first_heap first_input (orb first_stop last_stop) current last_heap output),
  kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ run.
Proof.
  intros environment critical sg observer origin event_observer initial first_heap first_input first_stop middle middle_heap
    first_output next_input last_stop current last_heap output prefix bridge suffix Hprefix Hsuffix.
  destruct (kernel_program_original_sequence_include_selected_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ prefix Hprefix) as [included Hincluded].
  exists (KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ included bridge suffix).
  apply KernelCSourceThen; assumption.
Qed.

Lemma selected_c_sequence_restore_preserves_packet :
  forall environment critical sg observer origin event_observer local active call saved acquired
    initial before input stopped current restored (packet : Prop) arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written middle final_cursor after
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      initial before input stopped current restored
      (coq_prop packet && flag_pend_caller_restore_input environment critical local active sg
        (FlagPendTaskCaller call) call saved acquired current)),
  kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ run ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor restored written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  let event := flag_pend_task_restore_c_event environment critical local active sg call saved acquired current restored after in
  exists (completed : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    initial before input (orb stopped false) current after
    (coq_prop packet && event.(flag_pend_event_output))),
  flag_pend_task_primitive_c_event environment critical sg event /\
  kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ completed.
Proof.
  intros environment critical sg observer origin event_observer local active call saved acquired initial before input stopped
    current restored packet arch restore cursor written middle final_cursor after run Hsource Hr0 Hmask Hprefix Hsuffix event.
  destruct (proj2 (kernel_program_selected_c_sequence_resources environment critical sg observer origin
    _ _ _ _ _ _ _ run)) as [Hpacket Hinput].
  assert (Hprimitive : flag_pend_task_primitive_c_event environment critical sg event).
  { unfold event; eapply FlagPendTaskPrimitiveRestore; eassumption. }
  pose (primitive := FlagPendTaskPrimitiveCStep environment critical sg event Hprimitive).
  pose (step := kernel_program_selected_paired_primitive environment critical sg observer origin _ _ _ _ _ _ _ primitive).
  pose (tail := KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput (fun heap Howner => Howner)
    (KernelCSequenceAtom _ _ _ _ _ _ _ _ step) (fun heap Howner => conj Hpacket Howner)).
  exists (KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ run (fun heap Howner => proj2 Howner) tail).
  split; [exact Hprimitive|].
  apply KernelCSourceThen; [exact Hsource|].
  apply KernelCSourceAdapt, KernelCSourceAtom; unfold step; apply kernel_program_selected_paired_primitive_source.
Qed.

Lemma selected_c_sequence_save_preserves_packet :
  forall environment critical sg observer origin event_observer local active call mask
    initial before input stopped current resumed (packet : Prop) arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers final_registers after
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      initial before input stopped current resumed
      (coq_prop packet && flag_pend_caller_save_input environment critical local active sg
        (FlagPendTaskCaller call) call mask current)),
  kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ run ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current resumed final_registers current after ->
  let event := flag_pend_task_save_c_event environment critical local active sg call mask
    final_registers.(kernel_save_r0) current resumed after in
  exists (completed : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    initial before input (orb stopped false) current after
    (coq_prop packet && event.(flag_pend_event_output))),
  flag_pend_task_primitive_c_event environment critical sg event /\
  kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ completed.
Proof.
  intros environment critical sg observer origin event_observer local active call mask initial before input stopped current resumed
    packet arch save registers final_registers after run Hsource Hnone Hvalid Hmask Hsuffix event.
  destruct (proj2 (kernel_program_selected_c_sequence_resources environment critical sg observer origin
    _ _ _ _ _ _ _ run)) as [Hpacket Hinput].
  assert (Hprimitive : flag_pend_task_primitive_c_event environment critical sg event).
  { unfold event; eapply FlagPendTaskPrimitiveSave; eassumption. }
  pose (primitive := FlagPendTaskPrimitiveCStep environment critical sg event Hprimitive).
  pose (step := kernel_program_selected_paired_primitive environment critical sg observer origin _ _ _ _ _ _ _ primitive).
  pose (tail := KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput (fun heap Howner => Howner)
    (KernelCSequenceAtom _ _ _ _ _ _ _ _ step) (fun heap Howner => conj Hpacket Howner)).
  exists (KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ run (fun heap Howner => proj2 Howner) tail).
  split; [exact Hprimitive|].
  apply KernelCSourceThen; [exact Hsource|].
  apply KernelCSourceAdapt, KernelCSourceAtom; unfold step; apply kernel_program_selected_paired_primitive_source.
Qed.

End SelectedCompletionComposition.
