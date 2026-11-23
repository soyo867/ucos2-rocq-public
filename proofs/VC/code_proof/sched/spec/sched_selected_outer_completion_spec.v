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
Require Export Ucos2Verify.VC.code.sched.spec.sched_return_facts_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_caller_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_completion_composition_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_source_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_suffix_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_environment_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_c_control_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_endpoint_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_c_environment_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_environment_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_c_idle_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_return_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_completion_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_call_value_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_terminal_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.



























































































(** Endpoint observations are computed from this prefix and the actual last
    C completion.  The Task call's initial guard is local call evidence;
    intermediate counter changes and TaskDel stopped branches remain in
    the sequence.  Its stop bit is proved false only at the real return. *)
Module SelectedOuterCompletion.
Import CriticalComponent PrimitiveComponent TerminalReturn TerminalCallValue FlagPendSchedulerResources.
Import SelectedCProgram SelectedCSource SelectedReturnPrimitive SelectedCompletionSource.
Import TaskSelectedCompletion SelectedCompletionSuffix.
Import SelectedCompletionComposition SelectedControlComposition SelectedIdleComposition.
Import SelectedEndpointObservations SelectedEnvironmentBuilder SelectedCallerPreservation.
Import IRQAcquiredReturn IRQSelectedCompletion.

Lemma task_selected_c_completion_ready_normal :
  forall environment critical
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    sg frame call original saved acquired receipt other before installed sp actual selected restored,
  let local := kernel_sched_saved_local_resource_at environment.(task_stack_call_platform) critical sg
    call.(InstallComponent.task_install_fields_entry).(TskState) original saved acquired receipt other in
  let rest := armv7a_task_switch_control task_abi call.(InstallComponent.task_install_fields_context) **
    unmap_table_rep sg ** frame in
  forall (complete : InstallComponent.task_install_c_segment environment local sg rest call before installed sp actual),
  task_install_selected_owner environment local sg rest call selected installed ->
  call.(InstallComponent.task_install_fields_incoming) = original.(os_sched_call_stack) ->
  task_stack_live_coverage call.(InstallComponent.task_install_fields_entry).(TskState)
    (Some (task_stack_key call.(InstallComponent.task_install_fields_context).(os_sched_call_stack))) ->
  armv7a_task_restore_transition task_abi call.(InstallComponent.task_install_fields_context) selected installed restored ->
  let current := InstallComponent.task_install_fields_current call in
  let returned := kernel_selected_call selected current in
  flag_pend_current_ready returned current /\
  (forall initial, kernel_call_normal_return original initial returned current).
Proof.
  intros environment critical task_abi sg frame call original saved acquired receipt other before installed sp actual selected restored
    local rest complete Hselected Hincoming Hcoverage Hrestore current returned.
  destruct (task_selected_c_environment_call_preserved environment critical task_abi sg frame call original saved acquired
    receipt other before installed sp actual selected restored complete Hselected Hincoming Hcoverage Hrestore)
    as [run [Hsource [Hreturned [Hsame Hpreserved]]]].
  pose proof (proj2 (kernel_program_return_c_sequence_resources environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ run)) as Howned.
  pose proof (proj1 (flag_pend_caller_restore_input_state_inv environment critical other
    (fun _ _ => receipt ** frame) sg (FlagPendTaskCaller returned) returned saved acquired current restored Howned)) as Hvalid.
  pose proof complete as [[Hsaved [Hdestination [Hhigh Hstate]]] Hcompletion].
  assert (Hstack : returned.(os_sched_call_stack) = call.(InstallComponent.task_install_fields_incoming)).
  { exact (eq_trans (proj2 (proj2 Hsame)) (eq_sym Hincoming)). }
  unfold returned, current in *.
  split.
  - eapply SchedulerReturnFacts.os_sched_install_current_ready; eassumption.
  - intro initial; unfold kernel_call_normal_return; split; [exact Hsame|]. intros _.
    unfold kernel_call_stack_available; rewrite (proj1 Hreturned), Hstack.
    apply task_stack_take_lookup.
Qed.

Lemma irq_acquired_c_completion_outer_sequence :
  forall environment critical sg event_observer handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap installed selected after source prefix hook install restore
    initial first_heap input prefix_stop prefix_output
    (run : kernel_c_sequence (kernel_program_selected_c_step (task_sw_hook_call_environment environment) critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap input prefix_stop entry before prefix_output)
    (bridge : prefix_output |-- IRQCPrefix.os_int_exit_prefix_fields_owner
      (task_sw_hook_call_environment environment) critical sg handler entry original saved acquired receipt other frame),
  kernel_program_selected_c_sequence_source (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ run ->
  kernel_program_selected_sequence_idle_source (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ run ->
  task_in_range sg initial.(TskState) -> kernel_call_task_source original initial ->
  initial.(SchedState).(isRunning) = true -> os_sched_selection_enabled initial = true ->
  kernel_irq_acquired_c_completion environment critical sg handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap installed selected after source prefix hook install restore ->
  let returned := kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack) transfer.(os_int_exit_incoming_fragments) in
  let current := os_int_exit_installed_state transfer in
  exists (whole : kernel_c_sequence (kernel_program_selected_c_step (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)) initial first_heap input
    (orb prefix_stop false) current after
    (coq_prop (flag_pend_call_endpoint_observations (task_sw_hook_call_environment environment) sg
       (FlagPendTaskCaller original) original initial returned current) &&
      irq_selected_suffix_output (task_sw_hook_call_environment environment) critical sg handler transfer
        original saved acquired receipt other frame)),
  kernel_program_selected_c_sequence_source (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ whole /\
  kernel_program_selected_sequence_idle_source (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ whole /\
  kernel_call_task_source returned current /\ orb prefix_stop false = false.
Proof.
  intros environment critical sg event_observer handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap installed selected after source prefix hook install restore initial first_heap input prefix_stop
    prefix_output run bridge Hsource Hidle Hrange Horiginal Hrunning Henabled complete returned current.
  pose (primitive := @KernelIRQAcquiredReturnCStep environment critical sg handler entry transfer original saved acquired
    receipt other frame before prepared hooked_heap installed selected after source prefix hook install restore complete).
  pose (step := @KernelSelectedProgramIRQ critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin)
    environment _ _ _ _ _ _ _ primitive).
  pose (tail := KernelCSequenceAtom _ _ _ _ _ _ _ _ step).
  pose (all := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ run bridge tail).
  assert (Hall_source : kernel_program_selected_c_sequence_source (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ all).
  { unfold all; apply KernelCSourceThen; [exact Hsource|].
    apply KernelCSourceAtom; unfold step; apply KernelSelectedProgramIRQSource. }
  assert (Hall_idle : kernel_program_selected_sequence_idle_source (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ all).
  { unfold all; apply KernelCSourceThen; [exact Hidle|].
    apply KernelCSourceAtom; unfold step; apply KernelSelectedIRQIdleSource. }
  destruct (kernel_irq_acquired_c_completion_task_source environment critical sg handler entry transfer original saved acquired
    receipt other frame before prepared hooked_heap installed selected after source prefix hook install restore complete)
    as [Hreturned Hsame].
  destruct (irq_acquired_c_completion_endpoint_facts environment critical sg handler entry transfer original saved acquired
    receipt other frame before prepared hooked_heap installed selected after source prefix hook install restore complete)
    as [Hready [_ [_ [Hnormal _]]]].
  destruct (kernel_program_selected_completed_sequence_idle_non_idle (task_sw_hook_call_environment environment) critical sg
    original returned _ _ _ _ _ _ _ all Hall_idle Hrange Horiginal Hrunning (Hnormal initial) Hreturned)
    as [Hstop [Hidle_all Hnonidle_all]].
  assert (Hendpoint : flag_pend_call_endpoint_observations (task_sw_hook_call_environment environment) sg
    (FlagPendTaskCaller original) original initial returned current).
  { split; [intros; exact Hready|]. split; [intros [_ Hinitial]; exact (Hidle_all Hinitial)|].
    split; [intros [_ Hinitial]; exact (Hnonidle_all Hinitial)|].
    split; [apply Hnormal|]. intros _.
    eapply irq_acquired_selected_sequence_control; eassumption. }
  pose proof (proj1 (kernel_program_selected_c_sequence_resources (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ all)) as Hinput.
  exists (KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput (fun heap Howner => Howner) all
    (fun heap Howner => conj Hendpoint Howner)).
  split; [apply KernelCSourceAdapt; exact Hall_source|].
  split; [apply KernelCSourceAdapt; exact Hall_idle|]. exact (conj Hreturned Hstop).
Qed.

(** The full last selector is retained in the call record's own context,
    outgoing/incoming stacks and hooked state.  It supplies final enabled;
    Running comes from this actual prefix rather than counter-frame claims. *)
Lemma task_selected_c_completion_outer_sequence :
  forall environment critical
    (task_abi : Armv7aTaskContextABI (task_sw_hook_call_environment environment).(task_stack_call_external)
      (task_sw_hook_call_environment environment).(task_stack_call_platform)
      (task_sw_hook_call_environment environment).(task_stack_call_port)
      (task_sw_hook_call_environment environment).(task_stack_call_continuations))
    sg event_observer frame original saved acquired receipt other initial first_heap input prefix_stop prefix_output
    last_entry context saved_sp outgoing hooked incoming resumed
    (Hswitch : os_sched_requests_switch last_entry = true)
    (Hsave : (task_sw_hook_call_environment environment).(task_stack_call_external).(os_sched_arch_save_source)
      context saved_sp outgoing)
    (Hhook : kernel_client_step (task_sw_hook_call_environment environment).(task_stack_call_external).(os_sched_hook_action)
      sg (os_sched_save_current_sp (os_sched_prefix_state last_entry)
        context.(os_sched_call_stack).(stackLeaseSlot) saved_sp) hooked)
    (Hdestination : os_sched_destination_binding (task_sw_hook_call_environment environment).(task_stack_call_external)
      context outgoing hooked incoming resumed),
  let call := {| InstallComponent.task_install_fields_context := context;
                 InstallComponent.task_install_fields_outgoing := outgoing;
                 InstallComponent.task_install_fields_incoming := incoming;
                 InstallComponent.task_install_fields_resumed := resumed;
                 InstallComponent.task_install_fields_entry := hooked |} in
  let local := kernel_sched_saved_local_resource_at (task_sw_hook_call_environment environment).(task_stack_call_platform)
    critical sg hooked.(TskState) original saved acquired receipt other in
  let rest := armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame in
  forall before installed sp actual
    (complete : InstallComponent.task_install_c_segment (task_sw_hook_call_environment environment) local sg rest
      call before installed sp actual)
    (run : kernel_c_sequence (kernel_program_selected_c_step (task_sw_hook_call_environment environment) critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap input prefix_stop hooked before prefix_output)
    (bridge : prefix_output |-- InstallComponent.task_install_fields_entry_owner
      (task_sw_hook_call_environment environment) local sg call ** rest),
  kernel_program_selected_c_sequence_source (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ run ->
  kernel_program_selected_sequence_idle_source (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ run ->
  task_in_range sg initial.(TskState) -> kernel_call_task_source original initial ->
  initial.(SchedState).(isRunning) = true -> os_sched_selection_enabled initial = true ->
  incoming = original.(os_sched_call_stack) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  exists selected, forall restored,
  armv7a_task_restore_transition task_abi context selected installed restored ->
  let current := InstallComponent.task_install_fields_current call in
  let returned := kernel_selected_call selected current in
  exists (whole : kernel_c_sequence (kernel_program_selected_c_step (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)) initial first_heap input
    (orb prefix_stop false) current restored
    (coq_prop (flag_pend_call_endpoint_observations (task_sw_hook_call_environment environment) sg
       (FlagPendTaskCaller original) original initial returned current) &&
      flag_pend_caller_restore_input (task_sw_hook_call_environment environment) critical other
        (fun _ _ => receipt ** frame) sg (FlagPendTaskCaller returned) returned saved acquired current)),
  kernel_program_selected_c_sequence_source (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ whole /\
  kernel_call_task_source returned current /\ orb prefix_stop false = false.
Proof.
  intros environment critical task_abi sg event_observer frame original saved acquired receipt other initial first_heap input
    prefix_stop prefix_output last_entry context saved_sp outgoing hooked incoming resumed Hswitch Hsave Hhook Hdestination
    call local rest before installed sp actual complete run bridge Hsource Hidle Hrange Horiginal Hrunning Henabled Hincoming Hcoverage.
  pose proof (proj2 (InstallComponent.task_install_c_segment_resources (task_sw_hook_call_environment environment)
    local sg rest call before installed sp actual complete)) as Hpost.
  destruct (task_install_fields_installed_owner_selected (task_sw_hook_call_environment environment)
    local sg rest call installed Hpost) as [selected Hselected].
  exists selected; intros restored Hrestore current returned.
  destruct (task_selected_c_environment_return (task_sw_hook_call_environment environment) critical task_abi sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer frame call original saved acquired receipt other
    before installed sp actual selected restored complete Hselected Hincoming Hcoverage Hrestore)
    as [old_tail [Hold_tail [Hreturned Hsame]]].
  destruct (kernel_program_return_sequence_include_acquired_irq_source (task_sw_hook_call_environment environment)
    critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer
    _ _ _ _ _ _ _ old_tail Hold_tail) as [tail Htail].
  pose (all := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ run bridge tail).
  assert (Hall_source : kernel_program_selected_c_sequence_source (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ all).
  { unfold all; apply KernelCSourceThen; assumption. }
  destruct (task_selected_c_completion_ready_normal (task_sw_hook_call_environment environment) critical task_abi sg
    frame call original saved acquired receipt other before installed sp actual selected restored complete
    Hselected Hincoming Hcoverage Hrestore) as [Hready Hnormal].
  assert (Hstop : orb prefix_stop false = false).
  { eapply kernel_call_completed_task_source_not_stopped; [exact Hrange|exact Horiginal| |apply Hnormal|exact Hreturned].
    eapply kernel_program_selected_c_sequence_observer_lifetime; exact all. }
  assert (Hprefix_stop : prefix_stop = false) by now rewrite Bool.orb_false_r in Hstop.
  destruct (kernel_program_selected_sequence_idle_source_transport (task_sw_hook_call_environment environment)
    critical sg original _ _ _ _ _ _ _ run Hidle (proj1 Horiginal) Hrunning Hprefix_stop) as [Hprefix_idle Hprefix_nonidle].
  assert (Hcontrol : kernel_call_control_rely sg initial current).
  { eapply kernel_call_enabled_control_rely; [exact Henabled| |].
    - change (os_sched_selection_enabled hooked = true).
      change (hooked = os_sched_save_current_sp (os_sched_prefix_state last_entry)
        context.(os_sched_call_stack).(stackLeaseSlot) saved_sp) in Hhook.
      rewrite Hhook. change (os_sched_selection_enabled last_entry = true).
      exact (proj1 (proj1 (os_sched_requests_switch_iff last_entry) Hswitch)).
    - change (hooked.(SchedState).(isRunning) = initial.(SchedState).(isRunning)).
      eapply kernel_program_selected_c_sequence_running; exact run. }
  assert (Hendpoint : flag_pend_call_endpoint_observations (task_sw_hook_call_environment environment) sg
    (FlagPendTaskCaller original) original initial returned current).
  { split; [intros; exact Hready|].
    split; [intros [_ Hinitial]; exact (Hprefix_idle Hinitial)|].
    split.
    - intros [_ Hinitial].
      pose proof (Hprefix_nonidle Hinitial) as Hmiddle.
      unfold flag_pend_non_idle_at in Hmiddle.
      rewrite <- (proj2 (proj2 Hsame)) in Hmiddle; exact Hmiddle.
    - split; [exact (Hnormal initial)|]. intros _; exact Hcontrol. }
  pose proof (proj1 (kernel_program_selected_c_sequence_resources (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ all)) as Hinput.
  exists (KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput (fun heap Howner => Howner) all
    (fun heap Howner => conj Hendpoint Howner)).
  split; [apply KernelCSourceAdapt; exact Hall_source|]. exact (conj Hreturned Hstop).
Qed.

(** The actual callee's final Restore closes this selected return's masked
    owner.  Its prefix and suffix use different real heaps; Adapt only
    discards the primitive's additional pure packet at the same last heap. *)
Lemma selected_return_restore_c_environment :
  forall environment critical local next_local active sg original saved acquired initial first_heap stopped returned current
    restored arch (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written middle final_cursor after
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap
      (flag_pend_caller_save_input environment critical local active sg
        (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial)
      stopped current restored
      (coq_prop (flag_pend_call_endpoint_observations environment sg
         (FlagPendTaskCaller original) original initial returned current) &&
       flag_pend_caller_restore_input environment critical next_local active sg
         (FlagPendTaskCaller returned) returned saved acquired current)),
  kernel_program_selected_c_sequence_source environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ run ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor restored written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  exists (completed : SelectedEnvironment.flag_pend_task_c_environment_run environment critical local next_local active sg
    original (armv7a_irq_fiq_mask saved) initial first_heap stopped returned current after),
  ContinuationPhaseSource.flag_pend_task_c_environment_call_source environment critical local next_local active sg
    None original (armv7a_irq_fiq_mask saved) initial first_heap stopped returned current after completed.
Proof.
  intros environment critical local next_local active sg original saved acquired initial first_heap stopped returned current
    restored arch restore cursor written middle final_cursor after run Hsource Hr0 Hmask Hprefix Hsuffix.
  destruct (selected_c_sequence_restore_preserves_packet environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None next_local active returned saved acquired initial first_heap
    _ stopped current restored _ arch restore cursor written middle final_cursor after
    run Hsource Hr0 Hmask Hprefix Hsuffix) as [returned_run [Hprimitive Hreturned_source]].
  pose proof (proj1 (kernel_program_selected_c_sequence_resources environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ returned_run)) as Hinput.
  replace stopped with (orb stopped false) by apply Bool.orb_false_r.
  unfold SelectedEnvironment.flag_pend_task_c_environment_run.
  eexists (KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput (fun heap Howner => Howner) returned_run
    (fun heap Howner => conj (proj1 Howner) (proj2 (proj2 Howner)))).
  apply KernelCSourceAdapt; exact Hreturned_source.
Qed.

End SelectedOuterCompletion.
