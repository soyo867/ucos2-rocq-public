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
Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_selected_completion_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_return_facts_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_caller_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_source_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_suffix_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_environment_spec.
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



















(** Concrete endpoint observations of the same selected C completion.
    Task install preserves its entry's control fields.  IRQ exit genuinely
    decrements nesting, so its control result is stated at an enabled Task
    call cut, not by misidentifying the acquired interrupt cut. *)
Module SelectedEndpointObservations.
Import CriticalComponent PrimitiveComponent TerminalReturn TerminalCallValue FlagPendSchedulerResources.
Import SelectedReturnPrimitive TaskSelectedCompletion IRQSelectedCompletion SelectedCompletionSuffix.
Import SelectedCompletionSource SelectedEnvironmentBuilder SelectedCallerPreservation IRQAcquiredReturn.

Lemma task_selected_c_completion_endpoints :
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
  flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller original) original
    call.(InstallComponent.task_install_fields_entry) returned current.
Proof.
  intros environment critical task_abi sg frame call original saved acquired receipt other before installed sp actual selected restored
    local rest complete Hselected Hincoming Hcoverage Hrestore current returned.
  destruct (task_selected_c_environment_call_preserved environment critical task_abi sg frame call original saved acquired
    receipt other before installed sp actual selected restored complete Hselected Hincoming Hcoverage Hrestore)
    as [run [Hsource [Hreturned [Hsame Hpreserved]]]].
  pose proof (proj2 (kernel_program_return_c_sequence_resources environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ run)) as Howned.
  pose proof (proj1 (flag_pend_caller_restore_input_state_inv environment critical other
    (fun _ _ => receipt ** frame) sg (FlagPendTaskCaller returned) returned saved acquired current
    restored Howned)) as Hvalid.
  pose proof complete as [Hinstall Hcompletion].
  destruct Hinstall as [Hsaved [Hdestination [Hhigh Hstate]]].
  assert (Hstack : returned.(os_sched_call_stack) = call.(InstallComponent.task_install_fields_incoming)).
  { exact (eq_trans (proj2 (proj2 Hsame)) (eq_sym Hincoming)). }
  assert (Hready : flag_pend_current_ready returned current).
  { eapply SchedulerReturnFacts.os_sched_install_current_ready; eassumption. }
  unfold returned, current in *.
  unfold flag_pend_call_endpoint_observations; split; [intros; exact Hready|].
  split; [intros [_ Hidle]; exact Hidle|]. split.
  - intros [_ Hnonidle]; unfold flag_pend_non_idle_at in *.
    rewrite (proj2 (proj2 Hsame)); exact Hnonidle.
  - split.
    + unfold kernel_call_normal_return; split; [exact Hsame|]. intros _.
      unfold kernel_call_stack_available; rewrite (proj1 Hreturned), Hstack.
      apply task_stack_take_lookup.
    + intros _; unfold kernel_call_control_rely; split; reflexivity.
Qed.

(** The returned owner establishes validity at its actual heap.  The
    destination selected by OSIntExit then gives readiness, independent of
    the interrupted caller having been ready at the earlier cut. *)
Lemma irq_acquired_c_completion_endpoint_facts :
  forall environment critical sg handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap installed selected after source prefix hook install restore,
  kernel_irq_acquired_c_completion environment critical sg handler entry transfer original saved acquired receipt other
    frame before prepared hooked_heap installed selected after source prefix hook install restore ->
  let returned := kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack) transfer.(os_int_exit_incoming_fragments) in
  let current := os_int_exit_installed_state transfer in
  flag_pend_current_ready returned current /\
  (task_idle_ready sg entry.(TskState) -> task_idle_ready sg current.(TskState)) /\
  (flag_pend_non_idle_at sg original entry -> flag_pend_non_idle_at sg returned current) /\
  (forall initial, kernel_call_normal_return original initial returned current) /\
  current.(SchedState).(isRunning) = entry.(SchedState).(isRunning) /\
  os_sched_selection_enabled current = true.
Proof.
  intros environment critical sg handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap installed selected after source prefix hook install restore Hcomplete returned current.
  destruct (kernel_irq_acquired_c_completion_task_source environment critical sg handler entry transfer original
    saved acquired receipt other frame before prepared hooked_heap installed selected after source prefix hook install restore Hcomplete)
    as [Hreturned Hsame].
  assert (Horigin : original.(os_sched_call_origin) = RunningInvocation
    transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration))
    by exact (proj1 Hreturned).
  pose proof (proj2 (kernel_irq_acquired_c_completion_resources environment critical sg handler entry transfer original
    saved acquired receipt other frame before prepared hooked_heap installed selected after source prefix hook install restore Hcomplete)) as Howned.
  pose proof (proj1 (flag_pend_caller_restore_input_state_inv (task_sw_hook_call_environment environment) critical other
    (fun _ _ => irq_selected_suffix_receipt handler receipt frame) sg (FlagPendTaskCaller returned) returned
    saved acquired current after Howned)) as Hvalid.
  pose proof (BuiltinComponent.os_int_exit_configured_transfer_hooked_eq environment sg handler entry transfer source) as Hhook.
  destruct (BuiltinComponent.os_int_exit_configured_transfer_state_frame environment sg handler entry transfer source)
    as [Hnodes [Hlife Hrest]].
  split.
  - eapply SchedulerReturnFacts.task_sw_hook_irq_transfer_current_ready; [exact source|exact Hvalid|reflexivity].
  - split.
    + intros Hidle; unfold current, os_int_exit_installed_state; rewrite Hhook; exact Hidle.
    + split.
      * intros Hnonidle.
        assert (Hlease : transfer.(os_int_exit_incoming_stack) = original.(os_sched_call_stack))
          by exact (proj2 (proj2 Hsame)).
        unfold current, os_int_exit_installed_state; rewrite Hhook.
        unfold flag_pend_non_idle_at, returned, kernel_restored_stack_call; cbn.
        rewrite Hlease; exact Hnonidle.
      * split.
        -- intros initial; unfold kernel_call_normal_return; split; [exact Hsame|]. intros _.
           unfold kernel_call_stack_available, returned, kernel_restored_stack_call; cbn.
           rewrite Horigin.
           apply task_stack_take_lookup.
        -- split.
           ++ unfold current, os_int_exit_installed_state; rewrite Hhook.
              exact (proj2 (proj2 (proj2 (os_sched_ready_checkpoint_frame (os_int_exit_after_nesting entry))))).
           ++ pose proof source as [Hswitch Hsource_rest].
              change (os_sched_requests_switch (os_int_exit_after_nesting entry) = true) in Hswitch.
              pose proof (proj1 (proj1 (os_sched_requests_switch_iff _) Hswitch)) as Henabled.
              unfold current, os_int_exit_installed_state; rewrite Hhook; exact Henabled.
Qed.

(** This algebra consumes actual initial/final enabled cuts.  In the IRQ
    caller, final enabled is produced above; initial enabled is the Task
    call's real C guard.  Running equality must be supplied by the actual
    intervening C modules, not by endpoint-normal or by ARM. *)
Lemma kernel_call_enabled_control_rely : forall sg before after,
  os_sched_selection_enabled before = true ->
  os_sched_selection_enabled after = true ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning) ->
  kernel_call_control_rely sg before after.
Proof.
  intros sg before after Hbefore Hafter Hrunning.
  apply os_sched_selection_enabled_iff in Hbefore; apply os_sched_selection_enabled_iff in Hafter.
  unfold kernel_call_control_rely; split; [exact Hrunning|].
  destruct before.(IntrState), after.(IntrState); cbn in *; intuition congruence.
Qed.

Lemma irq_acquired_c_completion_control_at_enabled_entry :
  forall environment critical sg handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap installed selected after source prefix hook install restore initial,
  kernel_irq_acquired_c_completion environment critical sg handler entry transfer original saved acquired receipt other
    frame before prepared hooked_heap installed selected after source prefix hook install restore ->
  os_sched_selection_enabled initial = true ->
  entry.(SchedState).(isRunning) = initial.(SchedState).(isRunning) ->
  kernel_call_control_rely sg initial (os_int_exit_installed_state transfer).
Proof.
  intros environment critical sg handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap installed selected after source prefix hook install restore initial Hcomplete Hinitial Hrunning.
  destruct (irq_acquired_c_completion_endpoint_facts environment critical sg handler entry transfer original saved acquired
    receipt other frame before prepared hooked_heap installed selected after source prefix hook install restore Hcomplete)
    as [Hready [Hidle [Hnonidle [Hnormal [Hrun Henabled]]]]].
  apply kernel_call_enabled_control_rely; [exact Hinitial|exact Henabled|congruence].
Qed.

End SelectedEndpointObservations.
