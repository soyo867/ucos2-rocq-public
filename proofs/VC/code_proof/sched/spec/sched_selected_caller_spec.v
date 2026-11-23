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
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_call_preservation_spec.
Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_selected_completion_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_source_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_suffix_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_environment_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_prefix_spec.
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


(** The concrete selected C completions produce the original caller
    preservation contracts.  The endpoint source is obtained from the
    selected descriptor and its saved capsule in these very completions;
    it is not an extra premise of either producer. *)
Module SelectedCallerPreservation.
Import CriticalComponent PrimitiveComponent TerminalReturn TerminalCallValue FlagPendSchedulerResources.
Import SelectedReturnPrimitive TaskSelectedCompletion IRQSelectedCompletion SelectedCompletionSuffix.
Import SelectedCompletionSource SelectedEnvironmentBuilder.
Import SelectedPrefixSource.

Lemma task_selected_c_environment_call_preserved :
  forall environment critical
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    sg frame call original saved acquired receipt other
    before installed sp actual selected restored,
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
  exists (run : kernel_c_sequence
    (kernel_program_return_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
    call.(InstallComponent.task_install_fields_entry) before
    (InstallComponent.task_install_fields_entry_owner environment local sg call ** rest) false current restored
    (flag_pend_caller_restore_input environment critical other (fun _ _ => receipt ** frame) sg
      (FlagPendTaskCaller returned) returned saved acquired current)),
  kernel_program_return_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ run /\
  kernel_call_task_source returned current /\ task_tcb_init_stack_same_call returned original /\
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation)
    call.(InstallComponent.task_install_fields_entry) current /\
  task_tcb_init_stack_source_preserved original call.(InstallComponent.task_install_fields_entry) current.
Proof.
  intros environment critical task_abi sg frame call original saved acquired receipt other
    before installed sp actual selected restored local rest complete Hselected Hincoming Hcoverage Hrestore current returned.
  destruct (task_selected_c_environment_return environment critical task_abi sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None frame call original saved acquired receipt other
    before installed sp actual selected restored complete Hselected Hincoming Hcoverage Hrestore)
    as [run [Hsource [Hreturned Hsame]]].
  pose proof (proj2 (kernel_program_return_c_sequence_resources environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ run)) as Howned.
  pose proof (proj1 (flag_pend_caller_restore_input_state_inv environment critical other
    (fun _ _ => receipt ** frame) sg (FlagPendTaskCaller returned) returned saved acquired current
    restored Howned)) as Hvalid.
  destruct (task_install_selected_owner_tuple environment local sg rest call selected installed Hselected)
    as [Hstack Hfragments].
  assert (Horiginal : selected.(armv7a_continuation_stack) = original.(os_sched_call_stack)) by congruence.
  destruct (task_install_selected_owner_saved_facts environment critical sg rest call original saved acquired
    receipt other selected installed Horiginal Hselected) as [Hcall [Hmask [Horigin Hactive]]].
  pose proof (proj1 (task_tcb_init_stack_same_call_source_iff returned original current Hsame) Hreturned) as Horiginal_source.
  destruct (kernel_program_return_c_sequence_source_frames environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ run Hsource)
    as [Htask [Hevent [Hname Htimer]]].
  exists run; split; [exact Hsource|]. split; [exact Hreturned|]. split; [exact Hsame|]. split.
  - intros Hbefore; split; [exact Hvalid|]. split; [exact Htask|]. split; [|exact Hname].
    eapply CallPreservation.task_invocation_active_all_origins_transport;
      [exact Hactive|exact (proj1 (proj2 Horiginal_source))].
  - intros _; exact Horiginal_source.
Qed.

Lemma irq_selected_c_environment_call_preserved :
  forall environment critical sg handler entry transfer original saved acquired receipt other frame
    before installed selected after source install restore,
  kernel_irq_selected_suffix_c_completion environment critical sg handler entry transfer original saved acquired receipt other
    frame before installed selected after source install restore ->
  let returned := kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack)
    transfer.(os_int_exit_incoming_fragments) in
  let current := os_int_exit_installed_state transfer in
  exists (run : kernel_c_sequence
    (kernel_program_return_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
    transfer.(os_int_exit_hooked_state) before
    (irq_selected_suffix_input environment critical sg handler transfer original saved acquired receipt other frame)
    false current after (irq_selected_suffix_output environment critical sg handler transfer original saved acquired receipt other frame)),
  kernel_program_return_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ run /\
  kernel_call_task_source returned current /\ task_tcb_init_stack_same_call returned original /\
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) transfer.(os_int_exit_hooked_state) current /\
  task_tcb_init_stack_source_preserved original transfer.(os_int_exit_hooked_state) current.
Proof.
  intros environment critical sg handler entry transfer original saved acquired receipt other frame
    before installed selected after source install restore Hcomplete returned current.
  destruct (irq_selected_c_environment_return environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None handler entry transfer original saved acquired receipt other frame
    before installed selected after source install restore Hcomplete) as [run [Hsource [Hreturned Hsame]]].
  pose proof (proj2 (kernel_irq_selected_suffix_c_completion_resources environment critical sg handler entry transfer
    original saved acquired receipt other frame before installed selected after source install restore Hcomplete)) as Howned.
  pose proof (proj1 (flag_pend_caller_restore_input_state_inv environment critical other
    (fun _ _ => irq_selected_suffix_receipt handler receipt frame) sg (FlagPendTaskCaller returned) returned saved acquired current
    after Howned)) as Hvalid.
  pose proof (proj1 (task_tcb_init_stack_same_call_source_iff returned original current Hsame) Hreturned) as Horiginal_source.
  pose proof Hcomplete as Hcopy; destruct Hcopy as [Hinput Hincoming Horigin Hactive Hterminal].
  destruct (kernel_program_return_c_sequence_source_frames environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ run Hsource)
    as [Htask [Hevent [Hname Htimer]]].
  exists run; split; [exact Hsource|]. split; [exact Hreturned|]. split; [exact Hsame|]. split.
  - intros Hbefore; split; [exact Hvalid|]. split; [exact Htask|]. split; [|exact Hname].
    eapply CallPreservation.task_invocation_active_all_origins_transport;
      [exact Hactive|exact (proj1 (proj2 Horiginal_source))].
  - intros _; exact Horiginal_source.
Qed.

(** A real earlier C prefix is retained, including temporary non-closed
    phases and its original middle heap.  Only its actual post-to-pre
    bridge feeds this selected install.  The saved caller's active fields
    are projected from the input owner, not imposed on every middle state. *)
Lemma task_selected_c_prefix_call_preserved :
  forall environment critical
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    sg frame call original saved acquired receipt other
    initial first_heap first_local active mask first_stopped first_output
    before installed sp actual selected restored,
  let local := kernel_sched_saved_local_resource_at environment.(task_stack_call_platform) critical sg
    call.(InstallComponent.task_install_fields_entry).(TskState) original saved acquired receipt other in
  let rest := armv7a_task_switch_control task_abi call.(InstallComponent.task_install_fields_context) **
    unmap_table_rep sg ** frame in
  forall (prefix : kernel_c_sequence
    (kernel_program_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial first_heap
    (flag_pend_caller_save_input environment critical first_local active sg
      (FlagPendTaskCaller original) original mask initial)
    first_stopped call.(InstallComponent.task_install_fields_entry) before first_output)
    (bridge : first_output |-- InstallComponent.task_install_fields_entry_owner environment local sg call ** rest)
    (complete : InstallComponent.task_install_c_segment environment local sg rest call before installed sp actual),
  kernel_program_c_sequence_call_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix ->
  (forall observed state, active observed state |--
    coq_prop (exists task, flag_active_task_fields original observed state task) && active observed state) ->
  task_install_selected_owner environment local sg rest call selected installed ->
  call.(InstallComponent.task_install_fields_incoming) = original.(os_sched_call_stack) ->
  task_stack_live_coverage call.(InstallComponent.task_install_fields_entry).(TskState)
    (Some (task_stack_key call.(InstallComponent.task_install_fields_context).(os_sched_call_stack))) ->
  armv7a_task_restore_transition task_abi call.(InstallComponent.task_install_fields_context) selected installed restored ->
  let current := InstallComponent.task_install_fields_current call in
  let returned := kernel_selected_call selected current in
  exists (run : kernel_c_sequence
    (kernel_program_return_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial first_heap
    (flag_pend_caller_save_input environment critical first_local active sg
      (FlagPendTaskCaller original) original mask initial)
    (orb first_stopped false) current restored
    (flag_pend_caller_restore_input environment critical other (fun _ _ => receipt ** frame) sg
      (FlagPendTaskCaller returned) returned saved acquired current)),
  kernel_program_return_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ run /\
  kernel_call_task_source returned current /\ task_tcb_init_stack_same_call returned original /\
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) initial current /\
  task_tcb_init_stack_source_preserved original initial current /\ orb first_stopped false = false.
Proof.
  intros environment critical task_abi sg frame call original saved acquired receipt other
    initial first_heap first_local active mask first_stopped first_output before installed sp actual selected restored
    local rest prefix bridge complete Hprefix Hfields Hselected Hincoming Hcoverage Hrestore current returned.
  destruct (task_selected_c_environment_return environment critical task_abi sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None frame call original saved acquired receipt other
    before installed sp actual selected restored complete Hselected Hincoming Hcoverage Hrestore)
    as [terminal [Hterminal [Hreturned Hsame]]].
  destruct (kernel_selected_return_after_original_c_prefix environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None
    _ _ _ _ _ _ _ _ _ _ _ prefix bridge terminal Hprefix Hterminal) as [run Hsource].
  destruct (kernel_program_return_c_sequence_resources environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ run)
    as [Hinput Houtput].
  destruct (proj1 (CallPreservation.flag_pend_caller_save_input_active_fields environment critical first_local active sg
    original original mask initial Hfields first_heap Hinput)) as [Hinitial Hactive].
  pose proof (proj1 (flag_pend_caller_restore_input_state_inv environment critical other
    (fun _ _ => receipt ** frame) sg (FlagPendTaskCaller returned) returned saved acquired current
    restored Houtput)) as Hcurrent.
  exists run; split; [exact Hsource|]. split; [exact Hreturned|]. split; [exact Hsame|].
  eapply kernel_program_return_c_sequence_call_preserved; [exact Hsource|exact Hcurrent| |exact Hactive|exact Hsame|exact Hreturned].
  exact (proj1 (proj2 Hinitial)).
Qed.

(** The Save suffix consumes the call computed by the preceding actual
    return construction.  It preserves that very run's source marker and
    fixes both endpoint heaps to the existing primitive event. *)
Lemma selected_c_environment_save_with_source :
  forall environment critical sg observer origin event_observer local active call mask
    initial before input stopped current resumed arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers final_registers after
    (run : kernel_c_sequence (kernel_program_return_c_step environment critical sg observer origin)
      initial before input stopped current resumed
      (flag_pend_caller_save_input environment critical local active sg
        (FlagPendTaskCaller call) call mask current)),
  kernel_program_return_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ run ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current resumed
    final_registers current after ->
  let event := flag_pend_task_save_c_event environment critical local active sg call mask
    final_registers.(kernel_save_r0) current resumed after in
  exists (completed : kernel_c_sequence (kernel_program_return_c_step environment critical sg observer origin)
    initial before input (orb stopped false) current after event.(flag_pend_event_output)),
  flag_pend_task_primitive_c_event environment critical sg event /\
  kernel_program_return_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ completed.
Proof.
  intros environment critical sg observer origin event_observer local active call mask initial before input stopped current resumed
    arch save registers final_registers after run Hsource Hnone Hvalid Hmask Hsuffix event.
  pose proof (proj2 (kernel_program_return_c_sequence_resources environment critical sg observer origin
    initial before input stopped current resumed _ run)) as Hinput.
  assert (Hprimitive : flag_pend_task_primitive_c_event environment critical sg event).
  { unfold event; eapply FlagPendTaskPrimitiveSave; eassumption. }
  pose (primitive := FlagPendTaskPrimitiveCStep environment critical sg event Hprimitive).
  pose (old_step := @KernelProgramCPairedPrimitive environment critical sg observer origin _ _ _ _ _ _ _ primitive).
  pose (step := @KernelProgramReturnOriginal environment critical sg observer origin _ _ _ _ _ _ _ old_step).
  exists (KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ run (fun h H => H)
    (KernelCSequenceAtom _ _ _ _ _ _ _ _ step)).
  split; [exact Hprimitive|].
  apply KernelCSourceThen; [exact Hsource|].
  apply KernelCSourceAtom; unfold step; apply KernelProgramReturnOriginalSource.
  right; unfold old_step; apply KernelProgramCPairedPrimitiveSource.
Qed.

End SelectedCallerPreservation.
