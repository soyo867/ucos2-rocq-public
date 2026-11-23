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
Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_acquired_fields_prefix_spec.
Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_fields_prefix_spec.
Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_selected_completion_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_caller_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_call_value_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


(** OSIntExit from its acquired C cut through the actual selected IRQ
    return.  The observed running branch precedes Save in the C function;
    this prefix reads only the protected nesting/counter/selector cells.
    Every intermediate heap and original proof remains an index. *)
Module IRQAcquiredReturn.
Import CriticalComponent PrimitiveComponent IRQCPrefix IRQAcquiredCPrefix.
Import IRQSelectedCompletion TerminalCallValue SelectedCallerPreservation.

Inductive kernel_irq_acquired_c_completion environment critical sg handler entry transfer original saved acquired
  receipt other frame before prepared hooked_heap installed selected after
  (source : os_int_exit_transfer_source
    (task_sw_hook_call_environment environment).(task_stack_call_external)
    environment.(task_stack_call_port) sg handler entry transfer)
  (prefix : os_int_exit_acquired_switch_prefix_execution sg entry before prepared)
  (hook : kernel_heap_execution [] prepared hooked_heap)
  (install : sched_install_heap_fragment sg hooked_heap installed
    (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp))
  (restore : armv7a_restore_transition (task_sw_hook_call_environment environment).(task_stack_call_continuations)
    handler selected installed after) : Prop :=
| KernelIRQAcquiredCComplete :
    os_int_exit_acquired_c_prefix_completion environment critical sg handler entry transfer original
      saved acquired receipt other frame before prepared hooked_heap source prefix hook ->
    kernel_irq_selected_suffix_c_completion (task_sw_hook_call_environment environment) critical sg handler entry transfer
      original saved acquired receipt other frame hooked_heap installed selected after source install restore ->
    kernel_irq_acquired_c_completion environment critical sg handler entry transfer original saved acquired receipt other
      frame before prepared hooked_heap installed selected after source prefix hook install restore.

Lemma kernel_irq_acquired_c_completion_from_entry :
  forall environment critical sg handler entry transfer original saved acquired receipt other frame before
    (source : os_int_exit_transfer_source
      (task_sw_hook_call_environment environment).(task_stack_call_external)
      environment.(task_stack_call_port) sg handler entry transfer),
  os_int_exit_prefix_fields_owner (task_sw_hook_call_environment environment) critical sg handler entry
    original saved acquired receipt other frame before ->
  transfer.(os_int_exit_incoming_stack) = original.(os_sched_call_stack) ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage entry.(TskState) None ->
  exists prepared (prefix : os_int_exit_acquired_switch_prefix_execution sg entry before prepared)
    (hook : kernel_heap_execution [] prepared prepared) installed selected
    (install : sched_install_heap_fragment sg prepared installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp)),
    armv7a_continuation_restore_reads selected installed /\
    forall after (restore : armv7a_restore_transition (task_sw_hook_call_environment environment).(task_stack_call_continuations)
      handler selected installed after),
    kernel_irq_acquired_c_completion environment critical sg handler entry transfer original saved acquired receipt other
      frame before prepared prepared installed selected after source prefix hook install restore.
Proof.
  intros environment critical sg handler entry transfer original saved acquired receipt other frame before
    source Hinput Hincoming Haddress Hcoverage.
  destruct (os_int_exit_configured_acquired_prefix_source environment critical sg handler entry transfer original
    saved acquired receipt other frame before source Hinput) as [prepared [prefix [hook Hprefix]]].
  destruct (os_int_exit_acquired_c_prefix_completion_resources environment critical sg handler entry transfer original
    saved acquired receipt other frame before prepared prepared source prefix hook Hprefix) as [_ [Hhigh Hhooked]].
  pose proof (BuiltinComponent.os_int_exit_configured_transfer_hooked_eq environment sg handler entry transfer source) as Hhook.
  assert (Hcovered : task_stack_live_coverage transfer.(os_int_exit_hooked_state).(TskState) None).
  { rewrite Hhook; exact Hcoverage. }
  destruct (kernel_irq_selected_suffix_c_completion_from_c_post (task_sw_hook_call_environment environment) critical sg
    handler entry transfer original saved acquired receipt other prepared frame source Hhigh Hincoming Haddress Hcovered Hhooked)
    as [installed [selected [install [Hreads Hreturn]]]].
  exists prepared, prefix, hook, installed, selected, install; split; [exact Hreads|].
  intros after restore; constructor; [exact Hprefix|exact (Hreturn after restore)].
Qed.

Lemma kernel_irq_acquired_c_completion_resources :
  forall environment critical sg handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap installed selected after source prefix hook install restore,
  kernel_irq_acquired_c_completion environment critical sg handler entry transfer original saved acquired receipt other
    frame before prepared hooked_heap installed selected after source prefix hook install restore ->
  os_int_exit_prefix_fields_owner (task_sw_hook_call_environment environment) critical sg handler entry
    original saved acquired receipt other frame before /\
  irq_selected_suffix_output (task_sw_hook_call_environment environment) critical sg handler transfer
    original saved acquired receipt other frame after.
Proof.
  intros environment critical sg handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap installed selected after source prefix hook install restore [Hprefix Hsuffix].
  split.
  - exact (proj1 (os_int_exit_acquired_c_prefix_completion_resources environment critical sg handler entry transfer original
      saved acquired receipt other frame before prepared hooked_heap source prefix hook Hprefix)).
  - exact (proj2 (kernel_irq_selected_suffix_c_completion_resources (task_sw_hook_call_environment environment) critical sg
      handler entry transfer original saved acquired receipt other frame hooked_heap installed selected after source install restore Hsuffix)).
Qed.

Lemma kernel_irq_acquired_c_completion_task_source :
  forall environment critical sg handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap installed selected after source prefix hook install restore,
  kernel_irq_acquired_c_completion environment critical sg handler entry transfer original saved acquired receipt other
    frame before prepared hooked_heap installed selected after source prefix hook install restore ->
  let returned := kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack) transfer.(os_int_exit_incoming_fragments) in
  kernel_call_task_source returned (os_int_exit_installed_state transfer) /\
  task_tcb_init_stack_same_call returned original.
Proof.
  intros environment critical sg handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap installed selected after source prefix hook install restore [Hprefix Hsuffix] returned.
  split.
  - eapply kernel_irq_selected_suffix_c_completion_task_source; exact Hsuffix.
  - pose proof Hsuffix as Hcopy; destruct Hcopy as [Hinput Hincoming Horigin Hactive Hterminal].
    unfold returned, kernel_restored_stack_call, task_tcb_init_stack_same_call; cbn; auto.
Qed.

Lemma kernel_irq_acquired_c_completion_call_preserved :
  forall environment critical sg handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap installed selected after source prefix hook install restore,
  kernel_irq_acquired_c_completion environment critical sg handler entry transfer original saved acquired receipt other
    frame before prepared hooked_heap installed selected after source prefix hook install restore ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) entry (os_int_exit_installed_state transfer) /\
  task_tcb_init_stack_source_preserved original entry (os_int_exit_installed_state transfer).
Proof.
  intros environment critical sg handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap installed selected after source prefix hook install restore Hcomplete.
  pose proof (proj2 (kernel_irq_acquired_c_completion_resources environment critical sg handler entry transfer original
    saved acquired receipt other frame before prepared hooked_heap installed selected after source prefix hook install restore Hcomplete)) as Howned.
  destruct (kernel_irq_acquired_c_completion_task_source environment critical sg handler entry transfer original
    saved acquired receipt other frame before prepared hooked_heap installed selected after source prefix hook install restore Hcomplete)
    as [Hreturned Hsame].
  pose proof (proj1 (task_tcb_init_stack_same_call_source_iff _ original _ Hsame) Hreturned) as Horiginal.
  pose proof (proj1 (flag_pend_caller_restore_input_state_inv (task_sw_hook_call_environment environment) critical other
    (fun _ _ => irq_selected_suffix_receipt handler receipt frame) sg
    (FlagPendTaskCaller (kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack) transfer.(os_int_exit_incoming_fragments)))
    (kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack) transfer.(os_int_exit_incoming_fragments))
    saved acquired (os_int_exit_installed_state transfer) after Howned)) as Hvalid.
  pose proof (BuiltinComponent.os_int_exit_configured_transfer_hooked_eq environment sg handler entry transfer source) as Hhook.
  pose proof Hcomplete as [Hprefix Hsuffix]; destruct Hsuffix as [Hinput Hincoming Horigin Hactive Hterminal].
  rewrite Hhook in Hactive.
  split.
  - intros Hbefore; split; [exact Hvalid|]. split.
    + unfold os_int_exit_installed_state; rewrite Hhook; reflexivity.
    + split.
      * eapply CallPreservation.task_invocation_active_all_origins_transport;
          [exact Hactive|exact (proj1 (proj2 Horiginal))].
      * unfold os_int_exit_installed_state; rewrite Hhook; reflexivity.
  - intros _; exact Horiginal.
Qed.

(** KernelCSegmentRelation adapter for the finite C union.  Its sole atom
    keeps the original acquired-prefix, hook, install and return proofs. *)
Inductive kernel_irq_acquired_return_c_step environment critical sg : KernelCSegmentRelation :=
| KernelIRQAcquiredReturnCStep : forall handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap installed selected after source prefix hook install restore,
    kernel_irq_acquired_c_completion environment critical sg handler entry transfer original saved acquired receipt other
      frame before prepared hooked_heap installed selected after source prefix hook install restore ->
    kernel_irq_acquired_return_c_step environment critical sg entry before
      (os_int_exit_prefix_fields_owner (task_sw_hook_call_environment environment) critical sg handler entry
        original saved acquired receipt other frame) false (os_int_exit_installed_state transfer) after
      (irq_selected_suffix_output (task_sw_hook_call_environment environment) critical sg handler transfer
        original saved acquired receipt other frame).

Lemma kernel_irq_acquired_return_c_step_resources : forall environment critical sg
  state before input stopped current after output,
  kernel_irq_acquired_return_c_step environment critical sg state before input stopped current after output ->
  input before /\ output after.
Proof. intros; destruct H; eapply kernel_irq_acquired_c_completion_resources; eassumption. Qed.

Lemma kernel_irq_acquired_return_c_step_preserves_observer : forall environment critical sg observer origin
  state before input stopped current after output,
  kernel_irq_acquired_return_c_step environment critical sg state before input stopped current after output ->
  task_invocation_active state.(TskState) observer origin ->
  task_invocation_active current.(TskState) observer origin /\ sched_observer_current_cache origin current.
Proof.
  intros environment critical sg observer origin state before input stopped current after output Hstep Hactive.
  destruct Hstep; eapply BuiltinComponent.os_int_exit_configured_transfer_preserves_observer_cache; eassumption.
Qed.

Lemma kernel_irq_acquired_return_c_step_lifetime : forall environment critical sg observer origin
  state before input stopped current after output,
  kernel_irq_acquired_return_c_step environment critical sg state before input stopped current after output ->
  task_observer_lifetime_result observer origin state.(TskState) current.(TskState) stopped.
Proof.
  intros environment critical sg observer origin state before input stopped current after output Hstep; destruct Hstep.
  destruct (BuiltinComponent.os_int_exit_configured_transfer_state_frame environment sg handler entry transfer source)
    as [Hnodes [Hlife Hrest]].
  apply task_observer_lifetime_result_not_stopped, task_observer_lifetime_transport_fields; [exact Hlife|].
  intros slot; rewrite Hnodes; reflexivity.
Qed.

Lemma kernel_irq_acquired_return_c_step_frames : forall environment critical sg observer
  state before input stopped current after output,
  kernel_irq_acquired_return_c_step environment critical sg state before input stopped current after output ->
  task_creation_frame observer state.(TskState) current.(TskState) /\
  (forall invocation, event_creation_frame invocation state.(EventState) current.(EventState)) /\
  state.(NameState) = current.(NameState) /\ timer_public_trace sg state.(TimerState) current.(TimerState).
Proof.
  intros environment critical sg observer state before input stopped current after output Hstep; destruct Hstep.
  pose proof (BuiltinComponent.os_int_exit_configured_transfer_hooked_eq environment sg handler entry transfer source) as Hhook.
  unfold os_int_exit_installed_state; rewrite Hhook.
  split; [reflexivity|]. split; [intros; reflexivity|]. split; [reflexivity|constructor].
Qed.

End IRQAcquiredReturn.
