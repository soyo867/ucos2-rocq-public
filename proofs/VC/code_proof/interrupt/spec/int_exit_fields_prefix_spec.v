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
Require Import Ucos2Verify.VC.code.sched.spec.sched_profile_heap_spec.
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
Require Import Ucos2Verify.VC.code.task.spec.task_pending_irq_switch_source_spec.
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
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


Module IRQCPrefix.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Import FlagPendSchedulerResources.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The selected configuration has no per-task profiling or TLS writes.
    These are the existing OSIntExit counter, selector and global-counter
    fragments.  The proof keeps their supplied heap endpoints. *)
Lemma os_sched_switch_prefix_execution_deterministic : forall sg before first second,
  os_sched_source_switch_prefix_execution sg before first ->
  os_sched_source_switch_prefix_execution sg before second -> first = second.
Proof.
  intros sg before first second
    [_ [_ [selected [high [current [Hselect [_ [_ [_ Hcounter]]]]]]]]]
    [_ [_ [selected' [high' [current' [Hselect' [_ [_ [_ Hcounter']]]]]]]]].
  assert (selected = selected') by
    (eapply os_int_exit_selection_heap_fragment_deterministic; eassumption).
  subst selected'; eapply os_sched_profile_global_fragment_deterministic; eassumption.
Qed.

Lemma os_int_exit_switch_prefix_execution_deterministic : forall sg before first second,
  os_int_exit_source_switch_prefix_execution sg before first ->
  os_int_exit_source_switch_prefix_execution sg before second -> first = second.
Proof.
  intros sg before first second [counted [Hcounter Hselect]] [counted' [Hcounter' Hselect']].
  assert (counted = counted') by
    (eapply os_int_exit_masked_active_counter_deterministic; eassumption).
  subst counted'; eapply os_sched_switch_prefix_execution_deterministic; eassumption.
Qed.

(** The running observation is read from this actual fragment and this
    original fields owner.  No invariant-to-Running implication is used. *)
Lemma os_int_exit_active_counter_fields_frame_preservation : forall sg state
  (frame : Assertion) before after,
  (UCOS2_fields_inv sg state ** frame) before ->
  os_int_exit_masked_counter_fragment sg before true after ->
  (UCOS2_fields_inv sg (os_int_exit_counter_state true state) ** frame) after.
Proof.
  intros sg state frame before after
    [owned [rest [Hjoin [[Hvalid Hraw] Hframe]]]] Hcounter.
  pose proof (os_int_exit_fields_raw_running_load sg state owned Hraw) as Hread.
  assert (Hread_whole : uchar_load sg.(g_OSRunning)
    (if state.(SchedState).(isRunning) then 1 else 0) before).
  { eapply uchar_load_frame; eassumption. }
  assert (Hactual : uchar_load sg.(g_OSRunning) 1 before).
  { inversion Hcounter; subst; assumption. }
  assert (Hone : (if state.(SchedState).(isRunning) then 1 else 0) = 1)
    by (eapply uchar_load_deterministic; eassumption).
  rewrite Hone in Hread.
  destruct (os_int_exit_counter_heap_fields_raw_post sg true state owned Hraw)
    as [written [Hwrites Hwritten]].
  assert (Hprivate : os_int_exit_masked_counter_fragment sg owned true written).
  { econstructor; [exact Hread| |exact Hwrites].
    apply os_int_exit_fields_raw_nesting_load; exact Hraw. }
  destruct (os_int_exit_masked_counter_fragment_frame sg owned true written rest before
    Hprivate Hjoin) as [final [Hwhole Hfinal]].
  assert (final = after) by
    (eapply os_int_exit_masked_active_counter_deterministic; eassumption).
  subst final; exists written, rest; split; [exact Hfinal|].
  split; [split; [exact Hvalid|exact Hwritten]|exact Hframe].
Qed.

(** Start with the original counter fragment; the following C selector
    and OSCtxSwCtr write are produced from its actual resulting heap. *)
Lemma os_int_exit_fields_switch_prefix_after_counter : forall sg state
  (frame : Assertion) before counted,
  os_int_exit_requests_switch true state = true ->
  state.(SchedState).(readyList) <> [] ->
  (UCOS2_fields_inv sg state ** unmap_table_rep sg ** frame) before ->
  os_int_exit_masked_counter_fragment sg before true counted ->
  exists after,
    os_int_exit_source_switch_prefix_execution sg before after /\
    sched_high_ready_consistency (os_int_exit_ready_checkpoint true state).(TskState)
      (os_int_exit_ready_checkpoint true state).(SchedState) /\
    (UCOS2_fields_inv sg (os_int_exit_ready_checkpoint true state) **
      unmap_table_rep sg ** frame) after.
Proof.
  intros sg state frame before counted Hswitch Hnonempty Hpre Hcounter.
  assert (Hopen : UCOS2_fields_inv sg state ** unmap_table_rep sg ** frame |--
    UCOS2_fields_inv sg state ** (unmap_table_rep sg ** frame)) by entailer!.
  pose proof (os_int_exit_active_counter_fields_frame_preservation sg state
    (unmap_table_rep sg ** frame) before counted (Hopen before Hpre) Hcounter) as Hcounted.
  assert (Horder : UCOS2_fields_inv sg (os_int_exit_counter_state true state) **
    (unmap_table_rep sg ** frame) |--
    UCOS2_fields_inv sg (os_int_exit_counter_state true state) **
    unmap_table_rep sg ** frame) by entailer!.
  destruct (os_sched_fields_switch_prefix_frame_source sg
    (os_int_exit_counter_state true state) frame counted Hswitch Hnonempty
    (Horder counted Hcounted)) as [after [Hselect [Hhigh Hafter]]].
  exists after; split; [exists counted; split; assumption|].
  split; [exact Hhigh|exact Hafter].
Qed.

(** This transports to the supplied prefix endpoint, using deterministic
    execution rather than replacing it with an unrelated produced heap. *)
Lemma os_int_exit_fields_switch_prefix_preservation : forall sg state
  (frame : Assertion) before after,
  os_int_exit_requests_switch true state = true ->
  state.(SchedState).(readyList) <> [] ->
  (UCOS2_fields_inv sg state ** unmap_table_rep sg ** frame) before ->
  os_int_exit_source_switch_prefix_execution sg before after ->
  sched_high_ready_consistency (os_int_exit_ready_checkpoint true state).(TskState)
    (os_int_exit_ready_checkpoint true state).(SchedState) /\
  (UCOS2_fields_inv sg (os_int_exit_ready_checkpoint true state) **
    unmap_table_rep sg ** frame) after.
Proof.
  intros sg state frame before after Hswitch Hnonempty Hpre Hprefix.
  pose proof Hprefix as [counted [Hcounter Hselect]].
  destruct (os_int_exit_fields_switch_prefix_after_counter sg state frame before counted
    Hswitch Hnonempty Hpre Hcounter) as [produced [Hproduced Hpost]].
  assert (produced = after) by
    (eapply os_int_exit_switch_prefix_execution_deterministic; eassumption).
  subst produced; exact Hpost.
Qed.

(** A real transfer's selected destination supplies this fact.  There is
    no ready/nonempty guard in the execution relation or new API input. *)
Lemma os_int_exit_configured_transfer_ready_nonempty : forall environment sg handler entry transfer,
  os_int_exit_transfer_source
    (task_sw_hook_call_environment environment).(task_stack_call_external)
    environment.(task_stack_call_port) sg handler entry transfer ->
  entry.(SchedState).(readyList) <> [].
Proof.
  intros environment sg handler entry transfer [Hswitch [_ [_ [Hhook [[Hhigh _] _]]]]].
  change (transfer.(os_int_exit_hooked_state) = os_int_exit_ready_checkpoint true entry) in Hhook.
  rewrite Hhook in Hhigh.
  change (os_sched_requests_switch (os_int_exit_after_nesting entry) = true) in Hswitch.
  pose proof (proj1 (os_sched_requests_switch_iff _) Hswitch) as [Henabled _].
  change ((os_sched_ready_checkpoint (os_int_exit_after_nesting entry)).(highRdyTid) =
    Some transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)) in Hhigh.
  unfold os_sched_ready_checkpoint in Hhigh; rewrite Henabled, Hswitch in Hhigh.
  change (hd_error entry.(SchedState).(readyList) =
    Some transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)) in Hhigh.
  intros Hempty; rewrite Hempty in Hhigh; discriminate.
Qed.

Definition os_int_exit_prefix_fields_owner environment critical sg handler state
  original saved acquired receipt other (frame : Assertion) : Assertion :=
  let resource := kernel_saved_continuation_entry environment.(task_stack_call_continuations) state.(TskState)
    (kernel_sched_saved_local_resource_at environment.(task_stack_call_platform) critical sg state.(TskState)
      original saved acquired receipt other) in
  UCOS2_fields_inv sg state ** store_parked_continuations resource state.(TskState).(parkedTaskStacks) **
  (interrupt_platform_running environment.(task_stack_call_platform)
     handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
   os_int_exit_context_resources environment.(task_stack_call_port) handler ** unmap_table_rep sg ** frame).

(** All three supplied proof indices belong to the same original entry,
    transfer and heaps.  The capsule family uses the same original call,
    saved/acquired masks, receipt and other-local policy at both cuts. *)
Lemma os_int_exit_configured_c_prefix_fields_resources :
  forall environment critical sg handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap
    (source : os_int_exit_transfer_source
      (task_sw_hook_call_environment environment).(task_stack_call_external)
      environment.(task_stack_call_port) sg handler entry transfer)
    (prefix : os_int_exit_source_switch_prefix_execution sg before prepared)
    (hook : kernel_heap_execution [] prepared hooked_heap),
  os_int_exit_prefix_fields_owner (task_sw_hook_call_environment environment) critical sg handler entry
    original saved acquired receipt other frame before ->
  sched_high_ready_consistency transfer.(os_int_exit_hooked_state).(TskState)
    transfer.(os_int_exit_hooked_state).(SchedState) /\
  os_int_exit_prefix_fields_owner (task_sw_hook_call_environment environment) critical sg handler
    transfer.(os_int_exit_hooked_state) original saved acquired receipt other frame hooked_heap.
Proof.
  intros environment critical sg handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap source prefix hook Hinput.
  pose proof source as [Hswitch [_ [_ [Hhook _]]]].
  change (transfer.(os_int_exit_hooked_state) = os_int_exit_ready_checkpoint true entry) in Hhook.
  pose proof (os_int_exit_configured_transfer_ready_nonempty environment sg handler entry transfer source)
    as Hnonempty.
  set (capsules := store_parked_continuations
    (kernel_saved_continuation_entry (task_sw_hook_call_environment environment).(task_stack_call_continuations)
      entry.(TskState) (kernel_sched_saved_local_resource_at environment.(task_stack_call_platform)
        critical sg entry.(TskState) original saved acquired receipt other)) entry.(TskState).(parkedTaskStacks)).
  set (residual := capsules ** (interrupt_platform_running environment.(task_stack_call_platform)
    handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources environment.(task_stack_call_port) handler ** frame)).
  assert (Hopen : os_int_exit_prefix_fields_owner (task_sw_hook_call_environment environment) critical sg
    handler entry original saved acquired receipt other frame |--
    UCOS2_fields_inv sg entry ** unmap_table_rep sg ** residual).
  { unfold os_int_exit_prefix_fields_owner, residual, capsules; entailer!. }
  destruct (os_int_exit_fields_switch_prefix_preservation sg entry residual before prepared
    Hswitch Hnonempty (Hopen before Hinput) prefix) as [Hhigh Hprepared].
  assert (Hnil : kernel_heap_execution [] prepared prepared).
  { repeat split; try reflexivity; constructor. }
  assert (hooked_heap = prepared) by
    (eapply kernel_heap_execution_deterministic; [exact hook|exact Hnil]).
  subst hooked_heap; split; [rewrite Hhook; exact Hhigh|].
  assert (Hclose : UCOS2_fields_inv sg (os_int_exit_ready_checkpoint true entry) **
    unmap_table_rep sg ** residual |--
    os_int_exit_prefix_fields_owner (task_sw_hook_call_environment environment) critical sg handler
      transfer.(os_int_exit_hooked_state) original saved acquired receipt other frame).
  { rewrite Hhook; unfold os_int_exit_prefix_fields_owner, residual, capsules.
    change (os_int_exit_ready_checkpoint true entry).(TskState) with entry.(TskState).
    entailer!. }
  exact (Hclose prepared Hprepared).
Qed.

(** Construct the C selector and the configured no-write hook from the
    supplied actual counter cut.  This returns the prefix witness used by
    the later install/restore consumer, together with its own heap owner. *)
Lemma os_int_exit_configured_c_prefix_from_counter :
  forall environment critical sg handler entry transfer original saved acquired receipt other frame before counted
    (source : os_int_exit_transfer_source
      (task_sw_hook_call_environment environment).(task_stack_call_external)
      environment.(task_stack_call_port) sg handler entry transfer)
    (counter : os_int_exit_masked_counter_fragment sg before true counted),
  os_int_exit_prefix_fields_owner (task_sw_hook_call_environment environment) critical sg handler entry
    original saved acquired receipt other frame before ->
  exists prepared (prefix : os_int_exit_source_switch_prefix_execution sg before prepared)
    (hook : kernel_heap_execution [] prepared prepared),
    sched_high_ready_consistency transfer.(os_int_exit_hooked_state).(TskState)
      transfer.(os_int_exit_hooked_state).(SchedState) /\
    os_int_exit_prefix_fields_owner (task_sw_hook_call_environment environment) critical sg handler
      transfer.(os_int_exit_hooked_state) original saved acquired receipt other frame prepared.
Proof.
  intros environment critical sg handler entry transfer original saved acquired receipt other frame before counted
    source counter Hinput.
  pose proof source as [Hswitch _].
  pose proof (os_int_exit_configured_transfer_ready_nonempty environment sg handler entry transfer source)
    as Hnonempty.
  set (residual := store_parked_continuations
    (kernel_saved_continuation_entry (task_sw_hook_call_environment environment).(task_stack_call_continuations)
      entry.(TskState) (kernel_sched_saved_local_resource_at environment.(task_stack_call_platform)
        critical sg entry.(TskState) original saved acquired receipt other)) entry.(TskState).(parkedTaskStacks) **
    (interrupt_platform_running environment.(task_stack_call_platform)
      handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources environment.(task_stack_call_port) handler ** frame)).
  assert (Hopen : os_int_exit_prefix_fields_owner (task_sw_hook_call_environment environment) critical sg
    handler entry original saved acquired receipt other frame |--
    UCOS2_fields_inv sg entry ** unmap_table_rep sg ** residual).
  { unfold os_int_exit_prefix_fields_owner, residual; entailer!. }
  destruct (os_int_exit_fields_switch_prefix_after_counter sg entry residual before counted Hswitch Hnonempty
    (Hopen before Hinput) counter) as [prepared [prefix Hpost]].
  assert (hook : kernel_heap_execution [] prepared prepared).
  { repeat split; try reflexivity; constructor. }
  exists prepared, prefix, hook.
  exact (os_int_exit_configured_c_prefix_fields_resources environment critical sg handler entry transfer
    original saved acquired receipt other frame before prepared prepared source prefix hook Hinput).
Qed.

End IRQCPrefix.
