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
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_return_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_call_value_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module IRQTerminalReturn.
Import PrimitiveComponent SequenceReturn TerminalCallValue.
Import FlagPendSchedulerResources.

Inductive irq_selected_c_terminal_return environment critical sg handler entry transfer
  original saved acquired (receipt : Assertion) other before installed selected irq_return (frame : Assertion)
  (source : os_int_exit_transfer_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) sg handler entry transfer)
  (install : sched_install_heap_fragment sg before installed
    (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp))
  (restore : armv7a_restore_transition environment.(task_stack_call_continuations)
    handler selected installed irq_return) : OsSchedCallContext -> Prop :=
| IRQSelectedCTerminalReturn :
    selected.(armv7a_continuation_stack) = transfer.(os_int_exit_incoming_stack) ->
    selected.(armv7a_continuation_sp) = transfer.(os_int_exit_incoming_sp) ->
    selected.(armv7a_continuation_fragments) = transfer.(os_int_exit_incoming_fragments) ->
    selected.(armv7a_continuation_call) = Some original ->
    (kernel_continuation_call_masked environment.(task_stack_call_continuations)
       kernel_program_fields_inv other critical sg
       (task_stack_call_active_key (armv7a_continuation_resumed_call selected original))
       (armv7a_continuation_resumed_call selected original) saved acquired
       (os_int_exit_installed_state transfer) ** receipt **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)
       irq_return ->
    irq_selected_c_terminal_return environment critical sg handler entry transfer original saved acquired receipt
      other before installed selected irq_return frame source install restore
      (armv7a_continuation_resumed_call selected original).

(** This producer calls the existing C/IRQ proof once and keeps exactly
    the witnesses it returns.  TaskSource/ready/cache are not inputs to the
    packet constructor; the returned context is calculated from selected. *)
Lemma irq_selected_c_terminal_return_from_c_post :
  forall environment critical sg handler entry transfer original saved acquired receipt other before frame
    (source : os_int_exit_transfer_source environment.(task_stack_call_external)
      environment.(task_stack_call_port) sg handler entry transfer),
  let abi := environment.(task_stack_call_continuations) in
  let hooked := transfer.(os_int_exit_hooked_state) in
  let local := kernel_sched_saved_local_resource_at environment.(task_stack_call_platform) critical sg
    hooked.(TskState) original saved acquired receipt other in
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  transfer.(os_int_exit_incoming_stack) = original.(os_sched_call_stack) ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) None ->
  (UCOS2_fields_inv sg hooked ** store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
   (interrupt_platform_running environment.(task_stack_call_platform)
      handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources environment.(task_stack_call_port) handler ** unmap_table_rep sg ** frame)) before ->
  exists installed selected
    (install : sched_install_heap_fragment sg before installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp)),
    armv7a_continuation_restore_reads selected installed /\
    forall irq_return
      (restore : armv7a_restore_transition abi handler selected installed irq_return),
    let returned := kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack)
      transfer.(os_int_exit_incoming_fragments) in
    irq_selected_c_terminal_return environment critical sg handler entry transfer original saved acquired receipt
      other before installed selected irq_return frame source install restore returned /\
    kernel_call_task_source returned (os_int_exit_installed_state transfer) /\
    task_tcb_init_stack_same_call returned original /\
    kernel_call_normal_return original hooked returned (os_int_exit_installed_state transfer) /\
    kernel_call_control_rely sg hooked (os_int_exit_installed_state transfer).
Proof.
  intros environment critical sg handler entry transfer original saved acquired receipt other before frame
    source abi hooked local resource Hhigh Hincoming Haddress Hcoverage Hpre.
  destruct (os_sched_task_irq_selected_masked_return_source environment critical sg handler entry transfer
    original saved acquired receipt other before frame source Hhigh Hincoming Haddress Hcoverage Hpre)
    as [installed [selected [Hlease [Hsp [Hfragments [Hcall [Hpc [Hmask
      [Hinstall [Hpointers [Hreads Hrestore]]]]]]]]]]].
  exists installed, selected, Hinstall; split; [exact Hreads|].
  intros irq_return Hactual returned.
  destruct (Hrestore irq_return Hactual)
    as [Hmemory [Hsame [Hsource [Hready [Hcurrent_ready [Hnormal [Hcontrol Howned]]]]]]].
  assert (Hvalue : armv7a_continuation_resumed_call selected original = returned).
  { unfold returned; apply armv7a_continuation_resumed_call_tuple; [congruence|exact Hfragments]. }
  rewrite <- Hvalue; split.
  - constructor; try assumption; congruence.
  - exact (conj Hsource (conj Hsame (conj Hnormal Hcontrol))).
Qed.

Lemma irq_selected_c_terminal_return_current :
  forall environment critical sg handler entry transfer original saved acquired receipt other
    before installed selected irq_return frame source install restore returned,
  irq_selected_c_terminal_return environment critical sg handler entry transfer original saved acquired receipt
    other before installed selected irq_return frame source install restore returned ->
  (os_int_exit_installed_state transfer).(SchedState).(curTaskID) =
    Some returned.(os_sched_call_stack).(stackLeaseSlot).
Proof.
  intros environment critical sg handler entry transfer original saved acquired receipt other
    before installed selected irq_return frame source install restore returned Hterminal.
  destruct Hterminal as [Hlease Hsp Hfragments Hcall Howned].
  change ((os_int_exit_installed_state transfer).(SchedState).(curTaskID) =
    Some selected.(armv7a_continuation_stack).(stackLeaseSlot)).
  rewrite Hlease.
  exact (proj1 (os_int_exit_transfer_current_at environment.(task_stack_call_external)
    environment.(task_stack_call_port) sg handler entry transfer source)).
Qed.

End IRQTerminalReturn.
