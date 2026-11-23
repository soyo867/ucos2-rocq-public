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
Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_terminal_return_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_call_value_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


(** OSIntExit's real selected-return suffix.  [entry] and [transfer] are
    retained from the original C invocation.  The input owner is explicitly
    the post-hook cut, not a relabelling of the earlier function entry.
    The C prefix must feed that same cut.  The actual selected descriptor,
    install and IRQ return are preserved as parameters of the completion. *)
Module IRQSelectedCompletion.
Import PrimitiveComponent TerminalCallValue IRQTerminalReturn FlagPendSchedulerResources.

Definition irq_selected_suffix_input environment critical sg handler transfer original saved acquired
  receipt other (frame : Assertion) : Assertion :=
  let hooked := transfer.(os_int_exit_hooked_state) in
  let resource := kernel_saved_continuation_entry environment.(task_stack_call_continuations) hooked.(TskState)
    (kernel_sched_saved_local_resource_at environment.(task_stack_call_platform) critical sg hooked.(TskState)
      original saved acquired receipt other) in
  UCOS2_fields_inv sg hooked ** store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
  (interrupt_platform_running environment.(task_stack_call_platform)
     handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
   os_int_exit_context_resources environment.(task_stack_call_port) handler ** unmap_table_rep sg ** frame).

Definition irq_selected_suffix_receipt handler (receipt frame : Assertion) : Assertion :=
  receipt ** task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame.

Definition irq_selected_suffix_output environment critical sg handler transfer original saved acquired receipt other frame :=
  let returned := kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack)
    transfer.(os_int_exit_incoming_fragments) in
  flag_pend_caller_restore_input environment critical other
    (fun _ _ => irq_selected_suffix_receipt handler receipt frame) sg
    (FlagPendTaskCaller returned) returned saved acquired (os_int_exit_installed_state transfer).

Inductive kernel_irq_selected_suffix_c_completion environment critical sg handler entry transfer original saved acquired
  receipt other frame before installed selected after
  (source : os_int_exit_transfer_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) sg handler entry transfer)
  (install : sched_install_heap_fragment sg before installed
    (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp))
  (restore : armv7a_restore_transition environment.(task_stack_call_continuations)
    handler selected installed after) : Prop :=
| KernelIRQSelectedSuffixCComplete :
    irq_selected_suffix_input environment critical sg handler transfer original saved acquired receipt other frame before ->
    transfer.(os_int_exit_incoming_stack) = original.(os_sched_call_stack) ->
    original.(os_sched_call_origin) = RunningInvocation transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)
      transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration) ->
    task_invocation_active transfer.(os_int_exit_hooked_state).(TskState)
      original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
    irq_selected_c_terminal_return environment critical sg handler entry transfer original saved acquired receipt other
      before installed selected after frame source install restore
      (kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack) transfer.(os_int_exit_incoming_fragments)) ->
    kernel_irq_selected_suffix_c_completion environment critical sg handler entry transfer original saved acquired receipt other
      frame before installed selected after source install restore.

Lemma kernel_irq_selected_suffix_c_completion_from_c_post :
  forall environment critical sg handler entry transfer original saved acquired receipt other before frame
    (source : os_int_exit_transfer_source environment.(task_stack_call_external)
      environment.(task_stack_call_port) sg handler entry transfer),
  sched_high_ready_consistency transfer.(os_int_exit_hooked_state).(TskState)
    transfer.(os_int_exit_hooked_state).(SchedState) ->
  transfer.(os_int_exit_incoming_stack) = original.(os_sched_call_stack) ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage transfer.(os_int_exit_hooked_state).(TskState) None ->
  irq_selected_suffix_input environment critical sg handler transfer original saved acquired receipt other frame before ->
  exists installed selected
    (install : sched_install_heap_fragment sg before installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp)),
    armv7a_continuation_restore_reads selected installed /\
    forall after (restore : armv7a_restore_transition environment.(task_stack_call_continuations)
      handler selected installed after),
    kernel_irq_selected_suffix_c_completion environment critical sg handler entry transfer original saved acquired receipt other
      frame before installed selected after source install restore.
Proof.
  intros environment critical sg handler entry transfer original saved acquired receipt other before frame
    source Hhigh Hincoming Haddress Hcoverage Hinput.
  destruct (irq_selected_c_terminal_return_from_c_post environment critical sg handler entry transfer
    original saved acquired receipt other before frame source Hhigh Hincoming Haddress Hcoverage Hinput)
    as [installed [selected [install [Hreads Hreturn]]]].
  exists installed, selected, install; split; [exact Hreads|].
  intros after restore.
  destruct (Hreturn after restore) as [Hterminal [Hsource [Hsame Hrest]]].
  constructor; [exact Hinput|exact Hincoming|exact (proj1 Hsource)| |exact Hterminal].
  exact (proj1 (proj2 Hsource)).
Qed.

Lemma kernel_irq_selected_suffix_c_completion_resources :
  forall environment critical sg handler entry transfer original saved acquired receipt other frame before installed selected after
    source install restore,
  kernel_irq_selected_suffix_c_completion environment critical sg handler entry transfer original saved acquired receipt other
    frame before installed selected after source install restore ->
  irq_selected_suffix_input environment critical sg handler transfer original saved acquired receipt other frame before /\
  irq_selected_suffix_output environment critical sg handler transfer original saved acquired receipt other frame after.
Proof.
  intros environment critical sg handler entry transfer original saved acquired receipt other frame before installed selected after
    source install restore Hcomplete; destruct Hcomplete as [Hinput Hincoming Horigin Hactive Hterminal].
  split; [exact Hinput|].
  destruct Hterminal as [Hstack Hsp Hfragments Hcall Howned].
  unfold irq_selected_suffix_output.
  assert (Hvalue : armv7a_continuation_resumed_call selected original =
    kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack) transfer.(os_int_exit_incoming_fragments)).
  { apply armv7a_continuation_resumed_call_tuple; assumption. }
  rewrite <- Hvalue.
  apply (proj2 (flag_pend_task_restore_input_masked_equiv environment critical other
    (fun _ _ => irq_selected_suffix_receipt handler receipt frame) sg
    (armv7a_continuation_resumed_call selected original) saved acquired (os_int_exit_installed_state transfer))).
  match type of Howned with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold irq_selected_suffix_receipt; entailer!. }
  exact (Hclose after Howned).
Qed.

Lemma kernel_irq_selected_suffix_c_completion_task_source :
  forall environment critical sg handler entry transfer original saved acquired receipt other frame before installed selected after
    source install restore,
  kernel_irq_selected_suffix_c_completion environment critical sg handler entry transfer original saved acquired receipt other
    frame before installed selected after source install restore ->
  kernel_call_task_source
    (kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack) transfer.(os_int_exit_incoming_fragments))
    (os_int_exit_installed_state transfer).
Proof.
  intros environment critical sg handler entry transfer original saved acquired receipt other frame before installed selected after
    source install restore [Hinput Hincoming Horigin Hactive Hterminal].
  unfold kernel_call_task_source, kernel_restored_stack_call; cbn.
  split; [exact Horigin|]. split; [exact Hactive|].
  unfold task_execution_current; rewrite Horigin.
  exact (proj1 (os_int_exit_transfer_current_at environment.(task_stack_call_external)
    environment.(task_stack_call_port) sg handler entry transfer source)).
Qed.

Lemma kernel_irq_selected_suffix_c_completion_preserves_observer :
  forall environment critical sg handler entry transfer original saved acquired receipt other frame before installed selected after
    source install restore observer origin,
  kernel_irq_selected_suffix_c_completion environment critical sg handler entry transfer original saved acquired receipt other
    frame before installed selected after source install restore ->
  task_invocation_active transfer.(os_int_exit_hooked_state).(TskState) observer origin ->
  task_invocation_active (os_int_exit_installed_state transfer).(TskState) observer origin /\
    sched_observer_current_cache origin (os_int_exit_installed_state transfer).
Proof.
  intros environment critical sg handler entry transfer original saved acquired receipt other frame before installed selected after
    source install restore observer origin Hcomplete Hactive.
  split; [exact Hactive|].
  apply sched_current_consistency_implies_observer_cache.
  pose proof source as Htransfer; destruct Htransfer as [_ [_ [_ [_ [Hdestination _]]]]].
  destruct Hdestination as [Hhigh [[node [Hnode [Hgeneration [Hpriority Hsp]]]] Hrest]].
  unfold sched_current_consistency, os_int_exit_installed_state; cbn.
  rewrite Hhigh; exists node; exact (conj Hnode Hpriority).
Qed.

Lemma kernel_irq_selected_suffix_c_completion_lifetime :
  forall environment critical sg handler entry transfer original saved acquired receipt other frame before installed selected after
    source install restore observer origin,
  kernel_irq_selected_suffix_c_completion environment critical sg handler entry transfer original saved acquired receipt other
    frame before installed selected after source install restore ->
  task_observer_lifetime_result observer origin transfer.(os_int_exit_hooked_state).(TskState)
    (os_int_exit_installed_state transfer).(TskState) false.
Proof.
  intros; apply task_observer_lifetime_result_not_stopped, task_observer_lifetime_transport_fields.
  - reflexivity.
  - intros; reflexivity.
Qed.

End IRQSelectedCompletion.
