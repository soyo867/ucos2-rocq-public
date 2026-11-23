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
Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_fields_prefix_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


(** OSIntExit's selected C suffix after its real Save result.  OSRunning
    was observed before Save (OSIntExit.c:180); this suffix reads only the
    acquired nesting cell (line 208) before the existing selector.  The
    entry and source below are the original acquired entry/transfer tuple. *)
Module IRQAcquiredCPrefix.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations IRQCPrefix.
Import FlagPendSchedulerResources.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition os_int_exit_acquired_counter_execution sg entry (before after : model) : Prop :=
  uchar_load sg.(g_OSIntNesting) entry.(IntrState).(intNesting) before /\
  kernel_heap_execution (os_int_exit_counter_heap_writes sg true entry) before after.

Lemma os_int_exit_acquired_counter_fields_frame_post : forall sg entry
  (frame : Assertion) before,
  (UCOS2_fields_inv sg entry ** frame) before ->
  exists after,
    os_int_exit_acquired_counter_execution sg entry before after /\
    (UCOS2_fields_inv sg (os_int_exit_counter_state true entry) ** frame) after.
Proof.
  intros sg entry frame before [owned [rest [Hjoin [[Hvalid Hraw] Hframe]]]].
  pose proof (os_int_exit_fields_raw_nesting_load sg entry owned Hraw) as Hread.
  assert (Hwhole_read : uchar_load sg.(g_OSIntNesting) entry.(IntrState).(intNesting) before).
  { eapply uchar_load_frame; eassumption. }
  destruct (os_int_exit_counter_heap_fields_raw_post sg true entry owned Hraw)
    as [written [Hwrites Hwritten]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hwrites Hjoin)
    as [after [Hwhole Hafter]].
  exists after; split; [split; assumption|].
  exists written, rest; split; [exact Hafter|].
  split; [split; [exact Hvalid|exact Hwritten]|exact Hframe].
Qed.

Lemma os_int_exit_acquired_counter_fields_frame_preservation : forall sg entry
  (frame : Assertion) before after,
  (UCOS2_fields_inv sg entry ** frame) before ->
  os_int_exit_acquired_counter_execution sg entry before after ->
  (UCOS2_fields_inv sg (os_int_exit_counter_state true entry) ** frame) after.
Proof.
  intros sg entry frame before after Hinput [Hread Hcounter].
  destruct (os_int_exit_acquired_counter_fields_frame_post sg entry frame before Hinput)
    as [produced [[Hproduced_read Hproduced] Hpost]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced; exact Hpost.
Qed.

Definition os_int_exit_acquired_switch_prefix_execution sg entry (before after : model) : Prop :=
  exists counted,
    os_int_exit_acquired_counter_execution sg entry before counted /\
    os_sched_source_switch_prefix_execution sg counted after.

Lemma os_int_exit_acquired_switch_prefix_deterministic : forall sg entry before first second,
  os_int_exit_acquired_switch_prefix_execution sg entry before first ->
  os_int_exit_acquired_switch_prefix_execution sg entry before second -> first = second.
Proof.
  intros sg entry before first second [counted [[Hread Hcounter] Hselect]]
    [counted' [[Hread' Hcounter'] Hselect']].
  assert (counted = counted') by (eapply kernel_heap_execution_deterministic; eassumption).
  subst counted'; eapply os_sched_switch_prefix_execution_deterministic; eassumption.
Qed.

Lemma os_int_exit_acquired_fields_prefix_frame_post : forall sg entry
  (frame : Assertion) before,
  os_int_exit_requests_switch true entry = true ->
  entry.(SchedState).(readyList) <> [] ->
  (UCOS2_fields_inv sg entry ** unmap_table_rep sg ** frame) before ->
  exists after,
    os_int_exit_acquired_switch_prefix_execution sg entry before after /\
    sched_high_ready_consistency (os_int_exit_ready_checkpoint true entry).(TskState)
      (os_int_exit_ready_checkpoint true entry).(SchedState) /\
    (UCOS2_fields_inv sg (os_int_exit_ready_checkpoint true entry) **
      unmap_table_rep sg ** frame) after.
Proof.
  intros sg entry frame before Hswitch Hnonempty Hinput.
  assert (Hopen : UCOS2_fields_inv sg entry ** unmap_table_rep sg ** frame |--
    UCOS2_fields_inv sg entry ** (unmap_table_rep sg ** frame)) by entailer!.
  destruct (os_int_exit_acquired_counter_fields_frame_post sg entry
    (unmap_table_rep sg ** frame) before (Hopen before Hinput)) as [counted [Hcounter Hcounted]].
  assert (Horder : UCOS2_fields_inv sg (os_int_exit_counter_state true entry) **
    (unmap_table_rep sg ** frame) |--
    UCOS2_fields_inv sg (os_int_exit_counter_state true entry) **
    unmap_table_rep sg ** frame) by entailer!.
  destruct (os_sched_fields_switch_prefix_frame_source sg (os_int_exit_counter_state true entry)
    frame counted Hswitch Hnonempty (Horder counted Hcounted)) as [after [Hselect [Hhigh Hpost]]].
  exists after; split; [exists counted; split; assumption|].
  split; [exact Hhigh|exact Hpost].
Qed.

Lemma os_int_exit_acquired_fields_prefix_preservation : forall sg entry
  (frame : Assertion) before after,
  os_int_exit_requests_switch true entry = true ->
  entry.(SchedState).(readyList) <> [] ->
  (UCOS2_fields_inv sg entry ** unmap_table_rep sg ** frame) before ->
  os_int_exit_acquired_switch_prefix_execution sg entry before after ->
  sched_high_ready_consistency (os_int_exit_ready_checkpoint true entry).(TskState)
    (os_int_exit_ready_checkpoint true entry).(SchedState) /\
  (UCOS2_fields_inv sg (os_int_exit_ready_checkpoint true entry) **
    unmap_table_rep sg ** frame) after.
Proof.
  intros sg entry frame before after Hswitch Hnonempty Hinput Hprefix.
  destruct (os_int_exit_acquired_fields_prefix_frame_post sg entry frame before Hswitch Hnonempty Hinput)
    as [produced [Hproduced Hpost]].
  assert (produced = after) by (eapply os_int_exit_acquired_switch_prefix_deterministic; eassumption).
  subst produced; exact Hpost.
Qed.

Lemma os_int_exit_configured_acquired_prefix_fields_resources :
  forall environment critical sg handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap
    (source : os_int_exit_transfer_source
      (task_sw_hook_call_environment environment).(task_stack_call_external)
      environment.(task_stack_call_port) sg handler entry transfer)
    (prefix : os_int_exit_acquired_switch_prefix_execution sg entry before prepared)
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
  destruct (os_int_exit_acquired_fields_prefix_preservation sg entry residual before prepared
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

(** Only the original input owner is stored.  The output and high-ready
    consistency are derived from the actual execution indices above. *)
Inductive os_int_exit_acquired_c_prefix_completion environment critical sg handler entry transfer
  original saved acquired receipt other frame before prepared hooked_heap
  (source : os_int_exit_transfer_source
    (task_sw_hook_call_environment environment).(task_stack_call_external)
    environment.(task_stack_call_port) sg handler entry transfer)
  (prefix : os_int_exit_acquired_switch_prefix_execution sg entry before prepared)
  (hook : kernel_heap_execution [] prepared hooked_heap) : Prop :=
| OsIntExitAcquiredCPrefixComplete :
    os_int_exit_prefix_fields_owner (task_sw_hook_call_environment environment) critical sg handler entry
      original saved acquired receipt other frame before ->
    os_int_exit_acquired_c_prefix_completion environment critical sg handler entry transfer original
      saved acquired receipt other frame before prepared hooked_heap source prefix hook.

Lemma os_int_exit_acquired_c_prefix_completion_resources :
  forall environment critical sg handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap source prefix hook,
  os_int_exit_acquired_c_prefix_completion environment critical sg handler entry transfer original
    saved acquired receipt other frame before prepared hooked_heap source prefix hook ->
  os_int_exit_prefix_fields_owner (task_sw_hook_call_environment environment) critical sg handler entry
    original saved acquired receipt other frame before /\
  sched_high_ready_consistency transfer.(os_int_exit_hooked_state).(TskState)
    transfer.(os_int_exit_hooked_state).(SchedState) /\
  os_int_exit_prefix_fields_owner (task_sw_hook_call_environment environment) critical sg handler
    transfer.(os_int_exit_hooked_state) original saved acquired receipt other frame hooked_heap.
Proof.
  intros environment critical sg handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap source prefix hook [Hinput].
  split; [exact Hinput|].
  exact (os_int_exit_configured_acquired_prefix_fields_resources environment critical sg handler entry transfer
    original saved acquired receipt other frame before prepared hooked_heap source prefix hook Hinput).
Qed.

(** This is the constructive production entry.  The original selected C
    transfer supplies the switch guard and destination; the owned cells
    supply each actual C load/store.  No endpoint resource or cache fact
    is an input to this producer. *)
Lemma os_int_exit_configured_acquired_prefix_source :
  forall environment critical sg handler entry transfer original saved acquired receipt other frame before
    (source : os_int_exit_transfer_source
      (task_sw_hook_call_environment environment).(task_stack_call_external)
      environment.(task_stack_call_port) sg handler entry transfer),
  os_int_exit_prefix_fields_owner (task_sw_hook_call_environment environment) critical sg handler entry
    original saved acquired receipt other frame before ->
  exists prepared (prefix : os_int_exit_acquired_switch_prefix_execution sg entry before prepared)
    (hook : kernel_heap_execution [] prepared prepared),
    os_int_exit_acquired_c_prefix_completion environment critical sg handler entry transfer original
      saved acquired receipt other frame before prepared prepared source prefix hook.
Proof.
  intros environment critical sg handler entry transfer original saved acquired receipt other frame before
    source Hinput.
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
  destruct (os_int_exit_acquired_fields_prefix_frame_post sg entry residual before Hswitch Hnonempty
    (Hopen before Hinput)) as [prepared [prefix Hpost]].
  assert (hook : kernel_heap_execution [] prepared prepared).
  { repeat split; try reflexivity; constructor. }
  exists prepared, prefix, hook; constructor; exact Hinput.
Qed.

End IRQAcquiredCPrefix.
