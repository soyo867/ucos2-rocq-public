(** Report-only ordinary module extracted from the frozen checked C context.
    The original proof bodies are retained under the recorded shared-reference map. *)
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
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.lib.task.
Require Export Ucos2Verify.lib.sched.
Require Export Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Export Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_current_source_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Export Ucos2Verify.lib.event.
Require Export Ucos2Verify.lib.event_wait.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_always_nonswitch_source_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_wake_source_spec.
Require Export Ucos2Verify.lib.event_pool.
Require Export Ucos2Verify.lib.flag_fields_resources.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_program_region_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Export Ucos2Verify.lib.task_stack.
Require Export Ucos2Verify.lib.task_storage.
Require Export Ucos2Verify.lib.kernel_program_storage.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Export Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_task_nontimer_source_spec.
Require Export Ucos2Verify.VC.code.sched.spec.flag_fields_client_spec.
Require Export Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Export Ucos2Verify.VC.code.task.spec.flag_fields_publication_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Export Ucos2Verify.lib.cross_module_invariants.
Require Export Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Export Ucos2Verify.lib.kernel_execution.
Require Export Ucos2Verify.lib.task_context.
Require Export Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.lib.kernel_heap_execution.
Require Export Ucos2Verify.lib.kernel_heap_observation.
Require Export Ucos2Verify.lib.kernel_heap_storage.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Export Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Export Ucos2Verify.VC.code.sched.spec.flag_fields_local_return_spec.
Require Export Ucos2Verify.VC.code.sched.spec.flag_fields_heap_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Export Ucos2Verify.lib.field_storage.
Require Export Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Export Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Export Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_current_irq_source_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Export Ucos2Verify.lib.task_retirement.
Require Export Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Export Ucos2Verify.VC.code.interrupt.spec.int_enter_heap_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Export Ucos2Verify.VC.code.sched.spec.flag_fields_sched_source_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_pend_inherit_call_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_current_client_source_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Export Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Export Ucos2Verify.lib.flag.
Require Export Ucos2Verify.lib.tick.
Require Export Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_return_spec.
Require Export Ucos2Verify.lib.array_abstraction.
Require Export Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Export Ucos2Verify.lib.queue_core.
Require Export Ucos2Verify.lib.kernel_resources.
Require Export Ucos2Verify.lib.kernel_names.
Require Export Ucos2Verify.VC.code.queue.spec.q_create_lifecycle_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_post_api_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_fields_disabled_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Export Ucos2Verify.lib.task_idle_ready.
Require Export Ucos2Verify.lib.timer_execution.
Require Export Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Export Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Export Ucos2Verify.lib.ucos2_spatial.
Require Export Ucos2Verify.lib.task_status.
Require Export Ucos2Verify.lib.flag_stack.
Require Export Ucos2Verify.VC.code.flag.spec.flag_block_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_block_call_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_unlink_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_source_resources_spec.
Require Export Ucos2Verify.VC.code.sched.spec.flag_source_call_spec.
Require Export Ucos2Verify.lib.error_codes.
Require Export Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Export Ucos2Verify.lib.flag_node_fields.
Require Export Ucos2Verify.VC.code.flag.spec.flag_block_call_fields_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_unlink_fields_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_source_fields_resources_spec.
Require Export Ucos2Verify.VC.code.sched.spec.flag_continuation_fields_resources_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_api_entry_source_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_continuation_return_stage_spec.
Require Export Ucos2Verify.VC.code.core.spec.kernel_idle_ready_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_modular_call_spec.
Require Export Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Export Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_call_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_save_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_wake_source_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_task_return_irq_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_task_delete_source_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_pend_sched_phase_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


Import UCOS2_C_Rules ListNotations.
Import PrimitiveComponent.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Exact recombination of the ordinary C high-cache and counter stores.
    The boolean in the counter is the real source switch request. *)
Lemma os_sched_selected_work_cells_prefix_inv : forall sg entry,
  UCOS2_state_inv sg entry -> os_sched_selection_enabled entry = true ->
  entry.(SchedState).(readyList) <> nil ->
  os_sched_fields_work_cells sg entry (os_sched_selected entry) (os_sched_selected_tcb sg entry)
    (if os_sched_requests_switch entry
     then (os_sched_counter entry + 1) mod 4294967296 else os_sched_counter entry) |--
  UCOS2_fields_inv sg (os_sched_prefix_state entry) ** unmap_table_rep sg.
Proof.
  intros sg entry Hvalid Henabled Hnonempty.
  pose proof (proj1 (os_sched_selection_enabled_iff entry) Henabled) as [Hints Hlocks].
  assert (Hintr : interrupt_in_range entry.(IntrState)).
  { unfold interrupt_in_range; rewrite Hints, Hlocks; lia. }
  unfold os_sched_prefix_state.
  sep_apply_r_atomic (os_sched_fields_prefix_merge_inv sg entry Hvalid (fun _ => Hnonempty)).
  unfold os_sched_fields_work_cells, os_sched_fields_work_frame,
    os_sched_fields_remaining_task_storage_sched, os_sched_prefix_rep,
    os_sched_prefix_physical_rep, os_sched_counter_stage.
  rewrite Henabled.
  unfold sched_new_rep, sched_cache_cells, sched_physical_without_high,
    task_public_storage, task_public_storage_without_prio_tbl, store_prio_tbl,
    UCOS2_raw_rep_missing_task_storage_sched_flag, UCOS2_selected_rep.
  rewrite sched_rows_array_equiv.
  unfold os_sched_ints, os_sched_locks, os_sched_group, os_sched_rows,
    os_sched_selected, os_sched_selected_tcb, os_sched_current, os_sched_counter, os_sched_table.
  cbn [UCOS2_module_rep].
  destruct (os_sched_requests_switch entry);
    cbn [sched_increment_switch_counter curSchedPrio curTaskID ctxSwCtr isRunning];
    unfold interrupt_inv, store_int_state; entailer!.
Qed.

Lemma os_sched_selected_work_cells_masked : forall environment critical local active
  sg call saved acquired entry,
  UCOS2_state_inv sg entry -> os_sched_selection_enabled entry = true ->
  entry.(SchedState).(readyList) <> nil ->
  task_stack_live_coverage entry.(TskState) (task_stack_call_active_key call) ->
  os_sched_active_local_stable active ->
  critical_region_masked environment.(task_stack_call_platform) critical sg
    call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
  task_tcb_init_stack_context environment call ** os_sched_fields_capsules environment local entry **
  active call entry **
  os_sched_fields_work_cells sg entry (os_sched_selected entry) (os_sched_selected_tcb sg entry)
    (if os_sched_requests_switch entry
     then (os_sched_counter entry + 1) mod 4294967296 else os_sched_counter entry) |--
  kernel_continuation_call_masked environment.(task_stack_call_continuations) kernel_program_fields_inv
    local critical sg (task_stack_call_active_key call) call saved acquired (os_sched_prefix_state entry) **
  active call (os_sched_prefix_state entry).
Proof.
  intros environment critical local active sg call saved acquired entry Hvalid Henabled
    Hnonempty Hcoverage Hstable.
  sep_apply_l_atomic (os_sched_selected_work_cells_prefix_inv sg entry Hvalid Henabled Hnonempty).
  sep_apply_l_atomic (proj1 (os_sched_active_prefix_transport active call entry Hstable)).
  sep_apply_r_atomic (proj1 (os_sched_fields_restore_input_masked_world environment critical local
    sg call saved acquired (os_sched_prefix_state entry))).
  unfold os_sched_fields_restore_input, task_tcb_init_stack_context.
  assert (Hcapsules : os_sched_fields_capsules environment local (os_sched_prefix_state entry) =
    os_sched_fields_capsules environment local entry) by reflexivity.
  rewrite Hcapsules.
  change (task_stack_live_coverage (os_sched_prefix_state entry).(TskState)
    (task_stack_call_active_key call)) in Hcoverage.
  entailer!.
Qed.
