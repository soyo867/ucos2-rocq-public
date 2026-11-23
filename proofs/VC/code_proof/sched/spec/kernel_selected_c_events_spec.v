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
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


Module SelectedProgramEvents.
Import CriticalComponent PrimitiveComponent SelectedCProgram.

Definition flag_pend_program_c_event environment critical sg event : Prop :=
  exists stopped,
    kernel_c_sequence (kernel_program_selected_c_step environment critical sg
      (flag_pend_program_c_observer event) (flag_pend_program_c_origin event))
      event.(flag_pend_event_before) event.(flag_pend_event_first_heap)
      event.(flag_pend_event_input) stopped event.(flag_pend_event_current)
      event.(flag_pend_event_last_heap) event.(flag_pend_event_output).


Lemma flag_pend_program_c_event_resources : forall environment critical sg event,
  flag_pend_program_c_event environment critical sg event ->
  event.(flag_pend_event_input) event.(flag_pend_event_first_heap) /\
    event.(flag_pend_event_output) event.(flag_pend_event_last_heap).
Proof.
  intros environment critical sg event [stopped Hrun].
  eapply kernel_program_selected_c_sequence_resources; exact Hrun.
Qed.


Lemma flag_pend_program_c_event_primitive : forall environment critical sg event,
  flag_pend_task_primitive_c_event environment critical sg event ->
  flag_pend_program_c_event environment critical sg event.
Proof.
  intros environment critical sg event Hactual.
  exists false; apply KernelCSequenceAtom, kernel_program_selected_paired_primitive,
    FlagPendTaskPrimitiveCStep; exact Hactual.
Qed.


Lemma flag_pend_program_c_event_current_cache : forall environment critical sg event,
  flag_pend_program_c_event environment critical sg event ->
  event.(flag_pend_event_caller) = FlagPendTaskCaller event.(flag_pend_event_original) ->
  task_in_range sg event.(flag_pend_event_before).(TskState) ->
  kernel_call_task_source event.(flag_pend_event_original) event.(flag_pend_event_before) ->
  sched_current_consistency event.(flag_pend_event_before).(TskState)
    event.(flag_pend_event_before).(SchedState) ->
  kernel_call_normal_return event.(flag_pend_event_original) event.(flag_pend_event_before)
    event.(flag_pend_event_returned) event.(flag_pend_event_current) ->
  kernel_call_task_source event.(flag_pend_event_returned) event.(flag_pend_event_current) ->
  sched_current_consistency event.(flag_pend_event_current).(TskState)
    event.(flag_pend_event_current).(SchedState).
Proof.
  intros environment critical sg event [stopped Hrun] Hcaller Hrange Hsource Hcache Hnormal Hreturned.
  unfold flag_pend_program_c_observer, flag_pend_program_c_origin in Hrun.
  rewrite Hcaller in Hrun; cbn in Hrun.
  exact (proj2 (kernel_program_selected_c_sequence_completed_current_cache environment critical sg
    event.(flag_pend_event_original) event.(flag_pend_event_returned)
    event.(flag_pend_event_before) event.(flag_pend_event_first_heap) event.(flag_pend_event_input)
    stopped event.(flag_pend_event_current) event.(flag_pend_event_last_heap) event.(flag_pend_event_output)
    Hrun Hrange Hsource Hcache Hnormal Hreturned)).
Qed.


Lemma flag_pend_program_c_save_event_input_range :
  forall environment critical local next_local active sg original mask saved before first_heap returned current last_heap,
  flag_pend_program_c_event environment critical sg
    (flag_pend_task_save_completed_c_event environment critical local next_local active sg
      original mask saved before first_heap returned current last_heap) ->
  task_in_range sg before.(TskState).
Proof.
  intros environment critical local next_local active sg original mask saved before first_heap returned current last_heap Hactual.
  pose proof (proj1 (flag_pend_program_c_event_resources _ _ _ _ Hactual)) as Hinput.
  exact (flag_pend_caller_save_input_task_in_range environment critical local active sg
    (FlagPendTaskCaller original) original mask before first_heap Hinput).
Qed.


Lemma flag_pend_program_c_restore_event_input_range :
  forall environment critical local next_local active sg original saved acquired before first_heap returned current last_heap,
  flag_pend_program_c_event environment critical sg
    (flag_pend_task_restore_completed_c_event environment critical local next_local active sg
      original saved acquired before first_heap returned current last_heap) ->
  task_in_range sg before.(TskState).
Proof.
  intros environment critical local next_local active sg original saved acquired before first_heap returned current last_heap Hactual.
  pose proof (proj1 (flag_pend_program_c_event_resources _ _ _ _ Hactual)) as Hinput.
  exact (flag_pend_caller_restore_input_task_in_range environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before first_heap Hinput).
Qed.

(** The same event gives its input range and output normal return.  Only
    the existing entry and returned Task-source observations are consumed.
    No public cache/ready/false-stop premise is added. *)

Lemma flag_pend_program_c_save_current_cache :
  forall environment critical local next_local active sg original mask saved before first_heap returned current last_heap,
  flag_pend_program_c_event environment critical sg
    (flag_pend_task_save_completed_c_event environment critical local next_local active sg
      original mask saved before first_heap returned current last_heap) ->
  kernel_call_task_source original before ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  kernel_call_task_source returned current ->
  sched_current_consistency current.(TskState) current.(SchedState).
Proof.
  intros environment critical local next_local active sg original mask saved before first_heap returned current last_heap
    Hactual Hsource Hcache Hreturned.
  pose proof (proj2 (flag_pend_program_c_event_resources _ _ _ _ Hactual)) as Houtput.
  destruct Houtput as [[Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]] Howned].
  eapply (flag_pend_program_c_event_current_cache environment critical sg
    (flag_pend_task_save_completed_c_event environment critical local next_local active sg
      original mask saved before first_heap returned current last_heap)); try eassumption; try reflexivity.
  exact (flag_pend_program_c_save_event_input_range environment critical local next_local active sg
    original mask saved before first_heap returned current last_heap Hactual).
Qed.


Lemma flag_pend_program_c_restore_current_cache :
  forall environment critical local next_local active sg original saved acquired before first_heap returned current last_heap,
  flag_pend_program_c_event environment critical sg
    (flag_pend_task_restore_completed_c_event environment critical local next_local active sg
      original saved acquired before first_heap returned current last_heap) ->
  kernel_call_task_source original before ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  kernel_call_task_source returned current ->
  sched_current_consistency current.(TskState) current.(SchedState).
Proof.
  intros environment critical local next_local active sg original saved acquired before first_heap returned current last_heap
    Hactual Hsource Hcache Hreturned.
  pose proof (proj2 (flag_pend_program_c_event_resources _ _ _ _ Hactual)) as Houtput.
  destruct Houtput as [[Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]] Howned].
  eapply (flag_pend_program_c_event_current_cache environment critical sg
    (flag_pend_task_restore_completed_c_event environment critical local next_local active sg
      original saved acquired before first_heap returned current last_heap)); try eassumption; try reflexivity.
  exact (flag_pend_program_c_restore_event_input_range environment critical local next_local active sg
    original saved acquired before first_heap returned current last_heap Hactual).
Qed.

End SelectedProgramEvents.
