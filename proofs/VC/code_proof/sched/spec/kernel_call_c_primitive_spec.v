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
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_always_nonswitch_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_wake_source_spec.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_region_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_nontimer_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.flag_fields_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.lib.kernel_execution.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_local_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_irq_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.lib.task_retirement.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_sched_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_inherit_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_client_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_return_spec.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_api_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_disabled_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.lib.flag_stack.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_unlink_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_source_call_spec.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.lib.flag_node_fields.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_unlink_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_fields_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_fields_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_api_entry_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_return_stage_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_idle_ready_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_call_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_save_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_wake_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_irq_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_delete_source_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Export Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module PrimitiveComponent.









































Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition flag_pend_caller_save_observation environment critical sg caller original returned_caller returned
  mask saved before acquired : Prop :=
  match caller, returned_caller with
  | FlagPendTaskCaller actual, FlagPendTaskCaller next =>
      actual = original /\ next = returned /\
      os_sched_continuation_save_effect environment critical sg original mask saved before returned acquired /\
      task_tcb_init_stack_same_call returned original /\
      task_tcb_init_stack_source_preserved original before acquired
  | FlagPendInterruptCaller view key, FlagPendInterruptCaller next next_key =>
      returned = original /\ next_key = key /\ sched_fields_same_view next view /\
      critical_region_interval critical sg view.(os_execution_invocation) before acquired
  | _, _ => False
  end.

Definition flag_pend_caller_restore_observation environment critical sg caller original returned_caller returned
  released current : Prop :=
  match caller, returned_caller with
  | FlagPendTaskCaller actual, FlagPendTaskCaller next =>
      actual = original /\ next = returned /\
      os_sched_continuation_restore_effect environment critical sg original released returned current /\
      task_tcb_init_stack_same_call returned original /\
      task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released current /\
      (UCOS2_state_inv sg released -> task_tcb_init_stack_source_preserved original released current)
  | FlagPendInterruptCaller view key, FlagPendInterruptCaller next next_key =>
      returned = original /\ next_key = key /\ sched_fields_same_view next view /\
      critical_region_interval critical sg view.(os_execution_invocation) released current
  | _, _ => False
  end.

(** Actual uninterrupted Task Save/Restore branches.  The existing platform
    transitions are used as their approved C primitive contracts.  Distinct
    physical heaps are retained; kernel-state identity is not heap identity.
    This file does not instantiate or strengthen FlagPendLinkedSources. *)

Lemma flag_pend_caller_save_input_state_inv :
  forall environment critical local active sg caller call mask state,
  flag_pend_caller_save_input environment critical local active sg caller call mask state |--
  coq_prop (UCOS2_state_inv sg state) &&
    flag_pend_caller_save_input environment critical local active sg caller call mask state.
Proof.
  intros; destruct caller;
    unfold flag_pend_caller_save_input, flag_pend_active_save_input,
      os_sched_fields_save_input, UCOS2_fields_inv;
    Intros; entailer!.
Qed.

Lemma flag_pend_caller_restore_input_state_inv :
  forall environment critical local active sg caller call saved acquired state,
  flag_pend_caller_restore_input environment critical local active sg caller call saved acquired state |--
  coq_prop (UCOS2_state_inv sg state) &&
    flag_pend_caller_restore_input environment critical local active sg caller call saved acquired state.
Proof.
  intros; destruct caller;
    unfold flag_pend_caller_restore_input, flag_pend_active_restore_input,
      os_sched_fields_restore_input, UCOS2_fields_inv;
    Intros; entailer!.
Qed.

Lemma flag_pend_caller_save_input_task_in_range :
  forall environment critical local active sg caller call mask state heap,
  flag_pend_caller_save_input environment critical local active sg caller call mask state heap ->
  task_in_range sg state.(TskState).
Proof.
  intros environment critical local active sg caller call mask state heap Hinput.
  pose proof (proj1 (flag_pend_caller_save_input_state_inv
    environment critical local active sg caller call mask state heap Hinput)) as Hvalid.
  exact (proj1 (proj2 Hvalid)).
Qed.

Lemma flag_pend_caller_restore_input_task_in_range :
  forall environment critical local active sg caller call saved acquired state heap,
  flag_pend_caller_restore_input environment critical local active sg caller call saved acquired state heap ->
  task_in_range sg state.(TskState).
Proof.
  intros environment critical local active sg caller call saved acquired state heap Hinput.
  pose proof (proj1 (flag_pend_caller_restore_input_state_inv
    environment critical local active sg caller call saved acquired state heap Hinput)) as Hvalid.
  exact (proj1 (proj2 Hvalid)).
Qed.

(** These are ownership equalities for this exact Task input.  They do not
    transport the arbitrary active predicate across an environment window. *)
Lemma flag_pend_task_save_input_closed_equiv :
  forall environment critical local active sg call mask state,
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller call) call mask state --||--
  (kernel_continuation_call_closed environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg (task_stack_call_active_key call) call mask state ** active call state).
Proof.
  intros; unfold flag_pend_caller_save_input, flag_pend_active_save_input; split.
  - Intros.
    sep_apply_l_atomic (proj1 (os_sched_fields_save_input_closed_world
      environment critical local sg call mask state)); entailer!.
  - sep_apply_l_atomic (proj2 (os_sched_fields_save_input_closed_world
      environment critical local sg call mask state)); entailer!.
Qed.

Lemma flag_pend_task_restore_input_masked_equiv :
  forall environment critical local active sg call saved acquired state,
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller call) call saved acquired state --||--
  (kernel_continuation_call_masked environment.(task_stack_call_continuations)
    kernel_program_fields_inv local critical sg (task_stack_call_active_key call)
    call saved acquired state ** active call state).
Proof.
  intros; unfold flag_pend_caller_restore_input, flag_pend_active_restore_input; split.
  - Intros.
    sep_apply_l_atomic (proj1 (os_sched_fields_restore_input_masked_world
      environment critical local sg call saved acquired state)); entailer!.
  - sep_apply_l_atomic (proj2 (os_sched_fields_restore_input_masked_world
      environment critical local sg call saved acquired state)); entailer!.
Qed.

Lemma flag_pend_call_endpoint_observations_refl : forall environment sg call state,
  flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller call) call state call state.
Proof.
  intros; cbn [flag_pend_call_endpoint_observations].
  split; [tauto|]. split; [tauto|]. split; [tauto|].
  split; [apply kernel_call_normal_return_refl|].
  intros _. unfold kernel_call_control_rely; split; reflexivity.
Qed.

Definition flag_pend_task_save_c_event environment critical local active sg call mask saved
  state before after : FlagPendLinkedEvent :=
  {| flag_pend_event_operation := FlagPendSaveSource;
     flag_pend_event_caller := FlagPendTaskCaller call;
     flag_pend_event_original := call;
     flag_pend_event_returned_caller := FlagPendTaskCaller call;
     flag_pend_event_returned := call;
     flag_pend_event_before := state;
     flag_pend_event_current := state;
     flag_pend_event_first_heap := before;
     flag_pend_event_last_heap := after;
     flag_pend_event_input := flag_pend_caller_save_input environment critical local active sg
       (FlagPendTaskCaller call) call mask state;
     flag_pend_event_output :=
       coq_prop (flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller call) call state call state) &&
       flag_pend_caller_restore_input environment critical local active sg
         (FlagPendTaskCaller call) call saved state state |}.

Definition flag_pend_task_restore_c_event environment critical local active sg call saved acquired
  state before after : FlagPendLinkedEvent :=
  {| flag_pend_event_operation := FlagPendRestoreSource;
     flag_pend_event_caller := FlagPendTaskCaller call;
     flag_pend_event_original := call;
     flag_pend_event_returned_caller := FlagPendTaskCaller call;
     flag_pend_event_returned := call;
     flag_pend_event_before := state;
     flag_pend_event_current := state;
     flag_pend_event_first_heap := before;
     flag_pend_event_last_heap := after;
     flag_pend_event_input := flag_pend_caller_restore_input environment critical local active sg
       (FlagPendTaskCaller call) call saved acquired state;
     flag_pend_event_output :=
       coq_prop (flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller call) call state call state) &&
       flag_pend_caller_save_input environment critical local active sg
         (FlagPendTaskCaller call) call (armv7a_irq_fiq_mask saved) state |}.

Section FlagPendTaskPrimitiveCEvents.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources) (sg : StableGlobVars).

(** Constructors retain the original primitive transition proofs.  There is
    no constructor for an unrelated source or an endpoint-equal C tree. *)
Inductive flag_pend_task_primitive_c_event : FlagPendLinkedEvent -> Prop :=
| FlagPendTaskPrimitiveSave : forall local active call mask state arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers before final_registers after,
    registers.(kernel_save_return_word) = None ->
    valid_os_cpu_sr registers.(kernel_save_cpsr) ->
    armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
    flag_pend_caller_save_input environment critical local active sg (FlagPendTaskCaller call) call mask state before ->
    armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
      final_registers state after ->
    flag_pend_task_primitive_c_event
      (flag_pend_task_save_c_event environment critical local active sg call mask
        final_registers.(kernel_save_r0) state before after)
| FlagPendTaskPrimitiveRestore : forall local active call saved acquired state arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor before written middle final_cursor after,
    cursor.(kernel_restore_r0) = saved ->
    armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
    flag_pend_caller_restore_input environment critical local active sg
      (FlagPendTaskCaller call) call saved acquired state before ->
    armv7a_restore_prefix_transition restore cursor before written middle ->
    armv7a_restore_suffix_transition restore written middle final_cursor after ->
    flag_pend_task_primitive_c_event
      (flag_pend_task_restore_c_event environment critical local active sg call saved acquired state before after).

Lemma flag_pend_task_uninterrupted_save_resources :
  forall local active call mask state arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers before final_registers after,
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  flag_pend_caller_save_input environment critical local active sg (FlagPendTaskCaller call) call mask state before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before final_registers state after ->
  interrupt_saved_value mask final_registers.(kernel_save_r0) /\
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller call) call final_registers.(kernel_save_r0) state state after.
Proof.
  intros local active call mask state arch save registers before final_registers after
    Hreturn Hvalid Hmask Hinput Hactual.
  pose proof (proj1 (flag_pend_task_save_input_closed_equiv environment critical local active sg call mask state)
    before Hinput) as Hclosed.
  destruct (kernel_continuation_call_uninterrupted_save
    environment.(task_stack_call_external) environment.(task_stack_call_platform) environment.(task_stack_call_port)
    critical arch environment.(task_stack_call_continuations) save kernel_program_fields_inv local
    sg (task_stack_call_active_key call) call state mask registers before final_registers state after
    (active call state) Hreturn Hvalid Hmask Hclosed Hactual) as [Hstate [Hr0 [Hrun Houtput]]].
  split.
  - rewrite Hr0; split; assumption.
  - exact (proj2 (flag_pend_task_restore_input_masked_equiv environment critical local active sg
      call final_registers.(kernel_save_r0) state state) after Houtput).
Qed.

Lemma flag_pend_task_uninterrupted_restore_resources :
  forall local active call saved acquired state arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor before written middle final_cursor after,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller call) call saved acquired state before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller call) call (armv7a_irq_fiq_mask saved) state after.
Proof.
  intros local active call saved acquired state arch restore cursor before written middle final_cursor after
    Hr0 Hmask Hinput Hprefix Hsuffix.
  pose proof (proj1 (flag_pend_task_restore_input_masked_equiv environment critical local active sg
    call saved acquired state) before Hinput) as Hmasked.
  destruct (kernel_continuation_call_uninterrupted_restore
    environment.(task_stack_call_external) environment.(task_stack_call_platform) environment.(task_stack_call_port)
    critical arch environment.(task_stack_call_continuations) restore kernel_program_fields_inv local
    sg (task_stack_call_active_key call) call saved acquired state cursor before written middle final_cursor after
    (active call state) Hr0 Hmask Hmasked Hprefix Hsuffix) as [Hrun [Hreturn Houtput]].
  exact (proj2 (flag_pend_task_save_input_closed_equiv environment critical local active sg
    call (armv7a_irq_fiq_mask saved) state) after Houtput).
Qed.

Lemma flag_pend_task_primitive_c_event_resources : forall event,
  flag_pend_task_primitive_c_event event ->
  event.(flag_pend_event_input) event.(flag_pend_event_first_heap) /\
    event.(flag_pend_event_output) event.(flag_pend_event_last_heap).
Proof.
  intros event Hactual; destruct Hactual; cbn.
  - split; [assumption|]. split; [exact (flag_pend_call_endpoint_observations_refl environment sg call state)|].
    exact (proj2 (flag_pend_task_uninterrupted_save_resources
      local active call mask state arch save registers before final_registers after H H0 H1 H2 H3)).
  - split; [assumption|]. split; [exact (flag_pend_call_endpoint_observations_refl environment sg call state)|].
    eapply flag_pend_task_uninterrupted_restore_resources; eassumption.
Qed.

(** The environment branch uses these two distinct cuts around its actual
    C execution.  Neither cut pretends that the whole Restore has returned. *)
Lemma flag_pend_task_restore_prefix_resources :
  forall local active call saved acquired state arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor before written after,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller call) call saved acquired state before ->
  armv7a_restore_prefix_transition restore cursor before written after ->
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller call) call (armv7a_irq_fiq_mask saved) state after.
Proof.
  intros local active call saved acquired state arch restore cursor before written after Hr0 Hmask Hinput Hactual.
  pose proof (proj1 (flag_pend_task_restore_input_masked_equiv environment critical local active sg
    call saved acquired state) before Hinput) as Hmasked.
  unfold kernel_continuation_call_masked in Hmasked.
  assert (Hopen :
    critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) call **
    kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_fields_inv local
      sg (task_stack_call_active_key call) state ** active call state |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) call **
    (kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_fields_inv local
      sg (task_stack_call_active_key call) state ** active call state)) by entailer!.
  destruct (armv7a_restore_prefix_releases_critical_region environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch restore sg call saved acquired cursor before written after
    _ Hr0 Hmask (Hopen before Hmasked) Hactual) as [Hwritten [Hmemory Howned]].
  apply (proj2 (flag_pend_task_save_input_closed_equiv environment critical local active sg
    call (armv7a_irq_fiq_mask saved) state)).
  match type of Howned with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold kernel_continuation_call_closed; entailer!. }
  exact (Hclose after Howned).
Qed.

Lemma flag_pend_task_restore_suffix_resources :
  forall local active call state word arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor before final_cursor after,
  cursor.(kernel_restore_msr_word) = Some word ->
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller call) call (armv7a_irq_fiq_mask word) state before ->
  armv7a_restore_suffix_transition restore cursor before final_cursor after ->
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller call) call (armv7a_irq_fiq_mask word) state after.
Proof.
  intros local active call state word arch restore cursor before final_cursor after Hword Hinput Hactual.
  pose proof (proj1 (flag_pend_task_save_input_closed_equiv environment critical local active sg
    call (armv7a_irq_fiq_mask word) state) before Hinput) as Hclosed.
  unfold kernel_continuation_call_closed in Hclosed.
  assert (Hopen :
    kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      call (armv7a_irq_fiq_mask word) **
    kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_fields_inv local
      sg (task_stack_call_active_key call) state ** active call state |--
    kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      call (armv7a_irq_fiq_mask word) **
    (kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_fields_inv local
      sg (task_stack_call_active_key call) state ** active call state)) by entailer!.
  destruct (armv7a_restore_suffix_transports_owned_execution environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch restore call word cursor before final_cursor after
    _ Hword (Hopen before Hclosed) Hactual) as [Hfinal [Hmemory Howned]].
  apply (proj2 (flag_pend_task_save_input_closed_equiv environment critical local active sg
    call (armv7a_irq_fiq_mask word) state)).
  match type of Howned with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold kernel_continuation_call_closed; entailer!. }
  exact (Hclose after Howned).
Qed.

Inductive flag_pend_task_primitive_c_step : kernel_c_sequence_spec.KernelCSegmentRelation :=
| FlagPendTaskPrimitiveCStep : forall event,
    flag_pend_task_primitive_c_event event ->
    flag_pend_task_primitive_c_step event.(flag_pend_event_before) event.(flag_pend_event_first_heap)
      event.(flag_pend_event_input) false event.(flag_pend_event_current) event.(flag_pend_event_last_heap)
      event.(flag_pend_event_output)
| FlagPendTaskRestoreCPrefix : forall local active call saved acquired state arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor before written after,
    cursor.(kernel_restore_r0) = saved ->
    armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
    flag_pend_caller_restore_input environment critical local active sg
      (FlagPendTaskCaller call) call saved acquired state before ->
    armv7a_restore_prefix_transition restore cursor before written after ->
    flag_pend_task_primitive_c_step state before
      (flag_pend_caller_restore_input environment critical local active sg
        (FlagPendTaskCaller call) call saved acquired state) false state after
      (flag_pend_caller_save_input environment critical local active sg
        (FlagPendTaskCaller call) call (armv7a_irq_fiq_mask saved) state)
| FlagPendTaskRestoreCSuffix : forall local active call state word arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor before final_cursor after,
    cursor.(kernel_restore_msr_word) = Some word ->
    flag_pend_caller_save_input environment critical local active sg
      (FlagPendTaskCaller call) call (armv7a_irq_fiq_mask word) state before ->
    armv7a_restore_suffix_transition restore cursor before final_cursor after ->
    flag_pend_task_primitive_c_step state before
      (flag_pend_caller_save_input environment critical local active sg
        (FlagPendTaskCaller call) call (armv7a_irq_fiq_mask word) state) false state after
      (flag_pend_caller_save_input environment critical local active sg
        (FlagPendTaskCaller call) call (armv7a_irq_fiq_mask word) state).

Lemma flag_pend_task_primitive_c_step_resources : forall state before input stopped current after output,
  flag_pend_task_primitive_c_step state before input stopped current after output -> input before /\ output after.
Proof.
  intros until output; intro Hstep; destruct Hstep.
  - eapply flag_pend_task_primitive_c_event_resources; eassumption.
  - split; [assumption|]. eapply flag_pend_task_restore_prefix_resources; eassumption.
  - split; [assumption|]. eapply flag_pend_task_restore_suffix_resources; eassumption.
Qed.

Lemma flag_pend_task_primitive_c_step_preserves_observer :
  forall observer origin state before input stopped current after output,
  flag_pend_task_primitive_c_step state before input stopped current after output ->
  task_invocation_active state.(TskState) observer origin /\ sched_observer_current_cache origin state ->
  task_invocation_active current.(TskState) observer origin /\ sched_observer_current_cache origin current.
Proof.
  intros until output; intros Hstep Hinitial; destruct Hstep; try exact Hinitial.
  destruct H; exact Hinitial.
Qed.

Lemma flag_pend_task_primitive_c_step_observer_lifetime :
  forall observer origin state before input stopped current after output,
  flag_pend_task_primitive_c_step state before input stopped current after output ->
  task_observer_lifetime_result observer origin state.(TskState) current.(TskState) stopped.
Proof.
  intros until output; intro Hstep; destruct Hstep.
  - destruct H; apply task_observer_lifetime_result_not_stopped, task_observer_lifetime_transport_refl.
  - apply task_observer_lifetime_result_not_stopped, task_observer_lifetime_transport_refl.
  - apply task_observer_lifetime_result_not_stopped, task_observer_lifetime_transport_refl.
Qed.

(** These two constructors are actual producers, not assumptions about
    arbitrary old events.  History is made from the very transition used
    by the sequence's primitive leaf.  The operation and all heap fields
    of the emitted event are fixed below. *)
Lemma flag_pend_task_uninterrupted_save_c_event :
  forall local active call mask state arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers before final_registers after,
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  flag_pend_caller_save_input environment critical local active sg (FlagPendTaskCaller call) call mask state before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before final_registers state after ->
  flag_pend_caller_save_observation environment critical sg (FlagPendTaskCaller call) call
    (FlagPendTaskCaller call) call mask final_registers.(kernel_save_r0) state state /\
  interrupt_saved_value mask final_registers.(kernel_save_r0) /\
  let event := flag_pend_task_save_c_event environment critical local active sg call mask
    final_registers.(kernel_save_r0) state before after in
  flag_pend_task_primitive_c_event event /\
  kernel_c_sequence_spec.kernel_c_sequence flag_pend_task_primitive_c_step event.(flag_pend_event_before) event.(flag_pend_event_first_heap)
    event.(flag_pend_event_input) false event.(flag_pend_event_current) event.(flag_pend_event_last_heap)
    event.(flag_pend_event_output).
Proof.
  intros local active call mask state arch save registers before final_registers after
    Hreturn Hvalid Hmask Hinput Hactual.
  pose proof (proj1 (flag_pend_task_uninterrupted_save_resources local active call mask state arch save
    registers before final_registers after Hreturn Hvalid Hmask Hinput Hactual)) as Hsaved.
  assert (Hpacket : flag_pend_task_primitive_c_event
    (flag_pend_task_save_c_event environment critical local active sg call mask
      final_registers.(kernel_save_r0) state before after)).
  { eapply FlagPendTaskPrimitiveSave; eassumption. }
  split.
  - cbn [flag_pend_caller_save_observation].
    split; [reflexivity|]. split; [reflexivity|]. split.
    + right; split; [eapply KernelCallSaveUninterrupted; eassumption|exact Hsaved].
    + split; [unfold task_tcb_init_stack_same_call; auto|].
      unfold task_tcb_init_stack_source_preserved; auto.
  - split; [exact Hsaved|]. split; [exact Hpacket|].
    apply kernel_c_sequence_spec.KernelCSequenceAtom, FlagPendTaskPrimitiveCStep; exact Hpacket.
Qed.

Lemma flag_pend_task_uninterrupted_restore_c_event :
  forall local active call saved acquired state arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor before written middle final_cursor after,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller call) call saved acquired state before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  flag_pend_caller_restore_observation environment critical sg (FlagPendTaskCaller call) call
    (FlagPendTaskCaller call) call state state /\
  let event := flag_pend_task_restore_c_event environment critical local active sg call saved acquired state before after in
  flag_pend_task_primitive_c_event event /\
  kernel_c_sequence_spec.kernel_c_sequence flag_pend_task_primitive_c_step event.(flag_pend_event_before) event.(flag_pend_event_first_heap)
    event.(flag_pend_event_input) false event.(flag_pend_event_current) event.(flag_pend_event_last_heap)
    event.(flag_pend_event_output).
Proof.
  intros local active call saved acquired state arch restore cursor before written middle final_cursor after
    Hr0 Hmask Hinput Hprefix Hsuffix.
  assert (Hpacket : flag_pend_task_primitive_c_event
    (flag_pend_task_restore_c_event environment critical local active sg call saved acquired state before after)).
  { eapply FlagPendTaskPrimitiveRestore; eassumption. }
  split.
  - cbn [flag_pend_caller_restore_observation].
    split; [reflexivity|]. split; [reflexivity|]. split.
    + right; eapply KernelCallRestoreUninterrupted; eassumption.
    + split; [unfold task_tcb_init_stack_same_call; auto|].
      split; [apply task_tcb_init_call_preserved_refl|].
      unfold task_tcb_init_stack_source_preserved; auto.
  - split; [exact Hpacket|].
    apply kernel_c_sequence_spec.KernelCSequenceAtom, FlagPendTaskPrimitiveCStep; exact Hpacket.
Qed.
End FlagPendTaskPrimitiveCEvents.


















End PrimitiveComponent.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Import PrimitiveComponent.

Import PrimitiveComponent.

Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
(** Sources decorate the original C completion proof.  They retain the
    invocation/allocation from that completion; no constructor assumes any
    creation-frame, cache, ready or future-return conclusion. *)
Import EventStateDef.
Import EventStateDef.



(** A selected environment is an actual sequence of the fixed C program.
    Its existing return owner contains the original C endpoint contract.
    The ABI suffix/prefix below is composed with that very sequence; there
    is no independently supplied old source or endpoint-equal replacement
    tree.  State, caller, local resources and heaps may all change in the
    environment.  Its stopped bit is retained, not assumed false. *)
Import PrimitiveComponent.
