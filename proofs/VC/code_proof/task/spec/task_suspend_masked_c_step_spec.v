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
Require Export Ucos2Verify.VC.code.task.spec.task_suspend_c_step_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
















Module TaskSuspendMaskedC.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import CriticalComponent PrimitiveComponent TaskSuspendActualC.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The original acquired/checkpoint masked owners are retained independently.
    Their continuation-capsule indices follow the actual state update.  Only
    the external frame stays fixed; Restore and the optional Scheduler call
    remain subsequent C segments. *)
Record task_suspend_masked_completion environment critical saved_local sg
  caller saved call (frame : Assertion) before after : Prop := {
  suspend_masked_source : task_suspend_actual_source sg call;
  suspend_masked_input :
    (task_suspend_masked environment critical saved_local sg caller saved
      call.(suspend_actual_entry) call.(suspend_actual_entry) ** frame) before;
  suspend_masked_output :
    (task_suspend_masked environment critical saved_local sg caller saved
      call.(suspend_actual_entry) call.(suspend_actual_checkpoint) ** frame) after
}.

Lemma task_suspend_masked_completion_from_c_post :
  forall environment critical saved_local sg caller saved call frame before after,
  task_suspend_current_read_view sg call.(suspend_actual_request) call.(suspend_actual_entry)
    call.(suspend_actual_current_pointer) call.(suspend_actual_current_priority)
    call.(suspend_actual_read_residual) ->
  (task_suspend_masked environment critical saved_local sg caller saved
    call.(suspend_actual_entry) call.(suspend_actual_entry) ** frame) before ->
  (coq_prop (task_suspend_step sg call.(suspend_actual_request) call.(suspend_actual_current_priority)
    call.(suspend_actual_entry) call.(suspend_actual_result) call.(suspend_actual_self)
    call.(suspend_actual_checkpoint)) &&
    (task_suspend_masked environment critical saved_local sg caller saved
      call.(suspend_actual_entry) call.(suspend_actual_checkpoint) ** frame)) after ->
  task_suspend_masked_completion environment critical saved_local sg caller saved call frame before after.
Proof.
  intros environment critical saved_local sg caller saved call frame before after Hread Hinput [Hstep Houtput].
  constructor; [split; assumption|exact Hinput|exact Houtput].
Qed.

Lemma task_suspend_masked_completion_from_acquired_c_post :
  forall environment critical saved_local sg original mask original_state
    caller saved call frame before after,
  task_suspend_acquired_facts critical sg original call.(suspend_actual_request) mask original_state
    saved caller call.(suspend_actual_entry) call.(suspend_actual_current_pointer)
    call.(suspend_actual_current_priority) call.(suspend_actual_read_residual) ->
  (task_suspend_masked environment critical saved_local sg caller saved
    call.(suspend_actual_entry) call.(suspend_actual_entry) ** frame) before ->
  (coq_prop (task_suspend_step sg call.(suspend_actual_request) call.(suspend_actual_current_priority)
    call.(suspend_actual_entry) call.(suspend_actual_result) call.(suspend_actual_self)
    call.(suspend_actual_checkpoint)) &&
    (task_suspend_masked environment critical saved_local sg caller saved
      call.(suspend_actual_entry) call.(suspend_actual_checkpoint) ** frame)) after ->
  task_suspend_masked_completion environment critical saved_local sg caller saved call frame before after.
Proof.
  intros environment critical saved_local sg original mask original_state caller saved call frame before after
    [Hentry [Hcompleted [Hclients [Hsave [Hvalid Hread]]]]] Hinput Houtput.
  eapply task_suspend_masked_completion_from_c_post; eassumption.
Qed.

Inductive task_suspend_masked_c_step environment critical sg : kernel_c_sequence_spec.KernelCSegmentRelation :=
| TaskSuspendMaskedCStep : forall saved_local caller saved call frame before after,
    task_suspend_masked_completion environment critical saved_local sg caller saved call frame before after ->
    task_suspend_masked_c_step environment critical sg call.(suspend_actual_entry) before
      (task_suspend_masked environment critical saved_local sg caller saved
        call.(suspend_actual_entry) call.(suspend_actual_entry) ** frame) false
      call.(suspend_actual_checkpoint) after
      (task_suspend_masked environment critical saved_local sg caller saved
        call.(suspend_actual_entry) call.(suspend_actual_checkpoint) ** frame).

Lemma task_suspend_masked_c_step_from_acquired_c_post :
  forall environment critical saved_local sg original mask original_state
    caller saved call frame before after,
  task_suspend_acquired_facts critical sg original call.(suspend_actual_request) mask original_state
    saved caller call.(suspend_actual_entry) call.(suspend_actual_current_pointer)
    call.(suspend_actual_current_priority) call.(suspend_actual_read_residual) ->
  (task_suspend_masked environment critical saved_local sg caller saved
    call.(suspend_actual_entry) call.(suspend_actual_entry) ** frame) before ->
  (coq_prop (task_suspend_step sg call.(suspend_actual_request) call.(suspend_actual_current_priority)
    call.(suspend_actual_entry) call.(suspend_actual_result) call.(suspend_actual_self)
    call.(suspend_actual_checkpoint)) &&
    (task_suspend_masked environment critical saved_local sg caller saved
      call.(suspend_actual_entry) call.(suspend_actual_checkpoint) ** frame)) after ->
  task_suspend_masked_c_step environment critical sg call.(suspend_actual_entry) before
    (task_suspend_masked environment critical saved_local sg caller saved
      call.(suspend_actual_entry) call.(suspend_actual_entry) ** frame) false
    call.(suspend_actual_checkpoint) after
    (task_suspend_masked environment critical saved_local sg caller saved
      call.(suspend_actual_entry) call.(suspend_actual_checkpoint) ** frame).
Proof.
  intros environment critical saved_local sg original mask original_state caller saved call frame before after
    Hfacts Hinput Houtput.
  constructor.
  eapply task_suspend_masked_completion_from_acquired_c_post; eassumption.
Qed.

Lemma task_suspend_masked_c_step_resources :
  forall environment critical sg entry before input stopped returned after output,
  task_suspend_masked_c_step environment critical sg entry before input stopped returned after output ->
  input before /\ output after.
Proof.
  intros environment critical sg entry before input stopped returned after output Hstep.
  destruct Hstep as [saved_local caller saved call frame before after [Hsource Hinput Houtput]]; auto.
Qed.

Lemma task_suspend_masked_c_step_preserves_observer :
  forall environment critical sg entry before input stopped returned after output observer origin,
  task_suspend_masked_c_step environment critical sg entry before input stopped returned after output ->
  task_invocation_active entry.(TskState) observer origin /\
    sched_observer_spec.sched_observer_current_cache origin entry ->
  task_invocation_active returned.(TskState) observer origin /\
    sched_observer_spec.sched_observer_current_cache origin returned.
Proof.
  intros environment critical sg entry before input stopped returned after output observer origin Hstep Hactive.
  destruct Hstep as [saved_local caller saved call frame before after [[Hread Hcode] Hinput Houtput]].
  eapply task_suspend_step_preserves_observer; eassumption.
Qed.

Lemma task_suspend_masked_c_step_observer_lifetime :
  forall environment critical sg entry before input stopped returned after output observer origin,
  task_suspend_masked_c_step environment critical sg entry before input stopped returned after output ->
  sched_observer_spec.task_observer_lifetime_result observer origin entry.(TskState) returned.(TskState) stopped.
Proof.
  intros environment critical sg entry before input stopped returned after output observer origin Hstep.
  destruct Hstep as [saved_local caller saved call frame before after [[Hread Hcode] Hinput Houtput]].
  eapply task_suspend_step_observer_lifetime; exact Hcode.
Qed.

Lemma task_suspend_masked_c_step_creation_frames :
  forall environment critical sg entry before input stopped returned after output task_observer event_observer,
  task_suspend_masked_c_step environment critical sg entry before input stopped returned after output ->
  task_creation_frame task_observer entry.(TskState) returned.(TskState) /\
  event_creation_frame event_observer entry.(EventState) returned.(EventState) /\
  entry.(NameState) = returned.(NameState) /\
  timer_public_trace sg entry.(TimerState) returned.(TimerState).
Proof.
  intros environment critical sg entry before input stopped returned after output task_observer event_observer Hstep.
  destruct Hstep as [saved_local caller saved call frame before after [[Hread Hcode] Hinput Houtput]].
  eapply task_suspend_step_creation_frames; exact Hcode.
Qed.

Lemma task_suspend_masked_c_step_control_fields :
  forall environment critical sg entry before input stopped returned after output,
  task_suspend_masked_c_step environment critical sg entry before input stopped returned after output ->
  returned.(SchedState).(isRunning) = entry.(SchedState).(isRunning) /\
  returned.(IntrState) = entry.(IntrState).
Proof.
  intros environment critical sg entry before input stopped returned after output Hstep.
  destruct Hstep as [saved_local caller saved call frame before after [[Hread Hcode] Hinput Houtput]].
  eapply task_suspend_step_control_fields; exact Hcode.
Qed.

Lemma task_suspend_masked_owner_valid :
  forall environment critical saved_local sg caller saved acquired state frame heap,
  (task_suspend_masked environment critical saved_local sg caller saved acquired state ** frame) heap ->
  UCOS2_state_inv sg state.
Proof.
  intros environment critical saved_local sg caller saved acquired state frame heap Howner.
  assert (Hvalid : task_suspend_masked environment critical saved_local sg caller saved acquired state ** frame |--
    coq_prop (UCOS2_state_inv sg state) &&
      (task_suspend_masked environment critical saved_local sg caller saved acquired state ** frame)).
  { unfold task_suspend_masked, UCOS2_inv; Intros; entailer!. }
  exact (proj1 (Hvalid heap Howner)).
Qed.

Lemma task_suspend_masked_c_step_idle_non_idle :
  forall environment critical sg observed entry before input stopped returned after output,
  task_suspend_masked_c_step environment critical sg entry before input stopped returned after output ->
  (task_idle_ready sg entry.(TskState) -> task_idle_ready sg returned.(TskState)) /\
  (flag_pend_non_idle_at sg observed entry -> flag_pend_non_idle_at sg observed returned).
Proof.
  intros environment critical sg observed entry before input stopped returned after output Hstep.
  destruct Hstep as [saved_local caller saved call frame before after [[Hread Hcode] Hinput Houtput]].
  eapply task_suspend_step_idle_non_idle; [|exact Hcode].
  eapply task_suspend_masked_owner_valid; exact Hinput.
Qed.

End TaskSuspendMaskedC.
