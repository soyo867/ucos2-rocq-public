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
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


Module CallPreservation.
Import PrimitiveComponent.


Lemma flag_active_fresh_task_fields : forall sg original node call state,
  flag_active_fresh sg original node call state |--
  coq_prop (exists task, flag_active_task_fields original call state task) &&
    flag_active_fresh sg original node call state.
Proof.
  intros sg original node call state heap Howned; split; [|exact Howned].
  destruct Howned as [[task [Hfields Hzero]] Hnode].
  exists task; exact Hfields.
Qed.

Lemma flag_active_waiting_task_fields : forall sg original node call state,
  flag_active_waiting sg original node call state |--
  coq_prop (exists task, flag_active_task_fields original call state task) &&
    flag_active_waiting sg original node call state.
Proof.
  intros sg original node call state heap Howned; split; [|exact Howned].
  destruct Howned as [[task [Hfields Hregistration]] Hnode].
  exists task; exact Hfields.
Qed.

(** In particular, the existing flag_pend_wait_active assertion has this
    form, with its outcome/Idle/non-Idle observations in [observations]. *)
Lemma flag_active_waiting_observation_task_fields : forall sg original node
  (observations : OsSchedCallContext -> UCOS2_Verify_State -> Prop) call state,
  (coq_prop (observations call state) && flag_active_waiting sg original node call state) |--
  coq_prop (exists task, flag_active_task_fields original call state task) &&
    (coq_prop (observations call state) && flag_active_waiting sg original node call state).
Proof.
  intros sg original node observations call state heap Howned; split; [|exact Howned].
  exact (proj1 (flag_active_waiting_task_fields sg original node call state heap (proj2 Howned))).
Qed.

Lemma flag_pend_caller_save_input_active_fields :
  forall environment critical local active sg original call mask state,
  (forall observed current, active observed current |--
    coq_prop (exists task, flag_active_task_fields original observed current task) &&
      active observed current) ->
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller call) call mask state |--
  coq_prop (UCOS2_state_inv sg state /\
    task_invocation_active state.(TskState) original.(os_sched_call_invocation)
      original.(os_sched_call_origin)) &&
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller call) call mask state.
Proof.
  intros environment critical local active sg original call mask state Hfields heap Howned.
  split; [|exact Howned]. split.
  - exact (proj1 (flag_pend_caller_save_input_state_inv
      environment critical local active sg (FlagPendTaskCaller call) call mask state heap Howned)).
  - destruct Howned as [_ [owned [rest [Hjoin [Hsave Hunmap]]]]].
    destruct Hsave as [core [active_heap [Hsplit [Hcore Hactive]]]].
    destruct (proj1 (Hfields call state active_heap Hactive))
      as [task [Hsame [Horigin [Hlookup [Hgeneration [Hlive Hclear]]]]]].
    exact Hlive.
Qed.

Lemma flag_pend_caller_restore_input_active_fields :
  forall environment critical local active sg original call saved acquired state,
  (forall observed current, active observed current |--
    coq_prop (exists task, flag_active_task_fields original observed current task) &&
      active observed current) ->
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller call) call saved acquired state |--
  coq_prop (UCOS2_state_inv sg state /\
    task_invocation_active state.(TskState) original.(os_sched_call_invocation)
      original.(os_sched_call_origin)) &&
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller call) call saved acquired state.
Proof.
  intros environment critical local active sg original call saved acquired state Hfields heap Howned.
  split; [|exact Howned]. split.
  - exact (proj1 (flag_pend_caller_restore_input_state_inv
      environment critical local active sg (FlagPendTaskCaller call) call saved acquired state heap Howned)).
  - destruct Howned as [_ [owned [rest [Hjoin [Hrestore Hunmap]]]]].
    destruct Hrestore as [core [active_heap [Hsplit [Hcore Hactive]]]].
    destruct (proj1 (Hfields call state active_heap Hactive))
      as [task [Hsame [Horigin [Hlookup [Hgeneration [Hlive Hclear]]]]]].
    exact Hlive.
Qed.

Lemma task_invocation_active_all_origins_transport : forall before after invocation origin,
  task_invocation_active before invocation origin ->
  task_invocation_active after invocation origin ->
  forall other, task_invocation_active before invocation other ->
    task_invocation_active after invocation other.
Proof.
  intros before after invocation origin [Hregistration Hbefore] Hafter other
    [Hother Hrest].
  assert (other = origin) by congruence; subst other; exact Hafter.
Qed.

(** Algebra used by the concrete owner projections below.  The validity
    and active facts are extracted from their original endpoint heaps. *)
Lemma kernel_program_c_sequence_observer_call_preserved :
  forall environment critical sg original before first_heap input stopped current last_heap output
    (run : kernel_c_sequence_spec.kernel_c_sequence
      (kernel_program_c_step environment critical sg
        original.(os_sched_call_invocation) original.(os_sched_call_origin))
      before first_heap input stopped current last_heap output),
  kernel_program_c_sequence_call_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None
    before first_heap input stopped current last_heap output run ->
  UCOS2_state_inv sg before -> UCOS2_state_inv sg current ->
  task_invocation_active before.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  task_invocation_active current.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) before current /\
    stopped = false.
Proof.
  intros environment critical sg original before first_heap input stopped current last_heap output
    run Hsource Hbefore Hcurrent Hactive_before Hactive_current.
  destruct (kernel_program_c_sequence_call_source_frames environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None
    before first_heap input stopped current last_heap output run Hsource)
    as [Hcreation [Hevent [Hname Htimer]]].
  split.
  - intro Hvalid; split; [exact Hcurrent|].
    split; [exact Hcreation|]. split; [|exact Hname].
    eapply task_invocation_active_all_origins_transport; eassumption.
  - pose proof (kernel_program_c_sequence_observer_lifetime environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin)
      before first_heap input stopped current last_heap output run) as Hlife.
    destruct Hlife as [Htransport Hstopped].
    destruct stopped; [|reflexivity].
    assert (Hinitial_lifetime : sched_observer_spec.task_observer_lifetime before.(TskState)
      original.(os_sched_call_invocation) original.(os_sched_call_origin)).
    { eapply sched_observer_spec.task_observer_lifetime_from_active; [|exact Hactive_before].
      exact (proj1 (proj2 Hbefore)). }
    exfalso; exact (Hstopped Hinitial_lifetime eq_refl Hactive_current).
Qed.

(** The actual Scheduler Save goal already has this same returned source.
    The same-call equality comes from this execution's original normal
    return observation.  No new source-return law is added to the effect. *)
Lemma kernel_call_normal_return_stack_source_preserved : forall original returned before current,
  kernel_call_normal_return original before returned current ->
  kernel_call_task_source returned current ->
  task_tcb_init_stack_source_preserved original before current.
Proof.
  intros original returned before current [Hsame Havailable] Hsource Hinitial.
  exact (proj1 (task_tcb_init_stack_same_call_source_iff returned original current Hsame) Hsource).
Qed.

End CallPreservation.
