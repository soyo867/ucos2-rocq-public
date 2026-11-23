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
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


(** C return selection and actual caller ownership have distinct sources.
    The finite C install/transfer produces the current pointer; the actual
    fresh/waiting owner supplies registration, generation and call identity.
    No lemma below assumes its returned kernel_call_task_source conclusion.

    The complete current-C history has FOUR constructors.  In particular,
    TaskLastCall is produced below from a selection indexed by the very
    last switch-source proof, rather than by projecting the old source
    premise already present in that constructor. *)
Module SourceReturn.
Import PrimitiveComponent.

Lemma flag_active_task_fields_current_source : forall original returned current task,
  flag_active_task_fields original returned current task ->
  current.(SchedState).(curTaskID) = Some returned.(os_sched_call_stack).(stackLeaseSlot) ->
  kernel_call_task_source returned current.
Proof.
  intros original returned current task
    [[Hinv [Horigin Hstack]] [Hrunning [Hlookup [Hgeneration [Hactive Hclear]]]]] Hcurrent.
  unfold kernel_call_task_source; rewrite Hinv, Horigin, Hstack.
  split; [exact Hrunning|]. split; [exact Hactive|].
  unfold task_execution_current; rewrite Hrunning, <- Hstack; exact Hcurrent.
Qed.

(** This consumes the actual direct current-ready C post.  A proof of
    ready which itself used TaskSource is not a producer for this input. *)
Lemma flag_active_task_fields_current_ready_source : forall original returned current task,
  flag_active_task_fields original returned current task ->
  os_sched_task_current_ready returned current ->
  kernel_call_task_source returned current.
Proof.
  intros original returned current task Hfields [ready [Hcurrent Hgeneration]].
  eapply flag_active_task_fields_current_source; [exact Hfields|].
  exact (proj1 (proj2 Hcurrent)).
Qed.

(** The exact original Task C completion and Hactual heap fragment are
    retained.  Hselected is the returned lease from the selected C/port
    tuple; it says nothing about cache, readiness, or a future return. *)
Lemma task_install_c_segment_selected_return_source :
  forall environment local sg frame call before after sp Hactual original returned task,
  InstallComponent.task_install_c_segment environment local sg frame call before after sp Hactual ->
  returned.(os_sched_call_stack) = call.(InstallComponent.task_install_fields_incoming) ->
  flag_active_task_fields original returned (InstallComponent.task_install_fields_current call) task ->
  kernel_call_task_source returned (InstallComponent.task_install_fields_current call).
Proof.
  intros environment local sg frame call before after sp Hactual original returned task
    [Hsource Hcompletion] Hselected Hfields.
  destruct Hcompletion as [Hmodule_source Haddress Hpre Hcurrent Hrestore Hpost].
  eapply flag_active_task_fields_current_source; [exact Hfields|].
  rewrite Hselected; exact (proj1 Hcurrent).
Qed.

(** This is the actual IRQ C completion, including its entry/installed
    heaps and its own IRQ return source.  No Task arch_resume is used. *)
Lemma kernel_irq_transfer_c_completion_selected_return_source :
  forall environment critical sg handler saved entry transfer frame before after original returned task,
  BuiltinComponent.kernel_irq_transfer_c_completion environment critical sg handler saved entry
    transfer frame before after ->
  returned.(os_sched_call_stack) = transfer.(os_int_exit_incoming_stack) ->
  flag_active_task_fields original returned (os_int_exit_installed_state transfer) task ->
  kernel_call_task_source returned (os_int_exit_installed_state transfer).
Proof.
  intros environment critical sg handler saved entry transfer frame before after original returned task
    Hcompletion Hselected Hfields.
  pose proof (BuiltinComponent.kernel_irq_transfer_c_completion_source environment critical sg
    handler saved entry transfer frame before after Hcompletion) as Htransfer.
  pose proof (os_int_exit_transfer_current_at
    (task_sw_hook_call_environment environment).(task_stack_call_external)
    environment.(task_stack_call_port) sg handler entry transfer Htransfer) as Hcurrent.
  eapply flag_active_task_fields_current_source; [exact Hfields|].
  rewrite Hselected; exact (proj1 Hcurrent).
Qed.

(** The source proof itself is an index.  Consequently a second switch
    with equal endpoints cannot replace this last C selection.  Its tuple
    is the selector/SP-save/hook/destination tuple of os_sched_switch_source. *)
Inductive os_sched_switch_selected_call (external : OsSchedExternalResources) sg entry context returned :
  forall current, os_sched_switch_source external sg entry context current -> Prop :=
| OsSchedSwitchSelectedCall : forall sp outgoing hooked incoming resumed
    (Hswitch : os_sched_requests_switch entry = true)
    (Hsave : external.(os_sched_arch_save_source) context sp outgoing)
    (Hhook : kernel_client_step external.(os_sched_hook_action) sg
      (os_sched_save_current_sp (os_sched_prefix_state entry)
        context.(os_sched_call_stack).(stackLeaseSlot) sp) hooked)
    (Hdestination : os_sched_destination_binding external context outgoing hooked incoming resumed),
    returned.(os_sched_call_stack) = incoming ->
    os_sched_switch_selected_call external sg entry context returned
      (os_sched_install_context context outgoing incoming hooked)
      (conj Hswitch
        (ex_intro _ sp (ex_intro _ outgoing (ex_intro _ hooked (ex_intro _ incoming
          (ex_intro _ resumed (conj Hsave (conj Hhook (conj Hdestination eq_refl))))))))).

(** The checked selected-return components already expose this actual
    descriptor/call/lease tuple.  This adapter only retains those values;
    it does not require another instruction-level implementation proof. *)
Lemma os_sched_switch_selected_call_from_continuation :
  forall external sg entry context sp outgoing hooked incoming resumed
    Hswitch Hsave Hhook Hdestination selected previous,
  selected.(armv7a_continuation_call) = Some previous ->
  selected.(armv7a_continuation_stack) = incoming ->
  os_sched_switch_selected_call external sg entry context
    (kernel_selected_call selected (os_sched_install_context context outgoing incoming hooked))
    (os_sched_install_context context outgoing incoming hooked)
    (conj Hswitch
      (ex_intro _ sp (ex_intro _ outgoing (ex_intro _ hooked (ex_intro _ incoming
        (ex_intro _ resumed (conj Hsave (conj Hhook (conj Hdestination eq_refl))))))))).
Proof.
  intros external sg entry context sp outgoing hooked incoming resumed
    Hswitch Hsave Hhook Hdestination selected previous Hcall Hstack.
  constructor; unfold kernel_selected_call; rewrite Hcall; exact Hstack.
Qed.

Lemma os_sched_switch_selected_call_current_pointer : forall external sg entry context returned current
  (source : os_sched_switch_source external sg entry context current),
  os_sched_switch_selected_call external sg entry context returned current source ->
  current.(SchedState).(curTaskID) = Some returned.(os_sched_call_stack).(stackLeaseSlot).
Proof.
  intros external sg entry context returned current source Hselected.
  destruct Hselected as [sp outgoing hooked incoming resumed Hswitch Hsave Hhook Hdestination Hstack].
  change (hooked.(SchedState).(highRdyTid) = Some returned.(os_sched_call_stack).(stackLeaseSlot)).
  rewrite Hstack; exact (proj1 Hdestination).
Qed.

Lemma os_sched_switch_selected_call_task_source : forall external sg entry context returned current
  (source : os_sched_switch_source external sg entry context current) original task,
  os_sched_switch_selected_call external sg entry context returned current source ->
  flag_active_task_fields original returned current task ->
  kernel_call_task_source returned current.
Proof.
  intros external sg entry context returned current source original task Hselected Hfields.
  eapply flag_active_task_fields_current_source; [exact Hfields|].
  eapply os_sched_switch_selected_call_current_pointer; exact Hselected.
Qed.

End SourceReturn.
