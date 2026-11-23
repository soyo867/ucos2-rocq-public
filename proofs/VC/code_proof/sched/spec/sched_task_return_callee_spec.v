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
Require Export Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
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
Require Export Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
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
Require Export Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_fields_active_phase_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_completion_composition_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_c_control_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Instantiate the TaskDel composite with the concrete program union.
    Both syntactic inclusions are discharged by its actual constructors.
    The original two captured sources, local frames and five heaps remain
    those of the checked body producer. *)
Import DeleteComponent CriticalComponent.

(** This is a fixed C interpretation, not a law asserted about an arbitrary
    old linked predicate.  Its producer must supply the same actual C run;
    the raw endpoint observations are part of that run's original output. *)
Import CriticalComponent PrimitiveComponent.

(** The selected source has a concrete interpretation for each original
    caller kind.  Task execution uses the proved C program.  IRQ execution
    additionally admits the already explicit view primitive contract; that
    contract is not promoted to a Task cache-preservation law. *)
Import CriticalComponent PrimitiveComponent.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
(** Sources decorate the original C completion proof.  They retain the
    invocation/allocation from that completion; no constructor assumes any
    creation-frame, cache, ready or future-return conclusion. *)
Import EventStateDef.
Import EventStateDef.












(** Provenance follows the existing execution proof.  An atomic marker is
    supplied by that C module's actual call/allocation protocol.  In
    particular, it may retain a foreign invocation condition; it is not a
    second execution picked for its endpoints. *)
Import CriticalComponent.



(** A selected environment is an actual sequence of the fixed C program.
    Its existing return owner contains the original C endpoint contract.
    The ABI suffix/prefix below is composed with that very sequence; there
    is no independently supplied old source or endpoint-equal replacement
    tree.  State, caller, local resources and heaps may all change in the
    environment.  Its stopped bit is retained, not assumed false. *)
Import PrimitiveComponent.

Module SchedulerCalleePhaseComponent.
Import CriticalComponent PrimitiveComponent TerminalReturn TerminalCallValue.
Import SelectedCProgram SelectedCSource.
Import SchedulerPhaseCandidate.
Import UCOS2_C_Rules TaskStateDef ListNotations FlagPendSchedulerResources.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A final Task switch obtains its endpoint control from the real C
    selector and the checked fixed hook, not from a promise about a
    foreign interval.  SP-save, cache-install and stack-take do not write
    the interrupt counters or OSRunning. *)
Import SchedulerActivePhaseComponent SchedulerPhaseCandidate.

Lemma os_sched_task_configured_switch_endpoint : forall environment sg entry context installed,
  os_sched_switch_source (task_sw_hook_call_environment environment).(task_stack_call_external)
    sg entry context installed ->
  sched_current_consistency installed.(TskState) installed.(SchedState) /\
  os_sched_selection_enabled installed = true /\ kernel_call_control_rely sg entry installed.
Proof.
  intros environment sg entry context installed
    [Hrequest [sp [outgoing [hooked [incoming [resumed [Hsave [Hhook [Hdestination Hinstalled]]]]]]]]].
  change (hooked = os_sched_save_current_sp (os_sched_prefix_state entry)
    context.(os_sched_call_stack).(stackLeaseSlot) sp) in Hhook.
  subst hooked; subst installed.
  split; [eapply os_sched_destination_installs_current_consistency; exact Hdestination|].
  assert (Hsaved_control : kernel_call_control_rely sg (os_sched_prefix_state entry)
    (os_sched_save_current_sp (os_sched_prefix_state entry) context.(os_sched_call_stack).(stackLeaseSlot) sp)).
  { unfold os_sched_save_current_sp; destruct ((os_sched_prefix_state entry).(TskState).(inUsedTaskStates)
      context.(os_sched_call_stack).(stackLeaseSlot)); split; reflexivity. }
  assert (Hcontrol : kernel_call_control_rely sg entry
    (os_sched_install_context context outgoing incoming
      (os_sched_save_current_sp (os_sched_prefix_state entry) context.(os_sched_call_stack).(stackLeaseSlot) sp))).
  { eapply kernel_call_control_rely_trans; [apply os_sched_prefix_control_rely|].
    eapply kernel_call_control_rely_trans; [exact Hsaved_control|]. split; reflexivity. }
  split; [|exact Hcontrol].
  unfold os_sched_selection_enabled; rewrite (proj2 Hcontrol).
  unfold os_sched_requests_switch in Hrequest.
  destruct (os_sched_selection_enabled entry) eqn:Henabled; [exact Henabled|discriminate].
Qed.

(** The final IRQ transfer uses the actual post-decrement selector.  This
    obtains an enabled endpoint even though the earlier foreign prefix
    may contain interrupts, locks and transient current-task states. *)
Lemma os_sched_task_configured_irq_transfer_endpoint : forall environment sg handler entry transfer,
  os_int_exit_transfer_source (task_sw_hook_call_environment environment).(task_stack_call_external)
    environment.(task_stack_call_port) sg handler entry transfer ->
  sched_current_consistency (os_int_exit_installed_state transfer).(TskState)
    (os_int_exit_installed_state transfer).(SchedState) /\
  os_sched_selection_enabled (os_int_exit_installed_state transfer) = true /\
  (os_int_exit_installed_state transfer).(SchedState).(isRunning) = entry.(SchedState).(isRunning).
Proof.
  intros environment sg handler entry transfer
    [Hrequest [Hentry [Hexception [Hhook [Hdestination Hreturn]]]]].
  change (transfer.(os_int_exit_hooked_state) = os_int_exit_ready_checkpoint true entry) in Hhook.
  split; [eapply os_int_exit_destination_installs_current_consistency; exact Hdestination|].
  split.
  - unfold os_sched_selection_enabled.
    rewrite (proj2 (proj2 (proj2 (os_int_exit_installed_current_eq transfer)))), Hhook.
    change (os_sched_selection_enabled (os_int_exit_after_nesting entry) = true).
    unfold os_int_exit_requests_switch, os_sched_requests_switch in Hrequest.
    destruct (os_sched_selection_enabled (os_int_exit_after_nesting entry)) eqn:Henabled;
      [reflexivity|discriminate].
  - change (transfer.(os_int_exit_hooked_state).(SchedState).(isRunning) = entry.(SchedState).(isRunning)).
    rewrite Hhook; exact (proj2 (proj2 (os_int_exit_checkpoint_current_frame true entry))).
Qed.

(** Internal task entry, supplied by the real Block/Restore source.  It
    permits a nonready caller and mutable priority.  These are current
    observations, not promises about a future acquisition or return. *)
Definition os_sched_task_entry_observation call state : Prop :=
  kernel_call_task_source call state /\
    sched_current_consistency state.(TskState) state.(SchedState) /\
    os_sched_selection_enabled state = true.

Definition os_sched_task_call_pre environment local active sg call mask state : Assertion :=
  coq_prop (os_sched_task_entry_observation call state) &&
  os_sched_active_call_pre environment local active sg call mask state.

Lemma os_sched_task_call_pre_open : forall environment critical local active sg call mask state,
  kernel_sched_ready_clients critical ->
  os_sched_task_call_pre environment local active sg call mask state |--
  coq_prop (os_sched_task_entry_observation call state /\ os_sched_active_local_stable active) &&
  (os_sched_active_save_input environment critical local active sg call mask state ** unmap_table_rep sg).
Proof.
  intros environment critical local active sg call mask state Hclients heap [Hentry Hpre].
  destruct (os_sched_active_call_pre_open environment critical local active sg call mask state
    Hclients heap Hpre) as [Hstable Hsave].
  split; [split; assumption|exact Hsave].
Qed.

Definition os_sched_task_switch_pre environment critical local active sg call saved acquired entry : Assertion :=
  coq_prop (os_sched_task_entry_observation call entry) &&
  os_sched_active_switch_pre environment critical local active sg call saved acquired entry.

Definition os_sched_task_restore_input environment critical local active sg call saved acquired state : Assertion :=
  coq_prop (os_sched_task_current_ready call state) &&
  os_sched_active_restore_input environment critical local active sg call saved acquired state.

Definition os_sched_task_save_output environment critical local active sg original mask saved before
  before_heap : Assertion :=
  fun after_heap => exists returned acquired next_local,
    os_sched_task_save_observation environment critical sg original mask saved before returned acquired /\
    os_sched_active_save_input environment critical local active sg original mask before before_heap /\
    os_sched_active_restore_input environment critical next_local active sg returned saved acquired acquired after_heap.

Lemma os_sched_task_save_output_from_event : forall environment critical local active sg original mask saved before
  returned acquired next_local before_heap after_heap,
  os_sched_active_save_event environment critical local active sg original mask saved before
    returned acquired next_local before_heap after_heap ->
  (sched_current_consistency before.(TskState) before.(SchedState) ->
    sched_current_consistency acquired.(TskState) acquired.(SchedState)) ->
  kernel_call_normal_return original before returned acquired -> kernel_call_control_rely sg before acquired ->
  os_sched_task_save_output environment critical local active sg original mask saved before before_heap after_heap.
Proof.
  intros environment critical local active sg original mask saved before returned acquired next_local before_heap
    after_heap [Heffect [Hsame [Hsaved [Hsource [Hcut [Hpre Hpost]]]]]] Htrace Hnormal Hcontrol.
  exists returned, acquired, next_local; split; [|auto].
  exact (conj Heffect (conj Hsame (conj Hsaved (conj Hsource
    (conj Hcut (conj Htrace (conj Hnormal Hcontrol))))))).
Qed.

Lemma os_sched_task_uninterrupted_save_output : forall environment critical local active sg call mask saved state
  next_local before_heap after_heap,
  os_sched_active_save_event environment critical local active sg call mask saved state call state
    next_local before_heap after_heap ->
  os_sched_task_save_output environment critical local active sg call mask saved state before_heap after_heap.
Proof.
  intros; eapply os_sched_task_save_output_from_event; [exact H|auto|apply kernel_call_normal_return_refl|].
  split; reflexivity.
Qed.

(** The current consequence is computed from the concrete finite module
    source above.  Normal return and endpoint control remain observations
    of this same paired call; the specialized IRQ and install producers
    below construct them from the actual final selector/take. *)
Lemma os_sched_task_completed_save_output : forall environment critical local active sg original mask saved before
  returned acquired next_local before_heap after_heap,
  os_sched_active_save_event environment critical local active sg original mask saved before
    returned acquired next_local before_heap after_heap ->
  sched_task_completed_current_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) sg before acquired ->
  kernel_call_normal_return original before returned acquired -> kernel_call_control_rely sg before acquired ->
  os_sched_task_save_output environment critical local active sg original mask saved before before_heap after_heap.
Proof.
  intros; eapply os_sched_task_save_output_from_event; try eassumption.
  eapply sched_task_completed_source_preserves_current_consistency; eassumption.
Qed.

(** Interrupted Save returns after the last actual equal-priority IRQ
    selector and wrapper take.  The module source supplies only its real
    state effects; normal/control are derived at this same endpoint. *)
Lemma os_sched_task_irq_same_priority_save_output : forall environment critical local active sg
  original mask saved before returned entry next_local before_heap after_heap,
  let acquired := os_int_exit_wrapper_restored_state (os_int_exit_same_priority_state entry)
    original.(os_sched_call_stack) in
  os_sched_active_save_event environment critical local active sg original mask saved before
    returned acquired next_local before_heap after_heap ->
  os_sched_task_entry_observation original before ->
  sched_task_completed_current_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) sg before entry ->
  interrupt_exit_requests_schedule true entry.(IntrState) = true ->
  sched_selected_priority entry.(TskState) entry.(SchedState) =
    sched_priority_byte entry.(SchedState).(curSchedPrio) ->
  sched_task_running_source environment.(task_stack_call_external) sg before entry ->
  os_sched_task_save_output environment critical local active sg original mask saved before before_heap after_heap.
Proof.
  intros environment critical local active sg original mask saved before returned entry next_local before_heap after_heap
    acquired Hevent [Hinitial [Hcurrent Hinitial_enabled]] Hcompleted Henabled Hequal Hrunning.
  pose proof (proj1 (proj2 Hevent)) as Hsame.
  assert (Hfinal_current : sched_current_consistency before.(TskState) before.(SchedState) ->
    sched_current_consistency acquired.(TskState) acquired.(SchedState)).
  { intro Hconsistent; unfold acquired; apply os_int_exit_wrapper_take_preserves_current_consistency.
    rewrite (os_sched_task_irq_same_priority_state_eq entry Henabled Hequal).
    apply os_sched_prefix_preserves_current_consistency.
    change (sched_current_consistency entry.(TskState) entry.(SchedState)).
    eapply sched_task_completed_source_preserves_current_consistency; eassumption. }
  assert (Hnormal : kernel_call_normal_return original before returned acquired).
  { split; [exact Hsame|]. intro Havailable.
    unfold kernel_call_stack_available; rewrite (proj1 (proj2 Hsame)), (proj1 Hinitial).
    apply task_stack_take_lookup. }
  assert (Hcontrol : kernel_call_control_rely sg before acquired).
  { apply os_sched_enabled_endpoints_control_rely; [exact Hinitial_enabled| |].
    - unfold acquired; eapply os_sched_task_irq_same_priority_enabled; eassumption.
    - unfold acquired; rewrite (os_sched_task_irq_same_priority_state_eq entry Henabled Hequal).
      change ((os_sched_prefix_state (os_int_exit_after_nesting entry)).(SchedState).(isRunning) =
        before.(SchedState).(isRunning)).
      etransitivity.
      + exact (proj2 (proj2 (proj2 (os_sched_ready_checkpoint_frame (os_int_exit_after_nesting entry))))).
      + exact (sched_task_running_source_running_eq _ _ _ _ Hrunning). }
  eapply os_sched_task_save_output_from_event; eassumption.
Qed.

Lemma os_sched_task_save_output_open : forall environment critical local active sg original mask saved before before_heap,
  os_sched_task_save_output environment critical local active sg original mask saved before before_heap |--
  EX returned acquired next_local,
    coq_prop (os_sched_task_save_observation environment critical sg original mask saved before returned acquired) &&
    os_sched_active_restore_input environment critical next_local active sg returned saved acquired acquired.
Proof.
  intros environment critical local active sg original mask saved before before_heap heap
    [returned [acquired [next_local [Hsource [Hpre Hpost]]]]].
  exists returned, acquired, next_local; split; [exact Hsource|exact Hpost].
Qed.

Definition os_sched_task_body_post environment critical active sg call saved acquired entry : Assertion :=
  EX returned current next_local,
    coq_prop (os_sched_task_body_observation environment critical sg call entry returned current) &&
    (kernel_continuation_call_masked environment.(task_stack_call_continuations) kernel_program_fields_inv
      next_local critical sg (task_stack_call_active_key returned) returned saved acquired current **
      active returned current).

Definition os_sched_task_switch_output environment critical local active sg call saved acquired entry
  before_heap : Assertion :=
  fun after_heap =>
    os_sched_task_switch_pre environment critical local active sg call saved acquired entry before_heap /\
    os_sched_task_body_post environment critical active sg call saved acquired entry after_heap.

Lemma os_sched_task_switch_output_open : forall environment critical local active sg call saved acquired entry before_heap,
  os_sched_task_switch_output environment critical local active sg call saved acquired entry before_heap |--
  os_sched_task_body_post environment critical active sg call saved acquired entry.
Proof. intros; intros heap [_ Hpost]; exact Hpost. Qed.

(** The actual final install is appended as the registered C install
    client, and the port's actual TaskRestore supplies arch_resume.  Thus
    both the history and the spatial post use the selected descriptor and
    the same returned heap.  [receipt_to_active] is the concrete local
    resource interpretation, discharged by the caller's saved-local module;
    no arbitrary active assertion is declared stable across a switch. *)
Lemma os_sched_task_selected_switch_output : forall environment critical
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg entry first_installed initial_local active initial_heap context outgoing hooked original saved acquired
  receipt other resumed before,
  let abi := environment.(task_stack_call_continuations) in
  let local := kernel_sched_saved_local_resource_at environment.(task_stack_call_platform) critical sg
    hooked.(TskState) original saved acquired receipt other in
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  os_sched_task_switch_pre environment critical initial_local active sg original saved acquired entry initial_heap ->
  os_sched_switch_source environment.(task_stack_call_external) sg entry original first_installed ->
  kernel_client_trace critical.(critical_region_clients) sg original.(os_sched_call_invocation)
    first_installed false hooked ->
  critical.(critical_region_clients) (os_sched_install_client environment.(task_stack_call_external)
    context outgoing original.(os_sched_call_stack) resumed) ->
  context.(os_sched_call_invocation) <> original.(os_sched_call_invocation) ->
  kernel_client_stops environment.(task_stack_call_external).(os_sched_hook_action)
    original.(os_sched_call_invocation) = false ->
  kernel_call_control_rely sg entry hooked ->
  UCOS2_state_inv sg hooked -> sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding environment.(task_stack_call_external)
    context outgoing hooked original.(os_sched_call_stack) resumed ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (forall returned, task_tcb_init_stack_same_call returned original -> kernel_call_task_source returned current ->
    os_sched_task_current_ready returned current -> receipt |-- active returned current) ->
  (UCOS2_fields_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   resource (task_stack_key context.(os_sched_call_stack)) (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context ** unmap_table_rep sg)) before ->
  exists installed selected,
    sched_install_heap_fragment sg before installed (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    (forall restored, armv7a_task_restore_transition task_abi context selected installed restored ->
      os_sched_task_switch_output environment critical initial_local active sg original saved acquired entry
        initial_heap restored).
Proof.
  intros environment critical task_abi sg entry first_installed initial_local active initial_heap context outgoing hooked
    original saved acquired receipt other resumed before abi local resource current
    Hinitial Hfirst Hforeign_trace Hregistered Hforeign Hhook Hcontrol Hvalid Hhigh Hsaved Hdestination
    Haddress Hcoverage Hreceipt Hpre.
  assert (Hframed : (UCOS2_fields_inv sg hooked **
    task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
    resource (task_stack_key context.(os_sched_call_stack)) (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
    store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
    (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** emp)) before).
  { match type of Hpre with ?P before => match goal with |- ?Q before =>
      assert (Hframe : P |-- Q) by entailer! end end; exact (Hframe before Hpre). }
  destruct (os_sched_task_selected_masked_return_source environment critical task_abi sg context outgoing hooked
    original saved acquired receipt other resumed before emp Hvalid Hhigh Hsaved Hdestination Haddress Hcoverage Hframed)
    as [installed [selected [Hinstall [Hreads [Hlease Hrestore]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  intros restored Hactual.
  destruct (Hrestore restored Hactual) as [Hcall [Hsame [Hsource [Hready [Hnormal [Hcontrols [Hresume Howned]]]]]]].
  set (returned := kernel_selected_call selected current) in *.
  assert (Hlast : kernel_client_trace critical.(critical_region_clients) sg original.(os_sched_call_invocation)
      hooked false current).
  { eapply os_sched_install_client_registered_trace; [exact Hregistered|exact Hforeign|].
    exact (conj Hsaved (conj Hdestination (conj Hhigh eq_refl))). }
  assert (Hbody : os_sched_task_body_observation environment critical sg original entry returned current).
  { unfold returned, current; eapply os_sched_task_selected_body_from_source; try eassumption.
    apply OsSchedTaskReturnPrefixClients; exact Hforeign_trace. }
  split; [exact Hinitial|].
  exists returned, current, other; split; [exact Hbody|].
  match type of Howned with ?P restored => match goal with |- ?Q restored => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic (Hreceipt returned Hsame Hsource
      (os_sched_task_ready_source_current_ready environment sg returned current Hready)); entailer!. }
  exact (Hclose restored Howned).
Qed.

(** IRQ selection is a distinct final return path of OSCtxSw.  The
    history retains the actual OSIntExit transfer and restore transition;
    it does not manufacture the task ABI's opaque resume observation.
    The handler-stack resource returned by that ABI is passed to the
    concrete caller resource interpretation, on this same returned heap. *)
Lemma os_sched_task_irq_selected_switch_output : forall environment critical
  sg entry first_installed initial_local active initial_heap handler irq_entry transfer
  original saved acquired receipt other before,
  let abi := environment.(task_stack_call_continuations) in
  let hooked := transfer.(os_int_exit_hooked_state) in
  let local := kernel_sched_saved_local_resource_at environment.(task_stack_call_platform) critical sg
    hooked.(TskState) original saved acquired receipt other in
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  let current := os_int_exit_installed_state transfer in
  os_sched_task_switch_pre environment critical initial_local active sg original saved acquired entry initial_heap ->
  os_sched_switch_source environment.(task_stack_call_external) sg entry original first_installed ->
  kernel_client_trace critical.(critical_region_clients) sg original.(os_sched_call_invocation)
    first_installed false irq_entry ->
  kernel_client_stops environment.(task_stack_call_external).(os_sched_hook_action)
    original.(os_sched_call_invocation) = false ->
  os_int_exit_transfer_source environment.(task_stack_call_external) environment.(task_stack_call_port)
    sg handler irq_entry transfer ->
  kernel_call_control_rely sg entry hooked ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  transfer.(os_int_exit_incoming_stack) = original.(os_sched_call_stack) ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) None ->
  (forall returned, task_tcb_init_stack_same_call returned original -> kernel_call_task_source returned current ->
    os_sched_task_current_ready returned current ->
    receipt ** task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments)
      |-- active returned current) ->
  (UCOS2_fields_inv sg hooked ** store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
   (interrupt_platform_running environment.(task_stack_call_platform)
      handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources environment.(task_stack_call_port) handler ** unmap_table_rep sg ** emp)) before ->
  exists installed selected,
    sched_install_heap_fragment sg before installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    (forall irq_return, armv7a_restore_transition abi handler selected installed irq_return ->
      os_sched_task_switch_output environment critical initial_local active sg original saved acquired entry
        initial_heap irq_return).
Proof.
  intros environment critical sg entry first_installed initial_local active initial_heap handler irq_entry transfer
    original saved acquired receipt other before abi hooked local resource current
    Hinitial Hfirst Htrace Hhook Htransfer Hcontrol Hhigh Hincoming Haddress Hcoverage Hreceipt Hpre.
  destruct (os_sched_task_irq_selected_masked_return_source environment critical sg handler irq_entry transfer
    original saved acquired receipt other before emp Htransfer Hhigh Hincoming Haddress Hcoverage Hpre)
    as [installed [selected [Hlease [Hsp [Hfragments [Hcall [Hpc [Hmask
      [Hinstall [Hpointers [Hreads Hrestore]]]]]]]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  intros irq_return Hactual.
  destruct (Hrestore irq_return Hactual) as [Hmemory [Hsame [Hsource [Hready [Hcurrent_ready
    [Hnormal [Hcontrols Howned]]]]]]].
  set (returned := armv7a_continuation_resumed_call selected original) in *.
  assert (Hbody : os_sched_task_body_observation environment critical sg original entry returned current).
  { split.
    - unfold returned, current; eapply OsSchedTaskBodyIRQLastInstall; try eassumption.
      left; exact Htrace.
    - split; [exact Hcurrent_ready|]. split.
      + split; [exact Hsame|]. intro Havailable.
        unfold kernel_call_stack_available; rewrite (proj1 Hsource).
        change (task_stack_take hooked.(TskState).(parkedTaskStacks) transfer.(os_int_exit_incoming_stack)
          (task_stack_key returned.(os_sched_call_stack)) = None).
        assert (Hstack : returned.(os_sched_call_stack) = transfer.(os_int_exit_incoming_stack)).
        { unfold returned; cbn; congruence. }
        rewrite Hstack; apply task_stack_take_lookup.
      + split.
        * eapply kernel_call_control_rely_trans; eassumption.
        * intros; exact Hsource. }
  split; [exact Hinitial|]. exists returned, current, other; split; [exact Hbody|].
  match type of Howned with ?P irq_return => match goal with |- ?Q irq_return => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic (Hreceipt returned Hsame Hsource Hcurrent_ready); entailer!. }
  exact (Hclose irq_return Howned).
Qed.

(** The fixed hook implementation is selected by construction.  This
    consumes its checked identity step at the actual SP-save cut and its
    no-retirement result; neither becomes a dynamic Pend precondition. *)
Lemma os_sched_task_configured_first_switch_source : forall environment sg entry original
  first_sp first_outgoing first_incoming first_resumed,
  let configured := task_sw_hook_call_environment environment in
  let first_updated := os_sched_save_current_sp (os_sched_prefix_state entry)
    original.(os_sched_call_stack).(stackLeaseSlot) first_sp in
  let first_installed := os_sched_install_context original first_outgoing first_incoming first_updated in
  os_sched_requests_switch entry = true ->
  environment.(task_stack_call_external).(os_sched_arch_save_source) original first_sp first_outgoing ->
  os_sched_destination_binding configured.(task_stack_call_external)
    original first_outgoing first_updated first_incoming first_resumed ->
  os_sched_switch_source configured.(task_stack_call_external) sg entry original first_installed.
Proof.
  intros; eapply task_sw_hook_call_environment_switch_source; eassumption.
Qed.

Definition os_sched_task_configured_selected_masked_return_source environment critical
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations)) :=
  os_sched_task_selected_masked_return_source (task_sw_hook_call_environment environment) critical
    (task_sw_hook_task_context_abi environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations) task_abi).

Lemma os_sched_task_body_restore_input : forall environment critical active sg call saved acquired entry,
  os_sched_task_body_post environment critical active sg call saved acquired entry |--
  EX returned current next_local,
    coq_prop (os_sched_task_body_observation environment critical sg call entry returned current /\
      UCOS2_state_inv sg current) &&
    (os_sched_task_restore_input environment critical next_local active sg returned saved acquired current **
      unmap_table_rep sg).
Proof.
  intros environment critical active sg call saved acquired entry heap
    [returned [current [next_local [Hbody Howned]]]].
  change (os_sched_task_body_observation environment critical sg call entry returned current) in Hbody.
  assert (Hopen :
    (kernel_continuation_call_masked environment.(task_stack_call_continuations)
      kernel_program_fields_inv next_local critical sg (task_stack_call_active_key returned)
      returned saved acquired current ** active returned current) |--
    coq_prop (UCOS2_state_inv sg current) &&
    ((os_sched_fields_restore_input environment critical next_local sg returned saved acquired current **
      active returned current) ** unmap_table_rep sg)).
  { sep_apply_l_atomic (proj2 (os_sched_fields_restore_input_masked_world
      environment critical next_local sg returned saved acquired current)).
    unfold os_sched_fields_restore_input, UCOS2_fields_inv; entailer!.
    all: match goal with |- ?P |-- coq_prop _ && ?Q =>
      assert (Hspatial_reorder : P |-- Q) by entailer!;
      intros actual Hresources;
      split; [exact H0|exact (Hspatial_reorder actual Hresources)]
    end.
  }
  destruct (Hopen heap Howned) as [Hvalid [body_heap [unmap_heap [Hjoin [Hresources Hunmap]]]]].
  exists returned, current, next_local; split; [exact (conj Hbody Hvalid)|].
  exists body_heap, unmap_heap; split; [exact Hjoin|].
  split; [split; [exact (proj1 (proj2 Hbody))|exact Hresources]|exact Hunmap].
Qed.

Definition os_sched_task_restore_output environment critical local active sg original saved acquired released
  before_heap : Assertion :=
  fun after_heap => exists returned current next_local,
    os_sched_task_restore_observation environment critical sg original released returned current /\
    os_sched_task_restore_input environment critical local active sg original saved acquired released before_heap /\
    (os_sched_fields_save_input environment critical next_local sg returned (armv7a_irq_fiq_mask saved) current **
      active returned current) after_heap.

Lemma os_sched_task_restore_output_from_event : forall environment critical local active sg original saved acquired released
  returned current next_local before_heap after_heap,
  os_sched_active_restore_event environment critical local active sg original saved acquired released
    returned current next_local before_heap after_heap ->
  os_sched_task_ready_source environment sg original released ->
  os_sched_task_ready_source environment sg returned current ->
  kernel_call_normal_return original released returned current -> kernel_call_control_rely sg released current ->
  os_sched_task_restore_output environment critical local active sg original saved acquired released before_heap after_heap.
Proof.
  intros environment critical local active sg original saved acquired released returned current next_local before_heap
    after_heap [Heffect [Hsame [Hpreserved [Hsource [Hpre Hpost]]]]] Hinitial Hready Hnormal Hcontrol.
  apply (os_sched_task_ready_source_current_ready environment sg) in Hinitial, Hready.
  exists returned, current, next_local; split.
  - exact (conj Heffect (conj Hsame (conj Hpreserved
      (conj Hsource (conj Hready (conj Hnormal Hcontrol)))))).
  - split; [split; assumption|exact Hpost].
Qed.

Lemma os_sched_task_uninterrupted_restore_output : forall environment critical local active sg call saved acquired state
  next_local before_heap after_heap,
  os_sched_active_restore_event environment critical local active sg call saved acquired state call state
    next_local before_heap after_heap ->
  os_sched_task_ready_source environment sg call state ->
  os_sched_task_restore_output environment critical local active sg call saved acquired state before_heap after_heap.
Proof.
  intros; eapply os_sched_task_restore_output_from_event; try eassumption.
  - apply kernel_call_normal_return_refl.
  - split; reflexivity.
Qed.

(** The wrapper's ordinary task return is after the real OSIntExit counter
    and equal-priority selector.  Suspend, wake and ChangePrio are allowed
    in the completed source before that selector.  Readiness is computed
    from its actual guard/current byte; it is not transported across those
    clients.  Running is the exact field frame of those C module posts. *)
Lemma os_sched_task_irq_same_priority_restore_output : forall environment critical local active sg
  original saved acquired released returned entry next_local before_heap after_heap,
  let current := os_int_exit_wrapper_restored_state (os_int_exit_same_priority_state entry)
    original.(os_sched_call_stack) in
  os_sched_active_restore_event environment critical local active sg original saved acquired released
    returned current next_local before_heap after_heap ->
  os_sched_task_ready_source environment sg original released ->
  sched_task_completed_current_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) sg released entry ->
  UCOS2_state_inv sg entry -> kernel_call_task_source original entry ->
  os_sched_selection_enabled released = true ->
  interrupt_exit_requests_schedule true entry.(IntrState) = true ->
  sched_selected_priority entry.(TskState) entry.(SchedState) =
    sched_priority_byte entry.(SchedState).(curSchedPrio) ->
  entry.(SchedState).(readyList) <> [] ->
  sched_task_running_source environment.(task_stack_call_external) sg released entry ->
  os_sched_task_restore_output environment critical local active sg original saved acquired released
    before_heap after_heap.
Proof.
  intros environment critical local active sg original saved acquired released returned entry next_local before_heap
    after_heap current Hevent Hinitial Hcompleted Hvalid Hentry_source Hreleased_enabled Henabled Hequal Hnonempty Hrunning.
  destruct Hevent as [Heffect [Hsame [Hpreserved [Hsource [Hpre Hpost]]]]].
  assert (Hentry_current : sched_current_consistency entry.(TskState) entry.(SchedState)).
  { eapply sched_task_completed_source_preserves_current_consistency; [exact Hcompleted|].
    eapply os_sched_task_ready_source_current_consistency; exact Hinitial. }
  assert (Hreturned_source : kernel_call_task_source returned entry).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff returned original entry Hsame)); exact Hentry_source. }
  assert (Hready : os_sched_task_ready_source environment sg returned current).
  { unfold current; eapply os_sched_task_irq_same_priority_ready_source; eassumption. }
  assert (Hnormal : kernel_call_normal_return original released returned current).
  { split; [exact Hsame|]. intro Havailable.
    unfold kernel_call_stack_available; rewrite (proj1 Hreturned_source), (proj2 (proj2 Hsame)).
    apply task_stack_take_lookup. }
  assert (Hcontrol : kernel_call_control_rely sg released current).
  { apply os_sched_enabled_endpoints_control_rely; [exact Hreleased_enabled| |].
    - unfold current; eapply os_sched_task_irq_same_priority_enabled; eassumption.
    - exact (sched_task_running_source_running_eq _ _ _ _ Hrunning). }
  eapply os_sched_task_restore_output_from_event; [|exact Hinitial|exact Hready|exact Hnormal|exact Hcontrol].
  exact (conj Heffect (conj Hsame (conj Hpreserved (conj Hsource (conj Hpre Hpost))))).
Qed.

Lemma os_sched_task_restore_output_open : forall environment critical local active sg original saved acquired released before_heap,
  os_sched_task_restore_output environment critical local active sg original saved acquired released before_heap |--
  EX returned current next_local,
    coq_prop (os_sched_task_restore_observation environment critical sg original released returned current) &&
    (os_sched_fields_save_input environment critical next_local sg returned (armv7a_irq_fiq_mask saved) current **
      active returned current).
Proof.
  intros environment critical local active sg original saved acquired released before_heap heap
    [returned [current [next_local [Hsource [Hpre Hpost]]]]].
  exists returned, current, next_local; split; [exact Hsource|exact Hpost].
Qed.

Lemma os_sched_task_restore_output_return : forall environment critical local active sg original scheduled resumed
  mask saved before entry released before_heap,
  os_sched_task_save_observation environment critical sg original mask saved before scheduled entry ->
  os_sched_task_body_observation environment critical sg scheduled entry resumed released ->
  UCOS2_state_inv sg released ->
  os_sched_task_restore_output environment critical local active sg resumed saved entry released before_heap **
    unmap_table_rep sg |--
  os_sched_task_history_return_post environment critical active sg original mask before.
Proof.
  intros environment critical local active sg original scheduled resumed mask saved before entry released before_heap
    Hsave Hbody Hvalid heap [restore_heap [unmap_heap [Hjoin [Hrestore_output Hunmap]]]].
  destruct Hrestore_output as [returned [current [next_local [Hrestore [Hpre Hpost]]]]].
  pose proof (os_sched_task_observations_compose environment critical sg original scheduled resumed returned
    mask saved before entry released current Hsave Hbody Hrestore Hvalid) as Hobservations.
  assert (Hmask : armv7a_irq_fiq_mask saved = mask).
  { destruct Hsave as [_ [_ [Hsaved _]]]; exact (proj2 Hsaved). }
  assert (Hframed : ((os_sched_fields_save_input environment critical next_local sg returned
    (armv7a_irq_fiq_mask saved) current ** active returned current) ** unmap_table_rep sg) heap).
  { exists restore_heap, unmap_heap; exact (conj Hjoin (conj Hpost Hunmap)). }
  assert (Hreorder :
    (os_sched_fields_save_input environment critical next_local sg returned
      (armv7a_irq_fiq_mask saved) current ** active returned current) ** unmap_table_rep sg |--
    (os_sched_fields_save_input environment critical next_local sg returned
      (armv7a_irq_fiq_mask saved) current ** unmap_table_rep sg) ** active returned current) by entailer!.
  destruct (Hreorder heap Hframed) as [world_heap [active_heap [Hworld_join [Hworld Hactive]]]].
  pose proof (proj1 (os_sched_fields_save_input_closed_world environment critical next_local sg returned
    (armv7a_irq_fiq_mask saved) current) world_heap Hworld) as Hclosed.
  rewrite Hmask in Hclosed.
  exists returned, current, next_local; split; [exact Hobservations|].
  exists world_heap, active_heap; exact (conj Hworld_join (conj Hclosed Hactive)).
Qed.

(** Pure projection of the approved C return relation.  The Task source
    aligns the original invocation origin with its existing stack key.
    No readiness, cache, control or new platform observation is added. *)
Lemma os_sched_c_return_normal_return :
  forall external critical sg entry original returned current,
  kernel_call_task_source original entry ->
  os_sched_c_return external critical sg entry original returned current ->
  kernel_call_normal_return original entry returned current.
Proof.
  intros external critical sg entry original returned current Htask Hreturn.
  pose proof (os_sched_c_return_execution_identity external critical sg entry
    original returned current Hreturn) as Hsame.
  unfold kernel_call_normal_return; split; [exact Hsame|].
  intro Havailable.
  destruct (os_sched_requests_switch entry) eqn:Hswitch.
  - unfold os_sched_c_return in Hreturn; rewrite Hswitch in Hreturn.
    destruct Hreturn as [installed [Hfirst [Htrace [Harch
      [Hi [Ho [Hs [Hactive [Hcurrent Hparked]]]]]]]]].
    destruct Htask as [Horigin Hsource].
    unfold kernel_call_stack_available.
    rewrite Ho, Horigin.
    exact Hparked.
  - unfold os_sched_c_return in Hreturn; rewrite Hswitch in Hreturn.
    destruct Hreturn as [Hreturned Hcurrent].
    subst returned current.
    change (kernel_call_stack_available original entry).
    exact Havailable.
Qed.


(** Consume one already returned C-call tuple and its original active
    resource, instead of reconstructing a physical receipt.  The new C
    source, ready and control observations are separate actual endpoint
    premises; this lemma does not manufacture them from [c_return]. *)
Lemma os_sched_task_switch_output_from_c_return : forall environment critical local active sg
  original saved acquired entry initial_heap returned current next_local returned_heap,
  os_sched_task_switch_pre environment critical local active sg original saved acquired entry initial_heap ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry original returned current ->
  os_sched_task_body_source environment critical sg entry original returned current ->
  os_sched_task_ready_source environment sg returned current ->
  kernel_call_control_rely sg entry current ->
  (kernel_continuation_call_masked environment.(task_stack_call_continuations)
    kernel_program_fields_inv next_local critical sg (task_stack_call_active_key returned)
    returned saved acquired current ** active returned current) returned_heap ->
  os_sched_task_switch_output environment critical local active sg original saved acquired entry
    initial_heap returned_heap.
Proof.
  intros environment critical local active sg original saved acquired entry initial_heap
    returned current next_local returned_heap Hinitial Hreturn Hbody Hready Hcontrol Howned.
  apply (os_sched_task_ready_source_current_ready environment sg) in Hready.
  pose proof Hinitial as [Hentry [world_heap [active_heap [Hjoin [Hswitch Hactive]]]]].
  destruct Hswitch as [[Hrequest [Hstorage Hparked]] Hmasked].
  change (os_sched_task_entry_observation original entry) in Hentry.
  pose proof (os_sched_c_return_normal_return environment.(task_stack_call_external)
    critical sg entry original returned current (proj1 Hentry) Hreturn) as Hnormal.
  assert (Hsource : kernel_call_task_source returned current).
  { eapply os_sched_continuation_c_return_source; [intros; exact Hstorage|exact Hreturn|exact (proj1 Hentry)]. }
  split; [exact Hinitial|].
  exists returned, current, next_local; split; [|exact Howned].
  exact (conj Hbody (conj Hready (conj Hnormal (conj Hcontrol (fun _ => Hsource))))).
Qed.

(** The ready fact is produced from this returned world's validity and the
    actual last C source.  The old return relation contributes only its
    existing identity/source observation; it is not used to invent the last
    source or the completed-call C control relation. *)
Lemma os_sched_task_switch_output_from_c_return_source : forall environment critical local active sg
  original saved acquired entry initial_heap returned current next_local returned_heap,
  let configured := task_sw_hook_call_environment environment in
  os_sched_task_switch_pre configured critical local active sg original saved acquired entry initial_heap ->
  os_sched_c_return configured.(task_stack_call_external) critical sg entry original returned current ->
  os_sched_task_body_source configured critical sg entry original returned current ->
  kernel_call_control_rely sg entry current ->
  (kernel_continuation_call_masked configured.(task_stack_call_continuations)
    kernel_program_fields_inv next_local critical sg (task_stack_call_active_key returned)
    returned saved acquired current ** active returned current) returned_heap ->
  os_sched_task_switch_output configured critical local active sg original saved acquired entry
    initial_heap returned_heap.
Proof.
  intros environment critical local active sg original saved acquired entry initial_heap
    returned current next_local returned_heap configured Hinitial Hreturn Hbody Hcontrol Howned.
  pose proof Hinitial as [Hentry [world_heap [active_heap [Hjoin [Hswitch Hactive]]]]].
  destruct Hswitch as [[Hrequest [Hstorage Hparked]] Hmasked].
  change (os_sched_task_entry_observation original entry) in Hentry.
  assert (Hvalid : UCOS2_state_inv sg current).
  { match type of Howned with ?P returned_heap =>
      assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg current) && TT) end.
    { unfold kernel_continuation_call_masked, kernel_continuation_inv,
        kernel_program_fields_inv, UCOS2_fields_inv; entailer!; intros ? ?; first [assumption | exact I]. }
    exact (proj1 (Hobserve returned_heap Howned)). }
  assert (Hready : os_sched_task_current_ready returned current).
  { eapply os_sched_task_switch_source_current_ready; eassumption. }
  pose proof (os_sched_c_return_normal_return configured.(task_stack_call_external)
    critical sg entry original returned current (proj1 Hentry) Hreturn) as Hnormal.
  assert (Hsource : kernel_call_task_source returned current).
  { eapply os_sched_continuation_c_return_source; [intros; exact Hstorage|exact Hreturn|exact (proj1 Hentry)]. }
  split; [exact Hinitial|].
  exists returned, current, next_local; split; [|exact Howned].
  exact (conj Hbody (conj Hready (conj Hnormal (conj Hcontrol (fun _ => Hsource))))).
Qed.

(** Final Restore consumes the actual same-call endpoint facts.  Current
    readiness is the logical C observation transported by that existing
    endpoint protocol; a fresh last-selector source tag is unnecessary. *)
Lemma os_sched_task_restore_output_from_current_ready : forall environment critical local active sg
  original saved acquired released returned current next_local before_heap after_heap,
  os_sched_active_restore_event environment critical local active sg original saved acquired released
    returned current next_local before_heap after_heap ->
  os_sched_task_current_ready original released ->
  os_sched_task_current_ready returned current ->
  kernel_call_normal_return original released returned current ->
  kernel_call_control_rely sg released current ->
  os_sched_task_restore_output environment critical local active sg original saved acquired released
    before_heap after_heap.
Proof.
  intros environment critical local active sg original saved acquired released returned current next_local
    before_heap after_heap [Heffect [Hsame [Hpreserved [Hsource [Hpre Hpost]]]]]
    Hinitial Hready Hnormal Hcontrol.
  exists returned, current, next_local; split.
  - exact (conj Heffect (conj Hsame (conj Hpreserved
      (conj Hsource (conj Hready (conj Hnormal Hcontrol)))))).
  - split; [split; assumption|exact Hpost].
Qed.

(** C-facing switch source output.  The normal/source observations and
    returned world belong to this one completed call.  Readiness and cache
    consistency are deliberately absent: the consumer derives them from
    the actual last C source and that returned world.  This definition is
    not a law declaring arbitrary old calls to have a last source. *)
Definition os_sched_task_switch_source_output environment critical local active sg
  original saved acquired entry initial_heap : Assertion :=
  fun returned_heap => os_sched_task_switch_pre environment critical local active sg original saved acquired entry initial_heap /\
    exists returned current next_local,
      (os_sched_task_body_source environment critical sg entry original returned current /\
       kernel_call_normal_return original entry returned current /\ kernel_call_control_rely sg entry current /\
       (kernel_call_task_source original entry -> kernel_call_task_source returned current)) /\
      (kernel_continuation_call_masked environment.(task_stack_call_continuations) kernel_program_fields_inv
        next_local critical sg (task_stack_call_active_key returned) returned saved acquired current **
        active returned current) returned_heap.

(** Both already proved selected-return producers use the same source,
    descriptor and returned heap.  Their outputs inhabit this smaller C
    declaration directly; no assertion is transported or reconstructed. *)
Lemma os_sched_task_switch_output_source :
  forall environment critical local active sg original saved acquired entry initial_heap,
  os_sched_task_switch_output environment critical local active sg original saved acquired entry initial_heap |--
  os_sched_task_switch_source_output environment critical local active sg original saved acquired entry initial_heap.
Proof.
  intros environment critical local active sg original saved acquired entry initial_heap heap
    [Hinitial [returned [current [next_local [[Hbody [Hready Hrest]] Howned]]]]].
  split; [exact Hinitial|]. exists returned, current, next_local; split; [exact (conj Hbody Hrest)|exact Howned].
Qed.

(** Actual full C source of the LAST scheduler invocation.  Its input cut
    is before its own selector, so a TaskDel/Mutex resource prefix does not
    have to pretend it already contains the later SP-save or hook steps.
    The old call output contributes identity/source/ownership only; the
    first installed state remains separate from the final current state. *)
Lemma os_sched_task_last_call_source_output : forall environment critical local active sg
  original saved acquired entry initial_heap first_installed last_entry last_context
  last_entry_heap returned current next_local returned_heap,
  os_sched_task_switch_pre environment critical local active sg original saved acquired entry initial_heap ->
  os_sched_switch_source environment.(task_stack_call_external) sg entry original first_installed ->
  os_sched_task_return_prefix environment critical sg original.(os_sched_call_invocation)
    first_installed last_entry last_entry_heap ->
  UCOS2_state_inv sg last_entry ->
  os_sched_switch_source environment.(task_stack_call_external) sg last_entry last_context current ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry original returned current ->
  kernel_call_control_rely sg entry current ->
  (kernel_continuation_call_masked environment.(task_stack_call_continuations)
    kernel_program_fields_inv next_local critical sg (task_stack_call_active_key returned)
    returned saved acquired current ** active returned current) returned_heap ->
  os_sched_task_switch_source_output environment critical local active sg original saved acquired entry
    initial_heap returned_heap.
Proof.
  intros environment critical local active sg original saved acquired entry initial_heap first_installed
    last_entry last_context last_entry_heap returned current next_local returned_heap
    Hinitial Hfirst Hprefix Hlast_valid Hlast Hreturn Hcontrol Howned.
  pose proof Hinitial as [Hentry [world_heap [active_heap [Hjoin [Hswitch Hactive]]]]].
  destruct Hswitch as [[Hrequest [Hstorage Hparked]] Hmasked].
  change (os_sched_task_entry_observation original entry) in Hentry.
  pose proof (os_sched_c_return_execution_identity environment.(task_stack_call_external)
    critical sg entry original returned current Hreturn) as Hsame.
  assert (Hnormal : kernel_call_normal_return original entry returned current).
  { split; [exact Hsame|]. intro Havailable.
    pose proof Hreturn as Hreturned.
    unfold os_sched_c_return in Hreturned; rewrite Hrequest in Hreturned.
    destruct Hreturned as [installed [Hfirst' [Htrace [Harch
      [Hi [Ho [Hs [Hactive' [Hcurrent Hparked']]]]]]]]].
    destruct (proj1 Hentry) as [Horigin Hsource].
    unfold kernel_call_stack_available; rewrite Ho, Horigin; exact Hparked'. }
  assert (Htask : kernel_call_task_source returned current).
  { eapply os_sched_continuation_c_return_source; [intros; exact Hstorage|exact Hreturn|exact (proj1 Hentry)]. }
  split; [exact Hinitial|]. exists returned, current, next_local; split; [|exact Howned].
  split.
  - eapply OsSchedTaskBodyTaskLastCall; try eassumption.
  - exact (conj Hnormal (conj Hcontrol (fun _ => Htask))).
Qed.

(** Same-event C consumer.  The heap is not projected away before reading
    its current invariant.  The actual C source then supplies ready, while
    all other endpoint observations and resources are retained verbatim. *)
Lemma os_sched_task_switch_source_output_observation :
  forall environment critical local active sg original saved acquired entry initial_heap,
  let configured := task_sw_hook_call_environment environment in
  os_sched_task_switch_source_output configured critical local active sg original saved acquired entry initial_heap |--
  os_sched_task_switch_output configured critical local active sg original saved acquired entry initial_heap.
Proof.
  intros environment critical local active sg original saved acquired entry initial_heap configured heap
    [Hinitial [returned [current [next_local [[Hbody [Hnormal [Hcontrol Htask]]] Howned]]]]].
  pose proof Hinitial as [Hentry [world_heap [active_heap [Hjoin [Hswitch Hactive]]]]].
  destruct Hswitch as [[Hrequest [Hstorage Hparked]] Hmasked].
  assert (Hvalid : UCOS2_state_inv sg current).
  { match type of Howned with ?P heap => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg current) && TT) end.
    { unfold kernel_continuation_call_masked, kernel_continuation_inv,
        kernel_program_fields_inv, UCOS2_fields_inv; entailer!; intros ? ?; first [assumption | exact I]. }
    exact (proj1 (Hobserve heap Howned)). }
  assert (Hready : os_sched_task_current_ready returned current).
  { eapply SchedulerPhaseCandidate.os_sched_task_switch_source_current_ready; eassumption. }
  split; [exact Hinitial|]. exists returned, current, next_local; split; [|exact Howned].
  exact (conj Hbody (conj Hready (conj Hnormal (conj Hcontrol Htask)))).
Qed.

Lemma os_sched_task_body_post_safeexec :
  forall environment critical active sg original saved acquired entry
    (X : OsSchedCallContext -> UCOS2_Verify_State -> Prop),
  safeExec (fun state => state = entry) (os_sched_task_body_program environment critical sg original) X ->
  os_sched_task_body_post environment critical active sg original saved acquired entry |--
  EX returned current next_local,
    coq_prop (os_sched_task_body_observation environment critical sg original entry returned current /\
      safeExec (fun state => state = current) (StateRelMonad.ret returned) X) &&
    (kernel_continuation_call_masked environment.(task_stack_call_continuations) kernel_program_fields_inv
      next_local critical sg (task_stack_call_active_key returned) returned saved acquired current **
      active returned current).
Proof.
  intros environment critical active sg original saved acquired entry X Hsafe heap
    [returned [current [next_local [Hobservations Howned]]]].
  exists returned, current, next_local; split; [split; [exact Hobservations|]|exact Howned].
  eapply os_sched_task_body_return_safeexec; [exact (proj1 Hobservations)|exact Hsafe].
Qed.

Lemma task_selected_c_prefix_switch_output :
  forall environment critical
    (task_abi : Armv7aTaskContextABI (task_sw_hook_call_environment environment).(task_stack_call_external)
      (task_sw_hook_call_environment environment).(task_stack_call_platform)
      (task_sw_hook_call_environment environment).(task_stack_call_port)
      (task_sw_hook_call_environment environment).(task_stack_call_continuations))
    sg entry first_installed initial_local active initial_heap last_entry context saved_sp outgoing hooked resumed
    original saved acquired receipt other frame first_heap input stopped before_heap output installed sp actual,
  let configured := task_sw_hook_call_environment environment in
  let call := {| InstallComponent.task_install_fields_context := context;
                 InstallComponent.task_install_fields_outgoing := outgoing;
                 InstallComponent.task_install_fields_incoming := original.(os_sched_call_stack);
                 InstallComponent.task_install_fields_resumed := resumed;
                 InstallComponent.task_install_fields_entry := hooked |} in
  let local := kernel_sched_saved_local_resource_at configured.(task_stack_call_platform) critical sg
    hooked.(TskState) original saved acquired receipt other in
  let rest := armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame in
  forall (prefix : kernel_c_sequence (kernel_program_selected_c_step configured critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      first_installed first_heap input stopped hooked before_heap output)
    (complete : InstallComponent.task_install_c_segment configured local sg rest call before_heap installed sp actual),
  os_sched_task_switch_pre configured critical initial_local active sg original saved acquired entry initial_heap ->
  os_sched_switch_source configured.(task_stack_call_external) sg entry original first_installed ->
  os_sched_requests_switch last_entry = true ->
  configured.(task_stack_call_external).(os_sched_arch_save_source) context saved_sp outgoing ->
  kernel_client_step configured.(task_stack_call_external).(os_sched_hook_action) sg
    (os_sched_save_current_sp (os_sched_prefix_state last_entry) context.(os_sched_call_stack).(stackLeaseSlot) saved_sp) hooked ->
  os_sched_destination_binding configured.(task_stack_call_external)
    context outgoing hooked original.(os_sched_call_stack) resumed ->
  kernel_program_selected_c_sequence_source configured critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix ->
  output |-- InstallComponent.task_install_fields_entry_owner configured local sg call ** rest ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (forall returned, task_tcb_init_stack_same_call returned original ->
    kernel_call_task_source returned (InstallComponent.task_install_fields_current call) ->
    os_sched_task_current_ready returned (InstallComponent.task_install_fields_current call) ->
    receipt ** frame |-- active returned (InstallComponent.task_install_fields_current call)) ->
  exists selected, forall restored,
  armv7a_task_restore_transition task_abi context selected installed restored ->
  let current := InstallComponent.task_install_fields_current call in
  let returned := kernel_selected_call selected current in
  exists (run : kernel_c_sequence (kernel_program_selected_c_step configured critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)) first_installed first_heap input
    (orb stopped false) current restored (os_sched_task_body_post configured critical active sg original saved acquired entry)),
  kernel_program_selected_c_sequence_source configured critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ run /\
  os_sched_task_switch_output configured critical initial_local active sg original saved acquired entry initial_heap restored /\
  (forall X, safeExec (fun state => state = entry) (os_sched_task_body_program configured critical sg original) X ->
    safeExec (fun state => state = current) (StateRelMonad.ret returned) X).
Proof.
  intros environment critical task_abi sg entry first_installed initial_local active initial_heap last_entry context saved_sp
    outgoing hooked resumed original saved acquired receipt other frame first_heap input stopped before_heap output installed sp actual
    configured call local rest prefix complete Hinitial Hfirst Hswitch Hsave Hhook Hdestination Hprefix Hbridge Hcoverage Hreceipt.
  destruct (SelectedCompletionComposition.task_selected_completion_environment_sequence configured critical task_abi sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None frame call original saved acquired receipt other
    before_heap installed sp actual complete eq_refl Hcoverage) as [selected Hterminal].
  exists selected; intros restored Hrestore current returned.
  destruct (Hterminal restored Hrestore) as [last [Hlast [Htask Hsame]]].
  change (kernel_call_task_source returned current) in Htask.
  change (task_tcb_init_stack_same_call returned original) in Hsame.
  destruct (kernel_program_selected_c_sequence_resources configured critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ last)
    as [Hlast_input [Hendpoint Howned]].
  pose proof (proj1 (flag_pend_caller_restore_input_state_inv configured critical other
    (fun _ _ => receipt ** frame) sg (FlagPendTaskCaller returned) returned saved acquired current restored Howned)) as Hvalid.
  pose proof complete as [Hstate Hcompletion].
  destruct Hstate as [Hsaved [Hdestination' [Hhigh Hcurrent]]].
  assert (Hready : os_sched_task_current_ready returned current).
  { eapply SchedulerReturnFacts.os_sched_install_current_ready; try eassumption.
    exact (proj2 (proj2 Hsame)). }
  assert (Hbody : os_sched_task_body_source configured critical sg entry original returned current).
  { unfold current, InstallComponent.task_install_fields_current, call.
    eapply OsSchedTaskBodyTaskLastInstall with (first_installed := first_installed)
      (resumed := resumed) (before_heap := before_heap); try eassumption.
    - eapply os_sched_task_c_sequence_prefix; exact Hprefix.
    - reflexivity. }
  assert (Hnormal : kernel_call_normal_return original entry returned current).
  { split; [exact Hsame|]. intro Havailable.
    unfold kernel_call_stack_available; rewrite (proj1 Htask).
    unfold current, InstallComponent.task_install_fields_current, call.
    change (task_stack_take
      (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks) context.(os_sched_call_stack) outgoing)
      original.(os_sched_call_stack) (task_stack_key returned.(os_sched_call_stack)) = None).
    rewrite (proj2 (proj2 Hsame)); apply task_stack_take_lookup. }
  assert (Hcontrol : kernel_call_control_rely sg entry current).
  { unfold current, call.
    eapply SelectedControlComposition.task_last_call_selected_sequence_control with
      (first_installed := first_installed) (last_entry := last_entry) (saved_sp := saved_sp)
      (observer := original.(os_sched_call_invocation)) (origin := original.(os_sched_call_origin)); eassumption. }
  assert (Hobservations : os_sched_task_body_observation configured critical sg original entry returned current).
  { exact (conj Hbody (conj Hready (conj Hnormal (conj Hcontrol (fun _ => Htask))))). }
  assert (Hclose :
    coq_prop (flag_pend_call_endpoint_observations configured sg (FlagPendTaskCaller original) original hooked returned current) &&
    flag_pend_caller_restore_input configured critical other (fun _ _ => receipt ** frame) sg
      (FlagPendTaskCaller returned) returned saved acquired current |--
    os_sched_task_body_post configured critical active sg original saved acquired entry).
  { intros heap [Hinner Howner].
    exists returned, current, other; split; [exact Hobservations|].
    pose proof (proj1 (flag_pend_task_restore_input_masked_equiv configured critical other
      (fun _ _ => receipt ** frame) sg returned saved acquired current) heap Howner) as Hmasked.
    match type of Hmasked with ?P heap => match goal with |- ?Q heap => assert (Hresource : P |-- Q) end end.
    { sep_apply_l_atomic (Hreceipt returned Hsame Htask Hready); entailer!. }
    exact (Hresource heap Hmasked). }
  pose (tail := KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hlast_input (fun heap Howner => Howner) last Hclose).
  pose (run := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ prefix Hbridge tail).
  exists run; split.
  - apply KernelCSourceThen; [exact Hprefix|]. apply KernelCSourceAdapt; exact Hlast.
  - split.
    + split; [exact Hinitial|]. exact (proj2 (kernel_program_selected_c_sequence_resources configured critical sg
        original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ run)).
    + intros X Hsafe; eapply os_sched_task_body_return_safeexec; eassumption.
Qed.

Lemma irq_acquired_c_prefix_switch_output :
  forall environment critical sg entry first_installed initial_local active initial_heap handler irq_entry transfer
    original saved acquired receipt other frame first_heap input stopped before_heap output
    prepared hooked_heap installed selected after source prefix hook install restore,
  let configured := task_sw_hook_call_environment environment in
  forall (earlier : kernel_c_sequence (kernel_program_selected_c_step configured critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      first_installed first_heap input stopped irq_entry before_heap output),
  IRQAcquiredReturn.kernel_irq_acquired_c_completion environment critical sg handler irq_entry transfer original saved acquired
    receipt other frame before_heap prepared hooked_heap installed selected after source prefix hook install restore ->
  os_sched_task_switch_pre configured critical initial_local active sg original saved acquired entry initial_heap ->
  os_sched_switch_source configured.(task_stack_call_external) sg entry original first_installed ->
  kernel_program_selected_c_sequence_source configured critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ earlier ->
  output |-- IRQCPrefix.os_int_exit_prefix_fields_owner configured critical sg handler irq_entry
    original saved acquired receipt other frame ->
  (forall returned, task_tcb_init_stack_same_call returned original ->
    kernel_call_task_source returned (os_int_exit_installed_state transfer) ->
    os_sched_task_current_ready returned (os_int_exit_installed_state transfer) ->
    IRQSelectedCompletion.irq_selected_suffix_receipt handler receipt frame |--
      active returned (os_int_exit_installed_state transfer)) ->
  let current := os_int_exit_installed_state transfer in
  let returned := kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack) transfer.(os_int_exit_incoming_fragments) in
  exists (run : kernel_c_sequence (kernel_program_selected_c_step configured critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)) first_installed first_heap input
    (orb stopped false) current after (os_sched_task_body_post configured critical active sg original saved acquired entry)),
  kernel_program_selected_c_sequence_source configured critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ run /\
  os_sched_task_switch_output configured critical initial_local active sg original saved acquired entry initial_heap after /\
  (forall X, safeExec (fun state => state = entry) (os_sched_task_body_program configured critical sg original) X ->
    safeExec (fun state => state = current) (StateRelMonad.ret returned) X).
Proof.
  intros environment critical sg entry first_installed initial_local active initial_heap handler irq_entry transfer original saved
    acquired receipt other frame first_heap input stopped before_heap output prepared hooked_heap installed selected after
    source prefix hook install restore configured earlier complete Hinitial Hfirst Hearlier Hbridge Hreceipt current returned.
  destruct (SelectedCompletionComposition.irq_acquired_completion_environment_sequence environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None handler irq_entry transfer original saved acquired
    receipt other frame before_heap prepared hooked_heap installed selected after source prefix hook install restore complete)
    as [last [Hlast [Htask [Hsame [Hready [Hidle [Hnonidle [Hnormal [Hrunning Henabled]]]]]]]]].
  assert (Hbody : os_sched_task_body_source configured critical sg entry original returned current).
  { eapply OsSchedTaskBodyIRQLastInstall with (first_installed := first_installed)
      (handler := handler) (irq_entry := irq_entry); try eassumption.
    - right; exists before_heap; eapply os_sched_task_c_sequence_prefix; exact Hearlier.
    - reflexivity.
    - exact (proj2 (proj2 Hsame)). }
  assert (Hfirst_running : first_installed.(SchedState).(isRunning) = entry.(SchedState).(isRunning)).
  { destruct Hfirst as [Hswitch [old_sp [outgoing [hooked [incoming [resumed [Hsave [Hhook [Hdest Hinstalled]]]]]]]]].
    change (hooked = os_sched_save_current_sp (os_sched_prefix_state entry)
      original.(os_sched_call_stack).(stackLeaseSlot) old_sp) in Hhook.
    rewrite Hinstalled, Hhook; exact (proj2 (proj2 (proj2 (os_sched_ready_checkpoint_frame entry)))). }
  assert (Hentry_enabled : os_sched_selection_enabled entry = true).
  { exact (proj1 (proj1 (os_sched_requests_switch_iff entry) (proj1 Hfirst))). }
  pose proof (SelectedControlComposition.kernel_program_selected_c_sequence_running configured critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ earlier) as Hprefix_running.
  assert (Hcontrol : kernel_call_control_rely sg entry current).
  { apply SelectedEndpointObservations.kernel_call_enabled_control_rely; [exact Hentry_enabled|exact Henabled|].
    change ((os_int_exit_installed_state transfer).(SchedState).(isRunning) = entry.(SchedState).(isRunning)).
    etransitivity; [exact Hrunning|].
    etransitivity; [exact Hprefix_running|exact Hfirst_running]. }
  assert (Hobservations : os_sched_task_body_observation configured critical sg original entry returned current).
  { exact (conj Hbody (conj Hready (conj (Hnormal entry) (conj Hcontrol (fun _ => Htask))))). }
  assert (Hclose : IRQSelectedCompletion.irq_selected_suffix_output configured critical sg handler transfer
    original saved acquired receipt other frame |-- os_sched_task_body_post configured critical active sg original saved acquired entry).
  { intros heap Howner; exists returned, current, other; split; [exact Hobservations|].
    pose proof (proj1 (flag_pend_task_restore_input_masked_equiv configured critical other
      (fun _ _ => IRQSelectedCompletion.irq_selected_suffix_receipt handler receipt frame)
      sg returned saved acquired current) heap Howner) as Hmasked.
    match type of Hmasked with ?P heap => match goal with |- ?Q heap => assert (Hresource : P |-- Q) end end.
    { sep_apply_l_atomic (Hreceipt returned Hsame Htask Hready); entailer!. }
    exact (Hresource heap Hmasked). }
  pose proof (proj1 (kernel_program_selected_c_sequence_resources configured critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ last)) as Hlast_input.
  pose (tail := KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hlast_input (fun heap Howner => Howner) last Hclose).
  pose (run := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ earlier Hbridge tail).
  exists run; split.
  - apply KernelCSourceThen; [exact Hearlier|]. apply KernelCSourceAdapt; exact Hlast.
  - split.
    + split; [exact Hinitial|]. exact (proj2 (kernel_program_selected_c_sequence_resources configured critical sg
        original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ run)).
    + intros X Hsafe; eapply os_sched_task_body_return_safeexec; eassumption.
Qed.

Lemma os_sched_task_switch_source_output_safeexec :
  forall environment critical local active sg original saved acquired entry initial_heap
    (X : OsSchedCallContext -> UCOS2_Verify_State -> Prop),
  let configured := task_sw_hook_call_environment environment in
  safeExec (fun state => state = entry) (os_sched_task_body_program configured critical sg original) X ->
  os_sched_task_switch_source_output configured critical local active sg original saved acquired entry initial_heap |--
  EX returned current next_local,
    coq_prop (os_sched_task_body_observation configured critical sg original entry returned current /\
      safeExec (fun state => state = current) (StateRelMonad.ret returned) X) &&
    (kernel_continuation_call_masked configured.(task_stack_call_continuations) kernel_program_fields_inv
      next_local critical sg (task_stack_call_active_key returned) returned saved acquired current ** active returned current).
Proof.
  intros environment critical local active sg original saved acquired entry initial_heap X configured Hsafe heap Hsource.
  pose proof (os_sched_task_switch_source_output_observation environment critical local active sg original saved acquired
    entry initial_heap heap Hsource) as [Hpre Hbody].
  exact (os_sched_task_body_post_safeexec configured critical active sg original saved acquired entry X Hsafe heap Hbody).
Qed.

End SchedulerCalleePhaseComponent.
