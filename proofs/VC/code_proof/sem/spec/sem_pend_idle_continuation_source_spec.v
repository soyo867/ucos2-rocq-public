Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.core.spec.kernel_idle_ready_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_idle_ready_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_checkpoint_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_task_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The initial witness is produced by [task_tcb_init_published_idle_ready]
    or its physical [task_tcb_init_publication_idle_stack_merge] consumer.
    The actual builtin C trace transports it through counter operations
    and a source-bound TCB publication. A publication changes old links,
    retaining Idle's priority/status/delay. There is no Extra transition
    and no claim that ChangePrio or the old SELF Suspend preserves Idle.

    This is used below on the SAME entry named by the wait origin. It is
    not an additional promise attached to Save/Restore or a new public
    OSSemPend Require. *)
Lemma sem_pend_builtin_trace_preserves_idle_ready : forall Extra sg cut initial next entry,
  @kernel_client_heap_state_trace Extra (fun _ _ _ _ _ => False) sg
    cut initial next entry ->
  UCOS2_state_inv sg initial -> task_idle_ready sg initial.(TskState) ->
  UCOS2_state_inv sg entry /\ task_idle_ready sg entry.(TskState).
Proof.
  intros Extra sg cut initial next entry Htrace.
  induction Htrace; intros Hvalid Hidle; [split; assumption|].
  apply IHHtrace.
  - destruct H.
    + apply os_int_enter_preserves_validity; exact Hvalid.
    + exact Hvalid.
    + eapply task_create_stack_publication_preserves_validity;
        [exact Hvalid|split; [exact H|reflexivity]].
    + contradiction.
  - destruct H.
    + exact Hidle.
    + exact Hidle.
    + change (task_idle_ready sg
        (task_tcb_init_published_state sg (task_create_stack_publication_args publication)
          publication.(stack_publication_invocation) publication.(stack_publication_acquired)
          state publication.(stack_publication_slot) publication.(stack_publication_image)).(TskState)).
      eapply task_tcb_init_publication_preserves_idle_ready with
        (origin := publication.(stack_publication_origin));
        [exact Hvalid|exact (proj1 (proj2 (proj2 H)))|exact Hidle].
    + contradiction.
Qed.

(** Consume the established Idle witness at the actual unawakened wait
    path. [initial] is a source checkpoint carrying the initializer's
    proved fact, not an arbitrary public state. [Hentry_trace] transports
    it to the acquired entry of this exact EventTaskWait. The second
    actual builtin trace starts Closed, so the already proved source
    theorem gives unchanged Task/Scheduler fields: no wake or priority
    mutation is smuggled into this family.

    The current canonical input supplies the actual returned execution
    resource and the complete generic local map. The existing Save module
    contract and C-prefix theorem are reused unchanged. All interrupt/lock
    branches remain: selection-enabled implies a real switch because this
    caller is still blocked and Idle remains ready. A disabled selector
    keeps its actual nonswitch prefix; no ready-return post is invented.

    The public projection still does not expose Idle-ready provenance for
    arbitrary client histories. This source-family consumer therefore is
    not a proof of the full public OSSemPend contract. *)
Lemma sem_pend_idle_continuation_sched_prefix_source :
  forall environment critical saved_local arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    Extra sg init_cut initial entry_cut original first_call mask first_saved public_before observed
    entry eid event tid node timeout call state registers before final_registers acquired saved_heap
    (frame : Assertion),
  let waiting := event_pend_state sg entry eid event tid node PendSem timeout in
  UCOS2_state_inv sg initial -> task_idle_ready sg initial.(TskState) ->
  @kernel_client_heap_state_trace Extra (fun _ _ _ _ _ => False) sg
    init_cut initial entry_cut entry ->
  sem_pend_observed_wait_origin (Some environment) critical sg original first_call mask first_saved
    public_before observed entry eid event tid node ->
  @kernel_client_heap_state_trace Extra (fun _ _ _ _ _ => False) sg
    KernelClientHeapClosed waiting KernelClientHeapClosed state ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (sem_pend_continuation_phase_sched_input
    (SemPendWaitPhase original mask public_before observed eid timeout waiting)
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg call mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  acquired = state /\
  kernel_call_save_uninterrupted_execution arch registers state before
    final_registers acquired saved_heap /\
  task_idle_ready sg state.(TskState) /\ state.(SchedState).(readyList) <> [] /\
  (os_sched_selection_enabled state = true -> os_sched_requests_switch state = true) /\
  exists prefix_heap,
    os_sched_modular_prefix_execution sg state saved_heap prefix_heap /\
    (os_sched_selection_enabled state = true ->
      sched_high_ready_consistency (os_sched_prefix_state state).(TskState)
        (os_sched_prefix_state state).(SchedState)) /\
    (kernel_continuation_call_masked environment.(task_stack_call_continuations)
      kernel_program_inv (task_create_continuation_local saved_local) critical sg
      (task_stack_call_active_key call) call final_registers.(kernel_save_r0) state
      (os_sched_prefix_state state) ** frame) prefix_heap.
Proof.
  intros environment critical saved_local arch save Extra sg init_cut initial entry_cut
    original first_call mask first_saved public_before observed entry eid event tid node timeout
    call state registers before final_registers acquired saved_heap frame waiting
    Hinitial Hidle_initial Hentry_trace Horigin Hwaiting_trace Hreturn Hcpsr Hmask Hpre Hsave.
  destruct (sem_pend_builtin_trace_preserves_idle_ready Extra sg init_cut initial entry_cut entry
    Hentry_trace Hinitial Hidle_initial) as [Hentry_valid Hidle_entry].
  pose proof Horigin as [Hacquire [Hwait_entry [Horiginal [Hsource Hcache]]]].
  pose proof Hwait_entry as [_ [_ [Hcurrent [Hnode [_ [_ [Hnonidle _]]]]]]].
  destruct (sem_pend_wait_preserves_call_source sg original entry eid event tid node timeout
    Hwait_entry Hsource Hcache) as [Hwaiting_valid [Hwaiting_source Hwaiting_cache]].
  fold waiting in Hwaiting_valid, Hwaiting_source, Hwaiting_cache.
  assert (Hidle_waiting : task_idle_ready sg waiting.(TskState)).
  { change (task_idle_ready sg
      (glob_task_set_usedtask entry.(TskState) tid
        (task_set_event_ptr (task_prepare_event_wait node PendSem timeout) (Some eid)))).
    eapply task_update_non_idle_preserves_idle_ready; eassumption. }
  destruct (sem_pend_builtin_trace_preserves_idle_ready Extra sg KernelClientHeapClosed waiting
    KernelClientHeapClosed state Hwaiting_trace Hwaiting_valid Hidle_waiting)
    as [Hstate_valid Hidle_state].
  destruct (kernel_client_builtin_closed_trace_task_fields Extra sg KernelClientHeapClosed waiting
    KernelClientHeapClosed state Hwaiting_trace eq_refl) as [_ [Htasks Hscheduler]].
  assert (Hnonempty : state.(SchedState).(readyList) <> []).
  { eapply sched_idle_ready_nonempty;
      [exact (proj1 (proj1 (proj2 (proj2 Hstate_valid))))|exact Hidle_state]. }
  assert (Hswitch : os_sched_selection_enabled state = true -> os_sched_requests_switch state = true).
  { intro Henabled.
    assert (Hwaiting_node : state.(TskState).(inUsedTaskStates) tid =
      Some (task_set_event_ptr (task_prepare_event_wait node PendSem timeout) (Some eid))).
    { rewrite Htasks.
      change ((if Z.eqb tid tid then
        Some (task_set_event_ptr (task_prepare_event_wait node PendSem timeout) (Some eid))
        else entry.(TskState).(inUsedTaskStates) tid) =
        Some (task_set_event_ptr (task_prepare_event_wait node PendSem timeout) (Some eid))).
      rewrite Z.eqb_refl; reflexivity. }
    assert (Hwaiting_priority : state.(SchedState).(curSchedPrio) = Some node.(curPrio)).
    { rewrite Hscheduler; change (entry.(SchedState).(curSchedPrio) = Some node.(curPrio)).
      unfold sched_current_consistency in Hcache; rewrite Hcurrent in Hcache.
      destruct Hcache as [found [Hfound Hprio]].
      assert (found = node) by congruence; subst found; exact Hprio. }
    exact (proj2 (os_sched_blocked_idle_requests_switch sg state tid
      (task_set_event_ptr (task_prepare_event_wait node PendSem timeout) (Some eid))
      Hstate_valid Hidle_state Henabled Hwaiting_node Hwaiting_priority
      (task_prepare_event_wait_not_ready node PendSem timeout))). }
  match type of Hpre with ?P before => assert (Hopen : P |--
    kernel_continuation_call_closed environment.(task_stack_call_continuations)
      kernel_program_inv (task_create_continuation_local saved_local) sg
      (task_stack_call_active_key call) call mask state ** frame) end.
  { cbn [sem_pend_continuation_phase_sched_input sem_pend_continuation_sched_input].
    unfold os_sched_continuation_pre; entailer!. }
  destruct (kernel_continuation_call_uninterrupted_save
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    environment.(task_stack_call_port) critical arch environment.(task_stack_call_continuations) save
    kernel_program_inv (task_create_continuation_local saved_local) sg (task_stack_call_active_key call)
    call state mask registers before final_registers acquired saved_heap frame
    Hreturn Hcpsr Hmask (Hopen before Hpre) Hsave) as [Hstate [Hr0 [Hsaved Hmasked]]].
  destruct (os_sched_modular_prefix_continuation_resources
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    environment.(task_stack_call_port) environment.(task_stack_call_continuations)
    (task_create_continuation_local saved_local) critical sg (task_stack_call_active_key call)
    call final_registers.(kernel_save_r0) state state saved_heap frame
    (fun _ => Hnonempty) Hmasked) as [prefix_heap [Hprefix [Hhigh Hafter]]].
  split; [exact Hstate|]. split; [exact Hsaved|]. split; [exact Hidle_state|].
  split; [exact Hnonempty|]. split; [exact Hswitch|].
  exists prefix_heap; split; [exact Hprefix|].
  split; [intro Henabled; exact (Hhigh (Hswitch Henabled))|exact Hafter].
Qed.
