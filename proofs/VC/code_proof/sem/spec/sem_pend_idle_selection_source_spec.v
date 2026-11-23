Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.sched Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_idle_guard_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_idle_ready_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_sched_entry_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The ordinary first-Save/Restore family keeps the prechecked state.
    Consume its actual waiting heap at the Scheduler selector. The Idle
    fact is transported across these exact wait stores, and both selection
    obligations are derived. Transport from boot through arbitrary other
    API calls remains a separate module-protocol obligation; this is not
    an added public SemPend Require or a claim of whole-API completion. *)
Lemma sem_pend_wait_idle_switch_prefix_source : forall external platform port abi
  sg entry eid event tid node timeout call focus (frame : Assertion) before,
  task_idle_ready sg entry.(TskState) ->
  entry.(TskState).(inUsedTaskStates) tid = Some node ->
  valid_task_prio sg node.(curPrio) ->
  entry.(SchedState).(curSchedPrio) = Some node.(curPrio) ->
  sem_pend_context_error (event_slot_type_value entry.(EventState) eid)
    entry.(IntrState).(intNesting) entry.(IntrState).(lockNesting) = None ->
  let waiting := event_pend_state sg entry eid event tid node PendSem timeout in
  (os_sched_source_switch_pre external platform port abi sg call focus waiting **
    unmap_table_rep sg ** frame) before ->
  exists after, os_sched_source_switch_prefix_execution sg before after /\
    sched_high_ready_consistency (os_sched_prefix_state waiting).(TskState)
      (os_sched_prefix_state waiting).(SchedState) /\
    (os_sched_source_switch_pre external platform port abi sg call focus
      (os_sched_prefix_state waiting) ** unmap_table_rep sg ** frame) after.
Proof.
  intros external platform port abi sg entry eid event tid node timeout call focus frame before
    Hidle Hnode Hprio Hcache Hclear waiting Hpre.
  assert (Hidle_wait : task_idle_ready sg waiting.(TskState)).
  { eapply event_pend_preserves_idle_ready; eassumption. }
  assert (Henabled : os_sched_selection_enabled waiting = true).
  { pose proof (sem_pend_wait_clear_scheduler_counts sg entry eid event tid node timeout Hclear) as Hcounts.
    cbv zeta in Hcounts; fold waiting in Hcounts.
    match type of Hpre with ?P before =>
      assert (Hobserve : P |-- coq_prop (os_sched_selection_enabled waiting = true) && TT) end.
    { unfold os_sched_source_switch_pre; Intros; sep_apply_l_atomic Hcounts.
      entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hpre)). }
  eapply os_sched_blocked_idle_switch_prefix_source with
    (tid := tid) (node := task_set_event_ptr (task_prepare_event_wait node PendSem timeout) (Some eid));
    [exact Hidle_wait|exact Henabled| |exact Hcache| |exact Hpre].
  - cbn [waiting event_pend_state event_wait_state replace_SchedS replace_EventS replace_TskS
      TskState glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
  - apply task_prepare_event_wait_not_ready.
Qed.

(** Consume the critical effect of the task-idle-protection variant at the
    existing physical SemPend wait/selector cut. The new client keeps the
    original argument guard and has an unconditional resolved-priority
    check. In particular an ISR requesting SELF while Idle is current
    takes the new error branch instead of clearing Idle's ready bit.

    The predecessor's Idle fact must already come from initialization and
    the actual intervening source steps. This theorem transports it over
    ONE registered critical mutation. It neither invents a Save/Restore
    source embedding nor changes the old projected source family. Further
    clients (in particular ChangePrio SELF) require separate preservation
    proofs before arbitrary environment traces can use this consumer. *)
Lemma sem_pend_wait_after_guarded_suspend_selection_source :
  forall external platform port abi sg actor priority predecessor entry
    eid event tid node timeout call focus (frame : Assertion) before,
  UCOS2_state_inv sg predecessor ->
  task_idle_ready sg predecessor.(TskState) ->
  kernel_client_step (task_suspend_idle_guard_client actor priority) sg predecessor entry ->
  entry.(TskState).(inUsedTaskStates) tid = Some node ->
  valid_task_prio sg node.(curPrio) ->
  entry.(SchedState).(curSchedPrio) = Some node.(curPrio) ->
  sem_pend_context_error (event_slot_type_value entry.(EventState) eid)
    entry.(IntrState).(intNesting) entry.(IntrState).(lockNesting) = None ->
  let waiting := event_pend_state sg entry eid event tid node PendSem timeout in
  (os_sched_source_switch_pre external platform port abi sg call focus waiting **
    unmap_table_rep sg ** frame) before ->
  exists after, os_sched_source_switch_prefix_execution sg before after /\
    sched_high_ready_consistency (os_sched_prefix_state waiting).(TskState)
      (os_sched_prefix_state waiting).(SchedState) /\
    (os_sched_source_switch_pre external platform port abi sg call focus
      (os_sched_prefix_state waiting) ** unmap_table_rep sg ** frame) after.
Proof.
  intros external platform port abi sg actor priority predecessor entry
    eid event tid node timeout call focus frame before Hvalid Hidle Hstep
    Hnode Hprio Hcache Hclear waiting Hpre.
  destruct (task_suspend_idle_guard_client_preserves_resources actor priority
    sg predecessor entry (conj Hvalid Hidle) Hstep) as [[_ Hidle_entry] _].
  exact (sem_pend_wait_idle_switch_prefix_source external platform port abi
    sg entry eid event tid node timeout call focus frame before
    Hidle_entry Hnode Hprio Hcache Hclear Hpre).
Qed.
