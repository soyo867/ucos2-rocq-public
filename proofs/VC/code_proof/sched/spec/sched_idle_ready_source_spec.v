Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.sched Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A blocked current task and a ready Idle witness force a different
    selected priority when the real scheduler guards are clear. No
    OSRunning/nonempty fallback is inserted in the source semantics. *)
Lemma os_sched_blocked_idle_requests_switch : forall sg state tid node,
  UCOS2_state_inv sg state -> task_idle_ready sg state.(TskState) ->
  os_sched_selection_enabled state = true ->
  state.(TskState).(inUsedTaskStates) tid = Some node ->
  state.(SchedState).(curSchedPrio) = Some node.(curPrio) ->
  is_effectively_ready node.(stat) node.(dly) = false ->
  state.(SchedState).(readyList) <> [] /\ os_sched_requests_switch state = true.
Proof.
  intros sg state tid node Hvalid Hidle Henabled Hnode Hcache Hblocked.
  pose proof (proj1 (proj1 (proj2 (proj2 Hvalid)))) as Hready.
  assert (Hnonempty : state.(SchedState).(readyList) <> [])
    by (eapply sched_idle_ready_nonempty; eassumption).
  split; [exact Hnonempty|]. apply os_sched_requests_switch_iff; split; [exact Henabled|].
  destruct state.(SchedState).(readyList) as [|head tail] eqn:Hlist; [contradiction|].
  assert (Hin : In head state.(SchedState).(readyList)) by (rewrite Hlist; left; reflexivity).
  destruct (proj1 Hready head Hin) as [selected [Hselected [_ Heffective]]].
  assert (Hsg : valid_stable_glob_vars sg).
  { pose proof (proj1 Hvalid) as Hprofile; unfold selected_kernel_profile in Hprofile; tauto. }
  rewrite (sched_selected_priority_eq_head sg _ _ head tail selected Hsg Hready Hlist Hselected).
  rewrite Hcache; cbn [sched_priority_byte].
  intro Hsame.
  assert (Hunique : task_priority_unique state.(TskState)).
  { pose proof (proj1 (proj2 Hvalid)) as Htasks; unfold task_in_range in Htasks; tauto. }
  assert (Hid : head = tid) by (eapply Hunique; eassumption).
  subst head; rewrite Hnode in Hselected; injection Hselected as Heq; subst selected; congruence.
Qed.

Lemma os_sched_blocked_idle_switch_prefix_source : forall external platform port abi
  sg state call focus tid node (frame : Assertion) before,
  task_idle_ready sg state.(TskState) -> os_sched_selection_enabled state = true ->
  state.(TskState).(inUsedTaskStates) tid = Some node ->
  state.(SchedState).(curSchedPrio) = Some node.(curPrio) ->
  is_effectively_ready node.(stat) node.(dly) = false ->
  (os_sched_source_switch_pre external platform port abi sg call focus state **
    unmap_table_rep sg ** frame) before ->
  exists after, os_sched_source_switch_prefix_execution sg before after /\
    sched_high_ready_consistency (os_sched_prefix_state state).(TskState)
      (os_sched_prefix_state state).(SchedState) /\
    (os_sched_source_switch_pre external platform port abi sg call focus
      (os_sched_prefix_state state) ** unmap_table_rep sg ** frame) after.
Proof.
  intros external platform port abi sg state call focus tid node frame before
    Hidle Henabled Hnode Hcache Hblocked Hpre.
  assert (Hvalid : UCOS2_state_inv sg state).
  { match type of Hpre with ?P before =>
      assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg state) && TT) end.
    { unfold os_sched_source_switch_pre, UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hpre)). }
  destruct (os_sched_blocked_idle_requests_switch sg state tid node Hvalid Hidle
    Henabled Hnode Hcache Hblocked) as [Hnonempty Hswitch].
  exact (os_sched_source_switch_prefix_resources external platform port abi sg state call focus
    frame before Hswitch Hnonempty Hpre).
Qed.
