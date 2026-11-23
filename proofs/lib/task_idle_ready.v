Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.cross_module_invariants.
Import TaskStateDef ListNotations.
Local Open Scope Z_scope.

(** A property of the actual live TCB map, not a new ghost field or an
    assumption about arbitrary kernel states. Initialization establishes
    it; a caller may use it only after transporting it through the actual
    intervening operations. The existing [task_idle_tail] alone states no
    readiness fact. *)
Definition task_idle_ready (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) : Prop :=
  exists idle node, tasks.(inUsedTaskStates) idle = Some node /\
    node.(curPrio) = sg.(osLowestPrio) /\
    is_effectively_ready node.(stat) node.(dly) = true.

Lemma task_commit_establishes_idle_ready : forall sg tasks p invocation node,
  node.(curPrio) = sg.(osLowestPrio) ->
  is_effectively_ready node.(stat) node.(dly) = true ->
  task_idle_ready sg (task_commit tasks p invocation node).
Proof.
  intros sg tasks p invocation node Hprio Hready.
  exists node.(taskID), (task_set_links node tasks.(tcbListHead) None).
  split; [exact (proj1 (task_commit_publication_fields_eq tasks p invocation node))|].
  split; assumption.
Qed.

Lemma task_commit_preserves_idle_ready : forall sg tasks p invocation node,
  tasks.(inUsedTaskStates) node.(taskID) = None ->
  task_idle_ready sg tasks ->
  task_idle_ready sg (task_commit tasks p invocation node).
Proof.
  intros sg tasks p invocation node Hfresh [idle [old [Hold [Hprio Hready]]]].
  destruct (task_commit_transports_old_fields tasks p invocation node idle old Hfresh Hold)
    as [current [Hcurrent Hfields]].
  exists idle, current; split; [exact Hcurrent|].
  pose proof (f_equal curPrio Hfields) as Hp.
  pose proof (f_equal stat Hfields) as Hs.
  pose proof (f_equal dly Hfields) as Hd.
  cbn [task_set_links curPrio stat dly] in Hp, Hs, Hd.
  rewrite Hp, Hs, Hd; auto.
Qed.

Lemma task_update_non_idle_preserves_idle_ready : forall sg tasks tid old new,
  tasks.(inUsedTaskStates) tid = Some old ->
  old.(curPrio) <> sg.(osLowestPrio) ->
  task_idle_ready sg tasks ->
  task_idle_ready sg (glob_task_set_usedtask tasks tid new).
Proof.
  intros sg tasks tid old new Hold Hnonidle [idle [node [Hnode [Hprio Hready]]]].
  assert (Hdifferent : idle <> tid).
  { intro Heq; subst idle; rewrite Hold in Hnode; injection Hnode as Heq; subst node; contradiction. }
  exists idle, node; split.
  - cbn [glob_task_set_usedtask inUsedTaskStates].
    rewrite (proj2 (Z.eqb_neq _ _) Hdifferent); exact Hnode.
  - auto.
Qed.

Lemma event_pend_preserves_idle_ready : forall sg state eid event tid node kind timeout,
  state.(TskState).(inUsedTaskStates) tid = Some node ->
  valid_task_prio sg node.(curPrio) ->
  task_idle_ready sg state.(TskState) ->
  task_idle_ready sg (event_pend_state sg state eid event tid node kind timeout).(TskState).
Proof.
  intros sg state eid event tid node kind timeout Hnode Hprio Hidle.
  eapply task_update_non_idle_preserves_idle_ready; [exact Hnode| |exact Hidle].
  unfold valid_task_prio in Hprio; lia.
Qed.

Lemma sched_idle_ready_nonempty : forall sg tasks scheduler,
  sched_ready_in_range sg tasks scheduler -> task_idle_ready sg tasks ->
  scheduler.(readyList) <> [].
Proof.
  intros sg tasks scheduler [_ [_ [Hcomplete _]]] [idle [node [Hnode [_ Hready]]]] Hempty.
  pose proof (Hcomplete idle node Hnode Hready) as Hin; rewrite Hempty in Hin; contradiction.
Qed.
