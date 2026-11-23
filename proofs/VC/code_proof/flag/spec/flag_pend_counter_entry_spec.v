Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_local_control_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagPendCounterEntry.
Import PrimitiveComponent PendPhaseCandidate FlagPendLocalControl.

(** The original early C tests supply the upper bounds; the actual byte
    owners supply nonnegativity. Pure UCOS2_state_inv alone is not used as
    a counter-range premise. The original resource is returned intact. *)
Lemma flag_pend_fields_guard_counters_zero : forall sg state,
  os_sched_ints state <= 0 -> os_sched_locks state <= 0 ->
  UCOS2_fields_inv sg state |--
  coq_prop (os_sched_ints state = 0 /\ os_sched_locks state = 0) &&
    UCOS2_fields_inv sg state.
Proof.
  intros sg state Hints Hlocks.
  assert (Hzero : UCOS2_fields_inv sg state |--
    coq_prop (os_sched_ints state = 0 /\ os_sched_locks state = 0)).
  { rewrite (flag_pend_counters_split sg state).
    sep_apply_l_atomic (store_uchar_range sg.(g_OSIntNesting) (os_sched_ints state)).
    sep_apply_l_atomic (store_uchar_range sg.(g_OSLockNesting) (os_sched_locks state)).
    entailer!. }
  intros heap Howned; split; [exact (Hzero heap Howned)|exact Howned].
Qed.

Lemma flag_pend_world_guard_counters_zero : forall environment local sg caller mask state,
  os_sched_ints state <= 0 -> os_sched_locks state <= 0 ->
  flag_pend_caller_world environment local sg caller mask state |--
  coq_prop (os_sched_ints state = 0 /\ os_sched_locks state = 0) &&
    flag_pend_caller_world environment local sg caller mask state.
Proof.
  intros environment local sg caller mask state Hints Hlocks.
  intros heap Hworld.
  destruct (proj1 (flag_pend_caller_world_split environment local sg caller mask state)
    heap Hworld) as [control_heap [fields_heap [Hjoin [Hcontrol Hfields]]]].
  split; [|exact Hworld].
  exact (proj1 (flag_pend_fields_guard_counters_zero sg state Hints Hlocks fields_heap Hfields)).
Qed.

Lemma flag_pend_saved_prefix_guard_counters_zero : forall environment critical sg original mask
  before i pgrp entered saved acquired,
  flag_pend_saved_prefix environment critical sg original mask before i pgrp entered saved acquired ->
  UCOS2_fields_inv sg acquired |--
  coq_prop (os_sched_ints acquired = 0 /\ os_sched_locks acquired = 0) &&
    UCOS2_fields_inv sg acquired.
Proof.
  intros environment critical sg original mask before i pgrp entered saved acquired
    [Hgroup [Hints [Hlocks [_ [_ [_ [_ Hcounters]]]]]]].
  apply flag_pend_fields_guard_counters_zero;
    unfold os_sched_ints, os_sched_locks in *; rewrite <- Hcounters; assumption.
Qed.

Lemma flag_pend_first_critical_counters_zero : forall sg i requested mode delay before result after,
  flag_pend_first_critical sg i requested mode delay before result after ->
  os_sched_ints before = 0 -> os_sched_locks before = 0 ->
  os_sched_ints after = 0 /\ os_sched_locks after = 0.
Proof.
  intros sg i requested mode delay before result after Hstep Hints Hlocks.
  destruct (flag_pend_first_critical_preserves_control _ _ _ _ _ _ _ _ Hstep) as [_ Hcounters].
  unfold os_sched_ints, os_sched_locks in *; rewrite Hcounters; split; assumption.
Qed.

Lemma flag_pend_resume_critical_counters_zero : forall sg i node mode before result after,
  flag_pend_resume_critical sg i node mode before result after ->
  os_sched_ints before = 0 -> os_sched_locks before = 0 ->
  os_sched_ints after = 0 /\ os_sched_locks after = 0.
Proof.
  intros sg i node mode before result after Hstep Hints Hlocks.
  destruct (flag_pend_resume_critical_preserves_control _ _ _ _ _ _ _ Hstep) as [_ Hcounters].
  unfold os_sched_ints, os_sched_locks in *; rewrite Hcounters; split; assumption.
Qed.

Lemma flag_pend_return_control_counters_zero : forall original before returned after,
  flag_pend_call_return_control original before returned after ->
  os_sched_ints before = 0 -> os_sched_locks before = 0 ->
  os_sched_ints after = 0 /\ os_sched_locks after = 0.
Proof.
  intros original before returned after [Hnormal [Hrunning Hcounters]] Hints Hlocks.
  unfold os_sched_ints, os_sched_locks in *; rewrite <- Hcounters; split; assumption.
Qed.

End FlagPendCounterEntry.
