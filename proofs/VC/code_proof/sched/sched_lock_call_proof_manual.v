Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From Ucos2Verify.VC.code.sched Require Import sched_lock_call_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.sched.spec.sched_lock_call_api_program_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSSchedLock_entail_wit_1_1 : OSSchedLock_entail_wit_1_1.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range (&( "OSIntNesting" ))
    (os_sched_lock_ints entry_3)).
  Intros.
  change (0 <= os_sched_lock_ints entry_3 <= 255) in H.
  rewrite unsigned_last_nbits_eq in PreH2 by
    (change (0 <= os_sched_lock_ints entry_3 < 4294967296); lia).
  assert (Hlt : (os_sched_lock_locks entry_3 <? 255) = true)
    by (apply Z.ltb_lt; exact PreH1).
  Exists entry_3.
  rewrite os_sched_lock_updated_locks_eq, PreH2, Z.eqb_refl, Hlt.
  entailer!.
Qed.

Lemma proof_of_OSSchedLock_entail_wit_1_2 : OSSchedLock_entail_wit_1_2.
Proof.
  left; intros.
  assert (Hlt : (os_sched_lock_locks entry_3 <? 255) = false)
    by (apply Z.ltb_ge; lia).
  assert (Hupdate : os_sched_lock_updated_locks entry_3 =
      os_sched_lock_locks entry_3).
  { rewrite os_sched_lock_updated_locks_eq, Hlt.
    destruct (os_sched_lock_ints entry_3 =? 0); reflexivity. }
  Exists entry_3; rewrite Hupdate; entailer!.
Qed.

Lemma proof_of_OSSchedLock_entail_wit_1_3 : OSSchedLock_entail_wit_1_3.
Proof.
  left; intros.
  assert (Hints : os_sched_lock_ints entry_3 <> 0).
  { intro Heq; apply PreH1; rewrite Heq; reflexivity. }
  assert (Heqb : (os_sched_lock_ints entry_3 =? 0) = false)
    by (apply Z.eqb_neq; exact Hints).
  Exists entry_3.
  rewrite os_sched_lock_updated_locks_eq, Heqb; entailer!.
Qed.

Lemma proof_of_OSSchedLock_return_wit_1 : OSSchedLock_return_wit_1.
Proof.
  left; intros.
  lazymatch goal with
  | Hsafe : os_sched_lock_continuation ?critical ?sg ?invocation ?before ?X |- _ =>
    sep_apply_l_atomic (os_sched_lock_post_program_post platform critical sg
      invocation origin mask before X Hsafe)
  end.
  entailer!.
Qed.

Lemma proof_of_OSSchedLock_return_wit_2 : OSSchedLock_return_wit_2.
Proof.
left; intros.
  lazymatch goal with
  | Hglobal : os_sched_lock_global_addresses sg _ _ _ |- _ =>
      pose proof Hglobal as [Hrunning _]; rewrite Hrunning
  end.
  apply os_sched_lock_program_not_running_return.
  - assumption.
  - lazymatch goal with
    | Hguard : unsigned_last_nbits (os_sched_lock_running before) 32 <> 1 |- _ =>
        intro Heq; apply Hguard; rewrite Heq; reflexivity
    end.
  - assumption.
Qed.

Lemma proof_of_OSSchedLock_partial_solve_wit_2_pure : OSSchedLock_partial_solve_wit_2_pure.
Proof.
left; intros.
  assert (Hrunning : os_sched_lock_running before = 1).
  { lazymatch goal with
    | Hguard : unsigned_last_nbits (os_sched_lock_running before) 32 = 1 |- _ =>
      unfold os_sched_lock_running in Hguard |- *;
      destruct (isRunning (SchedState before)); [reflexivity|discriminate Hguard]
    end. }
  entailer!.
Qed.

Lemma proof_of_OSSchedLock_which_implies_wit_1 : OSSchedLock_which_implies_wit_1.
Proof.
left; intros.
  pose proof PreH1 as [Hrunning _].
  unfold os_sched_lock_program_pre, os_sched_lock_pre.
  rewrite <- Hrunning; entailer!.
Qed.

Lemma proof_of_OSSchedLock_which_implies_wit_2 : OSSchedLock_which_implies_wit_2.
Proof.
left; intros.
  lazymatch goal with
  | Hglobal : os_sched_lock_global_addresses sg _ _ _ |- _ =>
      pose proof Hglobal as [Hrunning [Hints Hlocks]]
  end.
  sep_apply (os_sched_lock_split_counters sg entry_2).
  Intros.
  Exists entry_2; rewrite <- Hints, <- Hlocks; entailer!.
Qed.

Lemma proof_of_OSSchedLock_which_implies_wit_3 : OSSchedLock_which_implies_wit_3.
Proof.
left; intros.
  lazymatch goal with
  | Hbody : os_sched_lock_body_facts _ _ _ _ _ _ entry_2 |- _ =>
      pose proof Hbody as [_ [_ [Hvalid _]]]
  end.
  lazymatch goal with
  | Hglobal : os_sched_lock_global_addresses sg _ _ _ |- _ =>
      pose proof Hglobal as [Hrunning [Hints Hlocks]]
  end.
  rewrite Hints, Hlocks.
  Exists entry_2.
  sep_apply (os_sched_lock_merge_counters sg entry_2 Hvalid).
  entailer!.
Qed.
