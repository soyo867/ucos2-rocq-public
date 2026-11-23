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
From Ucos2Verify.VC.code.sched Require Import sched_unlock_call_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_call_api_program_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSSchedUnlock_safety_wit_1 : OSSchedUnlock_safety_wit_1.
Proof.
  unfold OSSchedUnlock_safety_wit_1; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSSchedUnlock_safety_wit_2 : OSSchedUnlock_safety_wit_2.
Proof.
  unfold OSSchedUnlock_safety_wit_2; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSSchedUnlock_safety_wit_3 : OSSchedUnlock_safety_wit_3.
Proof.
  unfold OSSchedUnlock_safety_wit_3; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSSchedUnlock_safety_wit_4 : OSSchedUnlock_safety_wit_4.
Proof.
  unfold OSSchedUnlock_safety_wit_4; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSSchedUnlock_safety_wit_5 : OSSchedUnlock_safety_wit_5.
Proof.
  unfold OSSchedUnlock_safety_wit_5; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_1_pure : OSSchedUnlock_partial_solve_wit_1_pure.
Proof.
  unfold OSSchedUnlock_partial_solve_wit_1_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_1 : OSSchedUnlock_partial_solve_wit_1.
Proof.
  unfold OSSchedUnlock_partial_solve_wit_1, OSSchedUnlock_partial_solve_wit_1_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_2_pure : OSSchedUnlock_partial_solve_wit_2_pure.
Proof.
  unfold OSSchedUnlock_partial_solve_wit_2_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_2 : OSSchedUnlock_partial_solve_wit_2.
Proof.
  unfold OSSchedUnlock_partial_solve_wit_2, OSSchedUnlock_partial_solve_wit_2_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_3_pure : OSSchedUnlock_partial_solve_wit_3_pure.
Proof.
  unfold OSSchedUnlock_partial_solve_wit_3_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_3 : OSSchedUnlock_partial_solve_wit_3.
Proof.
  unfold OSSchedUnlock_partial_solve_wit_3, OSSchedUnlock_partial_solve_wit_3_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_4_pure : OSSchedUnlock_partial_solve_wit_4_pure.
Proof.
  unfold OSSchedUnlock_partial_solve_wit_4_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_4 : OSSchedUnlock_partial_solve_wit_4.
Proof.
  unfold OSSchedUnlock_partial_solve_wit_4, OSSchedUnlock_partial_solve_wit_4_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_5_pure : OSSchedUnlock_partial_solve_wit_5_pure.
Proof.
  unfold OSSchedUnlock_partial_solve_wit_5_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_5 : OSSchedUnlock_partial_solve_wit_5.
Proof.
  unfold OSSchedUnlock_partial_solve_wit_5, OSSchedUnlock_partial_solve_wit_5_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_6_pure : OSSchedUnlock_partial_solve_wit_6_pure.
Proof.
  unfold OSSchedUnlock_partial_solve_wit_6_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_6 : OSSchedUnlock_partial_solve_wit_6.
Proof.
  unfold OSSchedUnlock_partial_solve_wit_6, OSSchedUnlock_partial_solve_wit_6_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_7_pure : OSSchedUnlock_partial_solve_wit_7_pure.
Proof.
  unfold OSSchedUnlock_partial_solve_wit_7_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_7 : OSSchedUnlock_partial_solve_wit_7.
Proof.
  unfold OSSchedUnlock_partial_solve_wit_7, OSSchedUnlock_partial_solve_wit_7_aux; intros.
  entailer!.
Qed.
