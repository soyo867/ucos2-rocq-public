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
From Ucos2Verify.VC.code.event Require Import event_task_rdy_full_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_full_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
Local Open Scope sac_scope.
Require Import Ucos2Verify.VC.code.event.spec.event_task_remove_spec.
Import Ucos2Verify.lib.ucos2_rules_lib.UCOS2_C_Rules.
Local Open Scope sac.

(* Ordinary proofs of the unchanged full-profile generated targets. *)
Lemma proof_of_OS_EventTaskRdy_safety_wit_3 : OS_EventTaskRdy_safety_wit_3.
Proof.
  unfold OS_EventTaskRdy_safety_wit_3.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_safety_wit_4 : OS_EventTaskRdy_safety_wit_4.
Proof.
  unfold OS_EventTaskRdy_safety_wit_4.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_entail_wit_2 : OS_EventTaskRdy_entail_wit_2.
Proof.
  unfold OS_EventTaskRdy_entail_wit_2.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_return_wit_1 : OS_EventTaskRdy_return_wit_1.
Proof.
  unfold OS_EventTaskRdy_return_wit_1.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_1_pure : OS_EventTaskRdy_partial_solve_wit_1_pure.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_1_pure.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_1 : OS_EventTaskRdy_partial_solve_wit_1.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_1.
  intros _; unfold OS_EventTaskRdy_partial_solve_wit_1_aux; intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_2_pure : OS_EventTaskRdy_partial_solve_wit_2_pure.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_2_pure.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_2 : OS_EventTaskRdy_partial_solve_wit_2.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_2.
  intros _; unfold OS_EventTaskRdy_partial_solve_wit_2_aux; intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_3_pure : OS_EventTaskRdy_partial_solve_wit_3_pure.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_3_pure.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_3 : OS_EventTaskRdy_partial_solve_wit_3.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_3.
  intros _; unfold OS_EventTaskRdy_partial_solve_wit_3_aux; intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_4_pure : OS_EventTaskRdy_partial_solve_wit_4_pure.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_4_pure.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_4 : OS_EventTaskRdy_partial_solve_wit_4.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_4.
  intros _; unfold OS_EventTaskRdy_partial_solve_wit_4_aux; intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_5 : OS_EventTaskRdy_partial_solve_wit_5.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_5.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_6_pure : OS_EventTaskRdy_partial_solve_wit_6_pure.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_6_pure.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_6 : OS_EventTaskRdy_partial_solve_wit_6.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_6.
  intros _; unfold OS_EventTaskRdy_partial_solve_wit_6_aux; intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_7_pure : OS_EventTaskRdy_partial_solve_wit_7_pure.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_7_pure.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_7 : OS_EventTaskRdy_partial_solve_wit_7.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_7.
  intros _; unfold OS_EventTaskRdy_partial_solve_wit_7_aux; intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_8_pure : OS_EventTaskRdy_partial_solve_wit_8_pure.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_8_pure.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_8 : OS_EventTaskRdy_partial_solve_wit_8.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_8.
  intros _; unfold OS_EventTaskRdy_partial_solve_wit_8_aux; intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_9 : OS_EventTaskRdy_partial_solve_wit_9.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_9.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_10_pure : OS_EventTaskRdy_partial_solve_wit_10_pure.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_10_pure.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_10 : OS_EventTaskRdy_partial_solve_wit_10.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_10.
  intros _; unfold OS_EventTaskRdy_partial_solve_wit_10_aux; intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_11_pure : OS_EventTaskRdy_partial_solve_wit_11_pure.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_11_pure.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_11 : OS_EventTaskRdy_partial_solve_wit_11.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_11.
  intros _; unfold OS_EventTaskRdy_partial_solve_wit_11_aux; intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_12_pure : OS_EventTaskRdy_partial_solve_wit_12_pure.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_12_pure.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_12 : OS_EventTaskRdy_partial_solve_wit_12.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_12.
  intros _; unfold OS_EventTaskRdy_partial_solve_wit_12_aux; intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_13 : OS_EventTaskRdy_partial_solve_wit_13.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_13.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_14 : OS_EventTaskRdy_partial_solve_wit_14.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_14.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_15 : OS_EventTaskRdy_partial_solve_wit_15.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_15.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_16 : OS_EventTaskRdy_partial_solve_wit_16.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_16.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_17 : OS_EventTaskRdy_partial_solve_wit_17.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_17.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_18_pure : OS_EventTaskRdy_partial_solve_wit_18_pure.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_18_pure.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_18 : OS_EventTaskRdy_partial_solve_wit_18.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_18.
  intros _; unfold OS_EventTaskRdy_partial_solve_wit_18_aux; intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_19_pure : OS_EventTaskRdy_partial_solve_wit_19_pure.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_19_pure.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_19 : OS_EventTaskRdy_partial_solve_wit_19.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_19.
  intros _; unfold OS_EventTaskRdy_partial_solve_wit_19_aux; intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRdy_partial_solve_wit_20 : OS_EventTaskRdy_partial_solve_wit_20.
Proof.
  unfold OS_EventTaskRdy_partial_solve_wit_20.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRemove_safety_wit_1 : OS_EventTaskRemove_safety_wit_1.
Proof.
  unfold OS_EventTaskRemove_safety_wit_1.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRemove_safety_wit_2 : OS_EventTaskRemove_safety_wit_2.
Proof.
  unfold OS_EventTaskRemove_safety_wit_2.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventTaskRemove_partial_solve_wit_1 : OS_EventTaskRemove_partial_solve_wit_1.
Proof.
  unfold OS_EventTaskRemove_partial_solve_wit_1.
  intros.
  entailer!; try lia; try congruence.
Qed.

