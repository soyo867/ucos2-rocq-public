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
From Ucos2Verify.VC.code.event Require Import event_wait_list_init_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.event.spec.event_wait_list_init_spec.
Import Ucos2Verify.lib.ucos2_rules_lib.UCOS2_C_Rules.
Local Open Scope sac.

(* Ordinary implementations of the unchanged generated targets. *)
Lemma proof_of_OS_EventWaitListInit_safety_wit_1 : OS_EventWaitListInit_safety_wit_1.
Proof.
  unfold OS_EventWaitListInit_safety_wit_1.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventWaitListInit_entail_wit_1 : OS_EventWaitListInit_entail_wit_1.
Proof.
  unfold OS_EventWaitListInit_entail_wit_1.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventWaitListInit_entail_wit_2 : OS_EventWaitListInit_entail_wit_2.
Proof.
  unfold OS_EventWaitListInit_entail_wit_2.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventWaitListInit_return_wit_1 : OS_EventWaitListInit_return_wit_1.
Proof.
  unfold OS_EventWaitListInit_return_wit_1.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventWaitListInit_partial_solve_wit_1 : OS_EventWaitListInit_partial_solve_wit_1.
Proof.
  unfold OS_EventWaitListInit_partial_solve_wit_1.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventWaitListInit_partial_solve_wit_2_pure : OS_EventWaitListInit_partial_solve_wit_2_pure.
Proof.
  unfold OS_EventWaitListInit_partial_solve_wit_2_pure.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventWaitListInit_partial_solve_wit_2 : OS_EventWaitListInit_partial_solve_wit_2.
Proof.
  unfold OS_EventWaitListInit_partial_solve_wit_2.
  intros _; unfold OS_EventWaitListInit_partial_solve_wit_2_aux; intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventWaitListInit_partial_solve_wit_3_pure : OS_EventWaitListInit_partial_solve_wit_3_pure.
Proof.
  unfold OS_EventWaitListInit_partial_solve_wit_3_pure.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventWaitListInit_partial_solve_wit_3 : OS_EventWaitListInit_partial_solve_wit_3.
Proof.
  unfold OS_EventWaitListInit_partial_solve_wit_3.
  intros _; unfold OS_EventWaitListInit_partial_solve_wit_3_aux; intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventWaitListInit_partial_solve_wit_4_pure : OS_EventWaitListInit_partial_solve_wit_4_pure.
Proof.
  unfold OS_EventWaitListInit_partial_solve_wit_4_pure.
  intros.
  entailer!; try lia; try congruence.
Qed.

Lemma proof_of_OS_EventWaitListInit_partial_solve_wit_4 : OS_EventWaitListInit_partial_solve_wit_4.
Proof.
  unfold OS_EventWaitListInit_partial_solve_wit_4.
  intros _; unfold OS_EventWaitListInit_partial_solve_wit_4_aux; intros.
  entailer!; try lia; try congruence.
Qed.

