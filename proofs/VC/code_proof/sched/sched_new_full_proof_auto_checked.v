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
From Ucos2Verify.VC.code.sched Require Import sched_new_full_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OS_SchedNew_partial_solve_wit_1_pure : OS_SchedNew_partial_solve_wit_1_pure.
Proof.
  unfold OS_SchedNew_partial_solve_wit_1_pure; intros.
  entailer!; try lia; try tauto.
Qed. 

Lemma proof_of_OS_SchedNew_partial_solve_wit_1 : OS_SchedNew_partial_solve_wit_1.
Proof.
  unfold OS_SchedNew_partial_solve_wit_1, OS_SchedNew_partial_solve_wit_1_aux; intros.
  entailer!; try lia; try tauto.
Qed. 

Lemma proof_of_OS_SchedNew_partial_solve_wit_2 : OS_SchedNew_partial_solve_wit_2.
Proof.
  unfold OS_SchedNew_partial_solve_wit_2; intros.
  sep_apply (UCharArray.full_split_to_missing_i (&("OSUnMapTbl"))
    group 256 unmap_table 0 ltac:(lia)).
  entailer!; try lia; try tauto.
Qed. 

Lemma proof_of_OS_SchedNew_partial_solve_wit_3 : OS_SchedNew_partial_solve_wit_3.
Proof.
  unfold OS_SchedNew_partial_solve_wit_3; intros.
  sep_apply (UCharArray.full_split_to_missing_i (&("OSRdyTbl"))
    y 8 rows 0 ltac:(lia)).
  entailer!; try lia; try tauto.
Qed. 

Lemma proof_of_OS_SchedNew_partial_solve_wit_4 : OS_SchedNew_partial_solve_wit_4.
Proof.
  unfold OS_SchedNew_partial_solve_wit_4; intros.
  sep_apply (UCharArray.full_split_to_missing_i (&("OSUnMapTbl"))
    (Znth y rows 0) 256 unmap_table 0 ltac:(lia)).
  entailer!; try lia; try tauto.
Qed. 

