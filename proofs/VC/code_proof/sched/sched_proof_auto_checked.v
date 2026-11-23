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
From Ucos2Verify.VC.code.sched Require Import sched_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OS_Sched_safety_wit_1 : OS_Sched_safety_wit_1.
Proof.
  unfold OS_Sched_safety_wit_1; intros.
  entailer!; try lia; try tauto.
Qed. 

Lemma proof_of_OS_Sched_safety_wit_2 : OS_Sched_safety_wit_2.
Proof.
  unfold OS_Sched_safety_wit_2; intros.
  entailer!; try lia; try tauto.
Qed. 

Lemma proof_of_OS_Sched_partial_solve_wit_1 : OS_Sched_partial_solve_wit_1.
Proof.
  unfold OS_Sched_partial_solve_wit_1; intros.
  entailer!; try lia; try tauto.
Qed. 

Lemma proof_of_OS_Sched_partial_solve_wit_2 : OS_Sched_partial_solve_wit_2.
Proof.
  unfold OS_Sched_partial_solve_wit_2; intros.
  entailer!; try lia; try tauto.
Qed. 

Lemma proof_of_OS_Sched_partial_solve_wit_3 : OS_Sched_partial_solve_wit_3.
Proof.
  unfold OS_Sched_partial_solve_wit_3, OS_Sched_partial_solve_wit_3_aux; intros.
  assert (Haddresses : sched_new_global_addresses sg
    (&("OSUnMapTbl")) (&("OSRdyGrp")) (&("OSRdyTbl")) (&("OSPrioHighRdy"))).
  { unfold os_sched_global_addresses in PreH3; tauto. }
  entailer!; try lia; try tauto.
Qed. 

Lemma proof_of_OS_Sched_partial_solve_wit_4 : OS_Sched_partial_solve_wit_4.
Proof.
  unfold OS_Sched_partial_solve_wit_4; intros.
  sep_apply (PtrArray.full_split_to_missing_i (&("OSTCBPrioTbl"))
    (os_sched_selected entry) 64 (os_sched_table sg entry) 0 ltac:(lia)).
  entailer!; try lia; try tauto.
Qed. 

Lemma proof_of_OS_Sched_partial_solve_wit_5_pure : OS_Sched_partial_solve_wit_5_pure.
Proof.
  unfold OS_Sched_partial_solve_wit_5_pure; intros.
  entailer!; try lia; try tauto.
Qed. 

Lemma proof_of_OS_Sched_partial_solve_wit_5 : OS_Sched_partial_solve_wit_5.
Proof.
  unfold OS_Sched_partial_solve_wit_5, OS_Sched_partial_solve_wit_5_aux; intros.
  entailer!; try lia; try tauto.
Qed. 

Lemma proof_of_OS_Sched_partial_solve_wit_6_pure : OS_Sched_partial_solve_wit_6_pure.
Proof.
  unfold OS_Sched_partial_solve_wit_6_pure; intros.
  entailer!; try lia; try tauto.
Qed. 

Lemma proof_of_OS_Sched_partial_solve_wit_6 : OS_Sched_partial_solve_wit_6.
Proof.
  unfold OS_Sched_partial_solve_wit_6, OS_Sched_partial_solve_wit_6_aux; intros.
  entailer!; try lia; try tauto.
Qed. 

