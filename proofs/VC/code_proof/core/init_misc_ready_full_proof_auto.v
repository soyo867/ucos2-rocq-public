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
From Ucos2Verify.VC.code.core Require Import init_misc_ready_full_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.core.spec.init_misc_spec.
Import UCOS2_C_Rules.
Require Import Ucos2Verify.VC.code.sched.spec.init_rdy_list_spec.
Import Ucos2Verify.lib.ucos2_rules_lib.UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OS_InitRdyList_safety_wit_1 : OS_InitRdyList_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_OS_InitRdyList_safety_wit_2 : OS_InitRdyList_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_OS_InitRdyList_safety_wit_3 : OS_InitRdyList_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_OS_InitRdyList_entail_wit_1 : OS_InitRdyList_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_OS_InitRdyList_entail_wit_2 : OS_InitRdyList_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_OS_InitRdyList_partial_solve_wit_1 : OS_InitRdyList_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OS_InitRdyList_partial_solve_wit_2_pure : OS_InitRdyList_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_OS_InitRdyList_partial_solve_wit_2 : OS_InitRdyList_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OS_InitRdyList_partial_solve_wit_3_pure : OS_InitRdyList_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_OS_InitRdyList_partial_solve_wit_3 : OS_InitRdyList_partial_solve_wit_3.
Proof. Admitted. 

