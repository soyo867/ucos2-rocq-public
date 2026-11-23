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
From Ucos2Verify.VC.code.queue Require Import q_init_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.VC.code.queue.spec.q_init_spec.
Local Open Scope sac.

Lemma proof_of_OS_QInit_safety_wit_1 : OS_QInit_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_OS_QInit_safety_wit_2 : OS_QInit_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_OS_QInit_safety_wit_3 : OS_QInit_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_OS_QInit_partial_solve_wit_1 : OS_QInit_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OS_QInit_partial_solve_wit_2 : OS_QInit_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OS_QInit_partial_solve_wit_3 : OS_QInit_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_OS_QInit_partial_solve_wit_4_pure : OS_QInit_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_OS_QInit_partial_solve_wit_4 : OS_QInit_partial_solve_wit_4.
Proof. Admitted. 

