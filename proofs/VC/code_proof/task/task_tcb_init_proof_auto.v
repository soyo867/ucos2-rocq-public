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
From Ucos2Verify.VC.code.task Require Import task_tcb_init_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_App_TaskCreateHook_return_wit_1 : App_TaskCreateHook_return_wit_1.
Proof. Admitted. 

Lemma proof_of_App_TCBInitHook_return_wit_1 : App_TCBInitHook_return_wit_1.
Proof. Admitted. 

Lemma proof_of_OSTCBInitHook_return_wit_1 : OSTCBInitHook_return_wit_1.
Proof. Admitted. 

Lemma proof_of_OSTCBInitHook_partial_solve_wit_1 : OSTCBInitHook_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OSTaskCreateHook_return_wit_1 : OSTaskCreateHook_return_wit_1.
Proof. Admitted. 

Lemma proof_of_OSTaskCreateHook_partial_solve_wit_1 : OSTaskCreateHook_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_safety_wit_1 : OS_TCBInit_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_safety_wit_2 : OS_TCBInit_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_safety_wit_3 : OS_TCBInit_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_safety_wit_7 : OS_TCBInit_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_safety_wit_8 : OS_TCBInit_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_safety_wit_9 : OS_TCBInit_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_safety_wit_10 : OS_TCBInit_safety_wit_10.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_safety_wit_11 : OS_TCBInit_safety_wit_11.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_safety_wit_12 : OS_TCBInit_safety_wit_12.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_safety_wit_13 : OS_TCBInit_safety_wit_13.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_safety_wit_14 : OS_TCBInit_safety_wit_14.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_safety_wit_15 : OS_TCBInit_safety_wit_15.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_partial_solve_wit_1 : OS_TCBInit_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_partial_solve_wit_2 : OS_TCBInit_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_partial_solve_wit_3_pure : OS_TCBInit_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_partial_solve_wit_3 : OS_TCBInit_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_partial_solve_wit_4 : OS_TCBInit_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_partial_solve_wit_5 : OS_TCBInit_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_partial_solve_wit_6 : OS_TCBInit_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_partial_solve_wit_7 : OS_TCBInit_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_partial_solve_wit_8 : OS_TCBInit_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_partial_solve_wit_9 : OS_TCBInit_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_partial_solve_wit_10 : OS_TCBInit_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_partial_solve_wit_11_pure : OS_TCBInit_partial_solve_wit_11_pure.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_partial_solve_wit_11 : OS_TCBInit_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_partial_solve_wit_12_pure : OS_TCBInit_partial_solve_wit_12_pure.
Proof. Admitted. 

Lemma proof_of_OS_TCBInit_partial_solve_wit_12 : OS_TCBInit_partial_solve_wit_12.
Proof. Admitted. 

