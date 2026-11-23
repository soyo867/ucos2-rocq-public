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
From Ucos2Verify.VC.code.flag Require Import flag_block_call_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_storage Ucos2Verify.lib.sched Ucos2Verify.lib.flag Ucos2Verify.lib.flag_execution.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope sac.

Lemma proof_of_OS_FlagBlock_safety_wit_1 : OS_FlagBlock_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_OS_FlagBlock_safety_wit_2 : OS_FlagBlock_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_OS_FlagBlock_return_wit_1 : OS_FlagBlock_return_wit_1.
Proof. Admitted. 

Lemma proof_of_OS_FlagBlock_partial_solve_wit_1_pure : OS_FlagBlock_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_OS_FlagBlock_partial_solve_wit_1 : OS_FlagBlock_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OS_FlagBlock_partial_solve_wit_2_pure : OS_FlagBlock_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_OS_FlagBlock_partial_solve_wit_2 : OS_FlagBlock_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OS_FlagBlock_partial_solve_wit_3_pure : OS_FlagBlock_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_OS_FlagBlock_partial_solve_wit_3 : OS_FlagBlock_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_OS_FlagBlock_partial_solve_wit_4_pure : OS_FlagBlock_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_OS_FlagBlock_partial_solve_wit_4 : OS_FlagBlock_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_OS_FlagBlock_partial_solve_wit_5_pure : OS_FlagBlock_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_OS_FlagBlock_partial_solve_wit_5 : OS_FlagBlock_partial_solve_wit_5.
Proof. Admitted. 

