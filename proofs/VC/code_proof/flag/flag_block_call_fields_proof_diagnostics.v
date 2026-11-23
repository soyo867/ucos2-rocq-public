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
From Ucos2Verify.VC.code.flag Require Import flag_block_call_fields_goal.
From Ucos2Verify.VC.code.flag Require Import flag_block_call_fields_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_storage Ucos2Verify.lib.sched Ucos2Verify.lib.flag Ucos2Verify.lib.flag_execution.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_fields_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope sac.

Lemma proof_of_OS_FlagBlock_entail_wit_1_1_split_goal_spatial : OS_FlagBlock_entail_wit_1_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OS_FlagBlock_entail_wit_1_2_split_goal_spatial : OS_FlagBlock_entail_wit_1_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OS_FlagBlock_entail_wit_2_1_split_goal_spatial : OS_FlagBlock_entail_wit_2_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OS_FlagBlock_entail_wit_2_2_split_goal_spatial : OS_FlagBlock_entail_wit_2_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OS_FlagBlock_which_implies_wit_3_split_goal_spatial : OS_FlagBlock_which_implies_wit_3_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OS_FlagBlock_which_implies_wit_4_split_goal_spatial : OS_FlagBlock_which_implies_wit_4_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OS_FlagBlock_which_implies_wit_5_split_goal_spatial : OS_FlagBlock_which_implies_wit_5_split_goal_spatial.
Proof. Abort.

