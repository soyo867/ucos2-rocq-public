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
From Ucos2Verify.VC.code.queue Require Import q_query_goal.
From Ucos2Verify.VC.code.queue Require Import q_query_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.queue.spec.q_query_api_spec.
Require Import Ucos2Verify.lib.array_abstraction.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSQQuery_entail_wit_1_2_split_goal_1 : OSQQuery_entail_wit_1_2_split_goal_1.
Proof. Abort.

Lemma proof_of_OSQQuery_entail_wit_1_2_split_goal_2 : OSQQuery_entail_wit_1_2_split_goal_2.
Proof. Abort.

Lemma proof_of_OSQQuery_return_wit_1_split_goal_spatial : OSQQuery_return_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSQQuery_return_wit_2_split_goal_spatial : OSQQuery_return_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSQQuery_return_wit_3_split_goal_spatial : OSQQuery_return_wit_3_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSQQuery_return_wit_4_split_goal_spatial : OSQQuery_return_wit_4_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSQQuery_return_wit_5_split_goal_spatial : OSQQuery_return_wit_5_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSQQuery_which_implies_wit_1_split_goal_1 : OSQQuery_which_implies_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_OSQQuery_which_implies_wit_1_split_goal_spatial : OSQQuery_which_implies_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSQQuery_which_implies_wit_2_split_goal_1 : OSQQuery_which_implies_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_OSQQuery_which_implies_wit_2_split_goal_2 : OSQQuery_which_implies_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_OSQQuery_which_implies_wit_2_split_goal_spatial : OSQQuery_which_implies_wit_2_split_goal_spatial.
Proof. Abort.

