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
From Ucos2Verify.VC.code.sem Require Import query_goal.
From Ucos2Verify.VC.code.sem Require Import query_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.memory.
Require Import Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.statistics.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_source_api_spec.
Local Open Scope sac.

Lemma proof_of_OSSemQuery_entail_wit_1_2_split_goal_1 : OSSemQuery_entail_wit_1_2_split_goal_1.
Proof. Abort.

Lemma proof_of_OSSemQuery_entail_wit_1_2_split_goal_2 : OSSemQuery_entail_wit_1_2_split_goal_2.
Proof. Abort.

Lemma proof_of_OSSemQuery_return_wit_1_split_goal_spatial : OSSemQuery_return_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSSemQuery_return_wit_2_split_goal_spatial : OSSemQuery_return_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSSemQuery_return_wit_3_split_goal_spatial : OSSemQuery_return_wit_3_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSSemQuery_return_wit_4_split_goal_spatial : OSSemQuery_return_wit_4_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSSemQuery_which_implies_wit_1_split_goal_1 : OSSemQuery_which_implies_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_OSSemQuery_which_implies_wit_1_split_goal_spatial : OSSemQuery_which_implies_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSSemQuery_which_implies_wit_2_split_goal_1 : OSSemQuery_which_implies_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_OSSemQuery_which_implies_wit_2_split_goal_2 : OSSemQuery_which_implies_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_OSSemQuery_which_implies_wit_2_split_goal_spatial : OSSemQuery_which_implies_wit_2_split_goal_spatial.
Proof. Abort.

