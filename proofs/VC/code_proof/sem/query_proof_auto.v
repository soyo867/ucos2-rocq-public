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

Lemma proof_of_OSSemQuery_safety_wit_1 : OSSemQuery_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_safety_wit_2 : OSSemQuery_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_safety_wit_3 : OSSemQuery_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_safety_wit_4 : OSSemQuery_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_safety_wit_5 : OSSemQuery_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_safety_wit_6 : OSSemQuery_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_safety_wit_7 : OSSemQuery_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_safety_wit_8 : OSSemQuery_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_safety_wit_9 : OSSemQuery_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_safety_wit_10 : OSSemQuery_safety_wit_10.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_safety_wit_11 : OSSemQuery_safety_wit_11.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_safety_wit_12 : OSSemQuery_safety_wit_12.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_safety_wit_13 : OSSemQuery_safety_wit_13.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_safety_wit_14 : OSSemQuery_safety_wit_14.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_safety_wit_15 : OSSemQuery_safety_wit_15.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_safety_wit_16 : OSSemQuery_safety_wit_16.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_safety_wit_17 : OSSemQuery_safety_wit_17.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_safety_wit_18 : OSSemQuery_safety_wit_18.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_safety_wit_19 : OSSemQuery_safety_wit_19.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_safety_wit_20 : OSSemQuery_safety_wit_20.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_safety_wit_21 : OSSemQuery_safety_wit_21.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_entail_wit_1_1 : OSSemQuery_entail_wit_1_1.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_1_pure : OSSemQuery_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_1 : OSSemQuery_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_2_pure : OSSemQuery_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_2 : OSSemQuery_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_3_pure : OSSemQuery_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_3 : OSSemQuery_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_4_pure : OSSemQuery_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_4 : OSSemQuery_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_5_pure : OSSemQuery_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_5 : OSSemQuery_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_6_pure : OSSemQuery_partial_solve_wit_6_pure.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_6 : OSSemQuery_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_7_pure : OSSemQuery_partial_solve_wit_7_pure.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_7 : OSSemQuery_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_8 : OSSemQuery_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_9_pure : OSSemQuery_partial_solve_wit_9_pure.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_9 : OSSemQuery_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_10_pure : OSSemQuery_partial_solve_wit_10_pure.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_10 : OSSemQuery_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_11_pure : OSSemQuery_partial_solve_wit_11_pure.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_11 : OSSemQuery_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_OSSemQuery_partial_solve_wit_12 : OSSemQuery_partial_solve_wit_12.
Proof. Admitted. 

