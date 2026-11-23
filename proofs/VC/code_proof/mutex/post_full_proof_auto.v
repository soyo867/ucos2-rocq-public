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
From Ucos2Verify.VC.code.mutex Require Import post_full_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.mutex_func_sem.
Require Import Ucos2Verify.lib.mutex_rdyatprio_spec.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.mutex_post_spec.
Local Open Scope sac.

Lemma proof_of_OSMutexPost_full_safety_wit_1 : OSMutexPost_full_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_safety_wit_2 : OSMutexPost_full_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_safety_wit_3 : OSMutexPost_full_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_safety_wit_4 : OSMutexPost_full_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_safety_wit_5 : OSMutexPost_full_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_safety_wit_6 : OSMutexPost_full_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_safety_wit_7 : OSMutexPost_full_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_safety_wit_9 : OSMutexPost_full_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_safety_wit_10 : OSMutexPost_full_safety_wit_10.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_safety_wit_11 : OSMutexPost_full_safety_wit_11.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_1_pure : OSMutexPost_full_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_1 : OSMutexPost_full_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_2_pure : OSMutexPost_full_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_2 : OSMutexPost_full_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_3_pure : OSMutexPost_full_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_3 : OSMutexPost_full_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_4_pure : OSMutexPost_full_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_4 : OSMutexPost_full_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_5 : OSMutexPost_full_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_6 : OSMutexPost_full_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_7 : OSMutexPost_full_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_8 : OSMutexPost_full_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_9_pure : OSMutexPost_full_partial_solve_wit_9_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_9 : OSMutexPost_full_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_10 : OSMutexPost_full_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_11 : OSMutexPost_full_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_12 : OSMutexPost_full_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_13 : OSMutexPost_full_partial_solve_wit_13.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_14_pure : OSMutexPost_full_partial_solve_wit_14_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_14 : OSMutexPost_full_partial_solve_wit_14.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_15_pure : OSMutexPost_full_partial_solve_wit_15_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_15 : OSMutexPost_full_partial_solve_wit_15.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_16 : OSMutexPost_full_partial_solve_wit_16.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_17_pure : OSMutexPost_full_partial_solve_wit_17_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_17 : OSMutexPost_full_partial_solve_wit_17.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_18 : OSMutexPost_full_partial_solve_wit_18.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_19 : OSMutexPost_full_partial_solve_wit_19.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_20 : OSMutexPost_full_partial_solve_wit_20.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_21 : OSMutexPost_full_partial_solve_wit_21.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_22 : OSMutexPost_full_partial_solve_wit_22.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_23 : OSMutexPost_full_partial_solve_wit_23.
Proof. Admitted. 

Lemma proof_of_OSMutexPost_full_partial_solve_wit_24 : OSMutexPost_full_partial_solve_wit_24.
Proof. Admitted. 

