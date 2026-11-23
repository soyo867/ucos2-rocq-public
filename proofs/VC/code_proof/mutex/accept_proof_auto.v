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
From Ucos2Verify.VC.code.mutex Require Import accept_goal.
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
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_accept_modular_spec.
Local Open Scope sac.

Lemma proof_of_OSMutexAccept_safety_wit_1 : OSMutexAccept_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_safety_wit_2 : OSMutexAccept_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_safety_wit_3 : OSMutexAccept_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_safety_wit_4 : OSMutexAccept_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_safety_wit_6 : OSMutexAccept_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_safety_wit_7 : OSMutexAccept_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_safety_wit_8 : OSMutexAccept_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_safety_wit_9 : OSMutexAccept_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_1_pure : OSMutexAccept_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_1 : OSMutexAccept_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_2 : OSMutexAccept_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_3_pure : OSMutexAccept_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_3 : OSMutexAccept_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_4_pure : OSMutexAccept_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_4 : OSMutexAccept_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_5_pure : OSMutexAccept_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_5 : OSMutexAccept_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_6_pure : OSMutexAccept_partial_solve_wit_6_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_6 : OSMutexAccept_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_7_pure : OSMutexAccept_partial_solve_wit_7_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_7 : OSMutexAccept_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_8 : OSMutexAccept_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_9 : OSMutexAccept_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_10_pure : OSMutexAccept_partial_solve_wit_10_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_10 : OSMutexAccept_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_11 : OSMutexAccept_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_12 : OSMutexAccept_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_13_pure : OSMutexAccept_partial_solve_wit_13_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_13 : OSMutexAccept_partial_solve_wit_13.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_14_pure : OSMutexAccept_partial_solve_wit_14_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_14 : OSMutexAccept_partial_solve_wit_14.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_15_pure : OSMutexAccept_partial_solve_wit_15_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_15 : OSMutexAccept_partial_solve_wit_15.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_16_pure : OSMutexAccept_partial_solve_wit_16_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexAccept_partial_solve_wit_16 : OSMutexAccept_partial_solve_wit_16.
Proof. Admitted. 

