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
From Ucos2Verify.VC.code.mutex Require Import rdyatprio_full_goal.
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
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.mutex_rdyatprio_spec.
Require Import Ucos2Verify.lib.array_abstraction.
Local Open Scope sac.

Lemma proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_1_pure : OSMutex_RdyAtPrio_full_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_1 : OSMutex_RdyAtPrio_full_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_2_pure : OSMutex_RdyAtPrio_full_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_2 : OSMutex_RdyAtPrio_full_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_3_noncurrent_owner : OSMutex_RdyAtPrio_full_partial_solve_wit_3_noncurrent_owner.
Proof. Admitted. 

Lemma proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_4_noncurrent_owner : OSMutex_RdyAtPrio_full_partial_solve_wit_4_noncurrent_owner.
Proof. Admitted. 

Lemma proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_5_current_owner : OSMutex_RdyAtPrio_full_partial_solve_wit_5_current_owner.
Proof. Admitted. 

Lemma proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_6_current_owner : OSMutex_RdyAtPrio_full_partial_solve_wit_6_current_owner.
Proof. Admitted. 

Lemma proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_7_current_owner : OSMutex_RdyAtPrio_full_partial_solve_wit_7_current_owner.
Proof. Admitted. 

Lemma proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_8_current_owner : OSMutex_RdyAtPrio_full_partial_solve_wit_8_current_owner.
Proof. Admitted. 

Lemma proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_9_noncurrent_owner : OSMutex_RdyAtPrio_full_partial_solve_wit_9_noncurrent_owner.
Proof. Admitted. 

Lemma proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_10_noncurrent_owner : OSMutex_RdyAtPrio_full_partial_solve_wit_10_noncurrent_owner.
Proof. Admitted. 

