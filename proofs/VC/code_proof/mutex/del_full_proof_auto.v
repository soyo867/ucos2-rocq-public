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
From Ucos2Verify.VC.code.mutex Require Import del_full_goal.
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
Require Import Ucos2Verify.lib.mutex_del_spec.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Local Open Scope sac.

Lemma proof_of_OSMutexDel_RefreshHighReady_safety_wit_1 : OSMutexDel_RefreshHighReady_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_RefreshHighReady_return_wit_1 : OSMutexDel_RefreshHighReady_return_wit_1.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_RefreshHighReady_return_wit_2 : OSMutexDel_RefreshHighReady_return_wit_2.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_1 : OSMutexDel_RefreshHighReady_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_2 : OSMutexDel_RefreshHighReady_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_3 : OSMutexDel_RefreshHighReady_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_4 : OSMutexDel_RefreshHighReady_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_5 : OSMutexDel_RefreshHighReady_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_6_pure : OSMutexDel_RefreshHighReady_partial_solve_wit_6_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_6 : OSMutexDel_RefreshHighReady_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_7_pure : OSMutexDel_RefreshHighReady_partial_solve_wit_7_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_7 : OSMutexDel_RefreshHighReady_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_8 : OSMutexDel_RefreshHighReady_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_9_pure : OSMutexDel_RefreshHighReady_partial_solve_wit_9_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_9 : OSMutexDel_RefreshHighReady_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_10_pure : OSMutexDel_RefreshHighReady_partial_solve_wit_10_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_10 : OSMutexDel_RefreshHighReady_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_11 : OSMutexDel_RefreshHighReady_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_12 : OSMutexDel_RefreshHighReady_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_13 : OSMutexDel_RefreshHighReady_partial_solve_wit_13.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_safety_wit_1 : OSMutexDel_full_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_safety_wit_2 : OSMutexDel_full_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_safety_wit_4 : OSMutexDel_full_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_safety_wit_5 : OSMutexDel_full_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_safety_wit_6 : OSMutexDel_full_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_safety_wit_8 : OSMutexDel_full_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_safety_wit_9 : OSMutexDel_full_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_safety_wit_11 : OSMutexDel_full_safety_wit_11.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_safety_wit_12 : OSMutexDel_full_safety_wit_12.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_entail_wit_10 : OSMutexDel_full_entail_wit_10.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_1_pure : OSMutexDel_full_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_1 : OSMutexDel_full_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_2 : OSMutexDel_full_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_3_pure : OSMutexDel_full_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_3 : OSMutexDel_full_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_4_pure : OSMutexDel_full_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_4 : OSMutexDel_full_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_5_pure : OSMutexDel_full_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_5 : OSMutexDel_full_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_6 : OSMutexDel_full_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_7_pure : OSMutexDel_full_partial_solve_wit_7_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_7 : OSMutexDel_full_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_8 : OSMutexDel_full_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_9_pure : OSMutexDel_full_partial_solve_wit_9_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_9 : OSMutexDel_full_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_10_pure : OSMutexDel_full_partial_solve_wit_10_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_10 : OSMutexDel_full_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_11_pure : OSMutexDel_full_partial_solve_wit_11_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_11 : OSMutexDel_full_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_12 : OSMutexDel_full_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_13_pure : OSMutexDel_full_partial_solve_wit_13_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_13 : OSMutexDel_full_partial_solve_wit_13.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_14 : OSMutexDel_full_partial_solve_wit_14.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_15 : OSMutexDel_full_partial_solve_wit_15.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_16 : OSMutexDel_full_partial_solve_wit_16.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_17 : OSMutexDel_full_partial_solve_wit_17.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_18 : OSMutexDel_full_partial_solve_wit_18.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_19_pure : OSMutexDel_full_partial_solve_wit_19_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_19 : OSMutexDel_full_partial_solve_wit_19.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_20_pure : OSMutexDel_full_partial_solve_wit_20_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_20 : OSMutexDel_full_partial_solve_wit_20.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_21_pure : OSMutexDel_full_partial_solve_wit_21_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_21 : OSMutexDel_full_partial_solve_wit_21.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_22 : OSMutexDel_full_partial_solve_wit_22.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_23 : OSMutexDel_full_partial_solve_wit_23.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_24_pure : OSMutexDel_full_partial_solve_wit_24_pure.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_24 : OSMutexDel_full_partial_solve_wit_24.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_25 : OSMutexDel_full_partial_solve_wit_25.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_26 : OSMutexDel_full_partial_solve_wit_26.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_27 : OSMutexDel_full_partial_solve_wit_27.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_28 : OSMutexDel_full_partial_solve_wit_28.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_29 : OSMutexDel_full_partial_solve_wit_29.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_30 : OSMutexDel_full_partial_solve_wit_30.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_31 : OSMutexDel_full_partial_solve_wit_31.
Proof. Admitted. 

Lemma proof_of_OSMutexDel_full_partial_solve_wit_32 : OSMutexDel_full_partial_solve_wit_32.
Proof. Admitted. 

