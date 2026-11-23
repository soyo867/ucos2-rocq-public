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
From Ucos2Verify.VC.code.queue Require Import q_pend_abort_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.queue.spec.q_pend_abort_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSQPendAbort_safety_wit_1 : OSQPendAbort_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_safety_wit_2 : OSQPendAbort_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_safety_wit_3 : OSQPendAbort_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_safety_wit_4 : OSQPendAbort_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_safety_wit_5 : OSQPendAbort_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_safety_wit_6 : OSQPendAbort_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_safety_wit_7 : OSQPendAbort_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_entail_wit_2 : OSQPendAbort_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_entail_wit_3 : OSQPendAbort_entail_wit_3.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_entail_wit_4 : OSQPendAbort_entail_wit_4.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_entail_wit_5_1 : OSQPendAbort_entail_wit_5_1.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_entail_wit_6_1 : OSQPendAbort_entail_wit_6_1.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_1_pure : OSQPendAbort_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_1 : OSQPendAbort_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_2_pure : OSQPendAbort_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_2 : OSQPendAbort_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_3 : OSQPendAbort_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_4_pure : OSQPendAbort_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_4 : OSQPendAbort_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_5 : OSQPendAbort_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_6 : OSQPendAbort_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_7 : OSQPendAbort_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_8_pure : OSQPendAbort_partial_solve_wit_8_pure.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_8 : OSQPendAbort_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_9 : OSQPendAbort_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_10_pure : OSQPendAbort_partial_solve_wit_10_pure.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_10 : OSQPendAbort_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_11 : OSQPendAbort_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_12 : OSQPendAbort_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_13_pure : OSQPendAbort_partial_solve_wit_13_pure.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_13 : OSQPendAbort_partial_solve_wit_13.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_14_pure : OSQPendAbort_partial_solve_wit_14_pure.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_14 : OSQPendAbort_partial_solve_wit_14.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_15_pure : OSQPendAbort_partial_solve_wit_15_pure.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_15 : OSQPendAbort_partial_solve_wit_15.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_16_pure : OSQPendAbort_partial_solve_wit_16_pure.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_16 : OSQPendAbort_partial_solve_wit_16.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_17_pure : OSQPendAbort_partial_solve_wit_17_pure.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_17 : OSQPendAbort_partial_solve_wit_17.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_18 : OSQPendAbort_partial_solve_wit_18.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_19_pure : OSQPendAbort_partial_solve_wit_19_pure.
Proof. Admitted. 

Lemma proof_of_OSQPendAbort_partial_solve_wit_19 : OSQPendAbort_partial_solve_wit_19.
Proof. Admitted. 

