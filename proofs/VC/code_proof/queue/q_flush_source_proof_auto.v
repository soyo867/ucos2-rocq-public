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
From Ucos2Verify.VC.code.queue Require Import q_flush_source_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.queue.spec.q_flush_call_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSQFlush_safety_wit_1 : OSQFlush_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_OSQFlush_safety_wit_2 : OSQFlush_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_OSQFlush_safety_wit_3 : OSQFlush_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_OSQFlush_partial_solve_wit_1_pure : OSQFlush_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_OSQFlush_partial_solve_wit_1 : OSQFlush_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OSQFlush_partial_solve_wit_2_pure : OSQFlush_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_OSQFlush_partial_solve_wit_2 : OSQFlush_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OSQFlush_partial_solve_wit_3 : OSQFlush_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_OSQFlush_partial_solve_wit_4_pure : OSQFlush_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_OSQFlush_partial_solve_wit_4 : OSQFlush_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_OSQFlush_partial_solve_wit_5_pure : OSQFlush_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_OSQFlush_partial_solve_wit_5 : OSQFlush_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_OSQFlush_partial_solve_wit_6_pure : OSQFlush_partial_solve_wit_6_pure.
Proof. Admitted. 

Lemma proof_of_OSQFlush_partial_solve_wit_6 : OSQFlush_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_OSQFlush_partial_solve_wit_7_pure : OSQFlush_partial_solve_wit_7_pure.
Proof. Admitted. 

Lemma proof_of_OSQFlush_partial_solve_wit_7 : OSQFlush_partial_solve_wit_7.
Proof. Admitted. 

