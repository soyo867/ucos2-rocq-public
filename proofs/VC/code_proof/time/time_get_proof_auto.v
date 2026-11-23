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
From Ucos2Verify.VC.code.time Require Import time_get_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.time.spec.time_get_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSTimeGet_safety_wit_1 : OSTimeGet_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_OSTimeGet_safety_wit_2 : OSTimeGet_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_OSTimeGet_partial_solve_wit_1 : OSTimeGet_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OSTimeGet_partial_solve_wit_2_pure : OSTimeGet_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeGet_partial_solve_wit_2 : OSTimeGet_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OSTimeGet_partial_solve_wit_3_pure : OSTimeGet_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeGet_partial_solve_wit_3 : OSTimeGet_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_OSTimeGet_partial_solve_wit_4_pure : OSTimeGet_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_OSTimeGet_partial_solve_wit_4 : OSTimeGet_partial_solve_wit_4.
Proof. Admitted. 

