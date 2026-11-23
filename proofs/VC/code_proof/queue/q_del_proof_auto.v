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
From Ucos2Verify.VC.code.queue Require Import q_del_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.queue.spec.q_del_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSQDel_safety_wit_1 : OSQDel_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_OSQDel_safety_wit_2 : OSQDel_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_OSQDel_safety_wit_3 : OSQDel_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_OSQDel_safety_wit_4 : OSQDel_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_OSQDel_safety_wit_5 : OSQDel_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_OSQDel_safety_wit_6 : OSQDel_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_OSQDel_safety_wit_7 : OSQDel_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_OSQDel_safety_wit_8 : OSQDel_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_OSQDel_safety_wit_9 : OSQDel_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_OSQDel_entail_wit_4 : OSQDel_entail_wit_4.
Proof. Admitted. 

Lemma proof_of_OSQDel_entail_wit_5 : OSQDel_entail_wit_5.
Proof. Admitted. 

Lemma proof_of_OSQDel_entail_wit_6 : OSQDel_entail_wit_6.
Proof. Admitted. 

Lemma proof_of_OSQDel_entail_wit_8_1 : OSQDel_entail_wit_8_1.
Proof. Admitted. 

Lemma proof_of_OSQDel_entail_wit_8_2 : OSQDel_entail_wit_8_2.
Proof. Admitted. 

Lemma proof_of_OSQDel_entail_wit_8_3 : OSQDel_entail_wit_8_3.
Proof. Admitted. 

Lemma proof_of_OSQDel_entail_wit_8_4 : OSQDel_entail_wit_8_4.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_1_pure : OSQDel_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_1 : OSQDel_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_2_pure : OSQDel_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_2 : OSQDel_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_3_pure : OSQDel_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_3 : OSQDel_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_4 : OSQDel_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_5_pure : OSQDel_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_5 : OSQDel_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_6_pure : OSQDel_partial_solve_wit_6_pure.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_6 : OSQDel_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_7 : OSQDel_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_8 : OSQDel_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_9_pure : OSQDel_partial_solve_wit_9_pure.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_9 : OSQDel_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_10_pure : OSQDel_partial_solve_wit_10_pure.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_10 : OSQDel_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_11 : OSQDel_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_12 : OSQDel_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_13_pure : OSQDel_partial_solve_wit_13_pure.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_13 : OSQDel_partial_solve_wit_13.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_14 : OSQDel_partial_solve_wit_14.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_15 : OSQDel_partial_solve_wit_15.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_16 : OSQDel_partial_solve_wit_16.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_17_pure : OSQDel_partial_solve_wit_17_pure.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_17 : OSQDel_partial_solve_wit_17.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_18 : OSQDel_partial_solve_wit_18.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_19 : OSQDel_partial_solve_wit_19.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_20_pure : OSQDel_partial_solve_wit_20_pure.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_20 : OSQDel_partial_solve_wit_20.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_21_pure : OSQDel_partial_solve_wit_21_pure.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_21 : OSQDel_partial_solve_wit_21.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_22 : OSQDel_partial_solve_wit_22.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_23_pure : OSQDel_partial_solve_wit_23_pure.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_23 : OSQDel_partial_solve_wit_23.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_24_pure : OSQDel_partial_solve_wit_24_pure.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_24 : OSQDel_partial_solve_wit_24.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_25 : OSQDel_partial_solve_wit_25.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_26 : OSQDel_partial_solve_wit_26.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_27_pure : OSQDel_partial_solve_wit_27_pure.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_27 : OSQDel_partial_solve_wit_27.
Proof. Admitted. 

Lemma proof_of_OSQDel_partial_solve_wit_28 : OSQDel_partial_solve_wit_28.
Proof. Admitted. 

