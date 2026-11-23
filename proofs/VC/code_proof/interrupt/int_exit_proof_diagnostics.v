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
From Ucos2Verify.VC.code.interrupt Require Import int_exit_goal.
From Ucos2Verify.VC.code.interrupt Require Import int_exit_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSIntExit_entail_wit_1_1_split_goal_1 : OSIntExit_entail_wit_1_1_split_goal_1.
Proof. Abort.

Lemma proof_of_OSIntExit_entail_wit_1_2_split_goal_1 : OSIntExit_entail_wit_1_2_split_goal_1.
Proof. Abort.

Lemma proof_of_OSIntExit_return_wit_2_split_goal_spatial : OSIntExit_return_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_OSIntExit_partial_solve_wit_2_pure_split_goal_1 : OSIntExit_partial_solve_wit_2_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_OSIntExit_which_implies_wit_1_split_goal_1 : OSIntExit_which_implies_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_OSIntExit_which_implies_wit_1_split_goal_2 : OSIntExit_which_implies_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_OSIntExit_which_implies_wit_1_split_goal_3 : OSIntExit_which_implies_wit_1_split_goal_3.
Proof. Abort.

Lemma proof_of_OSIntExit_which_implies_wit_1_split_goal_spatial : OSIntExit_which_implies_wit_1_split_goal_spatial.
Proof. Abort.

