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
From Ucos2Verify.VC.code.timer Require Import tmr_alloc_goal.
From Ucos2Verify.VC.code.timer Require Import tmr_alloc_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_alloc_spec.
Import UCOS2_C_Rules.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTmr_Alloc_return_wit_1 : OSTmr_Alloc_return_wit_1.
Proof.
  unfold OSTmr_Alloc_return_wit_1; left; intros.
  unfold tmr_alloc_low_post, tmr_alloc_globals, tmr_alloc_links.
  rewrite !tmr_alloc_unsigned_short_eq.
  Right; entailer!.
Qed.

Lemma proof_of_OSTmr_Alloc_return_wit_2 : OSTmr_Alloc_return_wit_2.
Proof.
  unfold OSTmr_Alloc_return_wit_2; left; intros.
  unfold tmr_alloc_low_post, tmr_alloc_globals, tmr_alloc_links.
  Left; entailer!.
Qed.

Lemma proof_of_OSTmr_Alloc_which_implies_wit_1 : OSTmr_Alloc_which_implies_wit_1.
Proof.
  unfold OSTmr_Alloc_which_implies_wit_1; intros.
  unfold tmr_alloc_low_pre, tmr_alloc_globals, tmr_alloc_links.
  Split; Intros.
  - Right; entailer!.
  - Left; entailer!.
Qed.

