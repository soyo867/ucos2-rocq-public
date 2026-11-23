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
From Ucos2Verify.VC.code.timer Require Import tmr_free_goal.
From Ucos2Verify.VC.code.timer Require Import tmr_free_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_free_spec.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTmr_Free_return_wit_1 : OSTmr_Free_return_wit_1.
Proof.
  unfold OSTmr_Free_return_wit_1; right; intros.
  unfold tmr_free_write_post, Ucos2Verify.lib.kernel_resources.kernel_u16,
    unsigned_last_nbits.
  rewrite Z.mul_0_l, Z.add_0_r.
  entailer!.
Qed.

Lemma proof_of_OSTmr_Free_which_implies_wit_1 : OSTmr_Free_which_implies_wit_1.
Proof.
  unfold OSTmr_Free_which_implies_wit_1; left; intros.
  unfold tmr_free_write_pre; entailer!.
Qed.

Lemma proof_of_OSTmr_Free_derive_raw_spec_by_write_spec : OSTmr_Free_derive_raw_spec_by_write_spec.
Proof.
  unfold OSTmr_Free_derive_raw_spec_by_write_spec.
  intros p LitMap free used root old.
  Exists root used free LitMap.
  apply tmr_free_raw_spec_consequence.
Qed.

Lemma proof_of_OSTmr_Free_derive_valid_pool_spec_by_raw_spec : OSTmr_Free_derive_valid_pool_spec_by_raw_spec.
Proof.
  unfold OSTmr_Free_derive_valid_pool_spec_by_raw_spec.
  intros p LitMap old t i s sg.
  Exists old (timer_id_pointer sg (timerFree s)) (timerUsedCount s)
    (timerFreeCount s) LitMap.
  apply tmr_free_valid_spec_consequence.
Qed.
