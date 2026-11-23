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
From Ucos2Verify.VC.code.flag Require Import flag_accept_goal.
From Ucos2Verify.VC.code.flag Require Import flag_accept_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.flag.spec.flag_accept_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSFlagAccept_entail_wit_1 : OSFlagAccept_entail_wit_1.
Proof.
  left; intros.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range (&("wait_type")) wait_type_pre).
  prop_apply_p (UCOS2_C_Rules.store_ushort_range (&("flags")) flags_pre).
  Intros.
  entailer!; try lia; unfold UINT_MAX; lia.
Qed.

Lemma proof_of_OSFlagAccept_entail_wit_2_1 : OSFlagAccept_entail_wit_2_1.
Proof.
  left; intros.
  pose proof (byte_clear_high_bit_eq_low_mask__entry_acquire wait_type_pre
    ltac:(lia)) as Hmode.
  pose proof (land_power_of_two_testbit__entry_acquire wait_type_pre 7
    ltac:(lia)) as Hbit.
  change (Z.land wait_type_pre 128 =
    if Z.testbit wait_type_pre 7 then 128 else 0) in Hbit.
  assert (Hconsume : 1 = flag_accept_consume_value wait_type_pre).
  { unfold flag_accept_consume_value.
    destruct (Z.testbit wait_type_pre 7); congruence. }
  subst pgrp_pre perr_pre requested wait_request.
  unfold flag_accept_mode, flag_accept_consume_bit in *.
  entailer!; congruence.
Qed.

Lemma proof_of_OSFlagAccept_entail_wit_2_2 : OSFlagAccept_entail_wit_2_2.
Proof.
  left; intros.
  pose proof (byte_clear_high_bit_eq_low_mask__entry_acquire wait_type_pre
    ltac:(lia)) as Hclear.
  pose proof (Z.lor_ldiff_and wait_type_pre 128) as Hmode.
  rewrite Z.ldiff_land, PreH2, Z.lor_0_r, Hclear in Hmode.
  pose proof (land_power_of_two_testbit__entry_acquire wait_type_pre 7
    ltac:(lia)) as Hbit.
  change (Z.land wait_type_pre 128 =
    if Z.testbit wait_type_pre 7 then 128 else 0) in Hbit.
  assert (Hconsume : 0 = flag_accept_consume_value wait_type_pre).
  { unfold flag_accept_consume_value.
    destruct (Z.testbit wait_type_pre 7); congruence. }
  subst pgrp_pre perr_pre requested wait_request.
  unfold flag_accept_mode, flag_accept_consume_bit in *.
  entailer!; congruence.
Qed.

Lemma proof_of_OSFlagAccept_entail_wit_3_1 : OSFlagAccept_entail_wit_3_1.
Proof.
  left; intros.
  unfold flag_accept_bits_frame; Intros.
  match goal with H : flag_accept_acquired_facts _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hfacts;
    pose proof H as [Hprofile [_ [_ [_ [_ [_ Hold]]]]]]
  end.
  destruct Hprofile as [_ [_ [Hwidth [Hclear _]]]].
  assert (Hready : 0 <= (Z.land (flagImageBits image) requested) <= 65535)
    by (apply land_mask_word16_in_range__flag_bit_effects; lia).
  rewrite land_word16_truncate_right_eq__flag_bit_effects by exact Hold.
  assert (Hpost : 0 <= (Z.land (flagImageBits image) (Z.lnot (Z.land (flagImageBits image) requested))) <= 65535).
  { rewrite Z.land_comm; apply land_mask_word16_in_range__flag_bit_effects; exact Hold. }
  assert (Hmode : Z.land wait_request 127 = 2)
    by (unfold flag_accept_mode in *; lia).
  assert (Hconsume : Z.testbit wait_request 7 = true).
  { rewrite PreH9 in PreH1; unfold flag_accept_consume_value in PreH1.
    destruct (Z.testbit wait_request 7); [reflexivity|vm_compute in PreH1; discriminate]. }
  assert (Heffect : flag_accept_effect sg image requested wait_request
    (Z.land (flagImageBits image) (Z.lnot (Z.land (flagImageBits image) requested))) (Z.land (flagImageBits image) requested) 0).
  { exists Ucos2Verify.lib.error_codes.OS_ERR_NONE; split; [|reflexivity].
    unfold flag_accept_bits, decode_flag_wait_mode; rewrite Hmode.
    cbn [Z.eqb Pos.eqb]; unfold flag_ready_bits.
    rewrite flag_word16_eq__flag_bit_effects by assumption.
    unfold flag_wait_satisfied.
    rewrite (proj2 (Z.eqb_eq _ _) PreH2), Hconsume.
    unfold flag_consume_bits; rewrite flag_word16_eq__flag_bit_effects by assumption.
    reflexivity. }
  Exists 0 (Z.land (flagImageBits image) (Z.lnot (Z.land (flagImageBits image) requested))).
  unfold flag_accept_checkpoint_facts; entailer!.
Qed.

Lemma proof_of_OSFlagAccept_entail_wit_3_2 : OSFlagAccept_entail_wit_3_2.
Proof.
  left; intros.
  unfold flag_accept_bits_frame; Intros.
  match goal with H : flag_accept_acquired_facts _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hfacts;
    pose proof H as [Hprofile [_ [_ [_ [_ [_ Hold]]]]]]
  end.
  destruct Hprofile as [_ [_ [Hwidth [Hclear _]]]].
  assert (Hready : 0 <= (Z.land (flagImageBits image) requested) <= 65535)
    by (apply land_mask_word16_in_range__flag_bit_effects; lia).
  assert (Hmode : Z.land wait_request 127 = 2)
    by (unfold flag_accept_mode in *; lia).
  assert (Hconsume : Z.testbit wait_request 7 = false).
  { rewrite PreH9 in PreH1; unfold flag_accept_consume_value in PreH1.
    destruct (Z.testbit wait_request 7); [vm_compute in PreH1; contradiction|reflexivity]. }
  assert (Heffect : flag_accept_effect sg image requested wait_request
    (flagImageBits image) (Z.land (flagImageBits image) requested) 0).
  { exists Ucos2Verify.lib.error_codes.OS_ERR_NONE; split; [|reflexivity].
    unfold flag_accept_bits, decode_flag_wait_mode; rewrite Hmode.
    cbn [Z.eqb Pos.eqb]; unfold flag_ready_bits.
    rewrite flag_word16_eq__flag_bit_effects by assumption.
    unfold flag_wait_satisfied.
    rewrite (proj2 (Z.eqb_eq _ _) PreH2), Hconsume.
    reflexivity. }
  Exists 0 (flagImageBits image).
  unfold flag_accept_checkpoint_facts; entailer!.
Qed.

Lemma proof_of_OSFlagAccept_entail_wit_3_3 : OSFlagAccept_entail_wit_3_3.
Proof.
  left; intros.
  unfold flag_accept_bits_frame; Intros.
  match goal with H : flag_accept_acquired_facts _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hfacts;
    pose proof H as [Hprofile [_ [_ [_ [_ [_ Hold]]]]]]
  end.
  destruct Hprofile as [_ [_ [Hwidth [Hclear _]]]].
  assert (Hready : 0 <= (Z.land (flagImageBits image) requested) <= 65535)
    by (apply land_mask_word16_in_range__flag_bit_effects; lia).
  assert (Hmode : Z.land wait_request 127 = 2)
    by (unfold flag_accept_mode in *; lia).
  assert (Heffect : flag_accept_effect sg image requested wait_request
    (flagImageBits image) (Z.land (flagImageBits image) requested) 112).
  { exists Ucos2Verify.lib.error_codes.OS_ERR_FLAG_NOT_RDY; split; [|reflexivity].
    unfold flag_accept_bits, decode_flag_wait_mode; rewrite Hmode.
    cbn [Z.eqb Pos.eqb]; unfold flag_ready_bits.
    rewrite flag_word16_eq__flag_bit_effects by assumption.
    unfold flag_wait_satisfied.
    rewrite (proj2 (Z.eqb_neq _ _) PreH1).
    reflexivity. }
  Exists 112 (flagImageBits image).
  unfold flag_accept_checkpoint_facts; entailer!.
Qed.

Lemma proof_of_OSFlagAccept_entail_wit_4_1 : OSFlagAccept_entail_wit_4_1.
Proof.
  left; intros.
  unfold flag_accept_bits_frame; Intros.
  match goal with H : flag_accept_acquired_facts _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hfacts;
    pose proof H as [Hprofile [_ [_ [_ [_ [_ Hold]]]]]]
  end.
  destruct Hprofile as [_ [_ [Hwidth [Hclear _]]]].
  assert (Hready : 0 <= (Z.land (flagImageBits image) requested) <= 65535)
    by (apply land_mask_word16_in_range__flag_bit_effects; lia).
  rewrite land_word16_truncate_right_eq__flag_bit_effects by exact Hold.
  assert (Hpost : 0 <= (Z.land (flagImageBits image) (Z.lnot (Z.land (flagImageBits image) requested))) <= 65535).
  { rewrite Z.land_comm; apply land_mask_word16_in_range__flag_bit_effects; exact Hold. }
  assert (Hmode : Z.land wait_request 127 = 3)
    by (unfold flag_accept_mode in *; lia).
  assert (Hconsume : Z.testbit wait_request 7 = true).
  { rewrite PreH9 in PreH1; unfold flag_accept_consume_value in PreH1.
    destruct (Z.testbit wait_request 7); [reflexivity|vm_compute in PreH1; discriminate]. }
  assert (Heffect : flag_accept_effect sg image requested wait_request
    (Z.land (flagImageBits image) (Z.lnot (Z.land (flagImageBits image) requested))) (Z.land (flagImageBits image) requested) 0).
  { exists Ucos2Verify.lib.error_codes.OS_ERR_NONE; split; [|reflexivity].
    unfold flag_accept_bits, decode_flag_wait_mode; rewrite Hmode.
    cbn [Z.eqb Pos.eqb]; unfold flag_ready_bits.
    rewrite flag_word16_eq__flag_bit_effects by assumption.
    unfold flag_wait_satisfied.
    rewrite (proj2 (Z.eqb_neq _ _) PreH2), Hconsume; cbn [negb].
    unfold flag_consume_bits; rewrite flag_word16_eq__flag_bit_effects by assumption.
    reflexivity. }
  Exists 0 (Z.land (flagImageBits image) (Z.lnot (Z.land (flagImageBits image) requested))).
  unfold flag_accept_checkpoint_facts; entailer!.
Qed.

Lemma proof_of_OSFlagAccept_entail_wit_4_2 : OSFlagAccept_entail_wit_4_2.
Proof.
  left; intros.
  unfold flag_accept_bits_frame; Intros.
  match goal with H : flag_accept_acquired_facts _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hfacts;
    pose proof H as [Hprofile [_ [_ [_ [_ [_ Hold]]]]]]
  end.
  destruct Hprofile as [_ [_ [Hwidth [Hclear _]]]].
  assert (Hready : 0 <= (Z.land (flagImageBits image) requested) <= 65535)
    by (apply land_mask_word16_in_range__flag_bit_effects; lia).
  assert (Hmode : Z.land wait_request 127 = 3)
    by (unfold flag_accept_mode in *; lia).
  assert (Hconsume : Z.testbit wait_request 7 = false).
  { rewrite PreH9 in PreH1; unfold flag_accept_consume_value in PreH1.
    destruct (Z.testbit wait_request 7); [vm_compute in PreH1; contradiction|reflexivity]. }
  assert (Heffect : flag_accept_effect sg image requested wait_request
    (flagImageBits image) (Z.land (flagImageBits image) requested) 0).
  { exists Ucos2Verify.lib.error_codes.OS_ERR_NONE; split; [|reflexivity].
    unfold flag_accept_bits, decode_flag_wait_mode; rewrite Hmode.
    cbn [Z.eqb Pos.eqb]; unfold flag_ready_bits.
    rewrite flag_word16_eq__flag_bit_effects by assumption.
    unfold flag_wait_satisfied.
    rewrite (proj2 (Z.eqb_neq _ _) PreH2), Hconsume; cbn [negb].
    reflexivity. }
  Exists 0 (flagImageBits image).
  unfold flag_accept_checkpoint_facts; entailer!.
Qed.

Lemma proof_of_OSFlagAccept_entail_wit_4_3 : OSFlagAccept_entail_wit_4_3.
Proof.
  left; intros.
  unfold flag_accept_bits_frame; Intros.
  match goal with H : flag_accept_acquired_facts _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hfacts;
    pose proof H as [Hprofile [_ [_ [_ [_ [_ Hold]]]]]]
  end.
  destruct Hprofile as [_ [_ [Hwidth [Hclear _]]]].
  assert (Hready : 0 <= (Z.land (flagImageBits image) requested) <= 65535)
    by (apply land_mask_word16_in_range__flag_bit_effects; lia).
  assert (Hmode : Z.land wait_request 127 = 3)
    by (unfold flag_accept_mode in *; lia).
  assert (Heffect : flag_accept_effect sg image requested wait_request
    (flagImageBits image) (Z.land (flagImageBits image) requested) 112).
  { exists Ucos2Verify.lib.error_codes.OS_ERR_FLAG_NOT_RDY; split; [|reflexivity].
    unfold flag_accept_bits, decode_flag_wait_mode; rewrite Hmode.
    cbn [Z.eqb Pos.eqb]; unfold flag_ready_bits.
    rewrite flag_word16_eq__flag_bit_effects by assumption.
    unfold flag_wait_satisfied.
    rewrite (proj2 (Z.eqb_eq _ _) PreH1); cbn [negb].
    reflexivity. }
  Exists 112 (flagImageBits image).
  unfold flag_accept_checkpoint_facts; entailer!.
Qed.

Lemma proof_of_OSFlagAccept_entail_wit_5_1 : OSFlagAccept_entail_wit_5_1.
Proof.
  left; intros.
  unfold flag_accept_bits_frame; Intros.
  match goal with H : flag_accept_acquired_facts _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hfacts;
    pose proof H as [Hprofile [_ [_ [_ [_ [_ Hold]]]]]]
  end.
  destruct Hprofile as [_ [_ [Hwidth [Hclear _]]]].
  assert (Hready : 0 <= (Z.land (Z.lnot (flagImageBits image)) requested) <= 65535)
    by (apply land_mask_word16_in_range__flag_bit_effects; lia).
  rewrite unsigned_last_nbits_eq by (change (0 <= flagImageBits image < 65536); lia).
  set (postbits := Z.lor (flagImageBits image) (Z.land (Z.lnot (flagImageBits image)) requested)).
  assert (Hmod : postbits mod 2 ^ 16 = postbits).
  { unfold postbits; rewrite <- Z.land_ones by lia.
    rewrite Z.land_lor_distr_l, !Z.land_ones by lia.
    rewrite !Z.mod_small by lia; reflexivity. }
  assert (Hpost : 0 <= postbits <= 65535).
  { pose proof (Z.mod_pos_bound postbits (2 ^ 16) ltac:(lia)) as Hbound.
    rewrite Hmod in Hbound; change (0 <= postbits < 65536) in Hbound; lia. }
  assert (Hmode : Z.land wait_request 127 = 0)
    by (unfold flag_accept_mode in *; lia).
  assert (Hconsume : Z.testbit wait_request 7 = true).
  { rewrite PreH9 in PreH1; unfold flag_accept_consume_value in PreH1.
    destruct (Z.testbit wait_request 7); [reflexivity|vm_compute in PreH1; discriminate]. }
  assert (Heffect : flag_accept_effect sg image requested wait_request
    postbits (Z.land (Z.lnot (flagImageBits image)) requested) 0).
  { exists Ucos2Verify.lib.error_codes.OS_ERR_NONE; split; [|reflexivity].
    unfold flag_accept_bits, decode_flag_wait_mode; rewrite Hmode.
    cbn [Z.eqb Pos.eqb]; rewrite Hclear; cbn [Z.eqb Pos.eqb]; unfold flag_ready_bits.
    rewrite flag_word16_eq__flag_bit_effects by assumption.
    unfold flag_wait_satisfied.
    rewrite (proj2 (Z.eqb_eq _ _) PreH2), Hconsume.
    unfold flag_consume_bits; fold postbits; rewrite flag_word16_eq__flag_bit_effects by assumption.
    reflexivity. }
  Exists 0 postbits.
  unfold flag_accept_checkpoint_facts; entailer!.
Qed.

Lemma proof_of_OSFlagAccept_entail_wit_5_2 : OSFlagAccept_entail_wit_5_2.
Proof.
  left; intros.
  unfold flag_accept_bits_frame; Intros.
  match goal with H : flag_accept_acquired_facts _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hfacts;
    pose proof H as [Hprofile [_ [_ [_ [_ [_ Hold]]]]]]
  end.
  destruct Hprofile as [_ [_ [Hwidth [Hclear _]]]].
  assert (Hready : 0 <= (Z.land (Z.lnot (flagImageBits image)) requested) <= 65535)
    by (apply land_mask_word16_in_range__flag_bit_effects; lia).
  assert (Hmode : Z.land wait_request 127 = 0)
    by (unfold flag_accept_mode in *; lia).
  assert (Hconsume : Z.testbit wait_request 7 = false).
  { rewrite PreH9 in PreH1; unfold flag_accept_consume_value in PreH1.
    destruct (Z.testbit wait_request 7); [vm_compute in PreH1; contradiction|reflexivity]. }
  assert (Heffect : flag_accept_effect sg image requested wait_request
    (flagImageBits image) (Z.land (Z.lnot (flagImageBits image)) requested) 0).
  { exists Ucos2Verify.lib.error_codes.OS_ERR_NONE; split; [|reflexivity].
    unfold flag_accept_bits, decode_flag_wait_mode; rewrite Hmode.
    cbn [Z.eqb Pos.eqb]; rewrite Hclear; cbn [Z.eqb Pos.eqb]; unfold flag_ready_bits.
    rewrite flag_word16_eq__flag_bit_effects by assumption.
    unfold flag_wait_satisfied.
    rewrite (proj2 (Z.eqb_eq _ _) PreH2), Hconsume.
    reflexivity. }
  Exists 0 (flagImageBits image).
  unfold flag_accept_checkpoint_facts; entailer!.
Qed.

Lemma proof_of_OSFlagAccept_entail_wit_5_3 : OSFlagAccept_entail_wit_5_3.
Proof.
  left; intros.
  unfold flag_accept_bits_frame; Intros.
  match goal with H : flag_accept_acquired_facts _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hfacts;
    pose proof H as [Hprofile [_ [_ [_ [_ [_ Hold]]]]]]
  end.
  destruct Hprofile as [_ [_ [Hwidth [Hclear _]]]].
  assert (Hready : 0 <= (Z.land (Z.lnot (flagImageBits image)) requested) <= 65535)
    by (apply land_mask_word16_in_range__flag_bit_effects; lia).
  assert (Hmode : Z.land wait_request 127 = 0)
    by (unfold flag_accept_mode in *; lia).
  assert (Heffect : flag_accept_effect sg image requested wait_request
    (flagImageBits image) (Z.land (Z.lnot (flagImageBits image)) requested) 112).
  { exists Ucos2Verify.lib.error_codes.OS_ERR_FLAG_NOT_RDY; split; [|reflexivity].
    unfold flag_accept_bits, decode_flag_wait_mode; rewrite Hmode.
    cbn [Z.eqb Pos.eqb]; rewrite Hclear; cbn [Z.eqb Pos.eqb]; unfold flag_ready_bits.
    rewrite flag_word16_eq__flag_bit_effects by assumption.
    unfold flag_wait_satisfied.
    rewrite (proj2 (Z.eqb_neq _ _) PreH1).
    reflexivity. }
  Exists 112 (flagImageBits image).
  unfold flag_accept_checkpoint_facts; entailer!.
Qed.

Lemma proof_of_OSFlagAccept_entail_wit_6_1 : OSFlagAccept_entail_wit_6_1.
Proof.
  left; intros.
  unfold flag_accept_bits_frame; Intros.
  match goal with H : flag_accept_acquired_facts _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hfacts;
    pose proof H as [Hprofile [_ [_ [_ [_ [_ Hold]]]]]]
  end.
  destruct Hprofile as [_ [_ [Hwidth [Hclear _]]]].
  assert (Hready : 0 <= (Z.land (Z.lnot (flagImageBits image)) requested) <= 65535)
    by (apply land_mask_word16_in_range__flag_bit_effects; lia).
  rewrite unsigned_last_nbits_eq by (change (0 <= flagImageBits image < 65536); lia).
  set (postbits := Z.lor (flagImageBits image) (Z.land (Z.lnot (flagImageBits image)) requested)).
  assert (Hmod : postbits mod 2 ^ 16 = postbits).
  { unfold postbits; rewrite <- Z.land_ones by lia.
    rewrite Z.land_lor_distr_l, !Z.land_ones by lia.
    rewrite !Z.mod_small by lia; reflexivity. }
  assert (Hpost : 0 <= postbits <= 65535).
  { pose proof (Z.mod_pos_bound postbits (2 ^ 16) ltac:(lia)) as Hbound.
    rewrite Hmod in Hbound; change (0 <= postbits < 65536) in Hbound; lia. }
  assert (Hmode : Z.land wait_request 127 = 1)
    by (unfold flag_accept_mode in *; lia).
  assert (Hconsume : Z.testbit wait_request 7 = true).
  { rewrite PreH9 in PreH1; unfold flag_accept_consume_value in PreH1.
    destruct (Z.testbit wait_request 7); [reflexivity|vm_compute in PreH1; discriminate]. }
  assert (Heffect : flag_accept_effect sg image requested wait_request
    postbits (Z.land (Z.lnot (flagImageBits image)) requested) 0).
  { exists Ucos2Verify.lib.error_codes.OS_ERR_NONE; split; [|reflexivity].
    unfold flag_accept_bits, decode_flag_wait_mode; rewrite Hmode.
    cbn [Z.eqb Pos.eqb]; rewrite Hclear; cbn [Z.eqb Pos.eqb]; unfold flag_ready_bits.
    rewrite flag_word16_eq__flag_bit_effects by assumption.
    unfold flag_wait_satisfied.
    rewrite (proj2 (Z.eqb_neq _ _) PreH2), Hconsume; cbn [negb].
    unfold flag_consume_bits; fold postbits; rewrite flag_word16_eq__flag_bit_effects by assumption.
    reflexivity. }
  Exists 0 postbits.
  unfold flag_accept_checkpoint_facts; entailer!.
Qed.

Lemma proof_of_OSFlagAccept_entail_wit_6_2 : OSFlagAccept_entail_wit_6_2.
Proof.
  left; intros.
  unfold flag_accept_bits_frame; Intros.
  match goal with H : flag_accept_acquired_facts _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hfacts;
    pose proof H as [Hprofile [_ [_ [_ [_ [_ Hold]]]]]]
  end.
  destruct Hprofile as [_ [_ [Hwidth [Hclear _]]]].
  assert (Hready : 0 <= (Z.land (Z.lnot (flagImageBits image)) requested) <= 65535)
    by (apply land_mask_word16_in_range__flag_bit_effects; lia).
  assert (Hmode : Z.land wait_request 127 = 1)
    by (unfold flag_accept_mode in *; lia).
  assert (Hconsume : Z.testbit wait_request 7 = false).
  { rewrite PreH9 in PreH1; unfold flag_accept_consume_value in PreH1.
    destruct (Z.testbit wait_request 7); [vm_compute in PreH1; contradiction|reflexivity]. }
  assert (Heffect : flag_accept_effect sg image requested wait_request
    (flagImageBits image) (Z.land (Z.lnot (flagImageBits image)) requested) 0).
  { exists Ucos2Verify.lib.error_codes.OS_ERR_NONE; split; [|reflexivity].
    unfold flag_accept_bits, decode_flag_wait_mode; rewrite Hmode.
    cbn [Z.eqb Pos.eqb]; rewrite Hclear; cbn [Z.eqb Pos.eqb]; unfold flag_ready_bits.
    rewrite flag_word16_eq__flag_bit_effects by assumption.
    unfold flag_wait_satisfied.
    rewrite (proj2 (Z.eqb_neq _ _) PreH2), Hconsume; cbn [negb].
    reflexivity. }
  Exists 0 (flagImageBits image).
  unfold flag_accept_checkpoint_facts; entailer!.
Qed.

Lemma proof_of_OSFlagAccept_entail_wit_6_3 : OSFlagAccept_entail_wit_6_3.
Proof.
  left; intros.
  unfold flag_accept_bits_frame; Intros.
  match goal with H : flag_accept_acquired_facts _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hfacts;
    pose proof H as [Hprofile [_ [_ [_ [_ [_ Hold]]]]]]
  end.
  destruct Hprofile as [_ [_ [Hwidth [Hclear _]]]].
  assert (Hready : 0 <= (Z.land (Z.lnot (flagImageBits image)) requested) <= 65535)
    by (apply land_mask_word16_in_range__flag_bit_effects; lia).
  assert (Hmode : Z.land wait_request 127 = 1)
    by (unfold flag_accept_mode in *; lia).
  assert (Heffect : flag_accept_effect sg image requested wait_request
    (flagImageBits image) (Z.land (Z.lnot (flagImageBits image)) requested) 112).
  { exists Ucos2Verify.lib.error_codes.OS_ERR_FLAG_NOT_RDY; split; [|reflexivity].
    unfold flag_accept_bits, decode_flag_wait_mode; rewrite Hmode.
    cbn [Z.eqb Pos.eqb]; rewrite Hclear; cbn [Z.eqb Pos.eqb]; unfold flag_ready_bits.
    rewrite flag_word16_eq__flag_bit_effects by assumption.
    unfold flag_wait_satisfied.
    rewrite (proj2 (Z.eqb_eq _ _) PreH1); cbn [negb].
    reflexivity. }
  Exists 112 (flagImageBits image).
  unfold flag_accept_checkpoint_facts; entailer!.
Qed.

Lemma proof_of_OSFlagAccept_entail_wit_7 : OSFlagAccept_entail_wit_7.
Proof.
  left; intros.
  unfold flag_accept_bits_frame; Intros.
  match goal with Hfacts : flag_accept_acquired_facts _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof Hfacts as [Hprofile [Hpe [Htype [Hadmission [Hacquire [Himage Holdrange]]]]]] end.
  assert (Hmode2 : (flag_accept_mode wait_request =? 2) = false)
    by (apply Z.eqb_neq; lia).
  assert (Hmode3 : (flag_accept_mode wait_request =? 3) = false)
    by (apply Z.eqb_neq; lia).
  assert (Hmode0 : (flag_accept_mode wait_request =? 0) = false)
    by (apply Z.eqb_neq; lia).
  assert (Hmode1 : (flag_accept_mode wait_request =? 1) = false)
    by (apply Z.eqb_neq; lia).
  assert (Heffect : flag_accept_effect sg image requested wait_request
    (flagImageBits image) 0 111).
  { unfold flag_accept_effect.
    exists Ucos2Verify.lib.error_codes.OS_ERR_FLAG_WAIT_TYPE; split; [|reflexivity].
    unfold flag_accept_bits, decode_flag_wait_mode.
    fold (flag_accept_mode wait_request).
    rewrite Hmode2, Hmode3.
    destruct (cfgFlagClearWait (osKernelConfig sg));
      rewrite ?Hmode0, ?Hmode1; reflexivity. }
  unfold flag_accept_checkpoint_facts; entailer!.
Qed.

Lemma proof_of_OSFlagAccept_return_wit_6 : OSFlagAccept_return_wit_6.
Proof.
  left; intros.
  assert (Htype : flagImageType observed <> 5).
  { intro Htype; apply PreH1; rewrite Htype; reflexivity. }
  subst perr_pre.
  sep_apply_l_atomic (flag_accept_type_error_api_post platform critical sg invocation
    origin irq_mask view pe error_addr before observed requested wait_request X
    PreH3 Htype PreH10).
  entailer!.
Qed.

Lemma proof_of_OSFlagAccept_return_wit_7 : OSFlagAccept_return_wit_7.
Proof.
  left; intros.
  assert (Hpe : pe = 0) by lia.
  rewrite Hpe in *; subst perr_pre.
  sep_apply_l_atomic (flag_accept_null_api_post platform critical sg invocation
    origin irq_mask view error_addr before observed requested wait_request X PreH7).
  entailer!.
Qed.

Lemma proof_of_OSFlagAccept_partial_solve_wit_3_pure : OSFlagAccept_partial_solve_wit_3_pure.
Proof.
  left; intros.
  assert (Htype : flagImageType observed <> 5).
  { intro Htype; apply PreH1; rewrite Htype; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSFlagAccept_partial_solve_wit_4_pure : OSFlagAccept_partial_solve_wit_4_pure.
Proof.
  left; intros.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range
    (&((pgrp_pre) # "os_flag_grp" ->ₛ "OSFlagType")) (flagImageType observed)).
  Intros.
  change (0 <= flagImageType observed <= 255) in H.
  rewrite unsigned_last_nbits_eq in PreH1 by
    (change (0 <= flagImageType observed < 4294967296); lia).
  entailer!.
Qed.

Lemma proof_of_OSFlagAccept_which_implies_wit_1 : OSFlagAccept_which_implies_wit_1.
Proof.
  left; intros.
  assert (Haddress : forall p, (&(p # "os_flag_grp" ->ₛ "OSFlagType")) = p)
    by (unfold flag_accept_profile in PreH1; tauto).
  rewrite Haddress.
  rewrite (flag_accept_before_split_type platform critical sg invocation origin
    irq_mask view pe before observed PreH1 PreH2).
  entailer!.
Qed.

Lemma proof_of_OSFlagAccept_which_implies_wit_2 : OSFlagAccept_which_implies_wit_2.
Proof.
  left; intros.
  assert (Haddress : forall p, (&(p # "os_flag_grp" ->ₛ "OSFlagType")) = p)
    by (unfold flag_accept_profile in PreH1; tauto).
  rewrite Haddress.
  unfold flag_accept_before_resource, flag_accept_type_frame.
  rewrite (proj2 (Z.eqb_neq _ _) PreH2), (proj2 (Z.eqb_neq _ _) PreH3).
  entailer!.
Qed.

Lemma proof_of_OSFlagAccept_which_implies_wit_3 : OSFlagAccept_which_implies_wit_3.
Proof.
  left; intros.
  assert (Haddress : forall p, (&(p # "os_flag_grp" ->ₛ "OSFlagType")) = p)
    by (unfold flag_accept_profile in PreH1; tauto).
  rewrite Haddress.
  rewrite (flag_accept_type_merge_success platform critical sg invocation origin
    irq_mask view pe before observed PreH1 PreH2).
  entailer!.
Qed.

Lemma proof_of_OSFlagAccept_which_implies_wit_4 : OSFlagAccept_which_implies_wit_4.
Proof.
  left; intros.
  assert (Haddress : forall p, (&(p # "os_flag_grp" ->ₛ "OSFlagFlags")) = p + 8)
    by (unfold flag_accept_profile in PreH1; tauto).
  rewrite Haddress.
  rewrite (flag_accept_acquired_split_bits platform critical sg invocation origin
    irq_mask cpu_sr view pe before observed entry_2 PreH1 PreH2 PreH3 PreH4 PreH5).
  Intros image; Exists entry_2 image; entailer!.
Qed.

Lemma proof_of_OSFlagAccept_which_implies_wit_5 : OSFlagAccept_which_implies_wit_5.
Proof.
  left; intros.
  assert (Hfacts : flag_accept_bits_frame platform critical sg invocation origin irq_mask
    saved view pe before observed entry image |--
    coq_prop (flag_accept_acquired_facts critical sg invocation irq_mask saved view pe
      before observed entry image)).
  { unfold flag_accept_bits_frame; entailer!. }
  prop_apply_p Hfacts; Intros.
  match goal with H : flag_accept_acquired_facts _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as [Hprofile _] end.
  destruct Hprofile as [_ [_ [Hwidth [_ [_ [_ Haddress]]]]]].
  rewrite Haddress.
  assert (Hrange : flag_word_in_range (osKernelConfig sg) bits).
  { unfold flag_word_in_range; rewrite Hwidth; cbn; lia. }
  sep_apply_l_atomic (flag_accept_bits_merge_restore platform critical sg invocation origin
    irq_mask saved view pe before observed entry image bits Hrange).
  entailer!.
Qed.

Lemma proof_of_OSFlagAccept_which_implies_wit_6 : OSFlagAccept_which_implies_wit_6.
Proof. left; intros; eapply flag_accept_restore_api_post; eauto. Qed.

Lemma proof_of_OSFlagAccept_which_implies_wit_7 : OSFlagAccept_which_implies_wit_7.
Proof.
  left; intros.
  assert (Hfacts : flag_accept_bits_frame platform critical sg invocation origin irq_mask
    saved view pe before observed entry image |--
    coq_prop (flag_accept_acquired_facts critical sg invocation irq_mask saved view pe
      before observed entry image)).
  { unfold flag_accept_bits_frame; entailer!. }
  prop_apply_p Hfacts; Intros.
  match goal with H : flag_accept_acquired_facts _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as [Hprofile _] end.
  destruct Hprofile as [_ [_ [Hwidth [_ [_ [_ Haddress]]]]]].
  rewrite Haddress.
  assert (Hrange : flag_word_in_range (osKernelConfig sg) bits).
  { unfold flag_word_in_range; rewrite Hwidth; cbn; lia. }
  sep_apply_l_atomic (flag_accept_bits_merge_restore platform critical sg invocation origin
    irq_mask saved view pe before observed entry image bits Hrange).
  entailer!.
Qed.

Lemma proof_of_OSFlagAccept_which_implies_wit_8 : OSFlagAccept_which_implies_wit_8.
Proof. left; intros; eapply flag_accept_restore_api_post; eauto. Qed.

Lemma proof_of_OSFlagAccept_which_implies_wit_9 : OSFlagAccept_which_implies_wit_9.
Proof.
  left; intros.
  assert (Hfacts : flag_accept_bits_frame platform critical sg invocation origin irq_mask
    saved view pe before observed entry image |--
    coq_prop (flag_accept_acquired_facts critical sg invocation irq_mask saved view pe
      before observed entry image)).
  { unfold flag_accept_bits_frame; entailer!. }
  prop_apply_p Hfacts; Intros.
  match goal with H : flag_accept_acquired_facts _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as [Hprofile _] end.
  destruct Hprofile as [_ [_ [Hwidth [_ [_ [_ Haddress]]]]]].
  rewrite Haddress.
  assert (Hrange : flag_word_in_range (osKernelConfig sg) bits).
  { unfold flag_word_in_range; rewrite Hwidth; cbn; lia. }
  sep_apply_l_atomic (flag_accept_bits_merge_restore platform critical sg invocation origin
    irq_mask saved view pe before observed entry image bits Hrange).
  entailer!.
Qed.

Lemma proof_of_OSFlagAccept_which_implies_wit_10 : OSFlagAccept_which_implies_wit_10.
Proof. left; intros; eapply flag_accept_restore_api_post; eauto. Qed.

Lemma proof_of_OSFlagAccept_which_implies_wit_11 : OSFlagAccept_which_implies_wit_11.
Proof.
  left; intros.
  assert (Hfacts : flag_accept_bits_frame platform critical sg invocation origin irq_mask
    saved view pe before observed entry image |--
    coq_prop (flag_accept_acquired_facts critical sg invocation irq_mask saved view pe
      before observed entry image)).
  { unfold flag_accept_bits_frame; entailer!. }
  prop_apply_p Hfacts; Intros.
  match goal with H : flag_accept_acquired_facts _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as [Hprofile _] end.
  destruct Hprofile as [_ [_ [Hwidth [_ [_ [_ Haddress]]]]]].
  rewrite Haddress.
  assert (Hrange : flag_word_in_range (osKernelConfig sg) bits).
  { unfold flag_word_in_range; rewrite Hwidth; cbn; lia. }
  sep_apply_l_atomic (flag_accept_bits_merge_restore platform critical sg invocation origin
    irq_mask saved view pe before observed entry image bits Hrange).
  entailer!.
Qed.

Lemma proof_of_OSFlagAccept_which_implies_wit_12 : OSFlagAccept_which_implies_wit_12.
Proof. left; intros; eapply flag_accept_restore_api_post; eauto. Qed.

Lemma proof_of_OSFlagAccept_which_implies_wit_13 : OSFlagAccept_which_implies_wit_13.
Proof. left; intros; eapply flag_accept_restore_api_post; eauto. Qed.

Lemma proof_of_OSFlagAccept_which_implies_wit_14 : OSFlagAccept_which_implies_wit_14.
Proof.
  left; intros.
  assert (Hfacts : flag_accept_bits_frame platform critical sg invocation origin irq_mask
    saved view pe before observed entry image |--
    coq_prop (flag_accept_acquired_facts critical sg invocation irq_mask saved view pe
      before observed entry image)).
  { unfold flag_accept_bits_frame; entailer!. }
  prop_apply_p Hfacts; Intros.
  match goal with H : flag_accept_acquired_facts _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as [Hprofile _] end.
  destruct Hprofile as [_ [_ [Hwidth [_ [_ [_ Haddress]]]]]].
  rewrite Haddress.
  assert (Hrange : flag_word_in_range (osKernelConfig sg) (flagImageBits image)).
  { unfold flag_word_in_range; rewrite Hwidth; cbn; lia. }
  sep_apply_l_atomic (flag_accept_bits_merge_restore platform critical sg invocation origin
    irq_mask saved view pe before observed entry image (flagImageBits image) Hrange).
  entailer!.
Qed.

