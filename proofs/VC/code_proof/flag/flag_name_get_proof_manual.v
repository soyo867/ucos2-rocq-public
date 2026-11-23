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
From Ucos2Verify.VC.code.flag Require Import flag_name_get_goal.
From Ucos2Verify.VC.code.flag Require Import flag_name_get_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.flag.spec.flag_name_get_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSFlagNameGet_entail_wit_1 : OSFlagNameGet_entail_wit_1.
Proof.
  left; intros.
  rewrite uchar_unsigned32_eq__critical_control in PreH6 by lia.
  assert (Hnest : task_name_get_nesting before = 0) by lia.
  assert (Hearly : flag_name_get_early_error pgrp_pre pname_pre
    (task_name_get_nesting before) = None).
  { unfold flag_name_get_early_error.
    rewrite (proj2 (Z.eqb_neq _ _) PreH9),
      (proj2 (Z.eqb_neq _ _) PreH8), Hnest; reflexivity. }
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation before acquired_2 PreH1 PreH10)) as Hvalid.
  unfold flag_name_get_guarded_private; rewrite Hearly.
  Exists acquired_2; unfold UCOS2_inv; entailer!.
Qed.

Lemma proof_of_OSFlagNameGet_return_wit_1 : OSFlagNameGet_return_wit_1.
Proof.
  left; intros.
  unfold task_name_get_restore_post; Intros current.
  destruct H as [Hrelease Hcurrent].
  destruct PreH29 as [_ Hmask]; rewrite Hmask.
  assert (Heffect : flag_name_get_effect sg before acquired pgrp_pre pname_pre
    slot raw retval 0 (Some (flag_name_get_name image))).
  { unfold flag_name_get_effect; rewrite PreH19.
    exists image; split; [exact PreH8|].
    right; split; [exact PreH9|].
    exists chars; split; [exact PreH2|].
    split; [exact PreH3|]; split; reflexivity. }
  assert (Hsafe : flag_name_get_return_safe current retval 0
    (Some (flag_name_get_name image)) X).
  { eapply flag_name_get_safe_return with (before := before) (acquired := acquired).
    - exact Heffect.
    - exact PreH21.
    - eassumption.
    - intros H; contradiction.
    - exact PreH30. }
  unfold flag_name_get_post.
  Exists acquired current 0 (Some (flag_name_get_name image)).
  unfold flag_name_get_guarded_private; rewrite PreH19.
  cbn [task_name_get_output_cell]; entailer!.
Qed.

Lemma proof_of_OSFlagNameGet_return_wit_2 : OSFlagNameGet_return_wit_2.
Proof.
  left; intros.
  rewrite uchar_unsigned32_eq__critical_control in PreH6 by lia.
  unfold task_name_get_restore_post; Intros current.
  destruct H as [Hrelease Hcurrent].
  destruct PreH19 as [_ Hmask]; rewrite Hmask.
  assert (Heffect : flag_name_get_effect sg before acquired pgrp_pre pname_pre
    slot raw 0 1 None).
  { unfold flag_name_get_effect; rewrite PreH9.
    exists image; split; [exact PreH5|].
    left; split; [exact PreH6|]; repeat split; reflexivity. }
  assert (Hsafe : flag_name_get_return_safe current 0 1 None X).
  { eapply flag_name_get_safe_return with (before := before) (acquired := acquired).
    - exact Heffect.
    - exact PreH11.
    - eassumption.
    - intros H; contradiction.
    - exact PreH20. }
  unfold flag_name_get_post; Exists acquired current 1 (@None Z).
  unfold flag_name_get_guarded_private; rewrite PreH9; entailer!.
Qed.

Lemma proof_of_OSFlagNameGet_return_wit_3 : OSFlagNameGet_return_wit_3.
Proof.
  left; intros.
  sep_apply task_name_get_closed_nesting_in_range__critical_control; Intros.
  rewrite uchar_unsigned32_eq__critical_control in PreH2 by lia.
  assert (Hnest : 0 < task_name_get_nesting before) by lia.
  assert (Hearly : flag_name_get_early_error pgrp_pre pname_pre
    (task_name_get_nesting before) = Some 17).
  { unfold flag_name_get_early_error.
    rewrite (proj2 (Z.eqb_neq _ _) PreH5), (proj2 (Z.eqb_neq _ _) PreH4),
      (proj2 (Z.ltb_lt _ _) Hnest); reflexivity. }
  assert (Heffect : flag_name_get_effect sg before before pgrp_pre pname_pre
    slot raw 0 17 None) by (unfold flag_name_get_effect; rewrite Hearly; auto).
  assert (Hinterval : critical_region_interval critical sg invocation before before)
    by constructor.
  assert (Hsafe : flag_name_get_return_safe before 0 17 None X).
  { eapply flag_name_get_safe_return; [exact Heffect|exact Hinterval|
      exact Hinterval|auto|exact PreH9]. }
  unfold flag_name_get_post; Exists before before 17 (@None Z); entailer!.
Qed.

Lemma proof_of_OSFlagNameGet_return_wit_4 : OSFlagNameGet_return_wit_4.
Proof.
  left; intros.
  assert (Hearly : flag_name_get_early_error pgrp_pre pname_pre
    (task_name_get_nesting before) = Some 12).
  { unfold flag_name_get_early_error.
    rewrite (proj2 (Z.eqb_neq _ _) PreH2), PreH1; reflexivity. }
  assert (Heffect : flag_name_get_effect sg before before pgrp_pre pname_pre
    slot raw 0 12 None) by (unfold flag_name_get_effect; rewrite Hearly; auto).
  assert (Hinterval : critical_region_interval critical sg invocation before before)
    by constructor.
  assert (Hsafe : flag_name_get_return_safe before 0 12 None X).
  { eapply flag_name_get_safe_return; [exact Heffect|exact Hinterval|
      exact Hinterval|auto|exact PreH6]. }
  unfold flag_name_get_post; Exists before before 12 (@None Z); entailer!.
Qed.

Lemma proof_of_OSFlagNameGet_return_wit_5 : OSFlagNameGet_return_wit_5.
Proof.
  left; intros.
  assert (Hearly : flag_name_get_early_error pgrp_pre pname_pre
    (task_name_get_nesting before) = Some 110).
  { unfold flag_name_get_early_error; rewrite PreH1; reflexivity. }
  assert (Heffect : flag_name_get_effect sg before before pgrp_pre pname_pre
    slot raw 0 110 None) by (unfold flag_name_get_effect; rewrite Hearly; auto).
  assert (Hinterval : critical_region_interval critical sg invocation before before)
    by constructor.
  assert (Hsafe : flag_name_get_return_safe before 0 110 None X).
  { eapply flag_name_get_safe_return; [exact Heffect|exact Hinterval|
      exact Hinterval|auto|exact PreH5]. }
  unfold flag_name_get_post; Exists before before 110 (@None Z); entailer!.
Qed.

Lemma proof_of_OSFlagNameGet_partial_solve_wit_10_pure : OSFlagNameGet_partial_solve_wit_10_pure.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range
    &((pgrp_pre) # "os_flag_grp" ->ₛ "OSFlagType") (flag_name_get_type image)).
  Intros.
  change (0 <= flag_name_get_type image <= 255) in H.
  rewrite unsigned_last_nbits_eq in PreH1 by
    (change (0 <= flag_name_get_type image < 4294967296); lia).
  entailer!.
Qed.

Lemma proof_of_OSFlagNameGet_which_implies_wit_1 : OSFlagNameGet_which_implies_wit_1.
Proof.
  left; intros; unfold flag_name_get_pre; entailer!.
Qed.

Lemma proof_of_OSFlagNameGet_which_implies_wit_2 : OSFlagNameGet_which_implies_wit_2.
Proof.
  left; intros.
  rewrite task_name_get_closed_raw_rep__resource_stages_strlen,
    task_name_get_raw_rep_split_nesting__resource_stages_strlen.
  pose proof (proj1 PreH1) as Hnest; rewrite Hnest; entailer!.
Qed.

Lemma proof_of_OSFlagNameGet_which_implies_wit_3 : OSFlagNameGet_which_implies_wit_3.
Proof.
  left; intros.
  rewrite task_name_get_closed_raw_rep__resource_stages_strlen,
    task_name_get_raw_rep_split_nesting__resource_stages_strlen.
  pose proof (proj1 PreH1) as Hnest; rewrite Hnest; entailer!.
Qed.

Lemma proof_of_OSFlagNameGet_which_implies_wit_4 : OSFlagNameGet_which_implies_wit_4.
Proof.
  left; intros.
  sep_apply store_uchar_with_range__resource_stages_strlen; Intros.
  rewrite task_name_get_closed_raw_rep__resource_stages_strlen,
    task_name_get_raw_rep_split_nesting__resource_stages_strlen.
  pose proof (proj1 PreH1) as Hnest; rewrite Hnest; entailer!; lia.
Qed.

Lemma proof_of_OSFlagNameGet_which_implies_wit_5 : OSFlagNameGet_which_implies_wit_5.
Proof.
  left; intros; unfold task_name_get_closed; entailer!.
Qed.

Lemma proof_of_OSFlagNameGet_which_implies_wit_6 : OSFlagNameGet_which_implies_wit_6.
Proof.
  left; intros old raw slot invocation before sg critical acquired pgrp pname
    Haddr Hinv Hearly Haccess Hinterval.
  destruct (proj1 (Haccess Hearly acquired Hinterval Hinv)) as [image Hselected].
  pose proof Haddr as Hlayout.
  destruct Hlayout as [Hnest [Htype [Hname [Hflag [Hnames Hoffset]]]]].
  Exists image.
  unfold UCOS2_inv; Intros.
  entailer!.
  rewrite Htype; unfold flag_name_get_type.
  rewrite (flag_name_get_read_equiv sg acquired pgrp slot raw image
    Hflag Hnames Hoffset Hselected).
  unfold flag_name_get_fields; entailer!.
Qed.

Lemma proof_of_OSFlagNameGet_which_implies_wit_7 : OSFlagNameGet_which_implies_wit_7.
Proof.
  left; intros raw slot sg acquired image pgrp Haddr Hinv Hselected.
  prop_apply_p (store_uchar_range
    &((pgrp) # "os_flag_grp" ->ₛ "OSFlagType") (flag_name_get_type image)).
  Intros.
  change (0 <= flag_name_get_type image <= 255) in H.
  pose proof Haddr as Hlayout.
  destruct Hlayout as [Hnest [Htype [Hname [Hflag [Hnames Hoffset]]]]].
  unfold UCOS2_inv; entailer!.
  rewrite Htype; unfold flag_name_get_type.
  pose proof (proj2 (flag_name_get_read_equiv sg acquired pgrp slot raw image
    Hflag Hnames Hoffset Hselected)) as Hmerge.
  unfold flag_name_get_fields in Hmerge.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma proof_of_OSFlagNameGet_which_implies_wit_8 : OSFlagNameGet_which_implies_wit_8.
Proof.
  left; intros old raw slot invocation before sg critical acquired image pgrp pname
    Haddr Hinv Hselected Htype Hearly Haccess Hinterval.
  destruct (proj2 (Haccess Hearly acquired Hinterval Hinv) image Hselected Htype)
    as [previous [chars [Hold Hread]]].
  pose proof Haddr as Hlayout.
  destruct Hlayout as [Hnest [Htypeaddr [Hnameaddr Hconfig]]].
  Exists chars previous.
  unfold flag_name_get_type in Htype.
  unfold flag_name_get_name_cell; rewrite Htype, Z.eqb_refl, Hold.
  unfold task_name_get_output_cell, flag_name_get_name, task_name_get_names.
  entailer!.
  rewrite Hnameaddr; entailer!.
Qed.

Lemma proof_of_OSFlagNameGet_which_implies_wit_9 : OSFlagNameGet_which_implies_wit_9.
Proof.
  left; intros raw slot sg acquired image pgrp Haddr Hinv Hselected Htype.
  pose proof Haddr as Hlayout.
  destruct Hlayout as [Hnest [Htypeaddr [Hnameaddr [Hflag [Hnames Hoffset]]]]].
  unfold UCOS2_inv; entailer!.
  rewrite Htypeaddr, Hnameaddr.
  unfold flag_name_get_type, flag_name_get_name.
  pose proof (proj2 (flag_name_get_read_equiv sg acquired pgrp slot raw image
    Hflag Hnames Hoffset Hselected)) as Hmerge.
  unfold flag_name_get_fields, flag_name_get_name_cell in Hmerge.
  unfold flag_name_get_type in Htype; rewrite Htype, Z.eqb_refl in Hmerge.
  rewrite Htype.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma proof_of_OSFlagNameGet_which_implies_wit_10 : OSFlagNameGet_which_implies_wit_10.
Proof.
  left; intros sg acquired image chars Hinv Hread.
  unfold UCOS2_inv.
  rewrite (flag_name_get_names_equiv sg acquired (flag_name_get_name image) chars Hread).
  entailer!.
Qed.

Lemma proof_of_OSFlagNameGet_which_implies_wit_11 : OSFlagNameGet_which_implies_wit_11.
Proof.
  left; intros; unfold flag_name_get_call_frame, flag_name_get_name; entailer!.
Qed.

Lemma proof_of_OSFlagNameGet_which_implies_wit_12 : OSFlagNameGet_which_implies_wit_12.
Proof.
  left; intros; unfold flag_name_get_call_frame, flag_name_get_name; entailer!.
Qed.

Lemma proof_of_OSFlagNameGet_which_implies_wit_13 : OSFlagNameGet_which_implies_wit_13.
Proof.
  left; intros sg acquired image chars Hinv Hread.
  rewrite <- (flag_name_get_names_equiv sg acquired (flag_name_get_name image) chars Hread).
  unfold UCOS2_inv; entailer!.
Qed.

Lemma proof_of_OS_StrLen_derive_flag_name_get_spec_by_exact_frame_spec : OS_StrLen_derive_flag_name_get_spec_by_exact_frame_spec.
Proof.
  intros psrc frame chars names entry.
  Intros; subst psrc.
  Exists entry entry names chars frame.
  apply derivable1s_emp_sepcon_unfold.
  - destruct (Z.eq_dec entry 0) as [Hzero|Hnonzero].
    + subst entry; Right; unfold task_name_get_name_bytes; simpl; entailer!.
    + Left; unfold task_name_get_name_bytes.
      rewrite (proj2 (Z.eqb_neq entry 0) Hnonzero).
      entailer!; apply H0; exact Hnonzero.
  - apply_sepcon_adjoint.
    Split.
    + Intros retval; subst.
      Exists 0; unfold task_name_get_name_bytes, task_name_get_length; simpl; entailer!.
    + Intros retval.
      Exists retval.
      unfold task_name_get_name_bytes, task_name_get_length.
      assert (Hnonzero : entry <> 0) by assumption.
      rewrite (proj2 (Z.eqb_neq entry 0) Hnonzero).
      unfold os_strlen_result in *; entailer!.
Qed.

