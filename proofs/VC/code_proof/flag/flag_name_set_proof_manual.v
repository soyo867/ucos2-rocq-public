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
From Ucos2Verify.VC.code.flag Require Import flag_name_set_goal.
From Ucos2Verify.VC.code.flag Require Import flag_name_set_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.flag.spec.flag_name_set_spec.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSFlagNameSet_entail_wit_1 : OSFlagNameSet_entail_wit_1.
Proof.
  left; intros; subst perr_pre pname_pre pgrp_pre.
  pose proof PreH1 as Hacquire.
  destruct Hacquire as [Hinterval [Hbefore [Hentry Hsaved]]].
  destruct (flag_name_set_acquired_image critical sg invocation p name view before entry_2
    PreH9 PreH8 PreH18 PreH17 Hentry Hinterval) as [image [Haccess Hready]].
  pose proof (proj1 (proj1 (proj2 (proj2 Haccess)))) as Htype_address.
  Exists image entry_2.
  rewrite Htype_address.
  entailer!.
  sep_apply_r_atomic (flag_name_set_type_split sg p view entry_2 image Haccess).
  entailer!.
Qed.

Lemma proof_of_OSFlagNameSet_entail_wit_2 : OSFlagNameSet_entail_wit_2.
Proof.
  left; intros.
  destruct PreH7 as [Hvalid [Hnames [[Htype_address Hname_address] [Haddress Hselected]]]] eqn:Haccess.
  rewrite Htype_address.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range p (flagImageType image)).
  Intros.
  assert (Hrange : 0 <= flagImageType image < 2 ^ 32) by (change (0 <= flagImageType image <= 255) in H; lia).
  rewrite (SimpleC.SL.IntLib.unsigned_last_nbits_eq _ _ Hrange) in PreH1.
  assert (Haccess_full : flag_name_set_access sg p view entry image).
  { unfold flag_name_set_access, flag_name_set_layout; auto. }
  pose proof (flag_name_set_step_wrong_type view name entry image Hselected PreH1) as Hstep.
  rewrite <- (flag_name_set_wrong_type_rep_eq p view entry image Hselected PreH1).
  sep_apply_l_atomic (flag_name_set_type_merge sg p view entry image Haccess_full).
  entailer!.
Qed.

Lemma proof_of_OSFlagNameSet_entail_wit_3 : OSFlagNameSet_entail_wit_3.
Proof.
  left; intros.
  pose proof (proj2 (proj1 (proj2 (proj2 PreH1)))) as Hname_address.
  pose proof (proj2 (proj2 (proj2 (proj2 PreH1)))) as Hselected.
  pose proof (PreH10 PreH2) as Havailable.
  pose proof (flag_name_set_step_success view name entry image Hselected PreH2) as Hstep.
  rewrite Hname_address.
  sep_apply_l_atomic (flag_name_set_name_merge_updated sg p view entry image name
    PreH1 PreH2 Havailable).
  entailer!.
Qed.

Lemma proof_of_OSFlagNameSet_return_wit_1 : OSFlagNameSet_return_wit_1.
Proof.
  left; intros.
  exact (flag_name_set_protected_return platform critical sg invocation origin mask cpu_sr
    view p name error_addr before entry 0 (flag_name_set_update view entry image name)
    X caller_frame PreH1 PreH2 PreH3 PreH4 PreH5 PreH6).
Qed.

Lemma proof_of_OSFlagNameSet_return_wit_2 : OSFlagNameSet_return_wit_2.
Proof.
  left; intros.
  exact (flag_name_set_protected_return platform critical sg invocation origin mask cpu_sr
    view p name error_addr before entry 1 entry X caller_frame
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6).
Qed.

Lemma proof_of_OSFlagNameSet_return_wit_3 : OSFlagNameSet_return_wit_3.
Proof.
  left; intros; subst pgrp_pre pname_pre perr_pre.
  assert (Hnest : 0 < task_name_set_nesting before) by lia.
  pose proof (flag_name_set_isr_return platform critical sg invocation origin mask
    view p name error_addr before X caller_frame PreH8 PreH7 Hnest PreH12) as Hreturn.
  sep_apply_r_atomic Hreturn; entailer!.
Qed.

Lemma proof_of_OSFlagNameSet_return_wit_4 : OSFlagNameSet_return_wit_4.
Proof.
  left; intros; subst pgrp_pre pname_pre perr_pre; subst name.
  pose proof (flag_name_set_program_null_name critical sg invocation view p before PreH2)
    as Hprogram.
  pose proof (flag_name_set_safe_return critical sg invocation view p 0 before 12 before X
    Hprogram PreH6) as Hreturn.
  unfold flag_name_set_api_post; Exists 12 before.
  unfold flag_name_set_return_resources.
  rewrite (proj2 (Z.eqb_neq p 0) PreH2); cbn; entailer!.
Qed.

Lemma proof_of_OSFlagNameSet_return_wit_5 : OSFlagNameSet_return_wit_5.
Proof.
  left; intros; subst pgrp_pre pname_pre perr_pre; subst p.
  pose proof (flag_name_set_program_null_group critical sg invocation view name before)
    as Hprogram.
  pose proof (flag_name_set_safe_return critical sg invocation view 0 name before 110 before X
    Hprogram PreH5) as Hreturn.
  unfold flag_name_set_api_post; Exists 110 before.
  unfold flag_name_set_return_resources; cbn; entailer!.
Qed.

Lemma proof_of_OSFlagNameSet_partial_solve_wit_7_pure : OSFlagNameSet_partial_solve_wit_7_pure.
Proof.
  left; intros.
  pose proof (proj1 (proj1 (proj2 (proj2 PreH7)))) as Htype_address.
  rewrite Htype_address.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range p (flagImageType image)).
  Intros.
  assert (Hrange : 0 <= flagImageType image < 2 ^ 32) by (change (0 <= flagImageType image <= 255) in H; lia).
  rewrite (SimpleC.SL.IntLib.unsigned_last_nbits_eq _ _ Hrange) in PreH1.
  entailer!.
Qed.

Lemma proof_of_OSFlagNameSet_which_implies_wit_1 : OSFlagNameSet_which_implies_wit_1.
Proof.
  left; intros.
  unfold mutex_query_closed; Intros.
  sep_apply_l_atomic (task_name_set_observation_split critical sg invocation before).
  Intros.
  unfold mem_name_set_nesting_address in PreH1.
  rewrite <- PreH1.
  entailer!.
Qed.

Lemma proof_of_OSFlagNameSet_which_implies_wit_2 : OSFlagNameSet_which_implies_wit_2.
Proof.
  left; intros.
  pose proof PreH1 as Hnesting_address.
  unfold mem_name_set_nesting_address in Hnesting_address.
  rewrite Hnesting_address.
  sep_apply_l_atomic (task_name_set_observation_merge critical sg invocation before).
  unfold mutex_query_closed; entailer!.
Qed.

Lemma proof_of_OSFlagNameSet_which_implies_wit_3 : OSFlagNameSet_which_implies_wit_3.
Proof.
  left; intros.
  pose proof PreH1 as Hnesting_address.
  unfold mem_name_set_nesting_address in Hnesting_address.
  rewrite Hnesting_address.
  sep_apply_l_atomic (task_name_set_observation_merge critical sg invocation before).
  unfold mutex_query_closed; entailer!.
Qed.

Lemma proof_of_OSFlagNameSet_which_implies_wit_4 : OSFlagNameSet_which_implies_wit_4.
Proof.
  left; intros.
  pose proof (proj1 (proj2 (proj2 PreH1))) as Hlayout.
  destruct Hlayout as [Htype_address Hname_address].
  rewrite Htype_address, Hname_address.
  sep_apply_l_atomic (flag_name_set_name_split sg p view entry image PreH1 PreH2).
  entailer!.
Qed.

