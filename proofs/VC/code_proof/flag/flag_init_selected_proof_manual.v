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
From Ucos2Verify.VC.code.flag Require Import flag_init_selected_goal.
From Ucos2Verify.VC.code.flag Require Import flag_init_selected_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_init_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.



Lemma proof_of_OS_FlagInit_entail_wit_2 : OS_FlagInit_entail_wit_2.
Proof.
  right; intros.
  destruct PreH2 as [Hpool Hroot].
  destruct PreH3 as [_ [_ [_ [Hsize Hfields]]]].
  specialize (Hfields ix ltac:(lia)).
  destruct Hfields as [Htype [Hlink [Hbits Hname]]].
  rewrite Hsize, <- Hpool, Htype, Hlink, Hname.
  replace (LitMap "?" + 0 * sizeof(CHAR)) with (LitMap "?") by lia.
  assert (Hlt : (ix <? 4) = true) by (apply Z.ltb_lt; lia).
  pose proof (flag_init_loop_residual_merge_group__flag_pool_initialization
    sg (LitMap "?") ix PreH1 ltac:(lia)) as Hmerge.
  rewrite Hlt in Hmerge.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.



Lemma proof_of_OS_FlagInit_entail_wit_4 : OS_FlagInit_entail_wit_4.
Proof.
  right; intros; subst ix.
  destruct PreH2 as [Hpool Hroot].
  destruct PreH3 as [_ [_ [_ [Hsize Hfields]]]].
  specialize (Hfields 4 ltac:(lia)).
  destruct Hfields as [Htype [Hlink [Hbits Hname]]].
  rewrite Hsize, <- Hpool, Htype, Hlink, Hname.
  replace (LitMap "?" + 0 * sizeof(CHAR)) with (LitMap "?") by lia.
  pose proof (flag_init_loop_residual_merge_group__flag_pool_initialization
    sg (LitMap "?") 4 PreH1 ltac:(lia)) as Hmerge.
  change (4 <? 4) with false in Hmerge.
  replace (4 + 1) with 5 in Hmerge by lia.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.



Lemma proof_of_OS_FlagInit_return_wit_1 : OS_FlagInit_return_wit_1.
Proof.
  right; intros.
  destruct PreH2 as [Hpool Hroot].
  unfold flag_init_post.
  rewrite Hpool, Hroot.
  replace (0 * sizeof("os_flag_grp")) with 0 by lia.
  rewrite Z.add_0_r; entailer!.
Qed.



Lemma proof_of_OS_FlagInit_which_implies_wit_1 : OS_FlagInit_which_implies_wit_1.
Proof.
  left; intros.
  pose proof PreH2 as [Hpool Hroot].
  pose proof PreH3 as [Hlo [Hhi [Halign [Hsize Hfields]]]].
  unfold flag_init_pre.
  rewrite Hpool, Hroot, Hsize.
  change (sizeof(UCHAR)) with 1.
  change UINT_MAX with 4294967295.
  rewrite Hpool in Hlo, Hhi.
  replace (0 * 16) with 0 by lia; rewrite Z.add_0_r.
  entailer!.
Qed.



Lemma proof_of_OS_FlagInit_which_implies_wit_2 : OS_FlagInit_which_implies_wit_2.
Proof.
  right; intros.
  destruct PreH2 as [Hpool Hroot].
  replace (0 * sizeof("os_flag_grp")) with 0 by lia.
  rewrite Z.add_0_r, PreH4, <- Hpool, <- Hroot.
  apply flag_init_mem_clr_to_loop_state.
Qed.



Lemma proof_of_OS_FlagInit_which_implies_wit_3 : OS_FlagInit_which_implies_wit_3.
Proof.
  right; intros.
  destruct PreH2 as [Hpool Hroot].
  pose proof PreH3 as [_ [_ [_ [Hsize Hfields]]]].
  specialize (Hfields ix ltac:(lia)).
  destruct Hfields as [Htype [Hlink [Hbits Hname]]].
  rewrite PreH8, Hsize, <- Hpool, Htype, Hlink, Hname.
  apply flag_init_loop_state_split_group__flag_pool_initialization;
    [exact PreH3|lia].
Qed.



Lemma proof_of_OS_FlagInit_which_implies_wit_4 : OS_FlagInit_which_implies_wit_4.
Proof.
  right; intros.
  destruct PreH2 as [Hpool Hroot].
  pose proof PreH3 as [_ [_ [_ [Hsize Hfields]]]].
  specialize (Hfields ix ltac:(lia)).
  destruct Hfields as [Htype [Hlink [Hbits Hname]]].
  rewrite PreH7, Hsize, <- Hpool, Htype, Hlink, Hname.
  apply flag_init_loop_state_split_group__flag_pool_initialization;
    [exact PreH3|lia].
Qed.



Lemma proof_of_OS_FlagInit_which_implies_wit_5 : OS_FlagInit_which_implies_wit_5.
Proof.
  left; intros.
  pose proof PreH2 as [Hpool Hroot].
  unfold flag_init_loop_state.
  change (80 - 5 * 16) with 0.
  unfold mem_clr_post.
  change (repeat_Z 0 0) with (@nil Z).
  rewrite UCharArray.full_empty, Hroot; entailer!.
Qed.

