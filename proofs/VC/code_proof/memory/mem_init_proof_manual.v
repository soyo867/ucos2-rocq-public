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
From Ucos2Verify.VC.code.memory Require Import mem_init_goal.
From Ucos2Verify.VC.code.memory Require Import mem_init_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.VC.code.memory.spec.mem_init_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OS_MemInit_entail_wit_2 : OS_MemInit_entail_wit_2.
Proof.
  left; intros.
  pose proof PreH2 as [Hpool Hroot].
  pose proof PreH3 as [_ [_ [_ [Hsizeof Hfields]]]].
  assert (Hi : 0 <= i < 5) by lia.
  destruct (Hfields i Hi) as [_ [Hfree [_ [_ [_ Hname]]]]].
  pose proof (mem_init_loop_residual_merge_control sg (LitMap "?") i
    PreH1 PreH3 Hi) as Hmerge.
  rewrite (proj2 (Z.ltb_lt i 4) PreH6) in Hmerge.
  rewrite Hpool, <- Hsizeof in Hfree, Hname, Hmerge.
  rewrite <- Hfree, <- Hname in Hmerge.
  rewrite Z.mul_0_l, Z.add_0_r.
  sep_apply_l_atomic Hmerge.
  sep_apply_l_atomic (GlobalStrings_merge LitMap "?").
  sep_apply store_ptr_undef_store_ptr.
  entailer!.
Qed.

Lemma proof_of_OS_MemInit_entail_wit_4 : OS_MemInit_entail_wit_4.
Proof.
  left; intros; subst i.
  pose proof PreH2 as [Hpool Hroot].
  pose proof PreH3 as [_ [_ [_ [Hsizeof Hfields]]]].
  destruct (Hfields 4 ltac:(lia)) as [_ [Hfree [_ [_ [_ Hname]]]]].
  pose proof (mem_init_loop_residual_merge_control sg (LitMap "?") 4
    PreH1 PreH3 ltac:(lia)) as Hmerge.
  change (4 <? 4) with false in Hmerge.
  change (4 + 1) with 5 in Hmerge.
  rewrite Hpool, <- Hsizeof in Hfree, Hname, Hmerge.
  rewrite <- Hfree, <- Hname in Hmerge.
  rewrite Z.mul_0_l, Z.add_0_r.
  sep_apply_l_atomic Hmerge.
  sep_apply_l_atomic (GlobalStrings_merge LitMap "?").
  sep_apply store_ushort_undef_store_ushort.
  sep_apply store_ptr_undef_store_ptr.
  entailer!.
Qed.

Lemma proof_of_OS_MemInit_return_wit_1 : OS_MemInit_return_wit_1.
Proof.
  left; intros.
  pose proof PreH2 as [Hpool Hroot].
  pose proof (mem_init_linked_pool_to_post sg (LitMap "?") PreH1) as Hpost.
  unfold mem_init_linked_pool in Hpost.
  rewrite Hpool, Hroot in Hpost.
  rewrite Z.mul_0_l, Z.add_0_r.
  sep_apply_l_atomic Hpost.
  entailer!.
Qed.

Lemma proof_of_OS_MemInit_which_implies_wit_1 : OS_MemInit_which_implies_wit_1.
Proof.
  left; intros.
  pose proof PreH2 as [Hpool Hroot].
  pose proof PreH3 as [Hlower [Hupper _]].
  rewrite Hpool in Hlower, Hupper.
  unfold mem_init_pre; rewrite Hpool, Hroot.
  rewrite Z.mul_0_l, Z.add_0_r, PreH4.
  change (sizeof(UCHAR)) with 1.
  entailer!; lia.
Qed.

Lemma proof_of_OS_MemInit_which_implies_wit_2 : OS_MemInit_which_implies_wit_2.
Proof.
  left; intros.
  pose proof PreH2 as [Hpool Hroot].
  pose proof (mem_init_mem_clr_to_loop_state sg (LitMap "?")) as Hinit.
  rewrite Hpool, Hroot in Hinit.
  rewrite Z.mul_0_l, Z.add_0_r, PreH4.
  sep_apply_l_atomic Hinit.
  entailer!.
Qed.

Lemma proof_of_OS_MemInit_which_implies_wit_3 : OS_MemInit_which_implies_wit_3.
Proof.
  left; intros.
  pose proof PreH2 as [Hpool Hroot].
  pose proof PreH3 as [_ [_ [_ [Hsizeof Hfields]]]].
  assert (Hi : 0 <= i < 5) by lia.
  destruct (Hfields i Hi) as [_ [Hfree [_ [_ [_ Hname]]]]].
  pose proof (mem_init_loop_state_split_control sg (LitMap "?") i
    PreH3 Hi) as Hsplit.
  rewrite Hpool, <- Hsizeof in Hfree, Hname, Hsplit.
  rewrite <- Hfree, <- Hname, <- PreH7 in Hsplit.
  sep_apply_l_atomic Hsplit.
  entailer!.
Qed.

Lemma proof_of_OS_MemInit_which_implies_wit_4 : OS_MemInit_which_implies_wit_4.
Proof.
  left; intros.
  pose proof PreH2 as [Hpool Hroot].
  pose proof PreH3 as [_ [_ [_ [Hsizeof Hfields]]]].
  assert (Hi : 0 <= i < 5) by lia.
  destruct (Hfields i Hi) as [_ [Hfree [_ [_ [_ Hname]]]]].
  pose proof (mem_init_loop_state_split_control sg (LitMap "?") i
    PreH3 Hi) as Hsplit.
  rewrite Hpool, <- Hsizeof in Hfree, Hname, Hsplit.
  rewrite <- Hfree, <- Hname, <- PreH7 in Hsplit.
  sep_apply_l_atomic Hsplit.
  entailer!; lia.
Qed.

Lemma proof_of_OS_MemInit_which_implies_wit_5 : OS_MemInit_which_implies_wit_5.
Proof.
  left; intros.
  pose proof PreH2 as [Hpool Hroot].
  pose proof (mem_init_loop_state_complete sg (LitMap "?")) as Hcomplete.
  rewrite Hroot in Hcomplete.
  sep_apply_l_atomic Hcomplete.
  entailer!.
Qed.

