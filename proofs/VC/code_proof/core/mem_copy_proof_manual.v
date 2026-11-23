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
From Ucos2Verify.VC.code.core Require Import mem_copy_goal.
From Ucos2Verify.VC.code.core Require Import mem_copy_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.core.spec.mem_copy_spec.
Require Import AUXLib.ListLib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OS_MemCopy_entail_wit_1 : OS_MemCopy_entail_wit_1.
Proof.
  unfold OS_MemCopy_entail_wit_1; left; intros.
  replace (size_pre - size_pre) with 0 by lia.
  change (sublist 0 0 bytes) with (@nil Z).
  unfold mem_copy_pre.
  sep_apply UCharArray.undef_full_to_undef_seg.
  rewrite UCharArray.seg_empty.
  entailer!.
Qed.

Lemma proof_of_OS_MemCopy_entail_wit_2 : OS_MemCopy_entail_wit_2.
Proof.
  unfold OS_MemCopy_entail_wit_2; left; intros.
  replace (size_pre - (size - 1)) with (size_pre - size + 1) by lia.
  assert (Hprefix :
    sublist 0 (size_pre - size + 1) bytes =
    sublist 0 (size_pre - size) bytes ++
      (Znth (size_pre - size) bytes 0 :: nil)).
  { rewrite (sublist_split 0 (size_pre - size + 1)
      (size_pre - size) bytes) by lia.
    rewrite (sublist_single 0 (size_pre - size) bytes) by lia.
    reflexivity. }
  rewrite Hprefix.
  sep_apply (UCharArray.seg_single pdest_pre (size_pre - size)
    (Znth (size_pre - size) bytes 0)).
  sep_apply (UCharArray.seg_merge_to_seg pdest_pre 0 (size_pre - size)
    (size_pre - size + 1) (sublist 0 (size_pre - size) bytes)
    (Znth (size_pre - size) bytes 0 :: nil) ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_OS_MemCopy_return_wit_1 : OS_MemCopy_return_wit_1.
Proof.
  unfold OS_MemCopy_return_wit_1; left; intros.
  assert (size = 0) by lia; subst size.
  rewrite Z.sub_0_r.
  rewrite (sublist_self bytes size_pre) by lia.
  rewrite UCharArray.undef_seg_empty.
  sep_apply UCharArray.seg_to_full.
  unfold mem_copy_post.
  simpl.
  rewrite Z.add_0_r, Z.sub_0_r.
  entailer!.
Qed.

Lemma proof_of_OS_MemCopy_which_implies_wit_1 : OS_MemCopy_which_implies_wit_1.
Proof.
  unfold OS_MemCopy_which_implies_wit_1; left; intros.
  rewrite (UCharArray.undef_seg_unfold pdest_pre (size_pre - size)
    size_pre ltac:(lia)).
  sep_apply (UCharArray.full_split_to_missing_i psrc_pre (size_pre - size)
    size_pre bytes 0 ltac:(lia)).
  subst pdest psrc.
  unfold StoreUCharAsElement.undefstoreA, StoreUCharAsElement.storeA.
  entailer!.
Qed.

