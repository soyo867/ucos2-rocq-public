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
From Ucos2Verify.VC.code.core Require Import init_misc_ready_full_goal.
From Ucos2Verify.VC.code.core Require Import init_misc_ready_full_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.core.spec.init_misc_spec.
Import UCOS2_C_Rules.
Require Import Ucos2Verify.VC.code.sched.spec.init_rdy_list_spec.
Import Ucos2Verify.lib.ucos2_rules_lib.UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OS_InitMisc_return_wit_1 : OS_InitMisc_return_wit_1.
Proof.
  left.
  intros R sg PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
    PreH7 PreH8 PreH9 PreH10 PreH11.
  unfold init_misc_zero.
  rewrite PreH1, PreH2, PreH3, PreH4, PreH5, PreH6,
    PreH7, PreH8, PreH9, PreH10, PreH11.
  entailer!.
Qed.
Lemma proof_of_OS_InitRdyList_return_wit_1 : OS_InitRdyList_return_wit_1.
Proof.
  unfold OS_InitRdyList_return_wit_1; left.
  intros i Hge Hnonneg Hle.
  assert (i = 8) by lia; subst i.
  unfold init_rdy_list_post.
  sep_apply_l_atomic (init_rdy_list_table_prefix_complete (&("OSRdyTbl"))).
  entailer!.
Qed.

Lemma proof_of_OS_InitRdyList_which_implies_wit_1 : OS_InitRdyList_which_implies_wit_1.
Proof.
  unfold OS_InitRdyList_which_implies_wit_1; left.
  apply init_rdy_list_pre_split_group.
Qed.

Lemma proof_of_OS_InitRdyList_which_implies_wit_2 : OS_InitRdyList_which_implies_wit_2.
Proof.
  unfold OS_InitRdyList_which_implies_wit_2; left.
  intros i Hnonneg Hlt.
  change (sizeof(UCHAR)) with 1; rewrite Z.mul_1_r.
  apply init_rdy_list_table_prefix_split_row; lia.
Qed.

Lemma proof_of_OS_InitRdyList_which_implies_wit_3 : OS_InitRdyList_which_implies_wit_3.
Proof.
  unfold OS_InitRdyList_which_implies_wit_3; left.
  intros i Hnonneg Hlt.
  change (sizeof(UCHAR)) with 1; rewrite Z.mul_1_r.
  apply init_rdy_list_table_prefix_merge_row; lia.
Qed.
