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
From Ucos2Verify.VC.code.core Require Import mem_clr_goal.
From Ucos2Verify.VC.code.core Require Import mem_clr_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OS_MemClr_entail_wit_1 : OS_MemClr_entail_wit_1.
Proof.
  unfold OS_MemClr_entail_wit_1.
  right; intros.
  apply mem_clr_pre_to_loop_state.
Qed.

Lemma proof_of_OS_MemClr_entail_wit_2 : OS_MemClr_entail_wit_2.
Proof.
  unfold OS_MemClr_entail_wit_2.
  right; intros.
  change (sizeof(UCHAR)) with 1.
  rewrite Z.mul_1_r.
  apply mem_clr_loop_state_merge_zero_byte; lia.
Qed.

Lemma proof_of_OS_MemClr_return_wit_1 : OS_MemClr_return_wit_1.
Proof.
  unfold OS_MemClr_return_wit_1.
  left; intros size_pre pdest_pre pdest size Hexit Hsize Hbound
    Hsize_pre Hpdest Haddress Hcursor.
  assert (size = 0) by lia.
  subst size.
  apply mem_clr_loop_state_to_post.
Qed.

Lemma proof_of_OS_MemClr_which_implies_wit_1 : OS_MemClr_which_implies_wit_1.
Proof.
  unfold OS_MemClr_which_implies_wit_1.
  left; intros size_pre pdest_pre size pdest Hsize Hbound Hsize_pre
    Hpdest Haddress Hcursor.
  subst pdest.
  change (sizeof(UCHAR)) with 1 in *.
  repeat rewrite Z.mul_1_r in *.
  sep_apply (mem_clr_loop_state_split_byte pdest_pre size_pre size ltac:(lia)).
  entailer!.
Qed.
