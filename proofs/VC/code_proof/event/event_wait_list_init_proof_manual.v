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
From Ucos2Verify.VC.code.event Require Import event_wait_list_init_goal.
From Ucos2Verify.VC.code.event Require Import event_wait_list_init_proof_auto_checked.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.event.spec.event_wait_list_init_spec.
Import Ucos2Verify.lib.ucos2_rules_lib.UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OS_EventWaitListInit_which_implies_wit_1 : OS_EventWaitListInit_which_implies_wit_1.
Proof.
  unfold OS_EventWaitListInit_which_implies_wit_1.
  left; intro pevent.
  apply event_wait_list_init_pre_split_group.
Qed.

Lemma proof_of_OS_EventWaitListInit_which_implies_wit_2 : OS_EventWaitListInit_which_implies_wit_2.
Proof.
  unfold OS_EventWaitListInit_which_implies_wit_2.
  left; intros i pevent Hlower Hupper.
  change (sizeof(UCHAR)) with 1.
  rewrite Z.mul_1_r.
  apply event_wait_list_init_table_prefix_split_row; lia.
Qed.

Lemma proof_of_OS_EventWaitListInit_which_implies_wit_3 : OS_EventWaitListInit_which_implies_wit_3.
Proof.
  unfold OS_EventWaitListInit_which_implies_wit_3.
  left; intros i pevent Hlower Hupper.
  change (sizeof(UCHAR)) with 1.
  rewrite Z.mul_1_r.
  apply event_wait_list_init_table_prefix_merge_row; lia.
Qed.

Lemma proof_of_OS_EventWaitListInit_which_implies_wit_4 : OS_EventWaitListInit_which_implies_wit_4.
Proof.
  unfold OS_EventWaitListInit_which_implies_wit_4.
  left; intros i pevent Hlower Hupper Hexit.
  assert (Hi : i = 8) by lia; subst i.
  intros heap Hheap; split.
  - reflexivity.
  - exact (event_wait_list_init_post_merge_table _ _ heap Hheap).
Qed.
