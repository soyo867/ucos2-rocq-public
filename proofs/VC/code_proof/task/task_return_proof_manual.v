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
From Ucos2Verify.VC.code.task Require Import task_return_goal.
From Ucos2Verify.VC.code.task Require Import task_return_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.task.spec.task_return_spec.
Import UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OS_TaskReturn_return_wit_1 : OS_TaskReturn_return_wit_1.
Proof.
  unfold OS_TaskReturn_return_wit_1; left; intros.
  unfold task_return_post; Exists retval; entailer!.
Qed.

Lemma proof_of_OS_TaskReturn_which_implies_wit_1 : OS_TaskReturn_which_implies_wit_1.
Proof.
  unfold OS_TaskReturn_which_implies_wit_1; left; intros.
  pose proof (task_return_entry_split_current environment critical saved_local
    completed sg call mask initial) as Hsplit.
  unfold task_delete_global_addresses in PreH1.
  destruct PreH1 as (_ & _ & Hcurrent & _).
  rewrite Hcurrent in Hsplit.
  exact Hsplit.
Qed.

Lemma proof_of_OS_TaskReturn_which_implies_wit_2 : OS_TaskReturn_which_implies_wit_2.
Proof.
  unfold OS_TaskReturn_which_implies_wit_2; left; intros.
  unfold task_delete_ptr_cell; apply derivable1_wand_elim2.
Qed.

