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
From Ucos2Verify.VC.code.task Require Import task_stk_clr_goal.
From Ucos2Verify.VC.code.task Require Import task_stk_clr_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.task.spec.task_stk_clr_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OS_TaskStkClr_entail_wit_1 : OS_TaskStkClr_entail_wit_1.
Proof.
  unfold OS_TaskStkClr_entail_wit_1; left; intros.
  assert (Henabled : task_stack_clear_enabled opt_pre = true).
  { apply task_stack_clear_enabled_iff; auto. }
  sep_apply (task_stk_clr_pre_implies_loop_initial
    pbos_pre size_pre opt_pre initial Henabled).
  entailer!.
Qed.

Lemma proof_of_OS_TaskStkClr_entail_wit_2 : OS_TaskStkClr_entail_wit_2.
Proof.
  unfold OS_TaskStkClr_entail_wit_2; left; intros.
  assert (Hnonzero : Z.eqb size_pre 0 = false) by (apply Z.eqb_neq; lia).
  assert (Hdone : 0 <= size_pre - size < Zlength initial) by lia.
  assert (Hbounds : task_stk_clr_array_bounds pbos_pre size_pre).
  { unfold task_stk_clr_array_bounds; rewrite sizeof_uint in PreH4.
    repeat split; try lia.
    rewrite <- Z.rem_mod_nonneg by lia; exact PreH3. }
  unfold task_stk_clr_loop, task_stk_clr_residual; rewrite Hnonzero.
  replace (size_pre - (size - 1)) with (size_pre - size + 1) by lia.
  rewrite <- PreH1.
  sep_apply (task_stack_clear_rep_merge_zero_cell
    pbos_pre initial (Zlength initial - size) ltac:(lia)).
  entailer!.
  rewrite PreH1; exact Hbounds.
Qed.

Lemma proof_of_OS_TaskStkClr_return_wit_1 : OS_TaskStkClr_return_wit_1.
Proof.
  unfold OS_TaskStkClr_return_wit_1; left; intros.
  assert (Hsize : size = 0) by lia; subst size.
  assert (Henabled : task_stack_clear_enabled opt_pre = true).
  { apply task_stack_clear_enabled_iff; auto. }
  unfold task_stk_clr_loop, task_stk_clr_post; rewrite Henabled.
  destruct (Z.eqb size_pre 0); [entailer!|].
  Intros.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  subst size_pre.
  rewrite Z.sub_0_r.
  unfold task_stack_clear_rep; rewrite task_stack_clear_words_complete.
  entailer!.
Qed.

Lemma proof_of_OS_TaskStkClr_return_wit_2 : OS_TaskStkClr_return_wit_2.
Proof.
  unfold OS_TaskStkClr_return_wit_2; left; intros.
  pose proof (task_stack_clear_disabled_without_clear opt_pre PreH1) as Hdisabled.
  unfold task_stk_clr_pre, task_stk_clr_post; rewrite Hdisabled.
  entailer!.
Qed.

Lemma proof_of_OS_TaskStkClr_return_wit_3 : OS_TaskStkClr_return_wit_3.
Proof.
  unfold OS_TaskStkClr_return_wit_3; left; intros.
  pose proof (task_stack_clear_disabled_without_check opt_pre PreH1) as Hdisabled.
  unfold task_stk_clr_pre, task_stk_clr_post; rewrite Hdisabled.
  entailer!.
Qed.

Lemma proof_of_OS_TaskStkClr_which_implies_wit_1 : OS_TaskStkClr_which_implies_wit_1.
Proof.
  unfold OS_TaskStkClr_which_implies_wit_1; left; intros.
  assert (Hnonzero : Z.eqb size_pre 0 = false) by (apply Z.eqb_neq; lia).
  unfold task_stk_clr_loop; rewrite Hnonzero.
  Intros.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  unfold task_stk_clr_array_bounds in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assert (Halign : Z.rem pbos_pre 4 = 0).
  { rewrite Z.rem_mod_nonneg by lia; assumption. }
  assert (Hdone : 0 <= size_pre - size < Zlength initial) by lia.
  sep_apply (task_stack_clear_rep_split_cell pbos_pre initial (size_pre - size) Hdone).
  sep_apply UIntArray.mixedstoreA_to_undefstoreA.
  unfold task_stk_clr_residual.
  unfold StoreUIntAsElement.undefstoreA.
  subst pbos.
  entailer!.
  - rewrite H; reflexivity.
  - rewrite sizeof_uint; lia.
  - rewrite sizeof_uint; lia.
  - rewrite sizeof_uint; lia.
Qed.

