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
From Ucos2Verify.VC.code.core Require Import task_idle_goal.
From Ucos2Verify.VC.code.core Require Import task_idle_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.core.spec.task_idle_spec.
Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OS_TaskIdle_entail_wit_1 : OS_TaskIdle_entail_wit_1.
Proof.
  unfold OS_TaskIdle_entail_wit_1; left; intros.
  pose proof (task_idle_prefix_empty critical hook sg invocation origin
    initial_mask initial) as Hprefix.
  Exists (@nil TaskIdleIteration) initial_mask initial.
  entailer!.
Qed.

Lemma proof_of_OS_TaskIdle_partial_solve_wit_3_pure : OS_TaskIdle_partial_solve_wit_3_pure.
Proof.
  unfold OS_TaskIdle_partial_solve_wit_3_pure; left; intros.
  pose proof (task_idle_counter_after_uint acquired) as Hcounter.
  entailer!.
Qed.

Lemma proof_of_OS_TaskIdle_which_implies_wit_1 : OS_TaskIdle_which_implies_wit_1.
Proof.
  unfold OS_TaskIdle_which_implies_wit_1; left; intros.
  Exists acquired_2.
  rewrite PreH1.
  sep_apply_l_atomic (task_idle_inv_split_counter platform critical hook sg
    invocation origin initial_mask initial history mask cpu_sr before acquired_2
    PreH2 PreH3 PreH5 PreH4).
  entailer!.
Qed.

Lemma proof_of_OS_TaskIdle_which_implies_wit_2 : OS_TaskIdle_which_implies_wit_2.
Proof.
  unfold OS_TaskIdle_which_implies_wit_2; left; intros.
  Exists (task_idle_update acquired).
  rewrite PreH1.
  sep_apply_l_atomic (task_idle_store_frame_merge_updated platform critical hook sg
    invocation origin initial_mask initial history mask cpu_sr before acquired).
  entailer!.
Qed.

Lemma proof_of_OS_TaskIdle_which_implies_wit_3 : OS_TaskIdle_which_implies_wit_3.
Proof.
  unfold OS_TaskIdle_which_implies_wit_3; left; intros.
  pose proof (task_idle_written_hook_extends_prefix critical hook sg invocation
    origin initial_mask initial history mask saved before acquired checkpoint
    restored next_mask_2 after_2 PreH1 PreH2 PreH3) as Hprefix.
  Exists (task_idle_extend_history history mask saved before acquired restored
    next_mask_2 after_2) next_mask_2 after_2.
  entailer!.
Qed.

