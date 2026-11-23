Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.array_abstraction.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OS_TaskStkClr, V2.93.01 Source/os_task.c:1364--1395.  This is the
    selected ARMv7-A/GNU instance: OS_STK is unsigned int (32 bits), and
    OS_STK_GROWTH = 1.  The function is compiled only when both
    OS_TASK_STAT_STK_CHK_EN and OS_TASK_CREATE_EXT_EN are enabled.

    The two masks below are the source constants 0x0001 and 0x0002.  The
    outer STK_CHK test is evaluated first.  A clear-only option does NOT
    initialize the stack.  Other option bits remain unconstrained.

    The list image permits None in the untouched suffix: the callee need
    not read the old stack values before overwriting them.  QCP's mixed
    unsigned-int array supplies exactly this ownership; no second array
    representation or additional global-state field is introduced. *)
Definition task_stack_clear_enabled (options : Z) : bool :=
  if Z.eqb (Z.land options 1) 0 then false
  else negb (Z.eqb (Z.land options 2) 0).

Lemma task_stack_clear_enabled_iff : forall options,
  task_stack_clear_enabled options = true <->
  Z.land options 1 <> 0 /\ Z.land options 2 <> 0.
Proof.
  intros; unfold task_stack_clear_enabled.
  destruct (Z.eqb (Z.land options 1) 0) eqn:Hcheck;
    destruct (Z.eqb (Z.land options 2) 0) eqn:Hclear;
    apply Z.eqb_eq in Hcheck || apply Z.eqb_neq in Hcheck;
    apply Z.eqb_eq in Hclear || apply Z.eqb_neq in Hclear;
    simpl; intuition discriminate.
Qed.

Lemma task_stack_clear_disabled_without_check : forall options,
  Z.land options 1 = 0 -> task_stack_clear_enabled options = false.
Proof. intros; unfold task_stack_clear_enabled; rewrite H; reflexivity. Qed.

Lemma task_stack_clear_disabled_without_clear : forall options,
  Z.land options 2 = 0 -> task_stack_clear_enabled options = false.
Proof.
  intros; unfold task_stack_clear_enabled; rewrite H.
  destruct (Z.eqb (Z.land options 1) 0); reflexivity.
Qed.

Lemma task_stack_clear_clear_only_disabled : task_stack_clear_enabled 2 = false.
Proof. reflexivity. Qed.

Lemma task_stack_clear_both_options_enabled : task_stack_clear_enabled 3 = true.
Proof. reflexivity. Qed.

Definition task_stack_clear_words (initial : list (option Z)) (done : Z)
  : list (option Z) :=
  copy_prefix_list (repeat (Some 0) (List.length initial)) initial done.

Lemma task_stack_clear_words_length : forall initial done,
  Zlength (task_stack_clear_words initial done) = Zlength initial.
Proof.
  intros; unfold task_stack_clear_words.
  rewrite copy_prefix_list_length.
  - rewrite !Zlength_correct, repeat_length; reflexivity.
  - rewrite !Zlength_correct, repeat_length; reflexivity.
Qed.

Lemma task_stack_clear_words_initial : forall initial,
  task_stack_clear_words initial 0 = initial.
Proof. reflexivity. Qed.

Lemma task_stack_clear_words_step : forall initial done,
  0 <= done < Zlength initial ->
  replace_Znth done (Some 0) (task_stack_clear_words initial done) =
  task_stack_clear_words initial (done + 1).
Proof.
  intros initial done Hdone; unfold task_stack_clear_words.
  rewrite <- (Znth_repeat (Some 0) (List.length initial) done) at 1.
  apply copy_prefix_list_step.
  - rewrite !Zlength_correct, repeat_length; reflexivity.
  - rewrite Zlength_correct, repeat_length; rewrite Zlength_correct in Hdone; exact Hdone.
Qed.

Lemma task_stack_clear_words_complete : forall initial,
  task_stack_clear_words initial (Zlength initial) =
  repeat (Some 0) (List.length initial).
Proof.
  intros; unfold task_stack_clear_words; apply copy_prefix_list_complete;
    rewrite !Zlength_correct, repeat_length; lia.
Qed.

(** This is an exact old-value frame, including unspecified values. *)
Lemma task_stack_clear_words_suffix : forall initial done,
  0 <= done <= Zlength initial ->
  skipn (Z.to_nat done) (task_stack_clear_words initial done) =
  skipn (Z.to_nat done) initial.
Proof.
  intros initial done Hdone; unfold task_stack_clear_words, copy_prefix_list.
  assert (Hlength : List.length
    (firstn (Z.to_nat done) (repeat (Some 0) (List.length initial))) = Z.to_nat done).
  { rewrite firstn_length, repeat_length; apply Nat.min_l.
    rewrite Zlength_correct in Hdone; lia. }
  rewrite skipn_app, Hlength, Nat.sub_diag; simpl.
  rewrite skipn_all2 by lia; reflexivity.
Qed.

Record TaskStackClearLoopState := {
  stackClearRemaining : Z;
  stackClearCursor : addr;
  stackClearDone : Z;
  stackClearWords : list (option Z)
}.

Definition task_stack_clear_initial (bottom : addr) (size : Z)
  (words : list (option Z)) : TaskStackClearLoopState :=
  {| stackClearRemaining := size; stackClearCursor := bottom;
     stackClearDone := 0; stackClearWords := words |}.

Definition task_stack_clear_decrement (s : TaskStackClearLoopState)
  : TaskStackClearLoopState :=
  {| stackClearRemaining := s.(stackClearRemaining) - 1;
     stackClearCursor := s.(stackClearCursor);
     stackClearDone := s.(stackClearDone);
     stackClearWords := s.(stackClearWords) |}.

(** The store and pointer postincrement are one C full-expression.  This
    transformer does not assert an evaluation order BETWEEN those two
    side effects.  The preceding size-- is a separate, sequenced statement.
    [stackClearDone] is a loop index, not an extra source guard or field. *)
Definition task_stack_clear_store_advance (s : TaskStackClearLoopState)
  : TaskStackClearLoopState :=
  {| stackClearRemaining := s.(stackClearRemaining);
     stackClearCursor := s.(stackClearCursor) + sizeof(UINT);
     stackClearDone := s.(stackClearDone) + 1;
     stackClearWords := replace_Znth s.(stackClearDone) (Some 0)
       s.(stackClearWords) |}.

Definition task_stack_clear_step (before after : TaskStackClearLoopState) : Prop :=
  0 < before.(stackClearRemaining) /\
  after = task_stack_clear_store_advance (task_stack_clear_decrement before).

Inductive task_stack_clear_steps : nat -> TaskStackClearLoopState ->
    TaskStackClearLoopState -> Prop :=
| task_stack_clear_steps_zero : forall s, task_stack_clear_steps O s s
| task_stack_clear_steps_succ : forall n before middle after,
    task_stack_clear_step before middle ->
    task_stack_clear_steps n middle after ->
    task_stack_clear_steps (S n) before after.

Definition task_stack_clear_frontier (bottom : addr) (initial : list (option Z))
  (done : Z) : TaskStackClearLoopState :=
  {| stackClearRemaining := Zlength initial - done;
     stackClearCursor := bottom + done * sizeof(UINT);
     stackClearDone := done; stackClearWords := task_stack_clear_words initial done |}.

Lemma task_stack_clear_frontier_initial : forall bottom initial,
  task_stack_clear_frontier bottom initial 0 =
  task_stack_clear_initial bottom (Zlength initial) initial.
Proof.
  intros; unfold task_stack_clear_frontier, task_stack_clear_initial;
    rewrite task_stack_clear_words_initial; f_equal; lia.
Qed.

Lemma task_stack_clear_step_frontier : forall bottom initial done,
  0 <= done < Zlength initial ->
  task_stack_clear_step (task_stack_clear_frontier bottom initial done)
    (task_stack_clear_frontier bottom initial (done + 1)).
Proof.
  intros bottom initial done Hdone; split; [simpl; lia|].
  unfold task_stack_clear_frontier, task_stack_clear_store_advance,
    task_stack_clear_decrement; simpl.
  rewrite task_stack_clear_words_step by exact Hdone; f_equal; ring.
Qed.

Lemma task_stack_clear_steps_frontier : forall n bottom initial done after,
  0 <= done <= Zlength initial ->
  task_stack_clear_steps n (task_stack_clear_frontier bottom initial done) after ->
  done + Z.of_nat n <= Zlength initial /\
  after = task_stack_clear_frontier bottom initial (done + Z.of_nat n).
Proof.
  induction n as [|n IH]; intros bottom initial done after Hdone Hsteps.
  - inversion Hsteps; subst; simpl; split; [lia|f_equal; lia].
  - inversion Hsteps as [|n' before middle after' Hstep Htail]; subst.
    destruct Hstep as [Hpositive Hmiddle]; simpl in Hpositive.
    assert (Hnext : task_stack_clear_step
      (task_stack_clear_frontier bottom initial done)
      (task_stack_clear_frontier bottom initial (done + 1))).
    { apply task_stack_clear_step_frontier; lia. }
    destruct Hnext as [_ Hnext]; rewrite <- Hnext in Hmiddle; subst middle.
    destruct (IH bottom initial (done + 1) after ltac:(lia) Htail) as [Hbound Hafter].
    rewrite Nat2Z.inj_succ; split; [lia|].
    rewrite Hafter; f_equal; lia.
Qed.

Lemma task_stack_clear_steps_exist : forall n bottom initial done,
  0 <= done -> done + Z.of_nat n <= Zlength initial ->
  task_stack_clear_steps n (task_stack_clear_frontier bottom initial done)
    (task_stack_clear_frontier bottom initial (done + Z.of_nat n)).
Proof.
  induction n as [|n IH]; intros bottom initial done Hdone Hbound.
  - simpl; replace (done + 0) with done by lia; constructor.
  - rewrite Nat2Z.inj_succ in *.
    replace (done + Z.succ (Z.of_nat n)) with (done + 1 + Z.of_nat n) by lia.
    eapply task_stack_clear_steps_succ.
    + apply task_stack_clear_step_frontier; lia.
    + apply IH; lia.
Qed.

(** Scalar bounds are a safety theorem, not extra executable guards.  In
    particular, positive unsigned size cannot underflow at size--. *)
Lemma task_stack_clear_step_size_in_range : forall before after,
  0 <= before.(stackClearRemaining) <= 4294967295 ->
  task_stack_clear_step before after ->
  0 <= after.(stackClearRemaining) < before.(stackClearRemaining).
Proof.
  intros before after Hrange [Hpositive ->]; simpl; lia.
Qed.

Definition task_stack_clear_result (options : Z)
  (before after : TaskStackClearLoopState) : Prop :=
  if Z.eqb (Z.land options 1) 0 then after = before
  else if Z.eqb (Z.land options 2) 0 then after = before
  else exists n, task_stack_clear_steps n before after /\ after.(stackClearRemaining) = 0.

Lemma task_stack_clear_result_disabled : forall options before after,
  task_stack_clear_enabled options = false ->
  (task_stack_clear_result options before after <-> after = before).
Proof.
  intros options before after Hdisabled.
  unfold task_stack_clear_result, task_stack_clear_enabled in *.
  destruct (Z.eqb (Z.land options 1) 0);
    destruct (Z.eqb (Z.land options 2) 0); simpl in *; intuition discriminate.
Qed.

Lemma task_stack_clear_result_enabled : forall options before after,
  task_stack_clear_enabled options = true ->
  (task_stack_clear_result options before after <->
    exists n, task_stack_clear_steps n before after /\ after.(stackClearRemaining) = 0).
Proof.
  intros options before after Henabled.
  unfold task_stack_clear_result, task_stack_clear_enabled in *.
  destruct (Z.eqb (Z.land options 1) 0);
    destruct (Z.eqb (Z.land options 2) 0); simpl in *; intuition discriminate.
Qed.

Lemma task_stack_clear_zero_size : forall options bottom words,
  task_stack_clear_result options (task_stack_clear_initial bottom 0 words)
    (task_stack_clear_initial bottom 0 words).
Proof.
  intros; unfold task_stack_clear_result.
  destruct (Z.eqb (Z.land options 1) 0); [reflexivity|].
  destruct (Z.eqb (Z.land options 2) 0); [reflexivity|].
  exists O; split; [constructor|reflexivity].
Qed.

Lemma task_stack_clear_result_complete : forall options bottom initial after,
  task_stack_clear_enabled options = true ->
  task_stack_clear_result options
    (task_stack_clear_initial bottom (Zlength initial) initial) after ->
  after.(stackClearRemaining) = 0 /\
  after.(stackClearCursor) = bottom + Zlength initial * sizeof(UINT) /\
  after.(stackClearDone) = Zlength initial /\
  after.(stackClearWords) = repeat (Some 0) (List.length initial).
Proof.
  intros options bottom initial after Henabled Hresult.
  apply (proj1 (task_stack_clear_result_enabled _ _ _ Henabled)) in Hresult.
  destruct Hresult as [n [Hsteps Hzero]].
  rewrite <- task_stack_clear_frontier_initial in Hsteps.
  destruct (task_stack_clear_steps_frontier n bottom initial 0 after
    ltac:(rewrite Zlength_correct; lia) Hsteps) as [Hbound Hafter].
  simpl in Hafter; subst after; simpl in Hzero |- *.
  assert (Hn : Z.of_nat n = Zlength initial) by lia; rewrite Hn.
  repeat split; try reflexivity; try lia; apply task_stack_clear_words_complete.
Qed.

Lemma task_stack_clear_result_exists : forall options bottom initial,
  exists after, task_stack_clear_result options
    (task_stack_clear_initial bottom (Zlength initial) initial) after.
Proof.
  intros options bottom initial; destruct (task_stack_clear_enabled options) eqn:Henabled.
  - exists (task_stack_clear_frontier bottom initial (Zlength initial)).
    apply (proj2 (task_stack_clear_result_enabled _ _ _ Henabled)).
    exists (List.length initial); split; [|simpl; lia].
    rewrite <- task_stack_clear_frontier_initial.
    replace (Zlength initial) with (0 + Z.of_nat (List.length initial))
      by (rewrite Zlength_correct; lia).
    apply task_stack_clear_steps_exist; rewrite ?Zlength_correct; lia.
  - exists (task_stack_clear_initial bottom (Zlength initial) initial).
    apply (proj2 (task_stack_clear_result_disabled _ _ _ Henabled)); reflexivity.
Qed.

(** The final postincrement forms the one-past pointer, without reading or
    writing there.  For a 32-bit flat address instance this arithmetic bound
    excludes wrap; allocation/provenance of the same array object is still a
    C/ABI obligation.  No growth-0 instance is claimed: its final decrement
    forms a one-before pointer, requiring a separate source/ABI safety audit. *)
Lemma task_stack_clear_cursor_in_range : forall bottom initial done,
  0 <= done <= Zlength initial ->
  0 <= bottom -> bottom + 4 * Zlength initial <= 4294967295 ->
  0 <= (task_stack_clear_frontier bottom initial done).(stackClearCursor) <= 4294967295.
Proof. intros; simpl; lia. Qed.

Definition task_stack_clear_rep (bottom : addr) (initial : list (option Z))
  (done : Z) : Assertion :=
  UIntArray.mixed_full bottom (Zlength initial) (task_stack_clear_words initial done).

Lemma task_stack_clear_rep_initial : forall bottom initial,
  task_stack_clear_rep bottom initial 0 = UIntArray.mixed_full bottom (Zlength initial) initial.
Proof. intros; reflexivity. Qed.

Lemma task_stack_clear_rep_split_cell : forall bottom initial done,
  0 <= done < Zlength initial ->
  task_stack_clear_rep bottom initial done |--
  UIntArray.mixedstoreA bottom done (Znth done (task_stack_clear_words initial done) None) **
  UIntArray.mixed_missing_i bottom done 0 (Zlength initial)
    (task_stack_clear_words initial done).
Proof. intros; unfold task_stack_clear_rep; apply UIntArray.mixed_full_split_to_mixed_missing_i; assumption. Qed.

Lemma task_stack_clear_rep_merge_original_cell : forall bottom initial done,
  0 <= done < Zlength initial ->
  UIntArray.mixedstoreA bottom done (Znth done (task_stack_clear_words initial done) None) **
  UIntArray.mixed_missing_i bottom done 0 (Zlength initial)
    (task_stack_clear_words initial done) |-- task_stack_clear_rep bottom initial done.
Proof.
  intros; unfold task_stack_clear_rep; eapply derivable1_trans.
  - apply UIntArray.mixed_missing_i_merge_to_mixed_full; assumption.
  - rewrite replace_Znth_Znth; reflexivity.
Qed.

(** Consumes an ACTUALLY written zero cell; the old/undef cell cannot be
    silently converted to zero by this lemma. *)
Lemma task_stack_clear_rep_merge_zero_cell : forall bottom initial done,
  0 <= done < Zlength initial ->
  (bottom + done * sizeof(UINT)) # UInt |-> 0 **
  UIntArray.mixed_missing_i bottom done 0 (Zlength initial)
    (task_stack_clear_words initial done) |-- task_stack_clear_rep bottom initial (done + 1).
Proof.
  intros; unfold task_stack_clear_rep; eapply derivable1_trans.
  - apply (UIntArray.mixed_missing_i_merge_to_mixed_full bottom done
      (Zlength initial) (Some 0) (task_stack_clear_words initial done)); assumption.
  - rewrite task_stack_clear_words_step by assumption; reflexivity.
Qed.

Lemma task_stack_clear_rep_complete : forall bottom initial,
  task_stack_clear_rep bottom initial (Zlength initial) |--
  UIntArray.full bottom (Zlength initial) (repeat 0 (List.length initial)).
Proof.
  intros; unfold task_stack_clear_rep; rewrite task_stack_clear_words_complete.
  replace (repeat (Some 0) (List.length initial)) with
    (map (@Some Z) (repeat 0 (List.length initial))) by (rewrite map_repeat; reflexivity).
  apply UIntArray.mixed_full_to_full.
Qed.

(** The entire untouched suffix is retained, not replaced by emp or True.
    [firstn done zeros] records the initialized prefix without duplicating
    QCP's segment predicates. *)
Definition task_stack_clear_prefix_residual (bottom : addr)
  (initial : list (option Z)) (done : Z) : Assertion :=
  UIntArray.mixed_full bottom done
    (firstn (Z.to_nat done) (repeat (Some 0) (List.length initial))) **
  UIntArray.mixed_full (bottom + done * sizeof(UINT)) (Zlength initial - done)
    (skipn (Z.to_nat done) initial).

Lemma task_stack_clear_prefix_residual_merge : forall bottom initial done,
  0 <= done <= Zlength initial ->
  task_stack_clear_prefix_residual bottom initial done |-- task_stack_clear_rep bottom initial done.
Proof.
  intros; unfold task_stack_clear_prefix_residual, task_stack_clear_rep,
    task_stack_clear_words, copy_prefix_list.
  apply UIntArray.mixed_full_merge_to_mixed_full; assumption.
Qed.

Lemma task_stack_clear_prefix_residual_split : forall bottom initial done,
  0 <= done <= Zlength initial ->
  task_stack_clear_rep bottom initial done |-- task_stack_clear_prefix_residual bottom initial done.
Proof.
  intros bottom initial done Hdone; unfold task_stack_clear_rep,
    task_stack_clear_prefix_residual.
  eapply derivable1_trans.
  - apply UIntArray.mixed_full_split_to_mixed_full; exact Hdone.
  - assert (Hprefix : Zlength (firstn (Z.to_nat done)
      (repeat (Some 0) (List.length initial))) = done).
    { rewrite Zlength_correct, firstn_length, repeat_length.
      rewrite Nat.min_l; rewrite Zlength_correct in Hdone; lia. }
    assert (Hsuffix : sublist done (Zlength initial) (task_stack_clear_words initial done) =
      skipn (Z.to_nat done) initial).
    { unfold sublist.
      rewrite firstn_all2.
      - apply task_stack_clear_words_suffix; exact Hdone.
      - pose proof (task_stack_clear_words_length initial done) as Hlength.
        rewrite Zlength_correct, Nat2Z.id.
        rewrite !Zlength_correct in Hlength; lia. }
    assert (Hfront : sublist 0 done (task_stack_clear_words initial done) =
      firstn (Z.to_nat done) (repeat (Some 0) (List.length initial))).
    { unfold task_stack_clear_words, copy_prefix_list.
      rewrite <- Hprefix at 1; apply sublist_app_exact1. }
    rewrite Hsuffix, Hfront; reflexivity.
Qed.
