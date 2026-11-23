Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.VC.code.task.spec.task_stack_clear_spec.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** C-level contract for the original growth-1 OS_TaskStkClr loop.
    The caller supplies one actual writable C array; the mixed UInt array
    records its typed storage. Same-object provenance remains the C/ABI
    interpretation, not a consequence of flat address bounds alone.
    None entries are writable but need not have initialized values.
    The final one-past cursor must be representable.  No pointer or array
    premise is imposed when the source performs no access. *)
Definition task_stk_clr_array_bounds (bottom count : Z) : Prop :=
  0 < bottom /\ bottom mod 4 = 0 /\ bottom + 4 * count <= 4294967295.

Definition task_stk_clr_pre (bottom count options : Z)
  (initial : list (option Z)) : Assertion :=
  if task_stack_clear_enabled options then
    if Z.eqb count 0 then emp
    else “ Zlength initial = count /\ task_stk_clr_array_bounds bottom count ” &&
         UIntArray.mixed_full bottom count initial
  else emp.

(** No-clear paths return emp, so every caller-supplied resource remains in
    the explicit unchanged frame.  On the accessing path this returns the
    exact same array object with every word initialized to zero. *)
Definition task_stk_clr_post (bottom count options : Z)
  (initial : list (option Z)) : Assertion :=
  if task_stack_clear_enabled options then
    if Z.eqb count 0 then emp
    else “ Zlength initial = count /\ task_stk_clr_array_bounds bottom count ” &&
         UIntArray.mixed_full bottom count (repeat (Some 0) (List.length initial))
  else emp.

Definition task_stk_clr_loop (bottom count remaining : Z)
  (initial : list (option Z)) : Assertion :=
  if Z.eqb count 0 then emp
  else “ Zlength initial = count /\ task_stk_clr_array_bounds bottom count ” &&
       task_stack_clear_rep bottom initial (count - remaining).

(** This is precisely the missing current cell of the actual mixed array;
    it retains both the already-zero prefix and the untouched old suffix. *)
Definition task_stk_clr_residual (bottom count remaining : Z)
  (initial : list (option Z)) : Assertion :=
  UIntArray.mixed_missing_i bottom (count - remaining) 0 count
    (task_stack_clear_words initial (count - remaining)).

Lemma task_stk_clr_post_disabled : forall bottom count options initial,
  task_stack_clear_enabled options = false ->
  task_stk_clr_post bottom count options initial = emp.
Proof. intros; unfold task_stk_clr_post; rewrite H; reflexivity. Qed.

Lemma task_stk_clr_post_zero_size : forall bottom options initial,
  task_stk_clr_post bottom 0 options initial = emp.
Proof.
  intros; unfold task_stk_clr_post.
  destruct (task_stack_clear_enabled options); reflexivity.
Qed.

Lemma task_stk_clr_pre_implies_loop_initial : forall bottom count options initial,
  task_stack_clear_enabled options = true ->
  task_stk_clr_pre bottom count options initial |--
  task_stk_clr_loop bottom count count initial.
Proof.
  intros; unfold task_stk_clr_pre, task_stk_clr_loop; rewrite H.
  destruct (Z.eqb count 0); [entailer!|].
  rewrite Z.sub_diag, task_stack_clear_rep_initial.
  Intros.
  repeat match goal with Hpair : _ /\ _ |- _ => destruct Hpair end.
  subst count; entailer!.
Qed.
