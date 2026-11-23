Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.

Import UCOS2_C_Rules.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The public contract forgets incoming byte values, but owns every byte.
    Initialized and mixed inputs can be weakened to this canonical QCP
    undefined-byte array using [UCharArray.full_to_undef_full] and
    [UCharArray.mixed_full_to_undef_full].  The empty array is [emp], including
    at address zero.  No OS invariant or typed-layout consequence is assumed. *)
Definition mem_clr_pre (p n : Z) : Assertion :=
  UCharArray.undef_full p n.

Definition mem_clr_post (p n : Z) : Assertion :=
  UCharArray.full p n (repeat_Z 0 n).

(** Exactly the prefix already visited is zero.  The suffix remains owned;
    discarding its old values does not discard its storage. *)
Definition mem_clr_loop_state (p n remaining : Z) : Assertion :=
  UCharArray.seg p 0 (n - remaining) (repeat_Z 0 (n - remaining)) **
  UCharArray.undef_seg p (n - remaining) n.

(** Structural residual around the next byte, valid for a new zero value. *)
Definition mem_clr_loop_residual (p n remaining : Z) : Assertion :=
  UCharArray.seg p 0 (n - remaining) (repeat_Z 0 (n - remaining)) **
  UCharArray.undef_seg p (n - remaining + 1) n.

Lemma mem_clr_pre_to_loop_state : forall p n,
  mem_clr_pre p n |-- mem_clr_loop_state p n n.
Proof.
  intros p n; unfold mem_clr_pre, mem_clr_loop_state.
  replace (n - n) with 0 by lia.
  change (repeat_Z 0 0) with (@nil Z); rewrite UCharArray.seg_empty.
  sep_apply UCharArray.undef_full_to_undef_seg; entailer!.
Qed.

Lemma mem_clr_loop_state_split_byte : forall p n remaining,
  0 < remaining <= n ->
  mem_clr_loop_state p n remaining |--
  (p + (n - remaining)) # UChar |->_ **
  mem_clr_loop_residual p n remaining.
Proof.
  intros p n remaining Hremaining.
  unfold mem_clr_loop_state, mem_clr_loop_residual.
  rewrite UCharArray.undef_seg_unfold by lia.
  unfold StoreUCharAsElement.undefstoreA.
  change (sizeof(UCHAR)) with 1.
  replace (p + (n - remaining) * 1) with (p + (n - remaining)) by lia.
  entailer!.
Qed.

Lemma mem_clr_loop_state_merge_zero_byte : forall p n remaining,
  0 < remaining <= n ->
  (p + (n - remaining)) # UChar |-> 0 **
  mem_clr_loop_residual p n remaining |--
  mem_clr_loop_state p n (remaining - 1).
Proof.
  intros p n remaining Hremaining.
  unfold mem_clr_loop_residual, mem_clr_loop_state.
  replace (n - (remaining - 1)) with (n - remaining + 1) by lia.
  rewrite repeat_Z_tail by lia.
  replace (p + (n - remaining)) with
    (p + (n - remaining) * sizeof(UCHAR)) by
    (change (sizeof(UCHAR)) with 1; lia).
  fold (StoreUCharAsElement.storeA p (n - remaining) 0).
  sep_apply UCharArray.seg_single.
  sep_apply (UCharArray.seg_merge_to_seg p 0 (n - remaining)
    (n - remaining + 1) (repeat_Z 0 (n - remaining)) [0]);
    [|lia].
  entailer!.
Qed.

Lemma mem_clr_loop_state_to_post : forall p n,
  mem_clr_loop_state p n 0 |-- mem_clr_post p n.
Proof.
  intros p n; unfold mem_clr_loop_state, mem_clr_post.
  replace (n - 0) with n by lia.
  rewrite UCharArray.undef_seg_empty.
  unfold UCharArray.full, UCharArray.seg, store_array.
  entailer!.
Qed.
