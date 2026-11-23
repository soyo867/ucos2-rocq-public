Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.kernel_resources.

Import UCOS2_C_Rules.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(**
  The callee does not own, copy, or publish a name.  A caller lends a
  contiguous byte sequence ending in NUL and retains an arbitrary disjoint
  frame.  [readable_name] is the pure name-resource fact; [UCharArray.full]
  is the concrete ownership which discharges each dereference in the C loop.
*)
Definition os_strlen_bytes (p : addr) (chars : list Z) : Assertion :=
  UCharArray.full p (Z.of_nat (S (List.length chars))) (chars ++ [0]).

Definition os_strlen_source (chars : list Z) : list Z := chars ++ [0].

Lemma os_strlen_source_zero_end : forall names base chars i,
  readable_name names base chars ->
  0 <= i <= Zlength chars ->
  unsigned_last_nbits (Znth i (os_strlen_source chars) 0) 32 = 0 ->
  i = Zlength chars.
Proof.
  intros names base chars i [Hchars _] Hi Hzero.
  destruct (Z.eq_dec i (Zlength chars)) as [Heq|Hneq]; [exact Heq|].
  assert (Hstrict : 0 <= i < Zlength chars) by lia.
  unfold os_strlen_source in Hzero.
  rewrite app_Znth1 in Hzero by exact Hstrict.
  rewrite Forall_forall in Hchars.
  assert (Hin : In (Znth i chars 0) chars).
  { unfold Znth; apply nth_In; rewrite Zlength_correct in Hstrict; lia. }
  specialize (Hchars _ Hin).
  rewrite unsigned_last_nbits_eq in Hzero by
    (change (0 <= Znth i chars 0 < 4294967296); lia).
  lia.
Qed.

Lemma os_strlen_seg_merge_reverse : forall (x : addr) lo mid hi (l1 l2 : list Z),
  lo <= mid <= hi ->
  UCharArray.seg x mid hi l2 ** UCharArray.seg x lo mid l1 |--
    UCharArray.seg x lo hi (l1 ++ l2).
Proof.
  intros x lo mid hi l1 l2 Hrange.
  sep_apply_l_atomic (UCharArray.seg_merge_to_seg x lo mid hi l1 l2 Hrange).
  entailer!.
Qed.

Definition os_strlen_readable (names : NameResourceState)
  (p : addr) (chars : list Z) : Prop :=
  readable_name names p chars.

(** Cursor [i] counts bytes already tested.  The suffix includes the current
    byte and, at the exit cursor, exactly the terminating NUL.  The [kernel_u8]
    relation deliberately models INT8U assignment even though the public
    no-wrap precondition below keeps the returned observation exact. *)
Definition os_strlen_loop_state (base : addr) (chars : list Z)
  (i len : Z) (frame : Assertion) : Assertion :=
  coq_prop
    (0 <= i /\ i <= Z.of_nat (List.length chars) /\
     len = kernel_u8 i) &&
  (UCharArray.seg base 0 i (sublist 0 i chars) **
   UCharArray.seg base i (Z.of_nat (S (List.length chars)))
     (sublist i (Z.of_nat (S (List.length chars))) (chars ++ [0])) **
   frame).

Definition os_strlen_loop_residual (base : addr) (chars : list Z)
  (i len : Z) (frame : Assertion) : Assertion :=
  UCharArray.seg base 0 i (sublist 0 i chars) **
  UCharArray.seg base (i + 1) (Z.of_nat (S (List.length chars)))
    (sublist (i + 1) (Z.of_nat (S (List.length chars))) (chars ++ [0])) **
  frame.

Definition os_strlen_success (chars : list Z) (result : Z) : Prop :=
  os_strlen_length_valid chars /\ result = name_length_result chars.

(** The actual INT8U accumulator wraps modulo 256.  The documented short-name
    policy is a sufficient condition for an exact length, not a memory-safety
    precondition of the source loop. *)
Definition os_strlen_result (chars : list Z) (result : Z) : Prop :=
  result = name_length_result chars.

Lemma os_strlen_result_no_wrap : forall chars result,
  os_strlen_length_valid chars ->
  os_strlen_result chars result -> os_strlen_success chars result.
Proof. intros chars result Hlength Hresult; split; assumption. Qed.

Lemma os_strlen_result_in_range : forall chars result,
  os_strlen_result chars result -> 0 <= result < 256.
Proof. intros chars result ->; apply name_length_result_in_range. Qed.

(** The source's API note says "less than 255".  The proof-facing callee
    condition is intentionally the exact weaker no-wrap fact [< 256]; callers
    may establish the documented policy separately. *)
Definition os_strlen_caller_policy (chars : list Z) : Prop :=
  os_strlen_documented_domain chars.

Lemma os_strlen_success_exact : forall chars result,
  os_strlen_success chars result ->
  result = Z.of_nat (List.length chars).
Proof.
  intros chars result [Hlength ->].
  apply name_length_result_exact; exact Hlength.
Qed.

Lemma os_strlen_caller_policy_no_wrap : forall chars,
  os_strlen_caller_policy chars -> os_strlen_length_valid chars.
Proof.
  intros; apply os_strlen_documented_domain_implies_length_valid; exact H.
Qed.

Lemma os_strlen_loop_entry : forall p chars frame,
  os_strlen_bytes p chars ** frame |--
  os_strlen_loop_state p chars 0 0 frame.
Proof.
  intros p chars frame.
  unfold os_strlen_bytes, os_strlen_loop_state.
  replace (Z.of_nat (S (List.length chars)))
    with (0 + Z.of_nat (S (List.length chars))) by lia.
  replace (kernel_u8 0) with 0 by reflexivity.
  (* [full] is the source-level ownership shape, while the loop invariant
     uses a zero-based segment.  Use the library's direction-preserving
     conversion rather than unfolding the list [chars ++ [0]]: the latter
     is not syntactically a cons cell until [chars] is destructed. *)
  sep_apply UCharArray.full_to_seg.
  repeat rewrite Z.add_0_l.
  change (sublist 0 0 (chars ++ [0])) with (@nil Z).
  rewrite UCharArray.seg_empty.
  assert (Hchars : Z.of_nat (S (List.length chars)) =
      Zlength (chars ++ [0])) by
    (rewrite (Zlength_app_cons chars 0), Zlength_correct; simpl; lia).
  rewrite Hchars.
  rewrite (sublist_self (chars ++ [0]) (Zlength (chars ++ [0])) eq_refl).
  entailer!.
Qed.

Lemma os_strlen_loop_exit : forall p chars len frame,
  os_strlen_length_valid chars ->
  os_strlen_loop_state p chars (Z.of_nat (List.length chars)) len frame |--
  coq_prop (len = name_length_result chars) &&
  os_strlen_bytes p chars ** frame.
Proof.
  intros p chars len frame Hlength.
  unfold os_strlen_loop_state, os_strlen_bytes, name_length_result.
  Intros.
  repeat match goal with
  | Hpure : _ /\ _ |- _ => destruct Hpure
  end.
  (* The separation-logic [Intros] tactic may choose a different generated
     hypothesis name as the library evolves.  Match the actual empty prefix
     resource instead of relying on the historical [H0] name. *)
  repeat match goal with
  | Hseg : UCharArray.seg _ _ _ nil |- _ =>
      rewrite UCharArray.seg_empty in Hseg
  end.
  replace (Z.of_nat (List.length chars) + 1)
    with (Z.of_nat (S (List.length chars))) by lia.
  rewrite sublist_self by (rewrite Zlength_correct; lia).
  rewrite kernel_u8_identity by (split; [lia|exact Hlength]).
  repeat match goal with
  | Hlen : len = kernel_u8 (Z.of_nat (List.length chars)) |- _ =>
      rewrite kernel_u8_identity in Hlen
        by (split; [lia|exact Hlength])
  end.
  entailer!.
  assert (Htail :
      sublist (Z.of_nat (List.length chars))
        (Z.of_nat (S (List.length chars))) (chars ++ [0]) = [0]).
  { replace (Z.of_nat (S (List.length chars)))
      with (Z.of_nat (List.length chars) + 1) by lia.
    assert (Hbound : 0 <= Z.of_nat (List.length chars) /\
        Z.of_nat (List.length chars) < Zlength (chars ++ [0])).
    { split; [lia|rewrite (Zlength_app_cons chars 0); rewrite Zlength_correct; simpl; lia]. }
    assert (Hsingle := sublist_single 0 (Z.of_nat (List.length chars))
      (chars ++ [0]) Hbound).
    rewrite Hsingle.
    rewrite (app_Znth2 0 chars [0] (Z.of_nat (List.length chars)))
      by (rewrite Zlength_correct; lia).
    replace (Z.of_nat (List.length chars) - Zlength chars)
      with 0 by (rewrite Zlength_correct; lia).
    simpl; reflexivity. }
  rewrite Htail.
  sep_apply (UCharArray.seg_merge_to_seg p 0
    (Z.of_nat (List.length chars))
    (Z.of_nat (S (List.length chars)))
    chars [0] ltac:(lia)).
  sep_apply UCharArray.seg_to_full.
  replace (p + 0 * sizeof(UCHAR)) with p by lia.
  replace (Z.of_nat (S (List.length chars)) - 0)
    with (Z.of_nat (S (List.length chars))) by lia.
  entailer!.
Qed.
