Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
From compcert.lib Require Import Integers.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Actual reads of owned QCP memory, using the same modulo-byte encoding
    as mstore. A stored encoded integer need not itself be canonical. The
    lemmas are shared from the checked MutexDel memory-fragment proof; they
    supply no ownership and no environment stability. *)
Module KernelHeapObservation.

Definition uchar_load (address observed : Z) (heap : model) : Prop :=
  0 <= observed < 256 /\
  exists encoded, heap.(ConAssertion.s_mem) address = value encoded /\
    Byte.eqm observed encoded.

Lemma uchar_load_deterministic : forall address first second heap,
  uchar_load address first heap -> uchar_load address second heap -> first = second.
Proof.
  intros address first second heap [Hfirst [x [Hx Hex]]] [Hsecond [y [Hy Hey]]].
  assert (x = y) by congruence; subst y.
  apply Byte.eqm_small_eq;
    [eapply Byte.eqm_trans; [exact Hex|apply Byte.eqm_sym; exact Hey]|exact Hfirst|exact Hsecond].
Qed.

Lemma uchar_store_load : forall address observed heap,
  (address # UChar |-> observed) heap -> uchar_load address observed heap.
Proof.
  intros address observed heap [[Hptr [Hlo Hhi]] [encoded [Heqm [Hmem _]]]].
  split; [change (observed <= 255) in Hhi; lia|].
  exists encoded; split;
    [rewrite Hmem; unfold single_byte_mem; rewrite addr_eqb_refl; reflexivity|exact Heqm].
Qed.

Lemma uchar_load_frame : forall address observed owned frame whole,
  uchar_load address observed owned -> join owned frame whole -> uchar_load address observed whole.
Proof.
  intros address observed owned frame whole [Hrange [encoded [Hbyte Heqm]]] [Hjoin _].
  split; [exact Hrange|]; exists encoded; split; [|exact Heqm].
  exact (proj2 (mem_join_Some3 _ _ _ _ _ Hjoin Hbyte)).
Qed.

Lemma framed_uchar_store_load : forall address observed (frame : Assertion) whole,
  (address # UChar |-> observed ** frame) whole -> uchar_load address observed whole.
Proof.
  intros address observed frame whole [cell [rest [Hjoin [Hcell Hrest]]]].
  eapply uchar_load_frame; [apply uchar_store_load; exact Hcell|exact Hjoin].
Qed.

(** A 32-bit little-endian pointer read observes four actual memory bytes.
    The bytes may use QCP's noncanonical integer encoding: [merge_int]
    already interprets them modulo 256. Only the resulting pointer is
    canonical. This predicate supplies no ownership or interference rule. *)
Definition pointer_load (address observed : Z) (heap : model) : Prop :=
  0 <= observed < 4294967296 /\
  exists b0 b1 b2 b3,
    heap.(ConAssertion.s_mem) address = value b0 /\
    heap.(ConAssertion.s_mem) (address + 1) = value b1 /\
    heap.(ConAssertion.s_mem) (address + 2) = value b2 /\
    heap.(ConAssertion.s_mem) (address + 3) = value b3 /\
    merge_int b0 b1 b2 b3 observed.

Lemma pointer_load_deterministic : forall address first second heap,
  pointer_load address first heap -> pointer_load address second heap -> first = second.
Proof.
  intros address first second heap
    [Hfirst [a [b [c [d [Ha [Hb [Hc [Hd Hmerge]]]]]]]]]
    [Hsecond [a' [b' [c' [d' [Ha' [Hb' [Hc' [Hd' Hmerge']]]]]]]]].
  assert (a = a') by congruence; assert (b = b') by congruence.
  assert (c = c') by congruence; assert (d = d') by congruence; subst a' b' c' d'.
  change (first mod 4294967296 =
    a mod 256 + b mod 256 * 256 + c mod 256 * 65536 + d mod 256 * 16777216) in Hmerge.
  change (second mod 4294967296 =
    a mod 256 + b mod 256 * 256 + c mod 256 * 65536 + d mod 256 * 16777216) in Hmerge'.
  rewrite (Z.mod_small first _ Hfirst) in Hmerge.
  rewrite (Z.mod_small second _ Hsecond) in Hmerge'; congruence.
Qed.

Lemma framed_byte_store_observation : forall address stored (frame : Assertion) whole,
  (store_byte address stored ** frame) whole ->
  exists encoded, whole.(ConAssertion.s_mem) address = value encoded /\ Byte.eqm stored encoded.
Proof.
  intros address stored frame whole [cell [rest [[Hjoin _] [[encoded [Heqm [Hmem _]]] Hrest]]]].
  exists encoded; split; [|exact Heqm].
  assert (Hbyte : cell.(ConAssertion.s_mem) address = value encoded).
  { rewrite Hmem; unfold single_byte_mem; rewrite addr_eqb_refl; reflexivity. }
  exact (proj2 (mem_join_Some3 _ _ _ _ _ Hjoin Hbyte)).
Qed.

Lemma pointer_store_load : forall address observed heap,
  (address # Ptr |-> observed) heap -> pointer_load address observed heap.
Proof.
  intros address observed heap [[Haddress Hrange] Hstore].
  change (store_4byte address observed heap) in Hstore.
  destruct Hstore as [a [b [c [d [Hmerge Hcells]]]]].
  assert (H0 : exists encoded, heap.(ConAssertion.s_mem) address = value encoded /\ Byte.eqm a encoded).
  { apply framed_byte_store_observation with (frame := TT).
    assert (Hfocus : store_byte address a ** (store_byte (address + 1) b **
      (store_byte (address + 2) c ** store_byte (address + 3) d)) |-- store_byte address a ** TT).
    { entailer!; intros ? ?; exact I. }
    exact (Hfocus heap Hcells). }
  assert (H1 : exists encoded, heap.(ConAssertion.s_mem) (address + 1) = value encoded /\ Byte.eqm b encoded).
  { apply framed_byte_store_observation with (frame := TT).
    assert (Hfocus : store_byte address a ** (store_byte (address + 1) b **
      (store_byte (address + 2) c ** store_byte (address + 3) d)) |-- store_byte (address + 1) b ** TT)
      by (entailer!; intros ? ?; exact I); exact (Hfocus heap Hcells). }
  assert (H2 : exists encoded, heap.(ConAssertion.s_mem) (address + 2) = value encoded /\ Byte.eqm c encoded).
  { apply framed_byte_store_observation with (frame := TT).
    assert (Hfocus : store_byte address a ** (store_byte (address + 1) b **
      (store_byte (address + 2) c ** store_byte (address + 3) d)) |-- store_byte (address + 2) c ** TT)
      by (entailer!; intros ? ?; exact I); exact (Hfocus heap Hcells). }
  assert (H3 : exists encoded, heap.(ConAssertion.s_mem) (address + 3) = value encoded /\ Byte.eqm d encoded).
  { apply framed_byte_store_observation with (frame := TT).
    assert (Hfocus : store_byte address a ** (store_byte (address + 1) b **
      (store_byte (address + 2) c ** store_byte (address + 3) d)) |-- store_byte (address + 3) d ** TT)
      by (entailer!; intros ? ?; exact I); exact (Hfocus heap Hcells). }
  destruct H0 as [a' [Ha Heqa]], H1 as [b' [Hb Heqb]],
    H2 as [c' [Hc Heqc]], H3 as [d' [Hd Heqd]].
  split; [unfold valid_ptr_value, addr_max_unsigned in Hrange; cbn in Hrange; lia|].
  exists a', b', c', d'; repeat split; try assumption.
  eapply merge_int_eqm; eassumption.
Qed.

Lemma pointer_load_frame : forall address observed owned frame whole,
  pointer_load address observed owned -> join owned frame whole -> pointer_load address observed whole.
Proof.
  intros address observed owned frame whole
    [Hrange [a [b [c [d [Ha [Hb [Hc [Hd Hmerge]]]]]]]]] [Hjoin _].
  split; [exact Hrange|]. exists a, b, c, d.
  split; [exact (proj2 (mem_join_Some3 _ _ _ _ _ Hjoin Ha))|].
  split; [exact (proj2 (mem_join_Some3 _ _ _ _ _ Hjoin Hb))|].
  split; [exact (proj2 (mem_join_Some3 _ _ _ _ _ Hjoin Hc))|].
  split; [exact (proj2 (mem_join_Some3 _ _ _ _ _ Hjoin Hd))|exact Hmerge].
Qed.

Lemma framed_pointer_store_load : forall address observed (frame : Assertion) whole,
  (address # Ptr |-> observed ** frame) whole -> pointer_load address observed whole.
Proof.
  intros address observed frame whole [cell [rest [Hjoin [Hcell Hrest]]]].
  eapply pointer_load_frame; [apply pointer_store_load; exact Hcell|exact Hjoin].
Qed.

End KernelHeapObservation.
