Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
From compcert.lib Require Import Integers.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Physical byte writes, in execution order.  This is a memory-effect
    component, not an OS rely relation or a new field in a kernel record.
    The permission guard is the ordinary store requirement; no endpoint
    invariant or desired post-state is included in the execution relation.

    A caller must bind this list to its actual source execution.  In
    particular, a pure KernelClientAction trace is NOT such a binding.
    Multi-byte C stores need their actual width/endianness decomposition. *)
Inductive kernel_heap_writes : list (Mem.addr * Mem.byte) -> mem -> mem -> Prop :=
| KernelHeapWritesNil : forall heap, kernel_heap_writes [] heap heap
| KernelHeapWritesCons : forall address stored rest before after,
    before address <> Noperm -> 0 <= stored < 256 ->
    kernel_heap_writes rest (mem_byte_update before address stored) after ->
    kernel_heap_writes ((address, stored) :: rest) before after.

Lemma kernel_heap_writes_deterministic : forall writes before first second,
  kernel_heap_writes writes before first ->
  kernel_heap_writes writes before second -> first = second.
Proof.
  intros writes before first second Hfirst; revert second.
  induction Hfirst; intros second Hsecond; inversion Hsecond; subst; auto.
Qed.

Lemma kernel_heap_writes_frame : forall writes owned after frame whole,
  kernel_heap_writes writes owned after -> mem_join owned frame whole ->
  exists final,
    kernel_heap_writes writes whole final /\ mem_join after frame final.
Proof.
  intros writes owned after frame whole Hwrites; revert whole.
  induction Hwrites as [heap|address stored rest before after Howned Hbyte Htail IH];
    intros whole Hjoin.
  - exists whole; split; [constructor|exact Hjoin].
  - assert (Hwhole : whole address <> Noperm).
    { specialize (Hjoin address); destruct Hjoin as
        [[? [? ?]]|[[? [? ?]]|[[? [? ?]]|[[v [? [? ?]]]|[v [? [? ?]]]]]]];
        congruence. }
    destruct (IH (mem_byte_update whole address stored)
      (mem_join_mem_update_l before frame whole address stored Hjoin Howned))
      as [final [Hrun Hfinal]].
    exists final; split; [econstructor; eassumption|exact Hfinal].
Qed.

Lemma kernel_heap_writes_preserve_framed_byte : forall writes owned after frame whole final address,
  kernel_heap_writes writes owned after ->
  mem_join owned frame whole -> mem_join after frame final ->
  frame address <> Noperm -> final address = whole address.
Proof.
  intros writes owned after frame whole final address Hwrites Hbefore Hafter Howned.
  specialize (Hbefore address); specialize (Hafter address).
  destruct Hbefore as
    [[? [? ?]]|[[? [? ?]]|[[? [? ?]]|[[v [? [? ?]]]|[v [? [? ?]]]]]]];
  destruct Hafter as
    [[? [? ?]]|[[? [? ?]]|[[? [? ?]]|[[v' [? [? ?]]]|[v' [? [? ?]]]]]]];
    congruence.
Qed.

(** Lift only the memory component of the existing QCP local state.
    Changing STS observations/tokens is a separate critical/CPU step. *)
Definition kernel_state_with_memory (state : model) (heap : mem) : model :=
  ConAssertion.mk_Lstate heap state.(ConAssertion.s_STS) state.(ConAssertion.s_token).

Definition kernel_heap_execution (writes : list (Mem.addr * Mem.byte))
  (before after : model) : Prop :=
  kernel_heap_writes writes before.(ConAssertion.s_mem) after.(ConAssertion.s_mem) /\
  after.(ConAssertion.s_STS) = before.(ConAssertion.s_STS) /\
  after.(ConAssertion.s_token) = before.(ConAssertion.s_token).

Lemma kernel_heap_execution_deterministic : forall writes before first second,
  kernel_heap_execution writes before first ->
  kernel_heap_execution writes before second -> first = second.
Proof.
  intros writes before first second [Hfirst [Hsts1 Htokens1]]
    [Hsecond [Hsts2 Htokens2]].
  pose proof (kernel_heap_writes_deterministic _ _ _ _ Hfirst Hsecond) as Hmem.
  destruct first, second; cbn in *; congruence.
Qed.

Lemma kernel_heap_execution_frame : forall writes owned after frame whole,
  kernel_heap_execution writes owned after -> join owned frame whole ->
  exists final, kernel_heap_execution writes whole final /\ join after frame final.
Proof.
  intros writes owned after frame whole [Hrun [Hsts Htokens]]
    [Hmem [Htoken_join Hsts_join]].
  destruct (kernel_heap_writes_frame writes _ _ _ _ Hrun Hmem)
    as [final_heap [Hfinal_run Hfinal_join]].
  exists (kernel_state_with_memory whole final_heap).
  split.
  - split; [exact Hfinal_run|]; split; reflexivity.
  - split; [exact Hfinal_join|]; cbn [kernel_state_with_memory].
    rewrite Hsts, Htokens; split; assumption.
Qed.

(** This produces the new physical whole heap from the actual environment
    writes.  The private frame is the SAME resource, not a fresh assertion
    granted by knowing an invocation number.  Q is established by the
    environment's checked source proof, rather than assumed in execution. *)
Lemma kernel_heap_execution_frame_assertion : forall writes (P Q F : Assertion)
  owned after frame whole,
  (forall initial final, P initial -> kernel_heap_execution writes initial final -> Q final) ->
  P owned -> F frame -> join owned frame whole ->
  kernel_heap_execution writes owned after ->
  exists final, kernel_heap_execution writes whole final /\ (Q ** F) final.
Proof.
  intros writes P Q F owned after frame whole Hproof HP HF Hjoin Hrun.
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin)
    as [final [Hwhole Hfinal]].
  exists final; split; [exact Hwhole|].
  exists after, frame; split; [exact Hfinal|]; split; [eapply Hproof; eassumption|exact HF].
Qed.

Lemma kernel_heap_uchar_store : forall address old stored state,
  0 <= stored < 256 -> (address # UChar |-> old) state ->
  exists final,
    kernel_heap_execution [(address, stored)] state final /\
    (address # UChar |-> stored) final.
Proof.
  intros address old stored state Hstored Hcell.
  unfold store_uchar, store_byte, mstore in Hcell.
  destruct Hcell as [[Haddress [Hnonnegative Hrange]] [encoded [Heqm [Hmem [Hsts Htoken]]]]].
  exists (kernel_state_with_memory state (single_byte_mem address stored)).
  split.
  - split; [|split; reflexivity].
    cbn [kernel_state_with_memory]; rewrite Hmem.
    replace (single_byte_mem address stored) with
      (mem_byte_update (single_byte_mem address encoded) address stored)
      by apply mem_update_single_eq.
    econstructor; [unfold single_byte_mem; rewrite addr_eqb_refl; discriminate|exact Hstored|constructor].
  - unfold store_uchar, store_byte, mstore; cbn [kernel_state_with_memory].
    split; [split; [exact Haddress|]; change (stored >= 0 /\ stored <= 255); lia|].
    exists stored; split; [apply Byte.eqm_refl|].
    split; [reflexivity|]; split; assumption.
Qed.

Lemma kernel_heap_framed_uchar_store : forall address old stored (frame : Assertion) whole,
  0 <= stored < 256 -> (address # UChar |-> old ** frame) whole ->
  exists final,
    kernel_heap_execution [(address, stored)] whole final /\
    (address # UChar |-> stored ** frame) final.
Proof.
  intros address old stored frame whole Hstored
    [cell [rest [Hjoin [Hcell Hrest]]]].
  destruct (kernel_heap_uchar_store address old stored cell Hstored Hcell)
    as [after [Hrun Hafter]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin)
    as [final [Hwhole Hfinal]].
  exists final; split; [exact Hwhole|].
  exists after, rest; split; [exact Hfinal|]; split; assumption.
Qed.

(** A changed shared byte is not a stale snapshot.  This small negative
    result catches attempts to derive a heap update from a pure trace while
    retaining every old shared cell in the caller's ordinary frame. *)
Lemma kernel_heap_store_changed_byte : forall heap address old stored,
  heap address = value old -> old <> stored ->
  mem_byte_update heap address stored address <> heap address.
Proof. intros; rewrite mem_update_eq, H; congruence. Qed.
