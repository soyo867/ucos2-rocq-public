Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem ConAssertion.
From compcert.lib Require Import Integers.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Shared physical store producers extracted from the checked private
    MutexCreate byte execution. This file adds the arbitrary 32-bit pointer
    store needed by the actual ARM IRQ TCB-SP write. The byte list is the
    effect of ONE typed store, not four interruptible C/ARM instructions.
    It reuses QCP's Arch32/LittleEndian store predicates and memory join. *)
Module KernelHeapStorage.

Lemma heap_writes_append : forall first second before middle after,
  kernel_heap_writes first before middle ->
  kernel_heap_writes second middle after ->
  kernel_heap_writes (first ++ second) before after.
Proof.
  intros first second before middle after Hfirst; revert after.
  induction Hfirst; intros final Hsecond; simpl; [exact Hsecond|].
  econstructor; eauto.
Qed.

Lemma heap_execution_append : forall first second before middle after,
  kernel_heap_execution first before middle ->
  kernel_heap_execution second middle after ->
  kernel_heap_execution (first ++ second) before after.
Proof.
  intros first second before middle after [Hfirst [Hsts1 Htokens1]] [Hsecond [Hsts2 Htokens2]].
  split; [eapply heap_writes_append; eassumption|].
  split; congruence.
Qed.

Lemma byte_noninit_store_execution : forall address stored state,
  0 <= stored < 256 -> store_byte_noninit address state ->
  exists final,
    kernel_heap_execution [(address, stored)] state final /\ store_byte address stored final.
Proof.
  intros address stored state Hstored [Hsts [Htoken Hmem]].
  assert (Howned : state.(ConAssertion.s_mem) address <> Noperm).
  { destruct Hmem as [Hmem|[old Hmem]]; rewrite Hmem;
      unfold single_Noninit_mem, single_byte_mem; rewrite addr_eqb_refl; discriminate. }
  assert (Hupdated : mem_byte_update state.(ConAssertion.s_mem) address stored =
    single_byte_mem address stored).
  { destruct Hmem as [Hmem|[old Hmem]]; rewrite Hmem.
    - apply functional_extensionality; intro other.
      unfold mem_byte_update, single_Noninit_mem, single_byte_mem.
      destruct (addr_eqb other address); reflexivity.
    - apply mem_update_single_eq. }
  exists (kernel_state_with_memory state (mem_byte_update state.(ConAssertion.s_mem) address stored)).
  split.
  - split; [|split; reflexivity].
    cbn [kernel_state_with_memory]; econstructor; [exact Howned|exact Hstored|constructor].
  - exists stored; split; [apply Byte.eqm_refl|].
    cbn [kernel_state_with_memory]; split; [exact Hupdated|]; split; assumption.
Qed.

Lemma framed_byte_noninit_store_execution : forall address stored (frame : Assertion) whole,
  0 <= stored < 256 -> (store_byte_noninit address ** frame) whole ->
  exists final,
    kernel_heap_execution [(address, stored)] whole final /\
    (store_byte address stored ** frame) final.
Proof.
  intros address stored frame whole Hstored [cell [rest [Hjoin [Hcell Hrest]]]].
  destruct (byte_noninit_store_execution address stored cell Hstored Hcell)
    as [after [Hrun Hafter]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin)
    as [final [Hwhole Hfinal]].
  exists final; split; [exact Hwhole|].
  exists after, rest; split; [exact Hfinal|]; split; assumption.
Qed.

Fixpoint byte_list_writes (address : Z) (bytes : list Z) : list (addr * Mem.byte) :=
  match bytes with
  | [] => []
  | stored :: rest => (address, stored) :: byte_list_writes (address + 1) rest
  end.

Fixpoint byte_list_rep (address : Z) (bytes : list Z) : Assertion :=
  match bytes with
  | [] => emp
  | stored :: rest => store_byte address stored ** byte_list_rep (address + 1) rest
  end.

Lemma byte_list_store_execution : forall bytes address (frame : Assertion) before,
  Forall (fun stored => 0 <= stored < 256) bytes ->
  (store_bytes_noninit address (List.length bytes) ** frame) before ->
  exists after,
    kernel_heap_execution (byte_list_writes address bytes) before after /\
    (byte_list_rep address bytes ** frame) after.
Proof.
  induction bytes as [|stored rest IH]; intros address frame before Hranges Hbefore.
  - exists before; split; [split; [constructor|split; reflexivity]|exact Hbefore].
  - inversion Hranges as [|stored0 rest0 Hstored Hrest]; subst.
    assert (Hsplit : store_bytes_noninit address (List.length (stored :: rest)) ** frame |--
      store_byte_noninit address ** (store_bytes_noninit (address + 1) (List.length rest) ** frame)).
    { cbn [List.length store_bytes_noninit]; entailer!. }
    destruct (framed_byte_noninit_store_execution address stored
      (store_bytes_noninit (address + 1) (List.length rest) ** frame) before Hstored (Hsplit _ Hbefore))
      as [middle [Hhead Hmiddle]].
    assert (Hreorder : store_byte address stored **
      (store_bytes_noninit (address + 1) (List.length rest) ** frame) |--
      store_bytes_noninit (address + 1) (List.length rest) ** (store_byte address stored ** frame)) by entailer!.
    destruct (IH (address + 1) (store_byte address stored ** frame) middle Hrest (Hreorder _ Hmiddle))
      as [after [Htail Hafter]].
    exists after; split.
    + change (kernel_heap_execution ([(address, stored)] ++ byte_list_writes (address + 1) rest) before after).
      eapply heap_execution_append; eassumption.
    + assert (Hmerge : byte_list_rep (address + 1) rest ** (store_byte address stored ** frame) |--
        byte_list_rep address (stored :: rest) ** frame).
      { cbn [byte_list_rep]; entailer!. }
      exact (Hmerge _ Hafter).
Qed.

Definition pointer_store_bytes (stored : Z) : list Z :=
  [stored mod 256; (stored / 256) mod 256;
   (stored / 256 / 256) mod 256; (stored / 256 / 256 / 256) mod 256].

Definition pointer_store_writes (address stored : Z) : list (addr * Mem.byte) :=
  byte_list_writes address (pointer_store_bytes stored).

Lemma pointer_store_bytes_in_range : forall stored,
  Forall (fun byte => 0 <= byte < 256) (pointer_store_bytes stored).
Proof. intros; unfold pointer_store_bytes; repeat constructor; apply Z.mod_pos_bound; lia. Qed.

Lemma pointer_store_bytes_merge : forall stored,
  0 <= stored < 4294967296 ->
  merge_int (stored mod 256) ((stored / 256) mod 256)
    ((stored / 256 / 256) mod 256) ((stored / 256 / 256 / 256) mod 256) stored.
Proof.
  intros stored Hrange.
  assert (Hq1 : 0 <= stored / 256 < 16777216).
  { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
  assert (Hq2 : 0 <= stored / 256 / 256 < 65536).
  { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
  assert (Hq3 : 0 <= stored / 256 / 256 / 256 < 256).
  { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
  pose proof (Z.div_mod stored 256 ltac:(lia)) as H0.
  pose proof (Z.div_mod (stored / 256) 256 ltac:(lia)) as H1.
  pose proof (Z.div_mod (stored / 256 / 256) 256 ltac:(lia)) as H2.
  change (stored mod 4294967296 =
    (stored mod 256) mod 256 +
    ((stored / 256) mod 256) mod 256 * 256 +
    ((stored / 256 / 256) mod 256) mod 256 * 65536 +
    ((stored / 256 / 256 / 256) mod 256) mod 256 * 16777216).
  rewrite !Z.mod_mod by lia.
  rewrite (Z.mod_small stored 4294967296 Hrange).
  rewrite (Z.mod_small (stored / 256 / 256 / 256) 256 Hq3).
  lia.
Qed.

Lemma pointer_store_execution : forall address stored before,
  0 <= stored < 4294967296 -> (address # Ptr |->_) before ->
  exists after,
    kernel_heap_execution (pointer_store_writes address stored) before after /\
    (address # Ptr |-> stored) after.
Proof.
  intros address stored before Hrange [Haddress Hbefore].
  change (store_4byte_noninit address before) in Hbefore.
  assert (Hsplit : store_4byte_noninit address |-- store_bytes_noninit address 4 ** emp).
  { unfold store_4byte_noninit; cbn [store_bytes_noninit].
    replace (address + 1 + 1) with (address + 2) by lia.
    replace (address + 2 + 1) with (address + 3) by lia; entailer!. }
  destruct (byte_list_store_execution (pointer_store_bytes stored) address emp before
    (pointer_store_bytes_in_range stored) (Hsplit _ Hbefore)) as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  split; [split; [exact Haddress|]; unfold valid_ptr_value, addr_max_unsigned; cbn; lia|].
  change (store_4byte address stored after).
  exists (stored mod 256), ((stored / 256) mod 256),
    ((stored / 256 / 256) mod 256), ((stored / 256 / 256 / 256) mod 256).
  split; [apply pointer_store_bytes_merge; exact Hrange|].
  assert (Hmerge : byte_list_rep address (pointer_store_bytes stored) ** emp |--
    store_byte address (stored mod 256) **
      (store_byte (address + 1) ((stored / 256) mod 256) **
       (store_byte (address + 2) ((stored / 256 / 256) mod 256) **
        store_byte (address + 3) ((stored / 256 / 256 / 256) mod 256)))).
  { unfold pointer_store_bytes; cbn [byte_list_rep].
    replace (address + 1 + 1) with (address + 2) by lia.
    replace (address + 2 + 1) with (address + 3) by lia; entailer!. }
  exact (Hmerge _ Hafter).
Qed.

Lemma framed_pointer_store_execution : forall address stored (frame : Assertion) whole,
  0 <= stored < 4294967296 -> (address # Ptr |->_ ** frame) whole ->
  exists final,
    kernel_heap_execution (pointer_store_writes address stored) whole final /\
    (address # Ptr |-> stored ** frame) final.
Proof.
  intros address stored frame whole Hrange [cell [rest [Hjoin [Hcell Hrest]]]].
  destruct (pointer_store_execution address stored cell Hrange Hcell) as [after [Hrun Hafter]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin) as [final [Hwhole Hfinal]].
  exists final; split; [exact Hwhole|].
  exists after, rest; split; [exact Hfinal|]; split; assumption.
Qed.

End KernelHeapStorage.
