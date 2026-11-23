Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_init_spec.

Import UCOS2_C_Rules.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Consequences of the real byte-clearing contract, not a second declaration
    asserting that OS_MemClr initializes a typed Queue table. The independent
    bound on its final cursor increment remains a caller obligation. *)
Lemma q_init_undef_node_to_bytes : forall sg qid,
  undef_queue_control_block sg qid |--
  coq_prop (qcb_addr sg qid mod 4 = 0 /\ 0 <= qcb_addr sg qid /\
    qcb_addr sg qid + 24 <= 4294967296) &&
  mem_clr_pre (qcb_addr sg qid) 24.
Proof.
  intros sg qid.
  unfold undef_queue_control_block, OSQPtr_off, OSQStart_off, OSQEnd_off,
    OSQIn_off, OSQOut_off, OSQSize_off, OSQEntries_off.
  set (p := qcb_addr sg qid).
  unfold undef_store_ptr, undef_store_ushort.
  change ptr_size with 4%nat.
  Intros.
  change (p + 0 >= 0 /\ p + 0 + 4 - 1 <= 4294967295 /\
    (p + 0) mod 4 = 0) in H.
  unfold store_4byte_noninit, store_2byte_noninit.
  unfold mem_clr_pre, UCharArray.undef_full, store_undef_array.
  change (Z.to_nat 24) with 24%nat.
  cbn [store_undef_array_rec].
  unfold StoreUCharAsElement.undefstoreA.
  change (sizeof(UCHAR)) with 1.
  unfold undef_store_uchar, isvalidptr_char.
  unfold isvalidptr, isvalidptr_short, aligned_4, aligned_2 in *.
  change addr_max_unsigned with 4294967295 in *.
  assert (Halign : p mod 4 = 0).
  { rewrite Z.add_0_r in H; exact (proj2 (proj2 H)). }
  assert (Hbase : 0 <= p) by lia.
  assert (Hbytes : p + 24 <= 4294967296) by lia.
  repeat match goal with
  | |- context [(p + ?a) + ?b] =>
      replace ((p + a) + b) with (p + (a + b)) by lia
  end.
  cbn.
  entailer!.
Qed.

Lemma q_init_cleared_node_to_typed : forall sg qid,
  0 <= qcb_addr sg qid ->
  qcb_addr sg qid + 24 <= 4294967296 ->
  qcb_addr sg qid mod 4 = 0 ->
  mem_clr_post (qcb_addr sg qid) 24 |--
  zero_queue_control_block sg qid.
Proof.
  intros sg qid Hp Hend Halign.
  unfold zero_queue_control_block, OSQPtr_off, OSQStart_off, OSQEnd_off,
    OSQIn_off, OSQOut_off, OSQSize_off, OSQEntries_off.
  set (p := qcb_addr sg qid) in *.
  unfold mem_clr_post, UCharArray.full, store_array.
  change (repeat_Z 0 24) with
    [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0].
  cbn [store_array_rec].
  unfold StoreUCharAsElement.storeA.
  change (sizeof(UCHAR)) with 1.
  assert (Hptr : forall i, 0 <= i <= 4 -> isvalidptr (p + 4 * i)).
  { intros i Hi.
    change (p + 4 * i >= 0 /\ p + 4 * i + 4 - 1 <= 4294967295 /\
      (p + 4 * i) mod 4 = 0).
    repeat split; try lia.
    rewrite Z.add_mod, Z.mul_mod, Halign by lia; reflexivity. }
  assert (Hshort : forall i, 0 <= i <= 1 -> isvalidptr_short (p + 20 + 2 * i)).
  { intros i Hi.
    change (p + 20 + 2 * i >= 0 /\ p + 20 + 2 * i + 1 <= 4294967295 /\
      (p + 20 + 2 * i) mod 2 = 0).
    repeat split; try lia.
    apply Z.mod_divide; [lia|].
    pose proof (Z.div_mod p 4 ltac:(lia)) as Hdiv; rewrite Halign in Hdiv.
    exists (2 * (p / 4) + 10 + i); lia. }
  pose proof (Hptr 0 ltac:(lia)); pose proof (Hptr 1 ltac:(lia)).
  pose proof (Hptr 2 ltac:(lia)); pose proof (Hptr 3 ltac:(lia)).
  pose proof (Hptr 4 ltac:(lia)).
  pose proof (Hshort 0 ltac:(lia)) as Hshort0.
  pose proof (Hshort 1 ltac:(lia)) as Hshort1.
  replace (p + 20 + 2 * 0) with (p + 20) in Hshort0 by lia.
  replace (p + 20 + 2 * 1) with (p + 22) in Hshort1 by lia.
  unfold store_ptr, store_ushort.
  change ptr_size with 4%nat; cbn.
  unfold store_4byte, store_2byte.
  Exists 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0.
  Exists 0 0 0 0.
  assert (Hvalue : valid_ptr_value 0) by (split; compute; congruence).
  assert (Hmerge_ptr : merge_int 0 0 0 0 0) by reflexivity.
  assert (Hmerge_short : merge_short 0 0 0) by reflexivity.
  unfold store_uchar.
  repeat match goal with
  | |- context [(p + ?a) + ?b] =>
      replace ((p + a) + b) with (p + (a + b)) by lia
  end.
  cbn.
  entailer!.
Qed.

Lemma q_init_undef_bytes_merge : forall p n m,
  0 <= n -> 0 <= m ->
  mem_clr_pre p n ** mem_clr_pre (p + n) m |--
  mem_clr_pre p (n + m).
Proof.
  intros p n m Hn Hm; unfold mem_clr_pre.
  pose proof (UCharArray.undef_full_merge_to_undef_full p n (n + m)
    ltac:(lia)) as Hmerge.
  change (sizeof(UCHAR)) with 1 in Hmerge.
  rewrite Z.mul_1_r in Hmerge.
  replace (n + m - n) with m in Hmerge by lia.
  exact Hmerge.
Qed.

Lemma q_init_undef_table_to_bytes : forall sg,
  queue_first_round_profile sg ->
  queue_table_undef sg |--
  coq_prop (sg.(g_OSQTbl) mod 4 = 0 /\ 0 <= sg.(g_OSQTbl) /\
    sg.(g_OSQTbl) + 96 <= 4294967296) &&
  mem_clr_pre sg.(g_OSQTbl) 96.
Proof.
  intros sg Hprofile; unfold queue_table_undef.
  rewrite (q_init_profile_all_ids sg Hprofile).
  cbn [store_undef_queue_nodes].
  sep_apply_l_atomic (q_init_undef_node_to_bytes sg 0); Intros.
  sep_apply_l_atomic (q_init_undef_node_to_bytes sg 1); Intros.
  sep_apply_l_atomic (q_init_undef_node_to_bytes sg 2); Intros.
  sep_apply_l_atomic (q_init_undef_node_to_bytes sg 3); Intros.
  unfold qcb_addr, sizeof_OS_Q in *.
  set (p := sg.(g_OSQTbl)) in *.
  replace (p + 0 * 24) with p in * by lia.
  replace (p + 1 * 24) with (p + 24) in * by lia.
  replace (p + 2 * 24) with (p + 48) in * by lia.
  replace (p + 3 * 24) with (p + 72) in * by lia.
  replace (p + 72) with ((p + 48) + 24) by lia.
  sep_apply_l_atomic (q_init_undef_bytes_merge (p + 48) 24 24 ltac:(lia) ltac:(lia)).
  replace (24 + 24) with 48 by lia.
  replace (p + 48) with ((p + 24) + 24) by lia.
  sep_apply_l_atomic (q_init_undef_bytes_merge (p + 24) 24 48 ltac:(lia) ltac:(lia)).
  replace (24 + 48) with 72 by lia.
  sep_apply_l_atomic (q_init_undef_bytes_merge p 24 72 ltac:(lia) ltac:(lia)).
  replace (24 + 72) with 96 by lia.
  entailer!.
Qed.

Lemma q_init_cleared_bytes_split : forall p n,
  n = 48 \/ n = 72 \/ n = 96 ->
  mem_clr_post p n |-- mem_clr_post p 24 ** mem_clr_post (p + 24) (n - 24).
Proof.
  intros p n Hn.
  assert (Hrange : 0 <= 24 <= n) by lia.
  pose proof (UCharArray.full_split_to_full p 24 n (repeat_Z 0 n) Hrange) as Hsplit.
  change (sizeof(UCHAR)) with 1 in Hsplit.
  replace (p + 24 * 1) with (p + 24) in Hsplit by lia.
  destruct Hn as [-> | [-> | ->]]; exact Hsplit.
Qed.

Lemma q_init_cleared_table_to_typed : forall sg,
  queue_first_round_profile sg ->
  0 <= sg.(g_OSQTbl) -> sg.(g_OSQTbl) + 96 <= 4294967296 ->
  sg.(g_OSQTbl) mod 4 = 0 ->
  mem_clr_post sg.(g_OSQTbl) 96 |-- queue_table_zero sg.
Proof.
  intros sg Hprofile Hp Hend Halign; unfold queue_table_zero.
  rewrite (q_init_profile_all_ids sg Hprofile).
  cbn [store_zero_queue_nodes].
  set (p := sg.(g_OSQTbl)) in *.
  sep_apply_l_atomic (q_init_cleared_bytes_split p 96 ltac:(auto)).
  change (96 - 24) with 72.
  sep_apply_l_atomic (q_init_cleared_bytes_split (p + 24) 72 ltac:(auto)).
  change (72 - 24) with 48.
  replace (p + 24 + 24) with (p + 48) by lia.
  sep_apply_l_atomic (q_init_cleared_bytes_split (p + 48) 48 ltac:(auto)).
  change (48 - 24) with 24.
  replace (p + 48 + 24) with (p + 72) by lia.
  assert (Hnode : forall qid, 0 <= qid <= 3 ->
    mem_clr_post (p + qid * 24) 24 |-- zero_queue_control_block sg qid).
  { intros qid Hqid; apply q_init_cleared_node_to_typed;
      unfold qcb_addr, sizeof_OS_Q; fold p; try lia.
    rewrite Z.add_mod, Z.mul_mod, Halign by lia.
    change (24 mod 4) with 0; rewrite Z.mul_0_r; reflexivity. }
  pose proof (Hnode 0 ltac:(lia)) as H0.
  pose proof (Hnode 1 ltac:(lia)) as H1.
  pose proof (Hnode 2 ltac:(lia)) as H2.
  pose proof (Hnode 3 ltac:(lia)) as H3.
  replace (p + 0 * 24) with p in H0 by lia.
  replace (p + 1 * 24) with (p + 24) in H1 by lia.
  replace (p + 2 * 24) with (p + 48) in H2 by lia.
  replace (p + 3 * 24) with (p + 72) in H3 by lia.
  sep_apply_l_atomic H0; sep_apply_l_atomic H1.
  sep_apply_l_atomic H2; sep_apply_l_atomic H3; entailer!.
Qed.
