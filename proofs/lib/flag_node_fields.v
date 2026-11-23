Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.flag_stack.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagNodeFieldStorage := FieldStorage Arch32 LittleEndian
  UCOS2_C_Rules UCOS2_C_Rules UCOS2_C_Rules UCOS2_C_Rules.

(** The local OS_FLAG_NODE exposed by the selected frontend has six typed
    fields.  This companion representation does not change the full-byte
    Flag interfaces.  Structure-relative addresses use the existing layout;
    an actual C local still needs its own proved field-address binding.
    No task-stack address, padding owner or allocation is inferred here. *)
Definition flag_node_fields_rep (c : KernelConfiguration) (p : addr)
  (v : FlagNodeImage) : Assertion :=
  p # Ptr |-> v.(flagNodeNext) ** (p + 4) # Ptr |-> v.(flagNodePrev) **
  (p + 8) # Ptr |-> v.(flagNodeTCB) ** (p + 12) # Ptr |-> v.(flagNodeGroup) **
  flag_word_rep c (p + 16) v.(flagNodeMask) **
  (p + flag_node_mode_offset c) # UChar |-> v.(flagNodeMode).

Definition flag_node_fields_uninit_rep (c : KernelConfiguration) (p : addr) : Assertion :=
  p # Ptr |->_ ** (p + 4) # Ptr |->_ ** (p + 8) # Ptr |->_ ** (p + 12) # Ptr |->_ **
  (if Z.eqb c.(cfgFlagBits) 8 then (p + 16) # UChar |->_ else
   if Z.eqb c.(cfgFlagBits) 16 then (p + 16) # UShort |->_ else (p + 16) # UInt |->_) **
  (p + flag_node_mode_offset c) # UChar |->_.

Definition flag_node_padding_rep (c : KernelConfiguration) (p : addr)
  (v : FlagNodeImage) : Assertion :=
  store_optional_bytes (p + flag_node_mode_offset c + 1) v.(flagNodePadding).

Definition flag_node_padding_uninit_rep (c : KernelConfiguration) (p : addr) : Assertion :=
  store_optional_bytes (p + flag_node_mode_offset c + 1)
    (repeat None (Z.to_nat (flag_node_size c - flag_node_mode_offset c - 1))).

Definition flag_node_fields_return_loan (c : KernelConfiguration)
  (w : FlagWaiterState) : Assertion :=
  flag_node_fields_rep c w.(flagNodeAddr) w.(flagWaitImage).

Lemma flag_node_rep_fields_padding : forall c p v,
  flag_node_rep c p v --||--
    flag_node_fields_rep c p v ** flag_node_padding_rep c p v.
Proof.
  intros; unfold flag_node_rep, flag_node_fields_rep, flag_node_padding_rep;
    split; entailer!.
Qed.

Lemma flag_node_uninit_rep_fields_padding : forall c p,
  flag_node_uninit_rep c p --||--
    flag_node_fields_uninit_rep c p ** flag_node_padding_uninit_rep c p.
Proof.
  intros; unfold flag_node_uninit_rep, flag_node_fields_uninit_rep,
    flag_node_padding_uninit_rep; split; entailer!.
Qed.

Lemma flag_node_return_loan_fields_padding : forall c w,
  flag_node_return_loan c w --||--
    flag_node_fields_return_loan c w **
    flag_node_padding_rep c w.(flagNodeAddr) w.(flagWaitImage).
Proof. intros; apply flag_node_rep_fields_padding. Qed.

Lemma flag_node_fields_rep_selected : forall p v,
  flag_node_fields_rep selected_kernel_configuration p v =
  (p # Ptr |-> v.(flagNodeNext) ** (p + 4) # Ptr |-> v.(flagNodePrev) **
   (p + 8) # Ptr |-> v.(flagNodeTCB) ** (p + 12) # Ptr |-> v.(flagNodeGroup) **
   (p + 16) # UShort |-> v.(flagNodeMask) ** (p + 18) # UChar |-> v.(flagNodeMode)).
Proof. reflexivity. Qed.

Lemma flag_node_fields_uninit_rep_selected : forall p,
  flag_node_fields_uninit_rep selected_kernel_configuration p =
  (p # Ptr |->_ ** (p + 4) # Ptr |->_ ** (p + 8) # Ptr |->_ **
   (p + 12) # Ptr |->_ ** (p + 16) # UShort |->_ ** (p + 18) # UChar |->_).
Proof. reflexivity. Qed.

Lemma flag_node_padding_uninit_rep_selected : forall p,
  flag_node_padding_uninit_rep selected_kernel_configuration p =
    store_optional_bytes (p + 19) [None].
Proof.
  intro p; unfold flag_node_padding_uninit_rep.
  change (store_optional_bytes (p + 18 + 1) [None] =
    store_optional_bytes (p + 19) [None]).
  replace (p + 18 + 1) with (p + 19) by lia; reflexivity.
Qed.

(** Forget values without relinquishing any field cell.  This is the
    exposure needed before a genuine frontend scope transition, not a
    separation-logic deallocation theorem. *)
Lemma flag_node_fields_rep_to_uninit : forall c p v,
  flag_node_fields_rep c p v |-- flag_node_fields_uninit_rep c p.
Proof.
  intros c p v; unfold flag_node_fields_rep, flag_node_fields_uninit_rep,
    flag_word_rep.
  sep_apply_l_atomic (store_ptr_undef_store_ptr p v.(flagNodeNext)).
  sep_apply_l_atomic (store_ptr_undef_store_ptr (p + 4) v.(flagNodePrev)).
  sep_apply_l_atomic (store_ptr_undef_store_ptr (p + 8) v.(flagNodeTCB)).
  sep_apply_l_atomic (store_ptr_undef_store_ptr (p + 12) v.(flagNodeGroup)).
  sep_apply_l_atomic (store_uchar_undef_store_uchar
    (p + flag_node_mode_offset c) v.(flagNodeMode)).
  destruct (Z.eqb c.(cfgFlagBits) 8), (Z.eqb c.(cfgFlagBits) 16).
  - sep_apply_l_atomic (store_uchar_undef_store_uchar (p + 16) v.(flagNodeMask)); entailer!.
  - sep_apply_l_atomic (store_uchar_undef_store_uchar (p + 16) v.(flagNodeMask)); entailer!.
  - sep_apply_l_atomic (store_ushort_undef_store_ushort (p + 16) v.(flagNodeMask)); entailer!.
  - sep_apply_l_atomic (store_uint_undef_store_uint (p + 16) v.(flagNodeMask)); entailer!.
Qed.

Lemma flag_node_fields_return_loan_to_uninit : forall c w,
  flag_node_fields_return_loan c w |-- flag_node_fields_uninit_rep c w.(flagNodeAddr).
Proof. intros; apply flag_node_fields_rep_to_uninit. Qed.

(** These are supplied address equalities, never an allocation/ABI axiom.
    They let a caller expose exactly its six actual local-field atoms. *)
Lemma flag_node_fields_uninit_rep_at_addresses : forall p next prev tcb grp flags mode,
  next = p -> prev = p + 4 -> tcb = p + 8 -> grp = p + 12 ->
  flags = p + 16 -> mode = p + 18 ->
  flag_node_fields_uninit_rep selected_kernel_configuration p =
    (next # Ptr |->_ ** prev # Ptr |->_ ** tcb # Ptr |->_ **
     grp # Ptr |->_ ** flags # UShort |->_ ** mode # UChar |->_).
Proof. intros; subst; apply flag_node_fields_uninit_rep_selected. Qed.

Definition flag_node_fields_rep_without_next (c : KernelConfiguration) (p : addr)
  (v : FlagNodeImage) : Assertion :=
  (p + 4) # Ptr |-> v.(flagNodePrev) ** (p + 8) # Ptr |-> v.(flagNodeTCB) **
  (p + 12) # Ptr |-> v.(flagNodeGroup) ** flag_word_rep c (p + 16) v.(flagNodeMask) **
  (p + flag_node_mode_offset c) # UChar |-> v.(flagNodeMode).

Definition flag_node_fields_rep_without_prev (c : KernelConfiguration) (p : addr)
  (v : FlagNodeImage) : Assertion :=
  p # Ptr |-> v.(flagNodeNext) ** (p + 8) # Ptr |-> v.(flagNodeTCB) **
  (p + 12) # Ptr |-> v.(flagNodeGroup) ** flag_word_rep c (p + 16) v.(flagNodeMask) **
  (p + flag_node_mode_offset c) # UChar |-> v.(flagNodeMode).

Lemma flag_node_fields_rep_split_next : forall c p v,
  flag_node_fields_rep c p v |--
    p # Ptr |-> v.(flagNodeNext) ** flag_node_fields_rep_without_next c p v.
Proof. intros; unfold flag_node_fields_rep, flag_node_fields_rep_without_next; entailer!. Qed.

Lemma flag_node_fields_rep_merge_next : forall c p v,
  p # Ptr |-> v.(flagNodeNext) ** flag_node_fields_rep_without_next c p v |--
    flag_node_fields_rep c p v.
Proof. intros; unfold flag_node_fields_rep, flag_node_fields_rep_without_next; entailer!. Qed.

Lemma flag_node_fields_rep_merge_updated_next : forall c p v next,
  p # Ptr |-> next ** flag_node_fields_rep_without_next c p v |--
    flag_node_fields_rep c p (flag_node_set_links v next v.(flagNodePrev)).
Proof.
  intros; unfold flag_node_fields_rep, flag_node_fields_rep_without_next,
    flag_node_set_links; cbn; entailer!.
Qed.

Lemma flag_node_fields_rep_split_prev : forall c p v,
  flag_node_fields_rep c p v |--
    (p + 4) # Ptr |-> v.(flagNodePrev) ** flag_node_fields_rep_without_prev c p v.
Proof. intros; unfold flag_node_fields_rep, flag_node_fields_rep_without_prev; entailer!. Qed.

Lemma flag_node_fields_rep_merge_prev : forall c p v,
  (p + 4) # Ptr |-> v.(flagNodePrev) ** flag_node_fields_rep_without_prev c p v |--
    flag_node_fields_rep c p v.
Proof. intros; unfold flag_node_fields_rep, flag_node_fields_rep_without_prev; entailer!. Qed.

Lemma flag_node_fields_rep_merge_updated_prev : forall c p v prev,
  (p + 4) # Ptr |-> prev ** flag_node_fields_rep_without_prev c p v |--
    flag_node_fields_rep c p (flag_node_set_links v v.(flagNodeNext) prev).
Proof.
  intros; unfold flag_node_fields_rep, flag_node_fields_rep_without_prev,
    flag_node_set_links; cbn; entailer!.
Qed.

Lemma flag_node_padding_rep_set_links_eq : forall c p v next prev,
  flag_node_padding_rep c p (flag_node_set_links v next prev) =
    flag_node_padding_rep c p v.
Proof. reflexivity. Qed.

Lemma flag_block_node_padding_rep_eq : forall sg w tcb head,
  flag_node_padding_rep sg.(osKernelConfig) w.(flagNodeAddr)
    (flag_block_node_image sg w tcb head) =
  flag_node_padding_rep sg.(osKernelConfig) w.(flagNodeAddr) w.(flagWaitImage).
Proof. reflexivity. Qed.

Definition flag_wait_nodes_fields_rep (sg : StableGlobVars)
  (nodes : addr -> option FlagWaiterState) : Assertion :=
  store_map (fun p w => flag_node_fields_rep sg.(osKernelConfig) p w.(flagWaitImage)) nodes.

Definition flag_wait_nodes_fields_without_node (sg : StableGlobVars)
  (nodes : addr -> option FlagWaiterState) (p : addr) : Assertion :=
  store_map_missing_i
    (fun p w => flag_node_fields_rep sg.(osKernelConfig) p w.(flagWaitImage)) nodes p.

Definition flag_wait_nodes_padding_rep (sg : StableGlobVars)
  (nodes : addr -> option FlagWaiterState) : Assertion :=
  store_map (fun p w => flag_node_padding_rep sg.(osKernelConfig) p w.(flagWaitImage)) nodes.

(** The policy records which nodes have actual supplemental padding owners.
    False supplies emp for that padding component only; the six typed fields
    remain in flag_wait_nodes_fields_rep.  It may cover multiple local nodes.
    It is not a capability or permission derived from a ghost identity. *)
Definition flag_node_padding_policy_rep (c : KernelConfiguration)
  (owns : addr -> bool) (p : addr) (v : FlagNodeImage) : Assertion :=
  if owns p then flag_node_padding_rep c p v else emp.

Definition flag_wait_nodes_padding_policy_rep (sg : StableGlobVars)
  (owns : addr -> bool) (nodes : addr -> option FlagWaiterState) : Assertion :=
  store_map (fun p w =>
    flag_node_padding_policy_rep sg.(osKernelConfig) owns p w.(flagWaitImage)) nodes.

Definition flag_wait_nodes_padding_policy_without_node (sg : StableGlobVars)
  (owns : addr -> bool) (nodes : addr -> option FlagWaiterState) (p : addr) : Assertion :=
  store_map_missing_i (fun p w =>
    flag_node_padding_policy_rep sg.(osKernelConfig) owns p w.(flagWaitImage)) nodes p.

(** This uses the checked finite-support distribution law: each map retains
    a NoDup support list, and the reverse direction aligns the two lists by
    permutation.  No finite-support hypothesis is silently discarded. *)
Lemma flag_wait_nodes_rep_fields_padding : forall sg nodes,
  flag_wait_nodes_rep sg nodes --||--
    flag_wait_nodes_fields_rep sg nodes ** flag_wait_nodes_padding_rep sg nodes.
Proof.
  intros sg nodes.
  assert (Hcells : flag_wait_nodes_rep sg nodes --||--
    store_map (fun p w =>
      flag_node_fields_rep sg.(osKernelConfig) p w.(flagWaitImage) **
      flag_node_padding_rep sg.(osKernelConfig) p w.(flagWaitImage)) nodes).
  { unfold flag_wait_nodes_rep; split; apply FlagNodeFieldStorage.store_map_mono;
      intros p w Hw.
    - apply (proj1 (flag_node_rep_fields_padding _ _ _)).
    - apply (proj2 (flag_node_rep_fields_padding _ _ _)). }
  rewrite Hcells.
  apply FlagNodeFieldStorage.store_map_sepcon.
Qed.

Lemma flag_wait_nodes_padding_policy_all : forall sg nodes,
  flag_wait_nodes_padding_policy_rep sg (fun _ => true) nodes =
    flag_wait_nodes_padding_rep sg nodes.
Proof. reflexivity. Qed.

Lemma flag_wait_nodes_padding_policy_live : forall sg owns nodes,
  (forall p w, nodes p = Some w -> owns p = true) ->
  flag_wait_nodes_padding_policy_rep sg owns nodes --||--
    flag_wait_nodes_padding_rep sg nodes.
Proof.
  intros sg owns nodes Howns.
  unfold flag_wait_nodes_padding_policy_rep, flag_wait_nodes_padding_rep;
    split; apply FlagNodeFieldStorage.store_map_mono; intros p w Hw;
    unfold flag_node_padding_policy_rep; rewrite (Howns p w Hw); reflexivity.
Qed.

Lemma flag_node_padding_policy_unowned : forall c owns p v,
  owns p = false -> flag_node_padding_policy_rep c owns p v = emp.
Proof. intros; unfold flag_node_padding_policy_rep; rewrite H; reflexivity. Qed.

(** The generic helper is restricted to the existing address-keyed waiter
    map.  Its missing predicate is MapLib's actual finite residual. *)
Lemma flag_waiter_store_map_missing_remove : forall
  (P : addr -> FlagWaiterState -> Assertion) nodes p,
  store_map_missing_i P nodes p --||-- store_map P (kernel_map_set nodes p None).
Proof.
  intros P nodes p.
  assert (Hframe : forall q, q <> p -> nodes q = kernel_map_set nodes p None q)
    by (intros; symmetry; apply kernel_map_set_other; assumption).
  rewrite (store_map_missing_i_equiv P _ _ p Hframe).
  split.
  - apply store_map_missing_equiv_store_map; apply kernel_map_set_same.
  - apply store_map_equiv_store_map_missing; apply kernel_map_set_same.
Qed.

Lemma flag_waiter_store_map_merge_updated : forall
  (P : addr -> FlagWaiterState -> Assertion) nodes p w,
  P p w ** store_map_missing_i P nodes p |--
    store_map P (kernel_map_set nodes p (Some w)).
Proof.
  intros P nodes p w.
  assert (Hframe : forall q, q <> p -> nodes q = kernel_map_set nodes p (Some w) q)
    by (intros; symmetry; apply kernel_map_set_other; assumption).
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv P _ _ p Hframe)).
  sep_apply_l_atomic (store_map_merge P p w _ (kernel_map_set_same _ nodes p (Some w))).
  entailer!.
Qed.

Lemma flag_waiter_store_map_insert : forall
  (P : addr -> FlagWaiterState -> Assertion) nodes p w,
  nodes p = None ->
  P p w ** store_map P nodes |-- store_map P (kernel_map_set nodes p (Some w)).
Proof.
  intros P nodes p w Hnone.
  sep_apply_l_atomic (store_map_equiv_store_map_missing P nodes p Hnone).
  sep_apply_l_atomic (flag_waiter_store_map_merge_updated P nodes p w); entailer!.
Qed.

Lemma flag_waiter_store_map_remove : forall
  (P : addr -> FlagWaiterState -> Assertion) nodes p w,
  nodes p = Some w ->
  store_map P nodes --||-- P p w ** store_map P (kernel_map_set nodes p None).
Proof.
  intros P nodes p w Hw.
  rewrite <- (flag_waiter_store_map_missing_remove P nodes p); split.
  - sep_apply_l_atomic (store_map_split P p w nodes Hw); entailer!.
  - sep_apply_l_atomic (store_map_merge P p w nodes Hw); entailer!.
Qed.

Lemma flag_wait_nodes_fields_rep_split_node : forall sg nodes p w,
  nodes p = Some w -> flag_wait_nodes_fields_rep sg nodes |--
    flag_node_fields_rep sg.(osKernelConfig) p w.(flagWaitImage) **
    flag_wait_nodes_fields_without_node sg nodes p.
Proof.
  intros; unfold flag_wait_nodes_fields_rep, flag_wait_nodes_fields_without_node.
  sep_apply_l_atomic (store_map_split
    (fun p w => flag_node_fields_rep sg.(osKernelConfig) p w.(flagWaitImage)) p w nodes H);
    entailer!.
Qed.

Lemma flag_wait_nodes_fields_rep_merge_node : forall sg nodes p w,
  nodes p = Some w ->
  flag_node_fields_rep sg.(osKernelConfig) p w.(flagWaitImage) **
  flag_wait_nodes_fields_without_node sg nodes p |-- flag_wait_nodes_fields_rep sg nodes.
Proof.
  intros; unfold flag_wait_nodes_fields_rep, flag_wait_nodes_fields_without_node.
  sep_apply_l_atomic (store_map_merge
    (fun p w => flag_node_fields_rep sg.(osKernelConfig) p w.(flagWaitImage)) p w nodes H);
    entailer!.
Qed.

Lemma flag_wait_nodes_fields_rep_merge_updated_node : forall sg nodes p w,
  flag_node_fields_rep sg.(osKernelConfig) p w.(flagWaitImage) **
  flag_wait_nodes_fields_without_node sg nodes p |--
    flag_wait_nodes_fields_rep sg (kernel_map_set nodes p (Some w)).
Proof.
  intros; exact (flag_waiter_store_map_merge_updated
    (fun p w => flag_node_fields_rep sg.(osKernelConfig) p w.(flagWaitImage)) nodes p w).
Qed.

Lemma flag_wait_nodes_fields_rep_insert_node : forall sg nodes p w,
  nodes p = None ->
  flag_node_fields_rep sg.(osKernelConfig) p w.(flagWaitImage) **
  flag_wait_nodes_fields_rep sg nodes |--
    flag_wait_nodes_fields_rep sg (kernel_map_set nodes p (Some w)).
Proof.
  intros; exact (flag_waiter_store_map_insert
    (fun p w => flag_node_fields_rep sg.(osKernelConfig) p w.(flagWaitImage)) nodes p w H).
Qed.

Lemma flag_wait_nodes_fields_rep_remove_node : forall sg nodes p w,
  nodes p = Some w -> flag_wait_nodes_fields_rep sg nodes --||--
    flag_node_fields_rep sg.(osKernelConfig) p w.(flagWaitImage) **
    flag_wait_nodes_fields_rep sg (kernel_map_set nodes p None).
Proof.
  intros; exact (flag_waiter_store_map_remove
    (fun p w => flag_node_fields_rep sg.(osKernelConfig) p w.(flagWaitImage)) nodes p w H).
Qed.

Lemma flag_wait_nodes_fields_rep_split_next : forall sg nodes p w,
  nodes p = Some w -> flag_wait_nodes_fields_rep sg nodes |--
    p # Ptr |-> w.(flagWaitImage).(flagNodeNext) **
    flag_node_fields_rep_without_next sg.(osKernelConfig) p w.(flagWaitImage) **
    flag_wait_nodes_fields_without_node sg nodes p.
Proof.
  intros; sep_apply_l_atomic (flag_wait_nodes_fields_rep_split_node sg nodes p w H).
  sep_apply_l_atomic (flag_node_fields_rep_split_next sg.(osKernelConfig) p w.(flagWaitImage)).
  entailer!.
Qed.

Lemma flag_wait_nodes_fields_rep_merge_updated_next : forall sg nodes p w next,
  nodes p = Some w ->
  p # Ptr |-> next **
  flag_node_fields_rep_without_next sg.(osKernelConfig) p w.(flagWaitImage) **
  flag_wait_nodes_fields_without_node sg nodes p |--
    flag_wait_nodes_fields_rep sg (flag_nodes_set_next nodes p next).
Proof.
  intros sg nodes p w next Hw.
  sep_apply_l_atomic (flag_node_fields_rep_merge_updated_next
    sg.(osKernelConfig) p w.(flagWaitImage) next).
  unfold flag_nodes_set_next; rewrite Hw; cbn [option_map].
  pose proof (flag_wait_nodes_fields_rep_merge_updated_node sg nodes p
    (flag_waiter_set_image w (flag_node_set_links w.(flagWaitImage) next w.(flagWaitImage).(flagNodePrev)))) as Hmerge.
  cbv beta iota delta [flag_waiter_set_image flagWaitImage] in Hmerge.
  fold (flagWaitImage w) in Hmerge.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma flag_wait_nodes_fields_rep_split_prev : forall sg nodes p w,
  nodes p = Some w -> flag_wait_nodes_fields_rep sg nodes |--
    (p + 4) # Ptr |-> w.(flagWaitImage).(flagNodePrev) **
    flag_node_fields_rep_without_prev sg.(osKernelConfig) p w.(flagWaitImage) **
    flag_wait_nodes_fields_without_node sg nodes p.
Proof.
  intros; sep_apply_l_atomic (flag_wait_nodes_fields_rep_split_node sg nodes p w H).
  sep_apply_l_atomic (flag_node_fields_rep_split_prev sg.(osKernelConfig) p w.(flagWaitImage)).
  entailer!.
Qed.

Lemma flag_wait_nodes_fields_rep_merge_updated_prev : forall sg nodes p w prev,
  nodes p = Some w ->
  (p + 4) # Ptr |-> prev **
  flag_node_fields_rep_without_prev sg.(osKernelConfig) p w.(flagWaitImage) **
  flag_wait_nodes_fields_without_node sg nodes p |--
    flag_wait_nodes_fields_rep sg (flag_nodes_set_prev nodes p prev).
Proof.
  intros sg nodes p w prev Hw.
  sep_apply_l_atomic (flag_node_fields_rep_merge_updated_prev
    sg.(osKernelConfig) p w.(flagWaitImage) prev).
  unfold flag_nodes_set_prev; rewrite Hw; cbn [option_map].
  pose proof (flag_wait_nodes_fields_rep_merge_updated_node sg nodes p
    (flag_waiter_set_image w (flag_node_set_links w.(flagWaitImage) w.(flagWaitImage).(flagNodeNext) prev))) as Hmerge.
  cbv beta iota delta [flag_waiter_set_image flagWaitImage] in Hmerge.
  fold (flagWaitImage w) in Hmerge.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma flag_wait_nodes_padding_policy_rep_split_node : forall sg owns nodes p w,
  nodes p = Some w -> flag_wait_nodes_padding_policy_rep sg owns nodes |--
    flag_node_padding_policy_rep sg.(osKernelConfig) owns p w.(flagWaitImage) **
    flag_wait_nodes_padding_policy_without_node sg owns nodes p.
Proof.
  intros; unfold flag_wait_nodes_padding_policy_rep, flag_wait_nodes_padding_policy_without_node.
  sep_apply_l_atomic (store_map_split
    (fun p w => flag_node_padding_policy_rep sg.(osKernelConfig) owns p w.(flagWaitImage))
    p w nodes H); entailer!.
Qed.

Lemma flag_wait_nodes_padding_policy_rep_merge_node : forall sg owns nodes p w,
  nodes p = Some w ->
  flag_node_padding_policy_rep sg.(osKernelConfig) owns p w.(flagWaitImage) **
  flag_wait_nodes_padding_policy_without_node sg owns nodes p |--
    flag_wait_nodes_padding_policy_rep sg owns nodes.
Proof.
  intros; unfold flag_wait_nodes_padding_policy_rep, flag_wait_nodes_padding_policy_without_node.
  sep_apply_l_atomic (store_map_merge
    (fun p w => flag_node_padding_policy_rep sg.(osKernelConfig) owns p w.(flagWaitImage))
    p w nodes H); entailer!.
Qed.

Lemma flag_wait_nodes_padding_policy_rep_merge_updated_node : forall sg owns nodes p w,
  flag_node_padding_policy_rep sg.(osKernelConfig) owns p w.(flagWaitImage) **
  flag_wait_nodes_padding_policy_without_node sg owns nodes p |--
    flag_wait_nodes_padding_policy_rep sg owns (kernel_map_set nodes p (Some w)).
Proof.
  intros; exact (flag_waiter_store_map_merge_updated
    (fun p w => flag_node_padding_policy_rep sg.(osKernelConfig) owns p w.(flagWaitImage)) nodes p w).
Qed.

Lemma flag_wait_nodes_padding_policy_rep_insert_node : forall sg owns nodes p w,
  nodes p = None ->
  flag_node_padding_policy_rep sg.(osKernelConfig) owns p w.(flagWaitImage) **
  flag_wait_nodes_padding_policy_rep sg owns nodes |--
    flag_wait_nodes_padding_policy_rep sg owns (kernel_map_set nodes p (Some w)).
Proof.
  intros; exact (flag_waiter_store_map_insert
    (fun p w => flag_node_padding_policy_rep sg.(osKernelConfig) owns p w.(flagWaitImage)) nodes p w H).
Qed.

Lemma flag_wait_nodes_padding_policy_rep_remove_node : forall sg owns nodes p w,
  nodes p = Some w -> flag_wait_nodes_padding_policy_rep sg owns nodes --||--
    flag_node_padding_policy_rep sg.(osKernelConfig) owns p w.(flagWaitImage) **
    flag_wait_nodes_padding_policy_rep sg owns (kernel_map_set nodes p None).
Proof.
  intros; exact (flag_waiter_store_map_remove
    (fun p w => flag_node_padding_policy_rep sg.(osKernelConfig) owns p w.(flagWaitImage)) nodes p w H).
Qed.

Lemma flag_wait_nodes_padding_rep_insert_node : forall sg nodes p w,
  nodes p = None ->
  flag_node_padding_rep sg.(osKernelConfig) p w.(flagWaitImage) **
  flag_wait_nodes_padding_rep sg nodes |--
    flag_wait_nodes_padding_rep sg (kernel_map_set nodes p (Some w)).
Proof.
  intros; exact (flag_waiter_store_map_insert
    (fun p w => flag_node_padding_rep sg.(osKernelConfig) p w.(flagWaitImage)) nodes p w H).
Qed.

Lemma flag_wait_nodes_padding_rep_remove_node : forall sg nodes p w,
  nodes p = Some w -> flag_wait_nodes_padding_rep sg nodes --||--
    flag_node_padding_rep sg.(osKernelConfig) p w.(flagWaitImage) **
    flag_wait_nodes_padding_rep sg (kernel_map_set nodes p None).
Proof.
  intros; exact (flag_waiter_store_map_remove
    (fun p w => flag_node_padding_rep sg.(osKernelConfig) p w.(flagWaitImage)) nodes p w H).
Qed.

(** The policy can omit the new local's padding while every old padding
    owner is retained.  This does not obtain padding for the new local. *)
Lemma flag_wait_nodes_padding_policy_rep_insert_unowned : forall sg owns nodes p w,
  nodes p = None -> owns p = false ->
  flag_wait_nodes_padding_policy_rep sg owns nodes --||--
    flag_wait_nodes_padding_policy_rep sg owns (kernel_map_set nodes p (Some w)).
Proof.
  intros sg owns nodes p w Hnone Howns.
  rewrite (flag_wait_nodes_padding_policy_rep_remove_node sg owns
    (kernel_map_set nodes p (Some w)) p w (kernel_map_set_same _ nodes p (Some w))).
  rewrite (flag_node_padding_policy_unowned _ _ _ _ Howns).
  assert (Hrestore : forall q,
    kernel_map_set (kernel_map_set nodes p (Some w)) p None q = nodes q).
  { intro q; unfold kernel_map_set; destruct (Z.eq_dec q p) as [->|Hne];
      [symmetry; exact Hnone|reflexivity]. }
  unfold flag_wait_nodes_padding_policy_rep.
  rewrite (store_map_equiv _ _ _ Hrestore); split; entailer!.
Qed.

(** Only the map domain and padding images are observed by this owner.
    Link writes therefore transport it without adding or removing bytes. *)
Lemma flag_wait_nodes_padding_policy_rep_equiv : forall sg owns before after,
  (forall p,
    option_map (fun w => w.(flagWaitImage).(flagNodePadding)) (before p) =
    option_map (fun w => w.(flagWaitImage).(flagNodePadding)) (after p)) ->
  flag_wait_nodes_padding_policy_rep sg owns before --||--
    flag_wait_nodes_padding_policy_rep sg owns after.
Proof.
  intros sg owns before after Hpadding.
  unfold flag_wait_nodes_padding_policy_rep, flag_node_padding_policy_rep,
    flag_node_padding_rep.
  rewrite (FlagNodeFieldStorage.store_map_value_map addr FlagWaiterState
    (list (option Z))
    (fun p padding => if owns p then
      store_optional_bytes (p + flag_node_mode_offset sg.(osKernelConfig) + 1) padding
      else emp)
    (fun w => w.(flagWaitImage).(flagNodePadding)) before).
  rewrite (FlagNodeFieldStorage.store_map_value_map addr FlagWaiterState
    (list (option Z))
    (fun p padding => if owns p then
      store_optional_bytes (p + flag_node_mode_offset sg.(osKernelConfig) + 1) padding
      else emp)
    (fun w => w.(flagWaitImage).(flagNodePadding)) after).
  apply store_map_equiv; exact Hpadding.
Qed.

Lemma flag_wait_nodes_padding_rep_equiv : forall sg before after,
  (forall p,
    option_map (fun w => w.(flagWaitImage).(flagNodePadding)) (before p) =
    option_map (fun w => w.(flagWaitImage).(flagNodePadding)) (after p)) ->
  flag_wait_nodes_padding_rep sg before --||-- flag_wait_nodes_padding_rep sg after.
Proof.
  intros sg before after H.
  change (flag_wait_nodes_padding_policy_rep sg (fun _ => true) before --||--
    flag_wait_nodes_padding_policy_rep sg (fun _ => true) after).
  apply flag_wait_nodes_padding_policy_rep_equiv; exact H.
Qed.

Lemma flag_wait_nodes_padding_policy_rep_set_next : forall sg owns nodes p next,
  flag_wait_nodes_padding_policy_rep sg owns (flag_nodes_set_next nodes p next) --||--
    flag_wait_nodes_padding_policy_rep sg owns nodes.
Proof.
  intros; apply flag_wait_nodes_padding_policy_rep_equiv; intro q.
  rewrite flag_nodes_set_next_lookup.
  destruct (nodes q), (Z.eq_dec q p); reflexivity.
Qed.

Lemma flag_wait_nodes_padding_policy_rep_set_prev : forall sg owns nodes p prev,
  flag_wait_nodes_padding_policy_rep sg owns (flag_nodes_set_prev nodes p prev) --||--
    flag_wait_nodes_padding_policy_rep sg owns nodes.
Proof.
  intros; apply flag_wait_nodes_padding_policy_rep_equiv; intro q.
  rewrite flag_nodes_set_prev_lookup.
  destruct (nodes q), (Z.eq_dec q p); reflexivity.
Qed.

Lemma flag_wait_nodes_padding_policy_rep_unlink_neighbors : forall sg owns nodes w,
  flag_wait_nodes_padding_policy_rep sg owns (flag_unlink_neighbor_nodes nodes w) --||--
    flag_wait_nodes_padding_policy_rep sg owns nodes.
Proof.
  intros; unfold flag_unlink_neighbor_nodes.
  destruct (Z.eqb w.(flagWaitImage).(flagNodePrev) 0),
    (Z.eqb w.(flagWaitImage).(flagNodeNext) 0);
    rewrite ?flag_wait_nodes_padding_policy_rep_set_prev,
      ?flag_wait_nodes_padding_policy_rep_set_next; split; reflexivity.
Qed.
