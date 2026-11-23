Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import SumLib.ZRange.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.queue_core.

Import UCOS2_C_Rules.
Import EventStateDef.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Function-specific stages for the source-order proof of [OS_QInit].

    Shared OS_Q layout, free-list ownership and the public pre/post footprint
    remain owned by [queue_core].  This file only names the transient states
    created by this implementation's clear-and-link loop. *)

Definition q_init_after_clear (sg : StableGlobVars) : Assertion :=
  sg.(g_OSQFreeList) # Ptr |->_ ** queue_table_zero sg.

(** The six cells untouched by every link write. *)
Definition q_init_zero_node_without_ptr
  (sg : StableGlobVars) (qid : QueueID) : Assertion :=
  (qcb_addr sg qid + OSQStart_off) # Ptr |-> 0 **
  (qcb_addr sg qid + OSQEnd_off) # Ptr |-> 0 **
  (qcb_addr sg qid + OSQIn_off) # Ptr |-> 0 **
  (qcb_addr sg qid + OSQOut_off) # Ptr |-> 0 **
  (qcb_addr sg qid + OSQSize_off) # UShort |-> 0 **
  (qcb_addr sg qid + OSQEntries_off) # UShort |-> 0.

(** A free-list node as established by [OS_QInit]: the link is explicit and
    every non-link field retains the zero written by [OS_MemClr].  This is
    intentionally stronger than the shared [free_queue_node], whose six
    non-link fields are abstract because later Queue APIs may reuse it. *)
Definition q_init_zero_linked_node (sg : StableGlobVars)
  (qid : QueueID) (next : addr) : Assertion :=
  (qcb_addr sg qid + OSQPtr_off) # Ptr |-> next **
  q_init_zero_node_without_ptr sg qid.

Fixpoint store_q_init_zero_linked_nodes (sg : StableGlobVars)
  (ids : list QueueID) : Assertion :=
  match ids with
  | [] => emp
  | qid :: rest =>
      q_init_zero_linked_node sg qid (queue_free_head sg rest) **
      store_q_init_zero_linked_nodes sg rest
  end.

(** Exact public list produced by this initializer. *)
Definition store_q_init_zero_linked_list (sg : StableGlobVars)
  (ids : list QueueID) : Assertion :=
  sg.(g_OSQFreeList) # Ptr |-> queue_free_head sg ids **
  store_q_init_zero_linked_nodes sg ids.

Fixpoint q_init_linked_prefix (sg : StableGlobVars)
  (ids : list QueueID) : Assertion :=
  match ids with
  | [] => emp
  | qid :: rest =>
      q_init_zero_linked_node sg qid (qcb_addr sg (qid + 1)) **
      q_init_linked_prefix sg rest
  end.

(** At loop head [ix], exactly the QCBs below [ix] have their successor
    links installed.  The suffix beginning at [ix] still contains the exact
    all-zero bytes established by OS_MemClr. *)
Definition q_init_loop_state (sg : StableGlobVars) (ix : Z) : Assertion :=
  coq_prop (0 <= ix <= sg.(osMaxQs) - 1) &&
  (sg.(g_OSQFreeList) # Ptr |->_ **
   q_init_linked_prefix sg (Zrange 0 ix) **
   store_zero_queue_nodes sg (Zrange ix sg.(osMaxQs))).

(** Focused form used immediately before writing QCB[ix].OSQPtr. *)
Definition q_init_loop_focus (sg : StableGlobVars) (ix : Z) : Assertion :=
  coq_prop (0 <= ix < sg.(osMaxQs)) &&
  (sg.(g_OSQFreeList) # Ptr |->_ **
   q_init_linked_prefix sg (Zrange 0 ix) **
   zero_queue_control_block sg ix **
   store_zero_queue_nodes sg (Zrange (ix + 1) sg.(osMaxQs))).

(** Residual paired with the explicit OSQPtr cell exposed to the C write. *)
Definition q_init_loop_residual (sg : StableGlobVars) (ix : Z) : Assertion :=
  coq_prop (0 <= ix < sg.(osMaxQs)) &&
  (sg.(g_OSQFreeList) # Ptr |->_ **
   q_init_linked_prefix sg (Zrange 0 ix) **
   q_init_zero_node_without_ptr sg ix **
   store_zero_queue_nodes sg (Zrange (ix + 1) sg.(osMaxQs))).

(** State just after QCB[ix].OSQPtr is assigned the address of QCB[ix+1]. *)
Definition q_init_link_committed (sg : StableGlobVars) (ix : Z) : Assertion :=
  coq_prop (0 <= ix < sg.(osMaxQs) - 1) &&
  (sg.(g_OSQFreeList) # Ptr |->_ **
   q_init_linked_prefix sg (Zrange 0 ix) **
   q_init_zero_linked_node sg ix (qcb_addr sg (ix + 1)) **
   store_zero_queue_nodes sg (Zrange (ix + 1) sg.(osMaxQs))).

(** The loop has linked all but the final QCB, which remains exactly zero. *)
Definition q_init_before_last_link (sg : StableGlobVars) : Assertion :=
  sg.(g_OSQFreeList) # Ptr |->_ **
  q_init_linked_prefix sg (Zrange 0 (sg.(osMaxQs) - 1)) **
  zero_queue_control_block sg (sg.(osMaxQs) - 1).

Definition q_init_last_link_residual (sg : StableGlobVars) : Assertion :=
  sg.(g_OSQFreeList) # Ptr |->_ **
  q_init_linked_prefix sg (Zrange 0 (sg.(osMaxQs) - 1)) **
  q_init_zero_node_without_ptr sg (sg.(osMaxQs) - 1).

(** The final null link is installed, but OSQFreeList is not published yet. *)
Definition q_init_before_publish (sg : StableGlobVars) : Assertion :=
  sg.(g_OSQFreeList) # Ptr |->_ **
  q_init_linked_prefix sg (Zrange 0 (sg.(osMaxQs) - 1)) **
  q_init_zero_linked_node sg (sg.(osMaxQs) - 1) 0.

Definition q_init_publish_residual (sg : StableGlobVars) : Assertion :=
  q_init_linked_prefix sg (Zrange 0 (sg.(osMaxQs) - 1)) **
  q_init_zero_linked_node sg (sg.(osMaxQs) - 1) 0.

Definition OS_QInit_spec (sg : StableGlobVars) : Assertion :=
  coq_prop (queue_free_ids_valid sg (queue_all_ids sg)) &&
  store_q_init_zero_linked_list sg (queue_all_ids sg).

Lemma q_init_profile_q_count :
  forall sg,
    queue_first_round_profile sg ->
    sg.(osMaxQs) = 4.
Proof.
  intros sg Hprofile. exact (proj1 Hprofile).
Qed.

Lemma q_init_profile_table_bytes :
  forall sg,
    queue_first_round_profile sg ->
    sg.(osMaxQs) * sizeof_OS_Q = 96.
Proof.
  intros sg Hprofile.
  destruct Hprofile as [Hcount _].
  unfold sizeof_OS_Q.
  lia.
Qed.

Lemma q_init_profile_all_ids :
  forall sg,
    queue_first_round_profile sg ->
    queue_all_ids sg = [0; 1; 2; 3].
Proof.
  intros sg Hprofile.
  destruct Hprofile as [Hcount _].
  unfold queue_all_ids.
  rewrite Hcount.
  reflexivity.
Qed.

Lemma q_init_spec_has_valid_free_ids :
  forall sg,
    OS_QInit_spec sg |--
      coq_prop (queue_free_ids_valid sg (queue_all_ids sg)) &&
      TT.
Proof.
  intros sg.
  unfold OS_QInit_spec.
  entailer!.
Qed.

Lemma q_init_zero_linked_node_implies_free_node : forall sg qid next,
  q_init_zero_linked_node sg qid next |-- free_queue_node sg qid next.
Proof.
  intros sg qid next; unfold q_init_zero_linked_node, q_init_zero_node_without_ptr,
    free_queue_node.
  sep_apply_l_atomic (store_ptr_undef_store_ptr (qcb_addr sg qid + OSQStart_off) 0).
  sep_apply_l_atomic (store_ptr_undef_store_ptr (qcb_addr sg qid + OSQEnd_off) 0).
  sep_apply_l_atomic (store_ptr_undef_store_ptr (qcb_addr sg qid + OSQIn_off) 0).
  sep_apply_l_atomic (store_ptr_undef_store_ptr (qcb_addr sg qid + OSQOut_off) 0).
  sep_apply_l_atomic (store_ushort_undef_store_ushort (qcb_addr sg qid + OSQSize_off) 0).
  sep_apply_l_atomic (store_ushort_undef_store_ushort (qcb_addr sg qid + OSQEntries_off) 0).
  entailer!.
Qed.

Lemma store_q_init_zero_linked_nodes_implies_free_nodes : forall sg ids,
  store_q_init_zero_linked_nodes sg ids |-- store_free_queue_nodes sg ids.
Proof.
  intros sg ids; induction ids as [|qid rest IH]; cbn.
  - reflexivity.
  - sep_apply_l_atomic (q_init_zero_linked_node_implies_free_node sg qid
      (queue_free_head sg rest)).
    sep_apply_l_atomic IH; entailer!.
Qed.

Lemma q_init_spec_implies_queue_init_post : forall sg,
  OS_QInit_spec sg |-- queue_init_post sg.
Proof.
  intros sg; unfold OS_QInit_spec, queue_init_post,
    store_q_init_zero_linked_list, store_free_queue_list.
  Intros.
  sep_apply_l_atomic (store_q_init_zero_linked_nodes_implies_free_nodes sg
    (queue_all_ids sg)).
  entailer!.
Qed.

(** Connect the exact C postcondition to the current Queue-owned resources.
    The Event index describes the initial empty published map; this entailment
    neither creates Event heap cells nor establishes the whole OS invariant. *)
Lemma q_init_spec_establishes_queue_storage : forall sg,
  OS_QInit_spec sg |-- queue_storage_rep sg (event_pool_initial sg).
Proof.
  intros sg.
  sep_apply_l_atomic (q_init_spec_implies_queue_init_post sg).
  unfold queue_init_post.
  Intros.
  sep_apply_l_atomic (queue_initial_storage_from_free_list sg).
  entailer!.
Qed.
