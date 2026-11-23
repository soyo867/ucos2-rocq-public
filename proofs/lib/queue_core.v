Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib Axioms Feq.
Require Import SumLib.ZRange.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.kernel_resources.

Import UCOS2_C_Rules.
Import TaskStateDef.
Import EventStateDef.
Import ListNotations.
Module QueueFieldStorage := FieldStorage Arch32 LittleEndian
  UCOS2_C_Rules UCOS2_C_Rules UCOS2_C_Rules UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope string_scope.

(** Shared QCB and ring representation for the uC/OS-II V2.93.01 APIs.
    [QueueFields] in the canonical Event state owns the logical FIFO;
    [publishedQueueBytes] records its physical slots, including stale values.
    There is no second Queue map or duplicated abstract message list.
    Function-specific control flow belongs under [VC/code_proof/queue/spec]. *)

(* ------------------------------------------------------------------ *)
(* L2: logical ring consistency, including the source-valid size=0 case. *)
(* ------------------------------------------------------------------ *)

Lemma queue_fields_consistency_zero :
  forall sg wl q,
    queue_fields_consistency sg wl q ->
    q.(qSize) = 0 ->
    q.(qInIndex) = 0 /\
    q.(qOutIndex) = 0 /\
    q.(qMessages) = [].
Proof.
  intros sg wl q Hvalid Hzero.
  unfold queue_fields_consistency in Hvalid.
  destruct Hvalid as [_ [_ [_ [Hshape _]]]].
  destruct Hshape as [Hzero_shape | Hpositive].
  - tauto.
  - lia.
Qed.

Lemma queue_fields_consistency_positive :
  forall sg wl q,
    queue_fields_consistency sg wl q ->
    0 < q.(qSize) ->
    0 <= q.(qInIndex) < q.(qSize) /\
    0 <= q.(qOutIndex) < q.(qSize) /\
    0 <= queue_entries q <= q.(qSize) /\
    q.(qInIndex) =
      Z.modulo (q.(qOutIndex) + queue_entries q) q.(qSize).
Proof.
  intros sg wl q Hvalid Hpositive.
  unfold queue_fields_consistency in Hvalid.
  destruct Hvalid as [_ [_ [_ [Hshape _]]]].
  destruct Hshape as [Hzero | Hpositive_shape].
  - lia.
  - tauto.
Qed.

Definition queue_ring_index (q : QueueFields) (k : Z) : Z :=
  if Z.eqb q.(qSize) 0
  then 0
  else Z.modulo (q.(qOutIndex) + k) q.(qSize).

Definition queue_slot_occupied
  (q : QueueFields) (slot_index : Z) (p : addr) : Prop :=
  exists k,
    0 <= k < queue_entries q /\
    queue_ring_index q k = slot_index /\
    p = Znth k q.(qMessages) 0.

(** Native physical storage retains values outside the logical FIFO as well
    as values inside it.  An unoccupied slot may contain a stale initialized
    pointer or uninitialized bytes; it is not forced to None. *)
Definition queue_slots_model
  (q : QueueFields) (slots : list (option addr)) : Prop :=
  Zlength slots = q.(qSize) /\
  forall i p, queue_slot_occupied q i p -> Znth i slots None = Some p.

Definition queue_buffer_rep (q : QueueFields)
  (slots : list (option addr)) : Assertion :=
  coq_prop (queue_slots_model q slots) &&
  PtrArray.mixed_full q.(qStart) q.(qSize) slots.

Definition queue_published_storage_binding
  (events : Glob_EventAbstractState) : Prop :=
  (forall eid e q,
     events.(inUsedEventStates) eid = Some e -> e.(queueFields) = Some q ->
     e.(eventType) = OS_EVENT_TYPE_Q /\ exists slots,
       events.(publishedQueueBytes) q.(qID) = Some slots /\
       queue_slots_model q slots) /\
  (forall qid slots, events.(publishedQueueBytes) qid = Some slots ->
     exists eid e q, events.(inUsedEventStates) eid = Some e /\
       e.(queueFields) = Some q /\ q.(qID) = qid) /\
  (forall eid1 eid2 e1 e2 q1 q2,
     events.(inUsedEventStates) eid1 = Some e1 ->
     events.(inUsedEventStates) eid2 = Some e2 ->
     e1.(queueFields) = Some q1 -> e2.(queueFields) = Some q2 ->
     q1.(qID) = q2.(qID) -> eid1 = eid2).

(** Only the QCB association is projected here.  An ECB allocation with
    no QCB and an absent ECB both contribute no private Queue resource. *)
Definition queue_private_owner (events : Glob_EventAbstractState)
  (eid : EventID) : option QueueID :=
  match events.(eventLifecycle).(eventPrivate) eid with
  | Some allocation => allocation.(eventPrivateQueue)
  | None => None
  end.

Definition queue_slot_private (events : Glob_EventAbstractState)
  (qid : QueueID) : Prop :=
  exists eid, queue_private_owner events eid = Some qid.

Definition queue_slot_published (events : Glob_EventAbstractState)
  (qid : QueueID) : Prop :=
  exists eid e q, events.(inUsedEventStates) eid = Some e /\
    e.(queueFields) = Some q /\ q.(qID) = qid.

Lemma queue_bytes_after_task_replacement : forall state tasks,
  (replace_TskS tasks state).(EventState).(publishedQueueBytes) =
    state.(EventState).(publishedQueueBytes).
Proof. reflexivity. Qed.

Lemma queue_bytes_after_scheduler_replacement : forall state scheduler,
  (replace_SchedS scheduler state).(EventState).(publishedQueueBytes) =
    state.(EventState).(publishedQueueBytes).
Proof. reflexivity. Qed.

Definition queue_buffer_undef (start : addr) (size : Z) : Assertion :=
  PtrArray.undef_full start size.

(* ------------------------------------------------------------------ *)
(* L3: source-shaped pure ring transformations shared by Queue APIs.   *)
(* ------------------------------------------------------------------ *)

Definition queue_with_contents (q : QueueFields)
  (qin qout : Z) (messages : list addr) : QueueFields :=
  {| qID       := q.(qID);
     qStart    := q.(qStart);
     qSize     := q.(qSize);
     qInIndex  := qin;
     qOutIndex := qout;
     qMessages := messages |}.

Definition queue_advance_index (size i : Z) : Z :=
  if Z.eqb (i + 1) size then 0 else i + 1.

Definition queue_retreat_index (size i : Z) : Z :=
  if Z.eqb i 0 then size - 1 else i - 1.

Definition queue_flush_state (q : QueueFields) : QueueFields :=
  queue_with_contents q 0 0 [].

Definition queue_enqueue_back
  (q : QueueFields) (p : addr) : option QueueFields :=
  if Z.ltb (queue_entries q) q.(qSize)
  then Some
    (queue_with_contents q
      (queue_advance_index q.(qSize) q.(qInIndex))
      q.(qOutIndex) (q.(qMessages) ++ [p]))
  else None.

Definition queue_enqueue_front
  (q : QueueFields) (p : addr) : option QueueFields :=
  if Z.ltb (queue_entries q) q.(qSize)
  then Some
    (queue_with_contents q q.(qInIndex)
      (queue_retreat_index q.(qSize) q.(qOutIndex))
      (p :: q.(qMessages)))
  else None.

Definition queue_dequeue_front
  (q : QueueFields) : option (addr * QueueFields) :=
  match q.(qMessages) with
  | [] => None
  | p :: rest =>
      Some
        (p,
         queue_with_contents q q.(qInIndex)
           (queue_advance_index q.(qSize) q.(qOutIndex)) rest)
  end.

Lemma queue_entries_with_contents :
  forall q qin qout messages,
    queue_entries (queue_with_contents q qin qout messages) =
    Zlength messages.
Proof. reflexivity. Qed.

Lemma queue_flush_preserves_consistency_total :
  forall sg wl q,
    queue_fields_consistency sg wl q ->
    queue_fields_consistency sg wl (queue_flush_state q).
Proof.
  intros sg wl q Hvalid.
  unfold queue_fields_consistency in *.
  destruct Hvalid as [Hqid [Hstart [Hsize [Hshape Hwait]]]].
  unfold queue_flush_state, queue_with_contents.
  simpl.
  split; [exact Hqid |].
  split; [exact Hstart |].
  split; [exact Hsize |].
  split.
  - destruct Hshape as [Hzero | Hpositive].
    + left. destruct Hzero as [Hzero _]. repeat split; auto.
    + right. destruct Hpositive as [Hpositive _].
      repeat split; try lia.
      all: unfold queue_entries; rewrite Zlength_nil; lia.
  - intros _. reflexivity.
Qed.

Lemma queue_advance_index_in_range : forall size i,
  0 < size -> 0 <= i < size -> 0 <= queue_advance_index size i < size.
Proof.
  intros; unfold queue_advance_index; destruct (Z.eqb (i + 1) size) eqn:E;
    [apply Z.eqb_eq in E|apply Z.eqb_neq in E]; lia.
Qed.

Lemma queue_advance_index_mod_eq : forall size i,
  0 < size -> 0 <= i < size ->
  queue_advance_index size i = (i + 1) mod size.
Proof.
  intros; unfold queue_advance_index; destruct (Z.eqb (i + 1) size) eqn:E.
  - apply Z.eqb_eq in E; rewrite E, Z.mod_same by lia; reflexivity.
  - apply Z.eqb_neq in E; symmetry; apply Z.mod_small; lia.
Qed.

Lemma queue_retreat_index_in_range : forall size i,
  0 < size -> 0 <= i < size -> 0 <= queue_retreat_index size i < size.
Proof.
  intros; unfold queue_retreat_index; destruct (Z.eqb i 0) eqn:E;
    [apply Z.eqb_eq in E|apply Z.eqb_neq in E]; lia.
Qed.

(** Enqueue is the no-waiter branch.  A direct handoff to a waiting task
    does not modify the FIFO and has a separate cross-module operation. *)
Lemma queue_enqueue_back_preserves_consistency_total : forall sg q message after,
  queue_fields_consistency sg [] q ->
  queue_enqueue_back q message = Some after ->
  queue_fields_consistency sg [] after.
Proof.
  intros sg q message after Hvalid Hstep.
  unfold queue_enqueue_back in Hstep.
  destruct (Z.ltb (queue_entries q) (qSize q)) eqn:Hroom; [|discriminate].
  apply Z.ltb_lt in Hroom; inversion Hstep; subst after; clear Hstep.
  pose proof (Zlength_nonneg q.(qMessages)) as Hlength.
  assert (Hpositive : 0 < q.(qSize)) by (unfold queue_entries in Hroom; lia).
  pose proof (queue_fields_consistency_positive sg [] q Hvalid Hpositive)
    as [Hin [Hout [Hcount Heq]]].
  pose proof (queue_advance_index_in_range _ _ Hpositive Hin) as Hnext.
  destruct Hvalid as [Hqid [Hstart [Hsize _]]].
  unfold queue_fields_consistency, queue_with_contents, queue_entries in *; simpl.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  split; [exact Hqid|]. split; [exact Hstart|]. split; [exact Hsize|]. split.
  - right; repeat split; try lia.
    rewrite queue_advance_index_mod_eq by lia.
    rewrite Heq.
    rewrite Z.add_mod_idemp_l by lia.
    f_equal; lia.
  - contradiction.
Qed.

Lemma queue_enqueue_front_preserves_consistency_total : forall sg q message after,
  queue_fields_consistency sg [] q ->
  queue_enqueue_front q message = Some after ->
  queue_fields_consistency sg [] after.
Proof.
  intros sg q message after Hvalid Hstep.
  unfold queue_enqueue_front in Hstep.
  destruct (Z.ltb (queue_entries q) (qSize q)) eqn:Hroom; [|discriminate].
  apply Z.ltb_lt in Hroom; inversion Hstep; subst after; clear Hstep.
  pose proof (Zlength_nonneg q.(qMessages)) as Hlength.
  assert (Hpositive : 0 < q.(qSize)) by (unfold queue_entries in Hroom; lia).
  pose proof (queue_fields_consistency_positive sg [] q Hvalid Hpositive)
    as [Hin [Hout [Hcount Heq]]].
  pose proof (queue_retreat_index_in_range _ _ Hpositive Hout) as Hnext.
  destruct Hvalid as [Hqid [Hstart [Hsize _]]].
  unfold queue_fields_consistency, queue_with_contents, queue_entries in *; simpl.
  rewrite Zlength_cons.
  split; [exact Hqid|]. split; [exact Hstart|]. split; [exact Hsize|]. split.
  - right; repeat split; try lia.
    rewrite Heq; unfold queue_retreat_index; destruct (Z.eqb (qOutIndex q) 0) eqn:E.
    + apply Z.eqb_eq in E; rewrite E; simpl.
      replace (qSize q - 1 + Z.succ (Zlength (qMessages q)))
        with (Zlength (qMessages q) + 1 * qSize q) by lia.
      rewrite Z.mod_add by lia; reflexivity.
    + f_equal; lia.
  - contradiction.
Qed.

Lemma queue_dequeue_front_queue_id_eq : forall q message after,
  queue_dequeue_front q = Some (message, after) -> after.(qID) = q.(qID).
Proof.
  intros q message after Hstep; unfold queue_dequeue_front in Hstep.
  destruct q.(qMessages); inversion Hstep; reflexivity.
Qed.

Lemma queue_dequeue_front_preserves_consistency_total : forall sg waiters q message after,
  queue_fields_consistency sg waiters q ->
  queue_dequeue_front q = Some (message, after) ->
  queue_fields_consistency sg waiters after.
Proof.
  intros sg waiters q message after Hvalid Hstep.
  unfold queue_dequeue_front in Hstep.
  destruct q.(qMessages) as [|head rest] eqn:Hmessages; [discriminate|].
  inversion Hstep; subst message after; clear Hstep.
  assert (Hpositive : 0 < q.(qSize)).
  { pose proof Hvalid as [_ [_ [_ [Hshape _]]]].
    destruct Hshape as [[Hsize [_ [_ Hempty]]]|[Hsize _]];
      [congruence|exact Hsize]. }
  pose proof (queue_fields_consistency_positive sg waiters q Hvalid Hpositive)
    as [Hin [Hout [Hcount Heq]]].
  pose proof (queue_advance_index_in_range _ _ Hpositive Hout) as Hnext.
  destruct Hvalid as [Hqid [Hstart [Hsize [_ Hwait]]]].
  assert (Hnowait : waiters = []).
  { destruct waiters; [reflexivity|]. exfalso; specialize (Hwait ltac:(discriminate)); congruence. }
  subst waiters.
  unfold queue_fields_consistency, queue_with_contents, queue_entries in *; simpl.
  rewrite Hmessages, Zlength_cons in Hcount, Heq.
  pose proof (Zlength_nonneg rest) as Hlength.
  split; [exact Hqid|]. split; [exact Hstart|]. split; [exact Hsize|]. split.
  - right; repeat split; try lia.
    rewrite queue_advance_index_mod_eq by lia.
    rewrite Z.add_mod_idemp_l by lia.
    rewrite Heq; f_equal; lia.
  - contradiction.
Qed.

Lemma queue_zero_capacity_enqueue_none : forall sg waiters q message,
  queue_fields_consistency sg waiters q -> q.(qSize) = 0 ->
  queue_enqueue_back q message = None /\ queue_enqueue_front q message = None.
Proof.
  intros sg waiters q message Hvalid Hsize.
  pose proof (proj2 (proj2 (queue_fields_consistency_zero _ _ _ Hvalid Hsize))) as Hempty.
  unfold queue_enqueue_back, queue_enqueue_front, queue_entries; rewrite Hempty, Hsize.
  split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* L1: OS_Q layout and free-list representation.                       *)
(* ------------------------------------------------------------------ *)

Definition queue_control_block_layout_prop
  (sg : StableGlobVars) (qid : QueueID)
  (ptr_addr start_addr end_addr in_addr out_addr
   size_addr entries_addr : addr) : Prop :=
  ptr_addr = qcb_addr sg qid + OSQPtr_off /\
  start_addr = qcb_addr sg qid + OSQStart_off /\
  end_addr = qcb_addr sg qid + OSQEnd_off /\
  in_addr = qcb_addr sg qid + OSQIn_off /\
  out_addr = qcb_addr sg qid + OSQOut_off /\
  size_addr = qcb_addr sg qid + OSQSize_off /\
  entries_addr = qcb_addr sg qid + OSQEntries_off.

Definition os_q_table_addr (sg : StableGlobVars) (p : addr) : Prop :=
  p = sg.(g_OSQTbl).

(** QCP intentionally keeps struct-field addresses opaque.  Consequently the
    compiled [OS_Q] ABI is an explicit public representation premise, in the
    exact arrow-field vocabulary emitted for C lvalues.  Queue functions carry
    this table-wide fact and select the current QCB when focusing a loop node. *)
Definition queue_table_layout_prop
  (sg : StableGlobVars) (table_base : addr) : Prop :=
  forall qid,
    0 <= qid < sg.(osMaxQs) ->
    queue_control_block_layout_prop sg qid
      (&(((table_base + qid * sizeof ("os_q"))) # "os_q" ->ₛ "OSQPtr"))
      (&(((table_base + qid * sizeof ("os_q"))) # "os_q" ->ₛ "OSQStart"))
      (&(((table_base + qid * sizeof ("os_q"))) # "os_q" ->ₛ "OSQEnd"))
      (&(((table_base + qid * sizeof ("os_q"))) # "os_q" ->ₛ "OSQIn"))
      (&(((table_base + qid * sizeof ("os_q"))) # "os_q" ->ₛ "OSQOut"))
      (&(((table_base + qid * sizeof ("os_q"))) # "os_q" ->ₛ "OSQSize"))
      (&(((table_base + qid * sizeof ("os_q"))) # "os_q" ->ₛ "OSQEntries")).

Lemma queue_table_layout_select :
  forall sg table_base qid,
    queue_table_layout_prop sg table_base ->
    0 <= qid < sg.(osMaxQs) ->
    queue_control_block_layout_prop sg qid
      (&(((table_base + qid * sizeof ("os_q"))) # "os_q" ->ₛ "OSQPtr"))
      (&(((table_base + qid * sizeof ("os_q"))) # "os_q" ->ₛ "OSQStart"))
      (&(((table_base + qid * sizeof ("os_q"))) # "os_q" ->ₛ "OSQEnd"))
      (&(((table_base + qid * sizeof ("os_q"))) # "os_q" ->ₛ "OSQIn"))
      (&(((table_base + qid * sizeof ("os_q"))) # "os_q" ->ₛ "OSQOut"))
      (&(((table_base + qid * sizeof ("os_q"))) # "os_q" ->ₛ "OSQSize"))
      (&(((table_base + qid * sizeof ("os_q"))) # "os_q" ->ₛ "OSQEntries")).
Proof.
  intros sg table_base qid Htable Hqid.
  exact (Htable qid Hqid).
Qed.

(** The first Queue round is tied to the selected 32-bit C layout.  QCP keeps
    named-struct sizes abstract, so the profile must carry the checked ABI
    fact that the seven-field [OS_Q] control block occupies 24 bytes. *)
Definition queue_first_round_profile (sg : StableGlobVars) : Prop :=
  sg.(osMaxQs) = 4 /\
  sizeof_alias_type "os_q" = sizeof_OS_Q.

Definition queue_free_head (sg : StableGlobVars)
  (ids : list QueueID) : addr :=
  match ids with
  | [] => 0
  | qid :: _ => qcb_addr sg qid
  end.

Definition free_queue_node (sg : StableGlobVars)
  (qid : QueueID) (next : addr) : Assertion :=
  (qcb_addr sg qid + OSQPtr_off) # Ptr |-> next **
  (qcb_addr sg qid + OSQStart_off) # Ptr |->_ **
  (qcb_addr sg qid + OSQEnd_off) # Ptr |->_ **
  (qcb_addr sg qid + OSQIn_off) # Ptr |->_ **
  (qcb_addr sg qid + OSQOut_off) # Ptr |->_ **
  (qcb_addr sg qid + OSQSize_off) # UShort |->_ **
  (qcb_addr sg qid + OSQEntries_off) # UShort |->_ .

Fixpoint store_free_queue_nodes (sg : StableGlobVars)
  (ids : list QueueID) : Assertion :=
  match ids with
  | [] => emp
  | qid :: rest =>
      free_queue_node sg qid (queue_free_head sg rest) **
      store_free_queue_nodes sg rest
  end.

Definition store_free_queue_list (sg : StableGlobVars)
  (ids : list QueueID) : Assertion :=
  sg.(g_OSQFreeList) # Ptr |-> queue_free_head sg ids **
  store_free_queue_nodes sg ids.

Definition undef_queue_control_block (sg : StableGlobVars)
  (qid : QueueID) : Assertion :=
  (qcb_addr sg qid + OSQPtr_off) # Ptr |->_ **
  (qcb_addr sg qid + OSQStart_off) # Ptr |->_ **
  (qcb_addr sg qid + OSQEnd_off) # Ptr |->_ **
  (qcb_addr sg qid + OSQIn_off) # Ptr |->_ **
  (qcb_addr sg qid + OSQOut_off) # Ptr |->_ **
  (qcb_addr sg qid + OSQSize_off) # UShort |->_ **
  (qcb_addr sg qid + OSQEntries_off) # UShort |->_ .

(** Exact state produced by OS_MemClr.  It is kept separate from the weaker
    free-node predicate because OS_QInit's link-building loop reads and writes
    the pointer cells after the byte clear. *)
Definition zero_queue_control_block (sg : StableGlobVars)
  (qid : QueueID) : Assertion :=
  (qcb_addr sg qid + OSQPtr_off) # Ptr |-> 0 **
  (qcb_addr sg qid + OSQStart_off) # Ptr |-> 0 **
  (qcb_addr sg qid + OSQEnd_off) # Ptr |-> 0 **
  (qcb_addr sg qid + OSQIn_off) # Ptr |-> 0 **
  (qcb_addr sg qid + OSQOut_off) # Ptr |-> 0 **
  (qcb_addr sg qid + OSQSize_off) # UShort |-> 0 **
  (qcb_addr sg qid + OSQEntries_off) # UShort |-> 0.

Fixpoint store_undef_queue_nodes (sg : StableGlobVars)
  (ids : list QueueID) : Assertion :=
  match ids with
  | [] => emp
  | qid :: rest =>
      undef_queue_control_block sg qid **
      store_undef_queue_nodes sg rest
  end.

Fixpoint store_zero_queue_nodes (sg : StableGlobVars)
  (ids : list QueueID) : Assertion :=
  match ids with
  | [] => emp
  | qid :: rest =>
      zero_queue_control_block sg qid **
      store_zero_queue_nodes sg rest
  end.

Definition queue_all_ids (sg : StableGlobVars) : list QueueID :=
  Zrange 0 sg.(osMaxQs).

Definition queue_free_ids_valid (sg : StableGlobVars)
  (ids : list QueueID) : Prop :=
  NoDup ids /\ Forall (valid_queue_id sg) ids.

Definition queue_table_undef (sg : StableGlobVars) : Assertion :=
  store_undef_queue_nodes sg (queue_all_ids sg).

Definition queue_table_zero (sg : StableGlobVars) : Assertion :=
  store_zero_queue_nodes sg (queue_all_ids sg).

(** Public footprint of OS_QInit before and after the source loop. *)
Definition queue_init_pre (sg : StableGlobVars) : Assertion :=
  sg.(g_OSQFreeList) # Ptr |->_ ** queue_table_undef sg.

Definition queue_init_post (sg : StableGlobVars) : Assertion :=
  coq_prop (queue_free_ids_valid sg (queue_all_ids sg)) &&
  store_free_queue_list sg (queue_all_ids sg).

Lemma queue_all_ids_nodup :
  forall sg, NoDup (queue_all_ids sg).
Proof.
  intros sg. unfold queue_all_ids. apply NoDup_Zrange.
Qed.

Lemma queue_all_ids_in_range :
  forall sg, Forall (valid_queue_id sg) (queue_all_ids sg).
Proof.
  intros sg. apply Forall_forall. intros qid Hin.
  unfold queue_all_ids in Hin.
  exact ((proj2 (In_Zrange 0 (osMaxQs sg) qid)) Hin).
Qed.

Lemma queue_all_ids_valid :
  forall sg, queue_free_ids_valid sg (queue_all_ids sg).
Proof.
  intros sg. split.
  - apply queue_all_ids_nodup.
  - apply queue_all_ids_in_range.
Qed.

Lemma store_free_queue_nodes_cons :
  forall sg qid rest,
    store_free_queue_nodes sg (qid :: rest) --||--
      free_queue_node sg qid (queue_free_head sg rest) **
      store_free_queue_nodes sg rest.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma store_free_queue_list_cons :
  forall sg qid rest,
    store_free_queue_list sg (qid :: rest) --||--
      sg.(g_OSQFreeList) # Ptr |-> qcb_addr sg qid **
      (free_queue_node sg qid (queue_free_head sg rest) **
       store_free_queue_nodes sg rest).
Proof.
  intros. unfold store_free_queue_list. simpl.
  reflexivity.
Qed.

(** Published QCBs and their physical rings are shared.  Detached QCBs
    are accounted for by their existing private ECB invocation, but their
    cells are held outside this predicate.  Free-list order is the actual
    root/links observation, not a duplicated logical FIFO. *)
Definition published_queue_node_rep (sg : StableGlobVars)
  (events : Glob_EventAbstractState) (_ : EventID) (e : OSEventAbstractState)
  : Assertion :=
  match e.(queueFields) with
  | None => emp
  | Some q => EX slots,
      coq_prop (events.(publishedQueueBytes) q.(qID) = Some slots) &&
      (used_queue_control_block sg q ** queue_buffer_rep q slots)
  end.

Definition queue_pool_partition (sg : StableGlobVars)
  (events : Glob_EventAbstractState) (free : list QueueID) : Prop :=
  queue_free_ids_valid sg free /\
  (forall qid,
    (queue_slot_published events qid \/ queue_slot_private events qid) <->
    valid_queue_id sg qid /\ ~ In qid free) /\
  (forall qid, queue_slot_published events qid ->
    ~ queue_slot_private events qid) /\
  (forall first second qid,
    queue_private_owner events first = Some qid ->
    queue_private_owner events second = Some qid -> first = second).

Definition queue_storage_rep (sg : StableGlobVars)
  (events : Glob_EventAbstractState) : Assertion :=
  coq_prop (queue_published_storage_binding events) &&
  (store_map (published_queue_node_rep sg events) events.(inUsedEventStates) **
   EX free, coq_prop (queue_pool_partition sg events free) &&
     store_free_queue_list sg free).

Lemma queue_storage_task_sched_frame : forall sg s tasks scheduler,
  queue_storage_rep sg
    (replace_SchedS scheduler (replace_TskS tasks s)).(EventState) =
  queue_storage_rep sg s.(EventState).
Proof. reflexivity. Qed.

(** OSQCreate's successful QCB pop changes the free root in C and records
    this association in ghost state.  It does not yet write any QCB/ECB
    field or publish the buffer.  The spatial rule below consumes the
    actual updated root, so this transformer cannot allocate bytes alone. *)
Definition queue_allocation_with_qcb (allocation : EventPrivateAllocation)
  (qid : QueueID) : EventPrivateAllocation :=
  {| eventPrivateInvocation := allocation.(eventPrivateInvocation);
     eventPrivateGeneration := allocation.(eventPrivateGeneration);
     eventPrivateQueue := Some qid;
     eventPrivateMutexPCP := allocation.(eventPrivateMutexPCP);
     eventPrivateStorage := allocation.(eventPrivateStorage) |}.

Definition queue_reserve_control_block (events : Glob_EventAbstractState)
  (eid : EventID) (allocation : EventPrivateAllocation) (qid : QueueID)
  : Glob_EventAbstractState :=
  let life := events.(eventLifecycle) in
  event_set_lifecycle events
    {| eventFreeStorage := life.(eventFreeStorage);
       eventPrivate := kernel_map_set life.(eventPrivate) eid
         (Some (queue_allocation_with_qcb allocation qid));
       eventNextGeneration := life.(eventNextGeneration);
       eventNextInvocation := life.(eventNextInvocation) |}.

Lemma queue_private_owner_after_reserve : forall events eid allocation qid other,
  queue_private_owner (queue_reserve_control_block events eid allocation qid) other =
    if Z.eq_dec other eid then Some qid else queue_private_owner events other.
Proof.
  intros; unfold queue_private_owner, queue_reserve_control_block,
    event_set_lifecycle, kernel_map_set; simpl.
  destruct (Z.eq_dec other eid); reflexivity.
Qed.

Lemma queue_reserve_frames_other_invocation : forall events eid allocation qid observer,
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateInvocation) <> observer ->
  event_creation_frame observer events (queue_reserve_control_block events eid allocation qid).
Proof.
  intros events eid allocation qid observer Hget Hforeign.
  eapply event_creation_view_update_foreign with (eid := eid).
  - intros; simpl; apply kernel_map_set_other; assumption.
  - intros other Hother; congruence.
  - intros other Hother; simpl in Hother; rewrite kernel_map_set_same in Hother.
    injection Hother as Hother; subst other; exact Hforeign.
Qed.

Lemma event_creation_frame_queue_owner : forall invocation before after eid allocation,
  event_creation_frame invocation before after ->
  before.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateInvocation) = invocation ->
  queue_private_owner after eid = queue_private_owner before eid.
Proof.
  intros invocation before after eid allocation Hframe Hget Hinv.
  unfold queue_private_owner.
  rewrite (event_creation_frame_lookup invocation before after eid allocation Hframe Hget Hinv), Hget.
  reflexivity.
Qed.

Lemma queue_slot_private_after_reserve : forall events eid allocation qid other,
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None ->
  (queue_slot_private (queue_reserve_control_block events eid allocation qid) other <->
    other = qid \/ queue_slot_private events other).
Proof.
  intros events eid allocation qid other Hget Hnone; split.
  - intros [owner Howner]; rewrite queue_private_owner_after_reserve in Howner.
    destruct (Z.eq_dec owner eid); [left; congruence|right; exists owner; exact Howner].
  - intros [->|[owner Howner]].
    + exists eid; rewrite queue_private_owner_after_reserve.
      destruct (Z.eq_dec eid eid); congruence.
    + exists owner; rewrite queue_private_owner_after_reserve.
      destruct (Z.eq_dec owner eid) as [->|Hne]; [|exact Howner].
      unfold queue_private_owner in Howner; rewrite Hget, Hnone in Howner; discriminate.
Qed.

Lemma queue_pool_free_unallocated : forall sg events free qid,
  queue_pool_partition sg events free -> In qid free ->
  ~ queue_slot_published events qid /\ ~ queue_slot_private events qid.
Proof.
  intros sg events free qid [_ [Hpart _]] Hin; split; intro Hslot;
    assert (Hallocated : queue_slot_published events qid \/
      queue_slot_private events qid) by auto;
    apply Hpart in Hallocated; tauto.
Qed.

Lemma queue_reserve_control_block_preserves_partition :
  forall sg events eid allocation qid rest,
  queue_pool_partition sg events (qid :: rest) ->
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None ->
  queue_pool_partition sg
    (queue_reserve_control_block events eid allocation qid) rest.
Proof.
  intros sg events eid allocation qid rest Hvalid Hget Hnone.
  destruct (queue_pool_free_unallocated sg events (qid :: rest) qid
    Hvalid (or_introl eq_refl)) as [Hnotpub Hnotpriv].
  destruct Hvalid as [[Hnd Hr] [Hpart [Hdisjoint Hunique]]].
  inversion Hnd as [|? ? Hnot Htail]; subst.
  inversion Hr as [|? ? Hrange Hrest]; subst.
  split; [split; assumption|]. split.
  - intro other.
    change ((queue_slot_published events other \/
      queue_slot_private (queue_reserve_control_block events eid allocation qid) other)
      <-> valid_queue_id sg other /\ ~ In other rest).
    rewrite queue_slot_private_after_reserve by assumption.
    destruct (Z.eq_dec other qid) as [->|Hne].
    + split; [intros _; split; assumption|intros _; auto].
    + specialize (Hpart other); simpl in Hpart; intuition congruence.
  - split.
    + intros other Hpub Hpriv.
      change (queue_slot_published events other) in Hpub.
      apply (proj1 (queue_slot_private_after_reserve events eid allocation qid other
        Hget Hnone)) in Hpriv.
      destruct Hpriv as [->|Hpriv]; [contradiction|eapply Hdisjoint; eauto].
    + intros first second other Hfirst Hsecond.
      rewrite queue_private_owner_after_reserve in Hfirst, Hsecond.
      destruct (Z.eq_dec first eid) as [->|Hfirstne];
        destruct (Z.eq_dec second eid) as [->|Hsecondne]; try reflexivity.
      * exfalso; apply Hnotpriv; exists second; congruence.
      * exfalso; apply Hnotpriv; exists first; congruence.
      * eapply Hunique; eauto.
Qed.

Lemma queue_reserve_control_block_preserves_event_partition :
  forall sg events eid allocation qid,
  event_pool_partition sg events ->
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_pool_partition sg
    (queue_reserve_control_block events eid allocation qid).
Proof.
  intros sg events eid allocation qid [Hpart Hdisjoint] Hget.
  assert (Hentries : event_allocated_slots
    (queue_reserve_control_block events eid allocation qid) =
    kernel_map_set (event_allocated_slots events) eid
      (Some (inr (queue_allocation_with_qcb allocation qid)))).
  { apply functional_extensionality; intro other; unfold event_allocated_slots,
      queue_reserve_control_block, event_set_lifecycle; simpl.
    unfold kernel_map_set; destruct (Z.eq_dec other eid); reflexivity. }
  split.
  - rewrite Hentries; eapply kernel_pool_replace_preserves_partition;
      [exact Hpart|apply event_allocated_slots_private; exact Hget].
  - intros other a Ha; simpl in Ha |- *; unfold kernel_map_set in Ha.
    destruct (Z.eq_dec other eid) as [->|Hne]; eapply Hdisjoint; eauto.
Qed.

Lemma queue_reserve_control_block_preserves_event_free_storage :
  forall sg events eid allocation qid,
  event_free_storage_valid sg events ->
  event_free_storage_valid sg
    (queue_reserve_control_block events eid allocation qid).
Proof. intros; exact H. Qed.

Lemma queue_reserve_control_block_preserves_event_identity :
  forall events eid allocation qid,
  event_identity_valid events ->
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_identity_valid (queue_reserve_control_block events eid allocation qid).
Proof.
  intros events eid allocation qid Hvalid Hget.
  eapply event_identity_valid_from_submap; [exact Hvalid|reflexivity|reflexivity| |].
  - intros other generation Hgen; unfold event_slot_generation, event_allocated_slots in *;
      simpl in Hgen; unfold kernel_map_set in Hgen.
    destruct (Z.eq_dec other eid) as [->|Hne]; [rewrite Hget; exact Hgen|exact Hgen].
  - intros other invocation Hinv; unfold event_private_invocation in *;
      simpl in Hinv; unfold kernel_map_set in Hinv.
    destruct (Z.eq_dec other eid) as [->|Hne]; [rewrite Hget; exact Hinv|exact Hinv].
Qed.

Lemma queue_detach_head_reconstructs_storage :
  forall sg events eid allocation qid rest,
  queue_published_storage_binding events ->
  queue_pool_partition sg events (qid :: rest) ->
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None ->
  store_map (published_queue_node_rep sg events) events.(inUsedEventStates) **
    (sg.(g_OSQFreeList) # Ptr |-> queue_free_head sg rest **
      (free_queue_node sg qid (queue_free_head sg rest) ** store_free_queue_nodes sg rest)) |--
  queue_storage_rep sg (queue_reserve_control_block events eid allocation qid) **
    free_queue_node sg qid (queue_free_head sg rest).
Proof.
  intros sg events eid allocation qid rest Hbinding Hpart Hget Hnone.
  pose proof (queue_reserve_control_block_preserves_partition sg events eid allocation qid rest
    Hpart Hget Hnone) as Hafter.
  unfold queue_storage_rep; entailer!.
  Exists rest; entailer!.
  unfold store_free_queue_list; entailer!.
Qed.

(** The selected 32-bit OS_Q layout is represented through QCP store_map.
    The byte inventory below does not assume equality with symbolic C field
    addresses; queue_table_layout_prop remains the explicit ABI bridge. *)
Inductive QCBField : Type :=
| QCBPtr | QCBStart | QCBEnd | QCBIn | QCBOut | QCBSize | QCBEntries.

Definition QCBField_eq_dec : forall x y : QCBField, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition QCBStorage := QCBField -> option Z.

Definition qcb_fields : list QCBField :=
  [QCBPtr; QCBStart; QCBEnd; QCBIn; QCBOut; QCBSize; QCBEntries].

Definition qcb_field_offset (f : QCBField) : Z :=
  match f with
  | QCBPtr => OSQPtr_off | QCBStart => OSQStart_off | QCBEnd => OSQEnd_off
  | QCBIn => OSQIn_off | QCBOut => OSQOut_off
  | QCBSize => OSQSize_off | QCBEntries => OSQEntries_off
  end.

Definition qcb_field_width (f : QCBField) : nat :=
  match f with QCBSize | QCBEntries => 2 | _ => 4 end.

Lemma qcb_fields_nodup : NoDup qcb_fields.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

Lemma qcb_field_in_inventory : forall f, In f qcb_fields.
Proof. intros []; simpl; tauto. Qed.

Lemma qcb_layout_covers_bytes :
  flat_map (fun f => map (fun n => qcb_field_offset f + Z.of_nat n)
    (seq 0 (qcb_field_width f))) qcb_fields = map Z.of_nat (seq 0 24).
Proof. reflexivity. Qed.

Definition qcb_cell (base : addr) (field : QCBField)
  (value : option Z) : Assertion :=
  let p := base + qcb_field_offset field in
  match field with
  | QCBSize | QCBEntries =>
      match value with Some v => p # UShort |-> v | None => p # UShort |->_ end
  | _ => match value with Some v => p # Ptr |-> v | None => p # Ptr |->_ end
  end.

Definition qcb_write :=
  @field_update QCBField (option Z) QCBField_eq_dec.

Definition qcb_storage_rep (sg : StableGlobVars) (qid : QueueID)
  (image : QCBStorage) : Assertion :=
  QueueFieldStorage.store_fields QCBField_eq_dec (qcb_cell (qcb_addr sg qid))
    qcb_fields image.

(** The QCB images are supplied by the actual suspended caller.  Only
    the Event-owned QCB association selects their storage; there is no
    second global QCB-image map.  The caller's buffer stays in its ordinary
    separating frame.  Equality below is resource reindexing, not a proof
    that a C callback refrains from writing these bytes. *)
Definition queue_creation_storage (sg : StableGlobVars) (events : Glob_EventAbstractState)
  (invocation : nat) (images : QueueID -> QCBStorage) : Assertion :=
  store_map (fun (_ : EventID) (allocation : EventPrivateAllocation) =>
    match allocation.(eventPrivateQueue) with
    | None => emp
    | Some qid => qcb_storage_rep sg qid (images qid)
    end) (event_creation_view events invocation).

Lemma event_creation_frame_queue_storage_eq : forall sg invocation before after images,
  event_creation_frame invocation before after ->
  queue_creation_storage sg after invocation images = queue_creation_storage sg before invocation images.
Proof. intros; unfold queue_creation_storage; rewrite H; reflexivity. Qed.

Definition qcb_storage_without_field (sg : StableGlobVars) (qid : QueueID)
  (image : QCBStorage) (field : QCBField) : Assertion :=
  QueueFieldStorage.store_fields QCBField_eq_dec (qcb_cell (qcb_addr sg qid))
    (remove QCBField_eq_dec field qcb_fields) image.

Lemma qcb_storage_split_field : forall sg qid image field,
  qcb_storage_rep sg qid image |--
    qcb_cell (qcb_addr sg qid) field (image field) **
    qcb_storage_without_field sg qid image field.
Proof.
  intros; apply QueueFieldStorage.store_fields_split_field;
    [apply qcb_fields_nodup|apply qcb_field_in_inventory].
Qed.

Lemma qcb_storage_merge_field : forall sg qid image field,
  qcb_cell (qcb_addr sg qid) field (image field) **
    qcb_storage_without_field sg qid image field |-- qcb_storage_rep sg qid image.
Proof.
  intros; apply QueueFieldStorage.store_fields_merge_field;
    [apply qcb_fields_nodup|apply qcb_field_in_inventory].
Qed.

Lemma qcb_storage_merge_updated_field : forall sg qid image field value,
  qcb_cell (qcb_addr sg qid) field value **
    qcb_storage_without_field sg qid image field |--
    qcb_storage_rep sg qid (qcb_write image field value).
Proof.
  intros; apply QueueFieldStorage.store_fields_merge_updated_field;
    [apply qcb_fields_nodup|apply qcb_field_in_inventory].
Qed.

Definition qcb_free_image (next : addr) : QCBStorage :=
  fun field => match field with QCBPtr => Some next | _ => None end.

Lemma qcb_free_image_rep : forall sg qid next,
  qcb_storage_rep sg qid (qcb_free_image next) --||-- free_queue_node sg qid next.
Proof.
  intros; unfold qcb_storage_rep, qcb_fields.
  repeat rewrite QueueFieldStorage.store_fields_cons by
    (repeat constructor; simpl; intuition discriminate).
  rewrite QueueFieldStorage.store_fields_nil.
  unfold qcb_free_image, qcb_cell, qcb_field_offset, free_queue_node.
  split; entailer!.
Qed.

(** Six writes, in source order.  QCreate never clears the old OSQPtr;
    size=0 and NULL message values are not removed from the model. *)
Definition qcb_initialize (image : QCBStorage) (start : addr) (size : Z)
  : QCBStorage :=
  qcb_write
    (qcb_write
      (qcb_write
        (qcb_write
          (qcb_write
            (qcb_write image QCBStart (Some start))
            QCBEnd (Some (start + size * Ucos2Verify.lib.event.sizeof_ptr)))
          QCBIn (Some start))
        QCBOut (Some start))
      QCBSize (Some size))
    QCBEntries (Some 0).

Definition queue_initial_fields (qid : QueueID) (start : addr) (size : Z) : QueueFields :=
  {| qID := qid; qStart := start; qSize := size;
     qInIndex := 0; qOutIndex := 0; qMessages := [] |}.

Lemma qcb_initialize_preserves_free_link : forall image start size,
  qcb_initialize image start size QCBPtr = image QCBPtr.
Proof. reflexivity. Qed.

Lemma queue_initial_fields_consistency : forall sg qid start size,
  valid_queue_id sg qid -> 0 < start -> 0 <= size <= 0xFFFF ->
  queue_fields_consistency sg [] (queue_initial_fields qid start size).
Proof.
  intros sg qid start size Hqid Hstart Hsize.
  unfold queue_fields_consistency, queue_initial_fields, queue_entries; simpl.
  rewrite !Zlength_nil.
  split; [exact Hqid|]; split; [exact Hstart|]; split; [exact Hsize|]; split.
  - destruct (Z.eq_dec size 0) as [->|Hnz]; [left; auto|right].
    repeat split; try lia; rewrite Z.mod_0_l by lia; reflexivity.
  - intros H; contradiction.
Qed.

Lemma queue_initial_slots_model : forall qid start size slots,
  Zlength slots = size ->
  queue_slots_model (queue_initial_fields qid start size) slots.
Proof.
  intros qid start size slots Hlen; split; [exact Hlen|].
  intros i p [k [Hk _]]; unfold queue_entries, queue_initial_fields in Hk;
    simpl in Hk; rewrite Zlength_nil in Hk; lia.
Qed.

Lemma qcb_initialize_storage_implies_used : forall sg qid image start size,
  qcb_storage_rep sg qid (qcb_initialize image start size) |--
    used_queue_control_block sg (queue_initial_fields qid start size).
Proof.
  intros; unfold qcb_storage_rep, qcb_fields.
  repeat rewrite QueueFieldStorage.store_fields_cons by
    (repeat constructor; simpl; intuition discriminate).
  rewrite QueueFieldStorage.store_fields_nil.
  unfold qcb_cell, qcb_field_offset, qcb_initialize, qcb_write,
    field_update, QCBField_eq_dec; simpl.
  unfold used_queue_control_block, queue_initial_fields, queue_end_addr,
    queue_in_addr, queue_out_addr, queue_entries; simpl.
  rewrite !Zlength_nil, ?Z.add_0_r.
  destruct (image QCBPtr) as [next|]; [sep_apply store_ptr_undef_store_ptr|]; entailer!.
Qed.

Lemma qcb_initialize_buffer_reconstructs_published : forall sg qid image start size slots,
  Zlength slots = size ->
  qcb_storage_rep sg qid (qcb_initialize image start size) **
    PtrArray.mixed_full start size slots |--
  used_queue_control_block sg (queue_initial_fields qid start size) **
    queue_buffer_rep (queue_initial_fields qid start size) slots.
Proof.
  intros; sep_apply qcb_initialize_storage_implies_used.
  unfold queue_buffer_rep.
  pose proof (queue_initial_slots_model qid start size slots H).
  entailer!.
Qed.

(** Publication transfers already initialized private cells and the caller's
    buffer.  This is not an extra C store or a runtime validity guard. *)
Definition queue_publish (events : Glob_EventAbstractState) (eid : EventID)
  (node : OSEventAbstractState) (qid : QueueID) (slots : list (option addr))
  : Glob_EventAbstractState :=
  let published := event_publish events eid node in
  {| inUsedEventStates := published.(inUsedEventStates);
     unUsedEventStates := published.(unUsedEventStates);
     publishedQueueBytes := kernel_map_set events.(publishedQueueBytes) qid (Some slots);
     eventLifecycle := published.(eventLifecycle) |}.

Lemma queue_private_owner_after_publish : forall events eid node qid slots other,
  queue_private_owner (queue_publish events eid node qid slots) other =
    if Z.eq_dec other eid then None else queue_private_owner events other.
Proof.
  intros; unfold queue_private_owner, queue_publish, event_publish;
    simpl; unfold kernel_map_set; destruct (Z.eq_dec other eid); reflexivity.
Qed.

Lemma queue_publish_frames_other_invocation : forall events eid allocation node qid slots observer,
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateInvocation) <> observer ->
  event_creation_frame observer events (queue_publish events eid node qid slots).
Proof.
  intros; change (event_creation_frame observer events (event_publish events eid node)).
  eapply event_publish_frames_other_invocation; eassumption.
Qed.

Lemma queue_slot_published_after_publish : forall events eid node q slots other,
  events.(inUsedEventStates) eid = None -> node.(queueFields) = Some q ->
  (queue_slot_published (queue_publish events eid node q.(qID) slots) other <->
    other = q.(qID) \/ queue_slot_published events other).
Proof.
  intros events eid node q slots other Hnone Hq; split.
  - intros [owner [e [q' [Hget [Hfields Hqid]]]]].
    simpl in Hget; unfold kernel_map_set in Hget.
    destruct (Z.eq_dec owner eid) as [->|Hne].
    + inversion Hget; subst e; rewrite Hq in Hfields; inversion Hfields; subst q'; auto.
    + right; exists owner, e, q'; auto.
  - intros [->|[owner [e [q' [Hget [Hfields Hqid]]]]]].
    + exists eid, node, q; simpl; rewrite kernel_map_set_same; auto.
    + exists owner, e, q'; simpl.
      rewrite kernel_map_set_other by (intro E; subst; congruence); auto.
Qed.

Lemma queue_slot_private_after_publish : forall sg events free eid node qid slots,
  queue_pool_partition sg events free ->
  queue_private_owner events eid = Some qid ->
  forall other,
  (queue_slot_private (queue_publish events eid node qid slots) other <->
    queue_slot_private events other /\ other <> qid).
Proof.
  intros sg events free eid node qid slots [_ [_ [_ Hunique]]] Howner other; split.
  - intros [owner Hget]; rewrite queue_private_owner_after_publish in Hget.
    destruct (Z.eq_dec owner eid) as [->|Hne]; [discriminate|].
    split; [exists owner; exact Hget|].
    intro E; subst other; apply Hne; eapply Hunique; eauto.
  - intros [[owner Hget] Hne]; exists owner.
    rewrite queue_private_owner_after_publish.
    destruct (Z.eq_dec owner eid) as [->|Hownerne]; [congruence|exact Hget].
Qed.

Lemma queue_publish_preserves_partition : forall sg events free eid node q slots,
  queue_pool_partition sg events free ->
  queue_private_owner events eid = Some q.(qID) ->
  events.(inUsedEventStates) eid = None -> node.(queueFields) = Some q ->
  queue_pool_partition sg (queue_publish events eid node q.(qID) slots) free.
Proof.
  intros sg events free eid node q slots Hvalid Howner Hnone Hq.
  pose proof (queue_slot_private_after_publish sg events free eid node q.(qID) slots
    Hvalid Howner) as Hprivate.
  destruct Hvalid as [Hfree [Hpart [Hdisjoint Hunique]]].
  assert (Hprivate_old : queue_slot_private events q.(qID)) by (exists eid; exact Howner).
  split; [exact Hfree|]; split.
  - intro other; rewrite queue_slot_published_after_publish by assumption.
    rewrite Hprivate; rewrite <- Hpart.
    destruct (Z.eq_dec other q.(qID)) as [->|Hne]; tauto.
  - split.
    + intros other Hpub Hpriv.
      apply (proj1 (queue_slot_published_after_publish events eid node q slots other Hnone Hq)) in Hpub.
      apply Hprivate in Hpriv; destruct Hpub as [->|Hpub].
      * tauto.
      * exact (Hdisjoint other Hpub (proj1 Hpriv)).
    + intros first second other Hfirst Hsecond.
      rewrite queue_private_owner_after_publish in Hfirst, Hsecond.
      destruct (Z.eq_dec first eid); [discriminate|].
      destruct (Z.eq_dec second eid); [discriminate|].
      eapply Hunique; eauto.
Qed.

Lemma queue_publish_preserves_storage_binding :
  forall events eid node q slots,
  queue_published_storage_binding events ->
  ~ queue_slot_published events q.(qID) ->
  events.(inUsedEventStates) eid = None ->
  node.(queueFields) = Some q -> node.(eventType) = OS_EVENT_TYPE_Q ->
  queue_slots_model q slots ->
  queue_published_storage_binding (queue_publish events eid node q.(qID) slots).
Proof.
  intros events eid node q slots [Hnodes [Hbytes Hunique]] Hfresh Hnone Hq Htype Hslots.
  assert (Holdqid : forall owner e q',
    events.(inUsedEventStates) owner = Some e -> e.(queueFields) = Some q' -> q'.(qID) <> q.(qID)).
  { intros owner e q' Hget Hfields E; apply Hfresh; exists owner, e, q'; auto. }
  split.
  - intros owner e q' Hget Hfields; simpl in Hget |- *; unfold kernel_map_set in Hget.
    destruct (Z.eq_dec owner eid) as [->|Hne].
    + inversion Hget; subst e; rewrite Hq in Hfields; inversion Hfields; subst q'.
      split; [exact Htype|exists slots; rewrite kernel_map_set_same; auto].
    + destruct (Hnodes owner e q' Hget Hfields) as [Htype' [bytes [Hgetbytes Hmodel]]].
      split; [exact Htype'|exists bytes].
      rewrite kernel_map_set_other by (eapply Holdqid; eauto); auto.
  - split.
    + intros other bytes Hgetbytes; simpl in Hgetbytes; unfold kernel_map_set in Hgetbytes.
      destruct (Z.eq_dec other q.(qID)) as [->|Hne].
      * exists eid, node, q; simpl; rewrite kernel_map_set_same; auto.
      * destruct (Hbytes other bytes Hgetbytes) as [owner [e [q' [Hget [Hfields Hqid]]]]].
        exists owner, e, q'; simpl.
        rewrite kernel_map_set_other by (intro E; subst; congruence); auto.
    + intros first second e1 e2 q1 q2 Hfirst Hsecond Hfields1 Hfields2 Hqid.
      simpl in Hfirst, Hsecond; unfold kernel_map_set in Hfirst, Hsecond.
      destruct (Z.eq_dec first eid) as [->|Hne1]; destruct (Z.eq_dec second eid) as [->|Hne2].
      * reflexivity.
      * inversion Hfirst; subst e1; rewrite Hq in Hfields1; inversion Hfields1; subst q1.
        exfalso; apply (Holdqid second e2 q2 Hsecond Hfields2); congruence.
      * inversion Hsecond; subst e2; rewrite Hq in Hfields2; inversion Hfields2; subst q2.
        exfalso; apply (Holdqid first e1 q1 Hfirst Hfields1); congruence.
      * eapply Hunique; eauto.
Qed.

Lemma queue_published_nodes_fresh_buffer_eq : forall sg events eid node qid slots,
  ~ queue_slot_published events qid ->
  store_map (published_queue_node_rep sg (queue_publish events eid node qid slots))
    events.(inUsedEventStates) =
  store_map (published_queue_node_rep sg events) events.(inUsedEventStates).
Proof.
  intros sg events eid node qid slots Hfresh.
  assert (Hcells :
    (fun owner => match events.(inUsedEventStates) owner with
       | Some e => published_queue_node_rep sg
           (queue_publish events eid node qid slots) owner e
       | None => emp end) =
    (fun owner => match events.(inUsedEventStates) owner with
       | Some e => published_queue_node_rep sg events owner e
       | None => emp end)).
  { apply functional_extensionality; intro owner.
    destruct (events.(inUsedEventStates) owner) as [e|] eqn:Hget; [|reflexivity].
    unfold published_queue_node_rep.
    destruct e.(queueFields) as [q|] eqn:Hfields; [|reflexivity].
    assert (Hne : q.(qID) <> qid).
    { intro E; apply Hfresh; exists owner, e, q; auto. }
    simpl; rewrite kernel_map_set_other by exact Hne; reflexivity. }
  unfold store_map; rewrite Hcells; reflexivity.
Qed.

Lemma queue_publish_reconstructs_storage :
  forall sg events free eid node q slots,
  queue_published_storage_binding events ->
  queue_pool_partition sg events free ->
  queue_private_owner events eid = Some q.(qID) ->
  events.(inUsedEventStates) eid = None ->
  node.(queueFields) = Some q -> node.(eventType) = OS_EVENT_TYPE_Q ->
  queue_slots_model q slots ->
  store_map (published_queue_node_rep sg events) events.(inUsedEventStates) **
    (used_queue_control_block sg q **
      (PtrArray.mixed_full q.(qStart) q.(qSize) slots ** store_free_queue_list sg free)) |--
  queue_storage_rep sg (queue_publish events eid node q.(qID) slots).
Proof.
  intros sg events free eid node q slots Hbinding Hpart Howner Hnone Hq Htype Hslots.
  assert (Hprivate : queue_slot_private events q.(qID)) by (exists eid; exact Howner).
  assert (Hfresh : ~ queue_slot_published events q.(qID)).
  { intro Hpub; exact ((proj1 (proj2 (proj2 Hpart))) q.(qID) Hpub Hprivate). }
  pose proof (queue_publish_preserves_partition sg events free eid node q slots
    Hpart Howner Hnone Hq) as Hpart_after.
  pose proof (queue_publish_preserves_storage_binding events eid node q slots
    Hbinding Hfresh Hnone Hq Htype Hslots) as Hbinding_after.
  assert (Hnode : used_queue_control_block sg q ** PtrArray.mixed_full q.(qStart) q.(qSize) slots |--
    published_queue_node_rep sg (queue_publish events eid node q.(qID) slots) eid node).
  { unfold published_queue_node_rep; rewrite Hq; Exists slots.
    simpl; rewrite kernel_map_set_same; unfold queue_buffer_rep; entailer!. }
  rewrite <- (queue_published_nodes_fresh_buffer_eq sg events eid node q.(qID) slots Hfresh).
  sep_apply_l_atomic Hnode.
  sep_apply_l_atomic (store_map_equiv_store_map_missing
    (published_queue_node_rep sg (queue_publish events eid node q.(qID) slots))
    events.(inUsedEventStates) eid Hnone).
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (published_queue_node_rep sg (queue_publish events eid node q.(qID) slots))
    events.(inUsedEventStates) (kernel_map_set events.(inUsedEventStates) eid (Some node)) eid
    ltac:(intros; symmetry; apply kernel_map_set_other; assumption))).
  sep_apply_l_atomic (store_map_merge
    (published_queue_node_rep sg (queue_publish events eid node q.(qID) slots))
    eid node (kernel_map_set events.(inUsedEventStates) eid (Some node))
    (kernel_map_set_same _ events.(inUsedEventStates) eid (Some node))).
  unfold queue_storage_rep; entailer!.
  Exists free; entailer!.
Qed.

Lemma queue_publish_from_private_buffer :
  forall sg events eid node q slots,
  queue_private_owner events eid = Some q.(qID) ->
  events.(inUsedEventStates) eid = None ->
  node.(queueFields) = Some q -> node.(eventType) = OS_EVENT_TYPE_Q ->
  queue_storage_rep sg events **
    (used_queue_control_block sg q ** queue_buffer_rep q slots) |--
  queue_storage_rep sg (queue_publish events eid node q.(qID) slots).
Proof.
  intros sg events eid node q slots Howner Hnone Hq Htype.
  unfold queue_storage_rep at 1; unfold queue_buffer_rep at 1; Intros free.
  eapply derivable1_trans; [|exact (queue_publish_reconstructs_storage sg events free eid node q slots
    ltac:(assumption) ltac:(assumption) Howner Hnone Hq Htype ltac:(assumption))].
  entailer!.
Qed.

Lemma queue_publish_reconstructs_event_queue :
  forall sg tasks events eid allocation node q slots,
  event_pool_partition sg events ->
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = Some q.(qID) ->
  allocation.(eventPrivateStorage) = event_image sg tasks node ->
  node.(queueFields) = Some q -> node.(eventType) = OS_EVENT_TYPE_Q ->
  (event_private_storage_rep sg eid allocation ** event_raw_rep sg tasks events) **
    (queue_storage_rep sg events **
      (used_queue_control_block sg q ** queue_buffer_rep q slots)) |--
  event_raw_rep sg tasks (queue_publish events eid node q.(qID) slots) **
    queue_storage_rep sg (queue_publish events eid node q.(qID) slots).
Proof.
  intros sg tasks events eid allocation node q slots Hpart Hget Hqid Himage Hq Htype.
  destruct (event_pool_private_not_free sg events eid allocation Hpart Hget)
    as [_ [_ Hnone]].
  assert (Howner : queue_private_owner events eid = Some q.(qID)).
  { unfold queue_private_owner; rewrite Hget; exact Hqid. }
  apply derivable1_sepcon_mono.
  - exact (event_publish_reconstructs_raw_rep sg tasks events eid allocation node
      Hpart Hget Himage).
  - exact (queue_publish_from_private_buffer sg events eid node q slots
      Howner Hnone Hq Htype).
Qed.

Lemma queue_pool_initial_partition : forall sg,
  queue_pool_partition sg (event_pool_initial sg) (queue_all_ids sg).
Proof.
  intros sg; split; [apply queue_all_ids_valid|]; split.
  - intro qid; split.
    + intros [[eid [e [q [Hget _]]]]|[eid Hget]]; discriminate.
    + intros [Hrange Hnot]; exfalso; apply Hnot.
      unfold queue_all_ids; apply In_Zrange; exact Hrange.
  - split.
    + intros qid [eid [e [q [Hget _]]]]; discriminate.
    + intros first second qid Hfirst; discriminate.
Qed.

Lemma queue_pool_initial_storage_binding : forall sg,
  queue_published_storage_binding (event_pool_initial sg).
Proof.
  intros sg; split; [intros eid e q Hget; discriminate|]; split;
    [intros qid slots Hget|intros first second e1 e2 q1 q2 Hget]; discriminate.
Qed.

Lemma queue_initial_storage_from_free_list : forall sg,
  store_free_queue_list sg (queue_all_ids sg) |--
  queue_storage_rep sg (event_pool_initial sg).
Proof.
  intros sg.
  pose proof (queue_pool_initial_partition sg) as Hpart.
  pose proof (queue_pool_initial_storage_binding sg) as Hbinding.
  assert (Hempty : store_map (published_queue_node_rep sg (event_pool_initial sg))
    (event_pool_initial sg).(inUsedEventStates) --||-- emp).
  { apply store_map_empty.
    - exists []; split; [intro i; split; [contradiction|intros [v H]; discriminate]|constructor].
    - intro i; left; reflexivity. }
  unfold queue_storage_rep; rewrite Hempty; entailer!.
  Exists (queue_all_ids sg); entailer!.
Qed.

Lemma queue_private_owner_after_event_private_write :
  forall events eid allocation field value,
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  queue_private_owner (event_private_write events eid allocation field value) =
    queue_private_owner events.
Proof.
  intros events eid allocation field value Hget; apply functional_extensionality; intro other.
  unfold queue_private_owner, event_private_write, event_set_lifecycle; simpl.
  unfold kernel_map_set; destruct (Z.eq_dec other eid) as [->|Hne]; [rewrite Hget|]; reflexivity.
Qed.

Lemma queue_storage_event_private_write_eq : forall sg events eid allocation field value,
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  queue_storage_rep sg (event_private_write events eid allocation field value) =
    queue_storage_rep sg events.
Proof.
  intros sg events eid allocation field value Hget.
  unfold queue_storage_rep, queue_pool_partition, queue_slot_private.
  rewrite (queue_private_owner_after_event_private_write events eid allocation field value Hget).
  reflexivity.
Qed.

Lemma queue_reserve_control_block_preserves_event_in_range :
  forall sg tasks events eid allocation qid,
  event_in_range sg tasks events ->
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_in_range sg tasks (queue_reserve_control_block events eid allocation qid).
Proof.
  intros sg tasks events eid allocation qid [Hpart [Hfree [Hidentity Hrest]]] Hget.
  split; [eapply queue_reserve_control_block_preserves_event_partition; eauto|].
  split; [eapply queue_reserve_control_block_preserves_event_free_storage; eauto|].
  split; [eapply queue_reserve_control_block_preserves_event_identity; eauto|].
  exact Hrest.
Qed.

Lemma queue_storage_event_detach_head_eq : forall sg events eid rest image,
  events.(eventLifecycle).(eventPrivate) eid = None ->
  queue_storage_rep sg (event_detach_head events eid rest image) =
    queue_storage_rep sg events.
Proof.
  intros sg events eid rest image Hnone.
  assert (Howners : queue_private_owner (event_detach_head events eid rest image) =
    queue_private_owner events).
  { apply functional_extensionality; intro other; unfold queue_private_owner,
      event_detach_head; simpl; unfold kernel_map_set.
    destruct (Z.eq_dec other eid) as [->|Hne]; [rewrite Hnone|]; reflexivity. }
  unfold queue_storage_rep, queue_pool_partition, queue_slot_private.
  rewrite Howners; reflexivity.
Qed.

Lemma queue_storage_event_rollback_eq : forall sg events eid allocation,
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None ->
  queue_storage_rep sg (event_rollback sg events eid allocation) =
    queue_storage_rep sg events.
Proof.
  intros sg events eid allocation Hget Hnone.
  assert (Howners : queue_private_owner (event_rollback sg events eid allocation) =
    queue_private_owner events).
  { apply functional_extensionality; intro other; unfold queue_private_owner,
      event_rollback; simpl; unfold kernel_map_set.
    destruct (Z.eq_dec other eid) as [->|Hne]; [rewrite Hget, Hnone|]; reflexivity. }
  unfold queue_storage_rep, queue_pool_partition, queue_slot_private.
  rewrite Howners; reflexivity.
Qed.

(** The deletion tail is entered after its waiter branch has completed.
    QCB root/link writes precede the ECB tail while still in the critical
    section.  The buffer is unregistered, never deallocated by OSQDel. *)
Definition queue_recycle (sg : StableGlobVars) (events : Glob_EventAbstractState)
  (eid : EventID) (image : EventStorage) (qid : QueueID) : Glob_EventAbstractState :=
  let recycled := event_recycle sg events eid image in
  {| inUsedEventStates := recycled.(inUsedEventStates);
     unUsedEventStates := recycled.(unUsedEventStates);
     publishedQueueBytes := kernel_map_set events.(publishedQueueBytes) qid None;
     eventLifecycle := recycled.(eventLifecycle) |}.

Definition qcb_recycle (image : QCBStorage) (next : addr) : QCBStorage :=
  qcb_write image QCBPtr (Some next).

Lemma qcb_recycle_preserves_other_fields : forall image next field,
  field <> QCBPtr -> qcb_recycle image next field = image field.
Proof. intros; apply field_update_other; assumption. Qed.

Lemma qcb_recycle_merge_storage : forall sg qid image next,
  (qcb_addr sg qid + OSQPtr_off) # Ptr |-> next **
    qcb_storage_without_field sg qid image QCBPtr |--
    qcb_storage_rep sg qid (qcb_recycle image next).
Proof.
  intros; exact (qcb_storage_merge_updated_field sg qid image QCBPtr (Some next)).
Qed.

Lemma qcb_cell_forget_value : forall base field value,
  qcb_cell base field value |-- qcb_cell base field None.
Proof.
  intros base field [value|]; [|reflexivity].
  destruct field; cbn [qcb_cell];
    first [apply store_ptr_undef_store_ptr|apply store_ushort_undef_store_ushort].
Qed.

Lemma qcb_recycle_storage_implies_free : forall sg qid image next,
  qcb_storage_rep sg qid (qcb_recycle image next) |-- free_queue_node sg qid next.
Proof.
  intros; eapply derivable1_trans; [|exact (proj1 (qcb_free_image_rep sg qid next))].
  apply QueueFieldStorage.store_fields_mono; intros field Hfield.
  destruct (QCBField_eq_dec field QCBPtr) as [->|Hne]; [reflexivity|].
  rewrite qcb_recycle_preserves_other_fields by exact Hne.
  assert (Hfree : qcb_free_image next field = None) by
    (destruct field; try reflexivity; congruence).
  rewrite Hfree; apply qcb_cell_forget_value.
Qed.

Lemma queue_private_owner_after_recycle : forall sg events eid image qid,
  queue_private_owner (queue_recycle sg events eid image qid) =
    queue_private_owner events.
Proof. reflexivity. Qed.

Lemma queue_slot_published_after_recycle : forall sg events eid node q image,
  queue_published_storage_binding events ->
  events.(inUsedEventStates) eid = Some node -> node.(queueFields) = Some q ->
  forall other,
  (queue_slot_published (queue_recycle sg events eid image q.(qID)) other <->
    queue_slot_published events other /\ other <> q.(qID)).
Proof.
  intros sg events eid node q image [_ [_ Hunique]] Hnode Hq other; split.
  - intros [owner [e [q' [Hget [Hfields Hqid]]]]].
    simpl in Hget; unfold kernel_map_set in Hget.
    destruct (Z.eq_dec owner eid) as [->|Hne]; [discriminate|].
    split; [exists owner, e, q'; auto|].
    intro E; apply Hne; eapply Hunique; eauto; congruence.
  - intros [[owner [e [q' [Hget [Hfields Hqid]]]]] Hne].
    exists owner, e, q'; simpl.
    rewrite kernel_map_set_other.
    + auto.
    + intro E; subst owner; rewrite Hnode in Hget; inversion Hget; subst e.
      rewrite Hq in Hfields; inversion Hfields; subst q'; congruence.
Qed.

Lemma queue_recycle_preserves_partition : forall sg events free eid node q image,
  queue_published_storage_binding events ->
  queue_pool_partition sg events free ->
  events.(inUsedEventStates) eid = Some node -> node.(queueFields) = Some q ->
  queue_pool_partition sg
    (queue_recycle sg events eid image q.(qID)) (q.(qID) :: free).
Proof.
  intros sg events free eid node q image Hbinding Hvalid Hget Hq.
  pose proof (queue_slot_published_after_recycle sg events eid node q image Hbinding Hget Hq)
    as Hpublished.
  destruct Hvalid as [[Hnd Hr] [Hpart [Hdisjoint Hunique]]].
  assert (Hpub : queue_slot_published events q.(qID)) by (exists eid, node, q; auto).
  destruct (proj1 (Hpart q.(qID)) (or_introl Hpub)) as [Hrange Hnot].
  pose proof (Hdisjoint q.(qID) Hpub) as Hnotprivate.
  split.
  - split; constructor; assumption.
  - split.
    + intro other; rewrite Hpublished.
      change (((queue_slot_published events other /\ other <> q.(qID)) \/
        queue_slot_private events other) <-> valid_queue_id sg other /\ ~ In other (q.(qID) :: free)).
      specialize (Hpart other); simpl.
      destruct (Z.eq_dec other q.(qID)) as [->|Hne]; intuition congruence.
    + split.
      * intros other Hpub_after Hpriv; apply Hpublished in Hpub_after.
        exact (Hdisjoint other (proj1 Hpub_after) Hpriv).
      * exact Hunique.
Qed.

Lemma queue_recycle_preserves_storage_binding : forall sg events eid node q image,
  queue_published_storage_binding events ->
  events.(inUsedEventStates) eid = Some node -> node.(queueFields) = Some q ->
  queue_published_storage_binding (queue_recycle sg events eid image q.(qID)).
Proof.
  intros sg events eid node q image [Hnodes [Hbytes Hunique]] Hnode Hq.
  assert (Hotherqid : forall owner e q', owner <> eid ->
    events.(inUsedEventStates) owner = Some e -> e.(queueFields) = Some q' -> q'.(qID) <> q.(qID)).
  { intros owner e q' Hne Hget Hfields Heq; apply Hne; eapply Hunique; eauto. }
  split.
  - intros owner e q' Hget Hfields; simpl in Hget |- *; unfold kernel_map_set in Hget.
    destruct (Z.eq_dec owner eid) as [->|Hne]; [discriminate|].
    destruct (Hnodes owner e q' Hget Hfields) as [Htype [slots [Hslot Hmodel]]].
    split; [exact Htype|exists slots].
    rewrite kernel_map_set_other by (eapply Hotherqid; eauto); auto.
  - split.
    + intros other slots Hslot; simpl in Hslot; unfold kernel_map_set in Hslot.
      destruct (Z.eq_dec other q.(qID)) as [->|Hne]; [discriminate|].
      destruct (Hbytes other slots Hslot) as [owner [e [q' [Hget [Hfields Hqid]]]]].
      exists owner, e, q'; simpl; rewrite kernel_map_set_other.
      * auto.
      * intro E; subst owner; rewrite Hnode in Hget; inversion Hget; subst e.
        rewrite Hq in Hfields; inversion Hfields; subst q'; congruence.
    + intros first second e1 e2 q1 q2 Hfirst Hsecond Hfields1 Hfields2 Hqid.
      simpl in Hfirst, Hsecond; unfold kernel_map_set in Hfirst, Hsecond.
      destruct (Z.eq_dec first eid); [discriminate|].
      destruct (Z.eq_dec second eid); [discriminate|].
      eapply Hunique; eauto.
Qed.

Lemma queue_recycled_nodes_frame_eq : forall sg events eid node q image,
  queue_published_storage_binding events ->
  events.(inUsedEventStates) eid = Some node -> node.(queueFields) = Some q ->
  store_map (published_queue_node_rep sg (queue_recycle sg events eid image q.(qID)))
    (queue_recycle sg events eid image q.(qID)).(inUsedEventStates) =
  store_map (published_queue_node_rep sg events)
    (queue_recycle sg events eid image q.(qID)).(inUsedEventStates).
Proof.
  intros sg events eid node q image [_ [_ Hunique]] Hnode Hq.
  assert (Hcells :
    (fun owner => match (queue_recycle sg events eid image q.(qID)).(inUsedEventStates) owner with
       | Some e => published_queue_node_rep sg
           (queue_recycle sg events eid image q.(qID)) owner e
       | None => emp end) =
    (fun owner => match (queue_recycle sg events eid image q.(qID)).(inUsedEventStates) owner with
       | Some e => published_queue_node_rep sg events owner e
       | None => emp end)).
  { apply functional_extensionality; intro owner.
    destruct ((queue_recycle sg events eid image q.(qID)).(inUsedEventStates) owner)
      as [e|] eqn:Hget; [|reflexivity].
    simpl in Hget; unfold kernel_map_set in Hget.
    destruct (Z.eq_dec owner eid) as [->|Hne]; [discriminate|].
    unfold published_queue_node_rep; destruct e.(queueFields) as [q'|] eqn:Hfields;
      [|reflexivity].
    assert (Hqidne : q'.(qID) <> q.(qID)).
    { intro E; apply Hne; eapply Hunique; eauto. }
    simpl; rewrite kernel_map_set_other by exact Hqidne; reflexivity. }
  unfold store_map; rewrite Hcells; reflexivity.
Qed.

(** The input contains the newly written free root/link and the residual
    with the deleted published node removed.  Keeping the old node in the
    residual would double-own the QCB and its buffer. *)
Lemma queue_recycle_reconstructs_storage : forall sg events free eid node q image,
  queue_published_storage_binding events ->
  queue_pool_partition sg events free ->
  events.(inUsedEventStates) eid = Some node -> node.(queueFields) = Some q ->
  store_map_missing_i (published_queue_node_rep sg events) events.(inUsedEventStates) eid **
    (sg.(g_OSQFreeList) # Ptr |-> qcb_addr sg q.(qID) **
      (free_queue_node sg q.(qID) (queue_free_head sg free) ** store_free_queue_nodes sg free)) |--
  queue_storage_rep sg (queue_recycle sg events eid image q.(qID)).
Proof.
  intros sg events free eid node q image Hbinding Hpart Hget Hq.
  pose proof (queue_recycle_preserves_partition sg events free eid node q image
    Hbinding Hpart Hget Hq) as Hpart_after.
  pose proof (queue_recycle_preserves_storage_binding sg events eid node q image
    Hbinding Hget Hq) as Hbinding_after.
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (published_queue_node_rep sg events) events.(inUsedEventStates)
    (kernel_map_set events.(inUsedEventStates) eid None) eid
    ltac:(intros; symmetry; apply kernel_map_set_other; assumption))).
  sep_apply_l_atomic (store_map_missing_equiv_store_map
    (published_queue_node_rep sg events) (kernel_map_set events.(inUsedEventStates) eid None) eid
    (kernel_map_set_same _ events.(inUsedEventStates) eid None)).
  pose proof (queue_recycled_nodes_frame_eq sg events eid node q image Hbinding Hget Hq) as Hframe.
  change (store_map (published_queue_node_rep sg (queue_recycle sg events eid image q.(qID)))
    (kernel_map_set events.(inUsedEventStates) eid None) =
    store_map (published_queue_node_rep sg events)
      (kernel_map_set events.(inUsedEventStates) eid None)) in Hframe.
  rewrite <- Hframe.
  unfold queue_storage_rep; entailer!.
  Exists (q.(qID) :: free); unfold store_free_queue_list; simpl; entailer!.
Qed.

Lemma queue_recycle_returns_buffer : forall sg events free eid node q image slots,
  queue_published_storage_binding events ->
  queue_pool_partition sg events free ->
  events.(inUsedEventStates) eid = Some node -> node.(queueFields) = Some q ->
  (store_map_missing_i (published_queue_node_rep sg events) events.(inUsedEventStates) eid **
    (sg.(g_OSQFreeList) # Ptr |-> qcb_addr sg q.(qID) **
      (free_queue_node sg q.(qID) (queue_free_head sg free) ** store_free_queue_nodes sg free))) **
    queue_buffer_rep q slots |--
  queue_storage_rep sg (queue_recycle sg events eid image q.(qID)) **
    PtrArray.mixed_full q.(qStart) q.(qSize) slots.
Proof.
  intros sg events free eid node q image slots Hbinding Hpart Hget Hq.
  apply derivable1_sepcon_mono.
  - exact (queue_recycle_reconstructs_storage sg events free eid node q image
      Hbinding Hpart Hget Hq).
  - unfold queue_buffer_rep; entailer!.
Qed.

(** OSQPtr has no live-queue interpretation.  None forgets its value while
    retaining its cell; it is not a claim that the C field was cleared. *)
Definition qcb_fields_image (q : QueueFields) : QCBStorage :=
  fun field => match field with
  | QCBPtr => None
  | QCBStart => Some q.(qStart)
  | QCBEnd => Some (queue_end_addr q)
  | QCBIn => Some (queue_in_addr q)
  | QCBOut => Some (queue_out_addr q)
  | QCBSize => Some q.(qSize)
  | QCBEntries => Some (queue_entries q)
  end.

Lemma used_queue_control_block_fields_equiv : forall sg q,
  used_queue_control_block sg q --||--
    qcb_storage_rep sg q.(qID) (qcb_fields_image q).
Proof.
  intros; unfold qcb_storage_rep, qcb_fields.
  repeat rewrite QueueFieldStorage.store_fields_cons by
    (repeat constructor; simpl; intuition discriminate).
  rewrite QueueFieldStorage.store_fields_nil.
  unfold qcb_fields_image, qcb_cell, qcb_field_offset, used_queue_control_block.
  split; entailer!.
Qed.

Lemma queue_storage_split_event : forall sg events eid node q,
  events.(inUsedEventStates) eid = Some node -> node.(queueFields) = Some q ->
  queue_storage_rep sg events |--
  EX free, EX slots,
    coq_prop (queue_published_storage_binding events /\ queue_pool_partition sg events free /\
      events.(publishedQueueBytes) q.(qID) = Some slots) &&
    ((used_queue_control_block sg q ** queue_buffer_rep q slots) **
      (store_map_missing_i (published_queue_node_rep sg events) events.(inUsedEventStates) eid **
        store_free_queue_list sg free)).
Proof.
  intros sg events eid node q Hget Hq; unfold queue_storage_rep; Intros free.
  sep_apply_l_atomic (store_map_split (published_queue_node_rep sg events) eid node
    events.(inUsedEventStates) Hget).
  assert (Hnode : published_queue_node_rep sg events eid node =
    EX slots, coq_prop (events.(publishedQueueBytes) q.(qID) = Some slots) &&
      (used_queue_control_block sg q ** queue_buffer_rep q slots)).
  { unfold published_queue_node_rep; rewrite Hq; reflexivity. }
  rewrite Hnode; Intros slots; Exists free; Exists slots; entailer!.
Qed.

Lemma queue_recycle_reconstructs_event_queue :
  forall sg tasks events free eid node q image slots,
  event_pool_partition sg events -> event_free_storage_valid sg events ->
  queue_published_storage_binding events -> queue_pool_partition sg events free ->
  events.(inUsedEventStates) eid = Some node -> node.(queueFields) = Some q ->
  (store_map_missing_i (used_event_rep sg tasks) events.(inUsedEventStates) eid **
    event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
      (event_recycle_image sg events.(unUsedEventStates) image) **
    event_free_storage_rep sg events **
    sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid) **
  ((store_map_missing_i (published_queue_node_rep sg events) events.(inUsedEventStates) eid **
    (sg.(g_OSQFreeList) # Ptr |-> qcb_addr sg q.(qID) **
      (free_queue_node sg q.(qID) (queue_free_head sg free) ** store_free_queue_nodes sg free))) **
    queue_buffer_rep q slots) |--
  event_raw_rep sg tasks (queue_recycle sg events eid image q.(qID)) **
    (queue_storage_rep sg (queue_recycle sg events eid image q.(qID)) **
      PtrArray.mixed_full q.(qStart) q.(qSize) slots).
Proof.
  intros sg tasks events free eid node q image slots Hevent Hfree Hbinding Hpart Hget Hq.
  apply derivable1_sepcon_mono.
  - exact (event_recycle_reconstructs_raw_rep sg tasks events eid node image Hevent Hfree Hget).
  - exact (queue_recycle_returns_buffer sg events free eid node q image slots Hbinding Hpart Hget Hq).
Qed.

Lemma queue_recycle_preserves_event_in_range : forall sg tasks events eid node qid image,
  event_in_range sg tasks events -> events.(inUsedEventStates) eid = Some node ->
  event_in_range sg tasks (queue_recycle sg events eid image qid).
Proof.
  intros sg tasks events eid node qid image Hvalid Hget.
  exact (event_recycle_preserves_in_range sg tasks events eid node image Hvalid Hget).
Qed.

(* Physical ring slots, source-ordered QCB writes, and shared storage updates. *)

Lemma queue_ring_index_in_range : forall q k,
  0 < q.(qSize) -> 0 <= queue_ring_index q k < q.(qSize).
Proof.
  intros q k Hsize; unfold queue_ring_index.
  destruct (Z.eqb q.(qSize) 0) eqn:E; [apply Z.eqb_eq in E; lia|].
  apply Z.mod_pos_bound; exact Hsize.
Qed.

Lemma queue_ring_index_injective : forall q first second,
  0 < q.(qSize) -> 0 <= first < q.(qSize) -> 0 <= second < q.(qSize) ->
  queue_ring_index q first = queue_ring_index q second -> first = second.
Proof.
  intros q first second Hsize Hfirst Hsecond Heq.
  unfold queue_ring_index in Heq.
  destruct (Z.eqb q.(qSize) 0) eqn:E; [apply Z.eqb_eq in E; lia|].
  pose proof (f_equal (fun i => (i + - q.(qOutIndex)) mod q.(qSize)) Heq) as Hshift.
  cbn beta in Hshift.
  rewrite !Z.add_mod_idemp_l in Hshift by lia.
  replace (q.(qOutIndex) + first + - q.(qOutIndex)) with first in Hshift by lia.
  replace (q.(qOutIndex) + second + - q.(qOutIndex)) with second in Hshift by lia.
  rewrite !Z.mod_small in Hshift by lia; exact Hshift.
Qed.

Lemma queue_flush_preserves_slots : forall q slots,
  queue_slots_model q slots -> queue_slots_model (queue_flush_state q) slots.
Proof.
  intros q slots [Hlen Hslots]; split; [exact Hlen|].
  intros i p [k [Hk _]]; unfold queue_entries, queue_flush_state, queue_with_contents in Hk;
    simpl in Hk; rewrite Zlength_nil in Hk; lia.
Qed.

Lemma queue_ring_index_zero : forall q,
  0 < q.(qSize) -> 0 <= q.(qOutIndex) < q.(qSize) -> queue_ring_index q 0 = q.(qOutIndex).
Proof.
  intros q Hsize Hout; unfold queue_ring_index.
  destruct (Z.eqb q.(qSize) 0) eqn:E; [apply Z.eqb_eq in E; lia|].
  rewrite Z.add_0_r; apply Z.mod_small; exact Hout.
Qed.

Lemma queue_ring_index_enqueue_position : forall sg waiters q,
  queue_fields_consistency sg waiters q -> 0 < q.(qSize) ->
  queue_ring_index q (queue_entries q) = q.(qInIndex).
Proof.
  intros sg waiters q Hvalid Hsize.
  destruct (queue_fields_consistency_positive sg waiters q Hvalid Hsize)
    as [_ [_ [_ Heq]]].
  unfold queue_ring_index; destruct (Z.eqb q.(qSize) 0) eqn:E;
    [apply Z.eqb_eq in E; lia|symmetry; exact Heq].
Qed.

Lemma queue_enqueue_back_preserves_slots : forall sg q slots message after,
  queue_fields_consistency sg [] q -> queue_slots_model q slots ->
  queue_enqueue_back q message = Some after ->
  queue_slots_model after (replace_Znth q.(qInIndex) (Some message) slots).
Proof.
  intros sg q slots message after Hvalid [Hlen Hslots] Hstep.
  unfold queue_enqueue_back in Hstep.
  destruct (Z.ltb (queue_entries q) q.(qSize)) eqn:Hroom; [|discriminate].
  apply Z.ltb_lt in Hroom; inversion Hstep; subst after; clear Hstep.
  assert (Hcount : 0 <= queue_entries q) by (apply Zlength_nonneg).
  assert (Hsize : 0 < q.(qSize)) by lia.
  destruct (queue_fields_consistency_positive sg [] q Hvalid Hsize)
    as [Hin [Hout [_ Heq]]].
  pose proof (queue_ring_index_enqueue_position sg [] q Hvalid Hsize) as Hwrite.
  split; [rewrite Zlength_replace_Znth; exact Hlen|].
  intros i value [k [Hk [Hindex Hvalue]]].
  assert (Hktotal : 0 <= k <= queue_entries q).
  { unfold queue_entries, queue_with_contents in Hk; simpl in Hk.
    rewrite Zlength_app, Zlength_cons, Zlength_nil in Hk; unfold queue_entries; lia. }
  change (queue_ring_index q k = i) in Hindex.
  change (value = Znth k (q.(qMessages) ++ [message]) 0) in Hvalue.
  assert (Hirange : 0 <= i < q.(qSize)).
  { rewrite <- Hindex; apply queue_ring_index_in_range; exact Hsize. }
  destruct (Z_lt_dec k (queue_entries q)) as [Hbefore|Hlast].
  - assert (Hne : q.(qInIndex) <> i).
    { intro E.
      assert (Hkeq : k = queue_entries q).
      { apply (queue_ring_index_injective q k (queue_entries q) Hsize ltac:(lia) ltac:(lia)).
        rewrite Hindex, Hwrite; congruence. }
      lia. }
    rewrite (Znth_replace_Znth_Diff None slots q.(qInIndex) i (Some message)) by
      (try rewrite Hlen; lia).
    apply Hslots; exists k; split; [lia|]; split; [exact Hindex|].
    rewrite app_Znth1 in Hvalue by (unfold queue_entries in Hbefore; lia); exact Hvalue.
  - assert (Hkeq : k = queue_entries q) by lia; subst k.
    rewrite Hwrite in Hindex; subst i.
    unfold queue_entries in Hvalue; rewrite app_Znth2, Z.sub_diag, Znth0_cons in Hvalue by lia.
    rewrite Znth_replace_Znth_Same by (rewrite Hlen; exact Hin); congruence.
Qed.

Lemma queue_ring_index_after_retreat : forall q qin messages k,
  0 < q.(qSize) ->
  queue_ring_index
    (queue_with_contents q qin (queue_retreat_index q.(qSize) q.(qOutIndex)) messages) (k + 1) =
    queue_ring_index q k.
Proof.
  intros q qin messages k Hsize; unfold queue_ring_index, queue_with_contents; simpl.
  destruct (Z.eqb q.(qSize) 0) eqn:E; [apply Z.eqb_eq in E; lia|].
  unfold queue_retreat_index; destruct (Z.eqb q.(qOutIndex) 0) eqn:Hout.
  - apply Z.eqb_eq in Hout; rewrite Hout; simpl.
    replace (q.(qSize) - 1 + (k + 1)) with (k + 1 * q.(qSize)) by lia.
    rewrite Z.mod_add by lia; reflexivity.
  - f_equal; lia.
Qed.

Lemma queue_ring_index_after_advance : forall q qin messages k,
  0 < q.(qSize) ->
  queue_ring_index
    (queue_with_contents q qin (queue_advance_index q.(qSize) q.(qOutIndex)) messages) k =
    queue_ring_index q (k + 1).
Proof.
  intros q qin messages k Hsize; unfold queue_ring_index, queue_with_contents; simpl.
  destruct (Z.eqb q.(qSize) 0) eqn:E; [apply Z.eqb_eq in E; lia|].
  unfold queue_advance_index; destruct (Z.eqb (q.(qOutIndex) + 1) q.(qSize)) eqn:Hout.
  - apply Z.eqb_eq in Hout; simpl.
    replace (q.(qOutIndex) + (k + 1)) with (k + 1 * q.(qSize)) by lia.
    rewrite Z.mod_add by lia; reflexivity.
  - f_equal; lia.
Qed.

Lemma queue_enqueue_front_preserves_slots : forall sg q slots message after,
  queue_fields_consistency sg [] q -> queue_slots_model q slots ->
  queue_enqueue_front q message = Some after ->
  queue_slots_model after
    (replace_Znth (queue_retreat_index q.(qSize) q.(qOutIndex)) (Some message) slots).
Proof.
  intros sg q slots message after Hvalid [Hlen Hslots] Hstep.
  unfold queue_enqueue_front in Hstep.
  destruct (Z.ltb (queue_entries q) q.(qSize)) eqn:Hroom; [|discriminate].
  apply Z.ltb_lt in Hroom; inversion Hstep; subst after; clear Hstep.
  assert (Hcount : 0 <= queue_entries q) by (apply Zlength_nonneg).
  assert (Hsize : 0 < q.(qSize)) by lia.
  destruct (queue_fields_consistency_positive sg [] q Hvalid Hsize) as [Hin [Hout _]].
  pose proof (queue_retreat_index_in_range _ _ Hsize Hout) as Hnewout.
  assert (Hwrite : queue_ring_index
    (queue_with_contents q q.(qInIndex) (queue_retreat_index q.(qSize) q.(qOutIndex))
      (message :: q.(qMessages))) 0 = queue_retreat_index q.(qSize) q.(qOutIndex)).
  { apply queue_ring_index_zero; assumption. }
  split; [rewrite Zlength_replace_Znth; exact Hlen|].
  intros i value [k [Hk [Hindex Hvalue]]].
  assert (Hktotal : 0 <= k <= queue_entries q).
  { unfold queue_entries, queue_with_contents in Hk; simpl in Hk.
    rewrite Zlength_cons in Hk; unfold queue_entries; lia. }
  change (value = Znth k (message :: q.(qMessages)) 0) in Hvalue.
  assert (Hirange : 0 <= i < q.(qSize)).
  { rewrite <- Hindex; exact (queue_ring_index_in_range
      (queue_with_contents q q.(qInIndex) (queue_retreat_index q.(qSize) q.(qOutIndex))
        (message :: q.(qMessages))) k Hsize). }
  destruct (Z.eq_dec k 0) as [->|Hnonzero].
  - rewrite Hwrite in Hindex; subst i.
    rewrite Znth0_cons in Hvalue.
    rewrite Znth_replace_Znth_Same by (rewrite Hlen; exact Hnewout); congruence.
  - assert (Hne : queue_retreat_index q.(qSize) q.(qOutIndex) <> i).
    { intro E.
      apply Hnonzero; apply (queue_ring_index_injective
        (queue_with_contents q q.(qInIndex) (queue_retreat_index q.(qSize) q.(qOutIndex))
          (message :: q.(qMessages))) k 0 Hsize ltac:(simpl; lia) ltac:(simpl; lia)).
      rewrite Hindex, Hwrite; congruence. }
    rewrite (Znth_replace_Znth_Diff None slots
      (queue_retreat_index q.(qSize) q.(qOutIndex)) i (Some message)) by
      (try rewrite Hlen; lia).
    apply Hslots; exists (k - 1); split; [lia|]; split.
    + rewrite <- (queue_ring_index_after_retreat q q.(qInIndex) (message :: q.(qMessages)) (k - 1) Hsize).
      replace (k - 1 + 1) with k by lia; exact Hindex.
    + rewrite Znth_cons in Hvalue by lia; exact Hvalue.
Qed.

Lemma queue_dequeue_front_preserves_slots : forall sg waiters q slots message after,
  queue_fields_consistency sg waiters q -> queue_slots_model q slots ->
  queue_dequeue_front q = Some (message, after) -> queue_slots_model after slots.
Proof.
  intros sg waiters q slots message after Hvalid [Hlen Hslots] Hstep.
  unfold queue_dequeue_front in Hstep; destruct q.(qMessages) as [|head rest] eqn:Hmessages; [discriminate|].
  inversion Hstep; subst message after; clear Hstep.
  assert (Hsize : 0 < q.(qSize)).
  { destruct Hvalid as [_ [_ [_ [Hshape _]]]].
    destruct Hshape as [[Hz [_ [_ Hempty]]]|[Hp _]]; [congruence|exact Hp]. }
  split; [exact Hlen|].
  intros i value [k [Hk [Hindex Hvalue]]]; apply Hslots; exists (k + 1); split.
  - unfold queue_entries, queue_with_contents in Hk; simpl in Hk.
    unfold queue_entries; rewrite Hmessages, Zlength_cons; lia.
  - split.
    + rewrite <- (queue_ring_index_after_advance q q.(qInIndex) rest k Hsize); exact Hindex.
    + change (value = Znth k rest 0) in Hvalue.
      rewrite Hmessages, Znth_cons by
        (unfold queue_entries, queue_with_contents in Hk; simpl in Hk; lia).
      replace (k + 1 - 1) with k by lia; exact Hvalue.
Qed.

Lemma queue_dequeue_front_head_slot : forall sg waiters q slots message after,
  queue_fields_consistency sg waiters q -> queue_slots_model q slots ->
  queue_dequeue_front q = Some (message, after) -> Znth q.(qOutIndex) slots None = Some message.
Proof.
  intros sg waiters q slots message after Hvalid [Hlen Hslots] Hstep.
  unfold queue_dequeue_front in Hstep; destruct q.(qMessages) as [|head rest] eqn:Hmessages; [discriminate|].
  inversion Hstep; subst message after; clear Hstep.
  assert (Hsize : 0 < q.(qSize)).
  { destruct Hvalid as [_ [_ [_ [Hshape _]]]].
    destruct Hshape as [[Hz [_ [_ Hempty]]]|[Hp _]]; [congruence|exact Hp]. }
  destruct (queue_fields_consistency_positive sg waiters q Hvalid Hsize) as [_ [Hout _]].
  apply Hslots; exists 0; split.
  - unfold queue_entries; rewrite Hmessages, Zlength_cons.
    pose proof (Zlength_nonneg rest); lia.
  - split; [apply queue_ring_index_zero; assumption|rewrite Hmessages, Znth0_cons; reflexivity].
Qed.

(** Array ownership is handled by QCP's existing mixed-array library.
    The Queue wrapper only retains the FIFO/slot relation needed after a
    source store.  None denotes owned unspecified bytes, not an absent cell. *)
Lemma queue_buffer_split_slot : forall q slots i,
  0 <= i < q.(qSize) ->
  queue_buffer_rep q slots |--
  coq_prop (queue_slots_model q slots) &&
    (PtrArray.mixedstoreA q.(qStart) i (Znth i slots None) **
      PtrArray.mixed_missing_i q.(qStart) i 0 q.(qSize) slots).
Proof.
  intros q slots i Hrange; unfold queue_buffer_rep; Intros.
  entailer!; apply PtrArray.mixed_full_split_to_mixed_missing_i; exact Hrange.
Qed.

Lemma queue_buffer_merge_slot : forall q slots i,
  queue_slots_model q slots -> 0 <= i < q.(qSize) ->
  PtrArray.mixedstoreA q.(qStart) i (Znth i slots None) **
    PtrArray.mixed_missing_i q.(qStart) i 0 q.(qSize) slots |-- queue_buffer_rep q slots.
Proof.
  intros q slots i Hmodel Hrange.
  eapply derivable1_trans;
    [exact (PtrArray.mixed_missing_i_merge_to_mixed_full q.(qStart) i q.(qSize)
      (Znth i slots None) slots Hrange)|].
  rewrite replace_Znth_Znth; unfold queue_buffer_rep; entailer!.
Qed.

Lemma queue_enqueue_back_merge_buffer : forall sg q slots message after,
  queue_fields_consistency sg [] q -> queue_slots_model q slots ->
  queue_enqueue_back q message = Some after ->
  (queue_in_addr q) # Ptr |-> message **
    PtrArray.mixed_missing_i q.(qStart) q.(qInIndex) 0 q.(qSize) slots |--
  queue_buffer_rep after (replace_Znth q.(qInIndex) (Some message) slots).
Proof.
  intros sg q slots message after Hvalid Hslots Hstep.
  pose proof (queue_enqueue_back_preserves_slots sg q slots message after Hvalid Hslots Hstep) as Hnew.
  unfold queue_enqueue_back in Hstep.
  destruct (Z.ltb (queue_entries q) q.(qSize)) eqn:Hroom; [|discriminate].
  apply Z.ltb_lt in Hroom; inversion Hstep; subst after; clear Hstep.
  assert (Hsize : 0 < q.(qSize)) by (pose proof (Zlength_nonneg q.(qMessages)); unfold queue_entries in Hroom; lia).
  destruct (queue_fields_consistency_positive sg [] q Hvalid Hsize) as [Hin _].
  eapply derivable1_trans;
    [exact (PtrArray.mixed_missing_i_merge_to_mixed_full q.(qStart) q.(qInIndex) q.(qSize)
      (Some message) slots Hin)|].
  unfold queue_buffer_rep; entailer!.
Qed.

Lemma queue_enqueue_front_merge_buffer : forall sg q slots message after,
  queue_fields_consistency sg [] q -> queue_slots_model q slots ->
  queue_enqueue_front q message = Some after ->
  (queue_out_addr after) # Ptr |-> message **
    PtrArray.mixed_missing_i q.(qStart) (queue_retreat_index q.(qSize) q.(qOutIndex)) 0 q.(qSize) slots |--
  queue_buffer_rep after
    (replace_Znth (queue_retreat_index q.(qSize) q.(qOutIndex)) (Some message) slots).
Proof.
  intros sg q slots message after Hvalid Hslots Hstep.
  pose proof (queue_enqueue_front_preserves_slots sg q slots message after Hvalid Hslots Hstep) as Hnew.
  unfold queue_enqueue_front in Hstep.
  destruct (Z.ltb (queue_entries q) q.(qSize)) eqn:Hroom; [|discriminate].
  apply Z.ltb_lt in Hroom; inversion Hstep; subst after; clear Hstep.
  assert (Hsize : 0 < q.(qSize)) by (pose proof (Zlength_nonneg q.(qMessages)); unfold queue_entries in Hroom; lia).
  destruct (queue_fields_consistency_positive sg [] q Hvalid Hsize) as [_ [Hout _]].
  pose proof (queue_retreat_index_in_range _ _ Hsize Hout) as Hnext.
  eapply derivable1_trans;
    [exact (PtrArray.mixed_missing_i_merge_to_mixed_full q.(qStart)
      (queue_retreat_index q.(qSize) q.(qOutIndex)) q.(qSize) (Some message) slots Hnext)|].
  unfold queue_buffer_rep; entailer!.
Qed.

Lemma queue_flush_preserves_buffer : forall q slots,
  queue_buffer_rep q slots |-- queue_buffer_rep (queue_flush_state q) slots.
Proof.
  intros q slots; unfold queue_buffer_rep; Intros.
  pose proof (queue_flush_preserves_slots q slots H); entailer!.
Qed.

Lemma queue_dequeue_front_preserves_buffer : forall sg waiters q slots message after,
  queue_fields_consistency sg waiters q -> queue_dequeue_front q = Some (message, after) ->
  queue_buffer_rep q slots |-- queue_buffer_rep after slots.
Proof.
  intros sg waiters q slots message after Hvalid Hstep.
  unfold queue_buffer_rep; Intros.
  pose proof (queue_dequeue_front_preserves_slots sg waiters q slots message after Hvalid H Hstep) as Hnew.
  unfold queue_dequeue_front in Hstep; destruct q.(qMessages) as [|head rest]; [discriminate|].
  inversion Hstep; subst message after; entailer!.
Qed.

Lemma queue_buffer_split_head : forall sg waiters q slots message after,
  queue_fields_consistency sg waiters q ->
  queue_dequeue_front q = Some (message, after) ->
  queue_buffer_rep q slots |--
  coq_prop (queue_slots_model q slots) &&
    ((queue_out_addr q) # Ptr |-> message **
      PtrArray.mixed_missing_i q.(qStart) q.(qOutIndex) 0 q.(qSize) slots).
Proof.
  intros sg waiters q slots message after Hvalid Hstep.
  assert (Hnonempty : q.(qMessages) <> []).
  { intro Hempty; unfold queue_dequeue_front in Hstep; rewrite Hempty in Hstep; discriminate. }
  assert (Hsize : 0 < q.(qSize)).
  { destruct Hvalid as [_ [_ [_ [Hshape _]]]]; destruct Hshape as [[_ [_ [_ Hempty]]]|[Hp _]];
      [contradiction|exact Hp]. }
  destruct (queue_fields_consistency_positive sg waiters q Hvalid Hsize) as [_ [Hout _]].
  unfold queue_buffer_rep; Intros.
  pose proof (queue_dequeue_front_head_slot sg waiters q slots message after Hvalid H Hstep) as Hhead.
  entailer!.
  pose proof (PtrArray.mixed_full_split_to_mixed_missing_i q.(qStart) q.(qOutIndex)
    q.(qSize) slots None Hout) as Hsplit.
  change (PtrArray.mixed_full q.(qStart) q.(qSize) slots |--
    PtrArray.mixedstoreA q.(qStart) q.(qOutIndex) (Znth q.(qOutIndex) slots None) **
      PtrArray.mixed_missing_i q.(qStart) q.(qOutIndex) 0 q.(qSize) slots) in Hsplit.
  rewrite Hhead in Hsplit; exact Hsplit.
Qed.

(** These are the QCB write slices shared by Queue operations, not complete
    public API semantics.  [q] is the entry observation; [image] retains all
    unwritten fields.  The advanced pointer can be one-past-end before the
    wrap store, so intermediate images need not satisfy the stable ring law.
    Actual buffer reads/stores are separate spatial obligations above. *)
Definition qcb_flush (image : QCBStorage) (start : addr) : QCBStorage :=
  qcb_write
    (qcb_write (qcb_write image QCBIn (Some start)) QCBOut (Some start))
    QCBEntries (Some 0).

Definition qcb_enqueue_back (q : QueueFields) (image : QCBStorage) : QCBStorage :=
  let advanced := queue_in_addr q + Ucos2Verify.lib.event.sizeof_ptr in
  let after_in := qcb_write image QCBIn (Some advanced) in
  let after_count := qcb_write after_in QCBEntries (Some (queue_entries q + 1)) in
  if Z.eqb advanced (queue_end_addr q)
  then qcb_write after_count QCBIn (Some q.(qStart)) else after_count.

(** OSQPostOpt's back branch performs the same stores in this distinct order:
    advance, optional wrap, count.  No scheduling/callback lies between them. *)
Definition qcb_enqueue_back_wrap_first (q : QueueFields) (image : QCBStorage)
  : QCBStorage :=
  let advanced := queue_in_addr q + Ucos2Verify.lib.event.sizeof_ptr in
  let after_in := qcb_write image QCBIn (Some advanced) in
  let after_wrap := if Z.eqb advanced (queue_end_addr q)
    then qcb_write after_in QCBIn (Some q.(qStart)) else after_in in
  qcb_write after_wrap QCBEntries (Some (queue_entries q + 1)).

Definition qcb_enqueue_front (q : QueueFields) (image : QCBStorage) : QCBStorage :=
  let wrap := Z.eqb (queue_out_addr q) q.(qStart) in
  let after_wrap := if wrap then qcb_write image QCBOut (Some (queue_end_addr q)) else image in
  let out := (if wrap then queue_end_addr q else queue_out_addr q) - Ucos2Verify.lib.event.sizeof_ptr in
  qcb_write (qcb_write after_wrap QCBOut (Some out))
    QCBEntries (Some (queue_entries q + 1)).

Definition qcb_dequeue_front (q : QueueFields) (image : QCBStorage) : QCBStorage :=
  let advanced := queue_out_addr q + Ucos2Verify.lib.event.sizeof_ptr in
  let after_out := qcb_write image QCBOut (Some advanced) in
  let after_count := qcb_write after_out QCBEntries (Some (queue_entries q - 1)) in
  if Z.eqb advanced (queue_end_addr q)
  then qcb_write after_count QCBOut (Some q.(qStart)) else after_count.

Lemma qcb_enqueue_back_write_order_eq : forall q image,
  qcb_enqueue_back_wrap_first q image = qcb_enqueue_back q image.
Proof.
  intros q image; apply functional_extensionality; intro field.
  unfold qcb_enqueue_back_wrap_first, qcb_enqueue_back.
  destruct (Z.eqb (queue_in_addr q + Ucos2Verify.lib.event.sizeof_ptr) (queue_end_addr q));
    destruct field; reflexivity.
Qed.

Lemma qcb_flush_fields_eq : forall q,
  qcb_flush (qcb_fields_image q) q.(qStart) =
    qcb_fields_image (queue_flush_state q).
Proof.
  intros q; apply functional_extensionality; intros [];
    unfold qcb_flush, qcb_write, qcb_fields_image, queue_flush_state,
      queue_with_contents, field_update, queue_in_addr, queue_out_addr, queue_end_addr, queue_entries;
    simpl; rewrite ?Zlength_nil; f_equal; lia.
Qed.

Lemma queue_in_advance_end_eqb : forall q,
  Z.eqb (queue_in_addr q + Ucos2Verify.lib.event.sizeof_ptr) (queue_end_addr q) =
    Z.eqb (q.(qInIndex) + 1) q.(qSize).
Proof.
  intros q; unfold queue_in_addr, queue_end_addr, Ucos2Verify.lib.event.sizeof_ptr.
  destruct (Z.eqb_spec (qStart q + qInIndex q * 4 + 4) (qStart q + qSize q * 4));
    destruct (Z.eqb_spec (qInIndex q + 1) (qSize q)); try reflexivity; lia.
Qed.

Lemma queue_out_advance_end_eqb : forall q,
  Z.eqb (queue_out_addr q + Ucos2Verify.lib.event.sizeof_ptr) (queue_end_addr q) =
    Z.eqb (q.(qOutIndex) + 1) q.(qSize).
Proof.
  intros q; unfold queue_out_addr, queue_end_addr, Ucos2Verify.lib.event.sizeof_ptr.
  destruct (Z.eqb_spec (qStart q + qOutIndex q * 4 + 4) (qStart q + qSize q * 4));
    destruct (Z.eqb_spec (qOutIndex q + 1) (qSize q)); try reflexivity; lia.
Qed.

Lemma queue_out_start_eqb : forall q,
  Z.eqb (queue_out_addr q) q.(qStart) = Z.eqb q.(qOutIndex) 0.
Proof.
  intros q; unfold queue_out_addr, Ucos2Verify.lib.event.sizeof_ptr.
  destruct (Z.eqb_spec (qStart q + qOutIndex q * 4) (qStart q));
    destruct (Z.eqb_spec (qOutIndex q) 0); try reflexivity; lia.
Qed.

Lemma qcb_enqueue_back_fields_eq : forall q message after,
  queue_enqueue_back q message = Some after ->
  qcb_enqueue_back q (qcb_fields_image q) = qcb_fields_image after.
Proof.
  intros q message after Hstep; unfold queue_enqueue_back in Hstep.
  destruct (Z.ltb (queue_entries q) q.(qSize)); [|discriminate].
  inversion Hstep; subst after; clear Hstep.
  unfold qcb_enqueue_back; rewrite queue_in_advance_end_eqb.
  destruct (Z.eqb (q.(qInIndex) + 1) q.(qSize)) eqn:Hwrap;
    apply functional_extensionality; intros [];
    unfold qcb_write, qcb_fields_image, field_update,
      queue_with_contents, queue_in_addr, queue_out_addr, queue_end_addr,
      queue_entries, queue_advance_index; simpl;
    rewrite ?Hwrap, ?Zlength_app, ?Zlength_cons, ?Zlength_nil;
    unfold Ucos2Verify.lib.event.sizeof_ptr; simpl; f_equal; try lia.
  change (Some (q.(qStart) + q.(qInIndex) * 4 + 4) =
    Some (q.(qStart) + (q.(qInIndex) + 1) * 4)).
  apply (@f_equal Z (option Z) (@Some Z)); lia.
Qed.

Lemma qcb_enqueue_back_wrap_first_fields_eq : forall q message after,
  queue_enqueue_back q message = Some after ->
  qcb_enqueue_back_wrap_first q (qcb_fields_image q) = qcb_fields_image after.
Proof.
  intros; rewrite qcb_enqueue_back_write_order_eq;
    eapply qcb_enqueue_back_fields_eq; eauto.
Qed.

Lemma qcb_enqueue_front_fields_eq : forall q message after,
  queue_enqueue_front q message = Some after ->
  qcb_enqueue_front q (qcb_fields_image q) = qcb_fields_image after.
Proof.
  intros q message after Hstep; unfold queue_enqueue_front in Hstep.
  destruct (Z.ltb (queue_entries q) q.(qSize)); [|discriminate].
  inversion Hstep; subst after; clear Hstep.
  unfold qcb_enqueue_front; rewrite queue_out_start_eqb.
  destruct (Z.eqb q.(qOutIndex) 0) eqn:Hwrap;
    apply functional_extensionality; intros [];
    unfold qcb_write, qcb_fields_image, field_update,
      queue_with_contents, queue_in_addr, queue_out_addr, queue_end_addr,
      queue_entries, queue_retreat_index; simpl;
    rewrite ?Hwrap, ?Zlength_cons;
    unfold Ucos2Verify.lib.event.sizeof_ptr; simpl; f_equal; try lia.
  all: apply (@f_equal Z (option Z) (@Some Z)); lia.
Qed.

Lemma qcb_dequeue_front_fields_eq : forall q message after,
  queue_dequeue_front q = Some (message, after) ->
  qcb_dequeue_front q (qcb_fields_image q) = qcb_fields_image after.
Proof.
  intros q message after Hstep; unfold queue_dequeue_front in Hstep.
  destruct q.(qMessages) as [|head rest] eqn:Hmessages; [discriminate|].
  inversion Hstep; subst message after; clear Hstep.
  unfold qcb_dequeue_front; rewrite queue_out_advance_end_eqb.
  destruct (Z.eqb (q.(qOutIndex) + 1) q.(qSize)) eqn:Hwrap;
    apply functional_extensionality; intros [];
    unfold qcb_write, qcb_fields_image, field_update,
      queue_with_contents, queue_in_addr, queue_out_addr, queue_end_addr,
      queue_entries, queue_advance_index; simpl;
    rewrite ?Hwrap, ?Hmessages, ?Zlength_cons;
    unfold Ucos2Verify.lib.event.sizeof_ptr; simpl; f_equal; try lia.
  all: apply (@f_equal Z (option Z) (@Some Z)); lia.
Qed.

(** The mathematical count updates above agree with the source UShort
    writes on stable guarded branches; neither increment nor decrement wraps. *)
Lemma queue_entries_in_range : forall sg waiters q,
  queue_fields_consistency sg waiters q -> 0 <= queue_entries q <= 0xFFFF.
Proof.
  intros sg waiters q [_ [_ [Hsize [Hshape _]]]].
  destruct Hshape as [[_ [_ [_ Hempty]]]|[_ [_ [_ [Hcount _]]]]]; [|lia].
  unfold queue_entries; rewrite Hempty, Zlength_nil; lia.
Qed.

Lemma queue_entries_increment_in_range : forall sg waiters q,
  queue_fields_consistency sg waiters q -> queue_entries q < q.(qSize) ->
  0 <= queue_entries q + 1 <= 0xFFFF.
Proof.
  intros sg waiters q Hvalid Hroom.
  pose proof (queue_entries_in_range sg waiters q Hvalid).
  destruct Hvalid as [_ [_ [Hsize _]]]; lia.
Qed.

Lemma queue_entries_decrement_in_range : forall sg waiters q,
  queue_fields_consistency sg waiters q -> 0 < queue_entries q ->
  0 <= queue_entries q - 1 <= 0xFFFF.
Proof.
  intros sg waiters q Hvalid Hnonempty.
  pose proof (queue_entries_in_range sg waiters q Hvalid); lia.
Qed.

Lemma qcb_flush_other_field_eq : forall image start field,
  field <> QCBIn -> field <> QCBOut -> field <> QCBEntries ->
  qcb_flush image start field = image field.
Proof. intros image start [] Hin Hout Hentries; try contradiction; reflexivity. Qed.

Lemma qcb_enqueue_back_other_field_eq : forall q image field,
  field <> QCBIn -> field <> QCBEntries ->
  qcb_enqueue_back q image field = image field.
Proof.
  intros q image field Hin Hentries; unfold qcb_enqueue_back.
  destruct (Z.eqb (queue_in_addr q + Ucos2Verify.lib.event.sizeof_ptr) (queue_end_addr q));
    destruct field; try contradiction; reflexivity.
Qed.

Lemma qcb_enqueue_front_other_field_eq : forall q image field,
  field <> QCBOut -> field <> QCBEntries ->
  qcb_enqueue_front q image field = image field.
Proof.
  intros q image field Hout Hentries; unfold qcb_enqueue_front.
  destruct (Z.eqb (queue_out_addr q) q.(qStart));
    destruct field; try contradiction; reflexivity.
Qed.

Lemma qcb_dequeue_front_other_field_eq : forall q image field,
  field <> QCBOut -> field <> QCBEntries ->
  qcb_dequeue_front q image field = image field.
Proof.
  intros q image field Hout Hentries; unfold qcb_dequeue_front.
  destruct (Z.eqb (queue_out_addr q + Ucos2Verify.lib.event.sizeof_ptr) (queue_end_addr q));
    destruct field; try contradiction; reflexivity.
Qed.

(** Each endpoint rule consumes the actual already-written QCB and buffer
    cells.  It is a fold of those resources, not permission to perform a
    store, nor an assertion that an arbitrary environment preserves them. *)
Lemma queue_enqueue_back_reconstructs_node : forall sg q slots message after,
  queue_fields_consistency sg [] q -> queue_slots_model q slots ->
  queue_enqueue_back q message = Some after ->
  qcb_storage_rep sg q.(qID)
    (qcb_enqueue_back q (qcb_fields_image q)) **
  ((queue_in_addr q) # Ptr |-> message **
    PtrArray.mixed_missing_i q.(qStart) q.(qInIndex) 0 q.(qSize) slots) |--
  used_queue_control_block sg after **
    queue_buffer_rep after (replace_Znth q.(qInIndex) (Some message) slots).
Proof.
  intros sg q slots message after Hvalid Hslots Hstep.
  assert (Hqid : after.(qID) = q.(qID)).
  { unfold queue_enqueue_back in Hstep; destruct (Z.ltb (queue_entries q) q.(qSize));
      inversion Hstep; reflexivity. }
  rewrite (qcb_enqueue_back_fields_eq q message after Hstep), <- Hqid.
  apply derivable1_sepcon_mono.
  - exact (proj2 (used_queue_control_block_fields_equiv sg after)).
  - exact (queue_enqueue_back_merge_buffer sg q slots message after Hvalid Hslots Hstep).
Qed.

Lemma queue_enqueue_back_wrap_first_reconstructs_node : forall sg q slots message after,
  queue_fields_consistency sg [] q -> queue_slots_model q slots ->
  queue_enqueue_back q message = Some after ->
  qcb_storage_rep sg q.(qID)
    (qcb_enqueue_back_wrap_first q (qcb_fields_image q)) **
  ((queue_in_addr q) # Ptr |-> message **
    PtrArray.mixed_missing_i q.(qStart) q.(qInIndex) 0 q.(qSize) slots) |--
  used_queue_control_block sg after **
    queue_buffer_rep after (replace_Znth q.(qInIndex) (Some message) slots).
Proof.
  intros; rewrite qcb_enqueue_back_write_order_eq;
    eapply queue_enqueue_back_reconstructs_node; eauto.
Qed.

Lemma queue_enqueue_front_reconstructs_node : forall sg q slots message after,
  queue_fields_consistency sg [] q -> queue_slots_model q slots ->
  queue_enqueue_front q message = Some after ->
  qcb_storage_rep sg q.(qID)
    (qcb_enqueue_front q (qcb_fields_image q)) **
  ((queue_out_addr after) # Ptr |-> message **
    PtrArray.mixed_missing_i q.(qStart) (queue_retreat_index q.(qSize) q.(qOutIndex)) 0 q.(qSize) slots) |--
  used_queue_control_block sg after **
    queue_buffer_rep after
      (replace_Znth (queue_retreat_index q.(qSize) q.(qOutIndex)) (Some message) slots).
Proof.
  intros sg q slots message after Hvalid Hslots Hstep.
  assert (Hqid : after.(qID) = q.(qID)).
  { unfold queue_enqueue_front in Hstep; destruct (Z.ltb (queue_entries q) q.(qSize));
      inversion Hstep; reflexivity. }
  rewrite (qcb_enqueue_front_fields_eq q message after Hstep), <- Hqid.
  apply derivable1_sepcon_mono.
  - exact (proj2 (used_queue_control_block_fields_equiv sg after)).
  - exact (queue_enqueue_front_merge_buffer sg q slots message after Hvalid Hslots Hstep).
Qed.

Lemma queue_dequeue_front_reconstructs_node : forall sg waiters q slots message after,
  queue_fields_consistency sg waiters q -> queue_dequeue_front q = Some (message, after) ->
  qcb_storage_rep sg q.(qID)
    (qcb_dequeue_front q (qcb_fields_image q)) ** queue_buffer_rep q slots |--
  used_queue_control_block sg after ** queue_buffer_rep after slots.
Proof.
  intros sg waiters q slots message after Hvalid Hstep.
  assert (Hqid : after.(qID) = q.(qID)).
  { unfold queue_dequeue_front in Hstep; destruct q.(qMessages); inversion Hstep; reflexivity. }
  rewrite (qcb_dequeue_front_fields_eq q message after Hstep), <- Hqid.
  apply derivable1_sepcon_mono.
  - exact (proj2 (used_queue_control_block_fields_equiv sg after)).
  - exact (queue_dequeue_front_preserves_buffer sg waiters q slots message after Hvalid Hstep).
Qed.

Lemma queue_flush_reconstructs_node : forall sg q slots,
  qcb_storage_rep sg q.(qID) (qcb_flush (qcb_fields_image q) q.(qStart)) **
    queue_buffer_rep q slots |--
  used_queue_control_block sg (queue_flush_state q) **
    queue_buffer_rep (queue_flush_state q) slots.
Proof.
  intros; rewrite qcb_flush_fields_eq; apply derivable1_sepcon_mono.
  - exact (proj2 (used_queue_control_block_fields_equiv sg (queue_flush_state q))).
  - apply queue_flush_preserves_buffer.
Qed.

(** Updating a live ring changes its canonical Event payload and its one
    physical-buffer entry together.  Pool membership, object generation,
    private allocations, waiter registration and ECB bytes are unchanged. *)
Definition event_set_queue_fields (e : OSEventAbstractState) (q : QueueFields)
  : OSEventAbstractState :=
  {| eventType := e.(eventType); mutexFields := e.(mutexFields);
     semFields := e.(semFields); mboxFields := e.(mboxFields);
     queueFields := Some q; waitList := e.(waitList);
     eventGeneration := e.(eventGeneration); eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19) |}.

Lemma event_set_queue_fields_same : forall e q,
  e.(queueFields) = Some q -> event_set_queue_fields e q = e.
Proof. intros e q H; destruct e; simpl in H; subst; reflexivity. Qed.

Lemma event_set_queue_fields_last_write : forall e before after,
  event_set_queue_fields (event_set_queue_fields e before) after = event_set_queue_fields e after.
Proof. reflexivity. Qed.

Definition queue_update (events : Glob_EventAbstractState) (eid : EventID)
  (node : OSEventAbstractState) (q : QueueFields) (slots : list (option addr))
  : Glob_EventAbstractState :=
  let updated := update_event_field_raw events eid (event_set_queue_fields node q) in
  {| inUsedEventStates := updated.(inUsedEventStates);
     unUsedEventStates := updated.(unUsedEventStates);
     publishedQueueBytes := kernel_map_set events.(publishedQueueBytes) q.(qID) (Some slots);
     eventLifecycle := updated.(eventLifecycle) |}.

Lemma queue_update_preserves_published_bytes : forall events eid node q slots,
  events.(publishedQueueBytes) q.(qID) = Some slots ->
  (queue_update events eid node q slots).(publishedQueueBytes) = events.(publishedQueueBytes).
Proof.
  intros events eid node q slots Hslots; apply functional_extensionality; intro qid.
  cbn [queue_update publishedQueueBytes]; unfold kernel_map_set.
  destruct (Z.eq_dec qid q.(qID)) as [->|Hother]; [symmetry; exact Hslots|reflexivity].
Qed.

Lemma queue_update_preserves_published_slots : forall events eid node before after slots,
  events.(inUsedEventStates) eid = Some node -> node.(queueFields) = Some before ->
  after.(qID) = before.(qID) -> forall qid,
  queue_slot_published (queue_update events eid node after slots) qid <->
    queue_slot_published events qid.
Proof.
  intros events eid node before after slots Hnode Hbefore Hsame qid; split.
  - intros [owner [e [q [Hget [Hfields Hqid]]]]]; simpl in Hget.
    destruct (Z.eqb owner eid) eqn:E.
    + apply Z.eqb_eq in E; subst owner; inversion Hget; subst e.
      simpl in Hfields; inversion Hfields; subst q.
      exists eid, node, before; intuition congruence.
    + exists owner, e, q; auto.
  - intros [owner [e [q [Hget [Hfields Hqid]]]]].
    destruct (Z.eqb owner eid) eqn:E.
    + apply Z.eqb_eq in E; subst owner; rewrite Hnode in Hget; inversion Hget; subst e.
      rewrite Hbefore in Hfields; inversion Hfields; subst q.
      exists eid, (event_set_queue_fields node after), after; simpl; rewrite Z.eqb_refl;
        intuition congruence.
    + exists owner, e, q; simpl; rewrite E; auto.
Qed.

Lemma queue_update_preserves_partition : forall sg events free eid node before after slots,
  queue_pool_partition sg events free ->
  events.(inUsedEventStates) eid = Some node -> node.(queueFields) = Some before ->
  after.(qID) = before.(qID) ->
  queue_pool_partition sg (queue_update events eid node after slots) free.
Proof.
  intros sg events free eid node before after slots [Hfree [Hpart [Hdisjoint Hunique]]]
    Hget Hbefore Hsame.
  pose proof (queue_update_preserves_published_slots events eid node before after slots
    Hget Hbefore Hsame) as Hpublished.
  split; [exact Hfree|]; split.
  - intro qid; rewrite Hpublished; exact (Hpart qid).
  - split.
    + intros qid Hpub Hpriv; apply (Hdisjoint qid); [apply Hpublished; exact Hpub|exact Hpriv].
    + exact Hunique.
Qed.

Lemma queue_update_preserves_storage_binding : forall events eid node before after slots,
  queue_published_storage_binding events ->
  events.(inUsedEventStates) eid = Some node -> node.(queueFields) = Some before ->
  after.(qID) = before.(qID) -> queue_slots_model after slots ->
  queue_published_storage_binding (queue_update events eid node after slots).
Proof.
  intros events eid node before after slots [Hnodes [Hbytes Hunique]] Hnode Hbefore Hsame Hmodel.
  pose proof (proj1 (Hnodes eid node before Hnode Hbefore)) as Htype.
  assert (Hotherqid : forall owner e q, owner <> eid ->
    events.(inUsedEventStates) owner = Some e -> e.(queueFields) = Some q -> q.(qID) <> after.(qID)).
  { intros owner e q Hne Hget Hfields Heq; apply Hne; eapply Hunique; eauto; congruence. }
  split.
  - intros owner e q Hget Hfields; simpl in Hget |- *.
    destruct (Z.eqb owner eid) eqn:E.
    + apply Z.eqb_eq in E; subst owner; inversion Hget; subst e.
      simpl in Hfields; inversion Hfields; subst q.
      split; [exact Htype|exists slots; rewrite kernel_map_set_same; auto].
    + apply Z.eqb_neq in E.
      destruct (Hnodes owner e q Hget Hfields) as [Hty [bytes [Hslot Hslots]]].
      split; [exact Hty|exists bytes].
      rewrite kernel_map_set_other by (eapply Hotherqid; eauto); auto.
  - split.
    + intros qid bytes Hslot; simpl in Hslot; unfold kernel_map_set in Hslot.
      destruct (Z.eq_dec qid after.(qID)) as [->|Hne].
      * exists eid, (event_set_queue_fields node after), after; simpl; rewrite Z.eqb_refl; auto.
      * destruct (Hbytes qid bytes Hslot) as [owner [e [q [Hget [Hfields Hqid]]]]].
        assert (Howner : Z.eqb owner eid = false).
        { apply Z.eqb_neq; intro E; subst owner; rewrite Hnode in Hget; inversion Hget; subst e.
          rewrite Hbefore in Hfields; inversion Hfields; subst q; congruence. }
        exists owner, e, q; simpl; rewrite Howner; auto.
    + intros first second e1 e2 q1 q2 Hfirst Hsecond Hfields1 Hfields2 Hqid.
      simpl in Hfirst, Hsecond.
      destruct (Z.eqb first eid) eqn:E1; destruct (Z.eqb second eid) eqn:E2.
      * apply Z.eqb_eq in E1; apply Z.eqb_eq in E2; congruence.
      * apply Z.eqb_eq in E1; apply Z.eqb_neq in E2; subst first.
        inversion Hfirst; subst e1; simpl in Hfields1; inversion Hfields1; subst q1.
        exfalso; apply (Hotherqid second e2 q2 E2 Hsecond Hfields2); congruence.
      * apply Z.eqb_neq in E1; apply Z.eqb_eq in E2; subst second.
        inversion Hsecond; subst e2; simpl in Hfields2; inversion Hfields2; subst q2.
        exfalso; apply (Hotherqid first e1 q1 E1 Hfirst Hfields1); congruence.
      * eapply Hunique; eauto.
Qed.

Lemma event_set_queue_fields_image_eq : forall sg tasks node before after,
  node.(eventType) = OS_EVENT_TYPE_Q -> node.(queueFields) = Some before ->
  after.(qID) = before.(qID) ->
  event_image sg tasks (event_set_queue_fields node after) = event_image sg tasks node.
Proof.
  intros sg tasks node before after Htype Hbefore Hsame.
  apply functional_extensionality; intros []; cbn [event_image event_set_queue_fields]; try reflexivity.
  unfold encode_event_ptr_value, verification_slice_encode_event_ptr_value; simpl; rewrite Htype, Hbefore;
    simpl; rewrite Hsame; reflexivity.
Qed.

Lemma queue_update_preserves_event_raw_rep : forall sg tasks events eid node before after slots,
  events.(inUsedEventStates) eid = Some node ->
  node.(eventType) = OS_EVENT_TYPE_Q -> node.(queueFields) = Some before ->
  after.(qID) = before.(qID) ->
  event_raw_rep sg tasks events |--
    event_raw_rep sg tasks (queue_update events eid node after slots).
Proof.
  intros sg tasks events eid node before after slots Hget Htype Hbefore Hsame.
  sep_apply_l_atomic (event_raw_rep_split_eid sg tasks events eid node Hget).
  assert (Hcell : used_event_rep sg tasks eid node =
    used_event_rep sg tasks eid (event_set_queue_fields node after)).
  { unfold used_event_rep; rewrite (event_set_queue_fields_image_eq sg tasks node before after
      Htype Hbefore Hsame); reflexivity. }
  rewrite Hcell.
  exact (event_raw_rep_merge_updated_eid sg tasks events eid (event_set_queue_fields node after)).
Qed.

Lemma queue_update_preserves_event_in_range : forall sg tasks events eid node before after slots,
  event_in_range sg tasks events -> events.(inUsedEventStates) eid = Some node ->
  node.(eventType) = OS_EVENT_TYPE_Q -> node.(queueFields) = Some before ->
  after.(qID) = before.(qID) -> queue_fields_consistency sg node.(waitList) after ->
  event_in_range sg tasks (queue_update events eid node after slots).
Proof.
  intros sg tasks events eid node before after slots Hvalid Hget Htype Hbefore Hsame Hq.
  pose proof Hvalid as [_ [_ [_ [Hfields [_ [_ Hwait]]]]]].
  apply (event_update_preserves_in_range sg tasks events eid node (event_set_queue_fields node after)).
  - exact Hvalid.
  - exact Hget.
  - reflexivity.
  - specialize (Hfields eid node Hget); unfold event_fields_consistency in *; simpl; rewrite Htype in *;
      intuition discriminate.
  - unfold event_payload_consistency; simpl; rewrite Htype; exact Hq.
  - unfold event_queue_id; simpl; rewrite Htype, Hbefore; simpl; rewrite Hsame; reflexivity.
  - exact (Hwait eid node Hget).
Qed.

(** The payload of a published node reads its QID's buffer entry.  Equality
    of Event maps alone is therefore insufficient to frame Queue storage. *)
Lemma queue_published_nodes_buffer_eq : forall sg before after nodes,
  (forall eid e q, nodes eid = Some e -> e.(queueFields) = Some q ->
    before.(publishedQueueBytes) q.(qID) = after.(publishedQueueBytes) q.(qID)) ->
  store_map (published_queue_node_rep sg before) nodes =
    store_map (published_queue_node_rep sg after) nodes.
Proof.
  intros sg before after nodes Hbytes.
  assert (Hcells :
    (fun eid => match nodes eid with
      | Some e => published_queue_node_rep sg before eid e | None => emp end) =
    (fun eid => match nodes eid with
      | Some e => published_queue_node_rep sg after eid e | None => emp end)).
  { apply functional_extensionality; intro eid; destruct (nodes eid) as [e|] eqn:Hget; [|reflexivity].
    unfold published_queue_node_rep; destruct e.(queueFields) as [q|] eqn:Hq; [|reflexivity].
    rewrite (Hbytes eid e q Hget Hq); reflexivity. }
  unfold store_map; rewrite Hcells; reflexivity.
Qed.

Lemma queue_update_missing_nodes_equiv : forall sg events eid node before after slots,
  queue_published_storage_binding events ->
  events.(inUsedEventStates) eid = Some node -> node.(queueFields) = Some before ->
  after.(qID) = before.(qID) ->
  store_map_missing_i (published_queue_node_rep sg events) events.(inUsedEventStates) eid --||--
    store_map_missing_i (published_queue_node_rep sg (queue_update events eid node after slots))
      (queue_update events eid node after slots).(inUsedEventStates) eid.
Proof.
  intros sg events eid node before after slots [_ [_ Hunique]] Hnode Hbefore Hsame.
  set (cleared := kernel_map_set events.(inUsedEventStates) eid None).
  assert (Hnone : cleared eid = None) by (unfold cleared; apply kernel_map_set_same).
  assert (Hclear : forall P : EventID -> OSEventAbstractState -> Assertion,
    store_map_missing_i P events.(inUsedEventStates) eid --||-- store_map P cleared).
  { intro P.
    destruct (store_map_missing_i_equiv P events.(inUsedEventStates) cleared eid
      ltac:(intros; symmetry; unfold cleared; apply kernel_map_set_other; assumption)) as [Hf Hb].
    split.
    - eapply derivable1_trans; [exact Hf|apply store_map_missing_equiv_store_map; exact Hnone].
    - eapply derivable1_trans; [apply store_map_equiv_store_map_missing; exact Hnone|exact Hb]. }
  assert (Hbuffers : store_map (published_queue_node_rep sg events) cleared =
    store_map (published_queue_node_rep sg (queue_update events eid node after slots)) cleared).
  { apply queue_published_nodes_buffer_eq; intros owner e q Hget Hq.
    unfold cleared, kernel_map_set in Hget; destruct (Z.eq_dec owner eid) as [->|Hne]; [discriminate|].
    assert (Hqidne : q.(qID) <> after.(qID)).
    { intro E; apply Hne; eapply Hunique; eauto; congruence. }
    simpl; rewrite kernel_map_set_other by exact Hqidne; reflexivity. }
  destruct (Hclear (published_queue_node_rep sg events)) as [HbeforeF HbeforeB].
  destruct (Hclear (published_queue_node_rep sg (queue_update events eid node after slots)))
    as [HafterF HafterB].
  destruct (store_map_missing_i_equiv
    (published_queue_node_rep sg (queue_update events eid node after slots))
    events.(inUsedEventStates) (queue_update events eid node after slots).(inUsedEventStates) eid
    ltac:(intros owner Hne; simpl; destruct (Z.eqb owner eid) eqn:E;
      [apply Z.eqb_eq in E; contradiction|reflexivity])) as [HmapF HmapB].
  split.
  - eapply derivable1_trans; [exact HbeforeF|]; rewrite Hbuffers.
    eapply derivable1_trans; [exact HafterB|exact HmapF].
  - eapply derivable1_trans; [exact HmapB|].
    eapply derivable1_trans; [exact HafterF|]; rewrite <- Hbuffers; exact HbeforeB.
Qed.

Lemma queue_update_reconstructs_storage : forall sg events free eid node before after slots,
  queue_published_storage_binding events -> queue_pool_partition sg events free ->
  events.(inUsedEventStates) eid = Some node -> node.(queueFields) = Some before ->
  after.(qID) = before.(qID) -> queue_slots_model after slots ->
  store_map_missing_i (published_queue_node_rep sg events) events.(inUsedEventStates) eid **
    ((used_queue_control_block sg after ** PtrArray.mixed_full after.(qStart) after.(qSize) slots) **
      store_free_queue_list sg free) |--
  queue_storage_rep sg (queue_update events eid node after slots).
Proof.
  intros sg events free eid node before after slots Hbinding Hpart Hget Hbefore Hsame Hslots.
  pose proof (queue_update_preserves_partition sg events free eid node before after slots
    Hpart Hget Hbefore Hsame) as Hpart_after.
  pose proof (queue_update_preserves_storage_binding events eid node before after slots
    Hbinding Hget Hbefore Hsame Hslots) as Hbinding_after.
  assert (Hnode : used_queue_control_block sg after ** PtrArray.mixed_full after.(qStart) after.(qSize) slots |--
    published_queue_node_rep sg (queue_update events eid node after slots)
      eid (event_set_queue_fields node after)).
  { unfold published_queue_node_rep; simpl; Exists slots.
    rewrite kernel_map_set_same; unfold queue_buffer_rep; entailer!. }
  sep_apply_l_atomic (proj1 (queue_update_missing_nodes_equiv sg events eid node before after slots
    Hbinding Hget Hbefore Hsame)).
  sep_apply_l_atomic Hnode.
  sep_apply_l_atomic (store_map_merge
    (published_queue_node_rep sg (queue_update events eid node after slots))
    eid (event_set_queue_fields node after)
    (queue_update events eid node after slots).(inUsedEventStates)
    ltac:(simpl; rewrite Z.eqb_refl; reflexivity)).
  unfold queue_storage_rep; entailer!; Exists free; entailer!.
Qed.

Lemma queue_update_reconstructs_event_queue : forall sg tasks events free eid node before after slots,
  queue_published_storage_binding events -> queue_pool_partition sg events free ->
  events.(inUsedEventStates) eid = Some node -> node.(eventType) = OS_EVENT_TYPE_Q ->
  node.(queueFields) = Some before -> after.(qID) = before.(qID) -> queue_slots_model after slots ->
  event_raw_rep sg tasks events **
    (store_map_missing_i (published_queue_node_rep sg events) events.(inUsedEventStates) eid **
      ((used_queue_control_block sg after ** PtrArray.mixed_full after.(qStart) after.(qSize) slots) **
        store_free_queue_list sg free)) |--
  event_raw_rep sg tasks (queue_update events eid node after slots) **
    queue_storage_rep sg (queue_update events eid node after slots).
Proof.
  intros sg tasks events free eid node before after slots Hbinding Hpart Hget Htype Hbefore Hsame Hslots.
  apply derivable1_sepcon_mono.
  - exact (queue_update_preserves_event_raw_rep sg tasks events eid node before after slots
      Hget Htype Hbefore Hsame).
  - exact (queue_update_reconstructs_storage sg events free eid node before after slots
      Hbinding Hpart Hget Hbefore Hsame Hslots).
Qed.

(** Updating only non-Queue fields of a live ECB leaves its QCB and ring
    unchanged.  The type premise is needed for the published binding, not
    for ownership alone.  These rules retain the complete Queue payload,
    including stale buffer cells, private associations and free links. *)
Lemma queue_event_update_preserves_published_slots : forall events eid old new,
  events.(inUsedEventStates) eid = Some old -> new.(queueFields) = old.(queueFields) ->
  forall qid, queue_slot_published (update_event_field_raw events eid new) qid <->
    queue_slot_published events qid.
Proof.
  intros events eid old new Hold Hqueue qid; split.
  - intros [owner [e [q [He [Hq Hqid]]]]]; simpl in He.
    destruct (Z.eqb owner eid) eqn:E.
    + apply Z.eqb_eq in E; subst owner; injection He as He; subst e.
      exists eid, old, q; split; [exact Hold|]; split; [rewrite <- Hqueue; exact Hq|exact Hqid].
    + exists owner, e, q; auto.
  - intros [owner [e [q [He [Hq Hqid]]]]].
    destruct (Z.eqb owner eid) eqn:E.
    + apply Z.eqb_eq in E; subst owner; rewrite Hold in He; injection He as He; subst e.
      exists eid, new, q; simpl; rewrite Z.eqb_refl.
      split; [reflexivity|]; split; [rewrite Hqueue; exact Hq|exact Hqid].
    + exists owner, e, q; simpl; rewrite E; auto.
Qed.

Lemma queue_event_update_preserves_partition : forall sg events free eid old new,
  queue_pool_partition sg events free ->
  events.(inUsedEventStates) eid = Some old -> new.(queueFields) = old.(queueFields) ->
  queue_pool_partition sg (update_event_field_raw events eid new) free.
Proof.
  intros sg events free eid old new [Hfree [Hpartition [Hdisjoint Hunique]]] Hold Hqueue.
  pose proof (queue_event_update_preserves_published_slots events eid old new Hold Hqueue)
    as Hpublished.
  split; [exact Hfree|]; split.
  - intro qid; rewrite Hpublished; exact (Hpartition qid).
  - split.
    + intros qid Hpub Hprivate; apply (Hdisjoint qid); [apply Hpublished; exact Hpub|exact Hprivate].
    + exact Hunique.
Qed.

Lemma queue_event_update_preserves_storage_binding : forall events eid old new,
  queue_published_storage_binding events ->
  events.(inUsedEventStates) eid = Some old -> new.(queueFields) = old.(queueFields) ->
  new.(eventType) = old.(eventType) ->
  queue_published_storage_binding (update_event_field_raw events eid new).
Proof.
  intros events eid old new [Hnodes [Hbytes Hunique]] Hold Hqueue Htype.
  assert (Horigin : forall owner e q,
    (update_event_field_raw events eid new).(inUsedEventStates) owner = Some e ->
    e.(queueFields) = Some q -> exists before,
      events.(inUsedEventStates) owner = Some before /\ before.(queueFields) = Some q /\
      e.(eventType) = before.(eventType)).
  { intros owner e q He Hq; simpl in He; destruct (Z.eqb owner eid) eqn:E.
    - apply Z.eqb_eq in E; subst owner; injection He as He; subst e.
      exists old; split; [exact Hold|]; split; [rewrite <- Hqueue; exact Hq|exact Htype].
    - exists e; auto. }
  split.
  - intros owner e q He Hq; destruct (Horigin owner e q He Hq) as [before [Hb [Hqb Htb]]].
    destruct (Hnodes owner before q Hb Hqb) as [Ht Hslots].
    split; [congruence|exact Hslots].
  - split.
    + intros qid slots Hslot.
      destruct (Hbytes qid slots Hslot) as [owner [e [q [He [Hq Hqid]]]]].
      destruct (Z.eqb owner eid) eqn:E.
      * apply Z.eqb_eq in E; subst owner; rewrite Hold in He; injection He as He; subst e.
        exists eid, new, q; simpl; rewrite Z.eqb_refl.
        split; [reflexivity|]; split; [rewrite Hqueue; exact Hq|exact Hqid].
      * exists owner, e, q; simpl; rewrite E; auto.
    + intros first second e1 e2 q1 q2 Hfirst Hsecond Hq1 Hq2 Hqid.
      destruct (Horigin first e1 q1 Hfirst Hq1) as [before1 [H1 [HQ1 _]]].
      destruct (Horigin second e2 q2 Hsecond Hq2) as [before2 [H2 [HQ2 _]]].
      eapply Hunique; eauto.
Qed.

Lemma queue_event_update_preserves_storage : forall sg events eid old new,
  events.(inUsedEventStates) eid = Some old -> new.(queueFields) = old.(queueFields) ->
  new.(eventType) = old.(eventType) ->
  queue_storage_rep sg events |--
    queue_storage_rep sg (update_event_field_raw events eid new).
Proof.
  intros sg events eid old new Hold Hqueue Htype.
  assert (Hnodes : store_map (published_queue_node_rep sg events) events.(inUsedEventStates) |--
    store_map (published_queue_node_rep sg (update_event_field_raw events eid new))
      (update_event_field_raw events eid new).(inUsedEventStates)).
  { assert (Hcell : published_queue_node_rep sg events eid old =
      published_queue_node_rep sg events eid new).
    { unfold published_queue_node_rep; rewrite Hqueue; reflexivity. }
    sep_apply_l_atomic (store_map_split (published_queue_node_rep sg events) eid old _ Hold).
    rewrite Hcell.
    sep_apply_l_atomic (proj1 (store_map_missing_i_equiv (published_queue_node_rep sg events)
      events.(inUsedEventStates) (update_event_field_raw events eid new).(inUsedEventStates) eid
      ltac:(intros owner Hne; simpl; destruct (Z.eqb owner eid) eqn:E;
        [apply Z.eqb_eq in E; contradiction|reflexivity]))).
    sep_apply_l_atomic (store_map_merge (published_queue_node_rep sg events) eid new
      (update_event_field_raw events eid new).(inUsedEventStates)
      ltac:(simpl; rewrite Z.eqb_refl; reflexivity)).
    entailer!. }
  unfold queue_storage_rep; Intros free.
  assert (Hbinding_after : queue_published_storage_binding (update_event_field_raw events eid new)).
  { eapply queue_event_update_preserves_storage_binding; eauto. }
  assert (Hpartition_after : queue_pool_partition sg (update_event_field_raw events eid new) free).
  { eapply queue_event_update_preserves_partition; eauto. }
  sep_apply_l_atomic Hnodes; entailer!; Exists free; entailer!.
Qed.

(** Inserting, replacing or removing an Event with no Queue payload does
    not change Queue ownership.  This interface is used by Sem/Mbox
    publication and recycling.  It preserves the real published bytes
    and private QCB associations, rather than forgetting those owners. *)
Lemma queue_storage_event_entry_frame : forall sg events after eid before next,
  events.(inUsedEventStates) eid = before ->
  (forall node, before = Some node -> node.(queueFields) = None) ->
  (forall node, next = Some node -> node.(queueFields) = None) ->
  after.(inUsedEventStates) = kernel_map_set events.(inUsedEventStates) eid next ->
  after.(publishedQueueBytes) = events.(publishedQueueBytes) ->
  (forall owner, queue_private_owner after owner = queue_private_owner events owner) ->
  queue_storage_rep sg events |-- queue_storage_rep sg after.
Proof.
  intros sg events after eid before next Hbefore HnoneBefore HnoneNext Hmap Hbytes Hprivate.
  assert (Hforward : forall owner node q,
    events.(inUsedEventStates) owner = Some node -> node.(queueFields) = Some q ->
    after.(inUsedEventStates) owner = Some node).
  { intros owner node q Hnode Hq; rewrite Hmap; unfold kernel_map_set.
    destruct (Z.eq_dec owner eid) as [->|Hne]; [|exact Hnode].
    exfalso; rewrite (HnoneBefore node ltac:(congruence)) in Hq; discriminate. }
  assert (Hback : forall owner node q,
    after.(inUsedEventStates) owner = Some node -> node.(queueFields) = Some q ->
    events.(inUsedEventStates) owner = Some node).
  { intros owner node q Hnode Hq; rewrite Hmap in Hnode; unfold kernel_map_set in Hnode.
    destruct (Z.eq_dec owner eid); [|exact Hnode].
    rewrite (HnoneNext node Hnode) in Hq; discriminate. }
  assert (Hpublished : forall qid,
    queue_slot_published after qid <-> queue_slot_published events qid).
  { intro qid; split; intros [owner [node [q [Hnode [Hq Hqid]]]]]; exists owner, node, q;
      split; [eapply Hback| |eapply Hforward|]; eauto. }
  assert (HprivateSlots : forall qid,
    queue_slot_private after qid <-> queue_slot_private events qid).
  { intro qid; unfold queue_slot_private; split; intros [owner Howner];
      exists owner; rewrite Hprivate in *; exact Howner. }
  assert (Hpred : published_queue_node_rep sg after = published_queue_node_rep sg events).
  { apply functional_extensionality; intro owner; apply functional_extensionality; intro node.
    unfold published_queue_node_rep; rewrite Hbytes; reflexivity. }
  assert (Hnodes : store_map (published_queue_node_rep sg events) events.(inUsedEventStates) |--
    store_map (published_queue_node_rep sg after) after.(inUsedEventStates)).
  { rewrite Hpred.
    assert (Hmissing : store_map (published_queue_node_rep sg events) events.(inUsedEventStates) |--
      store_map_missing_i (published_queue_node_rep sg events) events.(inUsedEventStates) eid).
    { destruct before as [node|].
      - assert (Hempty : published_queue_node_rep sg events eid node = emp).
        { unfold published_queue_node_rep; rewrite (HnoneBefore node eq_refl); reflexivity. }
        pose proof (store_map_split (published_queue_node_rep sg events) eid node _ Hbefore) as Hsplit.
        rewrite Hempty in Hsplit; eapply derivable1_trans; [exact Hsplit|]; entailer!.
      - apply store_map_equiv_store_map_missing; exact Hbefore. }
    eapply derivable1_trans; [exact Hmissing|].
    eapply derivable1_trans.
    - apply (proj1 (store_map_missing_i_equiv (published_queue_node_rep sg events)
        events.(inUsedEventStates) after.(inUsedEventStates) eid
        ltac:(intros owner Hne; rewrite Hmap; symmetry; apply kernel_map_set_other; exact Hne))).
    - assert (Hnext : after.(inUsedEventStates) eid = next).
      { rewrite Hmap; apply kernel_map_set_same. }
      destruct next as [node|].
      + assert (Hempty : published_queue_node_rep sg events eid node = emp).
        { unfold published_queue_node_rep; rewrite (HnoneNext node eq_refl); reflexivity. }
        pose proof (store_map_merge (published_queue_node_rep sg events) eid node
          after.(inUsedEventStates) Hnext) as Hmerge.
        rewrite Hempty in Hmerge.
        eapply derivable1_trans; [|exact Hmerge]; entailer!.
      + apply store_map_missing_equiv_store_map; exact Hnext. }
  unfold queue_storage_rep; Intros free.
  assert (Hbinding : queue_published_storage_binding after).
  { match goal with H : queue_published_storage_binding events |- _ =>
      destruct H as [Hentries [Hslots Hunique]] end.
    split.
    - intros owner node q Hnode Hq; rewrite Hbytes.
      exact (Hentries owner node q (Hback owner node q Hnode Hq) Hq).
    - split.
      + intros qid slots Hslot; rewrite Hbytes in Hslot.
        destruct (Hslots qid slots Hslot) as [owner [node [q [Hnode [Hq Hqid]]]]].
        exists owner, node, q; split; [eapply Hforward; eauto|auto].
      + intros first second e1 e2 q1 q2 H1 H2 HQ1 HQ2 Hqid.
        eapply Hunique; [eapply Hback; eauto|eapply Hback; eauto|exact HQ1|exact HQ2|exact Hqid]. }
  assert (Hpartition : queue_pool_partition sg after free).
  { match goal with H : queue_pool_partition sg events free |- _ =>
      destruct H as [Hfree [Hpart [Hdisjoint Hunique]]] end.
    split; [exact Hfree|]; split.
    - intro qid; rewrite Hpublished, HprivateSlots; exact (Hpart qid).
    - split.
      + intros qid Hpub Hpriv; apply (Hdisjoint qid); [apply Hpublished; exact Hpub|].
        apply HprivateSlots; exact Hpriv.
      + intros first second qid Hfirst Hsecond; rewrite Hprivate in Hfirst, Hsecond.
        eapply Hunique; eauto. }
  sep_apply_l_atomic Hnodes; entailer!; Exists free; entailer!.
Qed.

Lemma queue_event_publish_preserves_storage : forall sg events eid allocation node,
  events.(inUsedEventStates) eid = None ->
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None -> node.(queueFields) = None ->
  queue_storage_rep sg events |-- queue_storage_rep sg (event_publish events eid node).
Proof.
  intros sg events eid allocation node Hnone Hget Hprivate Hqueue.
  eapply queue_storage_event_entry_frame with (before := None) (next := Some node).
  - exact Hnone.
  - intros other Hother; discriminate.
  - intros other Hother; injection Hother as Hother; subst other; exact Hqueue.
  - reflexivity.
  - reflexivity.
  - intro owner; unfold queue_private_owner, event_publish; simpl; unfold kernel_map_set.
    destruct (Z.eq_dec owner eid) as [->|Hne]; [rewrite Hget; simpl; symmetry; exact Hprivate|reflexivity].
Qed.

Lemma queue_event_recycle_preserves_storage : forall sg events eid node image,
  events.(inUsedEventStates) eid = Some node -> node.(queueFields) = None ->
  queue_storage_rep sg events |--
    queue_storage_rep sg (event_recycle sg events eid image).
Proof.
  intros sg events eid node image Hnode Hnone.
  eapply queue_storage_event_entry_frame with (before := Some node) (next := None).
  - exact Hnode.
  - intros other Hother; injection Hother as Hother; subst other; exact Hnone.
  - intros other Hother; discriminate.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma queue_set_event_wait_list_preserves_storage : forall sg events eid e waiters,
  events.(inUsedEventStates) eid = Some e ->
  queue_storage_rep sg events |--
    queue_storage_rep sg (update_event_field_raw events eid (event_set_wait_list e waiters)).
Proof.
  intros; eapply queue_event_update_preserves_storage; [eassumption|reflexivity|reflexivity].
Qed.
