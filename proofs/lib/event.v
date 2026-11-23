Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SumLib.ZRange.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.event_pool.
Import UCOS2_C_Rules.
Import TaskStateDef.
Import EventStateDef.

Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Import ListNotations.
Local Open Scope list.
Local Open Scope sac_scope.

(* ================================================================== *)
(* Phase 5 Task 5.3:字段一致性谓词                                     *)
(* ================================================================== *)

Definition event_fields_consistency (e : OSEventAbstractState) : Prop :=
  match e.(eventType) with
  | OS_EVENT_TYPE_UNUSED =>
      e.(mutexFields) = None /\
      e.(semFields) = None /\
      e.(mboxFields) = None /\
      e.(queueFields) = None /\
      e.(waitList) = []
  | OS_EVENT_TYPE_MUTEX =>
      e.(mutexFields) <> None /\
      e.(semFields) = None /\
      e.(mboxFields) = None /\
      e.(queueFields) = None
  | OS_EVENT_TYPE_SEM =>
      e.(mutexFields) = None /\
      e.(semFields) <> None /\
      e.(mboxFields) = None /\
      e.(queueFields) = None
  | OS_EVENT_TYPE_MBOX =>
      e.(mutexFields) = None /\
      e.(semFields) = None /\
      e.(mboxFields) <> None /\
      e.(queueFields) = None
  | OS_EVENT_TYPE_Q =>
      e.(mutexFields) = None /\
      e.(semFields) = None /\
      e.(mboxFields) = None /\
      e.(queueFields) <> None
  | OS_EVENT_TYPE_FLAG =>
      False
  end.

Lemma non_queue_event_has_no_queue_fields : forall e,
  event_fields_consistency e -> e.(eventType) <> OS_EVENT_TYPE_Q -> e.(queueFields) = None.
Proof.
  intros e Hfields Htype; unfold event_fields_consistency in Hfields;
    destruct e.(eventType); intuition congruence.
Qed.

(** The saved low byte is the acquiring task's actual priority.  Its range
    includes OS_LOWEST_PRIO, just like native TCB priorities: OSMutexAccept
    does not contain an idle-priority rejection.  The application's task
    creation range [valid_task_prio] is deliberately not used for this C
    field.  The disabled-PCP byte is still not an owner-priority value. *)
Definition mutex_fields_consistency (sg : StableGlobVars) (m : MutexFields) : Prop :=
  match m.(mfOwner), m.(mfOwnerOrigPrio) with
  | None, None => True
  | Some _, Some op =>
      0 <= op /\ op <= sg.(osLowestPrio) /\ op <> sg.(osPrioMutexCeilDis)
  | _, _ => False
  end.

Definition sem_fields_consistency (wl : list TaskID) (s : SemFields) : Prop :=
  0 <= s.(semCount) <= 0xFFFF /\
  (wl <> [] -> s.(semCount) = 0).

Definition mbox_fields_consistency (wl : list TaskID) (m : MboxFields) : Prop :=
  (match m.(mboxMsg) with
   | None => True
   | Some p => p <> 0
   end) /\
  (wl <> [] -> m.(mboxMsg) = None).

Definition sizeof_ptr : Z := 4.

Definition queue_entries (q : QueueFields) : Z := Zlength q.(qMessages).

Definition queue_end_addr (q : QueueFields) : addr :=
  q.(qStart) + q.(qSize) * sizeof_ptr.

Definition queue_in_addr (q : QueueFields) : addr :=
  q.(qStart) + q.(qInIndex) * sizeof_ptr.

Definition queue_out_addr (q : QueueFields) : addr :=
  q.(qStart) + q.(qOutIndex) * sizeof_ptr.

Definition queue_fields_consistency (sg : StableGlobVars)
  (wl : list TaskID) (q : QueueFields) : Prop :=
  valid_queue_id sg q.(qID) /\
  0 < q.(qStart) /\
  0 <= q.(qSize) <= 0xFFFF /\
  ((q.(qSize) = 0 /\
    q.(qInIndex) = 0 /\
    q.(qOutIndex) = 0 /\
    q.(qMessages) = []) \/
   (0 < q.(qSize) /\
    0 <= q.(qInIndex) < q.(qSize) /\
    0 <= q.(qOutIndex) < q.(qSize) /\
    0 <= queue_entries q <= q.(qSize) /\
    q.(qInIndex) =
      Z.modulo (q.(qOutIndex) + queue_entries q) q.(qSize))) /\
  (wl <> [] -> q.(qMessages) = []).

(* Module-specific payload constraints for every in-use OS_EVENT. Event
   flags are deliberately absent: they use OS_FLAG_GRP, not OS_EVENT. *)
Definition event_payload_consistency (sg : StableGlobVars)
  (e : OSEventAbstractState) : Prop :=
  match e.(eventType) with
  | OS_EVENT_TYPE_UNUSED => False
  | OS_EVENT_TYPE_MUTEX =>
      match e.(mutexFields) with
      | Some m =>
          mutex_fields_consistency sg m /\
          (m.(mfOwner) = None -> e.(waitList) = [])
      | None => False
      end
  | OS_EVENT_TYPE_SEM =>
      match e.(semFields) with
      | Some s => sem_fields_consistency e.(waitList) s
      | None => False
      end
  | OS_EVENT_TYPE_MBOX =>
      match e.(mboxFields) with
      | Some m => mbox_fields_consistency e.(waitList) m
      | None => False
      end
  | OS_EVENT_TYPE_Q =>
      match e.(queueFields) with
      | Some q => queue_fields_consistency sg e.(waitList) q
      | None => False
      end
  | OS_EVENT_TYPE_FLAG => False
  end.

Definition event_queue_id (e : OSEventAbstractState) : option QueueID :=
  match e.(eventType), e.(queueFields) with
  | OS_EVENT_TYPE_Q, Some q => Some q.(qID)
  | _, _ => None
  end.

(* OSQCreate removes one OS_Q from OSQFreeList for each queue event.  Hence
   two live queue events cannot name the same OS_Q control block. *)
Definition queue_binding_unique
  (m : EventID -> option OSEventAbstractState) : Prop :=
  forall eid1 eid2 e1 e2 qid,
    m eid1 = Some e1 ->
    m eid2 = Some e2 ->
    event_queue_id e1 = Some qid ->
    event_queue_id e2 = Some qid ->
    eid1 = eid2.

(* ================================================================== *)
(* Phase 5 Task 5.4:verification_slice_event_in_range + 内存铺开                          *)
(* ================================================================== *)

(* Every configured OS_EVENT slot is represented exactly once: a [Some]
   entry is live and therefore absent from the free list, while a [None]
   entry is present in the free list.  Keeping the two directions named
   avoids silently weakening the public domain to live events only. *)
Definition event_slot_partition (sg : StableGlobVars)
  (gs : Glob_EventAbstractState) : Prop :=
  (forall eid,
      In eid gs.(unUsedEventStates) ->
      gs.(inUsedEventStates) eid = None) /\
  (forall eid,
      valid_event_id sg eid ->
      gs.(inUsedEventStates) eid = None ->
      In eid gs.(unUsedEventStates)).

Definition verification_slice_event_in_range (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState)
  (gs : Glob_EventAbstractState) : Prop :=
  (forall eid e, (gs.(inUsedEventStates)) eid = Some e ->
                0 <= eid /\ eid < sg.(osMaxEvents)) /\
  NoDup gs.(unUsedEventStates) /\
  Forall (fun eid => 0 <= eid /\ eid < sg.(osMaxEvents)) gs.(unUsedEventStates) /\
  event_slot_partition sg gs /\
  (forall eid e, (gs.(inUsedEventStates)) eid = Some e -> event_fields_consistency e) /\
  (forall eid e, (gs.(inUsedEventStates)) eid = Some e ->
                 event_payload_consistency sg e) /\
  queue_binding_unique gs.(inUsedEventStates) /\
  (forall eid e,
      (gs.(inUsedEventStates)) eid = Some e ->
      verification_slice_event_wait_entry_consistency sg tskSt eid e).

Lemma event_slot_partition_free_lookup :
  forall sg gs eid,
    event_slot_partition sg gs ->
    In eid gs.(unUsedEventStates) ->
    gs.(inUsedEventStates) eid = None.
Proof.
  intros sg gs eid Hpartition Hin.
  exact ((proj1 Hpartition) eid Hin).
Qed.

Lemma event_slot_partition_none_lookup :
  forall sg gs eid,
    event_slot_partition sg gs ->
    valid_event_id sg eid ->
    gs.(inUsedEventStates) eid = None ->
    In eid gs.(unUsedEventStates).
Proof.
  intros sg gs eid Hpartition Hvalid Hnone.
  exact ((proj2 Hpartition) eid Hvalid Hnone).
Qed.

Lemma event_slot_partition_used_not_free :
  forall sg gs eid e,
    event_slot_partition sg gs ->
    gs.(inUsedEventStates) eid = Some e ->
    ~ In eid gs.(unUsedEventStates).
Proof.
  intros sg gs eid e Hpartition Hused Hfree.
  pose proof (event_slot_partition_free_lookup
    sg gs eid Hpartition Hfree) as Hnone.
  rewrite Hused in Hnone. discriminate.
Qed.

Lemma event_slot_partition_valid_cases :
  forall sg gs eid,
    event_slot_partition sg gs ->
    valid_event_id sg eid ->
    (exists e, gs.(inUsedEventStates) eid = Some e) \/
    (gs.(inUsedEventStates) eid = None /\
     In eid gs.(unUsedEventStates)).
Proof.
  intros sg gs eid Hpartition Hvalid.
  destruct (gs.(inUsedEventStates) eid) as [e |] eqn:Hslot.
  - left. exists e. reflexivity.
  - right. split; [reflexivity |].
    eapply event_slot_partition_none_lookup; eauto.
Qed.

(* Stable in-place event updates keep the used/free partition when a live
   entry remains live.  Wait-list, owner, and payload-only updates all use
   this preservation shape. *)
Lemma event_slot_partition_preserved_some_to_some :
  forall sg gs mid old new,
    event_slot_partition sg gs ->
    gs.(inUsedEventStates) mid = Some old ->
    event_slot_partition sg
      {| inUsedEventStates := fun eid =>
           if Z.eqb eid mid then Some new
           else gs.(inUsedEventStates) eid;
         eventLifecycle := gs.(eventLifecycle);
         publishedQueueBytes := gs.(publishedQueueBytes);
         unUsedEventStates := gs.(unUsedEventStates) |}.
Proof.
  intros sg gs mid old new Hpartition Hmid.
  destruct Hpartition as [Hfree Hnone].
  split.
  - intros eid Hin. simpl.
    destruct (Z.eqb eid mid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst eid.
      specialize (Hfree mid Hin).
      rewrite Hmid in Hfree. discriminate.
    + apply Hfree. exact Hin.
  - intros eid Hvalid Hlookup. simpl in Hlookup.
    destruct (Z.eqb eid mid) eqn:Heq.
    + discriminate.
    + eapply Hnone; eauto.
Qed.

(* Allocation removes one known free node and publishes it as [Some]. *)
Lemma event_slot_partition_preserved_create :
  forall sg gs mid rest new,
    event_slot_partition sg gs ->
    gs.(unUsedEventStates) = mid :: rest ->
    ~ In mid rest ->
    event_slot_partition sg
      {| inUsedEventStates := fun eid =>
           if Z.eqb eid mid then Some new
           else gs.(inUsedEventStates) eid;
         eventLifecycle := gs.(eventLifecycle);
         publishedQueueBytes := gs.(publishedQueueBytes);
         unUsedEventStates := rest |}.
Proof.
  intros sg gs mid rest new Hpartition Hlist Hnotin.
  destruct Hpartition as [Hfree Hnone].
  split.
  - intros eid Hin. simpl.
    destruct (Z.eqb eid mid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst eid. contradiction.
    + apply Hfree. rewrite Hlist. simpl. right. exact Hin.
  - intros eid Hvalid Hlookup. simpl in Hlookup.
    destruct (Z.eqb eid mid) eqn:Heq.
    + discriminate.
    + assert (Hin : In eid (mid :: rest)).
      { rewrite <- Hlist. eapply Hnone; eauto. }
      simpl in Hin. destruct Hin as [Heq' | Hin].
      * subst eid. rewrite Z.eqb_refl in Heq. discriminate.
      * exact Hin.
Qed.

(* Deletion performs the inverse transition: one live slot becomes [None]
   and is linked at the front of the free list. *)
Lemma event_slot_partition_preserved_delete :
  forall sg gs mid old,
    event_slot_partition sg gs ->
    gs.(inUsedEventStates) mid = Some old ->
    event_slot_partition sg
      {| inUsedEventStates := fun eid =>
           if Z.eqb eid mid then None
           else gs.(inUsedEventStates) eid;
         eventLifecycle := gs.(eventLifecycle);
         publishedQueueBytes := gs.(publishedQueueBytes);
         unUsedEventStates := mid :: gs.(unUsedEventStates) |}.
Proof.
  intros sg gs mid old Hpartition Hmid.
  destruct Hpartition as [Hfree Hnone].
  split.
  - intros eid Hin. simpl in Hin |- *.
    destruct Hin as [Heq | Hin].
    + subst eid. rewrite Z.eqb_refl. reflexivity.
    + destruct (Z.eqb eid mid) eqn:Heq.
      * reflexivity.
      * apply Hfree. exact Hin.
  - intros eid Hvalid Hlookup. simpl in Hlookup |- *.
    destruct (Z.eqb eid mid) eqn:Heq.
    + left. symmetry. apply Z.eqb_eq. exact Heq.
    + right. eapply Hnone; eauto.
Qed.

(* A concrete all-free initializer witnesses that the strengthened partition
   and the complete event-range predicate are satisfiable for every profile. *)
Definition initial_event_abstract_state
  (sg : StableGlobVars) : Glob_EventAbstractState :=
  event_pool_initial sg.

Lemma verification_slice_initial_event_abstract_state_valid :
  forall sg tskSt,
    verification_slice_event_in_range sg tskSt (initial_event_abstract_state sg).
Proof.
  intros sg tskSt.
  unfold verification_slice_event_in_range, initial_event_abstract_state.
  simpl.
  refine (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ _))))))).
  - intros eid e Hused. discriminate.
  - apply NoDup_Zrange.
  - apply Forall_forall. intros eid Hin.
    exact ((proj2 (In_Zrange 0 (osMaxEvents sg) eid)) Hin).
  - unfold event_slot_partition. simpl. split.
    + intros eid Hin. reflexivity.
    + intros eid Hvalid Hnone.
      apply (proj1 (In_Zrange 0 (osMaxEvents sg) eid)).
      exact Hvalid.
  - intros eid e Hused. discriminate.
  - intros eid e Hused. discriminate.
  - unfold queue_binding_unique. intros eid1 eid2 e1 e2 qid Hused.
    discriminate.
  - intros eid e Hused. discriminate.
Qed.

(* Historical names-disabled size. Configured objects use event_object_size;
   OSEventName adds a four-byte pointer after this common prefix. *)
Definition sizeof_OS_EVENT : Z := 20.

Definition event_addr (sg : StableGlobVars) (eid : EventID) : addr :=
  event_pool_addr sg eid.

Lemma event_addr_shared_pool_binding : forall sg eid,
  event_addr sg eid = event_pool_addr sg eid.
Proof. reflexivity. Qed.

Lemma event_addr_injective : forall sg first second,
  event_addr sg first = event_addr sg second -> first = second.
Proof. intros; eapply event_pool_addr_injective; exact H. Qed.

(* 32-bit OS_Q layout: five pointers followed by two INT16U fields. *)
Definition sizeof_OS_Q : Z := 24.

Definition qcb_addr (sg : StableGlobVars) (qid : QueueID) : addr :=
  sg.(g_OSQTbl) + qid * sizeof_OS_Q.

Definition encode_event_type (ty : OSEventType) : Z :=
  match ty with
  | OS_EVENT_TYPE_UNUSED => 0
  | OS_EVENT_TYPE_MBOX   => 1
  | OS_EVENT_TYPE_Q      => 2
  | OS_EVENT_TYPE_SEM    => 3
  | OS_EVENT_TYPE_MUTEX  => 4
  | OS_EVENT_TYPE_FLAG   => 5
  end.

Definition verification_slice_encode_event_ptr_value (sg : StableGlobVars)
  (e : OSEventAbstractState) : Z :=
  match e.(eventType) with
  | OS_EVENT_TYPE_MUTEX =>
      match e.(mutexFields) with
      | Some m =>
          match m.(mfOwner) with
          | None => 0
          | Some tid => verification_slice_tcb_addr sg tid
          end
      | None => 0
      end
  | OS_EVENT_TYPE_MBOX =>
      match e.(mboxFields) with
      | Some m =>
          match m.(mboxMsg) with
          | None => 0
          | Some p => p
          end
      | None => 0
      end
  | OS_EVENT_TYPE_Q =>
      match e.(queueFields) with
      | Some q => qcb_addr sg q.(qID)
      | None => 0
      end
  | OS_EVENT_TYPE_UNUSED
  | OS_EVENT_TYPE_SEM
  | OS_EVENT_TYPE_FLAG => 0
  end.

Definition encode_event_cnt_value (e : OSEventAbstractState) : Z :=
  match e.(eventType), e.(mutexFields), e.(semFields) with
  | OS_EVENT_TYPE_MUTEX, Some m, _ =>
      match m.(mfOwner), m.(mfOwnerOrigPrio) with
      | None, None => (m.(mfPCP) * 256) + 0xFF
      | Some _, Some op => (m.(mfPCP) * 256) + op
      | _, _ => 0
      end
  | OS_EVENT_TYPE_SEM, _, Some s => s.(semCount)
  | _, _, _ => 0
  end.

(* OS_EVENT 字段偏移量 *)
Definition OSEventType_off : Z := 0.
Definition OSEventPtr_off  : Z := 4.
Definition OSEventCnt_off  : Z := 8.
Definition OSEventGrp_off  : Z := 10.
Definition OSEventTbl_off : Z := 11.

(* ================================================================== *)
(* L1: OS_EVENT representation bridges                                  *)
(* ================================================================== *)

(* QCP's C front end keeps struct-field addresses opaque, whereas the
   historical event representation below is written with base + offset.
   Keep the bridge at the event representation layer so every OS_EVENT
   client can share it; it is not a mutex-accept branch assumption. *)
Definition event_core_fields_layout_prop
  (sg : StableGlobVars) (eid : EventID)
  (type_addr ptr_addr cnt_addr : addr) : Prop :=
  type_addr = event_addr sg eid + OSEventType_off /\
  ptr_addr = event_addr sg eid + OSEventPtr_off /\
  cnt_addr = event_addr sg eid + OSEventCnt_off.

(* Shared layout bridge for the wait bitmap portion of OS_EVENT.  Query,
   Pend, Post and Delete all observe or update these same fields, so this
   representation fact belongs to the event module rather than a case lib. *)
Definition event_wait_fields_layout_prop
  (sg : StableGlobVars) (eid : EventID)
  (grp_addr tbl_addr : addr) : Prop :=
  grp_addr = event_addr sg eid + OSEventGrp_off /\
  tbl_addr = event_addr sg eid + OSEventTbl_off.

(* The front end intentionally keeps C field addresses opaque.  The compiled
   ABI is therefore an explicit public representation premise, written in the
   exact QCP arrow-field vocabulary used by generated C lvalues, rather than a
   consequence of stable global-variable validity. *)
Definition event_object_layout_prop
  (sg : StableGlobVars) (eid : EventID) : Prop :=
  event_core_fields_layout_prop sg eid
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventType"))
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventPtr"))
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventCnt")) /\
  event_wait_fields_layout_prop sg eid
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp"))
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventTbl")).

Definition event_table_layout_prop (sg : StableGlobVars) : Prop :=
  forall eid, valid_event_id sg eid -> event_object_layout_prop sg eid.

Lemma event_table_layout_select :
  forall sg eid,
    event_table_layout_prop sg ->
    valid_event_id sg eid ->
    event_object_layout_prop sg eid.
Proof.
  intros sg eid Htable Hvalid.
  exact (Htable eid Hvalid).
Qed.

Lemma event_object_layout_core_proj :
  forall sg eid,
    event_object_layout_prop sg eid ->
    event_core_fields_layout_prop sg eid
      (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventType"))
      (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventPtr"))
      (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventCnt")).
Proof.
  intros sg eid Hlayout.
  exact (proj1 Hlayout).
Qed.

Lemma event_object_layout_wait_proj :
  forall sg eid,
    event_object_layout_prop sg eid ->
    event_wait_fields_layout_prop sg eid
      (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp"))
      (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventTbl")).
Proof.
  intros sg eid Hlayout.
  exact (proj2 Hlayout).
Qed.

(* Typed-cell fact for an INT16U/unsigned-short event count.  This predicate
   deliberately records only representation range; mutex availability,
   ownership and PCP constraints belong to the mutex protocol layer. *)
Definition event_count_value_range_prop (cnt : Z) : Prop :=
  0 <= cnt <= 65535.

Definition OSQPtr_off     : Z := 0.
Definition OSQStart_off   : Z := 4.
Definition OSQEnd_off     : Z := 8.
Definition OSQIn_off      : Z := 12.
Definition OSQOut_off     : Z := 16.
Definition OSQSize_off    : Z := 20.
Definition OSQEntries_off : Z := 22.

Definition queue_control_block_snapshot_prop (sg : StableGlobVars)
  (q : QueueFields) (base start finish qin qout size entries : Z) : Prop :=
  base = qcb_addr sg q.(qID) /\
  start = q.(qStart) /\
  finish = queue_end_addr q /\
  qin = queue_in_addr q /\
  qout = queue_out_addr q /\
  size = q.(qSize) /\
  entries = queue_entries q.

(* OSQPtr is a free-list link and has no live-queue meaning after allocation. *)
Definition used_queue_control_block (sg : StableGlobVars)
  (q : QueueFields) : Assertion :=
  (qcb_addr sg q.(qID) + OSQPtr_off) # Ptr |->_ **
  (qcb_addr sg q.(qID) + OSQStart_off) # Ptr |-> q.(qStart) **
  (qcb_addr sg q.(qID) + OSQEnd_off) # Ptr |-> queue_end_addr q **
  (qcb_addr sg q.(qID) + OSQIn_off) # Ptr |-> queue_in_addr q **
  (qcb_addr sg q.(qID) + OSQOut_off) # Ptr |-> queue_out_addr q **
  (qcb_addr sg q.(qID) + OSQSize_off) # UShort |-> q.(qSize) **
  (qcb_addr sg q.(qID) + OSQEntries_off) # UShort |-> queue_entries q.

Fixpoint encode_event_wait_grp (wl : list TaskID)
  (tskSt : Glob_TaskAbstractState) : Z :=
  match wl with
  | [] => 0
  | tid :: rest =>
      match tskSt.(inUsedTaskStates) tid with
      | Some t => Z.lor (Z.shiftl 1 (t.(curPrio) / 8))
                        (encode_event_wait_grp rest tskSt)
      | None => encode_event_wait_grp rest tskSt
      end
  end.

Definition encode_event_wait_tbl_at (wl : list TaskID)
  (tskSt : Glob_TaskAbstractState) (y : Z) : Z :=
  fold_left (fun acc tid =>
    match tskSt.(inUsedTaskStates) tid with
    | Some t => if Z.eqb (t.(curPrio) / 8) y
                then acc + Z.shiftl 1 (t.(curPrio) mod 8)
                else acc
    | None => acc
  end) wl 0.

(* Source-total counterpart of the stable additive table encoder. *)
Definition encode_event_wait_tbl_at_or (wl : list TaskID)
  (tskSt : Glob_TaskAbstractState) (y : Z) : Z :=
  fold_right
    (fun tid acc =>
       match tskSt.(inUsedTaskStates) tid with
       | Some t =>
           if Z.eqb (t.(curPrio) / 8) y
           then Z.lor (Z.shiftl 1 (t.(curPrio) mod 8)) acc
           else acc
       | None => acc
       end)
    0 wl.

Lemma encode_event_wait_tbl_at_eq_or :
  forall wl tskSt y,
    NoDup wl ->
    task_priority_unique tskSt ->
    (forall tid t,
       In tid wl ->
       tskSt.(inUsedTaskStates) tid = Some t ->
       0 <= t.(curPrio)) ->
    encode_event_wait_tbl_at wl tskSt y =
    encode_event_wait_tbl_at_or wl tskSt y.
Proof.
  intros wl tskSt y Hnodup Hunique Hrange.
  change
    (encode_ready_tbl_at wl tskSt y =
     encode_ready_tbl_at_or wl tskSt y).
  apply encode_ready_tbl_at_eq_or; assumption.
Qed.

Definition encode_event_wait_tbl_values (e : OSEventAbstractState)
  (tskSt : Glob_TaskAbstractState) : list Z :=
  [ encode_event_wait_tbl_at e.(waitList) tskSt 0;
    encode_event_wait_tbl_at e.(waitList) tskSt 1;
    encode_event_wait_tbl_at e.(waitList) tskSt 2;
    encode_event_wait_tbl_at e.(waitList) tskSt 3;
    encode_event_wait_tbl_at e.(waitList) tskSt 4;
    encode_event_wait_tbl_at e.(waitList) tskSt 5;
    encode_event_wait_tbl_at e.(waitList) tskSt 6;
    encode_event_wait_tbl_at e.(waitList) tskSt 7 ].

Definition encode_event_wait_tbl_values_or (e : OSEventAbstractState)
  (tskSt : Glob_TaskAbstractState) : list Z :=
  [ encode_event_wait_tbl_at_or e.(waitList) tskSt 0;
    encode_event_wait_tbl_at_or e.(waitList) tskSt 1;
    encode_event_wait_tbl_at_or e.(waitList) tskSt 2;
    encode_event_wait_tbl_at_or e.(waitList) tskSt 3;
    encode_event_wait_tbl_at_or e.(waitList) tskSt 4;
    encode_event_wait_tbl_at_or e.(waitList) tskSt 5;
    encode_event_wait_tbl_at_or e.(waitList) tskSt 6;
    encode_event_wait_tbl_at_or e.(waitList) tskSt 7 ].

Definition event_snapshot_of_prop (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (evSt : Glob_EventAbstractState)
  (eid : EventID) (e : OSEventAbstractState)
  (etype ecnt eptr egrp : Z) (etbl : list Z) : Prop :=
    evSt.(inUsedEventStates) eid = Some e /\
    etype = encode_event_type e.(eventType) /\
    ecnt = encode_event_cnt_value e /\
    eptr = verification_slice_encode_event_ptr_value sg e /\
    egrp = encode_event_wait_grp e.(waitList) tskSt /\
    etbl = encode_event_wait_tbl_values e tskSt.

(* Source-total pure view of one used event.  Unlike the stable snapshot
   above, its selected wait-table bytes use the same OR encoder as
   [used_complete_event_raw]. *)
Definition event_raw_snapshot_of_prop (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (evSt : Glob_EventAbstractState)
  (eid : EventID) (e : OSEventAbstractState)
  (etype ecnt eptr egrp : Z) (etbl : list Z) : Prop :=
    evSt.(inUsedEventStates) eid = Some e /\
    etype = encode_event_type e.(eventType) /\
    ecnt = encode_event_cnt_value e /\
    eptr = verification_slice_encode_event_ptr_value sg e /\
    egrp = encode_event_wait_grp e.(waitList) tskSt /\
    etbl = encode_event_wait_tbl_values_or e tskSt.

Lemma encode_event_wait_tbl_values_stable_eq_raw :
  forall sg tskSt e,
    event_waitList_canonical sg tskSt e.(waitList) ->
    task_priority_unique tskSt ->
    encode_event_wait_tbl_values e tskSt =
    encode_event_wait_tbl_values_or e tskSt.
Proof.
  intros sg tskSt e Hcanonical Hunique.
  unfold event_waitList_canonical in Hcanonical.
  destruct Hcanonical as [Hnodup [_ Hrange]].
  assert (Heq : forall y,
    encode_event_wait_tbl_at e.(waitList) tskSt y =
    encode_event_wait_tbl_at_or e.(waitList) tskSt y).
  {
    intro y.
    apply encode_event_wait_tbl_at_eq_or; try assumption.
    intros tid t Hin Hlookup.
    destruct (Hrange tid Hin) as [t0 [Hlookup0 [Hnonneg _]]].
    rewrite Hlookup in Hlookup0.
    inversion Hlookup0; subst t0.
    exact Hnonneg.
  }
  unfold encode_event_wait_tbl_values,
    encode_event_wait_tbl_values_or.
  rewrite (Heq 0), (Heq 1), (Heq 2), (Heq 3),
    (Heq 4), (Heq 5), (Heq 6), (Heq 7).
  reflexivity.
Qed.

(* The raw/canonical conversion is deliberately conditional.  Literal
   source-total transient states need not satisfy either premise. *)
Lemma event_snapshot_of_prop_stable_iff_raw :
  forall sg tskSt evSt eid e etype ecnt eptr egrp etbl,
    event_waitList_canonical sg tskSt e.(waitList) ->
    task_priority_unique tskSt ->
    (event_snapshot_of_prop
       sg tskSt evSt eid e etype ecnt eptr egrp etbl <->
     event_raw_snapshot_of_prop
       sg tskSt evSt eid e etype ecnt eptr egrp etbl).
Proof.
  intros sg tskSt evSt eid e etype ecnt eptr egrp etbl
    Hcanonical Hunique.
  assert (Htbl :
    encode_event_wait_tbl_values e tskSt =
    encode_event_wait_tbl_values_or e tskSt).
  {
    apply (encode_event_wait_tbl_values_stable_eq_raw sg tskSt e);
      assumption.
  }
  unfold event_snapshot_of_prop, event_raw_snapshot_of_prop.
  split; intros Hsnapshot.
  - destruct Hsnapshot as
      [Hused [Htype [Hcnt [Hptr [Hgrp Hvalues]]]]].
    repeat split; try assumption.
    rewrite Hvalues.
    exact Htbl.
  - destruct Hsnapshot as
      [Hused [Htype [Hcnt [Hptr [Hgrp Hvalues]]]]].
    repeat split; try assumption.
    rewrite Hvalues.
    symmetry.
    exact Htbl.
Qed.

Definition event_snapshot_prop (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (evSt : Glob_EventAbstractState)
  (eid : EventID) (etype ecnt eptr egrp : Z) (etbl : list Z) : Prop :=
  exists e,
  event_snapshot_of_prop sg tskSt evSt eid e
    etype ecnt eptr egrp etbl.

(* Focused snapshot used when OSMutexPend relocates a blocked owner's
   priority in another event's wait bitmap. *)
Definition event_wait_snapshot_of_prop (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (evSt : Glob_EventAbstractState)
  (eid : EventID) (e : OSEventAbstractState)
  (event_base egrp : Z) (etbl : list Z) : Prop :=
  evSt.(inUsedEventStates) eid = Some e /\
  event_base = event_addr sg eid /\
  egrp = encode_event_wait_grp e.(waitList) tskSt /\
  etbl = encode_event_wait_tbl_values e tskSt.

Definition used_complete_event (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (ctrl_start : addr)
  (eid : EventID) (e : OSEventAbstractState) : Assertion :=
  (ctrl_start + OSEventType_off) # UChar |-> encode_event_type e.(eventType) **
  (ctrl_start + OSEventPtr_off)  # Ptr |->
    verification_slice_encode_event_ptr_value sg e **
  (ctrl_start + OSEventCnt_off)  # UShort |->
    encode_event_cnt_value e **
  (ctrl_start + OSEventGrp_off)  # UChar |->
    encode_event_wait_grp e.(waitList) tskSt **
  (ctrl_start + OSEventTbl_off + 0) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 0 **
  (ctrl_start + OSEventTbl_off + 1) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 1 **
  (ctrl_start + OSEventTbl_off + 2) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 2 **
  (ctrl_start + OSEventTbl_off + 3) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 3 **
  (ctrl_start + OSEventTbl_off + 4) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 4 **
  (ctrl_start + OSEventTbl_off + 5) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 5 **
  (ctrl_start + OSEventTbl_off + 6) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 6 **
  (ctrl_start + OSEventTbl_off + 7) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 7.

(* Source-total used-event record.  The non-bitmap fields keep their exact
   abstract encodings; both wait bitmap dimensions use OR. *)
Definition used_complete_event_raw (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (ctrl_start : addr)
  (eid : EventID) (e : OSEventAbstractState) : Assertion :=
  (ctrl_start + OSEventType_off) # UChar |-> encode_event_type e.(eventType) **
  (ctrl_start + OSEventPtr_off) # Ptr |-> verification_slice_encode_event_ptr_value sg e **
  (ctrl_start + OSEventCnt_off) # UShort |-> encode_event_cnt_value e **
  (ctrl_start + OSEventGrp_off) # UChar |->
    encode_event_wait_grp e.(waitList) tskSt **
  (ctrl_start + OSEventTbl_off + 0) # UChar |->
    encode_event_wait_tbl_at_or e.(waitList) tskSt 0 **
  (ctrl_start + OSEventTbl_off + 1) # UChar |->
    encode_event_wait_tbl_at_or e.(waitList) tskSt 1 **
  (ctrl_start + OSEventTbl_off + 2) # UChar |->
    encode_event_wait_tbl_at_or e.(waitList) tskSt 2 **
  (ctrl_start + OSEventTbl_off + 3) # UChar |->
    encode_event_wait_tbl_at_or e.(waitList) tskSt 3 **
  (ctrl_start + OSEventTbl_off + 4) # UChar |->
    encode_event_wait_tbl_at_or e.(waitList) tskSt 4 **
  (ctrl_start + OSEventTbl_off + 5) # UChar |->
    encode_event_wait_tbl_at_or e.(waitList) tskSt 5 **
  (ctrl_start + OSEventTbl_off + 6) # UChar |->
    encode_event_wait_tbl_at_or e.(waitList) tskSt 6 **
  (ctrl_start + OSEventTbl_off + 7) # UChar |->
    encode_event_wait_tbl_at_or e.(waitList) tskSt 7.

Lemma used_complete_event_stable_eq_raw :
  forall sg tskSt base eid e,
    event_waitList_canonical sg tskSt e.(waitList) ->
    task_priority_unique tskSt ->
    used_complete_event sg tskSt base eid e =
    used_complete_event_raw sg tskSt base eid e.
Proof.
  intros sg tskSt base eid e Hcanonical Hunique.
  unfold event_waitList_canonical in Hcanonical.
  destruct Hcanonical as [Hnodup [_ Hrange]].
  assert (Heq : forall y,
    encode_event_wait_tbl_at e.(waitList) tskSt y =
    encode_event_wait_tbl_at_or e.(waitList) tskSt y).
  {
    intro y.
    apply encode_event_wait_tbl_at_eq_or; try assumption.
    intros tid t Hin Hlookup.
    destruct (Hrange tid Hin) as [t0 [Hlookup0 [Hnonneg _]]].
    rewrite Hlookup in Hlookup0.
    inversion Hlookup0; subst t0.
    exact Hnonneg.
  }
  unfold used_complete_event, used_complete_event_raw.
  rewrite (Heq 0), (Heq 1), (Heq 2), (Heq 3),
    (Heq 4), (Heq 5), (Heq 6), (Heq 7).
  reflexivity.
Qed.

(* Exact residual after exposing only [OSEventType].  In particular, this
   keeps OSEventPtr, OSEventCnt and the complete wait bitmap owned; clients
   may inspect the public discriminator before learning mutex-specific
   owner/PCP facts. *)
Definition used_event_rest_no_type (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (ctrl_start : addr)
  (eid : EventID) (e : OSEventAbstractState) : Assertion :=
  (ctrl_start + OSEventPtr_off) # Ptr |->
    verification_slice_encode_event_ptr_value sg e **
  (ctrl_start + OSEventCnt_off) # UShort |->
    encode_event_cnt_value e **
  (ctrl_start + OSEventGrp_off) # UChar |->
    encode_event_wait_grp e.(waitList) tskSt **
  (ctrl_start + OSEventTbl_off + 0) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 0 **
  (ctrl_start + OSEventTbl_off + 1) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 1 **
  (ctrl_start + OSEventTbl_off + 2) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 2 **
  (ctrl_start + OSEventTbl_off + 3) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 3 **
  (ctrl_start + OSEventTbl_off + 4) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 4 **
  (ctrl_start + OSEventTbl_off + 5) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 5 **
  (ctrl_start + OSEventTbl_off + 6) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 6 **
  (ctrl_start + OSEventTbl_off + 7) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 7.

Lemma used_complete_event_split_type :
  forall sg tskSt base eid e,
    used_complete_event sg tskSt base eid e |--
      (base + OSEventType_off) # UChar |->
        encode_event_type e.(eventType) **
      used_event_rest_no_type sg tskSt base eid e.
Proof.
  intros. unfold used_complete_event, used_event_rest_no_type.
  entailer!.
Qed.

Lemma used_complete_event_merge_type :
  forall sg tskSt base eid e,
    (base + OSEventType_off) # UChar |->
      encode_event_type e.(eventType) **
    used_event_rest_no_type sg tskSt base eid e |--
      used_complete_event sg tskSt base eid e.
Proof.
  intros. unfold used_complete_event, used_event_rest_no_type.
  entailer!.
Qed.

(* Historical verification-slice ownership of exactly the Type, Ptr and Cnt
   typed cells, not a complete non-wait residual. Name and padding belong
   to the complete current Event representation. *)
Definition verification_slice_event_type_ptr_cnt_rep (sg : StableGlobVars)
  (ctrl_start : addr) (e : OSEventAbstractState) : Assertion :=
  (ctrl_start + OSEventType_off) # UChar |-> encode_event_type e.(eventType) **
  (ctrl_start + OSEventPtr_off) # Ptr |-> verification_slice_encode_event_ptr_value sg e **
  (ctrl_start + OSEventCnt_off) # UShort |-> encode_event_cnt_value e.

Definition used_event_rest_no_type_cnt_ptr (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (ctrl_start : addr)
  (eid : EventID) (e : OSEventAbstractState) : Assertion :=
  (ctrl_start + OSEventGrp_off) # UChar |->
    encode_event_wait_grp e.(waitList) tskSt **
  (ctrl_start + OSEventTbl_off + 0) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 0 **
  (ctrl_start + OSEventTbl_off + 1) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 1 **
  (ctrl_start + OSEventTbl_off + 2) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 2 **
  (ctrl_start + OSEventTbl_off + 3) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 3 **
  (ctrl_start + OSEventTbl_off + 4) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 4 **
  (ctrl_start + OSEventTbl_off + 5) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 5 **
  (ctrl_start + OSEventTbl_off + 6) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 6 **
  (ctrl_start + OSEventTbl_off + 7) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 7.

Definition used_event_wait_table_storage
  (tskSt : Glob_TaskAbstractState) (ctrl_start : addr)
  (e : OSEventAbstractState) : Assertion :=
  (ctrl_start + OSEventTbl_off + 0) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 0 **
  (ctrl_start + OSEventTbl_off + 1) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 1 **
  (ctrl_start + OSEventTbl_off + 2) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 2 **
  (ctrl_start + OSEventTbl_off + 3) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 3 **
  (ctrl_start + OSEventTbl_off + 4) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 4 **
  (ctrl_start + OSEventTbl_off + 5) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 5 **
  (ctrl_start + OSEventTbl_off + 6) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 6 **
  (ctrl_start + OSEventTbl_off + 7) # UChar |->
    encode_event_wait_tbl_at e.(waitList) tskSt 7.

Lemma queue_binding_unique_update_same_binding :
  forall m mid e_old e_new,
    m mid = Some e_old ->
    event_queue_id e_new = event_queue_id e_old ->
    queue_binding_unique m ->
    queue_binding_unique
      (fun eid => if Z.eqb eid mid then Some e_new else m eid).
Proof.
  intros m mid e_old e_new Hget Hbinding Hunique.
  unfold queue_binding_unique in *.
  intros eid1 eid2 e1 e2 qid Hget1 Hget2 Hqid1 Hqid2.
  destruct (Z.eqb eid1 mid) eqn:Heq1;
    destruct (Z.eqb eid2 mid) eqn:Heq2.
  - apply Z.eqb_eq in Heq1. apply Z.eqb_eq in Heq2. congruence.
  - apply Z.eqb_eq in Heq1. subst eid1.
    simpl in Hget1, Hget2.
    injection Hget1 as ->.
    eapply Hunique.
    + exact Hget.
    + exact Hget2.
    + rewrite <- Hbinding. exact Hqid1.
    + exact Hqid2.
  - apply Z.eqb_eq in Heq2. subst eid2.
    simpl in Hget1, Hget2.
    injection Hget2 as ->.
    eapply Hunique.
    + exact Hget1.
    + exact Hget.
    + exact Hqid1.
    + rewrite <- Hbinding. exact Hqid2.
  - simpl in Hget1, Hget2.
    eapply Hunique; eassumption.
Qed.

(* verification_slice_event_in_range 在 TskState 单 task 更新(event-relevant 字段保持)时保持 *)
(* t' 保持 curPrio/eventPtr/eventMultiWaitEvents/stat,仅改 statPend/dly 等 event 不关心字段 *)
(* 用于 atomic_mutex_pend_timeout_mark_preserves_inv 的 verification_slice_event_in_range 子目标 *)
Lemma verification_slice_event_in_range_preserved_by_tskSt_nonEventFields_update :
  forall sg tskSt1 tskSt2 evSt cur_tid t t',
    tskSt1.(inUsedTaskStates) cur_tid = Some t ->
    t'.(curPrio) = t.(curPrio) ->
    t'.(eventPtr) = t.(eventPtr) ->
    t'.(eventMultiWaitEvents) = t.(eventMultiWaitEvents) ->
    t'.(stat) = t.(stat) ->
    tskSt2 = {| inUsedTaskStates := fun tid =>
                  if Z.eqb tid cur_tid then Some t'
                  else tskSt1.(inUsedTaskStates) tid;
                unUsedTaskStates := tskSt1.(unUsedTaskStates);
                tcbListHead      := tskSt1.(tcbListHead);
                prioTbl          := tskSt1.(prioTbl);
                taskRegNextID := tskSt1.(taskRegNextID);
                parkedTaskStacks := tskSt1.(parkedTaskStacks);
                taskLifecycle := tskSt1.(taskLifecycle);
     taskCount        := tskSt1.(taskCount); |} ->
    verification_slice_event_in_range sg tskSt1 evSt ->
    verification_slice_event_in_range sg tskSt2 evSt.
Proof.
  intros sg tskSt1 tskSt2 evSt cur_tid t t'
    Hget Hcp' Hep' Hemp' Hstat' HtskSt2
    [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]].
  subst tskSt2.
  split.
  - exact H1.
  - split.
    + exact H2.
    + split.
      * exact H3.
      * split.
        -- exact H4.
        -- split.
           ++ exact H5.
           ++ split.
              ** exact H6.
              ** split; [exact H7 |].
                 intros eid e Hget_e.
                 destruct (H8 eid e Hget_e) as [Hwlc Hwec].
                 unfold verification_slice_event_wait_entry_consistency in *.
                 split.
                 --- (* event_waitList_canonical sg {|...|} e.(waitList) *)
                     unfold event_waitList_canonical in *.
                     destruct Hwlc as [Hnd [Hss Hforall]].
                     split.
                     +++ exact Hnd.
                     +++ split.
                         **** (* strictly_sorted_by ... *)
                         assert (Hext : forall x, wait_prio_key sg tskSt1 x = wait_prio_key sg
                           {| inUsedTaskStates := fun tid => if Z.eqb tid cur_tid then Some t' else tskSt1.(inUsedTaskStates) tid;
                              unUsedTaskStates := tskSt1.(unUsedTaskStates);
                              tcbListHead := tskSt1.(tcbListHead);
                              prioTbl := tskSt1.(prioTbl);
                              taskRegNextID := tskSt1.(taskRegNextID);
                              parkedTaskStacks := tskSt1.(parkedTaskStacks);
                              taskLifecycle := tskSt1.(taskLifecycle);
     taskCount := tskSt1.(taskCount); |} x).
                         { intros x. unfold wait_prio_key.
                           destruct (Z.eqb x cur_tid) eqn:Heq_x.
                           -- apply Z.eqb_eq in Heq_x. subst x.
                              simpl. rewrite Hget. rewrite Z.eqb_refl. simpl. rewrite Hcp'. reflexivity.
                           -- simpl. rewrite Heq_x. simpl. reflexivity. }
                         exact (strictly_sorted_by_key_ext _ _ _ _ Hext Hss).
                         **** (* forall tid, In tid (waitList e) -> exists t, ... *)
                         intros tid_in Hin.
                         destruct (Hforall tid_in Hin) as [t0 [Hget0 Hvtp]].
                         destruct (Z.eqb tid_in cur_tid) eqn:Heq_tin.
                         { apply Z.eqb_eq in Heq_tin. subst tid_in.
                           rewrite Hget in Hget0. inversion Hget0. subst t0.
                           exists t'. split.
                           - simpl. rewrite Z.eqb_refl. reflexivity.
                           - unfold valid_task_prio. rewrite Hcp'. exact Hvtp. }
                         { exists t0. split.
                           - simpl. rewrite Heq_tin. exact Hget0.
                           - exact Hvtp. }
                 --- (* match event_type_to_pend_type ... *)
                     destruct (event_type_to_pend_type e.(eventType)) eqn:Hety.
                     +++ (* Some pty *)
                         simpl in Hwec.
                         intros tid_in Hin.
                         destruct (Hwec _ Hin) as [t0 [Hget0 [Hep0 [Hemp0 Hpnd0]]]].
                         destruct (Z.eqb tid_in cur_tid) eqn:Heq_tin.
                         { apply Z.eqb_eq in Heq_tin. subst tid_in.
                           rewrite Hget in Hget0. inversion Hget0. subst t0.
                           exists t'. split.
                           - simpl. rewrite Z.eqb_refl. reflexivity.
                           - split.
                             + rewrite Hep'. exact Hep0.
                             + split.
                               * rewrite Hemp'. exact Hemp0.
                               * rewrite Hstat'. exact Hpnd0. }
                         { exists t0. split.
                           - simpl. rewrite Heq_tin. exact Hget0.
                           - split.
                             + exact Hep0.
                             + split.
                               * exact Hemp0.
                               * exact Hpnd0. }
                     +++ (* None *)
                         simpl in Hwec.
                         exact Hwec.
Qed.

(* update_event_field_raw:更新 EventState 中某个 eid *)
Definition update_event_field_raw (evSt : Glob_EventAbstractState)
  (eid : EventID) (e : OSEventAbstractState) : Glob_EventAbstractState :=
  {| inUsedEventStates :=
       fun eid' => if Z.eqb eid' eid then Some e
                   else evSt.(inUsedEventStates) eid';
     eventLifecycle := evSt.(eventLifecycle);
     publishedQueueBytes := evSt.(publishedQueueBytes);
     unUsedEventStates := evSt.(unUsedEventStates);
  |}.

Definition update_event_field (lvs : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState) : UCOS2_Verify_State :=
  replace_EventS (update_event_field_raw lvs.(EventState) eid e) lvs.

Lemma event_payload_consistency_remove_waiter :
  forall sg e tid,
    In tid e.(waitList) ->
    event_payload_consistency sg e ->
    event_payload_consistency sg
      {| eventGeneration := e.(eventGeneration);
         eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19);
         eventType   := e.(eventType);
         mutexFields := e.(mutexFields);
         semFields   := e.(semFields);
         mboxFields  := e.(mboxFields);
         queueFields := e.(queueFields);
         waitList    := remove_Z_eqb tid e.(waitList); |}.
Proof.
  intros sg e tid Hin Hpayload.
  assert (Hnonempty : e.(waitList) <> []).
  { intro Hnil. rewrite Hnil in Hin. inversion Hin. }
  unfold event_payload_consistency in *.
  destruct e.(eventType); simpl in *.
  - contradiction.
  - destruct e.(semFields) as [s |]; [| contradiction].
    unfold sem_fields_consistency in *. destruct Hpayload as [Hrange Hwait].
    split; [exact Hrange |]. intros _. exact (Hwait Hnonempty).
  - destruct e.(mutexFields) as [m |]; [| contradiction].
    destruct Hpayload as [Hm Hfree]. split; [exact Hm |].
    intro Howner. exfalso. apply Hnonempty. exact (Hfree Howner).
  - destruct e.(mboxFields) as [m |]; [| contradiction].
    unfold mbox_fields_consistency in *. destruct Hpayload as [Hmsg Hwait].
    split; [exact Hmsg |]. intros _. exact (Hwait Hnonempty).
  - destruct e.(queueFields) as [q |]; [| contradiction].
    unfold queue_fields_consistency in *.
    destruct Hpayload as [Hqid [Hstart [Hsize [Hshape Hwait]]]].
    split; [exact Hqid |].
    split; [exact Hstart |].
    split; [exact Hsize |].
    split; [exact Hshape |].
    intros _. exact (Hwait Hnonempty).
  - contradiction.
Qed.

Lemma verification_slice_event_in_range_preserved_by_eventTaskRemove :
  forall sg tskSt1 tskSt2 evSt1 evSt2 cur_tid mid e1 e2 t t',
    tskSt1.(inUsedTaskStates) cur_tid = Some t ->
    t'.(curPrio) = t.(curPrio) ->
    tskSt2 = {| inUsedTaskStates := fun tid =>
                  if Z.eqb tid cur_tid then Some t'
                  else tskSt1.(inUsedTaskStates) tid;
                unUsedTaskStates := tskSt1.(unUsedTaskStates);
                tcbListHead      := tskSt1.(tcbListHead);
                prioTbl          := tskSt1.(prioTbl);
                taskRegNextID := tskSt1.(taskRegNextID);
                parkedTaskStacks := tskSt1.(parkedTaskStacks);
                taskLifecycle := tskSt1.(taskLifecycle);
     taskCount        := tskSt1.(taskCount); |} ->
    evSt1.(inUsedEventStates) mid = Some e1 ->
    In cur_tid e1.(waitList) ->
    e2 = {| eventGeneration := e1.(eventGeneration);
            eventName := e1.(eventName);
     eventPadding1 := e1.(eventPadding1);
     eventPadding2 := e1.(eventPadding2);
     eventPadding3 := e1.(eventPadding3);
     eventPadding19 := e1.(eventPadding19);
            eventType   := e1.(eventType);
            mutexFields := e1.(mutexFields);
            semFields   := e1.(semFields);
            mboxFields  := e1.(mboxFields);
            queueFields := e1.(queueFields);
            waitList    := remove_Z_eqb cur_tid e1.(waitList); |} ->
    evSt2 = update_event_field_raw evSt1 mid e2 ->
    verification_slice_event_in_range sg tskSt1 evSt1 ->
    verification_slice_event_in_range sg tskSt2 evSt2.
Proof.
  intros sg tskSt1 tskSt2 evSt1 evSt2 cur_tid mid e1 e2 t t'
    Hget Hcp' HtskSt2 He1 Hin_wl He2 HevSt2
    [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]].
  (* Step 1: derive t.(eventPtr) = Some mid *)
  assert (Hep_mid : t.(eventPtr) = Some mid).
  { destruct (H8 mid e1 He1) as [_ Hwec].
    destruct (event_type_to_pend_type e1.(eventType)) eqn:Hety.
    - destruct (Hwec _ Hin_wl) as [t0 [Hget0 [Hep [_ _]]]].
      rewrite Hget in Hget0. injection Hget0 as ->. exact Hep.
    - simpl in Hwec. rewrite Hwec in Hin_wl. inversion Hin_wl. }
  (* Step 2: derive forall eid' ≠ mid, e' at eid' has cur_tid ∉ e'.waitList *)
  assert (Hnotin_other : forall eid' e',
                            eid' <> mid ->
                            evSt1.(inUsedEventStates) eid' = Some e' ->
                            ~ In cur_tid e'.(waitList)).
  { intros eid' e' Hne Hget'.
    destruct (H8 eid' e' Hget') as [_ Hwec'].
    destruct (event_type_to_pend_type e'.(eventType)) eqn:Hety'.
    - intro Hin'. destruct (Hwec' _ Hin') as [t0' [Hget0' [Hep' [_ _]]]].
      rewrite Hget in Hget0'. injection Hget0' as ->.
      rewrite Hep_mid in Hep'. injection Hep' as Heqpp. subst eid'. exfalso. apply Hne. reflexivity.
    - simpl in Hwec'. intro Hin'. rewrite Hwec' in Hin'. inversion Hin'. }
  assert (He2_binding : event_queue_id e2 = event_queue_id e1).
  { subst e2. reflexivity. }
  subst tskSt2. subst evSt2.
  unfold update_event_field_raw.
  split.
  - (* conj 1 *)
    intros eid0 ev0 Hget'.
    destruct (Z.eqb eid0 mid) eqn:Heq_mid.
    + apply Z.eqb_eq in Heq_mid. subst eid0.
      simpl in Hget'. rewrite Z.eqb_refl in Hget'. injection Hget' as ->.
      destruct (H1 mid e1 He1). split; assumption.
    + simpl in Hget'. rewrite Heq_mid in Hget'.
      destruct (H1 eid0 ev0 Hget'). split; assumption.
  - split.
    + simpl. exact H2.
    + split.
      * simpl. exact H3.
      * split.
        -- (* conj 4 *)
           eapply event_slot_partition_preserved_some_to_some; eauto.
        -- split.
           ++ (* conj 5: event_fields_consistency *)
              intros eid0 ev0 Hget'.
              destruct (Z.eqb eid0 mid) eqn:Heq_mid.
              ** apply Z.eqb_eq in Heq_mid. subst eid0.
                 simpl in Hget'. rewrite Z.eqb_refl in Hget'. injection Hget' as Heq. subst ev0.
                 assert (Hnonempty : e1.(waitList) <> [])
                   by (intro Hc; rewrite Hc in Hin_wl; inversion Hin_wl).
                 assert (Hefc_e1 : event_fields_consistency e1) by (exact (H5 mid e1 He1)).
                 subst e2.
                 unfold event_fields_consistency in *.
                 destruct e1.(eventType); simpl in *.
                 --- (* UNUSED *) destruct Hefc_e1 as [_ [_ [_ [_ Hwl]]]].
                     exfalso. apply Hnonempty. exact Hwl.
                 --- (* SEM *) destruct Hefc_e1 as [Hm [Hs [Hmb Hq]]]. repeat split; assumption.
                 --- (* MUTEX *) destruct Hefc_e1 as [Hm [Hs [Hmb Hq]]]. repeat split; assumption.
                 --- (* MBOX *) destruct Hefc_e1 as [Hm [Hs [Hmb Hq]]]. repeat split; assumption.
                 --- (* Q *) destruct Hefc_e1 as [Hm [Hs [Hmb Hq]]]. repeat split; assumption.
                 --- (* FLAG *) contradiction.
              ** simpl in Hget'. rewrite Heq_mid in Hget'.
                 exact (H5 eid0 ev0 Hget').
           ++ split.
              ** (* conj 6: event payload consistency *)
                 intros eid0 ev0 Hget'.
                 destruct (Z.eqb eid0 mid) eqn:Heq_mid.
                 +++ apply Z.eqb_eq in Heq_mid. subst eid0.
                     simpl in Hget'. rewrite Z.eqb_refl in Hget'. injection Hget' as Heq. subst ev0.
                     subst e2. apply event_payload_consistency_remove_waiter with (tid := cur_tid).
                     --- exact Hin_wl.
                     --- exact (H6 mid e1 He1).
                 +++ simpl in Hget'. rewrite Heq_mid in Hget'.
                     exact (H6 eid0 ev0 Hget').
               ** split; [exact (queue_binding_unique_update_same_binding
                                    evSt1.(inUsedEventStates) mid e1 e2
                                    He1 He2_binding H7) |].
                  (* conj 8: verification_slice_event_wait_entry_consistency *)
                  intros eid0 ev0 Hget'.
                 destruct (Z.eqb eid0 mid) eqn:Heq_mid.
                 *** (* eid0 = mid: ev0 = e2 *)
                     apply Z.eqb_eq in Heq_mid. subst eid0.
                     simpl in Hget'. rewrite Z.eqb_refl in Hget'. injection Hget' as Heq. subst ev0.
                      destruct (H8 mid e1 He1) as [Hwlc Hwec].
                     unfold verification_slice_event_wait_entry_consistency in *.
                     split.
                     --- (* event_waitList_canonical sg tskSt2 e2.waitList *)
                         unfold event_waitList_canonical in *.
                         destruct Hwlc as [Hnd [Hss Hforall]].
                         subst e2. simpl.
                         split.
                         +++ apply remove_Z_eqb_NoDup. exact Hnd.
                         +++ split.
                             **** (* strictly_sorted_by *)
                                 assert (Hext : forall x, wait_prio_key sg tskSt1 x = wait_prio_key sg
                                   {| inUsedTaskStates := fun tid => if Z.eqb tid cur_tid then Some t' else tskSt1.(inUsedTaskStates) tid;
                                      unUsedTaskStates := tskSt1.(unUsedTaskStates);
                                      tcbListHead := tskSt1.(tcbListHead);
                                      prioTbl := tskSt1.(prioTbl);
                                      taskRegNextID := tskSt1.(taskRegNextID);
                                      parkedTaskStacks := tskSt1.(parkedTaskStacks);
                                      taskLifecycle := tskSt1.(taskLifecycle);
     taskCount := tskSt1.(taskCount); |} x).
                                 { intros x. unfold wait_prio_key.
                                   destruct (Z.eqb x cur_tid) eqn:Heq_x.
                                   -- apply Z.eqb_eq in Heq_x. subst x.
                                      simpl. rewrite Hget. rewrite Z.eqb_refl. simpl. rewrite Hcp'. reflexivity.
                                   -- simpl. rewrite Heq_x. simpl. reflexivity. }
                                 apply remove_Z_eqb_strictly_sorted_by.
                                 apply strictly_sorted_by_key_ext with
                                   (key := wait_prio_key sg tskSt1); assumption.
                             **** (* forall tid', In tid' e2.waitList -> exists t0, ... *)
                                 intros tid_in Hin.
                                 destruct (Z.eqb tid_in cur_tid) eqn:Heq_tin.
                                 { (* tid_in = cur_tid, but cur_tid was removed *)
                                   apply Z.eqb_eq in Heq_tin. subst tid_in.
                                   exfalso. exact (remove_Z_eqb_notin cur_tid e1.(waitList) Hin). }
                                 apply remove_Z_eqb_in in Hin.
                                 destruct (Hforall tid_in Hin) as [t0 [Hget0 Hvtp]].
                                 exists t0. split.
                                 { simpl. exact Hget0. }
                                 { exact Hvtp. }
                     --- (* backlink *)
                         subst e2. simpl.
                         destruct (event_type_to_pend_type e1.(eventType)) eqn:Hety.
                         +++ (* Some pty *)
                             intros tid_in Hin.
                             destruct (Z.eqb tid_in cur_tid) eqn:Heq_tin.
                             { apply Z.eqb_eq in Heq_tin. subst tid_in.
                               exfalso. exact (remove_Z_eqb_notin cur_tid e1.(waitList) Hin). }
                             apply remove_Z_eqb_in in Hin.
                             destruct (Hwec _ Hin) as [t0 [Hget0 [Hep0 [Hemp0 Hpnd0]]]].
                             exists t0. split.
                             { simpl. exact Hget0. }
                             { split. exact Hep0. split. exact Hemp0. exact Hpnd0. }
                         +++ (* None: e2.waitList = remove_Z_eqb ... should be [] *)
                             rewrite Hwec. simpl. reflexivity.
                 *** (* eid0 ≠ mid: ev0 from evSt1 (unchanged) *)
                     simpl in Hget'. rewrite Heq_mid in Hget'.
                      destruct (H8 eid0 ev0 Hget') as [Hwlc Hwec].
                     unfold verification_slice_event_wait_entry_consistency in *.
                     split.
                     --- (* canonical *)
                         unfold event_waitList_canonical in *.
                         destruct Hwlc as [Hnd [Hss Hforall]].
                         split.
                         +++ exact Hnd.
                         +++ split.
                             **** assert (Hext : forall x, wait_prio_key sg tskSt1 x = wait_prio_key sg
                                   {| inUsedTaskStates := fun tid => if Z.eqb tid cur_tid then Some t' else tskSt1.(inUsedTaskStates) tid;
                                      unUsedTaskStates := tskSt1.(unUsedTaskStates);
                                      tcbListHead := tskSt1.(tcbListHead);
                                      prioTbl := tskSt1.(prioTbl);
                                      taskRegNextID := tskSt1.(taskRegNextID);
                                      parkedTaskStacks := tskSt1.(parkedTaskStacks);
                                      taskLifecycle := tskSt1.(taskLifecycle);
     taskCount := tskSt1.(taskCount); |} x).
                                 { intros x. unfold wait_prio_key.
                                   destruct (Z.eqb x cur_tid) eqn:Heq_x.
                                   -- apply Z.eqb_eq in Heq_x. subst x.
                                      simpl. rewrite Hget. rewrite Z.eqb_refl. simpl. rewrite Hcp'. reflexivity.
                                   -- simpl. rewrite Heq_x. simpl. reflexivity. }
                                 exact (strictly_sorted_by_key_ext _ _ _ _ Hext Hss).
                             **** intros tid_in Hin.
                                  destruct (Hforall tid_in Hin) as [t0 [Hget0 Hvtp]].
                                  destruct (Z.eqb tid_in cur_tid) eqn:Heq_tin.
                                  { (* tid_in = cur_tid: cur_tid ∉ ev0.waitList (eid0 ≠ mid), contradict *)
                                    apply Z.eqb_eq in Heq_tin. subst tid_in.
                                    exfalso. apply (Hnotin_other eid0 ev0).
                                    -- intro Hc. subst eid0. rewrite Z.eqb_refl in Heq_mid. discriminate.
                                    -- exact Hget'.
                                    -- exact Hin. }
                                  { exists t0. split.
                                    - simpl. rewrite Heq_tin. exact Hget0.
                                    - exact Hvtp. }
                     --- (* backlink *)
                         destruct (event_type_to_pend_type ev0.(eventType)) eqn:Hety0.
                         +++ intros tid_in Hin.
                              destruct (Hwec _ Hin) as [t0 [Hget0 [Hep0 [Hemp0 Hpnd0]]]].
                              destruct (Z.eqb tid_in cur_tid) eqn:Heq_tin.
                              { apply Z.eqb_eq in Heq_tin. subst tid_in.
                                exfalso. apply (Hnotin_other eid0 ev0).
                                -- intro Hc. subst eid0. rewrite Z.eqb_refl in Heq_mid. discriminate.
                                -- exact Hget'.
                                -- exact Hin. }
                              { exists t0. split.
                                - simpl. rewrite Heq_tin. exact Hget0.
                                - split. exact Hep0. split. exact Hemp0. exact Hpnd0. }
                         +++ exact Hwec.
Qed.

Definition unused_complete_event (sg : StableGlobVars) (ctrl_start : addr)
  (eid : EventID) : Assertion :=
  (ctrl_start + OSEventType_off) # UChar |-> encode_event_type OS_EVENT_TYPE_UNUSED **
  (ctrl_start + OSEventPtr_off)  # Ptr |->_ **
  (ctrl_start + OSEventCnt_off)  # UShort |->_ **
  (ctrl_start + OSEventGrp_off)  # UChar |->_ **
  (ctrl_start + OSEventTbl_off + 0) # UChar |->_ **
  (ctrl_start + OSEventTbl_off + 1) # UChar |->_ **
  (ctrl_start + OSEventTbl_off + 2) # UChar |->_ **
  (ctrl_start + OSEventTbl_off + 3) # UChar |->_ **
  (ctrl_start + OSEventTbl_off + 4) # UChar |->_ **
  (ctrl_start + OSEventTbl_off + 5) # UChar |->_ **
  (ctrl_start + OSEventTbl_off + 6) # UChar |->_ **
  (ctrl_start + OSEventTbl_off + 7) # UChar |->_ .

(* ================================================================== *)
(* Phase 5 Task 5.5:store_used_event_map + free list                  *)
(* ================================================================== *)

Definition store_used_event_map (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState)
  (m : EventID -> option OSEventAbstractState) : Assertion :=
  store_map
    (fun eid e => used_complete_event sg tskSt (event_addr sg eid) eid e)
    m.

Definition store_used_event_map_raw (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState)
  (m : EventID -> option OSEventAbstractState) : Assertion :=
  store_map
    (fun eid e =>
       used_complete_event_raw sg tskSt (event_addr sg eid) eid e)
    m.

Definition store_used_event_map_missing_i (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState)
  (m : EventID -> option OSEventAbstractState) (exclude_eid : EventID) : Assertion :=
  store_map_missing_i
    (fun eid e => used_complete_event sg tskSt (event_addr sg eid) eid e)
    m exclude_eid.

Definition store_used_event_map_raw_missing_i (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState)
  (m : EventID -> option OSEventAbstractState) (exclude_eid : EventID)
  : Assertion :=
  store_map_missing_i
    (fun eid e =>
       used_complete_event_raw sg tskSt (event_addr sg eid) eid e)
    m exclude_eid.

Definition remove_two_event_entries
  (m : EventID -> option OSEventAbstractState) (eid1 eid2 : EventID)
  : EventID -> option OSEventAbstractState :=
  fun eid =>
    if Z.eqb eid eid1 then None
    else if Z.eqb eid eid2 then None
    else m eid.

Definition store_used_event_map_missing_two (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState)
  (m : EventID -> option OSEventAbstractState) (eid1 eid2 : EventID)
  : Assertion :=
  store_used_event_map sg tskSt (remove_two_event_entries m eid1 eid2).

Definition free_event_head (sg : StableGlobVars)
  (l : list EventID) : addr :=
  match l with
  | [] => 0
  | eid :: _ => event_addr sg eid
  end.

Fixpoint store_free_event_nodes (sg : StableGlobVars)
  (l : list EventID) : Assertion :=
  match l with
  | [] => emp
  | eid :: rest =>
      (event_addr sg eid + OSEventType_off) # UChar |->
        encode_event_type OS_EVENT_TYPE_UNUSED **
      (event_addr sg eid + OSEventPtr_off) # Ptr |->
        free_event_head sg rest **
      (event_addr sg eid + OSEventCnt_off) # UShort |->_ **
      (event_addr sg eid + OSEventGrp_off) # UChar |->_ **
      (event_addr sg eid + OSEventTbl_off + 0) # UChar |->_ **
      (event_addr sg eid + OSEventTbl_off + 1) # UChar |->_ **
      (event_addr sg eid + OSEventTbl_off + 2) # UChar |->_ **
      (event_addr sg eid + OSEventTbl_off + 3) # UChar |->_ **
      (event_addr sg eid + OSEventTbl_off + 4) # UChar |->_ **
      (event_addr sg eid + OSEventTbl_off + 5) # UChar |->_ **
      (event_addr sg eid + OSEventTbl_off + 6) # UChar |->_ **
      (event_addr sg eid + OSEventTbl_off + 7) # UChar |->_ **
      store_free_event_nodes sg rest
  end.

Definition store_free_event_list (sg : StableGlobVars)
  (l : list EventID) : Assertion :=
  sg.(g_OSEventFreeList) # Ptr |-> free_event_head sg l **
  store_free_event_nodes sg l.

(* The non-type cells of one free OS_EVENT.  The link value is deliberately
   exact: it is the address of the next node in the concrete free-list order,
   or zero at the tail. *)
Definition free_event_node_rest_no_type (sg : StableGlobVars)
  (eid : EventID) (next : addr) : Assertion :=
  (event_addr sg eid + OSEventPtr_off) # Ptr |-> next **
  (event_addr sg eid + OSEventCnt_off) # UShort |->_ **
  (event_addr sg eid + OSEventGrp_off) # UChar |->_ **
  (event_addr sg eid + OSEventTbl_off + 0) # UChar |->_ **
  (event_addr sg eid + OSEventTbl_off + 1) # UChar |->_ **
  (event_addr sg eid + OSEventTbl_off + 2) # UChar |->_ **
  (event_addr sg eid + OSEventTbl_off + 3) # UChar |->_ **
  (event_addr sg eid + OSEventTbl_off + 4) # UChar |->_ **
  (event_addr sg eid + OSEventTbl_off + 5) # UChar |->_ **
  (event_addr sg eid + OSEventTbl_off + 6) # UChar |->_ **
  (event_addr sg eid + OSEventTbl_off + 7) # UChar |->_.

(* Storage for a prefix whose last link continues into [tail].  This zipper
   representation makes localization at an arbitrary free node reversible,
   without pretending that the selected node is the free-list head. *)
Fixpoint store_free_event_prefix (sg : StableGlobVars)
  (prefix tail : list EventID) : Assertion :=
  match prefix with
  | [] => emp
  | eid :: rest =>
      (event_addr sg eid + OSEventType_off) # UChar |->
        encode_event_type OS_EVENT_TYPE_UNUSED **
      free_event_node_rest_no_type sg eid
        (free_event_head sg (rest ++ tail)) **
      store_free_event_prefix sg rest tail
  end.

Definition store_free_event_list_no_type_at (sg : StableGlobVars)
  (prefix : list EventID) (eid : EventID) (suffix : list EventID)
  : Assertion :=
  sg.(g_OSEventFreeList) # Ptr |->
    free_event_head sg (prefix ++ eid :: suffix) **
  store_free_event_prefix sg prefix (eid :: suffix) **
  free_event_node_rest_no_type sg eid (free_event_head sg suffix) **
  store_free_event_nodes sg suffix.

Lemma store_free_event_nodes_split_type_at :
  forall sg prefix eid suffix,
    store_free_event_nodes sg (prefix ++ eid :: suffix) |--
      (event_addr sg eid + OSEventType_off) # UChar |->
        0 **
      store_free_event_prefix sg prefix (eid :: suffix) **
      free_event_node_rest_no_type sg eid (free_event_head sg suffix) **
      store_free_event_nodes sg suffix.
Proof.
  intros sg prefix. induction prefix as [|head prefix IH];
    intros eid suffix; simpl.
  - simpl. unfold free_event_node_rest_no_type. entailer!.
  - unfold free_event_node_rest_no_type.
    sep_apply_l_atomic (IH eid suffix).
    unfold free_event_node_rest_no_type.
    entailer!.
Qed.

Lemma store_free_event_nodes_merge_type_at :
  forall sg prefix eid suffix,
    (event_addr sg eid + OSEventType_off) # UChar |->
      0 **
    store_free_event_prefix sg prefix (eid :: suffix) **
    free_event_node_rest_no_type sg eid (free_event_head sg suffix) **
    store_free_event_nodes sg suffix |--
      store_free_event_nodes sg (prefix ++ eid :: suffix).
Proof.
  intros sg prefix. induction prefix as [|head prefix IH];
    intros eid suffix; simpl.
  - simpl. unfold free_event_node_rest_no_type. entailer!.
  - sep_apply_l_atomic (IH eid suffix).
    unfold free_event_node_rest_no_type.
    entailer!.
Qed.

Lemma store_free_event_list_split_type_at :
  forall sg prefix eid suffix,
    store_free_event_list sg (prefix ++ eid :: suffix) |--
      (event_addr sg eid + OSEventType_off) # UChar |->
        0 **
      store_free_event_list_no_type_at sg prefix eid suffix.
Proof.
  intros.
  unfold store_free_event_list, store_free_event_list_no_type_at.
  sep_apply_l_atomic
    (store_free_event_nodes_split_type_at sg prefix eid suffix).
  entailer!.
Qed.

Lemma store_free_event_list_merge_type_at :
  forall sg prefix eid suffix,
    (event_addr sg eid + OSEventType_off) # UChar |->
      0 **
    store_free_event_list_no_type_at sg prefix eid suffix |--
      store_free_event_list sg (prefix ++ eid :: suffix).
Proof.
  intros.
  unfold store_free_event_list, store_free_event_list_no_type_at.
  sep_apply_l_atomic
    (store_free_event_nodes_merge_type_at sg prefix eid suffix).
  entailer!.
Qed.

(* ================================================================== *)
(* Phase 5 Task 5.6:verification_slice_event_inv                                         *)
(* ================================================================== *)

(* Source-total event representation.  It owns the complete used-event map
   and free list but carries no event lifecycle, payload or task/event
   consistency proposition.  In particular, the group bitmap encoder above
   is OR-based, matching the concrete C update even when distinct priorities
   occupy the same wait-table row. *)
Definition verification_slice_event_raw_rep (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState)
  (st : Glob_EventAbstractState) : Assertion :=
  store_used_event_map_raw sg tskSt st.(inUsedEventStates) **
  store_free_event_list sg st.(unUsedEventStates).

(** Mutex owners use the same configured pool address as the Task map,
    ready cache and priority table, not the historical 68-byte slice. *)
Definition encode_event_ptr_value (sg : StableGlobVars) (e : OSEventAbstractState) : Z :=
  match e.(eventType), e.(mutexFields) with
  | OS_EVENT_TYPE_MUTEX, Some m => encode_task_link sg m.(mfOwner)
  | _, _ => verification_slice_encode_event_ptr_value sg e
  end.

Definition event_image (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (e : OSEventAbstractState) : EventStorage :=
  fun f => match f with
  | EventTypeField => Some (encode_event_type e.(eventType))
  | EventPtrField => Some (encode_event_ptr_value sg e)
  | EventCntField => Some (encode_event_cnt_value e)
  | EventGrpField => Some (encode_event_wait_grp e.(waitList) tasks)
  | EventTbl0 => Some (encode_event_wait_tbl_at_or e.(waitList) tasks 0)
  | EventTbl1 => Some (encode_event_wait_tbl_at_or e.(waitList) tasks 1)
  | EventTbl2 => Some (encode_event_wait_tbl_at_or e.(waitList) tasks 2)
  | EventTbl3 => Some (encode_event_wait_tbl_at_or e.(waitList) tasks 3)
  | EventTbl4 => Some (encode_event_wait_tbl_at_or e.(waitList) tasks 4)
  | EventTbl5 => Some (encode_event_wait_tbl_at_or e.(waitList) tasks 5)
  | EventTbl6 => Some (encode_event_wait_tbl_at_or e.(waitList) tasks 6)
  | EventTbl7 => Some (encode_event_wait_tbl_at_or e.(waitList) tasks 7)
  | EventPadding1 => e.(eventPadding1)
  | EventPadding2 => e.(eventPadding2)
  | EventPadding3 => e.(eventPadding3)
  | EventPadding19 => e.(eventPadding19)
  | EventNameField => Some e.(eventName)
  end.

(** A projection of the existing public Event map, not a second stored
    state.  Source-order byte-image traversals use it for refinement. *)
Definition event_used_images (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (events : Glob_EventAbstractState) : EventID -> option EventStorage :=
  fun eid => option_map (event_image sg tasks) (events.(inUsedEventStates) eid).

Lemma event_used_images_update : forall sg tasks events eid e,
  event_used_images sg tasks (update_event_field_raw events eid e) =
    kernel_map_set (event_used_images sg tasks events) eid (Some (event_image sg tasks e)).
Proof.
  intros; apply functional_extensionality; intro slot.
  unfold event_used_images, kernel_map_set; simpl.
  destruct (Z.eq_dec slot eid) as [->|Hne]; [rewrite Z.eqb_refl; reflexivity|].
  destruct (Z.eqb slot eid) eqn:E; [apply Z.eqb_eq in E; contradiction|reflexivity].
Qed.

Definition used_event_rep (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (eid : EventID) (e : OSEventAbstractState)
  : Assertion :=
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid) (event_image sg tasks e).

(** OSEventNameSet writes this pointer, not the string it denotes. The
    caller separately supplies the name-byte lifetime/ownership contract. *)
Definition event_set_name (e : OSEventAbstractState) (name : addr)
  : OSEventAbstractState :=
  {| eventType := e.(eventType); mutexFields := e.(mutexFields);
     semFields := e.(semFields); mboxFields := e.(mboxFields);
     queueFields := e.(queueFields); waitList := e.(waitList);
     eventGeneration := e.(eventGeneration); eventName := name;
     eventPadding1 := e.(eventPadding1); eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3); eventPadding19 := e.(eventPadding19) |}.

Lemma event_set_name_image_eq : forall sg tasks e name,
  event_image sg tasks (event_set_name e name) =
    event_write (event_image sg tasks e) EventNameField (Some name).
Proof. intros; apply functional_extensionality; intros []; reflexivity. Qed.

Definition event_rep_no_name (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (eid : EventID) (e : OSEventAbstractState)
  : Assertion :=
  event_storage_without_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg tasks e) EventNameField.

Lemma event_rep_split_name : forall sg tasks eid e,
  sg.(osKernelConfig).(cfgEventNames) = true ->
  used_event_rep sg tasks eid e |--
  (event_addr sg eid + 20) # Ptr |-> e.(eventName) **
    event_rep_no_name sg tasks eid e.
Proof.
  intros sg tasks eid e Hnamed; unfold used_event_rep, event_rep_no_name.
  apply (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg tasks e) EventNameField).
  apply event_name_field_in_fields; exact Hnamed.
Qed.

Lemma event_rep_merge_name : forall sg tasks eid e,
  sg.(osKernelConfig).(cfgEventNames) = true ->
  (event_addr sg eid + 20) # Ptr |-> e.(eventName) **
    event_rep_no_name sg tasks eid e |-- used_event_rep sg tasks eid e.
Proof.
  intros sg tasks eid e Hnamed; unfold used_event_rep, event_rep_no_name.
  apply (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg tasks e) EventNameField).
  apply event_name_field_in_fields; exact Hnamed.
Qed.

Lemma event_rep_merge_updated_name : forall sg tasks eid e name,
  sg.(osKernelConfig).(cfgEventNames) = true ->
  (event_addr sg eid + 20) # Ptr |-> name ** event_rep_no_name sg tasks eid e |--
    used_event_rep sg tasks eid (event_set_name e name).
Proof.
  intros sg tasks eid e name Hnamed; unfold used_event_rep, event_rep_no_name.
  rewrite event_set_name_image_eq.
  apply (event_storage_merge_updated_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg tasks e) EventNameField (Some name)).
  apply event_name_field_in_fields; exact Hnamed.
Qed.

Definition event_raw_rep (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (events : Glob_EventAbstractState) : Assertion :=
  store_map (used_event_rep sg tasks) events.(inUsedEventStates) **
  event_free_storage_rep sg events ** event_free_root_rep sg events.

(** Resource/field validity with an explicit waiter relation. The selected
    single-wait and configured Multi clients instantiate the last clause;
    no spatial resource or lifecycle condition is abstracted away. *)
Definition event_in_range_with_wait (sg : StableGlobVars)
  (events : Glob_EventAbstractState)
  (entry : EventID -> OSEventAbstractState -> Prop) : Prop :=
  event_pool_partition sg events /\
  event_free_storage_valid sg events /\
  event_identity_valid events /\
  (forall eid e, events.(inUsedEventStates) eid = Some e -> event_fields_consistency e) /\
  (forall eid e, events.(inUsedEventStates) eid = Some e -> event_payload_consistency sg e) /\
  queue_binding_unique events.(inUsedEventStates) /\
  (forall eid e, events.(inUsedEventStates) eid = Some e -> entry eid e).

Definition event_in_range (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (events : Glob_EventAbstractState) : Prop :=
  event_pool_partition sg events /\
  event_free_storage_valid sg events /\
  event_identity_valid events /\
  (forall eid e, events.(inUsedEventStates) eid = Some e -> event_fields_consistency e) /\
  (forall eid e, events.(inUsedEventStates) eid = Some e -> event_payload_consistency sg e) /\
  queue_binding_unique events.(inUsedEventStates) /\
  (forall eid e, events.(inUsedEventStates) eid = Some e ->
     event_wait_entry_consistency sg tasks eid e).

Lemma event_update_task_preserves_in_range : forall sg tasks events tid old new,
  tasks.(inUsedTaskStates) tid = Some old -> new.(curPrio) = old.(curPrio) ->
  new.(eventPtr) = old.(eventPtr) -> new.(eventMultiWaitEvents) = old.(eventMultiWaitEvents) ->
  (forall kind, task_linked_wait_phase old kind -> task_linked_wait_phase new kind) ->
  event_in_range sg tasks events ->
  event_in_range sg (glob_task_set_usedtask tasks tid new) events.
Proof.
  intros sg tasks events tid old new Hold Hp Hptr Hmulti Hphase
    [Hpool [Hfree [Hidentity [Hfields [Hpayload [Hqueue Hentries]]]]]].
  split; [exact Hpool|]; split; [exact Hfree|]; split; [exact Hidentity|].
  split; [exact Hfields|]; split; [exact Hpayload|]; split; [exact Hqueue|].
  intros eid e He; eapply event_wait_entry_update_task;
    [exact Hold|exact Hp|exact Hptr|exact Hmulti|exact Hphase|exact (Hentries eid e He)].
Qed.

Lemma event_update_status_preserves_in_range : forall sg tasks events tid old status,
  tasks.(inUsedTaskStates) tid = Some old ->
  task_non_suspension_bits status = task_non_suspension_bits old.(stat) ->
  event_in_range sg tasks events ->
  event_in_range sg (glob_task_set_usedtask tasks tid (task_set_status old status)) events.
Proof.
  intros sg tasks events tid old status Hold Hbits Hvalid.
  eapply event_update_task_preserves_in_range;
    [exact Hold|reflexivity|reflexivity|reflexivity| |exact Hvalid].
  intros kind Hphase; unfold task_linked_wait_phase; cbn [task_set_status stat statPend dly].
  rewrite Hbits; exact Hphase.
Qed.

Lemma initial_event_abstract_state_valid : forall sg tasks,
  event_in_range sg tasks (initial_event_abstract_state sg).
Proof.
  intros sg tasks.
  split; [apply event_pool_initial_partition|].
  split; [apply event_pool_initial_free_storage|].
  split; [apply event_pool_initial_identity_valid|].
  split; [intros; discriminate|]. split; [intros; discriminate|].
  split; intros; discriminate.
Qed.

(** The event bytes depend on waiter priorities, not on complete TCB
    equality.  A ready-list operation may use this transport only after
    proving it for every surviving event, including timeout-linked waiters. *)
Definition event_wait_priority_agreement (before after : Glob_TaskAbstractState)
  (events : Glob_EventAbstractState) : Prop :=
  forall eid e tid, events.(inUsedEventStates) eid = Some e -> In tid e.(waitList) ->
    option_map curPrio (before.(inUsedTaskStates) tid) =
    option_map curPrio (after.(inUsedTaskStates) tid).

Definition event_raw_encoding_agrees (before after : Glob_TaskAbstractState)
  (events : Glob_EventAbstractState) : Prop :=
  forall eid e, events.(inUsedEventStates) eid = Some e ->
    encode_event_wait_grp e.(waitList) before = encode_event_wait_grp e.(waitList) after /\
    forall y, encode_event_wait_tbl_at_or e.(waitList) before y =
      encode_event_wait_tbl_at_or e.(waitList) after y.

Lemma event_wait_encoding_priority_ext : forall ids before after,
  (forall tid, In tid ids -> option_map curPrio (before.(inUsedTaskStates) tid) =
    option_map curPrio (after.(inUsedTaskStates) tid)) ->
  encode_event_wait_grp ids before = encode_event_wait_grp ids after /\
  forall y, encode_event_wait_tbl_at_or ids before y = encode_event_wait_tbl_at_or ids after y.
Proof.
  induction ids as [|tid rest IH]; intros before after Heq.
  - split; reflexivity.
  - destruct (IH before after (fun q Hin => Heq q (or_intror Hin))) as [Hgrp Htbl].
    pose proof (Heq tid (or_introl eq_refl)) as Hhead.
    cbn [encode_event_wait_grp encode_event_wait_tbl_at_or fold_right].
    destruct (before.(inUsedTaskStates) tid) as [old|];
      destruct (after.(inUsedTaskStates) tid) as [new|]; simpl in Hhead; try discriminate.
    + injection Hhead as Hprio; rewrite Hprio, Hgrp; split; [reflexivity|].
      intro y; fold (encode_event_wait_tbl_at_or rest before y).
      fold (encode_event_wait_tbl_at_or rest after y); rewrite Htbl; reflexivity.
    + split; [exact Hgrp|exact Htbl].
Qed.

Lemma event_wait_priority_agreement_encodes : forall before after events,
  event_wait_priority_agreement before after events -> event_raw_encoding_agrees before after events.
Proof.
  intros before after events Heq eid e Hget.
  apply event_wait_encoding_priority_ext; intros tid Hin; eapply Heq; eauto.
Qed.

Lemma verification_slice_event_raw_rep_change_task_index : forall sg before after events,
  event_raw_encoding_agrees before after events ->
  verification_slice_event_raw_rep sg before events = verification_slice_event_raw_rep sg after events.
Proof.
  intros sg before after events Heq.
  unfold verification_slice_event_raw_rep, store_used_event_map_raw, store_map.
  assert (Hnodes :
    (fun eid => match events.(inUsedEventStates) eid with
      | Some e => used_complete_event_raw sg before (event_addr sg eid) eid e | None => emp end) =
    (fun eid => match events.(inUsedEventStates) eid with
      | Some e => used_complete_event_raw sg after (event_addr sg eid) eid e | None => emp end)).
  { apply functional_extensionality; intro eid.
    destruct (events.(inUsedEventStates) eid) as [e|] eqn:Hget; [|reflexivity].
    destruct (Heq eid e Hget) as [Hgrp Htbl].
    unfold used_complete_event_raw; rewrite Hgrp, !Htbl; reflexivity. }
  rewrite Hnodes; reflexivity.
Qed.

Lemma event_raw_rep_change_task_index : forall sg before after events,
  event_raw_encoding_agrees before after events ->
  event_raw_rep sg before events = event_raw_rep sg after events.
Proof.
  intros sg before after events Heq; unfold event_raw_rep, store_map.
  assert (Hnodes :
    (fun eid => match events.(inUsedEventStates) eid with
      | Some e => used_event_rep sg before eid e | None => emp end) =
    (fun eid => match events.(inUsedEventStates) eid with
      | Some e => used_event_rep sg after eid e | None => emp end)).
  { apply functional_extensionality; intro eid.
    destruct (events.(inUsedEventStates) eid) as [e|] eqn:Hget; [|reflexivity].
    destruct (Heq eid e Hget) as [Hgrp Htbl].
    assert (Himage : event_image sg before e = event_image sg after e).
    { apply functional_extensionality; intros []; cbn [event_image];
        rewrite ?Hgrp, ?Htbl; reflexivity. }
    unfold used_event_rep; rewrite Himage; reflexivity. }
  rewrite Hnodes; reflexivity.
Qed.

Lemma event_task_commit_encoding_frame : forall sg tasks events p invocation node,
  event_in_range sg tasks events -> tasks.(inUsedTaskStates) node.(taskID) = None ->
  event_raw_encoding_agrees tasks (task_commit tasks p invocation node) events.
Proof.
  intros sg tasks events p invocation node [_ [_ [_ [_ [_ [_ Hwait]]]]]] Hnone.
  apply event_wait_priority_agreement_encodes; intros eid e tid Hget Hin.
  destruct (proj1 (Hwait eid e Hget)) as [_ [_ Hlive]].
  destruct (Hlive tid Hin) as [t [Ht Hprio]].
  pose proof (task_commit_observation Z curPrio tasks p invocation node tid
    (fun _ _ _ => eq_refl)) as Hobs.
  change (option_map curPrio (tasks.(inUsedTaskStates) tid) =
    option_map curPrio ((task_commit tasks p invocation node).(inUsedTaskStates) tid)).
  symmetry; destruct (Z.eq_dec tid node.(taskID)) as [Heq|Hneq] in Hobs.
  - subst tid; congruence.
  - exact Hobs.
Qed.

Lemma task_commit_preserves_event_in_range : forall sg tasks events p invocation node,
  event_in_range sg tasks events -> tasks.(inUsedTaskStates) node.(taskID) = None ->
  event_in_range sg (task_commit tasks p invocation node) events.
Proof.
  intros sg tasks events p invocation node [Hpart [Hfree [Hidentity [Hfields [Hpayload [Hqueues Hwait]]]]]] Hnone.
  split; [exact Hpart|]. split; [exact Hfree|]. split; [exact Hidentity|].
  split; [exact Hfields|]. split; [exact Hpayload|].
  split; [exact Hqueues|]. intros eid e He.
  apply task_commit_preserves_event_wait_entry; [exact Hnone|apply Hwait; exact He].
Qed.

(* Structural residual after selecting one live event record. *)
Definition verification_slice_event_raw_rep_no_eid (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState)
  (st : Glob_EventAbstractState) (eid : EventID) : Assertion :=
  store_used_event_map_raw_missing_i
    sg tskSt st.(inUsedEventStates) eid **
  store_free_event_list sg st.(unUsedEventStates).

Lemma verification_slice_event_raw_rep_split_eid :
  forall sg tskSt st eid e,
    st.(inUsedEventStates) eid = Some e ->
    verification_slice_event_raw_rep sg tskSt st |--
      used_complete_event_raw sg tskSt (event_addr sg eid) eid e **
      verification_slice_event_raw_rep_no_eid sg tskSt st eid.
Proof.
  intros sg tskSt st eid e Hused.
  unfold verification_slice_event_raw_rep, verification_slice_event_raw_rep_no_eid, store_used_event_map_raw.
  sep_apply_l_atomic
    (store_map_split
      (fun eid0 e0 =>
         used_complete_event_raw sg tskSt (event_addr sg eid0) eid0 e0)
      eid e st.(inUsedEventStates) Hused).
  unfold store_used_event_map_raw_missing_i.
  entailer!.
Qed.

Lemma verification_slice_event_raw_rep_merge_eid :
  forall sg tskSt st eid e,
    st.(inUsedEventStates) eid = Some e ->
    used_complete_event_raw sg tskSt (event_addr sg eid) eid e **
    verification_slice_event_raw_rep_no_eid sg tskSt st eid |--
      verification_slice_event_raw_rep sg tskSt st.
Proof.
  intros sg tskSt st eid e Hused.
  unfold verification_slice_event_raw_rep_no_eid, store_used_event_map_raw_missing_i.
  sep_apply_l_atomic
    (store_map_merge
      (fun eid0 e0 =>
         used_complete_event_raw sg tskSt (event_addr sg eid0) eid0 e0)
      eid e st.(inUsedEventStates) Hused).
  unfold verification_slice_event_raw_rep, store_used_event_map_raw.
  entailer!.
Qed.

Definition verification_slice_event_inv (sg : StableGlobVars) (tskSt : Glob_TaskAbstractState)
  (st : Glob_EventAbstractState) : Assertion :=
  coq_prop (verification_slice_event_in_range sg tskSt st) &&
  store_used_event_map sg tskSt st.(inUsedEventStates) **
  store_free_event_list sg st.(unUsedEventStates).

Lemma verification_slice_event_inv_split_raw_validity :
  forall sg tskSt st,
    verification_slice_task_validity sg tskSt ->
    verification_slice_event_inv sg tskSt st |--
      verification_slice_event_raw_rep sg tskSt st &&
      coq_prop (verification_slice_event_in_range sg tskSt st).
Proof.
  intros sg tskSt st Htask.
  unfold verification_slice_event_inv.
  pureIntros.
  unfold verification_slice_event_raw_rep, store_used_event_map,
    store_used_event_map_raw, store_map.
  Intros l.
  Exists l.
  assert (Hmap :
    map
      (fun eid =>
         match st.(inUsedEventStates) eid with
         | Some e =>
             used_complete_event sg tskSt (event_addr sg eid) eid e
         | None => emp
         end) l =
    map
      (fun eid =>
         match st.(inUsedEventStates) eid with
         | Some e =>
             used_complete_event_raw sg tskSt
               (event_addr sg eid) eid e
         | None => emp
         end) l).
  {
    apply map_ext_in.
    intros eid Hin.
    destruct (st.(inUsedEventStates) eid) as [e|] eqn:Hlookup;
      [|reflexivity].
    apply used_complete_event_stable_eq_raw.
    - unfold verification_slice_event_in_range, verification_slice_event_in_range,
        verification_slice_event_in_range in H.
      destruct H as [_ [_ [_ [_ [_ [_ [_ Hentry]]]]]]].
      specialize (Hentry eid e Hlookup).
      unfold verification_slice_event_wait_entry_consistency in Hentry.
      exact (proj1 Hentry).
    - unfold verification_slice_task_validity, verification_slice_task_in_range,
        verification_slice_task_in_range in Htask.
      destruct Htask as [Htask _].
      destruct Htask as [_ [_ [_ [_ [_ [_ Hunique]]]]]].
      exact Hunique.
  }
  rewrite <- Hmap.
  entailer!.
Qed.

Definition verification_slice_event_inv_used_no_type (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (st : Glob_EventAbstractState)
  (eid : EventID) (e : OSEventAbstractState) : Assertion :=
  coq_prop (verification_slice_event_in_range sg tskSt st /\
            st.(inUsedEventStates) eid = Some e) &&
  store_used_event_map_missing_i
    sg tskSt st.(inUsedEventStates) eid **
  used_event_rest_no_type sg tskSt (event_addr sg eid) eid e **
  store_free_event_list sg st.(unUsedEventStates).

Definition verification_slice_event_inv_free_no_type (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (st : Glob_EventAbstractState)
  (eid : EventID) (prefix suffix : list EventID) : Assertion :=
  coq_prop (verification_slice_event_in_range sg tskSt st /\
            st.(inUsedEventStates) eid = None /\
            st.(unUsedEventStates) = prefix ++ eid :: suffix) &&
  store_used_event_map sg tskSt st.(inUsedEventStates) **
  store_free_event_list_no_type_at sg prefix eid suffix.

Definition event_slot_type_value (st : Glob_EventAbstractState)
  (eid : EventID) : Z :=
  match st.(inUsedEventStates) eid with
  | Some e => encode_event_type e.(eventType)
  | None => 0
  end.

Definition event_slot_unused_prop (st : Glob_EventAbstractState)
  (eid : EventID) : Prop :=
  st.(inUsedEventStates) eid = None.

(* Total residual for the public type read.  The live branch retains the
   complete non-type record and the free branch retains a list zipper with
   the selected node's exact successor. *)
Definition verification_slice_event_inv_no_type_at (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (st : Glob_EventAbstractState)
  (eid : EventID) : Assertion :=
  match st.(inUsedEventStates) eid with
  | Some e => verification_slice_event_inv_used_no_type sg tskSt st eid e
  | None =>
      EX prefix suffix : list EventID,
      verification_slice_event_inv_free_no_type sg tskSt st eid prefix suffix
  end.

Lemma event_valid_none_is_free :
  forall sg tskSt st eid,
    verification_slice_event_in_range sg tskSt st ->
    valid_event_id sg eid ->
    st.(inUsedEventStates) eid = None ->
    In eid st.(unUsedEventStates).
Proof.
  intros sg tskSt st eid Hvalid Heid Hnone.
  unfold verification_slice_event_in_range, verification_slice_event_in_range,
    verification_slice_event_in_range in Hvalid.
  destruct Hvalid as [_ [_ [_ [Hpartition _]]]].
  eapply event_slot_partition_none_lookup; eauto.
Qed.

Lemma verification_slice_event_inv_used_split_type :
  forall sg tskSt st eid e,
    st.(inUsedEventStates) eid = Some e ->
    verification_slice_event_inv sg tskSt st |--
      (event_addr sg eid + OSEventType_off) # UChar |->
        encode_event_type e.(eventType) **
      verification_slice_event_inv_used_no_type sg tskSt st eid e.
Proof.
  intros sg tskSt st eid e Hused.
  unfold verification_slice_event_inv, verification_slice_event_inv_used_no_type, store_used_event_map.
  pureIntros.
  sepcon_lift
    (store_map
      (fun eid0 e0 =>
         used_complete_event sg tskSt (event_addr sg eid0) eid0 e0)
      (inUsedEventStates st)).
  sep_apply_l_atomic
    (store_map_split
      (fun eid0 e0 =>
         used_complete_event sg tskSt (event_addr sg eid0) eid0 e0)
      eid e (inUsedEventStates st) Hused).
  sep_apply_l_atomic
    (used_complete_event_split_type sg tskSt
      (event_addr sg eid) eid e).
  entailer!.
Qed.

Lemma verification_slice_event_inv_used_merge_type :
  forall sg tskSt st eid e,
    st.(inUsedEventStates) eid = Some e ->
    (event_addr sg eid + OSEventType_off) # UChar |->
      encode_event_type e.(eventType) **
    verification_slice_event_inv_used_no_type sg tskSt st eid e |--
      verification_slice_event_inv sg tskSt st.
Proof.
  intros sg tskSt st eid e Hused.
  unfold verification_slice_event_inv_used_no_type, store_used_event_map_missing_i.
  pureIntros.
  sep_apply_l_atomic
    (used_complete_event_merge_type sg tskSt
      (event_addr sg eid) eid e).
  unfold verification_slice_event_inv, store_used_event_map.
  entailer!.
  sep_apply_l_atomic
    (store_map_merge
      (fun eid0 e0 =>
         used_complete_event sg tskSt (event_addr sg eid0) eid0 e0)
      eid e (inUsedEventStates st) Hused).
  entailer!.
Qed.

Lemma verification_slice_event_inv_free_split_type :
  forall sg tskSt st eid,
    valid_event_id sg eid ->
    st.(inUsedEventStates) eid = None ->
    verification_slice_event_inv sg tskSt st |--
      EX prefix suffix : list EventID,
      (event_addr sg eid + OSEventType_off) # UChar |->
        0 **
      verification_slice_event_inv_free_no_type sg tskSt st eid prefix suffix.
Proof.
  intros sg tskSt st eid Heid Hnone.
  unfold verification_slice_event_inv.
  pureIntros.
  pose proof
    (event_valid_none_is_free sg tskSt st eid H Heid Hnone) as Hin.
  apply in_split in Hin.
  destruct Hin as [prefix [suffix Hlist]].
  Exists prefix suffix.
  unfold verification_slice_event_inv_free_no_type.
  rewrite Hlist.
  sep_apply_l_atomic
    (store_free_event_list_split_type_at sg prefix eid suffix).
  entailer!.
Qed.

Lemma verification_slice_event_inv_free_merge_type :
  forall sg tskSt st eid prefix suffix,
    (event_addr sg eid + OSEventType_off) # UChar |->
      0 **
    verification_slice_event_inv_free_no_type sg tskSt st eid prefix suffix |--
      verification_slice_event_inv sg tskSt st.
Proof.
  intros sg tskSt st eid prefix suffix.
  unfold verification_slice_event_inv_free_no_type.
  pureIntros.
  destruct H as [Hvalid [_ Hlist]].
  sep_apply_l_atomic
    (store_free_event_list_merge_type_at sg prefix eid suffix).
  unfold verification_slice_event_inv.
  rewrite Hlist.
  entailer!.
Qed.

Lemma verification_slice_event_inv_split_type_total :
  forall sg tskSt st eid,
    valid_event_id sg eid ->
    verification_slice_event_inv sg tskSt st |--
      (event_addr sg eid + OSEventType_off) # UChar |->
        event_slot_type_value st eid **
      verification_slice_event_inv_no_type_at sg tskSt st eid.
Proof.
  intros sg tskSt st eid Heid.
  unfold event_slot_type_value, verification_slice_event_inv_no_type_at.
  destruct (inUsedEventStates st eid) as [e |] eqn:Hslot.
  - eapply verification_slice_event_inv_used_split_type; eauto.
  - sep_apply_l_atomic
      (verification_slice_event_inv_free_split_type sg tskSt st eid Heid Hslot).
    Intros prefix suffix.
    Exists prefix suffix.
    entailer!.
Qed.

Lemma verification_slice_event_inv_merge_type_total :
  forall sg tskSt st eid,
    valid_event_id sg eid ->
    (event_addr sg eid + OSEventType_off) # UChar |->
      event_slot_type_value st eid **
    verification_slice_event_inv_no_type_at sg tskSt st eid |--
      verification_slice_event_inv sg tskSt st.
Proof.
  intros sg tskSt st eid Heid.
  unfold event_slot_type_value, verification_slice_event_inv_no_type_at.
  destruct (inUsedEventStates st eid) as [e |] eqn:Hslot.
  - eapply verification_slice_event_inv_used_merge_type; eauto.
  - Intros prefix suffix.
    sep_apply_l_atomic
      (verification_slice_event_inv_free_merge_type sg tskSt st eid prefix suffix).
    entailer!.
Qed.

Definition verification_slice_event_inv_missing_usedevent (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (st : Glob_EventAbstractState)
  (eid : EventID) (e : OSEventAbstractState) : Assertion :=
  coq_prop (verification_slice_event_in_range sg tskSt st) &&
  store_used_event_map_missing_i sg tskSt st.(inUsedEventStates) eid **
  used_complete_event sg tskSt (event_addr sg eid) eid e **
  store_free_event_list sg st.(unUsedEventStates).

(* verification_slice_event_inv_no_eid:verification_slice_event_inv 减去第 eid 个 record 的所有 cell(完全不留)。*)
(* 用于 OSMutexQuery 类函数的 spec 重构:precondition 用 verification_slice_event_inv_no_eid,    *)
(* 第 eid 个 record 的 cell 由 spec 中显式 data_at 给出(避免 SL 重叠)。       *)
(* 同时配 consistency Prop 链接 cell 值与 abstract state。                    *)
Definition verification_slice_event_inv_no_eid (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (st : Glob_EventAbstractState)
  (eid : EventID) : Assertion :=
  coq_prop (verification_slice_event_in_range sg tskSt st) &&
  store_used_event_map_missing_i sg tskSt st.(inUsedEventStates) eid **
  store_free_event_list sg st.(unUsedEventStates).

(* Residual after exposing both the mutex event and a distinct event on which
   its owner is blocked.  The two complete records are owned by the caller. *)
Definition verification_slice_event_inv_no_two_eids (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (st : Glob_EventAbstractState)
  (eid1 eid2 : EventID) : Assertion :=
  coq_prop (eid1 <> eid2 /\ verification_slice_event_in_range sg tskSt st) &&
  store_used_event_map_missing_two
    sg tskSt st.(inUsedEventStates) eid1 eid2 **
  store_free_event_list sg st.(unUsedEventStates).

(* Residual event invariant when the caller owns OSEventFreeList itself. *)
Definition verification_slice_event_inv_no_free_head (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (st : Glob_EventAbstractState) : Assertion :=
  coq_prop (verification_slice_event_in_range sg tskSt st) &&
  store_used_event_map sg tskSt st.(inUsedEventStates) **
  store_free_event_nodes sg st.(unUsedEventStates).

Definition event_free_head_snapshot_prop (sg : StableGlobVars)
  (st : Glob_EventAbstractState) (eid : EventID) (rest : list EventID)
  (head next : addr) : Prop :=
  st.(unUsedEventStates) = eid :: rest /\
  head = event_addr sg eid /\
  next = free_event_head sg rest.

Definition event_free_list_head_prop (sg : StableGlobVars)
  (st : Glob_EventAbstractState) (head : addr) : Prop :=
  head = free_event_head sg st.(unUsedEventStates).

Definition event_free_list_exact_prop (st : Glob_EventAbstractState)
  (free_ids : list EventID) : Prop :=
  st.(unUsedEventStates) = free_ids.

Definition event_deleted_snapshot_prop
  (before after : Glob_EventAbstractState)
  (eid : EventID) (e : OSEventAbstractState) : Prop :=
  before.(inUsedEventStates) eid = Some e /\
  after.(inUsedEventStates) eid = None /\
  after.(unUsedEventStates) = eid :: before.(unUsedEventStates) /\
  (forall other,
      other <> eid ->
      after.(inUsedEventStates) other = before.(inUsedEventStates) other).

Definition verification_slice_event_inv_free_head_rest (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (st : Glob_EventAbstractState)
  (rest : list EventID) : Assertion :=
  coq_prop (verification_slice_event_in_range sg tskSt st) &&
  store_used_event_map sg tskSt st.(inUsedEventStates) **
  store_free_event_nodes sg rest.

(* etype_consistency_prop:cell 值 etype 与 abstract state evSt 的一致性 Prop *)
(* - Some e 时:etype = encode e.(eventType)                                *)
(* - None  时:etype = encode UNUSED                                       *)
(* 这是 Prop-level 约束,非 SL assertion,避免精确 SL 的重叠问题。          *)
Definition etype_consistency_prop
  (evSt : Glob_EventAbstractState) (eid : EventID) (etype : Z) : Prop :=
  match evSt.(inUsedEventStates) eid with
  | Some e => etype = encode_event_type e.(eventType)
  | None   => etype = encode_event_type OS_EVENT_TYPE_UNUSED
  end.

(* ================================================================== *)
(* 2026-07-02:atomic_event_wait_list_init 完整 Qed 的脚手架            *)
(* ================================================================== *)

(* 关键:event_fields_consistency 在 waitList 设为 [] 时,无论 eventType 如何都保持 *)
Lemma event_fields_consistency_set_waitList_empty_weaken :
  forall e,
    event_fields_consistency e ->
    event_fields_consistency
      {| eventGeneration := e.(eventGeneration);
         eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19);
         eventType   := e.(eventType);
         mutexFields := e.(mutexFields);
         semFields   := e.(semFields);
         mboxFields  := e.(mboxFields);
         queueFields := e.(queueFields);
         waitList    := [];
      |}.
Proof.
  intros e H. unfold event_fields_consistency in *.
  destruct e.(eventType).
  - (* UNUSED *)
    simpl in H. destruct H as [Hm [Hs [Hmb [Hq Hwl]]]]. simpl.
    repeat split; assumption.
  - (* SEM *)
    simpl in H. destruct H as [Hm [Hs [Hmb Hq]]]. simpl.
    repeat split; assumption.
  - (* MUTEX *)
    simpl in H. destruct H as [Hm [Hs [Hmb Hq]]]. simpl.
    repeat split; assumption.
  - (* MBOX *)
    simpl in H. destruct H as [Hm [Hs [Hmb Hq]]]. simpl.
    repeat split; assumption.
  - (* Q *)
    simpl in H. destruct H as [Hm [Hs [Hmb Hq]]]. simpl.
    repeat split; assumption.
  - (* FLAG *)
    simpl in H. contradiction.
Qed.

Lemma event_payload_consistency_set_waitList_empty :
  forall sg e,
    event_payload_consistency sg e ->
    event_payload_consistency sg
      {| eventGeneration := e.(eventGeneration);
         eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19);
         eventType   := e.(eventType);
         mutexFields := e.(mutexFields);
         semFields   := e.(semFields);
         mboxFields  := e.(mboxFields);
         queueFields := e.(queueFields);
         waitList    := []; |}.
Proof.
  intros sg e Hpayload.
  unfold event_payload_consistency in *.
  destruct e.(eventType); simpl in *.
  - contradiction.
  - destruct e.(semFields) as [s |]; [| contradiction].
    unfold sem_fields_consistency in *. destruct Hpayload as [Hrange _].
    split; [exact Hrange |]. intros Hneq. exfalso. apply Hneq. reflexivity.
  - destruct e.(mutexFields) as [m |]; [| contradiction].
    destruct Hpayload as [Hm _]. split; [exact Hm |]. intros _. reflexivity.
  - destruct e.(mboxFields) as [m |]; [| contradiction].
    unfold mbox_fields_consistency in *. destruct Hpayload as [Hmsg _].
    split; [exact Hmsg |]. intros Hneq. exfalso. apply Hneq. reflexivity.
  - destruct e.(queueFields) as [q |]; [| contradiction].
    unfold queue_fields_consistency in *.
    destruct Hpayload as [Hqid [Hstart [Hsize [Hshape _]]]].
    split; [exact Hqid |].
    split; [exact Hstart |].
    split; [exact Hsize |].
    split; [exact Hshape |].
    intros Hneq. exfalso. apply Hneq. reflexivity.
  - contradiction.
Qed.

Lemma verification_slice_event_wait_entry_consistency_empty_waitList_general :
  forall sg tskSt eid ev,
    ev.(waitList) = [] ->
    verification_slice_event_wait_entry_consistency sg tskSt eid ev.
Proof.
  intros sg tskSt eid ev Hwl.
  unfold verification_slice_event_wait_entry_consistency, event_waitList_canonical.
  rewrite Hwl. split.
  - split. + constructor. + split. * simpl. exact I. * intros tid Hin. inversion Hin.
  - destruct ev.(eventType); simpl; try reflexivity; intros tid Hin; inversion Hin.
Qed.

Lemma verification_slice_event_wait_entry_consistency_set_waitList_empty :
  forall sg tskSt eid e,
    verification_slice_event_wait_entry_consistency sg tskSt eid
      {| eventGeneration := e.(eventGeneration);
         eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19);
         eventType   := e.(eventType);
         mutexFields := e.(mutexFields);
         semFields   := e.(semFields);
         mboxFields  := e.(mboxFields);
         queueFields := e.(queueFields);
         waitList    := [];
      |}.
Proof.
  intros sg tskSt eid e.
  unfold verification_slice_event_wait_entry_consistency, event_waitList_canonical.
  split.
  - split.
    + constructor.
    + split.
      * simpl. exact I.
      * intros tid Hin. inversion Hin.
  - destruct e.(eventType); simpl; try reflexivity; intros tid Hin; inversion Hin.
Qed.

(* verification_slice_event_in_range 在 mid 处把 waitList 设为 [] 时保持(任意 eventType) *)
Lemma verification_slice_event_in_range_preserved_by_waitList_empty :
  forall sg tskSt evSt mid e_old,
    evSt.(inUsedEventStates) mid = Some e_old ->
    verification_slice_event_in_range sg tskSt evSt ->
    verification_slice_event_in_range sg tskSt
      {| inUsedEventStates := fun eid => if Z.eqb eid mid
                                          then Some {| eventGeneration := e_old.(eventGeneration);
                                                       eventName := e_old.(eventName);
     eventPadding1 := e_old.(eventPadding1);
     eventPadding2 := e_old.(eventPadding2);
     eventPadding3 := e_old.(eventPadding3);
     eventPadding19 := e_old.(eventPadding19);
                                                       eventType   := e_old.(eventType);
                                                       mutexFields := e_old.(mutexFields);
                                                       semFields   := e_old.(semFields);
                                                       mboxFields  := e_old.(mboxFields);
                                                       queueFields := e_old.(queueFields);
                                                       waitList    := []; |}
                                          else evSt.(inUsedEventStates) eid;
         eventLifecycle := evSt.(eventLifecycle);
         publishedQueueBytes := evSt.(publishedQueueBytes);
         unUsedEventStates := evSt.(unUsedEventStates);
      |}.
Proof.
  intros sg tskSt evSt mid e_old Hget
    [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]].
  split.
  - intros eid0 ev0 Hget'. destruct (Z.eqb eid0 mid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst eid0. destruct (H1 mid e_old Hget) as [Hlo Hhi]. split; assumption.
    + simpl in Hget'. rewrite Heq in Hget'. destruct (H1 eid0 ev0 Hget') as [Hlo Hhi]. split; assumption.
  - split.
    + exact H2.
    + split.
      * exact H3.
      * split.
        { eapply event_slot_partition_preserved_some_to_some; eauto. }
        { split.
          { intros eid0 ev0 Hget'. destruct (Z.eqb eid0 mid) eqn:Heq.
            + apply Z.eqb_eq in Heq. subst eid0. simpl in Hget'. rewrite Z.eqb_refl in Hget'.
              inversion Hget'; subst. apply event_fields_consistency_set_waitList_empty_weaken.
              exact (H5 mid e_old Hget).
            + simpl in Hget'. rewrite Heq in Hget'. exact (H5 eid0 ev0 Hget'). }
          { split.
            { intros eid0 ev0 Hget'. destruct (Z.eqb eid0 mid) eqn:Heq.
              + apply Z.eqb_eq in Heq. subst eid0. simpl in Hget'. rewrite Z.eqb_refl in Hget'.
                inversion Hget'; subst. apply event_payload_consistency_set_waitList_empty.
                exact (H6 mid e_old Hget).
              + simpl in Hget'. rewrite Heq in Hget'.
                exact (H6 eid0 ev0 Hget'). }
            { split.
              { eapply queue_binding_unique_update_same_binding.
                + exact Hget.
                + reflexivity.
                + exact H7. }
              { intros eid0 ev0 Hget'. destruct (Z.eqb eid0 mid) eqn:Heq.
                + apply Z.eqb_eq in Heq. subst eid0. simpl in Hget'. rewrite Z.eqb_refl in Hget'.
                  inversion Hget'; subst. apply verification_slice_event_wait_entry_consistency_set_waitList_empty.
                + simpl in Hget'. rewrite Heq in Hget'. exact (H8 eid0 ev0 Hget'). } } } }
Qed.

(* verification_slice_event_in_range 在 mid 处把 mutexFields 的 owner 清零(并 waitList 设为 [])时保持。
   用于 atomic_mutex_del_no_pend_prepare 的 verification_slice_event_in_range 子目标。 *)
Lemma verification_slice_event_in_range_preserved_by_mutex_owner_clear :
  forall sg tskSt evSt mid e_old m_old,
    evSt.(inUsedEventStates) mid = Some e_old ->
    e_old.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e_old.(mutexFields) = Some m_old ->
    verification_slice_event_in_range sg tskSt evSt ->
    verification_slice_event_in_range sg tskSt
      {| inUsedEventStates := fun eid => if Z.eqb eid mid
                                          then Some {| eventGeneration := e_old.(eventGeneration);
                                                       eventName := e_old.(eventName);
     eventPadding1 := e_old.(eventPadding1);
     eventPadding2 := e_old.(eventPadding2);
     eventPadding3 := e_old.(eventPadding3);
     eventPadding19 := e_old.(eventPadding19);
                                                       eventType   := e_old.(eventType);
                                                       mutexFields := Some {| mfPCP := m_old.(mfPCP);
                                                                              mfOwner := None;
                                                                              mfOwnerOrigPrio := None; |};
                                                       semFields   := e_old.(semFields);
                                                       mboxFields  := e_old.(mboxFields);
                                                       queueFields := e_old.(queueFields);
                                                       waitList    := []; |}
                                          else evSt.(inUsedEventStates) eid;
         eventLifecycle := evSt.(eventLifecycle);
         publishedQueueBytes := evSt.(publishedQueueBytes);
         unUsedEventStates := evSt.(unUsedEventStates);
      |}.
Proof.
  intros sg tskSt evSt mid e_old m_old Hget Htype Hmf
    [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]].
  split.
  - intros eid0 ev0 Hget'. destruct (Z.eqb eid0 mid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst eid0. destruct (H1 mid e_old Hget) as [Hlo Hhi]. split; assumption.
    + simpl in Hget'. rewrite Heq in Hget'. destruct (H1 eid0 ev0 Hget') as [Hlo Hhi]. split; assumption.
  - split.
    + exact H2.
    + split.
      * exact H3.
      * split.
        { eapply event_slot_partition_preserved_some_to_some; eauto. }
        { split.
          { intros eid0 ev0 Hget'. destruct (Z.eqb eid0 mid) eqn:Heq.
            + apply Z.eqb_eq in Heq. subst eid0. simpl in Hget'. rewrite Z.eqb_refl in Hget'.
              inversion Hget'; subst. unfold event_fields_consistency.
              rewrite Htype. simpl. split; [| split; [| split]].
              * discriminate.
              * (* semFields = None *)
                pose proof (H5 mid e_old Hget) as Hefc_e1. unfold event_fields_consistency in Hefc_e1.
                rewrite Htype in Hefc_e1. simpl in Hefc_e1. destruct Hefc_e1 as [_ [Hs _]]. exact Hs.
              * (* mboxFields = None *)
                pose proof (H5 mid e_old Hget) as Hefc_e1. unfold event_fields_consistency in Hefc_e1.
                rewrite Htype in Hefc_e1. simpl in Hefc_e1. destruct Hefc_e1 as [_ [_ [Hmb _]]]. exact Hmb.
              * (* queueFields = None *)
                pose proof (H5 mid e_old Hget) as Hefc_e1. unfold event_fields_consistency in Hefc_e1.
                rewrite Htype in Hefc_e1. simpl in Hefc_e1. destruct Hefc_e1 as [_ [_ [_ Hq]]]. exact Hq.
            + simpl in Hget'. rewrite Heq in Hget'. exact (H5 eid0 ev0 Hget'). }
          { split.
            { intros eid0 ev0 Hget'. destruct (Z.eqb eid0 mid) eqn:Heq.
              + apply Z.eqb_eq in Heq. subst eid0. simpl in Hget'. rewrite Z.eqb_refl in Hget'.
                inversion Hget'; subst. unfold event_payload_consistency.
                rewrite Htype. simpl. split.
                * unfold mutex_fields_consistency. simpl. exact I.
                * intros _. reflexivity.
              + simpl in Hget'. rewrite Heq in Hget'.
                exact (H6 eid0 ev0 Hget'). }
            { split.
              { eapply queue_binding_unique_update_same_binding.
                + exact Hget.
                + unfold event_queue_id. rewrite Htype. reflexivity.
                + exact H7. }
              { intros eid0 ev0 Hget'. destruct (Z.eqb eid0 mid) eqn:Heq.
                + apply Z.eqb_eq in Heq. subst eid0. simpl in Hget'. rewrite Z.eqb_refl in Hget'.
                  inversion Hget'; subst. apply verification_slice_event_wait_entry_consistency_empty_waitList_general.
                  reflexivity.
                + simpl in Hget'. rewrite Heq in Hget'. exact (H8 eid0 ev0 Hget'). } } } }
Qed.

(* ================================================================== *)
(* 2026-07-04:OSEventCnt bit-decode helpers for OSMutexQuery_real     *)
(* cnt = pcp*256 + (0xFF or origPrio),symexec spec 用函数式语法引用  *)
(* ================================================================== *)

Definition decode_PCP_from_cnt (cnt : Z) : Z := unsigned_last_nbits (Z.shiftr cnt 8) 8.

Definition decode_OwnerPrio_from_cnt (cnt : Z) : Z := Z.land cnt 255.

Definition decode_OSValue_from_cnt (cnt : Z) : Z :=
  if Z.eqb (Z.land cnt 255) 255 then 1 else 0.

(** In-place publication retains every other slot and the free-list/queue
    storage. This is not an allocation or an event-lifetime theorem. *)
Lemma event_update_preserves_in_range_with_wait : forall sg entry events eid old new,
  event_in_range_with_wait sg events entry ->
  events.(inUsedEventStates) eid = Some old ->
  new.(eventGeneration) = old.(eventGeneration) ->
  event_fields_consistency new -> event_payload_consistency sg new ->
  event_queue_id new = event_queue_id old ->
  entry eid new ->
  event_in_range_with_wait sg (update_event_field_raw events eid new) entry.
Proof.
  intros sg entry events eid old new
    [Hpartition [Hfree [Hidentity [Hfields [Hpayload [Hqueue Hwait]]]]]]
    Hold Hgeneration HfieldsNew HpayloadNew HqidNew HwaitNew.
  destruct (event_pool_used_not_free sg events eid old Hpartition Hold)
    as [_ [_ Hprivate]].
  assert (HpartNew : event_pool_partition sg (update_event_field_raw events eid new)).
  { destruct Hpartition as [Hpool Hdisjoint].
    assert (Hslot : event_allocated_slots events eid = Some (inl old)).
    { unfold event_allocated_slots; rewrite Hprivate, Hold; reflexivity. }
    assert (Hslots : event_allocated_slots (update_event_field_raw events eid new) =
      kernel_map_set (event_allocated_slots events) eid (Some (inl new))).
    { apply functional_extensionality; intro i; unfold event_allocated_slots,
        update_event_field_raw; simpl; unfold kernel_map_set.
      destruct (Z.eq_dec i eid) as [->|Hne].
      - rewrite Z.eqb_refl, Hprivate; reflexivity.
      - assert (Hi : Z.eqb i eid = false) by (apply Z.eqb_neq; exact Hne).
        rewrite Hi; reflexivity. }
    split.
    - rewrite Hslots; eapply kernel_pool_replace_preserves_partition; eauto.
    - intros i a Hi; simpl in Hi |- *; destruct (Z.eqb i eid) eqn:E.
      + apply Z.eqb_eq in E; subst i; rewrite Hprivate in Hi; discriminate.
      + eapply Hdisjoint; exact Hi. }
  assert (HidentityNew : event_identity_valid (update_event_field_raw events eid new)).
  { eapply event_identity_valid_from_submap;
      [exact Hidentity|apply Nat.le_refl|apply Nat.le_refl| |].
    - intros i generation Hi; unfold event_slot_generation, event_allocated_slots,
        update_event_field_raw in Hi |- *; simpl in Hi.
      destruct (events.(eventLifecycle).(eventPrivate) i); [exact Hi|].
      destruct (Z.eqb i eid) eqn:E; [|exact Hi].
      apply Z.eqb_eq in E; subst i; rewrite Hold; simpl in Hi |- *.
      rewrite Hgeneration in Hi; exact Hi.
    - intros i invocation Hi; exact Hi. }
  split; [exact HpartNew|]. split; [exact Hfree|]. split; [exact HidentityNew|].
  split.
  - intros i e Hget; simpl in Hget; destruct (Z.eqb i eid) eqn:Hi.
    + injection Hget as He; subst e; exact HfieldsNew.
    + eapply Hfields; exact Hget.
  - split.
    + intros i e Hget; simpl in Hget; destruct (Z.eqb i eid).
      * injection Hget as He; subst e; exact HpayloadNew.
      * eapply Hpayload; exact Hget.
    + split.
      * intros i j ei ej q Hi Hj Hqi Hqj; simpl in Hi, Hj.
        destruct (Z.eqb i eid) eqn:Hiid; destruct (Z.eqb j eid) eqn:Hjid.
        -- apply Z.eqb_eq in Hiid; apply Z.eqb_eq in Hjid; congruence.
        -- apply Z.eqb_eq in Hiid; subst i; injection Hi as He; subst ei.
           rewrite HqidNew in Hqi; eapply Hqueue; eauto.
        -- apply Z.eqb_eq in Hjid; subst j; injection Hj as He; subst ej.
           rewrite HqidNew in Hqj; eapply Hqueue; eauto.
        -- eapply Hqueue; eauto.
      * intros i e Hget; simpl in Hget; destruct (Z.eqb i eid) eqn:Hi.
        -- apply Z.eqb_eq in Hi; subst i; injection Hget as He; subst e; exact HwaitNew.
        -- eapply Hwait; exact Hget.
Qed.

Lemma event_update_preserves_in_range : forall sg tasks events eid old new,
  event_in_range sg tasks events ->
  events.(inUsedEventStates) eid = Some old ->
  new.(eventGeneration) = old.(eventGeneration) ->
  event_fields_consistency new -> event_payload_consistency sg new ->
  event_queue_id new = event_queue_id old ->
  event_wait_entry_consistency sg tasks eid new ->
  event_in_range sg tasks (update_event_field_raw events eid new).
Proof. intros; eapply event_update_preserves_in_range_with_wait; eassumption. Qed.

Lemma event_set_name_preserves_in_range : forall sg tasks events eid old name,
  event_in_range sg tasks events -> events.(inUsedEventStates) eid = Some old ->
  event_in_range sg tasks
    (update_event_field_raw events eid (event_set_name old name)).
Proof.
  intros sg tasks events eid old name Hvalid Hget.
  pose proof Hvalid as [_ [_ [_ [Hfields [Hpayload [_ Hwait]]]]]].
  eapply event_update_preserves_in_range;
    [exact Hvalid|exact Hget|reflexivity|exact (Hfields eid old Hget)|
     exact (Hpayload eid old Hget)|reflexivity|exact (Hwait eid old Hget)].
Qed.

Definition event_raw_rep_no_eid (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (events : Glob_EventAbstractState) (eid : EventID) : Assertion :=
  store_map_missing_i (used_event_rep sg tasks) events.(inUsedEventStates) eid **
  event_free_storage_rep sg events ** event_free_root_rep sg events.

Lemma event_raw_rep_split_eid : forall sg tasks events eid e,
  events.(inUsedEventStates) eid = Some e ->
  event_raw_rep sg tasks events |--
  used_event_rep sg tasks eid e ** event_raw_rep_no_eid sg tasks events eid.
Proof.
  intros sg tasks events eid e Hget.
  unfold event_raw_rep, event_raw_rep_no_eid.
  sep_apply_l_atomic (store_map_split (used_event_rep sg tasks)
    eid e events.(inUsedEventStates) Hget); entailer!.
Qed.

Lemma event_raw_rep_merge_eid : forall sg tasks events eid e,
  events.(inUsedEventStates) eid = Some e ->
  used_event_rep sg tasks eid e ** event_raw_rep_no_eid sg tasks events eid |--
  event_raw_rep sg tasks events.
Proof.
  intros sg tasks events eid e Hget.
  unfold event_raw_rep, event_raw_rep_no_eid.
  eapply derivable1_trans with
    ((store_map_missing_i (used_event_rep sg tasks) events.(inUsedEventStates) eid **
      used_event_rep sg tasks eid e) **
      event_free_storage_rep sg events ** event_free_root_rep sg events).
  - entailer!.
  - apply derivable1s_sepcon_proper; [|reflexivity].
    apply derivable1s_sepcon_proper; [|reflexivity].
    apply store_map_merge; exact Hget.
Qed.

Lemma event_raw_rep_no_eid_update_equiv : forall sg tasks events eid e,
  event_raw_rep_no_eid sg tasks events eid --||--
  event_raw_rep_no_eid sg tasks (update_event_field_raw events eid e) eid.
Proof.
  intros sg tasks events eid e; unfold event_raw_rep_no_eid;
    cbn [update_event_field_raw].
  assert (Hframe : forall i, i <> eid ->
    events.(inUsedEventStates) i =
      (if Z.eqb i eid then Some e else events.(inUsedEventStates) i)).
  { intros i Hne; destruct (Z.eqb i eid) eqn:Hi; [apply Z.eqb_eq in Hi; contradiction|reflexivity]. }
  destruct (store_map_missing_i_equiv (used_event_rep sg tasks) _ _ eid Hframe)
    as [Hforward Hbackward].
  split; [sep_apply_l_atomic Hforward|sep_apply_l_atomic Hbackward]; entailer!.
Qed.

(** The new object's bytes, not the old value's wand, reconstitute an
    updated public event. Pure validity is a separate obligation. *)
Lemma event_raw_rep_merge_updated_eid : forall sg tasks events eid e,
  used_event_rep sg tasks eid e ** event_raw_rep_no_eid sg tasks events eid |--
  event_raw_rep sg tasks (update_event_field_raw events eid e).
Proof.
  intros sg tasks events eid e.
  sep_apply_l_atomic (proj1 (event_raw_rep_no_eid_update_equiv sg tasks events eid e)).
  sep_apply_l_atomic (event_raw_rep_merge_eid sg tasks
    (update_event_field_raw events eid e) eid e ltac:(simpl; rewrite Z.eqb_refl; reflexivity)).
  entailer!.
Qed.

Lemma event_update_unlisted_task_preserves_in_range : forall sg tasks events tid new,
  (forall eid e, events.(inUsedEventStates) eid = Some e -> ~ In tid e.(waitList)) ->
  event_in_range sg tasks events ->
  event_in_range sg (glob_task_set_usedtask tasks tid new) events.
Proof.
  intros sg tasks events tid new Habsent
    [Hpartition [Hfree [Hidentity [Hfields [Hpayload [Hqueue Hentries]]]]]].
  split; [exact Hpartition|]. split; [exact Hfree|]. split; [exact Hidentity|].
  split; [exact Hfields|]. split; [exact Hpayload|].
  split; [exact Hqueue|]. intros eid e He.
  apply event_wait_entry_update_unlisted_task; [eapply Habsent|eapply Hentries]; eauto.
Qed.

Lemma glob_task_set_usedtask_preserves_event_priority_agreement : forall tasks events tid old new,
  tasks.(inUsedTaskStates) tid = Some old -> new.(curPrio) = old.(curPrio) ->
  event_wait_priority_agreement tasks (glob_task_set_usedtask tasks tid new) events.
Proof.
  intros tasks events tid old new Hold Hprio eid e slot He Hin; symmetry.
  eapply glob_task_set_usedtask_observation; eauto.
Qed.

Lemma event_detach_head_preserves_in_range : forall sg tasks events eid rest image,
  event_in_range sg tasks events -> events.(unUsedEventStates) = eid :: rest ->
  event_in_range sg tasks (event_detach_head events eid rest image).
Proof.
  intros sg tasks events eid rest image
    [Hpart [Hfree [Hidentity [Hfields [Hpayload [Hqueue Hwait]]]]]] Hhead.
  split; [eapply event_detach_head_preserves_partition; eauto|].
  split; [eapply event_detach_head_preserves_free_storage; eauto|].
  split; [apply event_detach_head_preserves_identity; exact Hidentity|].
  split; [exact Hfields|]. split; [exact Hpayload|]. split; assumption.
Qed.

Lemma event_private_write_preserves_in_range : forall sg tasks events eid a field value,
  event_in_range sg tasks events -> events.(eventLifecycle).(eventPrivate) eid = Some a ->
  event_in_range sg tasks (event_private_write events eid a field value).
Proof.
  intros sg tasks events eid a field value [Hpart [Hfree [Hidentity Hpublished]]] Hget.
  split; [eapply event_private_write_preserves_partition; eauto|].
  split; [apply event_private_write_preserves_free_storage; exact Hfree|].
  split; [eapply event_private_write_preserves_identity; eauto|exact Hpublished].
Qed.

Lemma event_publish_preserves_in_range : forall sg tasks events eid a node,
  event_in_range sg tasks events -> events.(eventLifecycle).(eventPrivate) eid = Some a ->
  node.(eventGeneration) = a.(eventPrivateGeneration) ->
  event_fields_consistency node -> event_payload_consistency sg node ->
  (forall other old q, events.(inUsedEventStates) other = Some old ->
    event_queue_id node = Some q -> event_queue_id old <> Some q) ->
  event_wait_entry_consistency sg tasks eid node ->
  event_in_range sg tasks (event_publish events eid node).
Proof.
  intros sg tasks events eid a node
    [Hpart [Hfree [Hidentity [Hfields [Hpayload [Hqueue Hwait]]]]]]
    Hget Hgeneration HfieldsNew HpayloadNew Hfresh HwaitNew.
  split; [eapply event_publish_preserves_partition; eauto|].
  split; [apply event_publish_preserves_free_storage; exact Hfree|].
  split; [eapply event_publish_preserves_identity; eauto|].
  split.
  - intros i e Hi; simpl in Hi; unfold kernel_map_set in Hi.
    destruct (Z.eq_dec i eid); [injection Hi as He; subst e; exact HfieldsNew|eapply Hfields; eauto].
  - split.
    + intros i e Hi; simpl in Hi; unfold kernel_map_set in Hi.
      destruct (Z.eq_dec i eid); [injection Hi as He; subst e; exact HpayloadNew|eapply Hpayload; eauto].
    + split.
      * intros i j ei ej q Hi Hj Hqi Hqj; simpl in Hi, Hj; unfold kernel_map_set in Hi, Hj.
        destruct (Z.eq_dec i eid) as [->|Hine]; destruct (Z.eq_dec j eid) as [->|Hjne].
        -- reflexivity.
        -- injection Hi as He; subst ei; exfalso; eapply Hfresh; eauto.
        -- injection Hj as He; subst ej; exfalso; eapply Hfresh; eauto.
        -- eapply Hqueue; eauto.
      * intros i e Hi; simpl in Hi; unfold kernel_map_set in Hi.
        destruct (Z.eq_dec i eid) as [->|Hne].
        -- injection Hi as He; subst e; exact HwaitNew.
        -- eapply Hwait; eauto.
Qed.

Lemma event_recycle_preserves_in_range : forall sg tasks events eid node image,
  event_in_range sg tasks events -> events.(inUsedEventStates) eid = Some node ->
  event_in_range sg tasks (event_recycle sg events eid image).
Proof.
  intros sg tasks events eid node image
    [Hpart [Hfree [Hidentity [Hfields [Hpayload [Hqueue Hwait]]]]]] Hget.
  split; [eapply event_recycle_preserves_partition; eauto|].
  split; [apply event_recycle_preserves_free_storage; exact Hfree|].
  split; [apply event_recycle_preserves_identity; exact Hidentity|].
  split.
  - intros i e Hi; simpl in Hi; unfold kernel_map_set in Hi.
    destruct (Z.eq_dec i eid); [discriminate|eapply Hfields; eauto].
  - split.
    + intros i e Hi; simpl in Hi; unfold kernel_map_set in Hi.
      destruct (Z.eq_dec i eid); [discriminate|eapply Hpayload; eauto].
    + split.
      * intros i j ei ej q Hi Hj Hqi Hqj; simpl in Hi, Hj; unfold kernel_map_set in Hi, Hj.
        destruct (Z.eq_dec i eid); [discriminate|].
        destruct (Z.eq_dec j eid); [discriminate|]. eapply Hqueue; eauto.
      * intros i e Hi; simpl in Hi; unfold kernel_map_set in Hi.
        destruct (Z.eq_dec i eid); [discriminate|eapply Hwait; eauto].
Qed.

Lemma event_detach_head_reconstructs_raw_rep : forall sg tasks events eid rest image,
  events.(eventLifecycle).(eventFreeStorage) eid = Some image ->
  store_map (used_event_rep sg tasks) events.(inUsedEventStates) **
  event_free_storage_rep sg events **
  sg.(g_OSEventFreeList) # Ptr |-> event_encode_pool_link sg (hd_error rest) |--
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image **
  event_raw_rep sg tasks (event_detach_head events eid rest image).
Proof.
  intros sg tasks events eid rest image Hget.
  sep_apply (event_detach_head_reconstructs_storage sg events eid rest image Hget).
  unfold event_raw_rep; simpl; entailer!.
Qed.

(** The entire private image must already match the initialized payload;
    this resource transfer does not stand in for the preceding C stores. *)
Lemma event_publish_reconstructs_raw_rep_on_fields : forall sg tasks events eid a node,
  event_pool_partition sg events -> events.(eventLifecycle).(eventPrivate) eid = Some a ->
  (forall field, In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
    a.(eventPrivateStorage) field = event_image sg tasks node field) ->
  event_private_storage_rep sg eid a ** event_raw_rep sg tasks events |--
  event_raw_rep sg tasks (event_publish events eid node).
Proof.
  intros sg tasks events eid a node Hpart Hget Himage.
  destruct (event_pool_private_not_free sg events eid a Hpart Hget) as [_ [_ Hnone]].
  assert (Hnode : event_private_storage_rep sg eid a = used_event_rep sg tasks eid node).
  { unfold event_private_storage_rep, used_event_rep;
      apply event_storage_rep_ext; exact Himage. }
  assert (Hmerge : used_event_rep sg tasks eid node **
    store_map (used_event_rep sg tasks) events.(inUsedEventStates) |--
    store_map (used_event_rep sg tasks)
      (kernel_map_set events.(inUsedEventStates) eid (Some node))).
  { sep_apply (store_map_equiv_store_map_missing (used_event_rep sg tasks) _ eid Hnone).
    sep_apply (proj1 (store_map_missing_i_equiv (used_event_rep sg tasks)
      events.(inUsedEventStates) (kernel_map_set events.(inUsedEventStates) eid (Some node)) eid
      ltac:(intros; symmetry; apply kernel_map_set_other; assumption))).
    sep_apply (store_map_merge (used_event_rep sg tasks) eid node _
      (kernel_map_set_same _ events.(inUsedEventStates) eid (Some node))); entailer!. }
  rewrite Hnode; unfold event_raw_rep; cbn [event_publish].
  sep_apply Hmerge; entailer!.
Qed.

(** Exact-image callers retain their interface.  Names-disabled creators
    use the field-extensional rule above: no nonexistent Name cell needs
    initialization, while all real fields including padding still match. *)
Lemma event_publish_reconstructs_raw_rep : forall sg tasks events eid a node,
  event_pool_partition sg events -> events.(eventLifecycle).(eventPrivate) eid = Some a ->
  a.(eventPrivateStorage) = event_image sg tasks node ->
  event_private_storage_rep sg eid a ** event_raw_rep sg tasks events |--
  event_raw_rep sg tasks (event_publish events eid node).
Proof.
  intros; eapply event_publish_reconstructs_raw_rep_on_fields;
    [eassumption|eassumption|intros field Hin; rewrite H1; reflexivity].
Qed.

(** The deleted object's Type/Ptr/Cnt and the root have already been
    updated.  The residual excludes its old public image, so the same
    bytes cannot be counted both in the live map and the free pool. *)
Lemma event_recycle_reconstructs_raw_rep : forall sg tasks events eid node image,
  event_pool_partition sg events -> event_free_storage_valid sg events ->
  events.(inUsedEventStates) eid = Some node ->
  store_map_missing_i (used_event_rep sg tasks) events.(inUsedEventStates) eid **
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    (event_recycle_image sg events.(unUsedEventStates) image) **
  event_free_storage_rep sg events **
  sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid |--
  event_raw_rep sg tasks (event_recycle sg events eid image).
Proof.
  intros sg tasks events eid node image Hpart Hfree Hget.
  sep_apply (proj1 (store_map_missing_i_equiv (used_event_rep sg tasks)
    events.(inUsedEventStates) (kernel_map_set events.(inUsedEventStates) eid None) eid
    ltac:(intros; symmetry; apply kernel_map_set_other; assumption))).
  sep_apply (store_map_missing_equiv_store_map (used_event_rep sg tasks)
    (kernel_map_set events.(inUsedEventStates) eid None) eid
    (kernel_map_set_same _ events.(inUsedEventStates) eid None)).
  sep_apply (event_recycle_reconstructs_free_storage sg events eid node image Hpart Hfree Hget).
  unfold event_raw_rep; simpl; entailer!.
Qed.

Lemma event_fields_consistency_remove_waiter : forall e tid,
  event_fields_consistency e ->
  event_fields_consistency (event_set_wait_list e (remove_Z_eqb tid e.(waitList))).
Proof.
  intros e tid Hfields; unfold event_fields_consistency in *; simpl.
  destruct e.(eventType); try exact Hfields.
  destruct Hfields as [Hm [Hs [Hb [Hq Hempty]]]].
  rewrite Hempty; repeat split; assumption.
Qed.

Lemma event_remove_waiter_preserves_in_range : forall sg tasks events eid e tid,
  event_in_range sg tasks events -> events.(inUsedEventStates) eid = Some e ->
  In tid e.(waitList) ->
  event_in_range sg tasks
    (update_event_field_raw events eid (event_set_wait_list e (remove_Z_eqb tid e.(waitList)))).
Proof.
  intros sg tasks events eid e tid Hvalid He Hin.
  pose proof Hvalid as [_ [_ [_ [Hfields [Hpayload [_ Hentries]]]]]].
  eapply event_update_preserves_in_range; [exact Hvalid|exact He|reflexivity| | |reflexivity|].
  - apply event_fields_consistency_remove_waiter; eapply Hfields; exact He.
  - apply event_payload_consistency_remove_waiter; [exact Hin|eapply Hpayload; exact He].
  - apply event_wait_entry_remove_waiter; eapply Hentries; exact He.
Qed.

(** In the single-Event profile, a registered waiter occurs only in its
    own Event.  This is derived from actual TCB backlinks, not an extra
    freshness premise supplied by a wake caller. *)
Lemma event_remove_waiter_absent : forall sg tasks events eid e tid,
  (forall slot node, events.(inUsedEventStates) slot = Some node ->
    event_wait_entry_consistency sg tasks slot node) ->
  events.(inUsedEventStates) eid = Some e -> In tid e.(waitList) ->
  forall slot node,
    (update_event_field_raw events eid
      (event_set_wait_list e (remove_Z_eqb tid e.(waitList)))).(inUsedEventStates) slot = Some node ->
    ~ In tid node.(waitList).
Proof.
  intros sg tasks events eid e tid Hentries He Hin slot node Hnode.
  simpl in Hnode; destruct (Z.eqb slot eid) eqn:E.
  - injection Hnode as Hnode; subst node; apply remove_Z_eqb_notin.
  - apply Z.eqb_neq in E; intro Hmember; apply E.
    eapply event_waiter_unique_event; eauto.
Qed.

Lemma event_remove_waiter_update_task_preserves_in_range :
  forall sg tasks events eid e tid new,
    event_in_range sg tasks events -> events.(inUsedEventStates) eid = Some e ->
    In tid e.(waitList) ->
    event_in_range sg (glob_task_set_usedtask tasks tid new)
      (update_event_field_raw events eid (event_set_wait_list e (remove_Z_eqb tid e.(waitList)))).
Proof.
  intros sg tasks events eid e tid new Hvalid He Hin.
  eapply event_update_unlisted_task_preserves_in_range.
  - eapply event_remove_waiter_absent; [|exact He|exact Hin].
    destruct Hvalid as [_ [_ [_ [_ [_ [_ Hentries]]]]]]; exact Hentries.
  - eapply event_remove_waiter_preserves_in_range; eauto.
Qed.

(** Endpoint of single-Event unlink plus TCB pointer cleanup.  Payload,
    lifecycle, allocation identity and all other Task fields are framed by
    their own owners.  No stable invariant is asserted between the stores. *)
Lemma event_wait_object_remove_update_task : forall sg s eid e tid new,
  event_wait_object_consistency sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> In tid e.(waitList) ->
  new.(eventPtr) = None -> new.(eventMultiWaitEvents) = [] ->
  event_wait_object_consistency sg
    (replace_EventS
      (update_event_field_raw s.(EventState) eid (event_set_wait_list e (remove_Z_eqb tid e.(waitList))))
      (replace_TskS (glob_task_set_usedtask s.(TskState) tid new) s)).
Proof.
  intros sg s eid e tid new [Hentries [Hback Hclosed]] He Hin Hnull Hmulti.
  assert (HbackNew : task_event_reference_backlink_consistency
    (glob_task_set_usedtask s.(TskState) tid new)
    (update_event_field_raw s.(EventState) eid (event_set_wait_list e (remove_Z_eqb tid e.(waitList))))).
  { intros slot t object node Ht Hnode Href.
    simpl in Ht, Hnode; destruct (Z.eqb slot tid) eqn:Etask.
    - injection Ht as Ht; subst t; rewrite Hnull, Hmulti in Href.
      destruct Href; [discriminate|contradiction].
    - apply Z.eqb_neq in Etask; destruct (Z.eqb object eid) eqn:Eevent.
      + apply Z.eqb_eq in Eevent; subst object; injection Hnode as Hnode; subst node.
        apply remove_Z_eqb_in_neq; [exact Etask|eapply Hback; eauto].
      + eapply Hback; eauto. }
  split.
  - intros slot node Hnode; simpl in Hnode; destruct (Z.eqb slot eid) eqn:E.
    + apply Z.eqb_eq in E; subst slot; injection Hnode as Hnode; subst node.
      apply event_wait_entry_remove_update_task; eapply Hentries; exact He.
    + apply Z.eqb_neq in E; apply event_wait_entry_update_unlisted_task.
      * intro Hmember; apply E; eapply event_waiter_unique_event; eauto.
      * eapply Hentries; exact Hnode.
  - split; [exact HbackNew|].
    intros slot t Ht; simpl in Ht; destruct (Z.eqb slot tid) eqn:E.
    + injection Ht as Ht; subst t; rewrite Hnull, Hmulti; split; intros object Href;
        [discriminate|contradiction].
    + destruct (Hclosed slot t Ht) as [HsingleClosed HmultiClosed].
      assert (Hlive : forall object,
        (exists node, s.(EventState).(inUsedEventStates) object = Some node) ->
        exists node, (update_event_field_raw s.(EventState) eid
          (event_set_wait_list e (remove_Z_eqb tid e.(waitList)))).(inUsedEventStates) object = Some node).
      { intros object [node Hnode]; simpl; destruct (Z.eqb object eid); eauto. }
      split; intros object Href; apply Hlive; [apply HsingleClosed|apply HmultiClosed]; exact Href.
Qed.

(** The source's EventGrp test agrees with list emptiness on the canonical
    representation.  Reuse the Scheduler encoding's existing head-bit
    proof rather than another bit-arithmetic implementation. *)
Lemma encode_event_wait_grp_zero_iff_empty : forall sg tasks waiters,
  event_waitList_canonical sg tasks waiters ->
  (encode_event_wait_grp waiters tasks = 0 <-> waiters = []).
Proof.
  intros sg tasks [|head tail] Hcanonical; [simpl; tauto|].
  split; [|discriminate].
  intros Hzero; destruct Hcanonical as [_ [_ Hmembers]].
  destruct (Hmembers head (or_introl eq_refl)) as [t [Ht Hprio]].
  pose proof (sched_group_head_bit head tail tasks t Ht
    (proj1 Hprio)) as Hbit.
  change (encode_ready_grp (head :: tail) tasks = 0) in Hzero.
  rewrite Hzero, Z.land_0_l in Hbit; contradiction.
Qed.

(** Literal two-level OSUnMapTbl expression for OS_LOWEST_PRIO <= 63.
    A zero bitmap still decodes exactly as the source does; nonemptiness
    belongs to the internal caller's contract, not a fabricated C guard. *)
Definition event_wait_priority (tasks : Glob_TaskAbstractState)
  (e : OSEventAbstractState) : Z :=
  let row := unmap_value (encode_event_wait_grp e.(waitList) tasks) in
  row * 8 + unmap_value (encode_event_wait_tbl_at_or e.(waitList) tasks row).

Lemma event_wait_priority_head_eq : forall sg tasks e head tail t,
  valid_stable_glob_vars sg -> event_waitList_canonical sg tasks e.(waitList) ->
  e.(waitList) = head :: tail -> tasks.(inUsedTaskStates) head = Some t ->
  event_wait_priority tasks e = t.(curPrio).
Proof.
  intros sg tasks e head tail t Hsg Hcanonical Hlist Hhead.
  destruct Hcanonical as [Hnd [Hsorted Hmembers]].
  rewrite Hlist in Hsorted, Hmembers.
  destruct (Hmembers head (or_introl eq_refl)) as [found [Hfound Hprio]].
  assert (found = t) by congruence; subst found.
  destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]].
  unfold event_wait_priority; rewrite Hlist.
  change (let row := unmap_value (encode_ready_grp (head :: tail) tasks) in
    row * 8 + unmap_value (encode_ready_tbl_at_or (head :: tail) tasks row) = t.(curPrio)).
  eapply sched_unmap_minimum_priority; [exact Hhead| | |].
  - unfold valid_task_prio in Hprio; lia.
  - intros tid other Hin Hget; destruct (Hmembers tid Hin) as [node [Hnode Hrange]].
    assert (node = other) by congruence; subst node; unfold valid_task_prio in Hrange; lia.
  - intros tid other Hin Hget.
    pose proof (sched_sorted_head_le TaskID (wait_prio_key sg tasks)
      head tail tid Hsorted Hin) as Hle.
    unfold wait_prio_key in Hle; rewrite Hhead, Hget in Hle; exact Hle.
Qed.

(** This closes the identity chain from Event bitmap to the actual
    OSTCBPrioTbl slot; no arbitrary owner is assumed equal to the waiter. *)
Lemma event_wait_priority_table_entry : forall sg tasks eid e head tail,
  valid_stable_glob_vars sg -> task_in_range sg tasks ->
  event_wait_entry_consistency sg tasks eid e -> e.(waitList) = head :: tail ->
  exists t, tasks.(inUsedTaskStates) head = Some t /\
    event_wait_priority tasks e = t.(curPrio) /\
    tasks.(prioTbl) (event_wait_priority tasks e) = PTTask head.
Proof.
  intros sg tasks eid e head tail Hsg Htasks [Hcanonical Hphase] Hlist.
  pose proof Hcanonical as [_ [_ Hmembers]].
  assert (Hin : In head e.(waitList)) by (rewrite Hlist; left; reflexivity).
  destruct (Hmembers head Hin) as [t [Ht Hprio]].
  pose proof (event_wait_priority_head_eq sg tasks e head tail t Hsg Hcanonical Hlist Ht) as Hdecoded.
  exists t; split; [exact Ht|]; split; [exact Hdecoded|]; rewrite Hdecoded.
  destruct Htasks as [_ [_ [_ [_ [_ [Hregistered _]]]]]]; exact (Hregistered head t Ht).
Qed.

(** These equations need a canonical bitmap and the actual TCB priority,
    not membership or the linked-wait phase.  Clearing an already absent
    waiter is needed for repeated entries in RemoveMulti.  OS_EventTaskRdy
    has already changed Stat/StatPend before entering Remove. *)
Lemma event_remove_waiter_bitmap_eq : forall sg tasks e tid t,
  valid_stable_glob_vars sg -> task_priority_unique tasks ->
  event_waitList_canonical sg tasks e.(waitList) ->
  valid_task_prio sg t.(curPrio) -> tasks.(inUsedTaskStates) tid = Some t ->
  encode_event_wait_grp (remove_Z_eqb tid e.(waitList)) tasks =
    (let cleared := Z.land (encode_event_wait_tbl_at_or e.(waitList) tasks (t.(curPrio) / 8))
       (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (t.(curPrio) mod 8))) 8) in
     if Z.eqb cleared 0
     then Z.land (encode_event_wait_grp e.(waitList) tasks)
       (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (t.(curPrio) / 8))) 8)
     else encode_event_wait_grp e.(waitList) tasks) /\
  forall row, encode_event_wait_tbl_at_or (remove_Z_eqb tid e.(waitList)) tasks row =
    if Z.eqb row (t.(curPrio) / 8)
    then Z.land (encode_event_wait_tbl_at_or e.(waitList) tasks row)
      (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (t.(curPrio) mod 8))) 8)
    else encode_event_wait_tbl_at_or e.(waitList) tasks row.
Proof.
  intros sg tasks e tid t Hsg Hunique [Hnd [Hsorted Hmembers]] Hprio Ht.
  assert (Hrange : forall slot node, In slot e.(waitList) ->
    tasks.(inUsedTaskStates) slot = Some node -> 0 <= node.(curPrio) < 64).
  { intros slot node Hmember Hnode.
    destruct (Hmembers slot Hmember) as [found [Hfound Hmember_prio]].
    assert (found = node) by congruence; subst found.
    destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]].
    unfold valid_task_prio in Hmember_prio; lia. }
  assert (Hnonnegative : forall slot node, In slot e.(waitList) ->
    tasks.(inUsedTaskStates) slot = Some node -> 0 <= node.(curPrio)).
  { intros; exact (proj1 (Hrange _ _ H H0)). }
  pose proof (proj1 Hprio) as Htask_nonnegative.
  assert (Htask_row : 0 <= t.(curPrio) / 8 < 8).
  { destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]].
    unfold valid_task_prio in Hprio.
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  split.
  - eapply encode_ready_grp_remove_waiter_any; try eassumption.
    intros slot node Hmember Hnode; pose proof (Hrange slot node Hmember Hnode).
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia.
  - intro row; destruct (Z.eqb row (t.(curPrio) / 8)) eqn:E.
    + apply Z.eqb_eq in E; subst row.
      eapply encode_ready_tbl_or_remove_selected_row_any; eassumption.
    + apply Z.eqb_neq in E.
      eapply encode_ready_tbl_or_remove_other_row; [exact Ht|congruence].
Qed.

Lemma event_table_image_eq : forall sg tasks e row,
  0 <= row < 8 ->
  event_image sg tasks e (event_table_field row) =
    Some (encode_event_wait_tbl_at_or e.(waitList) tasks row).
Proof.
  intros sg tasks e row Hrow.
  assert (Hcases : row = 0 \/ row = 1 \/ row = 2 \/ row = 3 \/
    row = 4 \/ row = 5 \/ row = 6 \/ row = 7) by lia.
  repeat destruct Hcases as [Hcases|Hcases]; subst row; reflexivity.
Qed.

(** Exact ECB image after the table-row store and conditional group store.
    The Type/Ptr/Cnt/Name and padding cells are left untouched. *)
Lemma event_remove_waiter_image_eq : forall sg tasks e tid t,
  valid_stable_glob_vars sg -> task_priority_unique tasks ->
  event_waitList_canonical sg tasks e.(waitList) ->
  valid_task_prio sg t.(curPrio) -> tasks.(inUsedTaskStates) tid = Some t ->
  event_image sg tasks (event_set_wait_list e (remove_Z_eqb tid e.(waitList))) =
    event_clear_waiter (event_image sg tasks e)
      (t.(curPrio) / 8) (encode_event_wait_tbl_at_or e.(waitList) tasks (t.(curPrio) / 8))
      (encode_event_wait_grp e.(waitList) tasks)
      (Z.shiftl 1 (t.(curPrio) mod 8)) (Z.shiftl 1 (t.(curPrio) / 8)).
Proof.
  intros sg tasks e tid t Hsg Hunique Hcanonical Hprio Ht.
  destruct (event_remove_waiter_bitmap_eq sg tasks e tid t Hsg Hunique Hcanonical Hprio Ht)
    as [Hgroup Htable].
  assert (Hrow : 0 <= t.(curPrio) / 8 < 8).
  { destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]].
    unfold valid_task_prio in Hprio.
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  set (written := event_clear_waiter (event_image sg tasks e)
    (t.(curPrio) / 8) (encode_event_wait_tbl_at_or e.(waitList) tasks (t.(curPrio) / 8))
    (encode_event_wait_grp e.(waitList) tasks)
    (Z.shiftl 1 (t.(curPrio) mod 8)) (Z.shiftl 1 (t.(curPrio) / 8))).
  assert (Htables : forall row, 0 <= row < 8 ->
    event_image sg tasks (event_set_wait_list e (remove_Z_eqb tid e.(waitList)))
      (event_table_field row) = written (event_table_field row)).
  { intros row Hbounded; unfold written.
    rewrite event_clear_waiter_table_field_eq by assumption.
    rewrite !event_table_image_eq by assumption; simpl; rewrite Htable.
    destruct (Z.eqb row (t.(curPrio) / 8)) eqn:E; [|reflexivity].
    apply Z.eqb_eq in E; subst row; reflexivity. }
  assert (Hgroup_image :
    event_image sg tasks (event_set_wait_list e (remove_Z_eqb tid e.(waitList)))
      EventGrpField = written EventGrpField).
  { unfold written; rewrite event_clear_waiter_group_field_eq by reflexivity.
    change (Some (encode_event_wait_grp (remove_Z_eqb tid e.(waitList)) tasks) =
      Some (if Z.eqb
        (Z.land (encode_event_wait_tbl_at_or e.(waitList) tasks (t.(curPrio) / 8))
          (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (t.(curPrio) mod 8))) 8)) 0
        then Z.land (encode_event_wait_grp e.(waitList) tasks)
          (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (t.(curPrio) / 8))) 8)
        else encode_event_wait_grp e.(waitList) tasks)).
    f_equal; exact Hgroup. }
  assert (Hother : forall field,
    event_field_offset field < 11 \/ 18 < event_field_offset field ->
    field <> EventGrpField -> written field = event_image sg tasks e field).
  { intros field Hoffset Hgroup_ne; unfold written.
    apply event_clear_waiter_unwritten_field_eq; [|exact Hgroup_ne].
    intro Heq; apply (f_equal event_field_offset) in Heq.
    rewrite event_table_field_offset_eq in Heq by exact Hrow; lia. }
  apply functional_extensionality; intro field; destruct field;
    try (apply Hgroup_image);
    try (apply (Htables 0); lia);
    try (apply (Htables 1); lia);
    try (apply (Htables 2); lia);
    try (apply (Htables 3); lia);
    try (apply (Htables 4); lia);
    try (apply (Htables 5); lia);
    try (apply (Htables 6); lia);
    try (apply (Htables 7); lia);
    rewrite Hother by (simpl; lia || discriminate);
    reflexivity.
Qed.

(** The premise is the storage actually obtained after the ECB stores,
    together with the original map residual.  No heap update is inferred
    merely from the abstract list removal. *)
Lemma event_remove_waiter_reconstructs_raw_rep : forall sg tasks events eid e tid t,
  valid_stable_glob_vars sg -> task_priority_unique tasks ->
  event_waitList_canonical sg tasks e.(waitList) ->
  valid_task_prio sg t.(curPrio) -> tasks.(inUsedTaskStates) tid = Some t ->
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_clear_waiter (event_image sg tasks e)
      (t.(curPrio) / 8) (encode_event_wait_tbl_at_or e.(waitList) tasks (t.(curPrio) / 8))
      (encode_event_wait_grp e.(waitList) tasks)
      (Z.shiftl 1 (t.(curPrio) mod 8)) (Z.shiftl 1 (t.(curPrio) / 8))) **
    event_raw_rep_no_eid sg tasks events eid |--
  event_raw_rep sg tasks
    (update_event_field_raw events eid (event_set_wait_list e (remove_Z_eqb tid e.(waitList)))).
Proof.
  intros sg tasks events eid e tid t Hsg Hunique Hcanonical Hprio Ht.
  rewrite <- (event_remove_waiter_image_eq sg tasks e tid t Hsg Hunique Hcanonical Hprio Ht).
  apply event_raw_rep_merge_updated_eid.
Qed.

Lemma event_insert_waiter_bitmap_eq : forall sg tasks e tid t,
  tasks.(inUsedTaskStates) tid = Some t ->
  encode_event_wait_grp (event_insert_waiter sg tasks e tid).(waitList) tasks =
    Z.lor (encode_event_wait_grp e.(waitList) tasks) (Z.shiftl 1 (t.(curPrio) / 8)) /\
  forall row, encode_event_wait_tbl_at_or (event_insert_waiter sg tasks e tid).(waitList) tasks row =
    if Z.eqb (t.(curPrio) / 8) row
    then Z.lor (encode_event_wait_tbl_at_or e.(waitList) tasks row) (Z.shiftl 1 (t.(curPrio) mod 8))
    else encode_event_wait_tbl_at_or e.(waitList) tasks row.
Proof.
  intros sg tasks e tid t Ht; split.
  - eapply encode_ready_grp_insert_remove; exact Ht.
  - intro row; eapply encode_ready_tbl_insert_remove; exact Ht.
Qed.

(** The two source OR stores are enough for the exact new ECB image;
    canonical membership and payload validity are separate obligations. *)
Lemma event_insert_waiter_image_eq : forall sg tasks e tid t,
  tasks.(inUsedTaskStates) tid = Some t -> 0 <= t.(curPrio) / 8 < 8 ->
  event_image sg tasks (event_insert_waiter sg tasks e tid) =
    event_mark_waiter (event_image sg tasks e)
      (t.(curPrio) / 8) (encode_event_wait_tbl_at_or e.(waitList) tasks (t.(curPrio) / 8))
      (encode_event_wait_grp e.(waitList) tasks)
      (Z.shiftl 1 (t.(curPrio) mod 8)) (Z.shiftl 1 (t.(curPrio) / 8)).
Proof.
  intros sg tasks e tid t Ht Hrow.
  destruct (event_insert_waiter_bitmap_eq sg tasks e tid t Ht) as [Hgroup Htable].
  set (written := event_mark_waiter (event_image sg tasks e)
    (t.(curPrio) / 8) (encode_event_wait_tbl_at_or e.(waitList) tasks (t.(curPrio) / 8))
    (encode_event_wait_grp e.(waitList) tasks)
    (Z.shiftl 1 (t.(curPrio) mod 8)) (Z.shiftl 1 (t.(curPrio) / 8))).
  assert (Htables : forall row, 0 <= row < 8 ->
    event_image sg tasks (event_insert_waiter sg tasks e tid) (event_table_field row) =
      written (event_table_field row)).
  { intros row Hbounded; unfold written.
    rewrite event_mark_waiter_table_field_eq by assumption.
    rewrite !event_table_image_eq by assumption.
    rewrite Htable, (Z.eqb_sym (t.(curPrio) / 8) row).
    destruct (Z.eqb row (t.(curPrio) / 8)) eqn:E; [|reflexivity].
    apply Z.eqb_eq in E; subst row; reflexivity. }
  assert (Hgroup_image : event_image sg tasks (event_insert_waiter sg tasks e tid) EventGrpField =
    written EventGrpField).
  { unfold written; rewrite event_mark_waiter_group_field_eq.
    change (Some (encode_event_wait_grp (event_insert_waiter sg tasks e tid).(waitList) tasks) =
      Some (Z.lor (encode_event_wait_grp e.(waitList) tasks) (Z.shiftl 1 (t.(curPrio) / 8)))).
    f_equal; exact Hgroup. }
  assert (Hother : forall field,
    event_field_offset field < 11 \/ 18 < event_field_offset field ->
    field <> EventGrpField -> written field = event_image sg tasks e field).
  { intros field Hoffset Hgroup_ne; unfold written.
    apply event_mark_waiter_unwritten_field_eq; [|exact Hgroup_ne].
    intro Heq; apply (f_equal event_field_offset) in Heq.
    rewrite event_table_field_offset_eq in Heq by exact Hrow; lia. }
  apply functional_extensionality; intro field; destruct field;
    try (apply Hgroup_image);
    try (apply (Htables 0); lia);
    try (apply (Htables 1); lia);
    try (apply (Htables 2); lia);
    try (apply (Htables 3); lia);
    try (apply (Htables 4); lia);
    try (apply (Htables 5); lia);
    try (apply (Htables 6); lia);
    try (apply (Htables 7); lia);
    rewrite Hother by (simpl; lia || discriminate); reflexivity.
Qed.

Lemma event_insert_waiter_reconstructs_raw_rep : forall sg tasks events eid e tid t,
  tasks.(inUsedTaskStates) tid = Some t -> 0 <= t.(curPrio) / 8 < 8 ->
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_mark_waiter (event_image sg tasks e)
      (t.(curPrio) / 8) (encode_event_wait_tbl_at_or e.(waitList) tasks (t.(curPrio) / 8))
      (encode_event_wait_grp e.(waitList) tasks)
      (Z.shiftl 1 (t.(curPrio) mod 8)) (Z.shiftl 1 (t.(curPrio) / 8))) **
    event_raw_rep_no_eid sg tasks events eid |--
  event_raw_rep sg tasks (update_event_field_raw events eid (event_insert_waiter sg tasks e tid)).
Proof.
  intros sg tasks events eid e tid t Ht Hrow.
  rewrite <- (event_insert_waiter_image_eq sg tasks e tid t Ht Hrow).
  apply event_raw_rep_merge_updated_eid.
Qed.

(** These are the Pend callers' unavailable-resource observations, not
    extra guards performed by OS_EventTaskWait.  A new waiter cannot be
    added to an available Sem/Mbox/Queue payload while preserving the
    existing object invariant. *)
Definition event_wait_resource_unavailable (e : OSEventAbstractState) : Prop :=
  match e.(eventType) with
  | OS_EVENT_TYPE_MUTEX =>
      match e.(mutexFields) with Some m => m.(mfOwner) <> None | None => False end
  | OS_EVENT_TYPE_SEM =>
      match e.(semFields) with Some s => s.(semCount) = 0 | None => False end
  | OS_EVENT_TYPE_MBOX =>
      match e.(mboxFields) with Some m => m.(mboxMsg) = None | None => False end
  | OS_EVENT_TYPE_Q =>
      match e.(queueFields) with Some q => q.(qMessages) = [] | None => False end
  | _ => False
  end.

Lemma event_insert_waiter_preserves_fields : forall sg tasks e tid,
  event_fields_consistency e -> event_wait_resource_unavailable e ->
  event_fields_consistency (event_insert_waiter sg tasks e tid).
Proof.
  intros sg tasks e tid Hfields Hunavailable.
  unfold event_insert_waiter, event_set_wait_list.
  unfold event_fields_consistency in *; simpl; unfold event_wait_resource_unavailable in Hunavailable.
  destruct e.(eventType); simpl in *; contradiction || assumption.
Qed.

Lemma event_insert_waiter_preserves_payload : forall sg tasks e tid,
  event_payload_consistency sg e -> event_wait_resource_unavailable e ->
  event_payload_consistency sg (event_insert_waiter sg tasks e tid).
Proof.
  intros sg tasks e tid Hpayload Hunavailable.
  unfold event_insert_waiter, event_set_wait_list.
  unfold event_payload_consistency in *; simpl; unfold event_wait_resource_unavailable in Hunavailable.
  destruct e.(eventType); simpl in *; try contradiction.
  - destruct e.(semFields) as [sem|]; [|contradiction].
    destruct Hpayload as [Hrange Hwait]; split; [exact Hrange|intros; exact Hunavailable].
  - destruct e.(mutexFields) as [m|]; [|contradiction].
    destruct Hpayload as [Hfields Hwait]; split; [exact Hfields|intro Hnone; contradiction].
  - destruct e.(mboxFields) as [mbox|]; [|contradiction].
    destruct Hpayload as [Hrange Hwait]; split; [exact Hrange|intros; exact Hunavailable].
  - destruct e.(queueFields) as [q|]; [|contradiction].
    destruct Hpayload as [Hid [Hstart [Hsize [Hring Hwait]]]].
    split; [exact Hid|]. split; [exact Hstart|]. split; [exact Hsize|].
    split; [exact Hring|intros; exact Hunavailable].
Qed.

Lemma event_unregistered_task_not_waiting : forall sg tasks events tid old,
  (forall eid e, events.(inUsedEventStates) eid = Some e ->
    event_wait_entry_consistency sg tasks eid e) ->
  tasks.(inUsedTaskStates) tid = Some old -> old.(eventPtr) = None ->
  forall eid e, events.(inUsedEventStates) eid = Some e -> ~ In tid e.(waitList).
Proof.
  intros sg tasks events tid old Hentries Hold Hnull eid e He Hin.
  destruct (event_waiter_task_fields sg tasks eid e tid (Hentries eid e He) Hin)
    as [found [kind [Hfound [_ [Hptr _]]]]].
  assert (found = old) by congruence; subst found; congruence.
Qed.

Lemma event_insert_waiter_update_task_preserves_in_range :
  forall sg tasks events eid e tid old new kind,
    event_in_range sg tasks events -> events.(inUsedEventStates) eid = Some e ->
    tasks.(inUsedTaskStates) tid = Some old -> old.(eventPtr) = None ->
    task_priority_unique (glob_task_set_usedtask tasks tid new) -> valid_task_prio sg new.(curPrio) ->
    new.(eventPtr) = Some eid -> new.(eventMultiWaitEvents) = [] -> task_linked_wait_phase new kind ->
    event_type_to_pend_type e.(eventType) = Some kind -> event_wait_resource_unavailable e ->
    let updated := glob_task_set_usedtask tasks tid new in
    event_in_range sg updated
      (update_event_field_raw events eid (event_insert_waiter sg updated e tid)).
Proof.
  intros sg tasks events eid e tid old new kind Hvalid He Hold Hnull Hunique Hprio
    Hptr Hmulti Hlinked Hkind Hunavailable updated.
  pose proof Hvalid as [_ [_ [_ [Hfields [Hpayload [_ Hentries]]]]]].
  pose proof (event_unregistered_task_not_waiting sg tasks events tid old Hentries Hold Hnull)
    as Habsent.
  assert (Hupdated : event_in_range sg updated events).
  { eapply event_update_unlisted_task_preserves_in_range; eauto. }
  eapply event_update_preserves_in_range;
    [exact Hupdated|exact He|reflexivity| | |reflexivity|].
  - apply event_insert_waiter_preserves_fields; [eapply Hfields; exact He|exact Hunavailable].
  - apply event_insert_waiter_preserves_payload; [eapply Hpayload; exact He|exact Hunavailable].
  - eapply event_wait_entry_insert_waiter with (t := new) (kind := kind).
    + apply event_wait_entry_update_unlisted_task; [eapply Habsent|eapply Hentries]; exact He.
    + exact Hunique.
    + unfold updated; simpl; rewrite Z.eqb_refl; reflexivity.
    + exact Hprio.
    + exact Hkind.
    + exact Hptr.
    + exact Hmulti.
    + exact Hlinked.
Qed.

Lemma event_wait_object_insert_update_task : forall sg s eid e tid old new kind,
  event_wait_object_consistency sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  s.(TskState).(inUsedTaskStates) tid = Some old -> old.(eventPtr) = None ->
  task_priority_unique (glob_task_set_usedtask s.(TskState) tid new) -> valid_task_prio sg new.(curPrio) ->
  new.(eventPtr) = Some eid -> new.(eventMultiWaitEvents) = [] -> task_linked_wait_phase new kind ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  let tasks := glob_task_set_usedtask s.(TskState) tid new in
  event_wait_object_consistency sg
    (replace_EventS (update_event_field_raw s.(EventState) eid (event_insert_waiter sg tasks e tid))
      (replace_TskS tasks s)).
Proof.
  intros sg s eid e tid old new kind [Hentries [Hback Hclosed]]
    He Hold Hnull Hunique Hprio Hptr Hmulti Hlinked Hkind tasks.
  pose proof (event_unregistered_task_not_waiting sg s.(TskState) s.(EventState)
    tid old Hentries Hold Hnull) as Habsent.
  set (events := update_event_field_raw s.(EventState) eid (event_insert_waiter sg tasks e tid)).
  assert (HbackNew : task_event_reference_backlink_consistency tasks events).
  { intros slot t object node Ht Hnode Href.
    unfold tasks in Ht; simpl in Ht; destruct (Z.eqb slot tid) eqn:Etask.
    - apply Z.eqb_eq in Etask; subst slot; injection Ht as Ht; subst t.
      rewrite Hptr, Hmulti in Href; destruct Href as [Hsame|Hfalse]; [|contradiction].
      injection Hsame as Hsame; subst object; unfold events in Hnode; simpl in Hnode.
      rewrite Z.eqb_refl in Hnode; injection Hnode as Hnode; subst node.
      apply event_insert_waiter_membership; left; reflexivity.
    - unfold events in Hnode; simpl in Hnode; destruct (Z.eqb object eid) eqn:Eevent.
      + apply Z.eqb_eq in Eevent; subst object; injection Hnode as Hnode; subst node.
        apply event_insert_waiter_membership; right; eapply Hback; eauto.
      + eapply Hback; eauto. }
  split.
  - intros object node Hnode; simpl in Hnode; destruct (Z.eqb object eid) eqn:Eevent.
    + apply Z.eqb_eq in Eevent; subst object; injection Hnode as Hnode; subst node.
      eapply event_wait_entry_insert_waiter with (t := new) (kind := kind).
      * apply event_wait_entry_update_unlisted_task; [eapply Habsent|eapply Hentries]; exact He.
      * exact Hunique.
      * unfold tasks; simpl; rewrite Z.eqb_refl; reflexivity.
      * exact Hprio.
      * exact Hkind.
      * exact Hptr.
      * exact Hmulti.
      * exact Hlinked.
    + apply event_wait_entry_update_unlisted_task; [eapply Habsent|eapply Hentries]; exact Hnode.
  - split; [exact HbackNew|].
    intros slot t Ht; unfold tasks in Ht; simpl in Ht; destruct (Z.eqb slot tid) eqn:Etask.
    + injection Ht as Ht; subst t; rewrite Hptr, Hmulti.
      split; intros object Href; [|contradiction].
      injection Href as Href; subst object.
      eexists; simpl; rewrite Z.eqb_refl; reflexivity.
    + destruct (Hclosed slot t Ht) as [HsingleClosed HmultiClosed].
      assert (Hlive : forall object,
        (exists node, s.(EventState).(inUsedEventStates) object = Some node) ->
        exists node, events.(inUsedEventStates) object = Some node).
      { intros object [node Hnode]; unfold events; simpl; destruct (Z.eqb object eid); eauto. }
      split; intros object Href; apply Hlive; [apply HsingleClosed|apply HmultiClosed]; exact Href.
Qed.
