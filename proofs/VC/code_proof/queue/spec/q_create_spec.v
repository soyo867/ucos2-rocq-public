Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.lib.event.
Require Export Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.cross_module_invariants.

Import ListNotations.
Import UCOS2_C_Rules.
Import TaskStateDef.
Import EventStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Historical OSQCreate verification-slice semantics and ownership stages.

    This slice does not model allocation generations or preserve an exact
    padding snapshot in the created Event. It is not the complete Event/QCB
    lifecycle contract; the latter is defined in q_create_lifecycle_spec.v.

    Reusable layout, event, wait-list, queue-ring, free-list and interrupt
    facts stay in their module owners.  This file only combines them in the
    source order of OSQCreate. *)

Inductive QCreateOutcome : Type :=
| QCreateFailure (queue_free_ids : list QueueID)
| QCreateSuccess
    (event_id : EventID) (queue_id : QueueID)
    (queue_free_ids : list QueueID).

Definition q_create_return_ptr
  (sg : StableGlobVars) (out : QCreateOutcome) : addr :=
  match out with
  | QCreateFailure _ => 0
  | QCreateSuccess eid _ _ => event_addr sg eid
  end.

Definition q_create_queue_fields
  (qid : QueueID) (start size : Z) : QueueFields :=
  {| qID       := qid;
     qStart    := start;
     qSize     := size;
     qInIndex  := 0;
     qOutIndex := 0;
     qMessages := [] |}.

Definition verification_slice_q_create_queue_event
  (qid : QueueID) (start size : Z) : OSEventAbstractState :=
  {| eventGeneration := 0%nat;
     eventName := 0; eventPadding1 := None; eventPadding2 := None;
     eventPadding3 := None; eventPadding19 := None;
     eventType   := OS_EVENT_TYPE_Q;
     mutexFields := None;
     semFields   := None;
     mboxFields  := None;
     queueFields := Some (q_create_queue_fields qid start size);
     waitList    := [] |}.

Definition verification_slice_q_create_event_state
  (before : Glob_EventAbstractState)
  (eid : EventID) (event_rest : list EventID)
  (qid : QueueID) (start size : Z) (buffer : list addr)
  : Glob_EventAbstractState :=
  {| inUsedEventStates := fun eid' =>
       if Z.eqb eid' eid
       then Some (verification_slice_q_create_queue_event qid start size)
       else before.(inUsedEventStates) eid';
     unUsedEventStates := event_rest;
     eventLifecycle := before.(eventLifecycle);
     publishedQueueBytes := fun qid' =>
       if Z.eqb qid' qid then Some (map (@Some addr) buffer)
       else before.(publishedQueueBytes) qid' |}.

(** [buffer] is the caller's existing [PtrArray.full] observation, not a
    new input restriction.  OSQCreate does not write these cells: publication
    registers their exact initialized values, including stale and null values
    outside the empty logical FIFO.  The same constructor is used by the C
    contract's successful endpoint and by the native-storage consequence below. *)

Definition verification_slice_q_create_success_state
  (before : UCOS2_Verify_State)
  (eid : EventID) (event_rest : list EventID)
  (qid : QueueID) (start size : Z) (buffer : list addr)
  : UCOS2_Verify_State :=
  replace_EventS
    (verification_slice_q_create_event_state before.(EventState)
       eid event_rest qid start size buffer)
    before.

(** Ordered public API semantics.  The queue free-list is not yet a top-level
    projection of [UCOS2_Verify_State], so its exact remainder is carried in
    the observable outcome.  No error input is excluded: the ISR, empty-event
    and empty-queue paths are all explicit and ordered. *)
Definition verification_slice_OSQCreate_sem
  (sg : StableGlobVars) (start size : Z)
  (queue_free_ids : list QueueID) (buffer : list addr)
  : program UCOS2_Verify_State QCreateOutcome :=
  fun before out after =>
    if Z.gtb before.(IntrState).(intNesting) 0
    then out = QCreateFailure queue_free_ids /\ after = before
    else
      match before.(EventState).(unUsedEventStates) with
      | [] => out = QCreateFailure queue_free_ids /\ after = before
      | eid :: event_rest =>
          match queue_free_ids with
          | [] => out = QCreateFailure [] /\ after = before
          | qid :: queue_rest =>
              out = QCreateSuccess eid qid queue_rest /\
              after =
                verification_slice_q_create_success_state before eid event_rest qid start size buffer
          end
      end.

Lemma verification_slice_OSQCreate_sem_total :
  forall sg start size queue_free_ids buffer before,
    exists out after, verification_slice_OSQCreate_sem sg start size queue_free_ids buffer before out after.
Proof.
  intros; unfold verification_slice_OSQCreate_sem.
  destruct (Z.gtb (intNesting (IntrState before)) 0).
  - exists (QCreateFailure queue_free_ids), before; auto.
  - destruct (unUsedEventStates (EventState before)) as [|eid event_rest].
    + exists (QCreateFailure queue_free_ids), before; auto.
    + destruct queue_free_ids as [|qid queue_rest].
      * exists (QCreateFailure []), before; auto.
      * exists (QCreateSuccess eid qid queue_rest),
          (verification_slice_q_create_success_state before eid event_rest qid start size buffer); auto.
Qed.

Lemma verification_slice_OSQCreate_sem_failure_state_eq :
  forall sg start size queue_free_ids buffer before remaining after,
    verification_slice_OSQCreate_sem sg start size queue_free_ids buffer before (QCreateFailure remaining) after ->
    after = before.
Proof.
  intros; unfold verification_slice_OSQCreate_sem in H.
  destruct (Z.gtb (intNesting (IntrState before)) 0); [tauto|].
  destruct (unUsedEventStates (EventState before)); [tauto|].
  destruct queue_free_ids; [tauto|]. destruct H; discriminate.
Qed.

Lemma verification_slice_OSQCreate_sem_success_endpoint :
  forall sg start size queue_free_ids buffer before eid qid remaining after,
    verification_slice_OSQCreate_sem sg start size queue_free_ids buffer before (QCreateSuccess eid qid remaining) after ->
    exists event_rest,
      before.(EventState).(unUsedEventStates) = eid :: event_rest /\
      queue_free_ids = qid :: remaining /\
      after = verification_slice_q_create_success_state before eid event_rest qid start size buffer.
Proof.
  intros; unfold verification_slice_OSQCreate_sem in H.
  destruct (Z.gtb (intNesting (IntrState before)) 0).
  - destruct H; discriminate.
  - destruct (unUsedEventStates (EventState before)) as [|id event_rest] eqn:Hfree.
    + destruct H; discriminate.
    + destruct queue_free_ids as [|queue queue_rest].
      * destruct H; discriminate.
      * destruct H as [Hout Hafter]; inversion Hout; subst.
        exists event_rest; auto.
Qed.

(** Parser-facing specialization of the critical-STS continuation type. *)
Definition QCreateContinuation : Type :=
  QCreateOutcome -> (UCOS2_Verify_State -> Prop) -> Prop.

Definition verification_slice_q_create_safe_pre
  (sg : StableGlobVars) (start size : Z)
  (queue_free_ids : list QueueID) (buffer : list addr)
  (lvs : UCOS2_Verify_State)
  (X : QCreateContinuation) : Prop :=
  safeExec (LastSeen lvs)
    (atomic_cmd (verification_slice_OSQCreate_sem sg start size queue_free_ids buffer)) X.

Definition q_create_safe_post
  (lvs : UCOS2_Verify_State) (out : QCreateOutcome)
  (X : QCreateContinuation) : Prop :=
  safeExec (LastSeen lvs)
    (@StateRelMonad.ret
       (UCOS2_Verify_State -> Prop) QCreateOutcome out) X.

(** A queue control block on [queue_free_ids] cannot already be named by a
    live queue event.  This is the operation-boundary coupling needed while
    QueueState is migration-local rather than a top-level OS projection. *)
Definition q_create_queue_ids_unbound
  (evSt : Glob_EventAbstractState)
  (queue_free_ids : list QueueID) : Prop :=
  forall qid,
    In qid queue_free_ids ->
    forall eid e,
      evSt.(inUsedEventStates) eid = Some e ->
      event_queue_id e <> Some qid.

Definition q_create_global_layout_prop
  (sg : StableGlobVars)
  (int_nesting_addr event_free_addr queue_free_addr : addr) : Prop :=
  os_int_nesting_addr sg int_nesting_addr /\
  os_event_free_list_addr sg event_free_addr /\
  os_q_free_list_addr sg queue_free_addr /\
  event_table_layout_prop sg /\
  queue_table_layout_prop sg sg.(g_OSQTbl) /\
  queue_first_round_profile sg.

Definition verification_slice_q_create_world_pure
  (sg : StableGlobVars) (start size : Z) (buffer : list addr)
  (lvs : UCOS2_Verify_State) (queue_free_ids : list QueueID) : Prop :=
  valid_stable_glob_vars sg /\
  0 < start /\
  0 <= size <= 65535 /\
  Zlength buffer = size /\
  queue_free_ids_valid sg queue_free_ids /\
  q_create_queue_ids_unbound lvs.(EventState) queue_free_ids /\
  verification_slice_cross_module_consistency sg lvs.

Definition verification_slice_q_create_world
  (sg : StableGlobVars) (start size : Z) (buffer : list addr)
  (lvs : UCOS2_Verify_State) (queue_free_ids : list QueueID)
  : Assertion :=
  coq_prop (verification_slice_q_create_world_pure
    sg start size buffer lvs queue_free_ids) &&
  ucos2_rules_lib.OutsideCritical sg lvs **
  interrupt_inv sg lvs.(IntrState) **
  verification_slice_event_inv sg lvs.(TskState) lvs.(EventState) **
  store_free_queue_list sg queue_free_ids **
  PtrArray.full start size buffer.

(** Thin parser-facing names for the module-owned representation atoms.  They
    do not weaken or duplicate those atoms; their sole purpose is to avoid
    exposing nested Rocq record types in C's [Extern Coq] declarations. *)
Definition q_create_outside
  (sg : StableGlobVars) (lvs : UCOS2_Verify_State) : Assertion :=
  ucos2_rules_lib.OutsideCritical sg lvs.

Definition q_create_inside
  (sg : StableGlobVars) (lvs : UCOS2_Verify_State) : Assertion :=
  ucos2_rules_lib.InsideCritical sg lvs.

Definition q_create_restore_ready
  (critical_entry : UCOS2_Verify_State) (saved_cpu_sr : Z) : Prop :=
  exists entry,
    interrupt_saved_cpu_sr entry critical_entry saved_cpu_sr.

Definition q_create_interrupt_rep
  (sg : StableGlobVars) (lvs : UCOS2_Verify_State) : Assertion :=
  interrupt_inv sg lvs.(IntrState).

Definition q_create_int_nesting (lvs : UCOS2_Verify_State) : Z :=
  lvs.(IntrState).(intNesting).

Definition q_create_interrupt_residual
  (sg : StableGlobVars) (lvs : UCOS2_Verify_State) : Assertion :=
  interrupt_inv_no_int_nesting sg lvs.(IntrState).

Definition verification_slice_q_create_event_rep
  (sg : StableGlobVars) (lvs : UCOS2_Verify_State) : Assertion :=
  verification_slice_event_inv sg lvs.(TskState) lvs.(EventState).

Definition verification_slice_q_create_event_no_free_head
  (sg : StableGlobVars) (lvs : UCOS2_Verify_State) : Assertion :=
  verification_slice_event_inv_no_free_head sg lvs.(TskState) lvs.(EventState).

Definition q_create_unused_events
  (lvs : UCOS2_Verify_State) : list EventID :=
  lvs.(EventState).(unUsedEventStates).

Definition verification_slice_q_create_event_residual
  (sg : StableGlobVars) (lvs : UCOS2_Verify_State)
  (event_rest : list EventID) : Assertion :=
  verification_slice_event_inv_free_head_rest
    sg lvs.(TskState) lvs.(EventState) event_rest.

Definition q_create_queue_free_list
  (sg : StableGlobVars) (queue_free_ids : list QueueID) : Assertion :=
  store_free_queue_list sg queue_free_ids.

Definition q_create_queue_free_nodes
  (sg : StableGlobVars) (queue_free_ids : list QueueID) : Assertion :=
  store_free_queue_nodes sg queue_free_ids.

Definition q_create_buffer
  (start size : Z) (buffer : list addr) : Assertion :=
  PtrArray.full start size buffer.

Definition verification_slice_q_create_success_world
  (sg : StableGlobVars) (start size : Z) (buffer : list addr)
  (lvs : UCOS2_Verify_State) (eid : EventID) (qid : QueueID)
  (queue_rest : list QueueID) : Assertion :=
  coq_prop
    (verification_slice_q_create_world_pure sg start size buffer lvs queue_rest /\
     lvs.(EventState).(inUsedEventStates) eid =
       Some (verification_slice_q_create_queue_event qid start size) /\
     lvs.(EventState).(publishedQueueBytes) qid =
       Some (map (@Some addr) buffer)) &&
  ucos2_rules_lib.OutsideCritical sg lvs **
  interrupt_inv sg lvs.(IntrState) **
  verification_slice_event_inv sg lvs.(TskState) lvs.(EventState) **
  store_free_queue_list sg queue_rest **
  used_queue_control_block sg (q_create_queue_fields qid start size) **
  PtrArray.full start size buffer.

Definition verification_slice_q_create_post_world
  (sg : StableGlobVars) (start size : Z) (buffer : list addr)
  (lvs : UCOS2_Verify_State) (out : QCreateOutcome) : Assertion :=
  match out with
  | QCreateFailure queue_free_ids =>
      verification_slice_q_create_world sg start size buffer lvs queue_free_ids
  | QCreateSuccess eid qid queue_rest =>
      verification_slice_q_create_success_world
        sg start size buffer lvs eid qid queue_rest
  end.

(** Event free-list zipper after the head is unlinked but before the selected
    event is initialized or rolled back.  The old validity bundle remains
    explicit while the source-total concrete representation is transient. *)
Definition verification_slice_q_create_event_pool_residual
  (sg : StableGlobVars) (tskSt : Glob_TaskAbstractState)
  (before : Glob_EventAbstractState) (event_rest : list EventID)
  : Assertion :=
  sg.(g_OSEventFreeList) # Ptr |-> free_event_head sg event_rest **
  verification_slice_event_inv_free_head_rest sg tskSt before event_rest.

Definition verification_slice_q_create_detached_event_node
  (sg : StableGlobVars) (eid : EventID) (event_rest : list EventID)
  : Assertion :=
  (event_addr sg eid + OSEventType_off) # UChar |->
    encode_event_type OS_EVENT_TYPE_UNUSED **
  free_event_node_rest_no_type
    sg eid (free_event_head sg event_rest).

(** Reversible head focus.  The module-owned residual and node predicates are
    kept intact; this case predicate only records that the selected source
    node is the concrete free-list head. *)
Definition verification_slice_q_create_event_head_exposed
  (sg : StableGlobVars) (tskSt : Glob_TaskAbstractState)
  (before : Glob_EventAbstractState) (eid : EventID)
  (event_rest : list EventID) : Assertion :=
  coq_prop
    (before.(unUsedEventStates) = eid :: event_rest /\
     valid_event_id sg eid) &&
  sg.(g_OSEventFreeList) # Ptr |-> event_addr sg eid **
  verification_slice_q_create_detached_event_node sg eid event_rest **
  verification_slice_event_inv_free_head_rest sg tskSt before event_rest.

Definition q_create_queue_head_exposed
  (sg : StableGlobVars) (qid : QueueID)
  (queue_rest : list QueueID) : Assertion :=
  coq_prop (valid_queue_id sg qid) &&
  sg.(g_OSQFreeList) # Ptr |-> qcb_addr sg qid **
  free_queue_node sg qid (queue_free_head sg queue_rest) **
  store_free_queue_nodes sg queue_rest.

Definition q_create_queue_pool_residual
  (sg : StableGlobVars) (queue_rest : list QueueID) : Assertion :=
  sg.(g_OSQFreeList) # Ptr |-> queue_free_head sg queue_rest **
  store_free_queue_nodes sg queue_rest.

(** Exact concrete footprint of OS_EventWaitListInit.  The helper owns only
    the wait bitmap; the already initialized type/count/pointer fields and
    all unrelated state remain caller frames. *)
Definition q_create_event_wait_init_pre (base : addr) : Assertion :=
  (base + OSEventGrp_off) # UChar |->_ **
  (base + OSEventTbl_off + 0) # UChar |->_ **
  (base + OSEventTbl_off + 1) # UChar |->_ **
  (base + OSEventTbl_off + 2) # UChar |->_ **
  (base + OSEventTbl_off + 3) # UChar |->_ **
  (base + OSEventTbl_off + 4) # UChar |->_ **
  (base + OSEventTbl_off + 5) # UChar |->_ **
  (base + OSEventTbl_off + 6) # UChar |->_ **
  (base + OSEventTbl_off + 7) # UChar |->_ .

Definition q_create_event_wait_init_post (base : addr) : Assertion :=
  (base + OSEventGrp_off) # UChar |-> 0 **
  (base + OSEventTbl_off + 0) # UChar |-> 0 **
  (base + OSEventTbl_off + 1) # UChar |-> 0 **
  (base + OSEventTbl_off + 2) # UChar |-> 0 **
  (base + OSEventTbl_off + 3) # UChar |-> 0 **
  (base + OSEventTbl_off + 4) # UChar |-> 0 **
  (base + OSEventTbl_off + 5) # UChar |-> 0 **
  (base + OSEventTbl_off + 6) # UChar |-> 0 **
  (base + OSEventTbl_off + 7) # UChar |-> 0.

Lemma q_create_interrupt_rebuild__return_paths :
  forall sg s,
    sg.(g_OSIntNesting) # UChar |-> s.(intNesting) **
    interrupt_inv_no_int_nesting sg s |--
    interrupt_inv sg s.
Proof.
  intros sg s.
  unfold interrupt_inv, interrupt_inv_no_int_nesting, store_int_state.
  pureIntros.
  apply _derivable1_andp_intros.
  - apply derivable1s_coq_prop_r. exact H.
  - cancel.
Qed.
Lemma q_create_event_rebuild__return_paths :
  forall sg tskSt st,
    sg.(g_OSEventFreeList) # Ptr |-> free_event_head sg st.(unUsedEventStates) **
    verification_slice_event_inv_no_free_head sg tskSt st |--
    verification_slice_event_inv sg tskSt st.
Proof.
  intros sg tskSt st.
  unfold verification_slice_event_inv, verification_slice_event_inv_no_free_head, store_free_event_list.
  pureIntros.
  apply _derivable1_andp_intros.
  - apply derivable1s_coq_prop_r. exact H.
  - cancel.
Qed.
Lemma q_create_atomic_safe_return__return_paths :
  forall (A : Type) (c : program UCOS2_Verify_State A)
         (ls0 ls2 : UCOS2_Verify_State) (retv : A)
         (X : A -> (UCOS2_Verify_State -> Prop) -> Prop),
    c ls0 retv ls2 ->
    safeExec (LastSeen ls0) (atomic_cmd c) X ->
    safeExec (LastSeen ls2)
      (@StateRelMonad.ret (UCOS2_Verify_State -> Prop) A retv) X.
Proof.
  intros A c ls0 ls2 retv X Hsem Hexec.
  eapply (highstependret_derive
    (atomic_cmd c) (LastSeen ls0) retv
    (fun _ => LastSeen ls2)).
  - unfold hs_eval, LastSeen, atomic_cmd.
    intros P0 HP0.
    exists (RTrans_Abs ls2).
    split.
    + exists ls0, ls2.
      split.
      * apply HP0. exact I.
      * split.
        -- exact Hsem.
        -- change (forall x, RTrans_Abs ls2 x <-> RTrans_Abs ls2 x).
           tauto.
    + change (forall x, RTrans_Abs ls2 x <-> RTrans_Abs ls2 x).
      tauto.
  - exact Hexec.
Qed.
Lemma q_create_free_event_head_zero_empty__return_paths :
  forall sg tskSt st,
    valid_stable_glob_vars sg ->
    verification_slice_event_in_range sg tskSt st ->
    free_event_head sg st.(unUsedEventStates) = 0 ->
    st.(unUsedEventStates) = [].
Proof.
  intros sg tskSt st Hsg Hvalid Hhead.
  destruct st.(unUsedEventStates) as [| eid event_rest] eqn:Hfree.
  - reflexivity.
  - unfold verification_slice_event_in_range, verification_slice_event_in_range,
      verification_slice_event_in_range in Hvalid.
    destruct Hvalid as [_ [_ [Hids _]]].
    rewrite Hfree in Hids.
    inversion Hids as [| ? ? Heid _]; subst.
    destruct Heid as [Heid0 Heidmax].
    unfold valid_stable_glob_vars in Hsg.
    repeat lazymatch type of Hsg with
      | _ /\ _ => destruct Hsg as [_ Hsg]
    end.
    unfold valid_stable_global_addresses in Hsg.
    destruct Hsg as [Haddresses _].
    rewrite Forall_forall in Haddresses.
    pose proof
      (Haddresses (g_OSEventTbl sg)) as Hevent_base.
    assert (Hin : In (g_OSEventTbl sg) (stable_global_addresses sg)).
    { unfold stable_global_addresses. simpl. auto. }
    specialize (Hevent_base Hin).
    cbn [free_event_head event_addr sizeof_OS_EVENT] in Hhead.
    unfold event_addr, event_pool_addr, event_object_size in Hhead.
    destruct sg.(osKernelConfig).(cfgEventNames); simpl in Hhead; lia.
Qed.
Lemma q_create_free_queue_head_zero_empty__return_paths :
  forall sg queue_free_ids,
    valid_stable_glob_vars sg ->
    queue_free_ids_valid sg queue_free_ids ->
    queue_free_head sg queue_free_ids = 0 ->
    queue_free_ids = [].
Proof.
  intros sg queue_free_ids Hsg Hvalid Hhead.
  destruct queue_free_ids as [| qid queue_rest].
  - reflexivity.
  - unfold queue_free_ids_valid in Hvalid.
    destruct Hvalid as [_ Hids].
    inversion Hids as [| ? ? Hqid _]; subst.
    unfold valid_queue_id in Hqid.
    unfold valid_stable_glob_vars in Hsg.
    repeat lazymatch type of Hsg with
      | _ /\ _ => destruct Hsg as [_ Hsg]
    end.
    unfold valid_stable_global_addresses in Hsg.
    destruct Hsg as [Haddresses _].
    rewrite Forall_forall in Haddresses.
    pose proof (Haddresses (g_OSQTbl sg)) as Hqueue_base.
    assert (Hin : In (g_OSQTbl sg) (stable_global_addresses sg)).
    { unfold stable_global_addresses. simpl. auto. }
    specialize (Hqueue_base Hin).
    cbn [queue_free_head qcb_addr sizeof_OS_Q] in Hhead.
    unfold qcb_addr, sizeof_OS_Q in Hhead.
    lia.
Qed.
Lemma q_create_event_rollback_rebuild__return_paths :
  forall sg tskSt st eid event_rest,
    st.(unUsedEventStates) = eid :: event_rest ->
    verification_slice_event_inv_free_head_rest sg tskSt st event_rest **
    sg.(g_OSEventFreeList) # Ptr |-> event_addr sg eid **
    (event_addr sg eid + OSEventType_off) # UChar |-> 0 **
    (event_addr sg eid + OSEventPtr_off) # Ptr |->
      free_event_head sg event_rest **
    (event_addr sg eid + OSEventCnt_off) # UShort |->_ **
    (event_addr sg eid + OSEventGrp_off) # UChar |->_ **
    (event_addr sg eid + OSEventTbl_off) # UChar |->_ **
    (event_addr sg eid + OSEventTbl_off + 1) # UChar |->_ **
    (event_addr sg eid + OSEventTbl_off + 2) # UChar |->_ **
    (event_addr sg eid + OSEventTbl_off + 3) # UChar |->_ **
    (event_addr sg eid + OSEventTbl_off + 4) # UChar |->_ **
    (event_addr sg eid + OSEventTbl_off + 5) # UChar |->_ **
    (event_addr sg eid + OSEventTbl_off + 6) # UChar |->_ **
    (event_addr sg eid + OSEventTbl_off + 7) # UChar |->_ |--
    verification_slice_event_inv sg tskSt st.
Proof.
  intros sg tskSt st eid event_rest Hfree.
  unfold verification_slice_event_inv, verification_slice_event_inv_free_head_rest, store_free_event_list.
  pureIntros.
  apply _derivable1_andp_intros.
  - apply derivable1s_coq_prop_r. exact H.
  - rewrite Hfree.
    simpl.
    replace (event_addr sg eid + OSEventTbl_off + 0)
      with (event_addr sg eid + OSEventTbl_off) by lia.
    repeat cancel.
Qed.
Lemma q_create_old_event_none__return_paths :
  forall sg before_t before_e eid event_rest,
    before_e.(unUsedEventStates) = eid :: event_rest ->
    verification_slice_event_in_range sg before_t before_e ->
    before_e.(inUsedEventStates) eid = None.
Proof.
  intros sg before_t before_e eid event_rest Hfree Hvalid.
  unfold verification_slice_event_in_range, verification_slice_event_in_range,
    verification_slice_event_in_range in Hvalid.
  destruct Hvalid as [_ [_ [_ [Hpartition _]]]].
  eapply event_slot_partition_free_lookup; eauto.
  rewrite Hfree. simpl. auto.
Qed.
Lemma verification_slice_q_create_event_valid_after__return_paths :
  forall sg start size buffer eid event_rest qid queue_rest before_t before_e,
    valid_queue_id sg qid ->
    0 < start ->
    0 <= size <= 65535 ->
    before_e.(unUsedEventStates) = eid :: event_rest ->
    verification_slice_event_in_range sg before_t before_e ->
    q_create_queue_ids_unbound before_e (qid :: queue_rest) ->
    verification_slice_event_in_range sg before_t
      (verification_slice_q_create_event_state before_e eid event_rest qid start size buffer).
Proof.
  intros sg start size buffer eid event_rest qid queue_rest before_t before_e
    Hqid Hstart Hsize Hfree Hvalid Hunbound.
  unfold verification_slice_event_in_range, verification_slice_event_in_range,
    verification_slice_event_in_range in *.
  destruct Hvalid as
    [Hids [Hnodup [Hfreeids [Hpartition
      [Hfields [Hpayload [Hqueue Hwait]]]]]]].
  rewrite Hfree in Hnodup, Hfreeids.
  apply NoDup_cons_iff in Hnodup.
  destruct Hnodup as [Heid_notin Hrest_nodup].
  inversion Hfreeids as [| ? ? Heid_range Hrest_range]; subst.
  unfold verification_slice_q_create_event_state.
  refine (conj _
    (conj Hrest_nodup
      (conj Hrest_range
        (conj _
          (conj _
            (conj _ (conj _ _))))))).
  - intros eid0 e Hget. simpl in Hget.
    destruct (Z.eqb eid0 eid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst eid0. exact Heid_range.
    + eapply Hids; eauto.
  - eapply event_slot_partition_preserved_create; eauto.
  - intros eid0 e Hget. simpl in Hget.
    destruct (Z.eqb eid0 eid) eqn:Heq.
    + inversion Hget; subst e.
      unfold verification_slice_q_create_queue_event, event_fields_consistency.
      simpl. repeat split; try reflexivity; discriminate.
    + eapply Hfields; eauto.
  - intros eid0 e Hget. simpl in Hget.
    destruct (Z.eqb eid0 eid) eqn:Heq.
    + inversion Hget; subst e.
      unfold verification_slice_q_create_queue_event, event_payload_consistency,
        queue_fields_consistency, q_create_queue_fields.
      simpl.
      split; [exact Hqid |].
      split; [exact Hstart |].
      split; [exact Hsize |].
      split.
      * destruct (Z.eq_dec size 0) as [Hzero | Hnonzero].
        -- left. repeat split; try assumption; reflexivity.
        -- right.
           assert (Hpositive : 0 < size) by lia.
           repeat split; try lia.
           all: unfold queue_entries; rewrite Zlength_nil.
           all: try lia.
      * intros Hcontra. exfalso. apply Hcontra. reflexivity.
    + eapply Hpayload; eauto.
  - intros eid1 eid2 e1 e2 qid0 Hget1 Hget2 Hq1 Hq2.
    simpl in Hget1, Hget2.
    destruct (Z.eqb eid1 eid) eqn:Heq1.
    + apply Z.eqb_eq in Heq1. subst eid1.
      inversion Hget1; subst e1.
      simpl [verification_slice_q_create_queue_event q_create_queue_fields
        event_queue_id] in Hq1.
      inversion Hq1; subst qid0.
      destruct (Z.eqb eid2 eid) eqn:Heq2.
      * apply Z.eqb_eq in Heq2. symmetry. exact Heq2.
      * exfalso.
        pose proof
          (Hunbound qid (or_introl eq_refl) eid2 e2 Hget2) as Hnot.
        exact (Hnot Hq2).
    + destruct (Z.eqb eid2 eid) eqn:Heq2.
      * apply Z.eqb_eq in Heq2. subst eid2.
        inversion Hget2; subst e2.
        simpl [verification_slice_q_create_queue_event q_create_queue_fields
          event_queue_id] in Hq2.
        inversion Hq2; subst qid0.
        exfalso.
        pose proof
          (Hunbound qid (or_introl eq_refl) eid1 e1 Hget1) as Hnot.
        exact (Hnot Hq1).
      * eapply Hqueue; eauto.
  - intros eid0 e Hget. simpl in Hget.
    destruct (Z.eqb eid0 eid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst eid0.
      inversion Hget; subst e.
      apply verification_slice_event_wait_entry_consistency_empty_waitList_general.
      reflexivity.
    + eapply Hwait; eauto.
Qed.
Lemma verification_slice_q_create_waitlist_consistency_after__return_paths :
  forall sg start size buffer eid event_rest qid lvs,
    event_wait.task_event_id_unreferenced_prop lvs eid ->
    event_wait.verification_slice_event_wait_object_consistency sg lvs ->
    event_wait.verification_slice_event_wait_object_consistency sg
      (verification_slice_q_create_success_state lvs eid event_rest qid start size buffer).
Proof.
  intros sg start size buffer eid event_rest qid lvs Hunref Hwait.
  unfold event_wait.verification_slice_event_wait_object_consistency in *.
  destruct Hwait as [Hforward [Hback Hclosed]].
  split.
  - intros eid0 e Hget.
    unfold verification_slice_q_create_success_state, verification_slice_q_create_event_state in Hget |- *.
    simpl in *.
    destruct (Z.eqb eid0 eid) eqn:Heq.
    + inversion Hget; subst e.
      apply verification_slice_event_wait_entry_consistency_empty_waitList_general.
      reflexivity.
    + eapply Hforward; eauto.
  - split.
    + unfold event_wait.task_event_reference_backlink_consistency in *.
      intros tid t eid0 e Htask Hget Href.
      unfold verification_slice_q_create_success_state, verification_slice_q_create_event_state in Htask, Hget.
      simpl in Htask, Hget.
      destruct (Z.eqb eid0 eid) eqn:Heq.
      * apply Z.eqb_eq in Heq. subst eid0.
        specialize (Hunref tid t Htask).
        destruct Hunref as [Hunref_single Hunref_multi].
        destruct Href as [Href | Href]; contradiction.
      * eapply Hback; eauto.
    + eapply
        (event_wait.task_event_reference_closure_preserved_by_event_extension
          lvs.(TskState) lvs.(EventState)
          (verification_slice_q_create_success_state lvs eid event_rest qid start size buffer).(EventState)).
      * intros eid0 [e Hget].
        unfold verification_slice_q_create_success_state, verification_slice_q_create_event_state. simpl.
        destruct (Z.eqb eid0 eid); [|eexists; exact Hget].
        eexists. reflexivity.
      * exact Hclosed.
Qed.
Lemma verification_slice_q_create_cross_consistency_after__return_paths :
  forall sg start size buffer eid event_rest qid lvs,
    lvs.(EventState).(unUsedEventStates) = eid :: event_rest ->
    verification_slice_event_in_range sg lvs.(TskState) lvs.(EventState) ->
    event_wait.task_event_id_unreferenced_prop lvs eid ->
    cross_module_invariants.verification_slice_cross_module_consistency sg lvs ->
    cross_module_invariants.verification_slice_cross_module_consistency sg
      (verification_slice_q_create_success_state lvs eid event_rest qid start size buffer).
Proof.
  intros sg start size buffer eid event_rest qid lvs Hfree Hevent Hunref Hcross.
  pose proof (q_create_old_event_none__return_paths
    sg lvs.(TskState) lvs.(EventState) eid event_rest Hfree Hevent) as Hnone.
  assert (Hlookup : forall mid e,
    lvs.(EventState).(inUsedEventStates) mid = Some e ->
    (if Z.eqb mid eid then Some (verification_slice_q_create_queue_event qid start size)
     else lvs.(EventState).(inUsedEventStates) mid) = Some e).
  { intros mid e Hget. destruct (Z.eqb mid eid) eqn:Hmid.
    - apply Z.eqb_eq in Hmid. subst mid.
      rewrite Hnone in Hget. discriminate.
    - exact Hget. }
  unfold cross_module_invariants.verification_slice_cross_module_consistency in Hcross |- *.
  destruct Hcross as
    [Hos [Hpt [Howner [Hwait [Hready [Horder
      [Hceiling [Hunique [Hprotocol Hpcp_unique]]]]]]]]].
  refine (conj _
    (conj _
      (conj _
        (conj _
          (conj _
            (conj _ (conj _ (conj _ (conj _ _))))))))).
  - unfold cross_module_invariants.osprio_cur_consistency,
      verification_slice_q_create_success_state. simpl. exact Hos.
  - intros p.
    specialize (Hpt p).
    unfold verification_slice_q_create_success_state, verification_slice_q_create_event_state. simpl.
    destruct (lvs.(TskState).(prioTbl) p); simpl in Hpt |- *.
    + destruct Hpt as [Hnoready Hnomutex]. split; [exact Hnoready|].
      intros [mid [e [m [Hget [Htype [Hfields Hreserve]]]]]].
      destruct (Z.eqb mid eid) eqn:Hmid.
      * inversion Hget; subst e.
        unfold verification_slice_q_create_queue_event in Htype, Hfields. simpl in *.
        discriminate.
      * apply Hnomutex. exists mid, e, m. repeat split; auto.
        unfold mutex.mutex_reserves_priority_slot in Hreserve.
        exact (proj1 Hreserve).
        exact (proj2 Hreserve).
    + destruct Hpt as
        [mid [e [m [Hget [Htype [Hfields [Hpcp Howner']]]]]]].
      exists mid, e, m. repeat split; auto.
    + destruct Hpt as [t [Htask [Hcur | Hmutex]]].
      * exists t. split; [exact Htask | left; exact Hcur].
      * destruct Hmutex as
          [mid [e [m [Hget [Htype [Hfields [Howner' Hsource]]]]]]].
        exists t. split.
        -- exact Htask.
        -- right. exists mid, e, m. split.
           ++ apply Hlookup. exact Hget.
           ++ repeat split; auto.
  - intros mid e m [Hget [Htype Hfields]].
    unfold verification_slice_q_create_success_state, verification_slice_q_create_event_state in Hget. simpl in Hget.
    destruct (Z.eqb mid eid) eqn:Hmid.
    + inversion Hget; subst e.
      unfold verification_slice_q_create_queue_event in Htype, Hfields.
      simpl in *. discriminate.
    + eapply Howner; eauto.
  - eapply verification_slice_q_create_waitlist_consistency_after__return_paths; eauto.
  - unfold cross_module_invariants.ready_list_completeness,
      verification_slice_q_create_success_state. simpl. exact Hready.
  - unfold cross_module_invariants.ready_list_order,
      verification_slice_q_create_success_state. simpl. exact Horder.
  - unfold cross_module_invariants.ceiling_priotbl_free,
      verification_slice_q_create_success_state. simpl. exact Hceiling.
  - unfold cross_module_invariants.task_priority_unique_prop,
      verification_slice_q_create_success_state. simpl. exact Hunique.
  - intros mid e m Hget Htype Hfields.
    unfold verification_slice_q_create_success_state, verification_slice_q_create_event_state in Hget. simpl in Hget.
    destruct (Z.eqb mid eid) eqn:Hmid.
    + inversion Hget; subst e.
      unfold verification_slice_q_create_queue_event in Htype, Hfields.
      simpl in *. discriminate.
    + eapply Hprotocol; eauto.
  - eapply cross_module_invariants.mutex_enabled_pcp_unique_transport
      with (lvs1 := lvs).
    + intros mid e m Hget Htype Hfields.
      unfold verification_slice_q_create_success_state, verification_slice_q_create_event_state in Hget.
      simpl in Hget.
      destruct (Z.eqb mid eid) eqn:Hmid.
      * inversion Hget; subst e.
        unfold verification_slice_q_create_queue_event in Htype, Hfields.
        simpl in *. discriminate.
      * exists e, m. repeat split; try assumption; reflexivity.
    + exact Hpcp_unique.
Qed.
Lemma q_create_unreferenced_free_head__return_paths :
  forall sg lvs eid event_rest,
    lvs.(EventState).(unUsedEventStates) = eid :: event_rest ->
    verification_slice_event_in_range sg lvs.(TskState) lvs.(EventState) ->
    cross_module_invariants.verification_slice_cross_module_consistency sg lvs ->
    event_wait.task_event_id_unreferenced_prop lvs eid.
Proof.
  intros sg lvs eid event_rest Hfree Hevent Hcross.
  pose proof (q_create_old_event_none__return_paths
    sg lvs.(TskState) lvs.(EventState) eid event_rest Hfree Hevent) as Hnone.
  unfold cross_module_invariants.verification_slice_cross_module_consistency in Hcross.
  destruct Hcross as [_ [_ [_ [Hwait _]]]].
  unfold event_wait.verification_slice_event_wait_object_consistency in Hwait.
  destruct Hwait as [_ [_ Hclosed]].
  eapply event_wait.task_event_reference_closure_implies_unreferenced;
    eauto.
Qed.
Lemma verification_slice_q_create_queue_ids_unbound_after__return_paths :
  forall sg before eid event_rest qid queue_rest start size buffer,
    queue_free_ids_valid sg (qid :: queue_rest) ->
    q_create_queue_ids_unbound before (qid :: queue_rest) ->
    q_create_queue_ids_unbound
      (verification_slice_q_create_event_state before eid event_rest qid start size buffer)
      queue_rest.
Proof.
  intros sg before eid event_rest qid queue_rest start size buffer Hvalid Hunbound.
  unfold queue_free_ids_valid in Hvalid.
  destruct Hvalid as [Hnodup _].
  apply NoDup_cons_iff in Hnodup.
  destruct Hnodup as [Hqid_notin _].
  unfold q_create_queue_ids_unbound in *.
  intros qid0 Hqid0 eid0 e Hget.
  unfold verification_slice_q_create_event_state in Hget. simpl in Hget.
  destruct (Z.eqb eid0 eid) eqn:Heq.
  - inversion Hget; subst e.
    simpl [verification_slice_q_create_queue_event q_create_queue_fields event_queue_id].
    intro Hequal. inversion Hequal; subst qid0.
    contradiction.
  - eapply Hunbound.
    + simpl. right. exact Hqid0.
    + exact Hget.
Qed.
Lemma verification_slice_q_create_world_pure_after__return_paths :
  forall sg start size buffer lvs eid event_rest qid queue_rest,
    lvs.(EventState).(unUsedEventStates) = eid :: event_rest ->
    verification_slice_event_in_range sg lvs.(TskState) lvs.(EventState) ->
    verification_slice_q_create_world_pure sg start size buffer lvs (qid :: queue_rest) ->
    verification_slice_q_create_world_pure sg start size buffer
      (verification_slice_q_create_success_state lvs eid event_rest qid start size buffer)
      queue_rest.
Proof.
  intros sg start size buffer lvs eid event_rest qid queue_rest
    Hfree Hevent Hworld.
  unfold verification_slice_q_create_world_pure in Hworld |- *.
  destruct Hworld as
    [Hsg [Hstart [Hsize [Hlen [Hqueues [Hunbound Hcross]]]]]].
  assert (Hqid : valid_queue_id sg qid).
  { destruct Hqueues as [_ Hids]. inversion Hids; subst. assumption. }
  assert (Hqueues_rest : queue_free_ids_valid sg queue_rest).
  { unfold queue_free_ids_valid in *.
    destruct Hqueues as [Hnodup Hids].
    inversion Hnodup; inversion Hids; subst. split; assumption. }
  pose proof
    (q_create_unreferenced_free_head__return_paths
      sg lvs eid event_rest Hfree Hevent Hcross) as Hunref.
  pose proof
    (verification_slice_q_create_cross_consistency_after__return_paths
      sg start size buffer eid event_rest qid lvs
      Hfree Hevent Hunref Hcross) as Hcross_after.
  pose proof
    (verification_slice_q_create_queue_ids_unbound_after__return_paths
      sg lvs.(EventState) eid event_rest qid queue_rest start size buffer
      Hqueues Hunbound) as Hunbound_after.
  cbn [verification_slice_q_create_success_state].
  refine (conj Hsg
    (conj Hstart
      (conj Hsize
        (conj Hlen
          (conj Hqueues_rest
            (conj Hunbound_after Hcross_after)))))).
Qed.
Lemma verification_slice_q_create_used_event_map_after__return_paths :
  forall sg tskSt before eid event_rest qid start size buffer,
    before.(inUsedEventStates) eid = None ->
    store_used_event_map sg tskSt before.(inUsedEventStates) **
      used_complete_event sg tskSt (event_addr sg eid) eid
        (verification_slice_q_create_queue_event qid start size)
    |--
    store_used_event_map sg tskSt
      (verification_slice_q_create_event_state before eid event_rest qid start size buffer).(inUsedEventStates).
Proof.
  intros sg tskSt before eid event_rest qid start size buffer Hnone.
  unfold store_used_event_map, verification_slice_q_create_event_state. simpl.
  sep_apply_l_atomic
    (store_map_equiv_store_map_missing
      (fun eid0 e =>
        used_complete_event sg tskSt (event_addr sg eid0) eid0 e)
      before.(inUsedEventStates) eid Hnone).
  assert (Hother : forall eid0, eid0 <> eid ->
    before.(inUsedEventStates) eid0 =
      (if Z.eqb eid0 eid then Some (verification_slice_q_create_queue_event qid start size)
       else before.(inUsedEventStates) eid0)).
  { intros eid0 Hneq.
    apply Z.eqb_neq in Hneq. rewrite Hneq. reflexivity. }
  pose proof
    (proj1 (store_map_missing_i_equiv
      (fun eid0 e =>
        used_complete_event sg tskSt (event_addr sg eid0) eid0 e)
      before.(inUsedEventStates)
      (fun eid0 =>
        if Z.eqb eid0 eid
        then Some (verification_slice_q_create_queue_event qid start size)
        else before.(inUsedEventStates) eid0)
      eid Hother)) as Hmissing.
  sep_apply_l_atomic Hmissing.
  apply (store_map_merge
    (fun eid0 e =>
      used_complete_event sg tskSt (event_addr sg eid0) eid0 e)
    eid (verification_slice_q_create_queue_event qid start size)
    (fun eid0 =>
      if Z.eqb eid0 eid
      then Some (verification_slice_q_create_queue_event qid start size)
      else before.(inUsedEventStates) eid0)).
  rewrite Z.eqb_refl. reflexivity.
Qed.
Lemma verification_slice_q_create_initialized_event__return_paths :
  forall sg tskSt eid qid start size,
    (event_addr sg eid + OSEventGrp_off) # UChar |-> 0 **
    (event_addr sg eid + OSEventTbl_off) # UChar |-> 0 **
    (event_addr sg eid + OSEventTbl_off + 1) # UChar |-> 0 **
    (event_addr sg eid + OSEventTbl_off + 2) # UChar |-> 0 **
    (event_addr sg eid + OSEventTbl_off + 3) # UChar |-> 0 **
    (event_addr sg eid + OSEventTbl_off + 4) # UChar |-> 0 **
    (event_addr sg eid + OSEventTbl_off + 5) # UChar |-> 0 **
    (event_addr sg eid + OSEventTbl_off + 6) # UChar |-> 0 **
    (event_addr sg eid + OSEventTbl_off + 7) # UChar |-> 0 **
    (event_addr sg eid + OSEventType_off) # UChar |-> 2 **
    (event_addr sg eid + OSEventPtr_off) # Ptr |-> qcb_addr sg qid **
    (event_addr sg eid + OSEventCnt_off) # UShort |-> 0
    |--
    used_complete_event sg tskSt (event_addr sg eid) eid
      (verification_slice_q_create_queue_event qid start size).
Proof.
  intros sg tskSt eid qid start size.
  unfold used_complete_event, verification_slice_q_create_queue_event, q_create_queue_fields,
    encode_event_type, verification_slice_encode_event_ptr_value, encode_event_cnt_value,
    encode_event_wait_grp, encode_event_wait_tbl_at.
  simpl.
  replace (event_addr sg eid + OSEventTbl_off + 0)
    with (event_addr sg eid + OSEventTbl_off) by lia.
  cancel ((event_addr sg eid + OSEventType_off) # UChar |-> 2).
  cancel ((event_addr sg eid + OSEventPtr_off) # Ptr |-> qcb_addr sg qid).
  cancel ((event_addr sg eid + OSEventCnt_off) # UShort |-> 0).
  cancel ((event_addr sg eid + OSEventGrp_off) # UChar |-> 0).
  cancel ((event_addr sg eid + OSEventTbl_off) # UChar |-> 0).
  cancel ((event_addr sg eid + OSEventTbl_off + 1) # UChar |-> 0).
  cancel ((event_addr sg eid + OSEventTbl_off + 2) # UChar |-> 0).
  cancel ((event_addr sg eid + OSEventTbl_off + 3) # UChar |-> 0).
  cancel ((event_addr sg eid + OSEventTbl_off + 4) # UChar |-> 0).
  cancel ((event_addr sg eid + OSEventTbl_off + 5) # UChar |-> 0).
  cancel ((event_addr sg eid + OSEventTbl_off + 6) # UChar |-> 0).
  cancel ((event_addr sg eid + OSEventTbl_off + 7) # UChar |-> 0).
Qed.
Lemma verification_slice_q_create_event_inv_after__return_paths :
  forall sg tskSt before eid event_rest qid start size buffer,
    before.(inUsedEventStates) eid = None ->
    verification_slice_event_in_range sg tskSt
      (verification_slice_q_create_event_state before eid event_rest qid start size buffer) ->
    verification_slice_event_inv_free_head_rest sg tskSt before event_rest **
    sg.(g_OSEventFreeList) # Ptr |-> free_event_head sg event_rest **
    used_complete_event sg tskSt (event_addr sg eid) eid
      (verification_slice_q_create_queue_event qid start size)
    |--
    verification_slice_event_inv sg tskSt
      (verification_slice_q_create_event_state before eid event_rest qid start size buffer).
Proof.
  intros sg tskSt before eid event_rest qid start size buffer Hnone Hvalid.
  unfold verification_slice_event_inv, verification_slice_event_inv_free_head_rest, store_free_event_list.
  pureIntros.
  apply _derivable1_andp_intros.
  - apply derivable1s_coq_prop_r. exact Hvalid.
  - sep_apply_l_atomic
      (verification_slice_q_create_used_event_map_after__return_paths
        sg tskSt before eid event_rest qid start size buffer Hnone).
    simpl [verification_slice_q_create_event_state].
    cancel.
Qed.
Lemma verification_slice_q_create_outside_after__return_paths :
  forall sg lvs eid event_rest qid start size buffer,
    q_create_outside sg lvs |--
    q_create_outside sg
      (verification_slice_q_create_success_state lvs eid event_rest qid start size buffer).
Proof.
  intros sg lvs eid event_rest qid start size buffer.
  unfold q_create_outside, ucos2_rules_lib.OutsideCritical,
    UCOS2_C_Rules.OutsideCritical,
    UCOS2_Critical_Rules.OutsideCritical.
  Intros s'. Exists s'. split_pure_spatial.
  - cancel.
  - dump_pre_spatial. exact H.
Qed.
Lemma verification_slice_q_create_event_lookup_after__return_paths :
  forall before eid event_rest qid start size buffer,
    (verification_slice_q_create_event_state before eid event_rest qid start size buffer).(inUsedEventStates) eid =
    Some (verification_slice_q_create_queue_event qid start size).
Proof.
  intros. unfold verification_slice_q_create_event_state. simpl.
  rewrite Z.eqb_refl. reflexivity.
Qed.
Lemma verification_slice_q_create_event_residual_valid__return_paths :
  forall sg lvs event_rest,
    verification_slice_q_create_event_residual sg lvs event_rest |--
    coq_prop
      (verification_slice_event_in_range sg lvs.(TskState) lvs.(EventState)).
Proof.
  intros sg lvs event_rest.
  unfold verification_slice_q_create_event_residual, verification_slice_event_inv_free_head_rest.
  pureIntros.
  apply derivable1s_coq_prop_r.
  exact H.
Qed.

(** Native queue-storage compatibility is an ownership transfer, not an
    additional conjunct of the public precondition.  The historical public
    world continues to return its QCB and exact [PtrArray.full] resource.
    A client already owning the other published queues can fold that frame
    and the newly returned resources into the native storage of the SAME
    success state.  No full native task/event/critical-wrapper claim follows. *)

Lemma verification_slice_q_create_published_buffer_lookup :
  forall before eid event_rest qid start size buffer,
    (verification_slice_q_create_event_state before eid event_rest qid start size buffer)
      .(publishedQueueBytes) qid = Some (map (@Some addr) buffer).
Proof.
  intros; unfold verification_slice_q_create_event_state; simpl; rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma verification_slice_q_create_published_buffer_other :
  forall before eid event_rest qid start size buffer other,
    other <> qid ->
    (verification_slice_q_create_event_state before eid event_rest qid start size buffer)
      .(publishedQueueBytes) other = before.(publishedQueueBytes) other.
Proof.
  intros; unfold verification_slice_q_create_event_state; simpl.
  apply Z.eqb_neq in H; rewrite H; reflexivity.
Qed.

Lemma verification_slice_q_create_used_event_other :
  forall before eid event_rest qid start size buffer other,
    other <> eid ->
    (verification_slice_q_create_event_state before eid event_rest qid start size buffer)
      .(inUsedEventStates) other = before.(inUsedEventStates) other.
Proof.
  intros; unfold verification_slice_q_create_event_state; simpl.
  apply Z.eqb_neq in H; rewrite H; reflexivity.
Qed.

Lemma q_create_initial_slots :
  forall qid start size buffer,
    Zlength buffer = size ->
    queue_slots_model (q_create_queue_fields qid start size)
      (map (@Some addr) buffer).
Proof.
  intros qid start size buffer Hlen; split.
  - rewrite !Zlength_correct in *; rewrite map_length; exact Hlen.
  - intros i p [k [Hrange _]].
    change (0 <= k < 0) in Hrange.
    lia.
Qed.

Lemma q_create_buffer_to :
  forall qid start size buffer,
    Zlength buffer = size ->
    PtrArray.full start size buffer |--
    queue_buffer_rep (q_create_queue_fields qid start size)
      (map (@Some addr) buffer).
Proof.
  intros qid start size buffer Hlen.
  unfold queue_buffer_rep.
  apply _derivable1_andp_intros.
  - apply derivable1s_coq_prop_r; apply q_create_initial_slots; exact Hlen.
  - apply PtrArray.full_to_mixed_full.
Qed.

Lemma q_create_buffer_to_full :
  forall qid start size buffer,
    queue_buffer_rep (q_create_queue_fields qid start size)
      (map (@Some addr) buffer) |-- PtrArray.full start size buffer.
Proof.
  intros; unfold queue_buffer_rep; pureIntros.
  apply PtrArray.mixed_full_to_full.
Qed.

Lemma q_create_pool_head_unbound :
  forall sg before qid queue_rest,
    queue_pool_partition sg before (qid :: queue_rest) ->
    forall eid e q, before.(inUsedEventStates) eid = Some e ->
      e.(queueFields) = Some q -> q.(qID) <> qid.
Proof.
  intros sg before qid queue_rest Hpool eid e q Hused Hfields Heq.
  destruct (queue_pool_free_unallocated sg before (qid :: queue_rest) qid
    Hpool (or_introl eq_refl)) as [Hnot_published _].
  apply Hnot_published; exists eid, e, q; auto.
Qed.

Lemma verification_slice_q_create_binding_after :
  forall sg before eid event_rest qid queue_rest start size buffer,
    before.(inUsedEventStates) eid = None ->
    queue_pool_partition sg before (qid :: queue_rest) ->
    queue_published_storage_binding before ->
    Zlength buffer = size ->
    queue_published_storage_binding
      (verification_slice_q_create_event_state before eid event_rest qid start size buffer).
Proof.
  intros sg before eid event_rest qid queue_rest start size buffer
    Hnone Hpool [Hforward [Hback Hunique]] Hlen.
  pose proof (q_create_pool_head_unbound sg before qid queue_rest Hpool) as Hfresh.
  split; [|split].
  - intros key e q Hused Hfields.
    unfold verification_slice_q_create_event_state in Hused; simpl in Hused.
    destruct (Z.eqb key eid) eqn:Hkey.
    + inversion Hused; subst e; simpl in Hfields; inversion Hfields; subst q.
      split; [reflexivity|]. exists (map (@Some addr) buffer); split.
      * apply verification_slice_q_create_published_buffer_lookup.
      * apply q_create_initial_slots; exact Hlen.
    + destruct (Hforward key e q Hused Hfields) as [Htype [slots [Hbytes Hmodel]]].
      split; [exact Htype|]. exists slots; split; [|exact Hmodel].
      rewrite verification_slice_q_create_published_buffer_other; [exact Hbytes|].
      eapply Hfresh; eauto.
  - intros key slots Hbytes.
    unfold verification_slice_q_create_event_state in Hbytes; simpl in Hbytes.
    destruct (Z.eqb key qid) eqn:Hkey.
    + apply Z.eqb_eq in Hkey; subst key.
      exists eid, (verification_slice_q_create_queue_event qid start size),
        (q_create_queue_fields qid start size).
      split; [apply verification_slice_q_create_event_lookup_after__return_paths|].
      split; reflexivity.
    + destruct (Hback key slots Hbytes) as [old_id [e [q [Hused [Hfields Hid]]]]].
      exists old_id, e, q; split; [|auto].
      rewrite verification_slice_q_create_used_event_other; [exact Hused|].
      intro Heq; subst old_id; rewrite Hnone in Hused; discriminate.
  - intros key1 key2 e1 e2 q1 q2 Hused1 Hused2 Hfields1 Hfields2 Hid.
    unfold verification_slice_q_create_event_state in Hused1, Hused2; simpl in Hused1, Hused2.
    destruct (Z.eqb key1 eid) eqn:Hkey1;
      destruct (Z.eqb key2 eid) eqn:Hkey2.
    + apply Z.eqb_eq in Hkey1, Hkey2; congruence.
    + inversion Hused1; subst e1; simpl in Hfields1; inversion Hfields1; subst q1.
      exfalso; apply (Hfresh key2 e2 q2 Hused2 Hfields2); symmetry; exact Hid.
    + inversion Hused2; subst e2; simpl in Hfields2; inversion Hfields2; subst q2.
      exfalso; apply (Hfresh key1 e1 q1 Hused1 Hfields1); exact Hid.
    + eapply Hunique; eauto.
Qed.

Lemma verification_slice_q_create_pool_partition_after :
  forall sg before eid event_rest qid queue_rest start size buffer,
    before.(inUsedEventStates) eid = None ->
    queue_pool_partition sg before (qid :: queue_rest) ->
    queue_pool_partition sg
      (verification_slice_q_create_event_state before eid event_rest qid start size buffer) queue_rest.
Proof.
  intros sg before eid event_rest qid queue_rest start size buffer Hnone
    [[Hnodup Hids] [Hpartition [Hdisjoint Hprivate_unique]]].
  inversion Hnodup as [|? ? Hnotin Hrestnodup]; subst.
  inversion Hids as [|? ? Hqid Hrestids]; subst.
  assert (Hlive : forall key,
    (exists id e q,
       (verification_slice_q_create_event_state before eid event_rest qid start size buffer)
          .(inUsedEventStates) id = Some e /\
       e.(queueFields) = Some q /\ q.(qID) = key) <->
    key = qid \/ (exists id e q, before.(inUsedEventStates) id = Some e /\
       e.(queueFields) = Some q /\ q.(qID) = key)).
  { intro key; split.
    - intros [id [e [q [Hused [Hfields Hid]]]]].
      unfold verification_slice_q_create_event_state in Hused; simpl in Hused.
      destruct (Z.eqb id eid).
      + inversion Hused; subst e; simpl in Hfields; inversion Hfields; subst q.
        left; symmetry; exact Hid.
      + right; exists id, e, q; auto.
    - intros [->|[id [e [q [Hused [Hfields Hid]]]]]].
      + exists eid, (verification_slice_q_create_queue_event qid start size),
          (q_create_queue_fields qid start size).
        split; [apply verification_slice_q_create_event_lookup_after__return_paths|]; split; reflexivity.
      + exists id, e, q; split; [|auto].
        rewrite verification_slice_q_create_used_event_other; [exact Hused|].
        intro Heq; subst id; rewrite Hnone in Hused; discriminate. }
  split; [split; assumption|]. split.
  - intro key.
    change ((queue_slot_published
      (verification_slice_q_create_event_state before eid event_rest qid start size buffer) key \/
      queue_slot_private before key) <-> valid_queue_id sg key /\ ~ In key queue_rest).
    unfold queue_slot_published; rewrite Hlive.
    change (((key = qid \/ queue_slot_published before key) \/
      queue_slot_private before key) <-> valid_queue_id sg key /\ ~ In key queue_rest).
    split.
    + intros [[Heq|Hpublished]|Hprivate].
      * subst key; auto.
      * destruct (proj1 (Hpartition key) (or_introl Hpublished)) as [Hrange Hfree].
        split; [exact Hrange|]; intro Hin; apply Hfree; right; exact Hin.
      * destruct (proj1 (Hpartition key) (or_intror Hprivate)) as [Hrange Hfree].
        split; [exact Hrange|]; intro Hin; apply Hfree; right; exact Hin.
    + intros [Hrange Hfree]; destruct (Z.eq_dec key qid) as [Heq|Hneq].
      * left; left; exact Heq.
      * assert (Hold : queue_slot_published before key \/ queue_slot_private before key).
        { apply (proj2 (Hpartition key)); split; [exact Hrange|].
          simpl; intros [Heq|Hin]; [congruence|contradiction]. }
        tauto.
  - split; [|exact Hprivate_unique].
    intros key Hpublished Hprivate.
    apply Hlive in Hpublished; destruct Hpublished as [Heq|Hold].
    + subst key.
      destruct (proj1 (Hpartition qid) (or_intror Hprivate)) as [_ Hfree].
      apply Hfree; left; reflexivity.
    + exact (Hdisjoint key Hold Hprivate).
Qed.

Lemma verification_slice_q_create_old_published_map_frame :
  forall sg before eid event_rest qid queue_rest start size buffer,
    queue_pool_partition sg before (qid :: queue_rest) ->
    store_map (published_queue_node_rep sg before)
      before.(inUsedEventStates) |--
    store_map (published_queue_node_rep sg
      (verification_slice_q_create_event_state before eid event_rest qid start size buffer))
      before.(inUsedEventStates).
Proof.
  intros sg before eid event_rest qid queue_rest start size buffer Hpool.
  pose proof (q_create_pool_head_unbound sg before qid queue_rest Hpool) as Hfresh.
  unfold store_map; Intros keys; Exists keys.
  assert (Hnodes :
    map (fun key => match before.(inUsedEventStates) key with
      | Some e => published_queue_node_rep sg before key e
      | None => emp end) keys =
    map (fun key => match before.(inUsedEventStates) key with
      | Some e => published_queue_node_rep sg
        (verification_slice_q_create_event_state before eid event_rest qid start size buffer) key e
      | None => emp end) keys).
  { apply map_ext; intro key.
    destruct (before.(inUsedEventStates) key) as [e|] eqn:Hused; [|reflexivity].
    unfold published_queue_node_rep.
    destruct e.(queueFields) as [q|] eqn:Hfields; [|reflexivity].
    pose proof (Hfresh key e q Hused Hfields) as Hneq.
    unfold verification_slice_q_create_event_state; simpl.
    apply Z.eqb_neq in Hneq; rewrite Hneq; reflexivity. }
  rewrite Hnodes; entailer!.
Qed.

Lemma verification_slice_q_create_initialized_node :
  forall sg before eid event_rest qid start size buffer,
    Zlength buffer = size ->
    used_queue_control_block sg (q_create_queue_fields qid start size) **
    PtrArray.full start size buffer |--
    published_queue_node_rep sg
      (verification_slice_q_create_event_state before eid event_rest qid start size buffer)
      eid (verification_slice_q_create_queue_event qid start size).
Proof.
  intros sg before eid event_rest qid start size buffer Hlen.
  unfold published_queue_node_rep.
  cbn [verification_slice_q_create_queue_event q_create_queue_fields].
  Exists (map (@Some addr) buffer).
  sep_apply_l_atomic (q_create_buffer_to qid start size buffer Hlen).
  apply _derivable1_andp_intros.
  - apply derivable1s_coq_prop_r; apply verification_slice_q_create_published_buffer_lookup.
  - cancel.
Qed.

Lemma verification_slice_q_create_node_recovers_public_resources :
  forall sg before eid event_rest qid start size buffer,
    published_queue_node_rep sg
      (verification_slice_q_create_event_state before eid event_rest qid start size buffer)
      eid (verification_slice_q_create_queue_event qid start size) |--
    used_queue_control_block sg (q_create_queue_fields qid start size) **
    PtrArray.full start size buffer.
Proof.
  intros; unfold published_queue_node_rep.
  cbn [verification_slice_q_create_queue_event q_create_queue_fields]; Intros slots.
  rewrite verification_slice_q_create_published_buffer_lookup in H; inversion H; subst slots.
  sep_apply_l_atomic (q_create_buffer_to_full qid start size buffer).
  cancel.
Qed.

Lemma verification_slice_q_create_published_map_after :
  forall sg before eid event_rest qid queue_rest start size buffer,
    before.(inUsedEventStates) eid = None ->
    queue_pool_partition sg before (qid :: queue_rest) ->
    Zlength buffer = size ->
    store_map (published_queue_node_rep sg before)
      before.(inUsedEventStates) **
    used_queue_control_block sg (q_create_queue_fields qid start size) **
    PtrArray.full start size buffer |--
    store_map (published_queue_node_rep sg
      (verification_slice_q_create_event_state before eid event_rest qid start size buffer))
      (verification_slice_q_create_event_state before eid event_rest qid start size buffer)
        .(inUsedEventStates).
Proof.
  intros sg before eid event_rest qid queue_rest start size buffer Hnone Hpool Hlen.
  sep_apply_l_atomic (verification_slice_q_create_old_published_map_frame
    sg before eid event_rest qid queue_rest start size buffer Hpool).
  sep_apply_l_atomic (store_map_equiv_store_map_missing
    (published_queue_node_rep sg
      (verification_slice_q_create_event_state before eid event_rest qid start size buffer))
    before.(inUsedEventStates) eid Hnone).
  assert (Hother : forall key, key <> eid ->
    before.(inUsedEventStates) key =
    (verification_slice_q_create_event_state before eid event_rest qid start size buffer)
      .(inUsedEventStates) key).
  { intros; symmetry; apply verification_slice_q_create_used_event_other; assumption. }
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (published_queue_node_rep sg
      (verification_slice_q_create_event_state before eid event_rest qid start size buffer))
    before.(inUsedEventStates)
    (verification_slice_q_create_event_state before eid event_rest qid start size buffer)
      .(inUsedEventStates) eid Hother)).
  sep_apply_l_atomic (verification_slice_q_create_initialized_node
    sg before eid event_rest qid start size buffer Hlen).
  sep_apply_l_atomic (store_map_merge
    (published_queue_node_rep sg
      (verification_slice_q_create_event_state before eid event_rest qid start size buffer))
    eid (verification_slice_q_create_queue_event qid start size)
    (verification_slice_q_create_event_state before eid event_rest qid start size buffer)
      .(inUsedEventStates)
    (verification_slice_q_create_event_lookup_after__return_paths
      before eid event_rest qid start size buffer)).
  cancel.
Qed.

Lemma verification_slice_q_create_storage_transfer :
  forall sg before eid event_rest qid queue_rest start size buffer,
    before.(inUsedEventStates) eid = None ->
    queue_pool_partition sg before (qid :: queue_rest) ->
    queue_published_storage_binding before ->
    Zlength buffer = size ->
    store_map (published_queue_node_rep sg before)
      before.(inUsedEventStates) **
    store_free_queue_list sg queue_rest **
    used_queue_control_block sg (q_create_queue_fields qid start size) **
    PtrArray.full start size buffer |--
    queue_storage_rep sg
      (verification_slice_q_create_event_state before eid event_rest qid start size buffer).
Proof.
  intros sg before eid event_rest qid queue_rest start size buffer
    Hnone Hpool Hbinding Hlen.
  pose proof (verification_slice_q_create_binding_after sg before eid event_rest qid queue_rest
    start size buffer Hnone Hpool Hbinding Hlen) as Hbinding_after.
  pose proof (verification_slice_q_create_pool_partition_after sg before eid event_rest qid queue_rest
    start size buffer Hnone Hpool) as Hpool_after.
  unfold queue_storage_rep.
  apply _derivable1_andp_intros.
  - apply derivable1s_coq_prop_r; exact Hbinding_after.
  - sep_apply_l_atomic (verification_slice_q_create_published_map_after
      sg before eid event_rest qid queue_rest start size buffer Hnone Hpool Hlen).
    Exists queue_rest; entailer!.
Qed.

(** The compatibility post has the old event/interrupt/public observations
    and the current queue-storage component. The free list and selected QCB/
    buffer occur only inside the latter, never twice.  Its existing-event
    representation remains the historical event interface; converting it to
    [event_raw_rep] requires the separately selected TCB-layout and
    wait-encoding interface and is not asserted by this theorem. *)
Definition verification_slice_q_create_storage_post
  (sg : StableGlobVars) (start size : Z) (buffer : list addr)
  (lvs : UCOS2_Verify_State) (eid : EventID) (qid : QueueID)
  (queue_rest : list QueueID) : Assertion :=
  coq_prop
    (verification_slice_q_create_world_pure sg start size buffer lvs queue_rest /\
     lvs.(EventState).(inUsedEventStates) eid =
       Some (verification_slice_q_create_queue_event qid start size) /\
     lvs.(EventState).(publishedQueueBytes) qid = Some (map (@Some addr) buffer)) &&
  q_create_outside sg lvs ** interrupt_inv sg lvs.(IntrState) **
  verification_slice_event_inv sg lvs.(TskState) lvs.(EventState) **
  queue_storage_rep sg lvs.(EventState).

Lemma verification_slice_q_create_success_world_storage_consequence :
  forall sg start size buffer before eid event_rest qid queue_rest,
    before.(EventState).(inUsedEventStates) eid = None ->
    queue_pool_partition sg before.(EventState) (qid :: queue_rest) ->
    queue_published_storage_binding before.(EventState) ->
    verification_slice_q_create_success_world sg start size buffer
      (verification_slice_q_create_success_state before eid event_rest qid start size buffer)
      eid qid queue_rest **
    store_map (published_queue_node_rep sg before.(EventState))
      before.(EventState).(inUsedEventStates) |--
    verification_slice_q_create_storage_post sg start size buffer
      (verification_slice_q_create_success_state before eid event_rest qid start size buffer)
      eid qid queue_rest.
Proof.
  intros sg start size buffer before eid event_rest qid queue_rest Hnone Hpool Hbinding.
  unfold verification_slice_q_create_success_world; pureIntros.
  destruct H as [Hworld [Hlookup Hbytes]].
  assert (Hlen : Zlength buffer = size).
  { unfold verification_slice_q_create_world_pure in Hworld; tauto. }
  unfold verification_slice_q_create_storage_post.
  apply _derivable1_andp_intros.
  - apply derivable1s_coq_prop_r; auto.
  - sep_apply_l_atomic (verification_slice_q_create_storage_transfer
      sg before.(EventState) eid event_rest qid queue_rest start size buffer
      Hnone Hpool Hbinding Hlen).
    unfold q_create_outside, verification_slice_q_create_success_state; cbn [replace_EventS EventState]; cancel.
Qed.
