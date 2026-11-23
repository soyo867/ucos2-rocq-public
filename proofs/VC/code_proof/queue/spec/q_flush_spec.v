Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib MapLib.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.lib.task.
Require Export Ucos2Verify.lib.sched.
Require Export Ucos2Verify.lib.tick.
Require Export Ucos2Verify.lib.event.
Require Export Ucos2Verify.lib.event_wait.
Require Export Ucos2Verify.lib.queue_core.
Require Export Ucos2Verify.lib.kernel_resources.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.lib.cross_module_invariants.
Require Export Ucos2Verify.lib.error_codes.

Import ListNotations.
Import UCOS2_C_Rules.
Import TaskStateDef EventStateDef.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** OSQFlush, Source/os_q.c:372-396, selected V2.93.01 profile.
    This file owns only the ordered operation, its three-write stage and
    operation-specific preservation facts.  Queue values, layout, event
    update, global invariants and interrupt relations retain shared owners. *)

Definition q_flush_event (e : OSEventAbstractState) : OSEventAbstractState :=
  match e.(queueFields) with
  | Some q => event_set_queue_fields e (queue_flush_state q)
  | None => e
  end.

Definition q_flush_state (before : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState) : UCOS2_Verify_State :=
  update_event_field before eid (q_flush_event e).

Definition OSQFlush_sem (pevent : addr) (eid : EventID)
  : program UCOS2_Verify_State Z :=
  fun before ret after =>
    if Z.eqb pevent 0 then
      ret = encode_os_err_code OS_ERR_PEVENT_NULL /\ after = before
    else
      match before.(EventState).(inUsedEventStates) eid with
      | None => ret = encode_os_err_code OS_ERR_EVENT_TYPE /\ after = before
      | Some e =>
          match e.(eventType) with
          | OS_EVENT_TYPE_Q =>
              e.(queueFields) <> None /\
              ret = encode_os_err_code OS_ERR_NONE /\
              after = q_flush_state before eid e
          | _ => ret = encode_os_err_code OS_ERR_EVENT_TYPE /\ after = before
          end
      end.

Definition q_flush_endpoint (pevent eid : Z) (before : UCOS2_Verify_State)
  : UCOS2_Verify_State :=
  if Z.eqb pevent 0 then before else
  match before.(EventState).(inUsedEventStates) eid with
  | Some e =>
      match e.(eventType) with
      | OS_EVENT_TYPE_Q => q_flush_state before eid e
      | _ => before
      end
  | None => before
  end.

Definition QFlushContinuation : Type :=
  Z -> (UCOS2_Verify_State -> Prop) -> Prop.

Definition q_flush_safe_pre (pevent eid : Z)
  (entry : UCOS2_Verify_State) (X : QFlushContinuation) : Prop :=
  safeExec (LastSeen entry) (atomic_cmd (OSQFlush_sem pevent eid)) X.

Definition q_flush_safe_post (after : UCOS2_Verify_State)
  (ret : Z) (X : QFlushContinuation) : Prop :=
  safeExec (LastSeen after)
    (@StateRelMonad.ret (UCOS2_Verify_State -> Prop) Z ret) X.

Definition q_flush_input_domain (sg : StableGlobVars) (pevent eid : Z) : Prop :=
  pevent = 0 \/ (valid_event_id sg eid /\ pevent = event_addr sg eid).

Definition q_flush_profile (sg : StableGlobVars) : Prop :=
  valid_stable_glob_vars sg /\
  event_table_layout_prop sg /\
  queue_table_layout_prop sg sg.(g_OSQTbl) /\
  queue_first_round_profile sg.

(** R is an arbitrary concrete assertion for precisely the untouched
    storage: OSQPtr, OSQEnd, OSQSize and the message buffer.  A caller can
    instantiate it with exact byte/slot values; the very same R is returned.
    Pointed-to objects remain separate disjoint caller frames: this API
    neither reads nor frees them.  The refinement below permits
    the weakest canonical representation too, including uninitialised
    stale slots, so snapshot precision does not narrow the public domain.
    This operation-local stage is not a new canonical queue representation. *)
Definition QFlushMemory : Type := Assertion.
Definition q_flush_memory (R : QFlushMemory) : Assertion := R.

Definition q_flush_readonly_refines (sg : StableGlobVars)
  (q : QueueFields) (R : QFlushMemory) : Prop :=
  R |--
    (qcb_addr sg q.(qID) + OSQPtr_off) # Ptr |->_ **
    (qcb_addr sg q.(qID) + OSQEnd_off) # Ptr |-> queue_end_addr q **
    (qcb_addr sg q.(qID) + OSQSize_off) # UShort |-> q.(qSize) **
    EX slots, queue_buffer_rep q slots.

Definition q_flush_write_stage (sg : StableGlobVars) (q : QueueFields)
  (qin qout count : Z) (R : QFlushMemory) : Assertion :=
  (qcb_addr sg q.(qID) + OSQStart_off) # Ptr |-> q.(qStart) **
  (qcb_addr sg q.(qID) + OSQIn_off) # Ptr |-> qin **
  (qcb_addr sg q.(qID) + OSQOut_off) # Ptr |-> qout **
  (qcb_addr sg q.(qID) + OSQEntries_off) # UShort |-> count ** R.

(** The arbitrary exact snapshot and the canonical read-only view describe
    the same heap (andp), not two disjoint copies of the QCB/ring.  The
    published slot witness is retained through all three source writes. *)
Definition q_flush_readonly_storage (sg : StableGlobVars) (q : QueueFields)
  (slots : list (option addr)) : Assertion :=
  (qcb_addr sg q.(qID) + OSQPtr_off) # Ptr |->_ **
  (qcb_addr sg q.(qID) + OSQEnd_off) # Ptr |-> queue_end_addr q **
  (qcb_addr sg q.(qID) + OSQSize_off) # UShort |-> q.(qSize) **
  queue_buffer_rep q slots.

Definition q_flush_queue_rest (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (eid : EventID) (free : list QueueID) : Assertion :=
  event_raw_rep sg s.(TskState) s.(EventState) **
  store_map_missing_i (published_queue_node_rep sg s.(EventState))
    s.(EventState).(inUsedEventStates) eid **
  store_free_queue_list sg free ** UCOS2_raw_rep_missing_event_queue sg s.

Definition q_flush_stage_facts (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState) (q : QueueFields)
  (free : list QueueID) (slots : list (option addr)) : Prop :=
  UCOS2_state_inv sg s /\ s.(EventState).(inUsedEventStates) eid = Some e /\
  e.(eventType) = OS_EVENT_TYPE_Q /\ e.(queueFields) = Some q /\
  queue_published_storage_binding s.(EventState) /\
  queue_pool_partition sg s.(EventState) free /\
  s.(EventState).(publishedQueueBytes) q.(qID) = Some slots.

Definition q_flush_owned_stage (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState) (q : QueueFields)
  (free : list QueueID) (slots : list (option addr))
  (qin qout count : Z) (R : QFlushMemory) : Assertion :=
  coq_prop (q_flush_stage_facts sg s eid e q free slots) &&
  (q_flush_write_stage sg q qin qout count
     (R && q_flush_readonly_storage sg q slots) **
   q_flush_queue_rest sg s eid free).

Definition q_flush_queue_storage (sg : StableGlobVars)
  (pevent eid : Z) (s : UCOS2_Verify_State) (R : QFlushMemory) : Assertion :=
  if Z.eqb pevent 0 then UCOS2_inv sg s else
  match s.(EventState).(inUsedEventStates) eid with
  | Some e =>
      match e.(eventType), e.(queueFields) with
      | OS_EVENT_TYPE_Q, Some q =>
          EX free, EX slots,
            q_flush_owned_stage sg s eid e q free slots
              (queue_in_addr q) (queue_out_addr q) (queue_entries q) R
      | _, _ => UCOS2_inv sg s
      end
  | None => UCOS2_inv sg s
  end.

Definition q_flush_snapshot (sg : StableGlobVars)
  (pevent eid : Z) (entry : UCOS2_Verify_State) (R : QFlushMemory) : Prop :=
  if Z.eqb pevent 0 then True else
  match entry.(EventState).(inUsedEventStates) eid with
  | Some e =>
      match e.(eventType), e.(queueFields) with
      | OS_EVENT_TYPE_Q, Some q => q_flush_readonly_refines sg q R
      | _, _ => True
      end
  | None => True
  end.

Definition q_flush_world (sg : StableGlobVars) (pevent eid : Z)
  (entry current : UCOS2_Verify_State) (R : QFlushMemory) : Assertion :=
  coq_prop (q_flush_profile sg /\ q_flush_input_domain sg pevent eid /\
    q_flush_snapshot sg pevent eid entry R) &&
  q_flush_queue_storage sg pevent eid current R.

(** Parser-facing aliases preserve the complete canonical global invariant
    and exact critical entry/current-state distinction. *)
Definition q_flush_global (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion := UCOS2_inv sg s.
Definition q_flush_outside (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion := ucos2_rules_lib.OutsideCritical sg s.
Definition q_flush_inside (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion := ucos2_rules_lib.InsideCritical sg s.
Definition q_flush_type (s : UCOS2_Verify_State) (eid : Z) : Z :=
  event_slot_type_value s.(EventState) eid.
Definition q_flush_no_type (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (eid : Z) : Assertion :=
  UCOS2_verification_slice_inv_no_event_type sg s eid.
Definition q_flush_event_lookup (s : UCOS2_Verify_State)
  (eid : Z) (e : OSEventAbstractState) (q : QueueFields) : Prop :=
  s.(EventState).(inUsedEventStates) eid = Some e /\
  e.(eventType) = OS_EVENT_TYPE_Q /\ e.(queueFields) = Some q.

(** Total ghost selectors give successive C annotations a stable name for
    the same lookup.  Their fallback is never dereferenced: the public
    type guard and the existing event validity establish the live arm. *)
Definition q_flush_selected_event (s : UCOS2_Verify_State) (eid : Z)
  : OSEventAbstractState :=
  match s.(EventState).(inUsedEventStates) eid with
  | Some e => e
  | None => {| eventType := OS_EVENT_TYPE_UNUSED;
      mutexFields := None; semFields := None; mboxFields := None;
      queueFields := None; waitList := []; eventGeneration := 0;
      eventName := 0; eventPadding1 := None; eventPadding2 := None;
      eventPadding3 := None; eventPadding19 := None |}
  end.
Definition q_flush_selected_queue (s : UCOS2_Verify_State) (eid : Z)
  : QueueFields :=
  match (q_flush_selected_event s eid).(queueFields) with
  | Some q => q
  | None => {| qID := 0; qStart := 0; qSize := 0;
      qInIndex := 0; qOutIndex := 0; qMessages := [] |}
  end.
Definition q_flush_view (s : UCOS2_Verify_State) (eid : Z)
  (e : OSEventAbstractState) (q : QueueFields) : Prop :=
  e = q_flush_selected_event s eid /\ q = q_flush_selected_queue s eid.
Lemma q_flush_view_total : forall s eid,
  exists e q, q_flush_view s eid e q.
Proof.
  intros. exists (q_flush_selected_event s eid), (q_flush_selected_queue s eid).
  split; reflexivity.
Qed.
Definition q_flush_event_rest (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (eid : Z) (e : OSEventAbstractState) : Assertion :=
  (event_addr sg eid + OSEventType_off) # UChar |-> encode_event_type e.(eventType) **
  (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value e **
  used_event_rest_no_type_cnt_ptr sg s.(TskState) (event_addr sg eid) eid e.
Definition q_flush_global_rest (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (eid : Z) : Assertion :=
  interrupt_inv sg s.(IntrState) ** verification_slice_task_inv sg s.(TskState) **
  verification_slice_sched_inv sg s.(TskState) s.(SchedState) **
  verification_slice_event_inv_no_eid sg s.(TskState) s.(EventState) eid **
  verification_slice_tick_inv sg s.(TickState) **
  coq_prop (verification_slice_cross_module_consistency sg s).

Lemma q_flush_event_identity : forall e,
  (q_flush_event e).(eventType) = e.(eventType) /\
  (q_flush_event e).(waitList) = e.(waitList) /\
  (q_flush_event e).(mutexFields) = e.(mutexFields) /\
  (q_flush_event e).(semFields) = e.(semFields) /\
  (q_flush_event e).(mboxFields) = e.(mboxFields) /\
  (q_flush_event e).(waitList) = e.(waitList) /\
  (q_flush_event e).(eventGeneration) = e.(eventGeneration) /\
  (q_flush_event e).(eventName) = e.(eventName) /\
  (q_flush_event e).(eventPadding1) = e.(eventPadding1) /\
  (q_flush_event e).(eventPadding2) = e.(eventPadding2) /\
  (q_flush_event e).(eventPadding3) = e.(eventPadding3) /\
  (q_flush_event e).(eventPadding19) = e.(eventPadding19).
Proof.
  intros e. destruct e as [ty mf sf mb q wl gen name p1 p2 p3 p19];
    destruct q as [q|]; repeat split; reflexivity.
Qed.

Lemma q_flush_exact_state_frame : forall before eid e,
  let after := q_flush_state before eid e in
  after.(IntrState) = before.(IntrState) /\
  after.(TskState) = before.(TskState) /\
  after.(SchedState) = before.(SchedState) /\
  after.(TickState) = before.(TickState) /\
  after.(EventState).(unUsedEventStates) = before.(EventState).(unUsedEventStates) /\
  after.(EventState).(inUsedEventStates) eid = Some (q_flush_event e) /\
  (forall other, other <> eid ->
    after.(EventState).(inUsedEventStates) other =
    before.(EventState).(inUsedEventStates) other).
Proof.
  intros before eid e. cbn zeta.
  unfold q_flush_state, update_event_field, update_event_field_raw, replace_EventS.
  cbn.
  repeat split; try reflexivity.
  - rewrite Z.eqb_refl. reflexivity.
  - intros other Hneq. apply Z.eqb_neq in Hneq. rewrite Hneq. reflexivity.
Qed.

Lemma q_flush_result_range : forall pevent eid before ret after,
  OSQFlush_sem pevent eid before ret after -> ret = 0 \/ ret = 1 \/ ret = 4.
Proof.
  intros pevent eid before ret after H.
  unfold OSQFlush_sem in H.
  destruct (Z.eqb pevent 0); [cbn in H; tauto|].
  destruct (inUsedEventStates (EventState before) eid) as [e|]; [|cbn in H; tauto].
  destruct (eventType e); cbn in H; tauto.
Qed.

Lemma q_flush_local_validity : forall sg e,
  event_fields_consistency e -> event_payload_consistency sg e ->
  e.(eventType) = OS_EVENT_TYPE_Q ->
  event_fields_consistency (q_flush_event e) /\
  event_payload_consistency sg (q_flush_event e).
Proof.
  intros sg e Hfields Hpayload Htype.
  destruct e as [ty mf sf mb q wl gen name p1 p2 p3 p19].
  cbn in Htype; subst ty.
  destruct q as [q0|] eqn:Hq.
  - cbn [event_fields_consistency event_payload_consistency
      q_flush_event event_set_queue_fields] in *.
    destruct Hfields as [Hm [Hs [Hb Hqnon]]].
    split.
    + split; [exact Hm|]. split; [exact Hs|]. split; [exact Hb|].
      discriminate.
    + apply queue_flush_preserves_consistency_total. exact Hpayload.
  - cbn [event_fields_consistency] in Hfields. contradiction.
Qed.

Lemma q_flush_event_validity : forall sg ts es eid e,
  es.(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_Q ->
  event_in_range sg ts es ->
  event_in_range sg ts (update_event_field_raw es eid (q_flush_event e)).
Proof.
  intros sg ts es eid e Hget Htype Hvalid.
  destruct Hvalid as [Hpartition [Hfree [Hidentity
    [Hfields [Hpayload [Hqueue Hwait]]]]]].
  destruct (q_flush_local_validity sg e (Hfields eid e Hget)
    (Hpayload eid e Hget) Htype) as [Hfields' Hpayload'].
  assert (Hgeneration :
    (q_flush_event e).(eventGeneration) = e.(eventGeneration)).
  { destruct e as [ty mf sf mb q wl gen name p1 p2 p3 p19].
    destruct q as [q|]; reflexivity. }
  assert (Hqid : event_queue_id (q_flush_event e) = event_queue_id e).
  { destruct e as [ty mf sf mb q wl gen name p1 p2 p3 p19].
    destruct q as [q|]; reflexivity. }
  assert (Hwait' : event_wait_entry_consistency sg ts eid (q_flush_event e)).
  { pose proof (q_flush_event_identity e) as Hidentity'.
    destruct Hidentity' as [Hty [Hwl _]].
    unfold event_wait_entry_consistency.
    rewrite Hty, Hwl.
    exact (Hwait eid e Hget). }
  assert (Hvalid' : event_in_range sg ts es).
  { split; [exact Hpartition|]. split; [exact Hfree|].
    split; [exact Hidentity|]. split; [exact Hfields|].
    split; [exact Hpayload|]. split; [exact Hqueue|].
    exact Hwait. }
  eapply event_update_preserves_in_range;
    [exact Hvalid'|exact Hget|exact Hgeneration|exact Hfields'|
     exact Hpayload'|exact Hqid|exact Hwait'].
Qed.

Lemma q_flush_lookup_back : forall before eid e j x,
  before.(EventState).(inUsedEventStates) eid = Some e ->
  (q_flush_state before eid e).(EventState).(inUsedEventStates) j = Some x ->
  exists old,
    before.(EventState).(inUsedEventStates) j = Some old /\
    x.(eventType) = old.(eventType) /\
    x.(mutexFields) = old.(mutexFields) /\
    x.(waitList) = old.(waitList).
Proof.
  intros before eid e j x Hget Hx.
  unfold q_flush_state, update_event_field, update_event_field_raw, replace_EventS in Hx.
  cbn in Hx.
  destruct (Z.eqb j eid) eqn:Hj.
  - apply Z.eqb_eq in Hj. subst j. inversion Hx; subst x.
    exists e. split; [exact Hget|].
    pose proof (q_flush_event_identity e) as Hidentity'.
    destruct Hidentity' as [Hty [Hwl [Hmf _]]].
    split; [exact Hty|]. split; [exact Hmf|exact Hwl].
  - exists x. split; [exact Hx|].
    repeat split; reflexivity.
Qed.

Lemma q_flush_lookup_forward : forall before eid e j old,
  before.(EventState).(inUsedEventStates) j = Some old ->
  exists x, (q_flush_state before eid e).(EventState).(inUsedEventStates) j = Some x.
Proof.
  intros. unfold q_flush_state, update_event_field, update_event_field_raw, replace_EventS.
  cbn.
  destruct (Z.eqb j eid).
  - exists (q_flush_event e). reflexivity.
  - exists old. assumption.
Qed.

Lemma q_flush_mutex_lookup : forall before eid e j x,
  before.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_Q -> x.(eventType) = OS_EVENT_TYPE_MUTEX ->
  ((q_flush_state before eid e).(EventState).(inUsedEventStates) j = Some x <->
   before.(EventState).(inUsedEventStates) j = Some x).
Proof.
  intros before eid e j x Hget He Hx.
  unfold q_flush_state, update_event_field, update_event_field_raw, replace_EventS.
  cbn.
  destruct (Z.eqb j eid) eqn:Hj; [|tauto].
  apply Z.eqb_eq in Hj. subst j. rewrite Hget.
  pose proof (q_flush_event_identity e) as Hidentity'.
  destruct Hidentity' as [Hty [Hwl [Hmf _]]].
  split.
  - intro H; inversion H; subst x. cbn in Hx.
    rewrite Hty in Hx. congruence.
  - intro H; inversion H; subst x. cbn in Hx. congruence.
Qed.

Lemma q_flush_cross_preserved : forall sg before eid e,
  before.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_Q ->
  cross_module_consistency sg before ->
  cross_module_consistency sg (q_flush_state before eid e).
Proof.
  intros sg before eid e Hget Htype Hcross.
  change (cross_module_consistency sg
    (replace_EventS
      (update_event_field_raw before.(EventState) eid (q_flush_event e)) before)).
  eapply cross_module_consistency_event_fields_update; [exact Hget| | | |exact Hcross].
  - destruct e as [ty mf sf mb q wl gen name p1 p2 p3 p19].
    destruct q as [q|]; reflexivity.
  - destruct e as [ty mf sf mb q wl gen name p1 p2 p3 p19].
    destruct q as [q|]; reflexivity.
  - destruct e as [ty mf sf mb q wl gen name p1 p2 p3 p19].
    destruct q as [q|]; reflexivity.
Qed.

(** The OS_EVENT record itself is not written by Flush.  Only its abstract
    queue payload changes; all fields read by its concrete representation
    remain exactly equal. *)
Lemma q_flush_event_rep_unchanged : forall sg ts eid e,
  used_event_rep sg ts eid (q_flush_event e) =
  used_event_rep sg ts eid e.
Proof.
  intros. unfold used_event_rep, event_image, q_flush_event.
  destruct e as [ty mf sf mb q wl gen name p1 p2 p3 p19].
  destruct q as [q|]; reflexivity.
Qed.

(** This pure bridge does not claim a memory update.  The spatial rule below
    separately consumes the post-write QCB and the unchanged ring. *)
Lemma q_flush_state_validity : forall sg before eid e,
  UCOS2_state_inv sg before ->
  before.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_Q ->
  UCOS2_state_inv sg (q_flush_state before eid e).
Proof.
  intros sg before eid e Hvalid Hget Htype.
  unfold q_flush_state, update_event_field.
  pose proof Hvalid as [_ [_ [_ [Hevents _]]]].
  eapply UCOS2_event_payload_update_preserves_validity.
  - exact Hvalid.
  - exact Hget.
  - destruct e as [ty mf sf mb q wl gen name p1 p2 p3 p19].
    destruct q as [q|]; reflexivity.
  - destruct e as [ty mf sf mb q wl gen name p1 p2 p3 p19].
    destruct q as [q|]; reflexivity.
  - destruct e as [ty mf sf mb q wl gen name p1 p2 p3 p19].
    destruct q as [q|]; reflexivity.
  - destruct e as [ty mf sf mb q wl gen name p1 p2 p3 p19].
    destruct q as [q|]; reflexivity.
  - eapply q_flush_event_validity; eauto.
Qed.

Lemma q_flush_buffer_empty_view : forall q,
  forall slots, queue_buffer_rep q slots |-- queue_buffer_rep (queue_flush_state q) slots.
Proof.
  intros q slots. apply queue_flush_preserves_buffer.
Qed.

Lemma q_flush_readonly_after : forall sg q R,
  q_flush_readonly_refines sg q R ->
  q_flush_readonly_refines sg (queue_flush_state q) R.
Proof.
  intros sg q R Hframe. unfold q_flush_readonly_refines in *.
  sep_apply_l_atomic Hframe.
  Intros slots.
  sep_apply_l_atomic (q_flush_buffer_empty_view q slots).
  unfold queue_flush_state, queue_with_contents, queue_end_addr. cbn.
  Exists slots. cancel. entailer!.
Qed.

Lemma q_flush_stage_is_canonical : forall sg q R,
  q_flush_readonly_refines sg q R ->
  q_flush_write_stage sg q (queue_in_addr q) (queue_out_addr q) (queue_entries q) R
  |-- used_queue_control_block sg q ** EX slots, queue_buffer_rep q slots.
Proof.
  intros sg q R Hframe. unfold q_flush_write_stage.
  unfold q_flush_readonly_refines in Hframe.
  sep_apply_l_atomic Hframe. Intros slots.
  unfold used_queue_control_block. entailer!.
  Exists slots. cancel. entailer!.
Qed.

Lemma q_flush_updated_stage_is_canonical : forall sg q R,
  q_flush_readonly_refines sg q R ->
  q_flush_write_stage sg q q.(qStart) q.(qStart) 0 R |--
  used_queue_control_block sg (queue_flush_state q) **
  EX slots, queue_buffer_rep (queue_flush_state q) slots.
Proof.
  intros sg q R Hframe.
  pose proof (q_flush_readonly_after sg q R Hframe) as Hafter.
  pose proof (q_flush_stage_is_canonical sg (queue_flush_state q) R Hafter) as Hcanonical.
  unfold q_flush_write_stage, queue_flush_state, queue_with_contents,
       queue_in_addr, queue_out_addr, queue_entries in Hcanonical.
  cbn in Hcanonical.
  rewrite !Z.add_0_r in Hcanonical.
  exact Hcanonical.
Qed.

Lemma q_flush_queue_update_state_eq : forall s eid e q slots,
  e.(queueFields) = Some q ->
  s.(EventState).(publishedQueueBytes) q.(qID) = Some slots ->
  replace_EventS (queue_update s.(EventState) eid e (queue_flush_state q) slots) s =
  q_flush_state s eid e.
Proof.
  intros s eid e q slots Hq Hslots.
  pose proof (queue_update_preserves_published_bytes s.(EventState) eid e
    (queue_flush_state q) slots Hslots) as Hbytes.
  unfold q_flush_state, update_event_field, q_flush_event; rewrite Hq.
  f_equal.
  unfold queue_update in *; cbn zeta in *.
  cbn [publishedQueueBytes] in Hbytes; rewrite Hbytes.
  destruct (EventState s); reflexivity.
Qed.

Lemma q_flush_queue_split : forall sg s eid e q,
  s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_Q -> e.(queueFields) = Some q ->
  UCOS2_inv sg s |-- EX free, EX slots,
    q_flush_owned_stage sg s eid e q free slots
      (queue_in_addr q) (queue_out_addr q) (queue_entries q)
      (q_flush_readonly_storage sg q slots).
Proof.
  intros sg s eid e q Hget Htype Hq.
  rewrite UCOS2_inv_split_event_queue; Intros.
  sep_apply_l_atomic (queue_storage_split_event sg s.(EventState) eid e q Hget Hq).
  Intros free slots; Exists free slots.
  unfold q_flush_owned_stage, q_flush_stage_facts, q_flush_write_stage,
    q_flush_readonly_storage, q_flush_queue_rest, used_queue_control_block.
  entailer!.
  apply _derivable1_andp_intros; reflexivity.
Qed.

Lemma q_flush_owned_stage_merge_original : forall sg s eid e q free slots R,
  q_flush_owned_stage sg s eid e q free slots
    (queue_in_addr q) (queue_out_addr q) (queue_entries q) R |-- UCOS2_inv sg s.
Proof.
  intros sg s eid e q free slots R.
  unfold q_flush_owned_stage, q_flush_stage_facts; Intros.
  destruct H as [Hvalid [Hget [Htype [Hq [Hbinding [Hpart Hbytes]]]]]].
  assert (Hnode : q_flush_write_stage sg q (queue_in_addr q) (queue_out_addr q)
      (queue_entries q) (R && q_flush_readonly_storage sg q slots) |--
    published_queue_node_rep sg s.(EventState) eid e).
  { unfold q_flush_write_stage, q_flush_readonly_storage, published_queue_node_rep.
    rewrite Hq; Exists slots; unfold used_queue_control_block; entailer!;
      apply derivable1_andp_elim2. }
  sep_apply_l_atomic Hnode; unfold q_flush_queue_rest; sepcon_right_assoc.
  sep_apply_l_atomic (store_map_merge (published_queue_node_rep sg s.(EventState))
    eid e s.(EventState).(inUsedEventStates) Hget).
  rewrite UCOS2_inv_split_event_queue; unfold queue_storage_rep; entailer!.
  Exists free; entailer!.
Qed.

Lemma q_flush_world_implies_global : forall sg pevent eid entry current R,
  q_flush_world sg pevent eid entry current R |-- UCOS2_inv sg current.
Proof.
  intros; unfold q_flush_world, q_flush_queue_storage; Intros.
  destruct (Z.eqb pevent 0); [entailer!|].
  destruct (current.(EventState).(inUsedEventStates) eid) as [e|]; [|entailer!].
  destruct e.(eventType); try entailer!.
  destruct e.(queueFields) as [q|]; [|entailer!].
  Intros free slots; apply q_flush_owned_stage_merge_original.
Qed.

Lemma q_flush_readonly_storage_refines : forall sg q slots,
  q_flush_readonly_refines sg q (q_flush_readonly_storage sg q slots).
Proof.
  intros; unfold q_flush_readonly_refines, q_flush_readonly_storage.
  Exists slots; entailer!.
Qed.

Lemma q_flush_world_from_global : forall sg pevent eid s,
  q_flush_profile sg -> q_flush_input_domain sg pevent eid ->
  UCOS2_inv sg s |-- EX R, q_flush_world sg pevent eid s s R.
Proof.
  intros sg pevent eid s Hprofile Hdomain.
  unfold q_flush_world, q_flush_queue_storage, q_flush_snapshot.
  destruct (Z.eqb pevent 0); [Exists emp; entailer!|].
  destruct (s.(EventState).(inUsedEventStates) eid) as [e|] eqn:Hget;
    [|Exists emp; entailer!].
  destruct e.(eventType) eqn:Htype; try solve [Exists emp; entailer!].
  destruct e.(queueFields) as [q|] eqn:Hq; [|Exists emp; entailer!].
  sep_apply_l_atomic (q_flush_queue_split sg s eid e q Hget Htype Hq).
  Intros free slots.
  pose proof (q_flush_readonly_storage_refines sg q slots) as Hrefines.
  Exists (q_flush_readonly_storage sg q slots); entailer!.
  Exists free slots; entailer!.
Qed.

Lemma q_flush_written_node_merge_global : forall sg s eid e q free slots,
  q_flush_stage_facts sg s eid e q free slots ->
  qcb_storage_rep sg q.(qID) (qcb_flush (qcb_fields_image q) q.(qStart)) **
    queue_buffer_rep q slots ** q_flush_queue_rest sg s eid free |--
  UCOS2_inv sg (q_flush_state s eid e).
Proof.
  intros sg s eid e q free slots [Hvalid [Hget [Htype [Hq [Hbinding [Hpart Hbytes]]]]]].
  rewrite <- (q_flush_queue_update_state_eq s eid e q slots Hq Hbytes).
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  pose proof (Hpayload eid e Hget) as Hqueue.
  unfold event_payload_consistency in Hqueue; rewrite Htype, Hq in Hqueue.
  pose proof (queue_flush_preserves_consistency_total sg e.(waitList) q Hqueue) as Hafter.
  sep_apply_l_atomic (queue_flush_reconstructs_node sg q slots).
  unfold queue_buffer_rep; Intros.
  unfold q_flush_queue_rest; sepcon_right_assoc.
  sep_apply_r_atomic (UCOS2_inv_merge_queue_update sg s free eid e q
    (queue_flush_state q) slots Hvalid Hbinding Hpart Hget Htype Hq eq_refl Hafter H).
  entailer!.
Qed.

Lemma q_flush_owned_stage_merge_updated : forall sg s eid e q free slots R,
  q_flush_owned_stage sg s eid e q free slots q.(qStart) q.(qStart) 0 R |--
  UCOS2_inv sg (q_flush_state s eid e).
Proof.
  intros sg s eid e q free slots R; unfold q_flush_owned_stage; Intros.
  assert (Hnode : q_flush_write_stage sg q q.(qStart) q.(qStart) 0
      (R && q_flush_readonly_storage sg q slots) |--
    qcb_storage_rep sg q.(qID) (qcb_flush (qcb_fields_image q) q.(qStart)) **
      queue_buffer_rep q slots).
  { rewrite qcb_flush_fields_eq.
    rewrite <- (used_queue_control_block_fields_equiv sg (queue_flush_state q)).
    unfold q_flush_write_stage, q_flush_readonly_storage, used_queue_control_block,
      queue_flush_state, queue_with_contents, queue_in_addr, queue_out_addr,
      queue_end_addr, queue_entries; cbn; rewrite !Z.add_0_r; entailer!;
      apply derivable1_andp_elim2. }
  sep_apply_l_atomic Hnode.
  sep_apply_r_atomic (q_flush_written_node_merge_global sg s eid e q free slots H).
  entailer!.
Qed.

Lemma q_flush_stage_facts_after : forall sg s eid e q free slots,
  q_flush_stage_facts sg s eid e q free slots ->
  q_flush_stage_facts sg (q_flush_state s eid e) eid (q_flush_event e)
    (queue_flush_state q) free slots.
Proof.
  intros sg s eid e q free slots [Hvalid [Hget [Htype [Hq [Hbinding [Hpart Hbytes]]]]]].
  destruct (proj1 Hbinding eid e q Hget Hq) as [_ [bytes [Hbytes' Hmodel]]].
  assert (bytes = slots) by congruence; subst bytes.
  pose proof (queue_flush_preserves_slots q slots Hmodel) as Hmodel'.
  unfold q_flush_stage_facts.
  split; [eapply q_flush_state_validity; eauto|].
  split.
  - unfold q_flush_state, update_event_field, update_event_field_raw, replace_EventS;
      cbn; rewrite Z.eqb_refl; reflexivity.
  - split; [unfold q_flush_event; rewrite Hq; exact Htype|].
    split; [unfold q_flush_event; rewrite Hq; reflexivity|].
    rewrite <- (q_flush_queue_update_state_eq s eid e q slots Hq Hbytes).
    split.
    + eapply queue_update_preserves_storage_binding; eauto; reflexivity.
    + split; [eapply queue_update_preserves_partition; eauto; reflexivity|].
      cbn [replace_EventS EventState queue_update publishedQueueBytes].
      apply kernel_map_set_same.
Qed.

Lemma q_flush_queue_rest_after : forall sg s eid e q free slots,
  q_flush_stage_facts sg s eid e q free slots ->
  q_flush_queue_rest sg s eid free |--
  q_flush_queue_rest sg (q_flush_state s eid e) eid free.
Proof.
  intros sg s eid e q free slots [Hvalid [Hget [Htype [Hq [Hbinding [Hpart Hbytes]]]]]].
  rewrite <- (q_flush_queue_update_state_eq s eid e q slots Hq Hbytes).
  unfold q_flush_queue_rest; cbn [replace_EventS EventState TskState].
  sepcon_right_assoc.
  sep_apply_l_atomic (queue_update_preserves_event_raw_rep sg s.(TskState)
    s.(EventState) eid e q (queue_flush_state q) slots Hget Htype Hq eq_refl).
  sep_apply_l_atomic (proj1 (queue_update_missing_nodes_equiv sg s.(EventState)
    eid e q (queue_flush_state q) slots Hbinding Hget Hq eq_refl)).
  entailer!.
Qed.

Lemma q_flush_readonly_storage_after : forall sg q slots R,
  R && q_flush_readonly_storage sg q slots |--
  R && q_flush_readonly_storage sg (queue_flush_state q) slots.
Proof.
  intros; apply _derivable1_andp_intros; [apply derivable1_andp_elim1|].
  sep_apply_l_atomic (derivable1_andp_elim2 R (q_flush_readonly_storage sg q slots)).
  unfold q_flush_readonly_storage.
  sep_apply_l_atomic (queue_flush_preserves_buffer q slots).
  unfold queue_flush_state, queue_with_contents, queue_end_addr; cbn; entailer!.
Qed.

Lemma q_flush_owned_stage_reindex : forall sg s eid e q free slots R,
  q_flush_owned_stage sg s eid e q free slots q.(qStart) q.(qStart) 0 R |--
  q_flush_owned_stage sg (q_flush_state s eid e) eid (q_flush_event e)
    (queue_flush_state q) free slots q.(qStart) q.(qStart) 0 R.
Proof.
  intros; unfold q_flush_owned_stage; Intros.
  pose proof (q_flush_stage_facts_after sg s eid e q free slots H) as Hafter.
  sep_apply_l_atomic (q_flush_queue_rest_after sg s eid e q free slots H).
  unfold q_flush_write_stage.
  sep_apply_l_atomic (q_flush_readonly_storage_after sg q slots R).
  cbn [queue_flush_state queue_with_contents qID qStart]; entailer!.
Qed.

Lemma q_flush_owned_stage_merge_world : forall sg pevent eid entry s e q free slots R,
  pevent <> 0 ->
  q_flush_profile sg -> q_flush_input_domain sg pevent eid ->
  q_flush_snapshot sg pevent eid entry R ->
  q_flush_owned_stage sg s eid e q free slots q.(qStart) q.(qStart) 0 R |--
  q_flush_world sg pevent eid entry (q_flush_state s eid e) R.
Proof.
  intros sg pevent eid entry s e q free slots R Hnonnull Hprofile Hdomain Hsnapshot.
  assert (Hnon : Z.eqb pevent 0 = false) by (apply Z.eqb_neq; exact Hnonnull).
  sep_apply_l_atomic (q_flush_owned_stage_reindex sg s eid e q free slots R).
  unfold q_flush_owned_stage; Intros.
  pose proof H as Hfacts.
  destruct Hfacts as [Hvalid [Hget [Htype [Hq [Hbinding [Hpart Hbytes]]]]]].
  unfold q_flush_world, q_flush_queue_storage; rewrite Hnon, Hget, Htype, Hq.
  Exists free slots; unfold q_flush_owned_stage.
  unfold queue_in_addr, queue_out_addr, queue_entries;
    cbn [queue_flush_state queue_with_contents qStart qInIndex qOutIndex qMessages];
    rewrite !Z.add_0_r; entailer!.
Qed.

(** Exact arrow-field view consumed by the three original C stores.  Start
    remains a read-only cell; no intermediate queue invariant is asserted. *)
Definition q_flush_source_fields (sg : StableGlobVars) (q : QueueFields)
  (qin qout count : Z) : Assertion :=
  (&(((qcb_addr sg q.(qID))) # "os_q" ->ₛ "OSQStart")) # Ptr |-> q.(qStart) **
  (&(((qcb_addr sg q.(qID))) # "os_q" ->ₛ "OSQIn")) # Ptr |-> qin **
  (&(((qcb_addr sg q.(qID))) # "os_q" ->ₛ "OSQOut")) # Ptr |-> qout **
  (&(((qcb_addr sg q.(qID))) # "os_q" ->ₛ "OSQEntries")) # UShort |-> count.

Definition q_flush_source_frame (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState) (q : QueueFields)
  (free : list QueueID) (slots : list (option addr)) (R : QFlushMemory) : Assertion :=
  coq_prop (q_flush_stage_facts sg s eid e q free slots) &&
  ((R && q_flush_readonly_storage sg q slots) ** q_flush_queue_rest sg s eid free).

Lemma q_flush_stage_queue_valid : forall sg s eid e q free slots,
  q_flush_stage_facts sg s eid e q free slots -> valid_queue_id sg q.(qID).
Proof.
  intros sg s eid e q free slots [Hvalid [Hget [Htype [Hq Hrest]]]].
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  pose proof (Hpayload eid e Hget) as Hqueue.
  unfold event_payload_consistency in Hqueue; rewrite Htype, Hq in Hqueue.
  exact (proj1 Hqueue).
Qed.

Lemma q_flush_write_stage_source_equiv : forall sg q qin qout count R,
  q_flush_profile sg -> valid_queue_id sg q.(qID) ->
  q_flush_write_stage sg q qin qout count R --||--
  q_flush_source_fields sg q qin qout count ** R.
Proof.
  intros sg q qin qout count R [_ [_ [Hlayout [_ Hsize]]]] Hqid.
  specialize (Hlayout q.(qID) Hqid).
  change (sizeof ("os_q") = sizeof_OS_Q) in Hsize.
  rewrite Hsize in Hlayout; fold (qcb_addr sg q.(qID)) in Hlayout.
  destruct Hlayout as [_ [Hstart [_ [Hin [Hout [_ Hentries]]]]]].
  unfold q_flush_write_stage, q_flush_source_fields.
  rewrite Hstart, Hin, Hout, Hentries; split; entailer!.
Qed.

Lemma q_flush_owned_stage_source_equiv : forall sg s eid e q free slots qin qout count R,
  q_flush_profile sg ->
  q_flush_owned_stage sg s eid e q free slots qin qout count R --||--
  q_flush_source_fields sg q qin qout count **
    q_flush_source_frame sg s eid e q free slots R.
Proof.
  intros; unfold q_flush_owned_stage, q_flush_source_frame; split; Intros.
  - rewrite (q_flush_write_stage_source_equiv sg q qin qout count
      (R && q_flush_readonly_storage sg q slots) H
      (q_flush_stage_queue_valid sg s eid e q free slots H0)); entailer!.
  - rewrite (q_flush_write_stage_source_equiv sg q qin qout count
      (R && q_flush_readonly_storage sg q slots) H
      (q_flush_stage_queue_valid sg s eid e q free slots H0)); entailer!.
Qed.

Lemma q_flush_source_fields_merge_global : forall sg s eid e q free slots R,
  q_flush_profile sg ->
  q_flush_source_fields sg q q.(qStart) q.(qStart) 0 **
    q_flush_source_frame sg s eid e q free slots R |--
  UCOS2_inv sg (q_flush_state s eid e).
Proof.
  intros; rewrite <- (q_flush_owned_stage_source_equiv sg s eid e q free slots
    q.(qStart) q.(qStart) 0 R H).
  apply q_flush_owned_stage_merge_updated.
Qed.

Lemma q_flush_sem_total : forall sg pevent eid before,
  event_in_range sg before.(TskState) before.(EventState) ->
  exists ret after, OSQFlush_sem pevent eid before ret after.
Proof.
  intros sg pevent eid before Hvalid. unfold OSQFlush_sem.
  destruct (Z.eqb pevent 0).
  - exists 4, before. split; reflexivity.
  - destruct (inUsedEventStates (EventState before) eid) as [e|] eqn:Hget.
    + assert (Hfields : event_fields_consistency e).
      { destruct Hvalid as [_ [_ [_ [Hfields _]]]].
        eapply Hfields; exact Hget. }
      destruct (eventType e) eqn:Htype; try (exists 1, before; split; reflexivity).
      exists 0, (q_flush_state before eid e).
      split.
      * unfold event_fields_consistency in Hfields. rewrite Htype in Hfields. tauto.
      * split; reflexivity.
    + exists 1, before. split; reflexivity.
Qed.

Lemma q_flush_safe_endpoint : forall pevent eid entry ret after X,
  OSQFlush_sem pevent eid entry ret after ->
  q_flush_safe_pre pevent eid entry X -> q_flush_safe_post after ret X.
Proof.
  intros pevent eid entry ret after X Hsem Hsafe.
  unfold q_flush_safe_pre in Hsafe. unfold q_flush_safe_post.
  eapply (highstependret_derive
    (atomic_cmd (OSQFlush_sem pevent eid)) (LastSeen entry) ret
    (fun _ => LastSeen after)); [|exact Hsafe].
  unfold hs_eval, atomic_cmd, LastSeen.
  intros B HB. exists (RTrans_Abs after). split.
  - exists entry, after. split.
    + apply HB. exact I.
    + split; [exact Hsem|]. intro s. split; trivial.
  - intro s. split; trivial.
Qed.

Lemma event_slot_type_unsigned32__return_and_pure : forall st eid,
  unsigned_last_nbits (event_slot_type_value st eid) 32 =
  event_slot_type_value st eid.
Proof.
  intros st eid. unfold event_slot_type_value.
  destruct (inUsedEventStates st eid) as [e |];
    [destruct (eventType e) |]; reflexivity.
Qed.
