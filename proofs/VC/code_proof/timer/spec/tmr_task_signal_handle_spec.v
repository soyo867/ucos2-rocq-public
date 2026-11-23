Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_next_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_api_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_delete_spec.
Require Import Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.sem.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.

(** The existing live-handle protocol is an explicit C environment
    obligation, not new memory ownership or an all-Task wait predicate.
    This file derives its actual creation endpoint and several real
    lifecycle preservation cases.  It does not assert that an arbitrary
    callback or all registered actions have these cases.  The selected
    callback capability may return any current public slot, including
    FREE/wrong-type; only a later SEM/clear-counter Save uses the protocol. *)

Lemma tmr_task_signal_create_published_slot :
  forall critical sg invocation count before signal after,
  sem_create_api_program critical sg invocation count before signal after ->
  signal <> 0 ->
  exists eid node,
    signal = event_addr sg eid /\ mutex_query_lookup after eid node /\
    node.(eventType) = OS_EVENT_TYPE_SEM.
Proof.
  intros critical sg invocation count before signal after Hcreate Hnonnull.
  unfold sem_create_api_program in Hcreate.
  match type of Hcreate with
  | context [if ?test then _ else _] => destruct test eqn:Hnesting in Hcreate
  end.
  - destruct Hcreate as [Hzero _]; contradiction.
  - destruct Hcreate as [entry [allocated [detached [Hsave [Hallocate Hreturn]]]]].
    destruct allocated as [[eid image]|].
    + destruct Hreturn as [resumed [initialized [allocation
        [Hrestore [Hstores [Hprivate [Hsignal ->]]]]]]].
      exists eid, (sem_create_event allocation count 0).
      split; [exact Hsignal|]. split; [|reflexivity].
      unfold mutex_query_lookup; cbn [replace_EventS EventState event_publish inUsedEventStates].
      apply kernel_map_set_same.
    + destruct Hreturn as [Hzero _]; contradiction.
Qed.

Lemma tmr_task_signal_recorded_value : forall timers signal recorded,
  timer_record_signal_result timers signal = Some recorded -> recorded.(timerSignalSem) = signal.
Proof.
  intros timers signal recorded Hrecord; unfold timer_record_signal_result in Hrecord.
  destruct timers.(timerInitPhase) eqn:Hphase in Hrecord; try discriminate.
  inversion Hrecord; reflexivity.
Qed.

(** Consume the actual successful Create program and actual signal store.
    The new invocation's lifetime protocol remains separately supplied by
    its registered C ownership discipline.  Create establishes the public
    ECB; it cannot establish a property of arbitrary future client actions. *)
Lemma tmr_task_signal_create_store_call_input :
  forall critical sg create_invocation task_invocation count before signal current timers,
  sem_create_api_program critical sg create_invocation count before signal current ->
  UCOS2_state_inv sg current -> signal <> 0 ->
  timer_record_signal_result current.(TimerState) signal = Some timers ->
  (forall eid, signal = event_addr sg eid ->
    mutex_query_handle_protocol critical sg task_invocation eid) ->
  exists eid node,
    sem_pend_call_input critical sg task_invocation timers.(timerSignalSem)
      (replace_TimerS timers current) eid node.
Proof.
  intros critical sg create_invocation task_invocation count before signal current timers
    Hcreate Hvalid Hnonnull Hrecord Hprotocol.
  destruct (tmr_task_signal_create_published_slot critical sg create_invocation count
    before signal current Hcreate Hnonnull) as [eid [node [Haddress [Hlookup Hsem]]]].
  exists eid, node.
  rewrite (tmr_task_signal_recorded_value _ _ _ Hrecord).
  change (sem_pend_call_input critical sg task_invocation signal current eid node).
  apply tmr_task_pend_input_public_used; try assumption.
  intros; apply Hprotocol; exact Haddress.
Qed.

(** An unsuccessful Create result is stored literally.  The unused pure
    slot witnesses carry no ECB bytes and have no validity requirement. *)
Lemma tmr_task_signal_null_store_call_input :
  forall critical sg invocation current timers eid observed,
  timer_record_signal_result current.(TimerState) 0 = Some timers ->
  sem_pend_call_input critical sg invocation timers.(timerSignalSem)
    (replace_TimerS timers current) eid observed.
Proof.
  intros critical sg invocation current timers eid observed Hrecord.
  rewrite (tmr_task_signal_recorded_value _ _ _ Hrecord).
  apply tmr_task_pend_input_null.
Qed.

(** A numerical handle bound alone does not establish public ownership:
    a valid slot may be private during EventCreate.  With the real current
    private-map exclusion, the pool partition gives exactly used OR FREE.
    [fallback] is an unused pure witness in the FREE alternative. *)
Lemma tmr_task_signal_slot_public_from_pool : forall sg state eid (fallback : OSEventAbstractState),
  UCOS2_state_inv sg state -> valid_event_id sg eid ->
  state.(EventState).(eventLifecycle).(eventPrivate) eid = None ->
  exists observed, sem_query_public_slot state eid observed.
Proof.
  intros sg state eid fallback Hvalid Hid Hprivate.
  destruct (state.(EventState).(inUsedEventStates) eid) as [node|] eqn:Hused.
  - exists node; left; exact Hused.
  - exists fallback; right; split; [exact Hused|].
    pose proof Hvalid as [_ [_ [_ [[Hpool _] _]]]].
    destruct Hpool as [[Hnodup [Hrange Hpartition]] Hdisjoint].
    destruct (in_dec Z.eq_dec eid state.(EventState).(unUsedEventStates)) as [Hfree|Hnot];
      [exact Hfree|].
    destruct (proj2 (Hpartition eid) (conj Hid Hnot)) as [allocated Hallocated].
    unfold event_allocated_slots in Hallocated; rewrite Hprivate, Hused in Hallocated; discriminate.
Qed.

(** The registered allocation and private-store actions leave the used
    map untouched.  Publication cannot overwrite a live handle: its own
    private-allocation precondition and the pool partition prove distinct
    slots.  No signal-specific ghost address or token is introduced. *)
Lemma tmr_task_signal_allocate_client_preserves_lookup :
  forall task_actor allocation_invocation sg before after eid node,
  kernel_client_step (event_create_allocate_client task_actor allocation_invocation) sg before after ->
  mutex_query_lookup before eid node -> mutex_query_lookup after eid node.
Proof.
  intros task_actor allocation_invocation sg before after eid node [_ [result Hstep]] Hlookup.
  unfold event_create_allocate_critical in Hstep.
  destruct before.(EventState).(unUsedEventStates) as [|selected rest] in Hstep.
  - destruct Hstep as [_ ->]; exact Hlookup.
  - destruct Hstep as [image [_ [_ ->]]]; exact Hlookup.
Qed.

Lemma tmr_task_signal_private_store_client_preserves_lookup :
  forall task_actor selected allocation field value sg before after eid node,
  kernel_client_step
    (event_create_private_store_client task_actor selected allocation field value) sg before after ->
  mutex_query_lookup before eid node -> mutex_query_lookup after eid node.
Proof.
  intros task_actor selected allocation field value sg before after eid node [_ ->] Hlookup.
  exact Hlookup.
Qed.

Lemma tmr_task_signal_publication_client_preserves_lookup :
  forall task_actor selected allocation published sg before after eid node,
  UCOS2_state_inv sg before ->
  kernel_client_step (event_create_publication_client task_actor selected allocation published)
    sg before after ->
  mutex_query_lookup before eid node -> mutex_query_lookup after eid node.
Proof.
  intros task_actor selected allocation published sg before after eid node Hvalid
    [Hprivate [Hname ->]] Hlookup.
  pose proof Hvalid as [_ [_ [_ [[Hpool _] _]]]].
  pose proof (proj2 (proj2 (event_pool_used_not_free sg before.(EventState) eid node Hpool Hlookup)))
    as Hnotprivate.
  assert (Hdifferent : eid <> selected) by (intro Hsame; subst selected; congruence).
  unfold mutex_query_lookup; cbn [replace_EventS EventState event_publish inUsedEventStates].
  rewrite kernel_map_set_other by exact Hdifferent; exact Hlookup.
Qed.

(** Payload/wait-list updates use the existing canonical Event updater.
    Only their actual unchanged type/generation fields are needed; other
    data, waiters, tasks and scheduler state may change. *)
Lemma tmr_task_signal_event_update_preserves_identity :
  forall events selected old updated eid previous,
  events.(inUsedEventStates) selected = Some old ->
  updated.(eventGeneration) = old.(eventGeneration) ->
  updated.(eventType) = old.(eventType) ->
  events.(inUsedEventStates) eid = Some previous ->
  exists current,
    (update_event_field_raw events selected updated).(inUsedEventStates) eid = Some current /\
    current.(eventGeneration) = previous.(eventGeneration) /\
    current.(eventType) = previous.(eventType).
Proof.
  intros events selected old updated eid previous Hselected Hgeneration Htype Hprevious.
  unfold update_event_field_raw; cbn [inUsedEventStates].
  match goal with
  | |- context [if ?test then _ else _] => destruct test eqn:Hequal
  end.
  - apply Z.eqb_eq in Hequal; subst eid.
    assert (previous = old) by congruence; subst previous.
    exists updated; split; [reflexivity|]. split; assumption.
  - exists previous; split; [exact Hprevious|]. split; reflexivity.
Qed.

Lemma tmr_task_signal_count_update_preserves_identity :
  forall state selected event count eid previous,
  mutex_query_lookup state selected event -> mutex_query_lookup state eid previous ->
  exists current,
    mutex_query_lookup (sem_count_update_state state selected event count) eid current /\
    current.(eventGeneration) = previous.(eventGeneration) /\
    current.(eventType) = previous.(eventType).
Proof.
  intros state selected event count eid previous Hselected Hprevious.
  unfold mutex_query_lookup, sem_count_update_state; cbn [replace_EventS EventState].
  eapply tmr_task_signal_event_update_preserves_identity;
    [exact Hselected|reflexivity|reflexivity|exact Hprevious].
Qed.

Lemma tmr_task_signal_wait_list_update_preserves_identity :
  forall events selected old waiters eid previous,
  events.(inUsedEventStates) selected = Some old ->
  events.(inUsedEventStates) eid = Some previous ->
  exists current,
    (update_event_field_raw events selected (event_set_wait_list old waiters)).(inUsedEventStates) eid =
      Some current /\
    current.(eventGeneration) = previous.(eventGeneration) /\
    current.(eventType) = previous.(eventType).
Proof.
  intros events selected old waiters eid previous Hselected Hprevious.
  eapply tmr_task_signal_event_update_preserves_identity;
    [exact Hselected|reflexivity|reflexivity|exact Hprevious].
Qed.

Lemma tmr_task_signal_recycle_other_preserves_lookup :
  forall sg state selected image eid previous,
  eid <> selected -> mutex_query_lookup state eid previous ->
  mutex_query_lookup (replace_EventS (event_recycle sg state.(EventState) selected image) state)
    eid previous.
Proof.
  intros sg state selected image eid previous Hneq Hprevious.
  unfold mutex_query_lookup; cbn [replace_EventS EventState event_recycle inUsedEventStates].
  rewrite kernel_map_set_other by exact Hneq; exact Hprevious.
Qed.

(** Deleting this signal has a real FREE endpoint; it must not be hidden
    by a successful-wait precondition.  A later reallocation can make the
    same slot private, which is exactly why public-slot availability is
    separate from numerical address validity. *)
Lemma tmr_task_signal_recycle_current_free : forall sg state eid event observed,
  sem_query_public_slot (event_delete_recycle_state sg state eid event) eid observed /\
  event_slot_type_value (event_delete_recycle_state sg state eid event).(EventState) eid = 0.
Proof.
  intros sg state eid event observed.
  pose proof (event_delete_recycle_removes_event sg state eid event) as Hnone.
  split.
  - right; split; [exact Hnone|]. left; reflexivity.
  - unfold event_slot_type_value; rewrite Hnone; reflexivity.
Qed.

Lemma tmr_task_signal_registered_retirement_refutes_handle_protocol :
  forall critical sg invocation action before after eid previous,
  critical.(critical_region_clients) action -> kernel_client_actor action <> Some invocation ->
  UCOS2_state_inv sg before -> kernel_client_step action sg before after ->
  mutex_query_lookup before eid previous -> after.(EventState).(inUsedEventStates) eid = None ->
  ~ mutex_query_handle_protocol critical sg invocation eid.
Proof.
  intros critical sg invocation action before after eid previous Hregistered Hforeign
    Hvalid Hstep Hprevious Hretired Hprotocol.
  destruct (Hprotocol action before after previous Hregistered Hforeign Hvalid Hstep Hprevious)
    as [current [Hcurrent Hidentity]].
  unfold mutex_query_lookup in Hcurrent; rewrite Hretired in Hcurrent; discriminate.
Qed.
