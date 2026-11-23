Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.ucos2_verify_inv.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.

(** OSQAccept, V2.93.01 os_q.c:70--115.  Prefix order: safety hook,
    conditional NULL argument check, unconditional type read, Save.
    There is no ISR/lock rejection, trace call or OS_Sched call.
    If the null-perr safety hook returns, this API returns NULL without
    writing perr.  Unmasked prefix observations need not share a snapshot. *)
Definition q_accept_safety_exception_requested (sg : StableGlobVars) (perr : addr) : bool :=
  (sg.(osKernelConfig).(cfgSafetyCritical) && Z.eqb perr 0)%bool.

Definition q_accept_argument_error (sg : StableGlobVars) (pevent : addr) : option OSErrCode :=
  if (sg.(osKernelConfig).(cfgArgumentChecks) && Z.eqb pevent 0)%bool
  then Some OS_ERR_PEVENT_NULL else None.

Definition q_accept_type_error (type_byte : Z) : option OSErrCode :=
  if Z.eqb type_byte (encode_event_type OS_EVENT_TYPE_Q)
  then None else Some OS_ERR_EVENT_TYPE.

(** Critical kernel endpoint and (message, perr) observation.  The perr
    store is BEFORE Restore on both arms, unlike PendAbort/Delete.
    An occupied slot may contain NULL: only perr distinguishes this from
    an empty queue.  No old slot byte is cleared.  Output-cell ownership
    is separate from the shared kernel resources. *)
Definition q_accept_critical (sg : StableGlobVars) (eid : EventID)
  : program UCOS2_Verify_State (addr * OSErrCode) :=
  fun s result after => exists e q,
    s.(EventState).(inUsedEventStates) eid = Some e /\ e.(queueFields) = Some q /\
    if Z.ltb 0 (queue_entries q) then
      exists message next slots,
        queue_dequeue_front q = Some (message, next) /\
        s.(EventState).(publishedQueueBytes) q.(qID) = Some slots /\
        result = (message, OS_ERR_NONE) /\
        after = replace_EventS (queue_update s.(EventState) eid e next slots) s
    else result = (0, OS_ERR_Q_EMPTY) /\ after = s.

Lemma q_accept_critical_exists : forall sg s eid e q,
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(queueFields) = Some q ->
  queue_published_storage_binding s.(EventState) ->
  exists result after, q_accept_critical sg eid s result after.
Proof.
  intros sg s eid e q He Hq Hbinding.
  destruct (Z.ltb 0 (queue_entries q)) eqn:Hcount.
  - destruct (proj1 Hbinding eid e q He Hq) as [_ [slots [Hslots Hmodel]]].
    assert (Hpop : exists message next, queue_dequeue_front q = Some (message, next)).
    { unfold queue_dequeue_front; destruct q.(qMessages) as [|message rest] eqn:Hmessages; [|eauto].
      unfold queue_entries in Hcount; rewrite Hmessages, Zlength_nil in Hcount; discriminate. }
    destruct Hpop as [message [next Hpop]].
    exists (message, OS_ERR_NONE), (replace_EventS (queue_update s.(EventState) eid e next slots) s).
    exists e, q; split; [exact He|]; split; [exact Hq|]; rewrite Hcount.
    exists message, next, slots; repeat split; assumption || reflexivity.
  - exists (0, OS_ERR_Q_EMPTY), s; exists e, q; split; [exact He|]; split; [exact Hq|].
    rewrite Hcount; split; reflexivity.
Qed.

Lemma q_accept_critical_deterministic : forall sg eid s r1 s1 r2 s2,
  q_accept_critical sg eid s r1 s1 -> q_accept_critical sg eid s r2 s2 -> r1 = r2 /\ s1 = s2.
Proof.
  intros sg eid s r1 s1 r2 s2 [e1 [q1 [He1 [Hq1 Hfirst]]]] [e2 [q2 [He2 [Hq2 Hsecond]]]].
  assert (e2 = e1) by congruence; subst e2.
  assert (q2 = q1) by congruence; subst q2.
  destruct (Z.ltb 0 (queue_entries q1)).
  - destruct Hfirst as [m1 [next1 [slots1 [Hnext1 [Hslots1 [-> ->]]]]]].
    destruct Hsecond as [m2 [next2 [slots2 [Hnext2 [Hslots2 [-> ->]]]]]].
    assert (m2 = m1 /\ next2 = next1) as [-> ->] by (split; congruence).
    assert (slots2 = slots1) by congruence; subst slots2; split; reflexivity.
  - destruct Hfirst as [-> ->]; destruct Hsecond as [-> ->]; split; reflexivity.
Qed.

Lemma q_accept_critical_preserves_validity : forall sg s eid e result after,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(eventType) = OS_EVENT_TYPE_Q ->
  q_accept_critical sg eid s result after -> UCOS2_state_inv sg after.
Proof.
  intros sg s eid e result after Hvalid He Htype [node [q [Hnode [Hq Hstep]]]].
  assert (node = e) by congruence; subst node; destruct (Z.ltb 0 (queue_entries q)).
  - destruct Hstep as [message [next [slots [Hnext [_ [_ ->]]]]]].
    eapply UCOS2_queue_dequeue_preserves_validity; eassumption.
  - destruct Hstep as [_ ->]; exact Hvalid.
Qed.

Lemma q_accept_critical_preserves_invocation : forall sg s eid result after invocation origin,
  q_accept_critical sg eid s result after ->
  task_invocation_active s.(TskState) invocation origin ->
  task_invocation_active after.(TskState) invocation origin.
Proof.
  intros sg s eid result after invocation origin [e [q [He [Hq Hstep]]]] Hactive.
  destruct (Z.ltb 0 (queue_entries q)).
  - destruct Hstep as [message [next [slots [_ [_ [_ ->]]]]]]; exact Hactive.
  - destruct Hstep as [_ ->]; exact Hactive.
Qed.

Lemma q_accept_critical_preserves_buffer : forall sg s eid result after,
  q_accept_critical sg eid s result after ->
  after.(EventState).(publishedQueueBytes) = s.(EventState).(publishedQueueBytes).
Proof.
  intros sg s eid result after [e [q [He [Hq Hstep]]]]; destruct (Z.ltb 0 (queue_entries q)).
  - destruct Hstep as [message [next [slots [Hnext [Hslots [_ ->]]]]]].
    apply queue_update_preserves_published_bytes.
    rewrite (queue_dequeue_front_queue_id_eq q message next Hnext); exact Hslots.
  - destruct Hstep as [_ ->]; reflexivity.
Qed.

Lemma q_accept_critical_empty_frame : forall sg s eid result after,
  q_accept_critical sg eid s result after -> snd result <> OS_ERR_NONE ->
  result = (0, OS_ERR_Q_EMPTY) /\ after = s.
Proof.
  intros sg s eid result after [e [q [He [Hq Hstep]]]] Herror.
  destruct (Z.ltb 0 (queue_entries q)); [|exact Hstep].
  destruct Hstep as [message [next [slots [_ [_ [-> _]]]]]]; contradiction Herror; reflexivity.
Qed.

Lemma q_accept_success_reads_head_slot : forall sg s eid e q message after,
  UCOS2_state_inv sg s -> queue_published_storage_binding s.(EventState) ->
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(eventType) = OS_EVENT_TYPE_Q ->
  e.(queueFields) = Some q -> q_accept_critical sg eid s (message, OS_ERR_NONE) after ->
  exists slots, s.(EventState).(publishedQueueBytes) q.(qID) = Some slots /\
    Znth q.(qOutIndex) slots None = Some message.
Proof.
  intros sg s eid e q message after Hvalid Hbinding He Htype Hq [node [before [Hnode [Hbefore Hstep]]]].
  assert (node = e) by congruence; subst node.
  assert (before = q) by congruence; subst before; destruct (Z.ltb 0 (queue_entries q)).
  - destruct Hstep as [actual [next [slots [Hnext [Hslots [Hresult _]]]]]].
    injection Hresult as Hmessage; subst actual.
    pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
    pose proof (Hpayload eid e He) as Hqueue; unfold event_payload_consistency in Hqueue.
    rewrite Htype, Hq in Hqueue.
    destruct (proj1 Hbinding eid e q He Hq) as [_ [bytes [Hbytes Hmodel]]].
    assert (bytes = slots) by congruence; subst bytes.
    exists slots; split; [exact Hslots|]; eapply queue_dequeue_front_head_slot; eauto.
  - destruct Hstep as [Hresult _]; discriminate.
Qed.
