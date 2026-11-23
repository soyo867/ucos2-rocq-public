Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_delete_spec.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.

(** OSQDel, V2.93.01 os_q.c:241--348.  The safety hook, IEC runtime
    restriction, argument check, ENTER trace, type and ISR checks occur
    before Save, in this order.  A returning null-perr safety hook causes
    NULL return without a perr write; a returning IEC hook writes the
    runtime-deletion error.  These observations are not one atomic entry
    snapshot.  The selected native Event image currently has no names. *)
Definition q_delete_safety_exception_requested (sg : StableGlobVars) (perr : addr) : bool :=
  event_delete_safety_exception_requested sg perr.

Definition q_delete_runtime_exception_requested (sg : StableGlobVars) (started_byte : Z) : bool :=
  event_delete_runtime_exception_requested sg started_byte.

Definition q_delete_argument_error (sg : StableGlobVars) (pevent : addr) : option OSErrCode :=
  event_delete_argument_error sg pevent.

Definition q_delete_context_error (type_byte int_nesting : Z) : option OSErrCode :=
  event_delete_context_error (encode_event_type OS_EVENT_TYPE_Q) type_byte int_nesting.

(** Existing pool transformer: QCB link/root writes precede ECB recycling.
    The post-wake image supplies untouched ECB fields.  The buffer binding
    is removed, but the source does not deallocate caller memory. *)
Definition q_delete_recycle_state (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState) (q : QueueFields) : UCOS2_Verify_State :=
  replace_EventS (queue_recycle sg s.(EventState) eid
    (event_image sg s.(TskState) e) q.(qID)) s.

(** Result = (pointer, (perr value, call_sched)).  tasks_waiting is the
    original bitmap observation, taken before switch(opt).  ALWAYS calls
    OS_Sched only if that observation was nonzero.  Error/perr/trace and
    scheduler return are composed after Restore, not executed here. *)
Definition q_delete_critical (sg : StableGlobVars) (eid : EventID) (opt : Z)
  : program UCOS2_Verify_State (addr * (OSErrCode * bool)) :=
  fun s result after => exists e,
    s.(EventState).(inUsedEventStates) eid = Some e /\
    let waiting := negb (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0) in
    if Z.eqb opt 0 then
      if waiting then result = (event_addr sg eid, (OS_ERR_TASK_WAITING, false)) /\ after = s
      else exists q, e.(queueFields) = Some q /\
        result = (0, (OS_ERR_NONE, false)) /\ after = q_delete_recycle_state sg s eid e q
    else if Z.eqb opt 1 then
      exists priorities ready node q,
        event_broadcast sg eid PendQ 0 PendAbort s priorities ready /\
        ready.(EventState).(inUsedEventStates) eid = Some node /\ node.(queueFields) = Some q /\
        result = (0, (OS_ERR_NONE, waiting)) /\ after = q_delete_recycle_state sg ready eid node q
    else result = (event_addr sg eid, (OS_ERR_INVALID_OPT, false)) /\ after = s.

Lemma q_delete_critical_exists : forall sg s eid e opt,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(eventType) = OS_EVENT_TYPE_Q ->
  exists result after, q_delete_critical sg eid opt s result after.
Proof.
  intros sg s eid e opt Hvalid He Htype.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  pose proof (Hpayload eid e He) as Hqueue; unfold event_payload_consistency in Hqueue.
  rewrite Htype in Hqueue; destruct e.(queueFields) as [q|] eqn:Hq; [|contradiction].
  set (waiting := negb (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0)).
  destruct (Z.eqb opt 0) eqn:Hnone.
  - destruct waiting eqn:Hwaiting.
    + exists (event_addr sg eid, (OS_ERR_TASK_WAITING, false)), s.
      exists e; split; [exact He|]; rewrite Hnone; fold waiting; rewrite Hwaiting; split; reflexivity.
    + exists (0, (OS_ERR_NONE, false)), (q_delete_recycle_state sg s eid e q).
      exists e; split; [exact He|]; rewrite Hnone; fold waiting; rewrite Hwaiting.
      exists q; repeat split; assumption || reflexivity.
  - destruct (Z.eqb opt 1) eqn:Halways.
    + destruct (event_broadcast_exists e.(waitList) sg s eid e PendQ 0 PendAbort
        Hvalid He ltac:(rewrite Htype; reflexivity) eq_refl)
        as [priorities [ready [Hloop [_ [Hnode _]]]]].
      exists (0, (OS_ERR_NONE, waiting)),
        (q_delete_recycle_state sg ready eid (event_set_wait_list e []) q).
      exists e; split; [exact He|]; rewrite Hnone, Halways; fold waiting.
      exists priorities, ready, (event_set_wait_list e []), q;
        repeat split; assumption || reflexivity.
    + exists (event_addr sg eid, (OS_ERR_INVALID_OPT, false)), s.
      exists e; split; [exact He|]; rewrite Hnone, Halways; split; reflexivity.
Qed.

Lemma q_delete_critical_deterministic : forall sg eid opt s r1 s1 r2 s2,
  q_delete_critical sg eid opt s r1 s1 -> q_delete_critical sg eid opt s r2 s2 ->
  r1 = r2 /\ s1 = s2.
Proof.
  intros sg eid opt s r1 s1 r2 s2 [e [He Hfirst]] [other [Hother Hsecond]].
  assert (other = e) by congruence; subst other.
  destruct (Z.eqb opt 0).
  - destruct (negb (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0)).
    + destruct Hfirst as [-> ->]; destruct Hsecond as [-> ->]; split; reflexivity.
    + destruct Hfirst as [q1 [Hq1 [-> ->]]]; destruct Hsecond as [q2 [Hq2 [-> ->]]].
      assert (q1 = q2) by congruence; subst q2; split; reflexivity.
  - destruct (Z.eqb opt 1).
    + destruct Hfirst as [ps1 [ready1 [node1 [q1 [Hloop1 [Hnode1 [Hq1 [-> ->]]]]]]]].
      destruct Hsecond as [ps2 [ready2 [node2 [q2 [Hloop2 [Hnode2 [Hq2 [-> ->]]]]]]]].
      destruct (event_broadcast_deterministic sg eid PendQ 0 PendAbort s ps1 ready1 ps2 ready2
        Hloop1 Hloop2) as [-> ->].
      assert (node1 = node2) by congruence; subst node2.
      assert (q1 = q2) by congruence; subst q2; split; reflexivity.
    + destruct Hfirst as [-> ->]; destruct Hsecond as [-> ->]; split; reflexivity.
Qed.

Lemma q_delete_critical_error_frame : forall sg s eid opt result after,
  q_delete_critical sg eid opt s result after -> fst (snd result) <> OS_ERR_NONE ->
  after = s /\
    (result = (event_addr sg eid, (OS_ERR_TASK_WAITING, false)) \/
     result = (event_addr sg eid, (OS_ERR_INVALID_OPT, false))).
Proof.
  intros sg s eid opt result after [e [He Hstep]] Herror.
  destruct (Z.eqb opt 0).
  - destruct (negb (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0)).
    + destruct Hstep as [-> ->]; split; [reflexivity|left; reflexivity].
    + destruct Hstep as [q [_ [-> _]]]; contradiction Herror; reflexivity.
  - destruct (Z.eqb opt 1).
    + destruct Hstep as [ps [ready [node [q [_ [_ [_ [-> _]]]]]]]];
        contradiction Herror; reflexivity.
    + destruct Hstep as [-> ->]; split; [reflexivity|right; reflexivity].
Qed.

Lemma q_delete_recycle_removes_event : forall sg s eid e q,
  (q_delete_recycle_state sg s eid e q).(EventState).(inUsedEventStates) eid = None.
Proof.
  intros; unfold q_delete_recycle_state, queue_recycle, event_recycle; simpl.
  unfold kernel_map_set; destruct (Z.eq_dec eid eid); congruence.
Qed.

Lemma q_delete_recycle_unregisters_buffer : forall sg s eid e q,
  (q_delete_recycle_state sg s eid e q).(EventState).(publishedQueueBytes) q.(qID) = None.
Proof.
  intros; unfold q_delete_recycle_state, queue_recycle; simpl.
  unfold kernel_map_set; destruct (Z.eq_dec q.(qID) q.(qID)); congruence.
Qed.

Lemma q_delete_critical_success_removes_event : forall sg s eid opt result after,
  q_delete_critical sg eid opt s result after -> fst (snd result) = OS_ERR_NONE ->
  after.(EventState).(inUsedEventStates) eid = None.
Proof.
  intros sg s eid opt result after [e [He Hstep]] Hsuccess.
  destruct (Z.eqb opt 0).
  - destruct (negb (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0)).
    + destruct Hstep as [-> _]; discriminate Hsuccess.
    + destruct Hstep as [q [_ [_ ->]]]; apply q_delete_recycle_removes_event.
  - destruct (Z.eqb opt 1).
    + destruct Hstep as [ps [ready [node [q [_ [_ [_ [_ ->]]]]]]]];
        apply q_delete_recycle_removes_event.
    + destruct Hstep as [-> _]; discriminate Hsuccess.
Qed.

Lemma q_delete_critical_preserves_validity : forall sg s eid e opt result after,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(eventType) = OS_EVENT_TYPE_Q ->
  q_delete_critical sg eid opt s result after -> UCOS2_state_inv sg after.
Proof.
  intros sg s eid e opt result after Hvalid He Htype [node [Hnode Hstep]].
  assert (node = e) by congruence; subst node.
  destruct (Z.eqb opt 0).
  - destruct (negb (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0)) eqn:Hwaiting.
    + destruct Hstep as [_ ->]; exact Hvalid.
    + destruct Hstep as [q [Hq [_ ->]]].
      apply Bool.negb_false_iff in Hwaiting; apply Z.eqb_eq in Hwaiting.
      pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [_ [_ Hentries]]]]]] _]]]].
      apply (proj1 (encode_event_wait_grp_zero_iff_empty sg s.(TskState) e.(waitList)
        (proj1 (Hentries eid e He)))) in Hwaiting.
      unfold q_delete_recycle_state; eapply UCOS2_queue_recycle_preserves_validity;
        [exact Hvalid|exact He|exact Htype|exact Hwaiting].
  - destruct (Z.eqb opt 1).
    + destruct Hstep as [ps [ready [node [q [Hloop [HreadyNode [Hq [_ ->]]]]]]]].
      pose proof (event_broadcast_result sg s eid e PendQ 0 PendAbort ps ready
        Hvalid He ltac:(rewrite Htype; reflexivity) Hloop) as [Hready [Hlast _]].
      assert (node = event_set_wait_list e []) by congruence; subst node.
      unfold q_delete_recycle_state; eapply UCOS2_queue_recycle_preserves_validity;
        [exact Hready|exact Hlast|exact Htype|reflexivity].
    + destruct Hstep as [_ ->]; exact Hvalid.
Qed.

Lemma q_delete_critical_preserves_invocation : forall sg s eid e opt result after invocation origin,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(eventType) = OS_EVENT_TYPE_Q ->
  q_delete_critical sg eid opt s result after ->
  task_invocation_active s.(TskState) invocation origin ->
  task_invocation_active after.(TskState) invocation origin.
Proof.
  intros sg s eid e opt result after invocation origin Hvalid He Htype [node [Hnode Hstep]] Hactive.
  assert (node = e) by congruence; subst node.
  destruct (Z.eqb opt 0).
  - destruct (negb (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0)).
    + destruct Hstep as [_ ->]; exact Hactive.
    + destruct Hstep as [q [_ [_ ->]]]; exact Hactive.
  - destruct (Z.eqb opt 1).
    + destruct Hstep as [ps [ready [node [q [Hloop [_ [_ [_ ->]]]]]]]].
      exact (event_broadcast_preserves_invocation sg eid PendQ 0 PendAbort s ps ready Hloop
        e invocation origin Hvalid He ltac:(rewrite Htype; reflexivity) Hactive).
    + destruct Hstep as [_ ->]; exact Hactive.
Qed.

(** The Queue has been recycled, but the aborted TCB and its invocation
    remain.  A later Queue Pend abort continuation need not dereference
    the now-free Event; this does not assert that OS_Sched has returned. *)
Lemma q_delete_always_updates_waiter : forall sg s eid e result after tid old,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(eventType) = OS_EVENT_TYPE_Q ->
  q_delete_critical sg eid 1 s result after ->
  In tid e.(waitList) -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  after.(TskState).(inUsedTaskStates) tid = Some (task_event_wake_single old PendQ 0 PendAbort).
Proof.
  intros sg s eid e result after tid old Hvalid He Htype [node [Hnode Hstep]] Hin Hold.
  assert (node = e) by congruence; subst node.
  destruct Hstep as [ps [ready [node [q [Hloop [_ [_ [_ ->]]]]]]]].
  exact (event_broadcast_updates_waiter sg eid PendQ 0 PendAbort s ps ready Hloop
    e tid old Hvalid He ltac:(rewrite Htype; reflexivity) Hin Hold).
Qed.

Lemma q_delete_critical_requests_schedule_iff : forall sg s eid e opt result after,
  s.(EventState).(inUsedEventStates) eid = Some e ->
  q_delete_critical sg eid opt s result after ->
  (snd (snd result) = true <-> opt = 1 /\ encode_event_wait_grp e.(waitList) s.(TskState) <> 0).
Proof.
  intros sg s eid e opt result after He [node [Hnode Hstep]].
  assert (node = e) by congruence; subst node.
  destruct (Z.eqb opt 0) eqn:Hnone.
  - apply Z.eqb_eq in Hnone; subst opt.
    destruct (negb (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0)).
    + destruct Hstep as [-> _]; simpl; split; [discriminate|intros [H _]; discriminate].
    + destruct Hstep as [q [_ [-> _]]]; simpl; split; [discriminate|intros [H _]; discriminate].
  - destruct (Z.eqb opt 1) eqn:Halways.
    + apply Z.eqb_eq in Halways; subst opt.
      destruct Hstep as [ps [ready [node [q [_ [_ [_ [-> _]]]]]]]]; simpl.
      rewrite Bool.negb_true_iff, Z.eqb_neq; tauto.
    + apply Z.eqb_neq in Halways; destruct Hstep as [-> _]; simpl.
      split; [discriminate|intros [H _]; contradiction].
Qed.
