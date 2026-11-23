Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event_wait Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.

(** These deductions use the actual stable single-wait endpoint. They do
    not assert a stable invariant at a Prepared cut, and they do not obtain
    the original timeout Event from generic validity or call identity. *)
Lemma sem_pend_live_multi_wait_empty : forall sg current tid node,
  UCOS2_state_inv sg current ->
  current.(TskState).(inUsedTaskStates) tid = Some node ->
  node.(eventMultiWaitEvents) = [].
Proof.
  intros sg current tid node Hvalid Hnode.
  destruct Hvalid as [_ [_ [_ [_ [Hcross _]]]]].
  destruct Hcross as [_ [_ [[Hentries [Hback Hclosed]] _]]].
  destruct node.(eventMultiWaitEvents) as [|event tail] eqn:Hlist;
    [reflexivity|].
  assert (Hin : In event node.(eventMultiWaitEvents)).
  { rewrite Hlist; left; reflexivity. }
  destruct (proj2 (Hclosed tid node Hnode) event Hin) as [entry Hentry].
  assert (Hmember : In tid entry.(waitList)).
  { eapply Hback; [exact Hnode|exact Hentry|right; exact Hin]. }
  destruct (event_waiter_task_fields sg current.(TskState) event entry tid
    (Hentries event entry Hentry) Hmember)
    as [same [kind [Hsame [_ [_ [Hempty _]]]]]].
  assert (same = node) by congruence; subst same.
  rewrite Hlist in Hempty; discriminate.
Qed.

Lemma sem_pend_ready_effective : forall sg current tid node,
  UCOS2_state_inv sg current ->
  current.(TskState).(inUsedTaskStates) tid = Some node ->
  In tid current.(SchedState).(readyList) ->
  is_effectively_ready node.(stat) node.(dly) = true.
Proof.
  intros sg current tid node Hvalid Hnode Hmember.
  destruct (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid)))) tid Hmember)
    as [same [Hsame [_ Hready]]].
  assert (same = node) by congruence; subst same; exact Hready.
Qed.

Lemma sem_pend_ready_non_timeout_pointers : forall sg current tid node,
  UCOS2_state_inv sg current ->
  current.(TskState).(inUsedTaskStates) tid = Some node ->
  In tid current.(SchedState).(readyList) ->
  node.(statPend) <> PendTimeout ->
  node.(eventPtr) = None /\ node.(tcbFlagNode) = 0.
Proof.
  intros sg current tid node Hvalid Hnode Hmember Hresult.
  pose proof (sem_pend_ready_effective sg current tid node Hvalid Hnode Hmember) as Hready.
  pose proof (task_effectively_ready_has_no_pending node Hready) as Hclear.
  destruct Hvalid as [_ [_ [_ [_ [Hcross _]]]]].
  pose proof Hcross as [_ [_ [Hwait [_ [_ [Hflag _]]]]]].
  split.
  - destruct node.(eventPtr) as [event|] eqn:Hptr; [|reflexivity].
    destruct (task_event_reference_has_waiter sg current tid node event Hcross Hnode Hptr)
      as [entry [Hentry Hwaiting]].
    destruct Hwait as [Hentries _].
    destruct (event_waiter_task_fields sg current.(TskState) event entry tid
      (Hentries event entry Hentry) Hwaiting)
      as [same [kind [Hsame [_ [_ [_ Hlinked]]]]]].
    assert (same = node) by congruence; subst same.
    destruct Hlinked as [Hpending|[_ [Htimeout _]]].
    + rewrite Hclear in Hpending; destruct kind; discriminate.
    + contradiction.
  - destruct (Z.eq_dec node.(tcbFlagNode) 0) as [Hzero|Hnonzero]; [exact Hzero|].
    destruct Hflag as [Hnodes Htasks].
    destruct (Htasks tid node Hnode (or_introl Hnonzero)) as [waiter [Hwaiter Htid]].
    destruct (Hnodes _ waiter Hwaiter)
      as [_ [same [Hsame [_ [_ [_ [Hlinked _]]]]]]].
    rewrite Htid in Hsame; assert (same = node) by congruence; subst same.
    destruct Hlinked as [Hpending|[_ [Htimeout _]]].
    + rewrite Hclear in Hpending; discriminate.
    + contradiction.
Qed.

(** The timeout association is a concrete endpoint fact supplied by the
    returning API/source producer. No public Require or environment-wide
    preservation promise is introduced by this consumer. *)
Lemma sem_pend_ready_resume_registration : forall sg current eid tid node,
  UCOS2_state_inv sg current ->
  current.(TskState).(inUsedTaskStates) tid = Some node ->
  In tid current.(SchedState).(readyList) ->
  (node.(statPend) = PendTimeout -> node.(eventPtr) = Some eid) ->
  sem_pend_resume_registration eid node.
Proof.
  intros sg current eid tid node Hvalid Hnode Hmember Htimeout.
  unfold sem_pend_resume_registration; split.
  - eapply sem_pend_live_multi_wait_empty; eassumption.
  - destruct node.(statPend) eqn:Hresult.
    + destruct (sem_pend_ready_non_timeout_pointers sg current tid node
        Hvalid Hnode Hmember ltac:(rewrite Hresult; discriminate)) as [Hptr Hflag].
      split; assumption.
    + assert (Hptr : node.(eventPtr) = Some eid) by (apply Htimeout; reflexivity).
      pose proof Hvalid as [_ [_ [_ [_ [Hcross _]]]]].
      destruct Hcross as [_ [_ [_ [_ [_ [Hflag _]]]]]].
      split; [|exact Hptr].
      exact (proj1 (task_with_event_ptr_has_no_flag_registration sg current.(TskState)
        current.(FlagState) tid node eid Hflag Hnode Hptr)).
    + destruct (sem_pend_ready_non_timeout_pointers sg current tid node
        Hvalid Hnode Hmember ltac:(rewrite Hresult; discriminate)) as [Hptr Hflag].
      split; assumption.
Qed.

Lemma sem_pend_ready_wait_continuation : forall sg current eid tid node generation,
  UCOS2_state_inv sg current ->
  current.(TskState).(inUsedTaskStates) tid = Some node ->
  In tid current.(SchedState).(readyList) ->
  node.(taskGeneration) = generation ->
  (node.(statPend) = PendTimeout -> node.(eventPtr) = Some eid) ->
  sem_pend_wait_continuation eid generation node.
Proof.
  intros sg current eid tid node generation Hvalid Hnode Hmember Hgeneration Htimeout.
  pose proof (sem_pend_ready_effective sg current tid node Hvalid Hnode Hmember) as Hready.
  pose proof (task_effectively_ready_has_no_pending node Hready) as Hclear.
  assert (Hdelay : node.(dly) = 0).
  { unfold is_effectively_ready in Hready; rewrite Hclear, Z.eqb_refl in Hready.
    apply andb_true_iff in Hready; apply Z.eqb_eq; exact (proj2 Hready). }
  destruct (sem_pend_ready_resume_registration sg current eid tid node
    Hvalid Hnode Hmember Htimeout) as [Hmulti [Hflag Hptr]].
  unfold sem_pend_wait_continuation; split; [exact Hgeneration|].
  split; [exact Hmulti|]. split; [exact Hflag|].
  destruct node.(statPend) eqn:Hresult.
  - right; split; [exact Hptr|]. split; [exact Hclear|discriminate].
  - left; split; [exact Hptr|]. right; repeat split; assumption.
  - right; split; [exact Hptr|]. split; [exact Hclear|discriminate].
Qed.

(** Select the live node once, from the actual returned Task source. Both
    registration and generation refer to that same node and original stack
    slot. The heap and the caller's local continuation are not reselected. *)
Lemma sem_pend_returned_ready_waiter : forall sg original returned current eid,
  UCOS2_state_inv sg current ->
  kernel_call_task_source returned current ->
  kernel_stack_call_same_call returned original ->
  In original.(os_sched_call_stack).(stackLeaseSlot) current.(SchedState).(readyList) ->
  (forall node,
    current.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
    node.(statPend) = PendTimeout -> node.(eventPtr) = Some eid) ->
  exists node,
    sem_pend_resume_entry sg current eid original.(os_sched_call_stack).(stackLeaseSlot) node /\
    node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) /\
    sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) node.
Proof.
  intros sg original returned current eid Hvalid Hsource Hsame Hmember Htimeout.
  destruct (kernel_call_task_source_current_at returned current Hsource)
    as [Hcurrent [node [Hnode Hgeneration]]].
  destruct Hsame as [_ [_ Hstack]].
  rewrite Hstack in Hcurrent, Hnode, Hgeneration.
  assert (Hregistration : sem_pend_resume_registration eid node).
  { eapply sem_pend_ready_resume_registration; [exact Hvalid|exact Hnode|exact Hmember|].
    exact (Htimeout node Hnode). }
  exists node; split.
  - exact (conj Hvalid (conj Hcurrent (conj Hnode (conj Hregistration Hmember)))).
  - split; [exact Hgeneration|].
    eapply sem_pend_ready_wait_continuation;
      [exact Hvalid|exact Hnode|exact Hmember|exact Hgeneration|exact (Htimeout node Hnode)].
Qed.
