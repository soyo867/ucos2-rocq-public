Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.

Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Composition interfaces for the V2.93.01 single-Event wait path.
    These proofs connect the actual Pend/Post/Tick transformers.  They
    neither turn the unmasked interval into one atomic operation nor
    assert that OS_Sched eventually returns.  The returning invocation,
    current-task observation and platform resources remain separate call
    obligations.  In particular Tick leaves the Event registration linked
    until the returning Pend performs Remove. *)
Lemma sem_pend_wait_task_observations : forall sg s eid e tid old timeout,
  let waiting := task_set_event_ptr
    (task_prepare_event_wait old PendSem timeout) (Some eid) in
  let after := event_pend_state sg s eid e tid old PendSem timeout in
  after.(TskState).(inUsedTaskStates) tid = Some waiting /\
  ~ In tid after.(SchedState).(readyList) /\
  is_effectively_ready waiting.(stat) waiting.(dly) = false /\
  waiting.(eventPtr) = Some eid /\ waiting.(statPend) = PendOK /\
  waiting.(dly) = timeout /\ waiting.(taskGeneration) = old.(taskGeneration).
Proof.
  intros sg s eid e tid old timeout; cbn zeta.
  split.
  - cbn [event_pend_state event_wait_state replace_SchedS replace_EventS
      replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
    rewrite Z.eqb_refl; reflexivity.
  - split; [apply remove_Z_eqb_notin|].
    split; [apply task_prepare_event_wait_not_ready|].
    repeat split; reflexivity.
Qed.

(** Post's selected waiter is obtained from the actual sorted wait list,
    not from a stale current-task cache.  Both a still-blocked waiter and
    an expired-but-not-yet-removed waiter can be selected by this branch. *)
Lemma sem_pend_post_establishes_resume_registration :
  forall sg s eid e tid tail old after,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_SEM -> e.(waitList) = tid :: tail ->
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  old.(eventMultiWaitEvents) = [] -> old.(tcbFlagNode) = 0 ->
  sem_post_critical sg eid s (OS_ERR_NONE, true) after ->
  after = event_wake_state sg s eid e tid old PendSem 0 PendOK /\
  after.(TskState).(inUsedTaskStates) tid =
    Some (task_event_wake_single old PendSem 0 PendOK) /\
  sem_pend_resume_registration eid (task_event_wake_single old PendSem 0 PendOK) /\
  UCOS2_state_inv sg after.
Proof.
  intros sg s eid e tid tail old after Hvalid He Htype Hlist Hold Hmulti Hflag Hstep.
  destruct (sem_post_critical_wake_observation sg s eid e OS_ERR_NONE after
    Hvalid He Htype Hstep) as [head [rest [t [Hhead [Ht [_ [Hafter Hevent]]]]]]].
  rewrite Hlist in Hhead; injection Hhead as Htid Htail; subst head rest.
  assert (t = old) by congruence; subst t.
  split; [exact Hafter|].
  split.
  - rewrite Hafter; cbn [event_wake_state replace_SchedS replace_EventS
      replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
    rewrite Z.eqb_refl; reflexivity.
  - split.
    + unfold sem_pend_resume_registration; split; [exact Hmulti|].
      split; [exact Hflag|reflexivity].
    + eapply sem_post_critical_preserves_validity; eassumption.
Qed.

Lemma sem_pend_tick_establishes_timeout_registration : forall sg s eid tid old,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  old.(dly) = 1 -> task_non_suspension_bits old.(stat) = task_pend_mask PendSem ->
  old.(eventPtr) = Some eid -> old.(eventMultiWaitEvents) = [] -> old.(tcbFlagNode) = 0 ->
  let after := tick_task_step sg tid old s in
  after.(TskState).(inUsedTaskStates) tid = Some (tick_task_update old) /\
  sem_pend_resume_registration eid (tick_task_update old) /\
  (tick_task_update old).(statPend) = PendTimeout /\
  after.(EventState) = s.(EventState) /\
  (exists e, after.(EventState).(inUsedEventStates) eid = Some e /\ In tid e.(waitList)) /\
  UCOS2_state_inv sg after.
Proof.
  intros sg s eid tid old Hcfg Hvalid Hold Hd Hpending Hptr Hmulti Hflag; cbn zeta.
  destruct (tick_task_one_tick_timeout old PendSem Hd Hpending ltac:(discriminate))
    as [Hdelay [Hbits [Htimeout Hpointer]]].
  assert (Hpost : UCOS2_state_inv sg (tick_task_step sg tid old s)).
  { eapply time_tick_task_step_preserves_state_inv; eassumption. }
  assert (Htask : (tick_task_step sg tid old s).(TskState).(inUsedTaskStates) tid =
      Some (tick_task_update old)).
  { rewrite tick_task_step_task_state_eq by exact Hold.
    cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity. }
  split; [exact Htask|].
  split.
  - unfold sem_pend_resume_registration; rewrite Htimeout.
    split; [unfold tick_task_update; rewrite Hd; exact Hmulti|].
    split; [unfold tick_task_update; rewrite Hd; exact Hflag|].
    rewrite Hpointer; exact Hptr.
  - split; [exact Htimeout|].
    split.
    + unfold tick_task_step; rewrite Hd, Hdelay; reflexivity.
    + split; [|exact Hpost].
      eapply sem_pend_resume_timeout_event; [exact Hpost|exact Htask|].
      rewrite Hpointer; exact Hptr.
Qed.

(** The final caller stores clear the registration and status, but retain
    Msg and Dly.  A timeout removes the Event entry before these stores;
    the duplicate NULL assignment is not a second list removal. *)
Lemma sem_pend_resume_cleanup_observations : forall sg eid s tid old result after,
  s.(SchedState).(curTaskID) = Some tid ->
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_resume_critical sg eid s result after ->
  exists cleaned, after.(TskState).(inUsedTaskStates) tid = Some cleaned /\
    cleaned.(stat) = Byte.zero /\ cleaned.(statPend) = PendOK /\
    cleaned.(eventPtr) = None /\ cleaned.(msg) = old.(msg) /\
    cleaned.(dly) = old.(dly) /\ cleaned.(taskGeneration) = old.(taskGeneration).
Proof.
  intros sg eid s tid old result after Hcur Hold Hstep.
  rewrite (proj1 (sem_pend_resume_critical_task_update sg eid s tid old result after
    Hcur Hold Hstep)).
  exists (task_event_pend_cleanup sg.(osKernelConfig).(cfgEventMultiEnabled) false old).
  split.
  - cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
  - destruct sg.(osKernelConfig).(cfgEventMultiEnabled); repeat split; reflexivity.
Qed.

(** A continuation assertion over existing TCB fields, not another global
    lifecycle record. The linked arm includes the expiry-before-Remove
    stage; the released arm allows Post/Abort to replace that result. *)
Definition sem_pend_wait_continuation (eid : EventID) (generation : nat)
  (t : TaskAbstractState) : Prop :=
  t.(taskGeneration) = generation /\ t.(eventMultiWaitEvents) = [] /\ t.(tcbFlagNode) = 0 /\
  or (t.(eventPtr) = Some eid /\ task_linked_wait_phase t PendSem)
   (t.(eventPtr) = None /\ task_non_suspension_bits t.(stat) = 0 /\
    t.(statPend) <> PendTimeout).

(** Only fields used by the Pend continuation are compared. In particular
    priority/bitmap coordinates, saved SP, list links, name, delete request,
    profiling and register fields may really change. This is an observation
    relation, not an operation or a permission: a concrete source client
    must prove it for the fields that its actual stores leave untouched. *)
Definition sem_pend_wait_fields_equal (before after : TaskAbstractState) : Prop :=
  after.(taskID) = before.(taskID) /\
  after.(taskGeneration) = before.(taskGeneration) /\
  after.(stat) = before.(stat) /\ after.(statPend) = before.(statPend) /\
  after.(dly) = before.(dly) /\ after.(eventPtr) = before.(eventPtr) /\
  after.(eventMultiWaitEvents) = before.(eventMultiWaitEvents) /\
  after.(tcbFlagNode) = before.(tcbFlagNode).

Lemma sem_pend_wait_fields_equal_preserves_continuation : forall eid generation before after,
  sem_pend_wait_fields_equal before after ->
  sem_pend_wait_continuation eid generation before ->
  sem_pend_wait_continuation eid generation after.
Proof.
  intros eid generation before after [Hid [Hg [Hs [Hp [Hd [He [Hm Hf]]]]]]].
  unfold sem_pend_wait_continuation, task_linked_wait_phase.
  rewrite Hg, Hs, Hp, Hd, He, Hm, Hf; trivial.
Qed.

(** OSTimeDlyResume's nonzero-delay branch, Source/os_time.c:202--208.
    The source clears the INT32U delay directly; it does not advance the
    kernel clock or run a sequence of synthetic ticks. Pending status is
    cleared to timeout, while an already released task gets PendOK. *)
Definition sem_pend_delay_resume_task (t : TaskAbstractState) : TaskAbstractState :=
  {| taskID := t.(taskID); taskGeneration := t.(taskGeneration);
     tcbStkPtr := t.(tcbStkPtr); tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom); tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt); tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode); tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName); tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr); tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart); tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed); tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43); tcbEventMultiPtr := t.(tcbEventMultiPtr);
     curPrio := t.(curPrio); stat := task_status_after_timeout t.(stat);
     statPend := snd (task_status_timeout (encode_task_status t.(stat)));
     dly := 0; eventPtr := t.(eventPtr); eventMultiWaitEvents := t.(eventMultiWaitEvents);
     eventMultiRdy := t.(eventMultiRdy); msg := t.(msg);
     nextTCB := t.(nextTCB); prevTCB := t.(prevTCB); delReq := t.(delReq) |}.

Lemma sem_pend_delay_resume_preserves_continuation : forall eid generation t,
  t.(dly) <> 0 -> sem_pend_wait_continuation eid generation t ->
  sem_pend_wait_continuation eid generation (sem_pend_delay_resume_task t).
Proof.
  intros eid generation t Hdelay [Hg [Hm [Hf Hphase]]].
  split; [exact Hg|]. split; [exact Hm|]. split; [exact Hf|].
  destruct Hphase as [[Hptr [Hpending|[Hclear [Htimeout Hzero]]]]|[Hptr [Hclear Hresult]]].
  - left; split; [exact Hptr|]. right.
    destruct (task_status_after_timeout_single_kind t.(stat) PendSem Hpending ltac:(discriminate))
      as [Hclear Htimeout].
    exact (conj Hclear (conj Htimeout eq_refl)).
  - contradiction.
  - right; split; [exact Hptr|].
    change (task_non_suspension_bits (task_status_after_timeout t.(stat)) = 0 /\
      snd (task_status_timeout (encode_task_status t.(stat))) <> PendTimeout).
    rewrite (task_status_single_of_mask t.(stat) None Hclear).
    destruct (task_is_suspended t.(stat)); split; reflexivity || discriminate.
Qed.

(** Source projections relevant to this wait. Other tasks/modules use the
    reflexive closure when they do not change this TCB. This is not a new
    all-kernel STS or a permission to execute these operations: actual
    kernel steps and their ownership/validity certificates are separate.
    Deletion is deliberately absent from a returning live-instance trace;
    its retirement outcome belongs to the existing invocation protocol. *)
Inductive sem_pend_wait_effect : TaskAbstractState -> TaskAbstractState -> Prop :=
| SemPendWaitTick : forall t, sem_pend_wait_effect t (tick_task_update t)
| SemPendWaitWake : forall t result, result <> PendTimeout ->
    sem_pend_wait_effect t (task_event_wake_single t PendSem 0 result)
| SemPendWaitSaveStack : forall t sp, sem_pend_wait_effect t (task_set_saved_sp t sp)
| SemPendWaitSuspend : forall t, sem_pend_wait_effect t (task_suspend t)
| SemPendWaitResume : forall t, sem_pend_wait_effect t (task_resume t)
| SemPendWaitOtherFields : forall before after,
    sem_pend_wait_fields_equal before after -> sem_pend_wait_effect before after
| SemPendWaitDelayResume : forall t, t.(dly) <> 0 ->
    sem_pend_wait_effect t (sem_pend_delay_resume_task t).

Lemma sem_pend_wait_establishes_continuation : forall eid old timeout,
  is_effectively_ready old.(stat) old.(dly) = true ->
  old.(eventMultiWaitEvents) = [] -> old.(tcbFlagNode) = 0 ->
  sem_pend_wait_continuation eid old.(taskGeneration)
    (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)).
Proof.
  intros eid old timeout Hready Hmulti Hflag.
  split; [reflexivity|]. split; [exact Hmulti|]. split; [exact Hflag|].
  left; split; [reflexivity|]. left.
  apply task_prepare_event_wait_pending_bits.
  apply task_effectively_ready_has_no_pending; exact Hready.
Qed.

Lemma sem_pend_wait_effect_preserves_continuation : forall eid generation before after,
  sem_pend_wait_effect before after ->
  sem_pend_wait_continuation eid generation before ->
  sem_pend_wait_continuation eid generation after.
Proof.
  intros eid generation before after Hstep;
    destruct Hstep as [t|t result HwakeResult|t sp|t|t|before after Hfields|t Hdelay];
    try (eapply sem_pend_wait_fields_equal_preserves_continuation; exact Hfields);
    try (eapply sem_pend_delay_resume_preserves_continuation; exact Hdelay).
  all: intros [Hg [Hm [Hf Hphase]]].
  - pose proof (tick_task_preserves_non_timeout_fields t) as Hfields; cbn zeta in Hfields.
    split; [intuition congruence|]. split; [intuition congruence|]. split; [intuition congruence|].
    destruct Hphase as [[Hptr Hlinked]|[Hptr [Hclear Hresult]]].
    + left; split; [intuition congruence|]. apply tick_preserves_linked_phase; exact Hlinked.
    + right; split; [intuition congruence|].
      unfold tick_task_update; destruct (Z.eqb t.(dly) 0); [auto|].
      destruct (Z.eqb (t.(dly) - 1) 0); [|auto].
      cbn [stat statPend].
      rewrite (task_status_single_of_mask t.(stat) None Hclear).
      destruct (task_is_suspended t.(stat)); split; reflexivity || discriminate.
  - split; [exact Hg|]. split; [exact Hm|]. split; [exact Hf|].
    right; split; [reflexivity|]. split; [|exact HwakeResult].
    destruct Hphase as [[Hptr Hlinked]|[Hptr [Hclear Hresult]]].
    + exact (proj2 (task_event_wake_single_clears_registration t PendSem 0 result Hlinked)).
    + change (task_non_suspension_bits (task_clear_pending_status t.(stat) PendSem) = 0).
      rewrite task_clear_pending_status_none by exact Hclear; exact Hclear.
  - exact (conj Hg (conj Hm (conj Hf Hphase))).
  - split; [exact Hg|]. split; [exact Hm|]. split; [exact Hf|].
    destruct Hphase as [[Hptr Hlinked]|[Hptr [Hclear Hresult]]].
    + left; split; [exact Hptr|]. apply task_suspend_preserves_linked_phase; exact Hlinked.
    + right; split; [exact Hptr|]. split; [|exact Hresult].
      exact (eq_trans (proj1 (task_status_suspend_observations t.(stat))) Hclear).
  - split; [exact Hg|]. split; [exact Hm|]. split; [exact Hf|].
    destruct Hphase as [[Hptr Hlinked]|[Hptr [Hclear Hresult]]].
    + left; split; [exact Hptr|]. apply task_resume_preserves_linked_phase; exact Hlinked.
    + right; split; [exact Hptr|]. split; [|exact Hresult].
      exact (eq_trans (proj1 (task_status_resume_observations t.(stat))) Hclear).
Qed.

Lemma sem_pend_wait_trace_preserves_continuation : forall eid generation before after,
  clos_refl_trans TaskAbstractState sem_pend_wait_effect before after ->
  sem_pend_wait_continuation eid generation before ->
  sem_pend_wait_continuation eid generation after.
Proof.
  intros eid generation before after Htrace; induction Htrace; intros Hbefore.
  - eapply sem_pend_wait_effect_preserves_continuation; eassumption.
  - exact Hbefore.
  - apply IHHtrace2; apply IHHtrace1; exact Hbefore.
Qed.

Lemma sem_pend_wait_ready_resume_registration : forall eid generation t,
  sem_pend_wait_continuation eid generation t ->
  is_effectively_ready t.(stat) t.(dly) = true ->
  sem_pend_resume_registration eid t /\ t.(taskGeneration) = generation.
Proof.
  intros eid generation t [Hg [Hm [Hf Hphase]]] Hready.
  split; [|exact Hg]. split; [exact Hm|]. split; [exact Hf|].
  destruct Hphase as [[Hptr [Hpending|[Hclear [Htimeout Hdelay]]]]|[Hptr [Hclear Hresult]]].
  - pose proof (task_effectively_ready_has_no_pending t Hready) as Hnone.
    rewrite Hnone in Hpending; discriminate.
  - rewrite Htimeout; exact Hptr.
  - destruct t.(statPend); exact Hptr || contradiction.
Qed.

(** Composed kernel-resource endpoint. The actual foreign interval supplies
    validity and lifetime preservation, while the source-projection trace
    supplies the wait-specific rely obligation. Neither is inferred from
    the other. A caller must establish that its actual actions map to the
    constructors above; arbitrary callbacks are NOT declared harmless.
    perr/stack cells remain caller resources and are not manufactured here. *)
Lemma sem_pend_wait_return_merge :
  forall critical sg s eid e fields tid old timeout invocation resumed current result after,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_SEM -> e.(semFields) = Some fields -> fields.(semCount) <= 0 ->
  s.(TskState).(inUsedTaskStates) tid = Some old -> old.(curPrio) <> sg.(osLowestPrio) ->
  old.(eventPtr) = None -> old.(eventMultiWaitEvents) = [] -> old.(tcbFlagNode) = 0 ->
  In tid s.(SchedState).(readyList) ->
  task_invocation_active s.(TskState) invocation (RunningInvocation tid old.(taskGeneration)) ->
  critical_region_interval critical sg invocation
    (event_pend_state sg s eid e tid old PendSem timeout) resumed ->
  resumed.(SchedState).(curTaskID) = Some tid ->
  resumed.(TskState).(inUsedTaskStates) tid = Some current ->
  sched_task_call_boundary resumed.(TskState) resumed.(SchedState) ->
  clos_refl_trans TaskAbstractState sem_pend_wait_effect
    (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)) current ->
  sem_pend_resume_critical sg eid resumed result after ->
  UCOS2_state_inv sg after /\
  task_invocation_active after.(TskState) invocation (RunningInvocation tid old.(taskGeneration)) /\
  (task_public_storage sg after.(TskState) **
   sched_raw_rep sg resumed.(TskState) resumed.(SchedState) **
   event_raw_rep sg resumed.(TskState) after.(EventState) **
   UCOS2_raw_rep_missing_task_storage_sched_event sg resumed |-- UCOS2_inv sg after).
Proof.
  intros critical sg s eid e fields tid old timeout invocation resumed current result after
    Hvalid He Htype Hfields Hempty Hold Hnonidle Hnull Hmulti Hflag Hready Hactive
    Hinterval Hcur Hcurrent Hboundary Heffects Hcleanup.
  pose proof (sem_pend_wait_preserves_validity sg s eid e fields tid old timeout
    Hvalid He Htype Hfields Hempty Hold Hnonidle Hnull Hmulti Hflag Hready) as Hwaiting.
  destruct (critical_region_interval_transports_resources critical sg invocation
    _ resumed Hinterval Hwaiting) as [Hresumed [_ Hlive]].
  assert (HactiveWaiting : task_invocation_active
    (event_pend_state sg s eid e tid old PendSem timeout).(TskState) invocation
    (RunningInvocation tid old.(taskGeneration))).
  { eapply glob_task_set_usedtask_preserves_invocation_active;
      [exact Hold|reflexivity|exact Hactive]. }
  specialize (Hlive _ HactiveWaiting).
  pose proof Hvalid as [_ [_ [Hsched _]]].
  destruct (proj1 (proj1 Hsched) tid Hready) as [found [Hfound [_ Heffective]]].
  assert (found = old) by congruence; subst found.
  pose proof (sem_pend_wait_establishes_continuation eid old timeout Heffective Hmulti Hflag)
    as Hcontinuation.
  pose proof (sem_pend_wait_trace_preserves_continuation eid old.(taskGeneration)
    _ current Heffects Hcontinuation) as HcurrentContinuation.
  destruct Hboundary as [Hrunning [selected [node [Hnode [Hselected [Hpriority [Hmember HreadyNow]]]]]]].
  assert (selected = tid) by congruence; subst selected.
  assert (node = current) by congruence; subst node.
  destruct (sem_pend_wait_ready_resume_registration eid old.(taskGeneration) current
    HcurrentContinuation HreadyNow) as [Hregistration Hgeneration].
  split.
  - eapply sem_pend_resume_critical_preserves_validity; eassumption.
  - split.
    + eapply sem_pend_resume_critical_preserves_invocation; eassumption.
    + eapply sem_pend_resume_critical_merge_resources; eassumption.
Qed.
