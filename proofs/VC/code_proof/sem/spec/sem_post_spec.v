Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.sem.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** V2.93.01 OSSemPost: conditional NULL check, ENTER trace, type
    check, Save.  There is no ISR/lock rejection.  EXIT trace follows
    Restore and, in the wake arm only, OS_Sched.  Hooks/Restore and the
    original invocation's return are not silently folded into this step. *)
Definition sem_post_argument_error (sg : StableGlobVars) (pevent : addr) : option OSErrCode :=
  if (sg.(osKernelConfig).(cfgArgumentChecks) && Z.eqb pevent 0)%bool
  then Some OS_ERR_PEVENT_NULL else None.

Definition sem_post_type_error (type_byte : Z) : option OSErrCode :=
  if Z.eqb type_byte (encode_event_type OS_EVENT_TYPE_SEM) then None else Some OS_ERR_EVENT_TYPE.

(** The bool is the subsequent OS_Sched CALL request, not evidence of
    a context switch.  A nonzero bitmap takes precedence over count.
    Wake uses the actual NULL/PendSem/PendOK arguments and does not
    increment OSEventCnt.  Overflow is an unchanged-kernel-state error. *)
Definition sem_post_critical (sg : StableGlobVars) (eid : EventID)
  : program UCOS2_Verify_State (OSErrCode * bool) :=
  fun s result after => exists e,
    s.(EventState).(inUsedEventStates) eid = Some e /\
    if Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0 then
      exists fields, e.(semFields) = Some fields /\
      if Z.ltb fields.(semCount) 65535 then
        result = (OS_ERR_NONE, false) /\
        after = sem_count_update_state s eid e (fields.(semCount) + 1)
      else result = (OS_ERR_SEM_OVF, false) /\ after = s
    else result = (OS_ERR_NONE, true) /\ exists priority,
      event_task_rdy sg s eid PendSem 0 PendOK = Some (priority, after).

Lemma sem_post_critical_exists : forall sg s eid e,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_SEM -> exists result after, sem_post_critical sg eid s result after.
Proof.
  intros sg s eid e Hvalid He Htype.
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0) eqn:Hempty.
  - pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
    pose proof (Hpayload eid e He) as Hcount; unfold event_payload_consistency in Hcount.
    rewrite Htype in Hcount; destruct e.(semFields) as [fields|] eqn:Hfields; [|contradiction].
    destruct (Z.ltb fields.(semCount) 65535) eqn:Hroom.
    + exists (OS_ERR_NONE, false), (sem_count_update_state s eid e (fields.(semCount) + 1)).
      exists e; split; [exact He|]; rewrite Hempty; exists fields; split; [exact Hfields|].
      rewrite Hroom; split; reflexivity.
    + exists (OS_ERR_SEM_OVF, false), s; exists e; split; [exact He|]; rewrite Hempty.
      exists fields; split; [exact Hfields|]; rewrite Hroom; split; reflexivity.
  - assert (Hkind : event_type_to_pend_type e.(eventType) = Some PendSem) by (rewrite Htype; reflexivity).
    destruct e.(waitList) as [|head tail] eqn:Hlist; [discriminate Hempty|].
    destruct (event_wake_head sg s eid e head tail PendSem 0 PendOK Hvalid He Hkind Hlist)
      as [old [_ [Hcall _]]].
    exists (OS_ERR_NONE, true), (event_wake_state sg s eid e head old PendSem 0 PendOK).
    exists e; split; [exact He|]; rewrite Hlist, Hempty; split; [reflexivity|].
    exists old.(curPrio); exact Hcall.
Qed.

Lemma sem_post_critical_deterministic : forall sg eid s r1 s1 r2 s2,
  sem_post_critical sg eid s r1 s1 -> sem_post_critical sg eid s r2 s2 -> r1 = r2 /\ s1 = s2.
Proof.
  intros sg eid s r1 s1 r2 s2 [e1 [He1 Hfirst]] [e2 [He2 Hsecond]].
  assert (e2 = e1) by congruence; subst e2.
  destruct (Z.eqb (encode_event_wait_grp e1.(waitList) s.(TskState)) 0).
  - destruct Hfirst as [f1 [Hf1 Hfirst]]; destruct Hsecond as [f2 [Hf2 Hsecond]].
    assert (f2 = f1) by congruence; subst f2; destruct (Z.ltb f1.(semCount) 65535); intuition congruence.
  - destruct Hfirst as [-> [p1 Hcall1]]; destruct Hsecond as [-> [p2 Hcall2]]; split; congruence.
Qed.

Lemma sem_post_critical_preserves_validity : forall sg s eid e result after,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_SEM -> sem_post_critical sg eid s result after ->
  UCOS2_state_inv sg after.
Proof.
  intros sg s eid e result after Hvalid He Htype [node [Hnode Hstep]].
  assert (node = e) by congruence; subst node.
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0) eqn:Hempty.
  - destruct Hstep as [fields [Hfields Hstep]].
    destruct (Z.ltb fields.(semCount) 65535) eqn:Hroom; destruct Hstep as [_ ->]; [|exact Hvalid].
    pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload [_ Hentries]]]]]] _]]]].
    pose proof (Hpayload eid e He) as Hcount; unfold event_payload_consistency in Hcount.
    rewrite Htype, Hfields in Hcount.
    pose proof (proj1 (encode_event_wait_grp_zero_iff_empty sg s.(TskState) e.(waitList)
      (proj1 (Hentries eid e He))) (proj1 (Z.eqb_eq _ _) Hempty)) as Hlist.
    apply UCOS2_sem_count_update_preserves_validity; try assumption.
    rewrite Hlist in Hcount |- *; apply sem_increment_preserves_consistency;
      [exact Hcount|apply Z.ltb_lt; exact Hroom].
  - destruct Hstep as [_ [priority Hcall]]; apply Z.eqb_neq in Hempty.
    assert (Hkind : event_type_to_pend_type e.(eventType) = Some PendSem) by (rewrite Htype; reflexivity).
    destruct (event_wake_decompose sg s eid e PendSem 0 PendOK priority after Hvalid He Hkind Hempty Hcall)
      as [head [tail [old [_ [_ [_ [_ [Hafter _]]]]]]]]; exact Hafter.
Qed.

Lemma sem_post_critical_overflow_frame : forall sg eid s result after,
  sem_post_critical sg eid s result after -> fst result <> OS_ERR_NONE ->
  result = (OS_ERR_SEM_OVF, false) /\ after = s.
Proof.
  intros sg eid s result after [e [He Hstep]] Herror.
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0).
  - destruct Hstep as [fields [_ Hstep]]; destruct (Z.ltb fields.(semCount) 65535);
      [destruct Hstep as [-> _]; contradiction Herror; reflexivity|exact Hstep].
  - destruct Hstep as [-> _]; contradiction Herror; reflexivity.
Qed.

Lemma sem_post_critical_wake_observation : forall sg s eid e error after,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_SEM -> sem_post_critical sg eid s (error, true) after ->
  exists head tail old,
    e.(waitList) = head :: tail /\ s.(TskState).(inUsedTaskStates) head = Some old /\
    error = OS_ERR_NONE /\ after = event_wake_state sg s eid e head old PendSem 0 PendOK /\
    after.(EventState).(inUsedEventStates) eid = Some (event_set_wait_list e tail).
Proof.
  intros sg s eid e error after Hvalid He Htype [node [Hnode Hstep]].
  assert (node = e) by congruence; subst node.
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0) eqn:Hempty.
  - destruct Hstep as [fields [_ Hstep]]; destruct (Z.ltb fields.(semCount) 65535);
      destruct Hstep as [Hresult _]; discriminate.
  - destruct Hstep as [Hresult [priority Hcall]]; injection Hresult as Herror; apply Z.eqb_neq in Hempty.
    assert (Hkind : event_type_to_pend_type e.(eventType) = Some PendSem) by (rewrite Htype; reflexivity).
    destruct (event_wake_decompose sg s eid e PendSem 0 PendOK priority after Hvalid He Hkind Hempty Hcall)
      as [head [tail [old [Hlist [Hold [_ [Hafter [_ Hlookup]]]]]]]].
    exists head, tail, old; repeat split; assumption.
Qed.

Lemma sem_post_critical_preserves_residual : forall sg s eid e result after,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_SEM -> sem_post_critical sg eid s result after ->
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |-- UCOS2_raw_rep_missing_task_storage_sched_event sg after.
Proof.
  intros sg s eid e result after Hvalid He Htype [node [Hnode Hstep]].
  assert (node = e) by congruence; subst node.
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0) eqn:Hempty.
  - destruct Hstep as [fields [_ Hstep]]; destruct (Z.ltb fields.(semCount) 65535);
      destruct Hstep as [_ ->]; [|reflexivity].
    unfold UCOS2_raw_rep_missing_task_storage_sched_event, sem_count_update_state; simpl.
    sep_apply_l_atomic (queue_event_update_preserves_storage sg s.(EventState) eid e
      (sem_set_count e (fields.(semCount) + 1)) He eq_refl eq_refl); entailer!.
  - destruct Hstep as [_ [priority Hcall]]; apply Z.eqb_neq in Hempty.
    assert (Hkind : event_type_to_pend_type e.(eventType) = Some PendSem) by (rewrite Htype; reflexivity).
    destruct (event_wake_decompose sg s eid e PendSem 0 PendOK priority after Hvalid He Hkind Hempty Hcall)
      as [head [tail [old [_ [_ [_ [-> _]]]]]]].
    apply UCOS2_event_wake_preserves_residual; exact He.
Qed.

Lemma sem_post_critical_merge_resources : forall sg s eid e result after,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_SEM -> sem_post_critical sg eid s result after ->
  task_public_storage sg after.(TskState) **
    sched_raw_rep sg after.(TskState) after.(SchedState) **
    event_raw_rep sg after.(TskState) after.(EventState) **
    UCOS2_raw_rep_missing_task_storage_sched_event sg s |-- UCOS2_inv sg after.
Proof.
  intros sg s eid e result after Hvalid He Htype Hstep.
  pose proof (sem_post_critical_preserves_validity sg s eid e result after Hvalid He Htype Hstep) as Hafter.
  sep_apply_l_atomic (sem_post_critical_preserves_residual sg s eid e result after Hvalid He Htype Hstep).
  rewrite UCOS2_inv_open_task_storage_sched_event; entailer!.
Qed.

Lemma sem_post_critical_preserves_invocation : forall sg s eid e result after invocation origin,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_SEM -> sem_post_critical sg eid s result after ->
  task_invocation_active s.(TskState) invocation origin ->
  task_invocation_active after.(TskState) invocation origin.
Proof.
  intros sg s eid e result after invocation origin Hvalid He Htype [node [Hnode Hstep]] Hactive.
  assert (node = e) by congruence; subst node.
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0) eqn:Hempty.
  - destruct Hstep as [fields [_ Hstep]]; destruct (Z.ltb fields.(semCount) 65535);
      destruct Hstep as [_ ->]; exact Hactive.
  - destruct Hstep as [_ [priority Hcall]]; apply Z.eqb_neq in Hempty.
    assert (Hkind : event_type_to_pend_type e.(eventType) = Some PendSem) by (rewrite Htype; reflexivity).
    destruct (event_wake_decompose sg s eid e PendSem 0 PendOK priority after Hvalid He Hkind Hempty Hcall)
      as [head [tail [old [_ [Hold [_ [-> _]]]]]]].
    eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hold|reflexivity|exact Hactive].
Qed.
