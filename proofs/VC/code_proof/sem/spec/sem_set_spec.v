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
Require Import Ucos2Verify.lib.sem.
Require Import Ucos2Verify.lib.ucos2_verify_inv.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.

(** V2.93.01 OSSemSet: safety hook, conditional NULL argument check,
    type check, then Save.  No ISR/lock rejection or OS_Sched call.
    The source writes perr=NONE BEFORE either branch and overwrites it
    with TASK_WAITING only in the rejection arm, all BEFORE Restore. *)
Definition sem_set_safety_exception_requested (sg : StableGlobVars) (perr : addr) : bool :=
  (sg.(osKernelConfig).(cfgSafetyCritical) && Z.eqb perr 0)%bool.

Definition sem_set_argument_error (sg : StableGlobVars) (pevent : addr) : option OSErrCode :=
  if (sg.(osKernelConfig).(cfgArgumentChecks) && Z.eqb pevent 0)%bool
  then Some OS_ERR_PEVENT_NULL else None.

Definition sem_set_type_error (type_byte : Z) : option OSErrCode :=
  if Z.eqb type_byte (encode_event_type OS_EVENT_TYPE_SEM) then None else Some OS_ERR_EVENT_TYPE.

(** [count] is the actual INT16U argument; its typed range is a caller
    fact, not a new runtime guard.  Retain count-first/bitmap-second order
    instead of replacing it by an invariant-derived wait-list guard. *)
Definition sem_set_critical (sg : StableGlobVars) (eid : EventID) (count : Z)
  : program UCOS2_Verify_State OSErrCode :=
  fun s error after => exists e fields,
    s.(EventState).(inUsedEventStates) eid = Some e /\ e.(semFields) = Some fields /\
    if Z.ltb 0 fields.(semCount) then
      error = OS_ERR_NONE /\ after = sem_count_update_state s eid e count
    else if Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0 then
      error = OS_ERR_NONE /\ after = sem_count_update_state s eid e count
    else error = OS_ERR_TASK_WAITING /\ after = s.

Lemma sem_set_critical_exists : forall sg s eid e fields count,
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(semFields) = Some fields ->
  exists error after, sem_set_critical sg eid count s error after.
Proof.
  intros sg s eid e fields count He Hfields.
  destruct (Z.ltb 0 fields.(semCount)) eqn:Hpositive.
  - exists OS_ERR_NONE, (sem_count_update_state s eid e count); exists e, fields.
    split; [exact He|]; split; [exact Hfields|]; rewrite Hpositive; split; reflexivity.
  - destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0) eqn:Hempty.
    + exists OS_ERR_NONE, (sem_count_update_state s eid e count); exists e, fields.
      split; [exact He|]; split; [exact Hfields|]; rewrite Hpositive, Hempty; split; reflexivity.
    + exists OS_ERR_TASK_WAITING, s; exists e, fields.
      split; [exact He|]; split; [exact Hfields|]; rewrite Hpositive, Hempty; split; reflexivity.
Qed.

Lemma sem_set_critical_deterministic : forall sg eid count s r1 s1 r2 s2,
  sem_set_critical sg eid count s r1 s1 -> sem_set_critical sg eid count s r2 s2 ->
  r1 = r2 /\ s1 = s2.
Proof.
  intros sg eid count s r1 s1 r2 s2 [e1 [f1 [He1 [Hf1 Hfirst]]]]
    [e2 [f2 [He2 [Hf2 Hsecond]]]].
  assert (e2 = e1) by congruence; subst e2; assert (f2 = f1) by congruence; subst f2.
  destruct (Z.ltb 0 f1.(semCount)); [intuition congruence|].
  destruct (Z.eqb (encode_event_wait_grp e1.(waitList) s.(TskState)) 0); intuition congruence.
Qed.

Lemma sem_set_critical_preserves_validity : forall sg s eid e count error after,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_SEM -> 0 <= count <= 65535 ->
  sem_set_critical sg eid count s error after -> UCOS2_state_inv sg after.
Proof.
  intros sg s eid e count error after Hvalid He Htype Hrange [node [fields [Hnode [Hfields Hstep]]]].
  assert (node = e) by congruence; subst node.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload [_ Hentries]]]]]] _]]]].
  pose proof (Hpayload eid e He) as Hcount; unfold event_payload_consistency in Hcount.
  rewrite Htype, Hfields in Hcount.
  assert (Hwrite : e.(waitList) = [] ->
    UCOS2_state_inv sg (sem_count_update_state s eid e count)).
  { intro Hlist; apply UCOS2_sem_count_update_preserves_validity; try assumption.
    rewrite Hlist; split; [exact Hrange|intros H; contradiction]. }
  destruct (Z.ltb 0 fields.(semCount)) eqn:Hpositive.
  - destruct Hstep as [_ ->]; apply Hwrite.
    apply sem_positive_count_no_waiters with (fields := fields); [exact Hcount|].
    apply Z.ltb_lt; exact Hpositive.
  - destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0) eqn:Hempty.
    + destruct Hstep as [_ ->]; apply Hwrite.
      apply (proj1 (encode_event_wait_grp_zero_iff_empty sg s.(TskState) e.(waitList)
        (proj1 (Hentries eid e He)))); apply Z.eqb_eq; exact Hempty.
    + destruct Hstep as [_ ->]; exact Hvalid.
Qed.

Lemma sem_set_critical_rejected_frame : forall sg eid count s error after,
  sem_set_critical sg eid count s error after -> error <> OS_ERR_NONE ->
  error = OS_ERR_TASK_WAITING /\ after = s.
Proof.
  intros sg eid count s error after [e [fields [_ [_ Hstep]]]] Herror.
  destruct (Z.ltb 0 fields.(semCount)); [intuition congruence|].
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0); intuition congruence.
Qed.

Lemma sem_set_critical_preserves_invocation : forall sg eid count s error after invocation origin,
  sem_set_critical sg eid count s error after ->
  task_invocation_active s.(TskState) invocation origin ->
  task_invocation_active after.(TskState) invocation origin.
Proof.
  intros sg eid count s error after invocation origin [e [fields [_ [_ Hstep]]]] Hactive.
  destruct (Z.ltb 0 fields.(semCount)); [destruct Hstep as [_ ->]; exact Hactive|].
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0);
    destruct Hstep as [_ ->]; exact Hactive.
Qed.
