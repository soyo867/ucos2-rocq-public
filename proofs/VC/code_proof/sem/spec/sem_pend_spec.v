Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.sem.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSSemPend, V2.93.01 os_sem.c:321--404.  The pre-Save observations,
    first critical section and returning critical section are separate.
    The C result is void; OSErrCode below observes the eventual perr
    store, not a C return value.  In the immediate branch perr is written
    AFTER Restore; the returning switch writes it BEFORE cleanup/Restore.
    Trace hooks, saved interrupt state and scheduler return remain actual
    call boundaries, not implicit atomic steps.  The timeout argument is
    the caller's INT32U value; no extra runtime range guard is inserted. *)
Definition sem_pend_safety_exception_requested (sg : StableGlobVars) (perr : addr) : bool :=
  (sg.(osKernelConfig).(cfgSafetyCritical) && Z.eqb perr 0)%bool.

Definition sem_pend_argument_error (sg : StableGlobVars) (pevent : addr) : option OSErrCode :=
  if (sg.(osKernelConfig).(cfgArgumentChecks) && Z.eqb pevent 0)%bool
  then Some OS_ERR_PEVENT_NULL else None.

(** The ENTER trace follows the argument check; type/ISR/lock checks
    follow it in this order.  Each input is a source-time observation,
    not a claim that all unmasked reads see one unchanged state.  A
    returning safety hook leads directly to return without writing perr. *)
Definition sem_pend_context_error (type_byte int_nesting lock_nesting : Z) : option OSErrCode :=
  if negb (Z.eqb type_byte (encode_event_type OS_EVENT_TYPE_SEM)) then Some OS_ERR_EVENT_TYPE else
  if Z.ltb 0 int_nesting then Some OS_ERR_PEND_ISR else
  if Z.ltb 0 lock_nesting then Some OS_ERR_PEND_LOCKED else None.

Lemma sem_pend_context_error_type_first : forall ty nesting locked,
  ty <> encode_event_type OS_EVENT_TYPE_SEM ->
  sem_pend_context_error ty nesting locked = Some OS_ERR_EVENT_TYPE.
Proof.
  intros; unfold sem_pend_context_error; rewrite (proj2 (Z.eqb_neq _ _) H); reflexivity.
Qed.

Lemma sem_pend_context_error_isr_before_lock : forall nesting locked,
  0 < nesting ->
  sem_pend_context_error (encode_event_type OS_EVENT_TYPE_SEM) nesting locked = Some OS_ERR_PEND_ISR.
Proof.
  intros; unfold sem_pend_context_error; rewrite Z.eqb_refl, (proj2 (Z.ltb_lt _ _) H); reflexivity.
Qed.

Lemma sem_pend_context_error_locked : forall locked,
  0 < locked ->
  sem_pend_context_error (encode_event_type OS_EVENT_TYPE_SEM) 0 locked = Some OS_ERR_PEND_LOCKED.
Proof.
  intros; unfold sem_pend_context_error; rewrite Z.eqb_refl, (proj2 (Z.ltb_lt _ _) H); reflexivity.
Qed.

(** A critical-section phase result, not the public void return.  The
    waiting branch saves the actual task instance for a later invocation
    continuation; it does not promise that OS_Sched returns. *)
Inductive SemPendStart : Type :=
| SemPendAcquired
| SemPendWaiting (tid : TaskID) (generation : nat).

Definition sem_pend_first_critical (sg : StableGlobVars) (eid : EventID) (timeout : Z)
  : program UCOS2_Verify_State SemPendStart :=
  fun s result after => exists e fields,
    s.(EventState).(inUsedEventStates) eid = Some e /\ e.(semFields) = Some fields /\
    if Z.ltb 0 fields.(semCount) then
      result = SemPendAcquired /\ after = sem_count_update_state s eid e (fields.(semCount) - 1)
    else exists tid old,
      s.(SchedState).(curTaskID) = Some tid /\ s.(TskState).(inUsedTaskStates) tid = Some old /\
      result = SemPendWaiting tid old.(taskGeneration) /\
      after = event_pend_state sg s eid e tid old PendSem timeout.

Lemma sem_pend_first_critical_exists : forall sg s eid e fields timeout,
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(semFields) = Some fields ->
  (fields.(semCount) <= 0 -> exists tid old,
    s.(SchedState).(curTaskID) = Some tid /\ s.(TskState).(inUsedTaskStates) tid = Some old) ->
  exists result after, sem_pend_first_critical sg eid timeout s result after.
Proof.
  intros sg s eid e fields timeout He Hfields Hcurrent.
  destruct (Z.ltb 0 fields.(semCount)) eqn:Hcount.
  - exists SemPendAcquired, (sem_count_update_state s eid e (fields.(semCount) - 1)).
    exists e, fields; split; [exact He|]; split; [exact Hfields|]; rewrite Hcount; auto.
  - apply Z.ltb_ge in Hcount; destruct (Hcurrent Hcount) as [tid [old [Hcur Hold]]].
    exists (SemPendWaiting tid old.(taskGeneration)), (event_pend_state sg s eid e tid old PendSem timeout).
    exists e, fields; split; [exact He|]; split; [exact Hfields|].
    rewrite (proj2 (Z.ltb_ge _ _) Hcount); exists tid, old; repeat split; assumption || reflexivity.
Qed.

Lemma sem_pend_first_critical_deterministic : forall sg eid timeout s result1 after1 result2 after2,
  sem_pend_first_critical sg eid timeout s result1 after1 ->
  sem_pend_first_critical sg eid timeout s result2 after2 -> result1 = result2 /\ after1 = after2.
Proof.
  intros sg eid timeout s result1 after1 result2 after2
    [e1 [f1 [He1 [Hf1 Hstep1]]]] [e2 [f2 [He2 [Hf2 Hstep2]]]].
  assert (e2 = e1) by congruence; subst e2; assert (f2 = f1) by congruence; subst f2.
  destruct (Z.ltb 0 f1.(semCount)); [intuition congruence|].
  destruct Hstep1 as [tid1 [old1 [Hcur1 [Hold1 [-> ->]]]]].
  destruct Hstep2 as [tid2 [old2 [Hcur2 [Hold2 [-> ->]]]]].
  assert (tid2 = tid1) by congruence; subst tid2.
  assert (old2 = old1) by congruence; subst old2; auto.
Qed.

Lemma sem_pend_immediate_count_update : forall sg s eid e fields timeout after,
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(semFields) = Some fields ->
  sem_pend_first_critical sg eid timeout s SemPendAcquired after ->
  0 < fields.(semCount) /\ after = sem_count_update_state s eid e (fields.(semCount) - 1).
Proof.
  intros sg s eid e fields timeout after He Hfields [node [before [Hnode [Hbefore Hstep]]]].
  assert (node = e) by congruence; subst node; assert (before = fields) by congruence; subst before.
  destruct (Z.ltb 0 fields.(semCount)) eqn:Hcount.
  - apply Z.ltb_lt in Hcount; tauto.
  - destruct Hstep as [tid [old [_ [_ [Hresult _]]]]]; discriminate.
Qed.

Lemma sem_pend_immediate_preserves_validity : forall sg s eid e fields timeout after,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_SEM -> e.(semFields) = Some fields ->
  sem_pend_first_critical sg eid timeout s SemPendAcquired after -> UCOS2_state_inv sg after.
Proof.
  intros sg s eid e fields timeout after Hvalid He Htype Hfields Hstep.
  destruct (sem_pend_immediate_count_update sg s eid e fields timeout after He Hfields Hstep)
    as [Hpositive ->].
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  pose proof (Hpayload eid e He) as Hcount; unfold event_payload_consistency in Hcount.
  rewrite Htype, Hfields in Hcount.
  eapply UCOS2_sem_count_update_preserves_validity; try eassumption.
  apply sem_decrement_preserves_consistency; assumption.
Qed.

(** The same documented non-idle Pend obligation as Queue applies here.
    Native ready indices include idle; do not derive this restriction
    from readiness or turn it into a new source guard.  Other registration
    and caller-boundary facts are supplied by the actual invocation. *)
Lemma sem_pend_wait_preserves_validity : forall sg s eid e fields tid old timeout,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_SEM -> e.(semFields) = Some fields -> fields.(semCount) <= 0 ->
  s.(TskState).(inUsedTaskStates) tid = Some old -> old.(curPrio) <> sg.(osLowestPrio) ->
  old.(eventPtr) = None -> old.(eventMultiWaitEvents) = [] -> old.(tcbFlagNode) = 0 ->
  In tid s.(SchedState).(readyList) ->
  UCOS2_state_inv sg (event_pend_state sg s eid e tid old PendSem timeout).
Proof.
  intros sg s eid e fields tid old timeout Hvalid He Htype Hfields Hempty Hold Hnotidle Hnull Hmulti Hflag Hready.
  pose proof Hvalid as [_ [_ [Hsched [Hevents _]]]].
  destruct (proj1 (proj1 Hsched) tid Hready) as [found [Hfound [Hprio Heffective]]].
  assert (found = old) by congruence; subst found.
  assert (Hwaitprio : valid_task_prio sg old.(curPrio)).
  { unfold task_priority_in_range in Hprio; unfold valid_task_prio; lia. }
  pose proof Hevents as [_ [_ [_ [_ [Hpayload _]]]]].
  pose proof (Hpayload eid e He) as Hcount; unfold event_payload_consistency in Hcount.
  rewrite Htype, Hfields in Hcount; destruct Hcount as [Hrange Hwaiters].
  assert (Hzero : fields.(semCount) = 0) by lia.
  apply (UCOS2_event_pend_preserves_validity sg s eid e tid old PendSem timeout);
    [exact Hvalid|exact He|exact Hold|exact Hwaitprio|exact Hnull|exact Hmulti|
     exact Hflag|exact Hready| | |].
  - rewrite Htype; reflexivity.
  - unfold event_wait_resource_unavailable; rewrite Htype, Hfields; exact Hzero.
  - intros m Hmutex; congruence.
Qed.

Lemma sem_pend_first_critical_preserves_invocation : forall sg eid timeout s result after invocation origin,
  sem_pend_first_critical sg eid timeout s result after ->
  task_invocation_active s.(TskState) invocation origin ->
  task_invocation_active after.(TskState) invocation origin.
Proof.
  intros sg eid timeout s result after invocation origin [e [fields [He [Hfields Hstep]]]] Hactive.
  destruct (Z.ltb 0 fields.(semCount)).
  - destruct Hstep as [_ ->]; exact Hactive.
  - destruct Hstep as [tid [old [Hcur [Hold [_ ->]]]]].
    eapply glob_task_set_usedtask_preserves_invocation_active;
      [exact Hold|reflexivity|exact Hactive].
Qed.

(** Preserve the raw switch's default-to-timeout behavior.  Valid TCBs
    encode the three constructors, but the source discriminator also
    specifies other byte values instead of silently dropping default. *)
Definition sem_pend_resume_error (status_byte : Z) : OSErrCode :=
  if Z.eqb status_byte 0 then OS_ERR_NONE else
  if Z.eqb status_byte 2 then OS_ERR_PEND_ABORT else OS_ERR_TIMEOUT.

Lemma sem_pend_resume_error_encode : forall status,
  sem_pend_resume_error (encode_pend_status status) =
    match status with PendOK => OS_ERR_NONE | PendAbort => OS_ERR_PEND_ABORT | PendTimeout => OS_ERR_TIMEOUT end.
Proof. intros []; reflexivity. Qed.

Lemma sem_pend_resume_default_timeout : forall status,
  status <> 0 -> status <> 2 -> sem_pend_resume_error status = OS_ERR_TIMEOUT.
Proof.
  intros; unfold sem_pend_resume_error;
    rewrite (proj2 (Z.eqb_neq _ _) H), (proj2 (Z.eqb_neq _ _) H0); reflexivity.
Qed.

(** This is the original single-Event invocation's return protocol, not
    an unconditional fact about every current TCB.  Success and abort
    need no surviving Sem object; Delete may have recycled it already. *)
Definition sem_pend_resume_registration (eid : EventID) (t : TaskAbstractState) : Prop :=
  t.(eventMultiWaitEvents) = [] /\ t.(tcbFlagNode) = 0 /\
  match t.(statPend) with
  | PendTimeout => t.(eventPtr) = Some eid
  | _ => t.(eventPtr) = None
  end.

Definition sem_pend_resume_critical (sg : StableGlobVars) (eid : EventID)
  : program UCOS2_Verify_State OSErrCode :=
  fun s result after => exists tid old,
    s.(SchedState).(curTaskID) = Some tid /\ s.(TskState).(inUsedTaskStates) tid = Some old /\
    result = sem_pend_resume_error (encode_pend_status old.(statPend)) /\
    match old.(statPend) with
    | PendTimeout => exists e, s.(EventState).(inUsedEventStates) eid = Some e /\
        after = event_pend_cleanup_state sg false (event_task_remove_state s eid e tid old)
          tid (task_set_event_ptr old None)
    | _ => after = event_pend_cleanup_state sg false s tid old
    end.

Lemma sem_pend_resume_timeout_event : forall sg s eid tid old,
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  old.(eventPtr) = Some eid ->
  exists e, s.(EventState).(inUsedEventStates) eid = Some e /\ In tid e.(waitList).
Proof.
  intros sg s eid tid old Hvalid Hold Hptr; pose proof Hvalid as [_ [_ [_ [_ [Hcross _]]]]].
  eapply task_event_reference_has_waiter; eassumption.
Qed.

Lemma sem_pend_resume_critical_exists : forall sg s eid tid old,
  UCOS2_state_inv sg s -> s.(SchedState).(curTaskID) = Some tid ->
  s.(TskState).(inUsedTaskStates) tid = Some old -> sem_pend_resume_registration eid old ->
  exists result after, sem_pend_resume_critical sg eid s result after.
Proof.
  intros sg s eid tid old Hvalid Hcur Hold [_ [_ Hregistration]].
  destruct old.(statPend) eqn:Hstatus.
  - eexists _, (event_pend_cleanup_state sg false s tid old).
    exists tid, old; split; [exact Hcur|]; split; [exact Hold|]; split; [reflexivity|].
    rewrite Hstatus; reflexivity.
  - destruct (sem_pend_resume_timeout_event sg s eid tid old Hvalid Hold Hregistration) as [e [He Hin]].
    eexists _, (event_pend_cleanup_state sg false (event_task_remove_state s eid e tid old)
      tid (task_set_event_ptr old None)).
    exists tid, old; split; [exact Hcur|]; split; [exact Hold|]; split; [reflexivity|].
    rewrite Hstatus; exists e; split; reflexivity || assumption.
  - eexists _, (event_pend_cleanup_state sg false s tid old).
    exists tid, old; split; [exact Hcur|]; split; [exact Hold|]; split; [reflexivity|].
    rewrite Hstatus; reflexivity.
Qed.

Lemma sem_pend_resume_critical_preserves_validity : forall sg s eid tid old result after,
  UCOS2_state_inv sg s -> s.(SchedState).(curTaskID) = Some tid ->
  s.(TskState).(inUsedTaskStates) tid = Some old -> sem_pend_resume_registration eid old ->
  In tid s.(SchedState).(readyList) -> sem_pend_resume_critical sg eid s result after ->
  UCOS2_state_inv sg after.
Proof.
  intros sg s eid tid old result after Hvalid Hcur Hold [Hmulti [Hflag Hregistration]] Hready
    [current [t [Hcurrent [Ht [_ Hstep]]]]].
  assert (current = tid) by congruence; subst current; assert (t = old) by congruence; subst t.
  destruct old.(statPend) eqn:Hstatus.
  - subst after; eapply UCOS2_event_pend_cleanup_preserves_validity; eauto.
  - destruct Hstep as [e [He ->]].
    destruct (sem_pend_resume_timeout_event sg s eid tid old Hvalid Hold Hregistration) as [node [Hnode Hin]].
    assert (node = e) by congruence; subst node.
    eapply UCOS2_event_pend_cleanup_preserves_validity.
    + eapply UCOS2_event_task_remove_preserves_validity; eauto.
    + cbn [event_task_remove_state replace_TskS replace_EventS TskState
        glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
    + reflexivity.
    + exact Hmulti.
    + exact Hflag.
    + exact Hready.
  - subst after; eapply UCOS2_event_pend_cleanup_preserves_validity; eauto.
Qed.

Lemma sem_pend_resume_critical_deterministic : forall sg eid s result1 after1 result2 after2,
  sem_pend_resume_critical sg eid s result1 after1 -> sem_pend_resume_critical sg eid s result2 after2 ->
  result1 = result2 /\ after1 = after2.
Proof.
  intros sg eid s result1 after1 result2 after2
    [tid1 [old1 [Hcur1 [Hold1 [Hr1 Hstep1]]]]]
    [tid2 [old2 [Hcur2 [Hold2 [Hr2 Hstep2]]]]].
  assert (tid2 = tid1) by congruence; subst tid2; assert (old2 = old1) by congruence; subst old2.
  split; [congruence|]; destruct old1.(statPend); try congruence.
  destruct Hstep1 as [e1 [He1 ->]], Hstep2 as [e2 [He2 ->]].
  assert (e2 = e1) by congruence; subst e2; reflexivity.
Qed.

Lemma sem_pend_resume_without_timeout_preserves_event : forall sg eid s tid old result after,
  s.(SchedState).(curTaskID) = Some tid -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  old.(statPend) <> PendTimeout -> sem_pend_resume_critical sg eid s result after ->
  after.(EventState) = s.(EventState).
Proof.
  intros sg eid s tid old result after Hcur Hold Hnotimeout [current [t [Hcurrent [Ht [_ Hstep]]]]].
  assert (current = tid) by congruence; subst current; assert (t = old) by congruence; subst t.
  destruct old.(statPend); [subst after|contradiction|subst after]; reflexivity.
Qed.

(** Complete TCB endpoint, including the important Msg/Dly frame.  The
    timeout Remove clears EventPtr first; the caller's repeated NULL
    assignment has the same final value, not a second Event removal. *)
Lemma sem_pend_resume_critical_task_update : forall sg eid s tid old result after,
  s.(SchedState).(curTaskID) = Some tid -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_resume_critical sg eid s result after ->
  after.(TskState) = glob_task_set_usedtask s.(TskState) tid
    (task_event_pend_cleanup sg.(osKernelConfig).(cfgEventMultiEnabled) false old) /\
  after.(SchedState) = s.(SchedState).
Proof.
  intros sg eid s tid old result after Hcur Hold [current [t [Hcurrent [Ht [_ Hstep]]]]].
  assert (current = tid) by congruence; subst current; assert (t = old) by congruence; subst t.
  destruct old.(statPend).
  - subst after; split; reflexivity.
  - destruct Hstep as [e [_ ->]]; split; [|reflexivity].
    unfold event_pend_cleanup_state, event_task_remove_state; cbn [replace_TskS replace_EventS TskState].
    unfold glob_task_set_usedtask; simpl; f_equal.
    apply functional_extensionality; intro slot; destruct (Z.eqb slot tid); [|reflexivity].
    destruct sg.(osKernelConfig).(cfgEventMultiEnabled); reflexivity.
  - subst after; split; reflexivity.
Qed.

Lemma sem_pend_resume_preserves_message_delay : forall sg eid s tid old result after,
  s.(SchedState).(curTaskID) = Some tid -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_resume_critical sg eid s result after ->
  exists current, after.(TskState).(inUsedTaskStates) tid = Some current /\
    current.(msg) = old.(msg) /\ current.(dly) = old.(dly).
Proof.
  intros sg eid s tid old result after Hcur Hold Hstep.
  rewrite (proj1 (sem_pend_resume_critical_task_update sg eid s tid old result after Hcur Hold Hstep)).
  eexists; split; [simpl; rewrite Z.eqb_refl; reflexivity|].
  destruct sg.(osKernelConfig).(cfgEventMultiEnabled); split; reflexivity.
Qed.

Lemma sem_pend_resume_critical_preserves_invocation : forall sg eid s tid old result after invocation origin,
  s.(SchedState).(curTaskID) = Some tid -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_resume_critical sg eid s result after ->
  task_invocation_active s.(TskState) invocation origin ->
  task_invocation_active after.(TskState) invocation origin.
Proof.
  intros sg eid s tid old result after invocation origin Hcur Hold Hstep Hactive.
  rewrite (proj1 (sem_pend_resume_critical_task_update sg eid s tid old result after Hcur Hold Hstep)).
  eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hold| |exact Hactive].
  destruct sg.(osKernelConfig).(cfgEventMultiEnabled); reflexivity.
Qed.

(** A returned scheduler boundary and active original invocation are
    inputs supplied by the call protocol.  This theorem cannot prove that
    a blocked task eventually resumes, nor equate a reused slot with the
    original task generation. *)
Lemma sem_pend_resume_from_task_boundary_preserves_validity :
  forall sg eid s tid old result after invocation generation,
  UCOS2_state_inv sg s -> s.(SchedState).(curTaskID) = Some tid ->
  s.(TskState).(inUsedTaskStates) tid = Some old -> sem_pend_resume_registration eid old ->
  sched_task_call_boundary s.(TskState) s.(SchedState) ->
  task_invocation_active s.(TskState) invocation (RunningInvocation tid generation) ->
  sem_pend_resume_critical sg eid s result after ->
  UCOS2_state_inv sg after /\
  task_invocation_active after.(TskState) invocation (RunningInvocation tid generation).
Proof.
  intros sg eid s tid old result after invocation generation Hvalid Hcur Hold Hregistration
    [Hrunning [selected [t [Ht [Hselected [Hpriority [Hready Heffective]]]]]]] Hactive Hstep.
  assert (selected = tid) by congruence; subst selected; split.
  - exact (sem_pend_resume_critical_preserves_validity
      sg s eid tid old result after Hvalid Hcur Hold Hregistration Hready Hstep).
  - exact (sem_pend_resume_critical_preserves_invocation
      sg eid s tid old result after invocation (RunningInvocation tid generation) Hcur Hold Hstep Hactive).
Qed.

Lemma sem_pend_resume_critical_preserves_residual : forall sg eid s result after,
  sem_pend_resume_critical sg eid s result after ->
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |-- UCOS2_raw_rep_missing_task_storage_sched_event sg after.
Proof.
  intros sg eid s result after [tid [old [Hcur [Hold [_ Hstep]]]]].
  destruct old.(statPend).
  - subst after; apply UCOS2_event_pend_cleanup_preserves_residual.
  - destruct Hstep as [e [He ->]].
    eapply derivable1_trans; [apply UCOS2_event_task_remove_preserves_residual; exact He|].
    apply UCOS2_event_pend_cleanup_preserves_residual.
  - subst after; apply UCOS2_event_pend_cleanup_preserves_residual.
Qed.

(** Actual written TCB/ECB resources are inputs, not consequences of a
    pure state transformer.  The unchanged Scheduler heap and old Event
    encoding index are transported by the proved priority frame. *)
Lemma sem_pend_resume_critical_merge_resources : forall sg eid s tid old result after,
  UCOS2_state_inv sg s -> s.(SchedState).(curTaskID) = Some tid ->
  s.(TskState).(inUsedTaskStates) tid = Some old -> sem_pend_resume_registration eid old ->
  In tid s.(SchedState).(readyList) -> sem_pend_resume_critical sg eid s result after ->
  task_public_storage sg after.(TskState) **
  sched_raw_rep sg s.(TskState) s.(SchedState) **
  event_raw_rep sg s.(TskState) after.(EventState) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |-- UCOS2_inv sg after.
Proof.
  intros sg eid s tid old result after Hvalid Hcur Hold Hregistration Hready Hstep.
  pose proof (sem_pend_resume_critical_preserves_validity
    sg s eid tid old result after Hvalid Hcur Hold Hregistration Hready Hstep) as Hpost.
  destruct (sem_pend_resume_critical_task_update sg eid s tid old result after Hcur Hold Hstep)
    as [Htasks Hsched].
  assert (Hevent : event_raw_rep sg s.(TskState) after.(EventState) =
    event_raw_rep sg after.(TskState) after.(EventState)).
  { apply event_raw_rep_change_task_index; apply event_wait_priority_agreement_encodes.
    rewrite Htasks; eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hold|].
    destruct sg.(osKernelConfig).(cfgEventMultiEnabled); reflexivity. }
  assert (Hschedrep : sched_raw_rep sg s.(TskState) s.(SchedState) =
    sched_raw_rep sg after.(TskState) after.(SchedState)).
  { rewrite Hsched, Htasks; apply sched_raw_rep_priority_ext; intros slot Hin.
    cbn [glob_task_set_usedtask inUsedTaskStates].
    destruct (Z.eqb slot tid) eqn:E; [|reflexivity].
    apply Z.eqb_eq in E; subst slot; rewrite Hold.
    destruct sg.(osKernelConfig).(cfgEventMultiEnabled); reflexivity. }
  rewrite Hevent, Hschedrep.
  sep_apply_l_atomic (sem_pend_resume_critical_preserves_residual sg eid s result after Hstep).
  unfold UCOS2_inv, UCOS2_raw_rep, task_shared_rep,
    UCOS2_raw_rep_missing_task_storage_sched, UCOS2_raw_rep_missing_task_storage_sched_event; entailer!.
Qed.
