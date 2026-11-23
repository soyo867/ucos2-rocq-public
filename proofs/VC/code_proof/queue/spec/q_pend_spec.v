Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSQPend, V2.93.01 os_q.c:436--539.  Observations before the first
    Save, the first critical section, and the returning critical section
    are separate.  They are not collapsed into an atomic whole API.
    Trace/platform/scheduler-return composition must bind the actual call
    instance and its storage.  A saved TCB slot alone does not establish
    that the same generation or invocation has resumed. *)
Definition q_pend_safety_exception_requested (sg : StableGlobVars) (perr : addr) : bool :=
  (sg.(osKernelConfig).(cfgSafetyCritical) && Z.eqb perr 0)%bool.

Definition q_pend_argument_error (sg : StableGlobVars) (pevent : addr) : option OSErrCode :=
  if (sg.(osKernelConfig).(cfgArgumentChecks) && Z.eqb pevent 0)%bool
  then Some OS_ERR_PEVENT_NULL else None.

(** Called after the ENTER trace and argument check.  Each argument is a
    source-time observation; this does not assert that the unmasked reads
    all see one unchanged global snapshot.  The safety-exception branch
    calls its external hook and, if it returns, returns NULL without
    writing perr; it does not flow through this discriminator. *)
Definition q_pend_context_error (type_byte int_nesting lock_nesting : Z) : option OSErrCode :=
  if negb (Z.eqb type_byte (encode_event_type OS_EVENT_TYPE_Q)) then Some OS_ERR_EVENT_TYPE else
  if Z.ltb 0 int_nesting then Some OS_ERR_PEND_ISR else
  if Z.ltb 0 lock_nesting then Some OS_ERR_PEND_LOCKED else None.

Lemma q_pend_context_error_type_first : forall ty nesting locked,
  ty <> 2 -> q_pend_context_error ty nesting locked = Some OS_ERR_EVENT_TYPE.
Proof.
  intros; unfold q_pend_context_error; cbn [encode_event_type].
  rewrite (proj2 (Z.eqb_neq _ _) H); reflexivity.
Qed.

Lemma q_pend_context_error_isr_before_lock : forall nesting locked,
  0 < nesting -> q_pend_context_error 2 nesting locked = Some OS_ERR_PEND_ISR.
Proof.
  intros nesting locked H.
  change ((if Z.ltb 0 nesting then Some OS_ERR_PEND_ISR else
    if Z.ltb 0 locked then Some OS_ERR_PEND_LOCKED else None) = Some OS_ERR_PEND_ISR).
  rewrite (proj2 (Z.ltb_lt _ _) H); reflexivity.
Qed.

(** A phase result, not the public pointer return.  The waiting branch
    records the actual TCB generation for the later continuation proof. *)
Inductive QueuePendStart : Type :=
| QueuePendImmediate (message : addr)
| QueuePendWaiting (tid : TaskID) (generation : nat).

Definition q_pend_first_critical (sg : StableGlobVars) (eid : EventID) (timeout : Z)
  : program UCOS2_Verify_State QueuePendStart :=
  fun s result after => exists e q,
    s.(EventState).(inUsedEventStates) eid = Some e /\ e.(queueFields) = Some q /\
    if Z.ltb 0 (queue_entries q) then
      exists message next slots,
        queue_dequeue_front q = Some (message, next) /\
        s.(EventState).(publishedQueueBytes) q.(qID) = Some slots /\
        result = QueuePendImmediate message /\
        after = replace_EventS (queue_update s.(EventState) eid e next slots) s
    else exists tid old,
      s.(SchedState).(curTaskID) = Some tid /\ s.(TskState).(inUsedTaskStates) tid = Some old /\
      result = QueuePendWaiting tid old.(taskGeneration) /\
      after = event_pend_state sg s eid e tid old PendQ timeout.

Lemma q_pend_first_critical_exists : forall sg s eid e q timeout,
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(queueFields) = Some q ->
  queue_published_storage_binding s.(EventState) ->
  (queue_entries q <= 0 -> exists tid old,
    s.(SchedState).(curTaskID) = Some tid /\ s.(TskState).(inUsedTaskStates) tid = Some old) ->
  exists result after, q_pend_first_critical sg eid timeout s result after.
Proof.
  intros sg s eid e q timeout He Hq Hbinding Hcurrent.
  destruct (Z.ltb 0 (queue_entries q)) eqn:Hcount.
  - destruct (proj1 Hbinding eid e q He Hq) as [_ [slots [Hslots Hmodel]]].
    assert (Hdequeue : exists message next, queue_dequeue_front q = Some (message, next)).
    { unfold queue_dequeue_front; destruct q.(qMessages) as [|message rest] eqn:Hmessages; [|eauto].
      unfold queue_entries in Hcount; rewrite Hmessages, Zlength_nil in Hcount; discriminate. }
    destruct Hdequeue as [message [next Hnext]].
    exists (QueuePendImmediate message), (replace_EventS (queue_update s.(EventState) eid e next slots) s).
    exists e, q; split; [exact He|]; split; [exact Hq|]; rewrite Hcount.
    exists message, next, slots; repeat split; assumption || reflexivity.
  - apply Z.ltb_ge in Hcount; destruct (Hcurrent Hcount) as [tid [old [Hcur Hold]]].
    exists (QueuePendWaiting tid old.(taskGeneration)), (event_pend_state sg s eid e tid old PendQ timeout).
    exists e, q; split; [exact He|]; split; [exact Hq|].
    rewrite (proj2 (Z.ltb_ge _ _) Hcount); exists tid, old; repeat split; assumption || reflexivity.
Qed.

Lemma q_pend_dequeue_preserves_validity : forall sg s eid e q message next slots,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_Q -> e.(queueFields) = Some q ->
  queue_dequeue_front q = Some (message, next) ->
  UCOS2_state_inv sg
    (replace_EventS (queue_update s.(EventState) eid e next slots) s).
Proof. intros; eapply UCOS2_queue_dequeue_preserves_validity; eassumption. Qed.

Lemma q_pend_first_critical_deterministic : forall sg eid timeout s result1 after1 result2 after2,
  q_pend_first_critical sg eid timeout s result1 after1 ->
  q_pend_first_critical sg eid timeout s result2 after2 ->
  result1 = result2 /\ after1 = after2.
Proof.
  intros sg eid timeout s result1 after1 result2 after2
    [e1 [q1 [He1 [Hq1 Hstep1]]]] [e2 [q2 [He2 [Hq2 Hstep2]]]].
  assert (e2 = e1) by congruence; subst e2.
  assert (q2 = q1) by congruence; subst q2.
  destruct (Z.ltb 0 (queue_entries q1)).
  - destruct Hstep1 as [m1 [next1 [slots1 [Hnext1 [Hslots1 [-> ->]]]]]].
    destruct Hstep2 as [m2 [next2 [slots2 [Hnext2 [Hslots2 [-> ->]]]]]].
    assert (m2 = m1 /\ next2 = next1) as [-> ->] by (split; congruence).
    assert (slots2 = slots1) by congruence; subst slots2; auto.
  - destruct Hstep1 as [tid1 [old1 [Hcur1 [Hold1 [-> ->]]]]].
    destruct Hstep2 as [tid2 [old2 [Hcur2 [Hold2 [-> ->]]]]].
    assert (tid2 = tid1) by congruence; subst tid2.
    assert (old2 = old1) by congruence; subst old2; auto.
Qed.

Lemma q_pend_first_critical_preserves_invocation : forall sg eid timeout s result after invocation origin,
  q_pend_first_critical sg eid timeout s result after ->
  task_invocation_active s.(TskState) invocation origin ->
  task_invocation_active after.(TskState) invocation origin.
Proof.
  intros sg eid timeout s result after invocation origin
    [e [q [He [Hq Hstep]]]] Hactive.
  destruct (Z.ltb 0 (queue_entries q)).
  - destruct Hstep as [message [next [slots [_ [_ [_ ->]]]]]]; exact Hactive.
  - destruct Hstep as [tid [old [Hcur [Hold [_ ->]]]]].
    eapply glob_task_set_usedtask_preserves_invocation_active;
      [exact Hold|reflexivity|exact Hactive].
Qed.

Lemma q_pend_immediate_reads_head_slot : forall sg s eid e q timeout message after,
  UCOS2_state_inv sg s -> queue_published_storage_binding s.(EventState) ->
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(eventType) = OS_EVENT_TYPE_Q ->
  e.(queueFields) = Some q ->
  q_pend_first_critical sg eid timeout s (QueuePendImmediate message) after ->
  exists slots,
    s.(EventState).(publishedQueueBytes) q.(qID) = Some slots /\
    Znth q.(qOutIndex) slots None = Some message /\
    after.(EventState).(publishedQueueBytes) = s.(EventState).(publishedQueueBytes).
Proof.
  intros sg s eid e q timeout message after Hvalid Hbinding He Htype Hq
    [node [before [Hnode [Hbefore Hstep]]]].
  assert (node = e) by congruence; subst node.
  assert (before = q) by congruence; subst before.
  destruct (Z.ltb 0 (queue_entries q)).
  - destruct Hstep as [actual [next [slots [Hnext [Hslots [Hmessage ->]]]]]].
    injection Hmessage as Hmessage; subst actual.
    pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
    pose proof (Hpayload eid e He) as Hqueue; unfold event_payload_consistency in Hqueue.
    rewrite Htype, Hq in Hqueue.
    destruct (proj1 Hbinding eid e q He Hq) as [_ [bytes [Hbytes Hmodel]]].
    assert (bytes = slots) by congruence; subst bytes.
    exists slots; split; [exact Hslots|]; split.
    + eapply queue_dequeue_front_head_slot; eauto.
    + apply queue_update_preserves_published_bytes.
      rewrite (queue_dequeue_front_queue_id_eq q message next Hnext); exact Hslots.
  - destruct Hstep as [tid [old [_ [_ [Hresult _]]]]]; discriminate.
Qed.

(** Micrium's documented idle-task protocol excludes Pend calls from
    OSTaskIdleHook (uC/OS-II, 2nd ed., section 3.08, printed p. 98).
    Native ready-table indices INCLUDE idle, so readiness alone cannot
    supply the non-idle wait domain.  Keep that caller obligation explicit;
    do not insert it into the source transformer as a new runtime guard.
    The immediate-dequeue theorem above does not need this condition. *)
Lemma q_pend_wait_preserves_validity : forall sg s eid e q tid old timeout,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_Q -> e.(queueFields) = Some q -> queue_entries q <= 0 ->
  s.(TskState).(inUsedTaskStates) tid = Some old -> old.(curPrio) <> sg.(osLowestPrio) ->
  old.(eventPtr) = None -> old.(eventMultiWaitEvents) = [] -> old.(tcbFlagNode) = 0 ->
  In tid s.(SchedState).(readyList) ->
  UCOS2_state_inv sg (event_pend_state sg s eid e tid old PendQ timeout).
Proof.
  intros sg s eid e q tid old timeout Hvalid He Htype Hq Hempty Hold Hnotidle Hnull Hmulti Hflag Hready.
  pose proof Hvalid as [_ [_ [Hsched _]]].
  destruct (proj1 (proj1 Hsched) tid Hready) as [found [Hfound [Hprio Heffective]]].
  assert (found = old) by congruence; subst found.
  assert (Hwaitprio : valid_task_prio sg old.(curPrio)).
  { unfold task_priority_in_range in Hprio; unfold valid_task_prio; lia. }
  apply (UCOS2_event_pend_preserves_validity sg s eid e tid old PendQ timeout);
    [exact Hvalid|exact He|exact Hold|exact Hwaitprio|exact Hnull|exact Hmulti|
     exact Hflag|exact Hready| | |].
  - rewrite Htype; reflexivity.
  - unfold event_wait_resource_unavailable; rewrite Htype, Hq.
    destruct q.(qMessages) as [|message rest] eqn:Hmessages; [reflexivity|].
    unfold queue_entries in Hempty; rewrite Hmessages, Zlength_cons in Hempty.
    pose proof (Zlength_nonneg rest); lia.
  - intros m Hmutex; congruence.
Qed.

Lemma q_pend_dequeue_merge_global : forall sg s eid e q message next slots free,
  UCOS2_state_inv sg s -> queue_published_storage_binding s.(EventState) ->
  queue_pool_partition sg s.(EventState) free ->
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(eventType) = OS_EVENT_TYPE_Q ->
  e.(queueFields) = Some q -> queue_slots_model q slots ->
  queue_dequeue_front q = Some (message, next) ->
  (event_raw_rep sg s.(TskState) s.(EventState) **
    (store_map_missing_i (published_queue_node_rep sg s.(EventState))
       s.(EventState).(inUsedEventStates) eid **
      ((used_queue_control_block sg next ** PtrArray.mixed_full next.(qStart) next.(qSize) slots) **
        store_free_queue_list sg free))) ** UCOS2_raw_rep_missing_event_queue sg s |--
  UCOS2_inv sg (replace_EventS (queue_update s.(EventState) eid e next slots) s).
Proof. intros; eapply UCOS2_inv_merge_queue_dequeue; eassumption. Qed.

(** The source switch has a real default-to-timeout branch.  Canonical
    TCBs encode one of three PendStatus values, but the raw discriminator
    retains that default instead of silently dropping it. *)
Definition q_pend_resume_branch (status_byte : Z) : PendStatus :=
  if Z.eqb status_byte 0 then PendOK else if Z.eqb status_byte 2 then PendAbort else PendTimeout.

Definition q_pend_resume_observation (status_byte message : Z) : addr * OSErrCode :=
  match q_pend_resume_branch status_byte with
  | PendOK => (message, OS_ERR_NONE)
  | PendAbort => (0, OS_ERR_PEND_ABORT)
  | PendTimeout => (0, OS_ERR_TIMEOUT)
  end.

Lemma q_pend_resume_branch_encode : forall status,
  q_pend_resume_branch (encode_pend_status status) = status.
Proof. intros []; reflexivity. Qed.

Lemma q_pend_resume_default_timeout : forall status message,
  status <> 0 -> status <> 2 -> q_pend_resume_observation status message = (0, OS_ERR_TIMEOUT).
Proof.
  intros; unfold q_pend_resume_observation, q_pend_resume_branch.
  rewrite (proj2 (Z.eqb_neq _ _) H), (proj2 (Z.eqb_neq _ _) H0); reflexivity.
Qed.

Lemma q_pend_resume_null_results_distinct :
  q_pend_resume_observation 0 0 = (0, OS_ERR_NONE) /\
  q_pend_resume_observation 1 0 = (0, OS_ERR_TIMEOUT) /\
  q_pend_resume_observation 2 0 = (0, OS_ERR_PEND_ABORT).
Proof. repeat split; reflexivity. Qed.

(** This is a RETURNED invocation checkpoint, not a new runtime check and
    not a theorem that the scheduler returns.  Its readiness and original
    generation must come from the actual context-switch/call protocol. *)
Definition q_pend_returning_invocation (s : UCOS2_Verify_State)
  (invocation : nat) (tid : TaskID) (generation : nat) : Prop :=
  task_invocation_active s.(TskState) invocation (RunningInvocation tid generation) /\
  s.(SchedState).(curTaskID) = Some tid /\ In tid s.(SchedState).(readyList).

Lemma q_pend_returning_invocation_of_task_boundary : forall s invocation tid generation,
  task_invocation_active s.(TskState) invocation (RunningInvocation tid generation) ->
  s.(SchedState).(curTaskID) = Some tid -> sched_task_call_boundary s.(TskState) s.(SchedState) ->
  q_pend_returning_invocation s invocation tid generation.
Proof.
  intros s invocation tid generation Hactive Hcur [Hrunning [selected [t Hboundary]]].
  destruct Hboundary as [Ht [Hselected [Hpriority [Hready Heffective]]]].
  assert (selected = tid) by congruence; subst selected.
  split; [exact Hactive|]; split; assumption.
Qed.

Lemma q_pend_returning_invocation_current_generation : forall s invocation tid generation current old,
  q_pend_returning_invocation s invocation tid generation ->
  s.(SchedState).(curTaskID) = Some current -> s.(TskState).(inUsedTaskStates) current = Some old ->
  current = tid /\ old.(taskGeneration) = generation.
Proof.
  intros s invocation tid generation current old [[Hinv [Hactive [original [Horiginal Hg]]]] [Hcur Hready]]
    Hcurrent Hold.
  assert (current = tid) by congruence; subst current.
  assert (old = original) by congruence; subst old; auto.
Qed.

(** Resume registration protocol for this original single-Event wait.
    A timeout keeps its EventPtr until Remove.  Posted/aborted returns do
    not dereference pevent, so they do NOT require the Queue still to exist.
    For example, Delete(ALWAYS) can abort then recycle the Queue first. *)
Definition q_pend_resume_registration (eid : EventID) (t : TaskAbstractState) : Prop :=
  t.(eventMultiWaitEvents) = [] /\ t.(tcbFlagNode) = 0 /\
  match t.(statPend) with
  | PendTimeout => t.(eventPtr) = Some eid
  | _ => t.(eventPtr) = None
  end.

Definition q_pend_resume_critical (sg : StableGlobVars) (eid : EventID)
  : program UCOS2_Verify_State (addr * OSErrCode) :=
  fun s result after => exists tid old,
    s.(SchedState).(curTaskID) = Some tid /\ s.(TskState).(inUsedTaskStates) tid = Some old /\
    result = q_pend_resume_observation (encode_pend_status old.(statPend)) (encode_msg old.(msg)) /\
    match old.(statPend) with
    | PendTimeout => exists e, s.(EventState).(inUsedEventStates) eid = Some e /\
        after = message_pend_cleanup_state sg (event_task_remove_state s eid e tid old)
          tid (task_set_event_ptr old None)
    | _ => after = message_pend_cleanup_state sg s tid old
    end.

Lemma q_pend_resume_timeout_event : forall sg s eid tid old,
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  old.(eventPtr) = Some eid ->
  exists e, s.(EventState).(inUsedEventStates) eid = Some e /\ In tid e.(waitList).
Proof.
  intros sg s eid tid old Hvalid Hold Hptr.
  pose proof Hvalid as [_ [_ [_ [_ [Hcross _]]]]].
  eapply task_event_reference_has_waiter; eassumption.
Qed.

Lemma q_pend_resume_critical_exists : forall sg s eid tid old,
  UCOS2_state_inv sg s -> s.(SchedState).(curTaskID) = Some tid ->
  s.(TskState).(inUsedTaskStates) tid = Some old -> q_pend_resume_registration eid old ->
  exists result after, q_pend_resume_critical sg eid s result after.
Proof.
  intros sg s eid tid old Hvalid Hcur Hold [_ [_ Hregistration]].
  destruct old.(statPend) eqn:Hstatus.
  - eexists _, (message_pend_cleanup_state sg s tid old).
    exists tid, old; split; [exact Hcur|]; split; [exact Hold|]; split; [reflexivity|].
    rewrite Hstatus; reflexivity.
  - destruct (q_pend_resume_timeout_event sg s eid tid old Hvalid Hold Hregistration) as [e [He Hin]].
    eexists _, (message_pend_cleanup_state sg (event_task_remove_state s eid e tid old)
      tid (task_set_event_ptr old None)).
    exists tid, old; split; [exact Hcur|]; split; [exact Hold|]; split; [reflexivity|].
    rewrite Hstatus; exists e; split; reflexivity || assumption.
  - eexists _, (message_pend_cleanup_state sg s tid old).
    exists tid, old; split; [exact Hcur|]; split; [exact Hold|]; split; [reflexivity|].
    rewrite Hstatus; reflexivity.
Qed.

Lemma q_pend_resume_critical_preserves_validity : forall sg s eid tid old result after,
  UCOS2_state_inv sg s -> s.(SchedState).(curTaskID) = Some tid ->
  s.(TskState).(inUsedTaskStates) tid = Some old -> q_pend_resume_registration eid old ->
  In tid s.(SchedState).(readyList) -> q_pend_resume_critical sg eid s result after ->
  UCOS2_state_inv sg after.
Proof.
  intros sg s eid tid old result after Hvalid Hcur Hold [Hmulti [Hflag Hregistration]] Hready
    [current [t [Hcurrent [Ht [_ Hstep]]]]].
  assert (current = tid) by congruence; subst current.
  assert (t = old) by congruence; subst t.
  destruct old.(statPend) eqn:Hstatus.
  - subst after; eapply UCOS2_message_pend_cleanup_preserves_validity; eauto.
  - destruct Hstep as [e [He ->]].
    destruct (q_pend_resume_timeout_event sg s eid tid old Hvalid Hold Hregistration) as [node [Hnode Hin]].
    assert (node = e) by congruence; subst node.
    eapply UCOS2_message_pend_cleanup_preserves_validity.
    + eapply UCOS2_event_task_remove_preserves_validity; eauto.
    + cbn [event_task_remove_state replace_TskS replace_EventS TskState
        glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
    + reflexivity.
    + exact Hmulti.
    + exact Hflag.
    + exact Hready.
  - subst after; eapply UCOS2_message_pend_cleanup_preserves_validity; eauto.
Qed.

Lemma q_pend_resume_critical_deterministic : forall sg eid s result1 after1 result2 after2,
  q_pend_resume_critical sg eid s result1 after1 ->
  q_pend_resume_critical sg eid s result2 after2 ->
  result1 = result2 /\ after1 = after2.
Proof.
  intros sg eid s result1 after1 result2 after2
    [tid1 [old1 [Hcur1 [Hold1 [Hr1 Hstep1]]]]]
    [tid2 [old2 [Hcur2 [Hold2 [Hr2 Hstep2]]]]].
  assert (tid2 = tid1) by congruence; subst tid2.
  assert (old2 = old1) by congruence; subst old2.
  split; [congruence|].
  destruct old1.(statPend); try congruence.
  destruct Hstep1 as [e1 [He1 ->]], Hstep2 as [e2 [He2 ->]].
  assert (e2 = e1) by congruence; subst e2; reflexivity.
Qed.

Lemma q_pend_resume_without_timeout_preserves_event : forall sg eid s tid old result after,
  s.(SchedState).(curTaskID) = Some tid -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  old.(statPend) <> PendTimeout -> q_pend_resume_critical sg eid s result after ->
  after.(EventState) = s.(EventState).
Proof.
  intros sg eid s tid old result after Hcur Hold Hnotimeout
    [current [t [Hcurrent [Ht [_ Hstep]]]]].
  assert (current = tid) by congruence; subst current.
  assert (t = old) by congruence; subst t.
  destruct old.(statPend); [subst after|contradiction|subst after]; reflexivity.
Qed.

(** The resumed critical section changes only its selected TCB and, on
    timeout, its old wait bitmap.  In particular it does not write delay,
    priority or scheduler caches/ready bits.  This theorem identifies the
    complete resulting TCB, rather than only projecting the reset fields. *)
Lemma q_pend_resume_critical_task_update : forall sg eid s tid old result after,
  s.(SchedState).(curTaskID) = Some tid -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  q_pend_resume_critical sg eid s result after ->
  after.(TskState) = glob_task_set_usedtask s.(TskState) tid
    (task_message_pend_cleanup sg.(osKernelConfig).(cfgEventMultiEnabled) old) /\
  after.(SchedState) = s.(SchedState).
Proof.
  intros sg eid s tid old result after Hcur Hold
    [current [t [Hcurrent [Ht [_ Hstep]]]]].
  assert (current = tid) by congruence; subst current.
  assert (t = old) by congruence; subst t.
  destruct old.(statPend).
  - subst after; split; reflexivity.
  - destruct Hstep as [e [_ ->]].
    split; [|reflexivity].
    unfold message_pend_cleanup_state, event_pend_cleanup_state, event_task_remove_state;
      cbn [replace_TskS replace_EventS TskState].
    unfold glob_task_set_usedtask; simpl; f_equal.
    apply functional_extensionality; intro slot.
    destruct (Z.eqb slot tid); [|reflexivity].
    destruct sg.(osKernelConfig).(cfgEventMultiEnabled); reflexivity.
  - subst after; split; reflexivity.
Qed.

Lemma q_pend_resume_critical_preserves_invocation : forall sg eid s tid old result after invocation origin,
  s.(SchedState).(curTaskID) = Some tid -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  q_pend_resume_critical sg eid s result after ->
  task_invocation_active s.(TskState) invocation origin ->
  task_invocation_active after.(TskState) invocation origin.
Proof.
  intros sg eid s tid old result after invocation origin Hcur Hold Hstep Hactive.
  rewrite (proj1 (q_pend_resume_critical_task_update sg eid s tid old result after Hcur Hold Hstep)).
  eapply glob_task_set_usedtask_preserves_invocation_active;
    [exact Hold| |exact Hactive].
  destruct sg.(osKernelConfig).(cfgEventMultiEnabled); reflexivity.
Qed.

Lemma q_pend_resume_critical_preserves_returning_invocation :
  forall sg eid s result after invocation tid generation,
  q_pend_returning_invocation s invocation tid generation ->
  q_pend_resume_critical sg eid s result after ->
  q_pend_returning_invocation after invocation tid generation.
Proof.
  intros sg eid s result after invocation tid generation
    [Hactive [Hcur Hready]] Hstep.
  pose proof Hstep as [current [old [Hcurrent [Hold _]]]].
  assert (current = tid) by congruence; subst current.
  pose proof (proj2 (q_pend_resume_critical_task_update
    sg eid s tid old result after Hcur Hold Hstep)) as Hsched.
  split.
  - eapply q_pend_resume_critical_preserves_invocation; eauto.
  - rewrite Hsched; auto.
Qed.
