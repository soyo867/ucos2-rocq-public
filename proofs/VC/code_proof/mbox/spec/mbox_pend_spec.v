Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Export Ucos2Verify.VC.code.mbox.spec.mbox_accept_spec.
Require Export Ucos2Verify.VC.code.mbox.spec.mbox_pend_sched_spec.
Require Export Ucos2Verify.VC.code.queue.spec.q_pend_api_spec.
Require Export Ucos2Verify.VC.code.queue.spec.q_pend_proof_helpers.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_retirement Ucos2Verify.lib.tick.
Require Import Ucos2Verify.VC.code.event.spec.event_task_wait_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_remove_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_sched_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_entry_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_entry_return_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_idle_protocol_spec.
Require Import Ucos2Verify.lib.kernel_runtime_inv.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.

Import ListNotations UCOS2_C_Rules Monad MonadNotation TaskStateDef.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** OSMboxPend, pinned V2.93.01 Source/os_mbox.c:317--404.
    This candidate composes the delivered Mailbox Scheduler with source semantics
    and independently proved resource consequences.
    The four-field returning critical section and the modular call HISTORY below
    are the existing type-independent message/continuation interfaces, not the
    PendQ-specific first section or Scheduler pre/post. *)

Definition mbox_pend_precritical_error (pevent type_byte int_nesting lock_nesting : Z)
  : option OSErrCode :=
  if Z.eqb pevent 0 then Some OS_ERR_PEVENT_NULL else
  if negb (Z.eqb type_byte 1) then Some OS_ERR_EVENT_TYPE else
  if Z.ltb 0 int_nesting then Some OS_ERR_PEND_ISR else
  if Z.ltb 0 lock_nesting then Some OS_ERR_PEND_LOCKED else None.

Lemma mbox_pend_precritical_null : forall ty nesting locked,
  mbox_pend_precritical_error 0 ty nesting locked = Some OS_ERR_PEVENT_NULL.
Proof. reflexivity. Qed.

Lemma mbox_pend_precritical_type : forall pe ty nesting locked,
  pe <> 0 -> ty <> 1 ->
  mbox_pend_precritical_error pe ty nesting locked = Some OS_ERR_EVENT_TYPE.
Proof.
  intros; unfold mbox_pend_precritical_error.
  rewrite (proj2 (Z.eqb_neq _ _) H), (proj2 (Z.eqb_neq _ _) H0); reflexivity.
Qed.

Lemma mbox_pend_precritical_isr : forall pe nesting locked,
  pe <> 0 -> 0 < nesting ->
  mbox_pend_precritical_error pe 1 nesting locked = Some OS_ERR_PEND_ISR.
Proof.
  intros; unfold mbox_pend_precritical_error.
  rewrite (proj2 (Z.eqb_neq _ _) H), (proj2 (Z.ltb_lt _ _) H0); reflexivity.
Qed.

Lemma mbox_pend_precritical_locked : forall pe locked,
  pe <> 0 -> 0 < locked ->
  mbox_pend_precritical_error pe 1 0 locked = Some OS_ERR_PEND_LOCKED.
Proof.
  intros; unfold mbox_pend_precritical_error.
  rewrite (proj2 (Z.eqb_neq _ _) H); cbn [Z.eqb negb Z.ltb].
  rewrite (proj2 (Z.ltb_lt _ _) H0); reflexivity.
Qed.

Lemma mbox_pend_precritical_clear : forall pe,
  pe <> 0 -> mbox_pend_precritical_error pe 1 0 0 = None.
Proof.
  intros; unfold mbox_pend_precritical_error.
  rewrite (proj2 (Z.eqb_neq _ _) H); reflexivity.
Qed.

(** Lifetime applies only after all four actual checks have passed.
    In particular neither ISR nor scheduler-locked early errors requires
    lifetime across an acquisition which it never executes. *)
Definition mbox_pend_api_input critical sg invocation pe before eid observed : Prop :=
  pe = 0 \/ (pe <> 0 /\ pe = event_addr sg eid /\ valid_event_id sg eid /\
    q_query_public_slot before eid observed /\
    (event_slot_type_value before.(EventState) eid = 1 ->
      before.(IntrState).(intNesting) <= 0 -> before.(IntrState).(lockNesting) <= 0 ->
      q_pend_entry_handle_protocol critical sg invocation before eid observed)).

Inductive MboxPendStart : Type :=
| MboxPendImmediate (message : addr)
| MboxPendWaiting (tid : TaskID) (generation : nat).

Definition mbox_pend_first_critical (sg : StableGlobVars) (eid : EventID) (timeout : Z)
  : program UCOS2_Verify_State MboxPendStart :=
  fun before result after => exists event mailbox,
    before.(EventState).(inUsedEventStates) eid = Some event /\
    event.(mboxFields) = Some mailbox /\
    if Z.eqb (mbox_message_ptr mailbox) 0 then
      exists tid node,
        before.(SchedState).(curTaskID) = Some tid /\
        before.(TskState).(inUsedTaskStates) tid = Some node /\
        result = MboxPendWaiting tid node.(taskGeneration) /\
        after = event_pend_state sg before eid event tid node PendMbox timeout
    else result = MboxPendImmediate (mbox_message_ptr mailbox) /\
         after = mbox_accept_update before eid event mailbox.

Lemma mbox_pend_first_critical_exists : forall sg before eid event mailbox timeout,
  before.(EventState).(inUsedEventStates) eid = Some event ->
  event.(mboxFields) = Some mailbox ->
  (mbox_message_ptr mailbox = 0 -> exists tid node,
    before.(SchedState).(curTaskID) = Some tid /\
    before.(TskState).(inUsedTaskStates) tid = Some node) ->
  exists result after, mbox_pend_first_critical sg eid timeout before result after.
Proof.
  intros * He Hm Hcurrent.
  destruct (Z.eqb (mbox_message_ptr mailbox) 0) eqn:Hempty.
  - apply Z.eqb_eq in Hempty; destruct (Hcurrent Hempty) as [tid [node [Htid Hnode]]].
    exists (MboxPendWaiting tid node.(taskGeneration)),
      (event_pend_state sg before eid event tid node PendMbox timeout).
    exists event, mailbox; split; [exact He|]; split; [exact Hm|].
    rewrite Hempty; exists tid, node; auto.
  - exists (MboxPendImmediate (mbox_message_ptr mailbox)),
      (mbox_accept_update before eid event mailbox).
    exists event, mailbox; split; [exact He|]; split; [exact Hm|].
    rewrite Hempty; auto.
Qed.

Lemma mbox_pend_first_critical_deterministic : forall sg eid timeout before r1 s1 r2 s2,
  mbox_pend_first_critical sg eid timeout before r1 s1 ->
  mbox_pend_first_critical sg eid timeout before r2 s2 -> r1 = r2 /\ s1 = s2.
Proof.
  intros * [e1 [m1 [He1 [Hm1 Hfirst]]]] [e2 [m2 [He2 [Hm2 Hsecond]]]].
  assert (e2 = e1) by congruence; subst e2.
  assert (m2 = m1) by congruence; subst m2.
  destruct (Z.eqb (mbox_message_ptr m1) 0).
  - destruct Hfirst as [tid1 [t1 [Hcur1 [Ht1 [Hr1 Hs1]]]]],
      Hsecond as [tid2 [t2 [Hcur2 [Ht2 [Hr2 Hs2]]]]].
    assert (tid2 = tid1) by congruence; subst tid2.
    assert (t2 = t1) by congruence; subst t2; split; congruence.
  - intuition congruence.
Qed.

Lemma mbox_pend_immediate_nonzero : forall sg eid timeout before message after,
  mbox_pend_first_critical sg eid timeout before (MboxPendImmediate message) after ->
  message <> 0.
Proof.
  intros * [event [mailbox [He [Hm Hstep]]]].
  destruct (Z.eqb (mbox_message_ptr mailbox) 0) eqn:Hempty.
  - destruct Hstep as [tid [node [_ [_ [Hresult _]]]]]; discriminate.
  - destruct Hstep as [Hresult _]; inversion Hresult; apply Z.eqb_neq; exact Hempty.
Qed.

Lemma mbox_pend_immediate_preserves_validity : forall sg before eid event mailbox timeout message after,
  UCOS2_state_inv sg before ->
  before.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MBOX -> event.(mboxFields) = Some mailbox ->
  mbox_pend_first_critical sg eid timeout before (MboxPendImmediate message) after ->
  UCOS2_state_inv sg after.
Proof.
  intros * Hvalid He Htype Hm [other [m [Ho [Hother Hstep]]]].
  assert (other = event) by congruence; subst other.
  assert (m = mailbox) by congruence; subst m.
  destruct (Z.eqb (mbox_message_ptr mailbox) 0).
  - destruct Hstep as [tid [node [_ [_ [Hresult _]]]]]; discriminate.
  - destruct Hstep as [_ ->]; apply mbox_accept_update_preserves_validity; assumption.
Qed.

Lemma mbox_pend_empty_message : forall sg before eid event mailbox,
  UCOS2_state_inv sg before ->
  before.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MBOX -> event.(mboxFields) = Some mailbox ->
  mbox_message_ptr mailbox = 0 -> mailbox.(mboxMsg) = None.
Proof.
  intros * [_ [_ [_ [Hevents _]]]] He Htype Hm Hempty.
  destruct Hevents as [_ [_ [_ [_ [Hpayload _]]]]].
  specialize (Hpayload eid event He); unfold event_payload_consistency in Hpayload.
  rewrite Htype, Hm in Hpayload; destruct Hpayload as [Hnonnull _].
  unfold mbox_message_ptr in Hempty.
  destruct mailbox.(mboxMsg); [contradiction|reflexivity].
Qed.

Lemma mbox_pend_wait_preserves_validity : forall sg before eid event mailbox tid node timeout,
  UCOS2_state_inv sg before ->
  before.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MBOX -> event.(mboxFields) = Some mailbox ->
  mbox_message_ptr mailbox = 0 ->
  before.(TskState).(inUsedTaskStates) tid = Some node ->
  valid_task_prio sg node.(curPrio) -> node.(eventPtr) = None ->
  node.(eventMultiWaitEvents) = [] -> node.(tcbFlagNode) = 0 ->
  In tid before.(SchedState).(readyList) ->
  UCOS2_state_inv sg (event_pend_state sg before eid event tid node PendMbox timeout).
Proof.
  intros * Hvalid He Htype Hm Hempty Hnode Hprio Hptr Hmulti Hflag Hready.
  pose proof (mbox_pend_empty_message sg before eid event mailbox Hvalid He Htype Hm Hempty) as Hnone.
  eapply UCOS2_event_pend_preserves_validity; try eassumption.
  - rewrite Htype; reflexivity.
  - unfold event_wait_resource_unavailable; rewrite Htype, Hm; exact Hnone.
  - intros mutex Hmutex; congruence.
Qed.

(** The existing message cleanup relation contains no PendQ test, Queue
    lookup, ring buffer or payload ownership. Retain it verbatim for both
    APIs, including the default-to-timeout branch and actual Msg value. *)
Definition mbox_pend_resume_critical := q_pend_resume_critical.

Lemma mbox_pend_resume_critical_eq : mbox_pend_resume_critical = q_pend_resume_critical.
Proof. reflexivity. Qed.

(** Mailbox-specific raw Wait instantiation. The shared prefix split
    [q_pend_wait_prefix_split] does not contain a Queue assumption and is
    reused directly. Only the real pending bit and unavailable-resource
    proof below differ; all unchanged task/scheduler/event cells are kept. *)
Definition mbox_pend_wait_entry sg entry eid current tid old : Prop :=
  UCOS2_state_inv sg entry /\
  entry.(SchedState).(curTaskID) = Some tid /\
  entry.(TskState).(inUsedTaskStates) tid = Some old /\
  mutex_query_lookup entry eid current /\
  current.(eventType) = OS_EVENT_TYPE_MBOX /\
  (exists mailbox, current.(mboxFields) = Some mailbox /\ mailbox.(mboxMsg) = None) /\
  old.(curPrio) <> sg.(osLowestPrio) /\ old.(eventPtr) = None /\
  old.(eventMultiWaitEvents) = [] /\ old.(tcbFlagNode) = 0 /\
  In tid entry.(SchedState).(readyList) /\ event_object_layout_prop sg eid.

Definition mbox_pend_wait_call_frame sg entry eid current tid old timeout : Assertion :=
  event_task_wait_tcb_rest (task_slot_addr sg tid)
    (task_tcb64_image sg (task_prepare_event_wait old PendMbox timeout)) **
  store_prio_tbl sg entry.(TskState).(prioTbl) **
  sem_post_task_frame sg entry.(TskState) tid **
  UCharArray.missing_i sg.(g_OSRdyTbl) (old.(curPrio) / 8) 0 8
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte entry.(SchedState).(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte entry.(SchedState).(highRdyPrio) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg entry.(SchedState).(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> entry.(SchedState).(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if entry.(SchedState).(isRunning) then 1 else 0) **
  event_task_wait_event_rest sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (old.(curPrio) / 8) (event_image sg entry.(TskState) current) **
  event_raw_rep_no_eid sg entry.(TskState) entry.(EventState) eid **
  UCOS2_raw_rep_missing_task_storage_sched_event sg entry.

Definition mbox_pend_wait_call_pre sg entry eid current tid old timeout : Assertion :=
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBY (Some (old.(curPrio) / 8)) **
  tcb_cell (task_slot_addr sg tid) TCBBitX (Some (tcb_bit_x_of_prio old.(curPrio))) **
  tcb_cell (task_slot_addr sg tid) TCBBitY (Some (tcb_bit_y_of_prio old.(curPrio))) **
  (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl") + old.(curPrio) / 8 * sizeof(UCHAR))
    # UChar |-> encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8) **
  &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
    # UChar |-> encode_event_wait_grp current.(waitList) entry.(TskState) **
  (sg.(g_OSRdyTbl) + old.(curPrio) / 8 * sizeof(UCHAR))
    # UChar |-> encode_ready_tbl_at_or entry.(SchedState).(readyList) entry.(TskState) (old.(curPrio) / 8) **
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp entry.(SchedState).(readyList) entry.(TskState) **
  mbox_pend_wait_call_frame sg entry eid current tid old timeout.

Definition mbox_pend_wait_call_post sg entry eid current tid old timeout : Assertion :=
  event_task_wait_post sg.(g_OSTCBCur) (task_slot_addr sg tid) (event_addr sg eid)
    sg.(g_OSRdyGrp) sg.(g_OSRdyTbl) (old.(curPrio) / 8)
    (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
    (encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) entry.(TskState))
    (encode_ready_tbl_at_or entry.(SchedState).(readyList) entry.(TskState) (old.(curPrio) / 8))
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState)) **
  mbox_pend_wait_call_frame sg entry eid current tid old timeout.

Lemma mbox_pend_tcb_merge_wait_prefix : forall sg tid old timeout,
  tcb_cell (task_slot_addr sg tid) TCBStat (Some (Z.lor (encode_task_status old.(stat)) 2)) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBDly (Some timeout) **
  sem_pend_tcb_residual (task_slot_addr sg tid) (task_tcb64_image sg old) TCBDly |--
  tcb64_storage_rep (task_slot_addr sg tid)
    (task_tcb64_image sg (task_prepare_event_wait old PendMbox timeout)).
Proof.
  intros; rewrite task_prepare_event_wait_image_eq.
  apply sem_pend_tcb_three_fields_merge_updated; discriminate.
Qed.

Lemma mbox_pend_wait_entry_prio : forall sg entry eid current tid old,
  mbox_pend_wait_entry sg entry eid current tid old -> valid_task_prio sg old.(curPrio).
Proof.
  intros * [Hvalid [_ [Hold [_ [_ [_ [Hnonidle _]]]]]]].
  pose proof Hvalid as [Hprofile _].
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  pose proof (sem_pend_task_priority_in_range sg entry tid old Hvalid Hold) as Hrange.
  unfold valid_task_prio; lia.
Qed.

Lemma mbox_pend_wait_entry_row_in_range : forall sg entry eid current tid old,
  mbox_pend_wait_entry sg entry eid current tid old -> 0 <= old.(curPrio) / 8 < 8.
Proof.
  intros * [Hvalid [_ [Hold _]]].
  pose proof (sem_pend_task_priority_in_range sg entry tid old Hvalid Hold) as Hrange.
  split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia].
Qed.

Lemma mbox_pend_wait_entry_resource_conditions : forall sg entry eid current tid old,
  mbox_pend_wait_entry sg entry eid current tid old ->
  event_type_to_pend_type current.(eventType) = Some PendMbox /\
  event_wait_resource_unavailable current /\
  (forall mutex, current.(eventType) = OS_EVENT_TYPE_MUTEX ->
    current.(mutexFields) = Some mutex -> mutex.(mfOwner) <> Some tid).
Proof.
  intros * [_ [_ [_ [_ [Htype [[mailbox [Hfields Hempty]] _]]]]]].
  split; [rewrite Htype; reflexivity|]. split.
  - unfold event_wait_resource_unavailable; rewrite Htype, Hfields; exact Hempty.
  - intros mutex Hmutex; congruence.
Qed.

(** The three real stores have occurred, but ready membership and EventPtr
    still describe the old state. Reassemble storage only and expose the
    exact cells consumed by the already checked internal helper. *)
Lemma mbox_pend_wait_prefix_split_call : forall sg entry eid current tid old timeout,
  mbox_pend_wait_entry sg entry eid current tid old ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_cell (task_slot_addr sg tid) TCBStat (Some (Z.lor (encode_task_status old.(stat)) 2)) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBDly (Some timeout) **
  sem_pend_prefix_frame sg entry tid old |--
  mbox_pend_wait_call_pre sg entry eid current tid old timeout.
Proof.
  intros * Hentry.
  pose proof (mbox_pend_wait_entry_row_in_range _ _ _ _ _ _ Hentry) as Hrow.
  destruct Hentry as [Hvalid [Hcur [Hold [He [Htype [Howner [Hnonidle
    [Hnone [Hmulti [Hflag [Hready Hlayout]]]]]]]]]]].
  unfold sem_pend_prefix_frame.
  sepcon_assoc_change.
  sep_apply_l_atomic (mbox_pend_tcb_merge_wait_prefix sg tid old timeout).
  sep_apply_l_atomic (event_task_wait_tcb_split (task_slot_addr sg tid)
    (task_tcb64_image sg (task_prepare_event_wait old PendMbox timeout))).
  unfold sem_pend_sched_without_current, UCOS2_raw_rep_missing_task_storage_sched.
  sep_apply_l_atomic (sched_rows_split_cell sg entry.(TskState) entry.(SchedState).(readyList)
    (old.(curPrio) / 8) Hrow).
  sep_apply_l_atomic (event_raw_rep_split_eid sg entry.(TskState) entry.(EventState) eid current He).
  unfold used_event_rep.
  sep_apply_l_atomic (event_task_wait_event_split_c_fields sg eid
    (event_image sg entry.(TskState) current) (old.(curPrio) / 8)
    (encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) entry.(TskState)) Hlayout Hrow
    (event_table_image_eq sg entry.(TskState) current (old.(curPrio) / 8) Hrow) eq_refl).
  unfold mbox_pend_wait_call_pre, mbox_pend_wait_call_frame,
    UCOS2_raw_rep_missing_task_storage_sched_event.
  cbn [task_tcb64_image task_prepare_event_wait].
  try rewrite Hnone; cbn [encode_event_link].
  entailer!.
  cbn [task_prepare_event_wait eventPtr curPrio tcb_y_of_prio].
  rewrite Hnone; reflexivity.
Qed.

Lemma mbox_pend_wait_call_merge : forall sg entry eid current tid old timeout,
  mbox_pend_wait_entry sg entry eid current tid old ->
  mbox_pend_wait_call_post sg entry eid current tid old timeout |--
  UCOS2_inv sg (event_pend_state sg entry eid current tid old PendMbox timeout).
Proof.
  intros * Hentry.
  pose proof (mbox_pend_wait_entry_row_in_range _ _ _ _ _ _ Hentry) as Hrow.
  pose proof (mbox_pend_wait_entry_prio _ _ _ _ _ _ Hentry) as Hprio.
  destruct (mbox_pend_wait_entry_resource_conditions _ _ _ _ _ _ Hentry)
    as [Hkind [Hunavailable Hnotowner]].
  destruct Hentry as [Hvalid [Hcur [Hold [He [Htype [Howner [Hnonidle
    [Hnone [Hmulti0 [Hflag [Hready Hlayout]]]]]]]]]]].
  pose proof Hvalid as [Hprofile [Htasks [[Hrdy Hmeta] [Hevents _]]]].
  assert (Hsg : valid_stable_glob_vars sg)
    by (unfold selected_kernel_profile in Hprofile; tauto).
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  pose proof Htasks as [_ [_ [_ [_ [_ [_ [Hunique [Hpriorities _]]]]]]]].
  pose proof (Hpriorities tid old Hold) as Hrange.
  pose proof (sched_ready_in_range_implies_structure sg entry.(TskState) entry.(SchedState) Hrdy)
    as Hstructure.
  unfold mbox_pend_wait_call_post, mbox_pend_wait_call_frame, event_task_wait_post.
  pose proof (event_task_wait_tcb_merge_event_ptr (task_slot_addr sg tid)
    (task_tcb64_image sg (task_prepare_event_wait old PendMbox timeout)) (event_addr sg eid)) as Htcb.
  change (tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some (event_addr sg eid)) **
    tcb_cell (task_slot_addr sg tid) TCBY (Some (old.(curPrio) / 8)) **
    tcb_cell (task_slot_addr sg tid) TCBBitX (Some (tcb_bit_x_of_prio old.(curPrio))) **
    tcb_cell (task_slot_addr sg tid) TCBBitY (Some (tcb_bit_y_of_prio old.(curPrio))) **
    event_task_wait_tcb_rest (task_slot_addr sg tid)
      (task_tcb64_image sg (task_prepare_event_wait old PendMbox timeout)) |--
    tcb64_storage_rep (task_slot_addr sg tid)
      (tcb_write (task_tcb64_image sg (task_prepare_event_wait old PendMbox timeout))
        TCBEventPtr (Some (event_addr sg eid)))) in Htcb.
  cbn [tcb_cell tcb_field_address] in Htcb.
  unfold tcb_y_of_prio in Htcb.
  sepcon_assoc_change.
  sep_apply_l_atomic Htcb.
  assert (Himage : tcb_write (task_tcb64_image sg (task_prepare_event_wait old PendMbox timeout))
    TCBEventPtr (Some (event_addr sg eid)) =
    task_tcb64_image sg (task_set_event_ptr (task_prepare_event_wait old PendMbox timeout) (Some eid)))
    by (symmetry; apply task_set_event_ptr_image_eq).
  rewrite Himage.
  sep_apply_l_atomic (sem_post_task_storage_merge sg entry.(TskState) tid
    (task_set_event_ptr (task_prepare_event_wait old PendMbox timeout) (Some eid)) Hmulti Hprofiling).
  sep_apply_l_atomic (event_task_wait_event_merge_c_fields sg eid (event_image sg entry.(TskState) current)
    (old.(curPrio) / 8)
    (encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) entry.(TskState))
    (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio)) Hlayout Hrow).
  sep_apply_l_atomic (event_task_wait_ready_merge_removed_task sg entry.(TskState) entry.(SchedState)
    tid old Hsg Hunique Hold Hrange Hstructure Hrow).
  assert (Hindex : forall state, sched_raw_rep sg entry.(TskState) state =
    sched_raw_rep sg (glob_task_set_usedtask entry.(TskState) tid
      (task_set_event_ptr (task_prepare_event_wait old PendMbox timeout) (Some eid))) state).
  { intro state; apply sched_raw_rep_priority_ext; intros slot Hin.
    cbn [glob_task_set_usedtask inUsedTaskStates]; destruct (Z.eqb slot tid) eqn:E;
      [apply Z.eqb_eq in E; subst slot; rewrite Hold|]; reflexivity. }
  intros heap Hheap.
  apply (UCOS2_inv_merge_event_pend_storage sg entry eid current tid old PendMbox timeout
    Hvalid He Hold Hprio Hnone Hmulti0 Hflag Hready Hkind Hunavailable Hnotowner heap).
  revert heap Hheap.
  match goal with |- forall heap : model, ?P heap -> ?Q heap => change (P |-- Q) end.
  cbn [event_pend_state event_wait_state replace_SchedS replace_EventS replace_TskS TskState SchedState].
  rewrite <- Hindex; unfold sched_raw_rep, sched_physical_rep.
  cbn [sched_remove_ready_task curSchedPrio highRdyPrio curTaskID highRdyTid ctxSwCtr isRunning].
  try rewrite Hcur; cbn [encode_task_link].
  entailer!.
  unfold sched_remove_ready_task, tcb_bit_x_of_prio, tcb_bit_y_of_prio.
  cbn; rewrite Hcur; cbn [encode_task_link]; entailer!.
Qed.

Lemma mbox_pend_wait_entry_preserves_validity : forall sg entry eid current tid old timeout,
  mbox_pend_wait_entry sg entry eid current tid old ->
  UCOS2_state_inv sg (event_pend_state sg entry eid current tid old PendMbox timeout).
Proof.
  intros * Hentry.
  pose proof (mbox_pend_wait_entry_prio _ _ _ _ _ _ Hentry) as Hprio.
  destruct (mbox_pend_wait_entry_resource_conditions _ _ _ _ _ _ Hentry)
    as [Hkind [Hunavailable Hnotowner]].
  destruct Hentry as [Hvalid [Hcur [Hold [He [Htype [Howner [Hnonidle
    [Hnone [Hmulti [Hflag [Hready Hlayout]]]]]]]]]]].
  eapply UCOS2_event_pend_preserves_validity; eassumption.
Qed.

(** Reuse the actual Mailbox Scheduler Save/body/Restore observation. *)
Definition mbox_pend_schedule_program (environment : option TaskStackCallEnvironment)
  critical sg original (mask : Z) : program UCOS2_Verify_State OsSchedCallContext :=
  fun before returned after => mbox_sched_return environment critical sg original before returned after.

Definition mbox_pend_started_program external environment critical sg entered eid (timeout mask : Z)
  (start : MboxPendStart) : program UCOS2_Verify_State (OSErrCode * addr) :=
  match start with
  | MboxPendImmediate message =>
      q_pend_finish_program external environment critical sg entered (message, OS_ERR_NONE)
  | MboxPendWaiting tid generation =>
      bind (q_pend_call_program external environment critical sg entered)
        (fun released => bind (mbox_pend_schedule_program environment critical sg released mask)
          (fun scheduled => bind (q_pend_call_program external environment critical sg scheduled)
            (fun resumed => bind (mbox_pend_resume_critical sg eid)
              (q_pend_finish_program external environment critical sg resumed))))
  end.

Definition mbox_pend_api_program external environment critical sg original pevent eid timeout mask
  : program UCOS2_Verify_State (OSErrCode * addr) :=
  bind (get eq) (fun before =>
    match mbox_pend_precritical_error pevent (event_slot_type_value before.(EventState) eid)
      before.(IntrState).(intNesting) before.(IntrState).(lockNesting) with
    | Some error => StateRelMonad.ret (error, 0)
    | None => bind (q_pend_call_program external environment critical sg original)
        (fun entered => bind (mbox_pend_first_critical sg eid timeout)
          (mbox_pend_started_program external environment critical sg entered eid timeout mask))
    end).

Definition mbox_pend_api_safe external environment critical sg original pevent eid timeout mask before
  (X : OSErrCode * addr -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before)
    (mbox_pend_api_program external environment critical sg original pevent eid timeout mask) X.

Definition mbox_pend_api_post external platform environment critical saved_local sg original
  mask pe eid timeout perr before message X : Assertion :=
  EX returned after error,
    coq_prop (mbox_pend_api_program external environment critical sg original pe eid timeout mask
      before (error, message) after /\ q_pend_return_safe after message error X /\
      kernel_stack_call_same_call returned original) &&
    (perr # UChar |-> encode_os_err_code error **
      sem_pend_continuation_save_input external platform environment critical saved_local sg returned mask after **
      unmap_table_rep sg).

Lemma mbox_pend_api_early_return : forall external environment critical sg original pevent eid timeout mask before error,
  mbox_pend_precritical_error pevent (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = Some error ->
  mbox_pend_api_program external environment critical sg original pevent eid timeout mask
    before (error, 0) before.
Proof.
  intros; unfold mbox_pend_api_program, StateRelMonad.bind, get.
  exists before, before; split; [split; reflexivity|]. rewrite H; split; reflexivity.
Qed.

Lemma mbox_pend_api_immediate_return : forall external environment critical sg original pevent eid timeout mask
  before entered entry checkpoint returned current message,
  mbox_pend_precritical_error pevent (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  q_pend_call_history external environment critical sg original before entered entry ->
  mbox_pend_first_critical sg eid timeout entry (MboxPendImmediate message) checkpoint ->
  q_pend_call_history external environment critical sg entered checkpoint returned current ->
  mbox_pend_api_program external environment critical sg original pevent eid timeout mask
    before (OS_ERR_NONE, message) current.
Proof.
  intros * Hprefix Hsave Hstep Hrestore.
  unfold mbox_pend_api_program, StateRelMonad.bind, get.
  exists before, before; split; [split; reflexivity|]. rewrite Hprefix.
  exists entered, entry; split; [exact Hsave|].
  exists (MboxPendImmediate message), checkpoint; split; [exact Hstep|].
  cbn [mbox_pend_started_program q_pend_finish_program StateRelMonad.bind].
  exists returned, current; split; [exact Hrestore|]. split; reflexivity.
Qed.

Lemma mbox_pend_api_waiting_return : forall external owned critical sg original pevent eid timeout mask
  before entered entry tid generation waiting released unmasked scheduled selected resumed resume_entry
  message error cleaned returned current,
  mbox_pend_precritical_error pevent (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  q_pend_call_history external (Some owned) critical sg original before entered entry ->
  mbox_pend_first_critical sg eid timeout entry (MboxPendWaiting tid generation) waiting ->
  q_pend_call_history external (Some owned) critical sg entered waiting released unmasked ->
  mbox_sched_return (Some owned) critical sg released unmasked scheduled selected ->
  q_pend_call_history external (Some owned) critical sg scheduled selected resumed resume_entry ->
  mbox_pend_resume_critical sg eid resume_entry (message, error) cleaned ->
  q_pend_call_history external (Some owned) critical sg resumed cleaned returned current ->
  mbox_pend_api_program external (Some owned) critical sg original pevent eid timeout mask
    before (error, message) current.
Proof.
  intros * Hprefix Hsave Hstart Hrelease Hschedule Hresume Hcleanup Hreturn.
  unfold mbox_pend_api_program, StateRelMonad.bind, get.
  exists before, before; split; [split; reflexivity|]. rewrite Hprefix.
  exists entered, entry; split; [exact Hsave|].
  exists (MboxPendWaiting tid generation), waiting; split; [exact Hstart|].
  cbn [mbox_pend_started_program StateRelMonad.bind].
  exists released, unmasked; split; [exact Hrelease|].
  exists scheduled, selected; split; [exact Hschedule|].
  exists resumed, resume_entry; split; [exact Hresume|].
  exists (message, error), cleaned; split; [exact Hcleanup|].
  unfold q_pend_finish_program, StateRelMonad.bind.
  exists returned, current; split; [exact Hreturn|]. split; reflexivity.
Qed.

Lemma mbox_pend_api_safe_return : forall external environment critical sg original pevent eid timeout mask
  before message error current X,
  mbox_pend_api_program external environment critical sg original pevent eid timeout mask
    before (error, message) current ->
  mbox_pend_api_safe external environment critical sg original pevent eid timeout mask before X ->
  q_pend_return_safe current message error X.
Proof.
  intros * Hprogram Hsafe; unfold mbox_pend_api_safe in Hsafe; unfold q_pend_return_safe.
  eapply (highstependret_derive
    (mbox_pend_api_program external environment critical sg original pevent eid timeout mask)
    (eq before) (error, message) (fun _ => eq current)); [|exact Hsafe].
  intros state <-; exists current; split; [exact Hprogram|reflexivity].
Qed.

(** The actual Wait result also preserves the existing blocking-call cut
    and reindexes its already owned continuation capsules. Neither lemma
    promises a future Scheduler return. *)
Lemma mbox_pend_event_wait_call_cut : forall sg call state eid event tid node timeout,
  UCOS2_state_inv sg state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  state.(SchedState).(curTaskID) = Some tid ->
  state.(TskState).(inUsedTaskStates) tid = Some node -> valid_task_prio sg node.(curPrio) ->
  node.(eventPtr) = None -> node.(eventMultiWaitEvents) = [] -> node.(tcbFlagNode) = 0 ->
  In tid state.(SchedState).(readyList) ->
  event_type_to_pend_type event.(eventType) = Some PendMbox -> event_wait_resource_unavailable event ->
  (forall mutex, event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex -> mutex.(mfOwner) <> Some tid) ->
  kernel_call_task_source call state -> sched_current_consistency state.(TskState) state.(SchedState) ->
  sem_pend_blocking_call_stage sg call state -> kernel_tcb_stack_field_layout sg ->
  let waiting := event_pend_state sg state eid event tid node PendMbox timeout in
  UCOS2_state_inv sg waiting /\ sem_pend_wait_sched_entry sg call waiting /\
  mbox_sched_wait_state call eid waiting.
Proof.
  intros sg call state eid event tid node timeout Hvalid He Hcurrent Hnode Hprio
    Hnull Hmulti Hflag Hready Hkind Hunavailable Hnotowner Hsource Hcache
    [Hidle [Havailable [Hint Hlock]]] Hlayout waiting.
  assert (Hvalid' : UCOS2_state_inv sg waiting).
  { eapply UCOS2_event_pend_preserves_validity; eassumption. }
  assert (Hsource' : kernel_call_task_source call waiting).
  { destruct Hsource as [Hlease [Hactive Hcur]].
    split; [exact Hlease|]. split.
    - unfold waiting; cbn [event_pend_state event_wait_state replace_TskS replace_SchedS replace_EventS TskState].
      eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hnode|reflexivity|exact Hactive].
    - exact Hcur. }
  assert (Hcache' : sched_current_consistency waiting.(TskState) waiting.(SchedState)).
  { unfold sched_current_consistency in Hcache; rewrite Hcurrent in Hcache.
    destruct Hcache as [current [Hlookup Hpriority]]; assert (current = node) by congruence; subst current.
    unfold sched_current_consistency.
    change (match state.(SchedState).(curTaskID) with
      | None => state.(SchedState).(curSchedPrio) = None
      | Some selected => exists current,
          (if Z.eqb selected tid then Some (task_set_event_ptr (task_prepare_event_wait node PendMbox timeout) (Some eid))
           else state.(TskState).(inUsedTaskStates) selected) = Some current /\
          state.(SchedState).(curSchedPrio) = Some current.(curPrio)
      end).
    rewrite Hcurrent; exists (task_set_event_ptr (task_prepare_event_wait node PendMbox timeout) (Some eid)).
    split; [rewrite Z.eqb_refl; reflexivity|exact Hpriority]. }
  assert (Hidle' : task_idle_ready sg waiting.(TskState)).
  { eapply event_pend_preserves_idle_ready; eassumption. }
  assert (Hready' : waiting.(SchedState).(readyList) <> []).
  { eapply sched_idle_ready_nonempty; [exact (proj1 (proj1 (proj2 (proj2 Hvalid'))))|exact Hidle']. }
  assert (Havailable' : kernel_call_stack_available call waiting) by exact Havailable.
  assert (Hcut : os_sched_call_cut sg call waiting).
  { eapply os_sched_call_cut_from_source; try eassumption.
    eapply kernel_call_task_source_stack_field_address; eassumption. }
  split; [exact Hvalid'|]. split.
  - split; [exact Hcut|]. split.
    + apply os_sched_selection_enabled_iff; split; assumption.
    + split; [exact Hsource'|]. split; [unfold sem_pend_blocking_call_stage; auto|exact Hcache'].
  - pose proof (kernel_call_task_source_current_at call state Hsource)
      as [Hslot [current [Hlookup Hgeneration]]].
    assert (Htid : tid = call.(os_sched_call_stack).(stackLeaseSlot)) by congruence.
    assert (current = node) by (rewrite <- Htid in Hlookup; congruence); subst current.
    unfold mbox_sched_wait_state; exists (task_set_event_ptr (task_prepare_event_wait node PendMbox timeout) (Some eid)).
    split.
    + unfold waiting; cbn [event_pend_state event_wait_state replace_TskS replace_SchedS replace_EventS TskState
        glob_task_set_usedtask inUsedTaskStates]; rewrite <- Htid, Z.eqb_refl; reflexivity.
    + rewrite <- Hgeneration; apply mbox_sched_wait_establishes_continuation; try assumption.
      pose proof Hvalid as [_ [_ [[Hready_inv _] _]]].
      destruct (proj1 Hready_inv _ Hready) as [current [Hready_lookup [_ Heffective]]].
      assert (current = node) by congruence; subst current; exact Heffective.
Qed.

Lemma mbox_pend_wait_call_continuations_merge : forall external platform environment saved_local sg call
  entry eid current tid old timeout,
  mbox_pend_wait_entry sg entry eid current tid old ->
  mbox_pend_wait_call_post sg entry eid current tid old timeout **
  sem_pend_optional_continuation_resources external platform environment saved_local call entry |--
  UCOS2_inv sg (event_pend_state sg entry eid current tid old PendMbox timeout) **
  sem_pend_optional_continuation_resources external platform environment saved_local call
    (event_pend_state sg entry eid current tid old PendMbox timeout).
Proof.
  intros * Hentry; pose proof Hentry as [_ [_ [Hold _]]].
  sep_apply_l_atomic (sem_pend_optional_continuation_task_update external platform environment saved_local
    call entry tid old (task_set_event_ptr (task_prepare_event_wait old PendMbox timeout) (Some eid))
    Hold eq_refl eq_refl).
  sep_apply_l_atomic (mbox_pend_wait_call_merge sg entry eid current tid old timeout Hentry).
  unfold sem_pend_optional_continuation_resources; destruct environment; entailer!.
Qed.

(** First-acquire facts are Mailbox-typed and only required after the actual
    NULL/type/ISR/lock prefix. No wait-lifetime restriction is hidden here. *)
Definition mbox_pend_acquire_facts critical sg invocation eid mask saved before entry observed current : Prop :=
  critical_region_interval critical sg invocation before entry /\
  UCOS2_state_inv sg entry /\ interrupt_saved_value mask saved /\
  mutex_query_lookup before eid observed /\ mutex_query_lookup entry eid current /\
  observed.(eventType) = OS_EVENT_TYPE_MBOX /\ current.(eventType) = OS_EVENT_TYPE_MBOX /\
  current.(eventGeneration) = observed.(eventGeneration).

Lemma mbox_pend_public_slot_is_mbox : forall before eid observed,
  q_query_public_slot before eid observed ->
  event_slot_type_value before.(EventState) eid = 1 ->
  mutex_query_lookup before eid observed /\ observed.(eventType) = OS_EVENT_TYPE_MBOX.
Proof.
  intros before eid observed Hslot Htype.
  unfold q_query_public_slot in Hslot.
  destruct Hslot as [Hused|[Hfree Hunused]].
  - split; [exact Hused|].
    unfold event_slot_type_value in Htype; rewrite Hused in Htype.
    apply mbox_accept_encoded_type; exact Htype.
  - unfold event_slot_type_value in Htype; rewrite Hfree in Htype; discriminate.
Qed.

Definition mbox_pend_api_prefix pe before eid : Prop :=
  mbox_pend_precritical_error pe (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None /\
  before.(IntrState).(intNesting) = 0 /\ before.(IntrState).(lockNesting) = 0.

(** Only the first acquisition is protected by the handle protocol. A
    Delete-ALWAYS while waiting is admitted by the separate wait history.
    The source obligations below reuse the checked Task entry/Idle
    preservation interfaces, not a new list of allowed foreign APIs. *)
Definition mbox_pend_nonblocking_acquire critical sg call before eid : Prop :=
  forall entry current queue,
    critical_region_interval critical sg call.(os_sched_call_invocation) before entry ->
    mutex_query_lookup entry eid current -> current.(eventType) = OS_EVENT_TYPE_MBOX ->
    current.(mboxFields) = Some queue -> mbox_message_ptr queue <> 0.

Definition mbox_pend_api_admission (environment : option TaskStackCallEnvironment)
  critical sg call pe before eid : Prop :=
  mbox_pend_api_prefix pe before eid ->
  ((exists owned, environment = Some owned /\ mbox_sched_clients owned critical) /\
    sem_pend_task_call_stage sg call before /\
    kernel_running_idle_ready sg before /\ kernel_call_stack_available call before /\
    q_pend_entry_source_protocol critical sg call before) \/
  mbox_pend_nonblocking_acquire critical sg call before eid.

Lemma mbox_pend_api_admission_early_error : forall environment critical sg call pe before eid error,
  mbox_pend_precritical_error pe (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = Some error ->
  mbox_pend_api_admission environment critical sg call pe before eid.
Proof. intros * Herror [Hclear _]; congruence. Qed.

Lemma mbox_pend_api_admission_nonblocking : forall environment critical sg call pe before eid,
  mbox_pend_nonblocking_acquire critical sg call before eid ->
  mbox_pend_api_admission environment critical sg call pe before eid.
Proof. intros * Hpositive _; right; exact Hpositive. Qed.

Lemma mbox_pend_api_admission_task : forall owned critical sg call pe before eid,
  sem_pend_task_call_stage sg call before -> kernel_running_idle_ready sg before ->
  kernel_call_stack_available call before -> q_pend_entry_source_protocol critical sg call before ->
  mbox_sched_clients owned critical ->
  mbox_pend_api_admission (Some owned) critical sg call pe before eid.
Proof. intros * Hstage Hidle Havailable Hsource Hclients _; left; split; [eauto|]; auto. Qed.

Lemma mbox_pend_prefix_guards : forall pe before eid,
  mbox_pend_api_prefix pe before eid ->
  pe <> 0 /\ event_slot_type_value before.(EventState) eid = 1 /\
  before.(IntrState).(intNesting) <= 0 /\ before.(IntrState).(lockNesting) <= 0.
Proof.
  intros pe before eid [H Hcounters]; unfold mbox_pend_precritical_error in H.
  destruct (Z.eqb pe 0) eqn:Hpe; [discriminate|].
  destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 1) eqn:Htype;
    cbn [negb] in H; [|discriminate].
  destruct (Z.ltb 0 before.(IntrState).(intNesting)) eqn:Hint; [discriminate|].
  destruct (Z.ltb 0 before.(IntrState).(lockNesting)) eqn:Hlock; [discriminate|].
  apply Z.eqb_neq in Hpe; apply Z.eqb_eq in Htype;
    apply Z.ltb_ge in Hint; apply Z.ltb_ge in Hlock; auto.
Qed.

Lemma mbox_pend_save_acquire_facts : forall external port critical sg original returned
  pe eid observed mask saved before acquired,
  UCOS2_state_inv sg before ->
  mbox_pend_api_input critical sg original.(os_sched_call_invocation) pe before eid observed ->
  mbox_pend_api_prefix pe before eid ->
  kernel_call_save_source external port critical sg original returned mask saved before acquired ->
  exists current, mbox_pend_acquire_facts critical sg original.(os_sched_call_invocation)
    eid mask saved before acquired observed current.
Proof.
  intros * Hvalid Hinput Hprefix Hsave.
  destruct (mbox_pend_prefix_guards _ _ _ Hprefix) as [Hnonnull [Htype [Hint Hlock]]].
  destruct Hinput as [Hzero|[_ [Haddress [Hid [Hslot Hprotocol]]]]]; [contradiction|].
  destruct (mbox_pend_public_slot_is_mbox before eid observed Hslot Htype) as [Hlookup Hqueue].
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsave) as Hinterval.
  destruct (Hprotocol Htype Hint Hlock acquired Hinterval) as [current [Hcurrent [Hg Hkind]]].
  pose proof (proj1 (critical_region_interval_transports_resources _ _ _ _ _ Hinterval Hvalid)) as Hvalid'.
  pose proof (proj2 (proj2 (proj2 (proj2 Hsave)))) as Hsaved.
  exists current; unfold mbox_pend_acquire_facts.
  repeat first [assumption | split | congruence].
Qed.

Lemma mbox_pend_empty_acquire_owned : forall environment critical sg original pe before eid
  entry current queue,
  mbox_pend_api_admission environment critical sg original pe before eid ->
  mbox_pend_api_prefix pe before eid ->
  critical_region_interval critical sg original.(os_sched_call_invocation) before entry ->
  mutex_query_lookup entry eid current -> current.(eventType) = OS_EVENT_TYPE_MBOX ->
  current.(mboxFields) = Some queue -> mbox_message_ptr queue = 0 ->
  exists owned, environment = Some owned /\ mbox_sched_clients owned critical.
Proof.
  intros * Hadmit Hprefix Hinterval Hlookup Htype Hfields Hempty.
  destruct (Hadmit Hprefix) as [[[owned [Howned Hclients]] _]|Hpositive]; [eauto|].
  specialize (Hpositive entry current queue Hinterval Hlookup Htype Hfields); contradiction.
Qed.


Lemma mbox_pend_empty_acquire_stage : forall owned critical sg original entered pe before eid
  entry current queue,
  UCOS2_state_inv sg before -> UCOS2_state_inv sg entry ->
  mbox_pend_api_admission (Some owned) critical sg original pe before eid ->
  mbox_pend_api_prefix pe before eid ->
  sem_pend_modular_call_history owned critical sg original before entered entry ->
  sem_pend_save_rely sg before entry ->
  mutex_query_lookup entry eid current -> current.(eventType) = OS_EVENT_TYPE_MBOX ->
  current.(mboxFields) = Some queue -> mbox_message_ptr queue = 0 ->
  sem_pend_task_call_stage sg entered entry /\ sem_pend_blocking_call_stage sg entered entry.
Proof.
  intros * Hvalid Hentry Hadmit Hprefix Hhistory Hrely Hlookup Htype Hfields Hempty.
  pose proof Hhistory as [Htrace [Hsame Havailable_return]].
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)
    as [Hinterval Hcontrol].
  destruct (Hadmit Hprefix) as [[Howned [Hstage [Hruntime [Havailable [Hclients Hidle_clients]]]]]|Hpositive].
  2: { specialize (Hpositive entry current queue Hinterval Hlookup Htype Hfields); contradiction. }
  destruct Hstage as [Hsource [Hrunning [old [Hready [Hg [Hnonidle [He [Hm Hf]]]]]]]].
  destruct (mutex_pend_modular_history_preserves_ready_entry owned critical sg original entered
    before entry old Hclients Hvalid Hsource Hrunning Hready
    ltac:(unfold sem_pend_task_unregistered; auto) Hhistory Hrely)
    as [Hsource' [Hrunning' [node [Hready' [Hg' [He' [Hm' Hf']]]]]]].
  pose proof Hvalid as [_ [_ [_ [_ [_ [Htail _]]]]]].
  destruct (Htail Hrunning) as [prefix [idle [idle_node [Horder [Hidle_node [Hidleprio Hothers]]]]]].
  assert (Hslot : mutex_idle_slot before.(TskState) idle) by (exists prefix; exact Horder).
  assert (Hdifferent : original.(os_sched_call_stack).(stackLeaseSlot) <> idle).
  { intro Hequal; pose proof (proj1 Hready) as Hold; rewrite Hequal in Hold.
    assert (old = idle_node) by congruence; subst old; contradiction. }
  assert (Hslot' : mutex_idle_slot entry.(TskState) idle).
  { eapply (mutex_idle_region_interval_preserves_slot critical sg idle
      original.(os_sched_call_invocation) before entry);
      [apply Hidle_clients; exact Hslot|exact Hvalid|exact Hinterval|exact Hslot]. }
  assert (Hnonidle' : node.(curPrio) <> sg.(osLowestPrio)).
  { eapply mutex_non_idle_priority; [exact (proj1 (proj2 Hentry))| |exact (proj1 Hready')|].
    - eapply mutex_running_idle_slot_task; eassumption.
    - rewrite (proj2 (proj2 Hsame)); exact Hdifferent. }
  split.
  - unfold sem_pend_task_call_stage; split; [exact Hsource'|]. split; [exact Hrunning'|].
    exists node; split; [exact Hready'|]. repeat split; assumption.
  - destruct Hrely as [[Hrun Hcounters] [Hruntime_return [Hcache Hready_return]]].
    pose proof (proj2 Hprefix) as [Hint Hlock].
    unfold sem_pend_blocking_call_stage; split.
    + apply (Hruntime_return Hruntime); exact Hrunning'.
    + split; [apply Havailable_return; exact Havailable|].
      rewrite Hcounters; auto.
Qed.

(** Literal CPU-call indices. Only an actual empty observation demands
    Task resources; the ordinary nonblocking and all early-error arms
    retain the no-capsule domain. *)
Inductive MboxPendSavePhase : Type :=
| MboxPendAcquirePhase (pe : addr) (eid : EventID) (observed : OSEventAbstractState)
| MboxPendResumePhase (phase : MboxPendSchedPhase).

Definition mbox_pend_save_phase_pre phase environment critical sg call mask before : Prop :=
  match phase with
  | MboxPendAcquirePhase pe eid observed =>
      mbox_pend_api_input critical sg call.(os_sched_call_invocation) pe before eid observed /\
      mbox_pend_api_prefix pe before eid /\ mbox_pend_api_admission environment critical sg call pe before eid
  | MboxPendResumePhase (MboxPendWaitPhase original initial_mask eid) =>
      mask = initial_mask /\
      (exists owned, environment = Some owned /\ mbox_sched_clients owned critical) /\
      mbox_sched_wait_selected_at sg original eid call before
  end.

Definition mbox_pend_save_phase_observation phase external environment critical sg call returned
  mask saved before acquired : Prop :=
  q_pend_call_history external environment critical sg call before returned acquired /\
  interrupt_saved_value mask saved /\
  match phase with
  | MboxPendAcquirePhase pe eid observed =>
      exists current, mbox_pend_acquire_facts critical sg call.(os_sched_call_invocation)
        eid mask saved before acquired observed current /\
        (forall queue, current.(mboxFields) = Some queue -> mbox_message_ptr queue = 0 ->
          (exists owned, environment = Some owned /\ mbox_sched_clients owned critical) /\
          sem_pend_task_call_stage sg returned acquired /\ sem_pend_blocking_call_stage sg returned acquired)
  | MboxPendResumePhase (MboxPendWaitPhase original initial_mask eid) =>
      (exists owned, environment = Some owned /\ mbox_sched_clients owned critical) /\
      mbox_sched_wait_selected_at sg original eid returned acquired
  end.

Definition mbox_pend_save_input phase external platform environment critical saved_local
  sg call mask before : Assertion :=
  coq_prop (mbox_pend_save_phase_pre phase environment critical sg call mask before) &&
  (sem_pend_continuation_save_input external platform environment critical saved_local sg call mask before **
    unmap_table_rep sg).

Definition mbox_pend_masked_frame := q_pend_masked_frame.

(** Only the ECB message word is exposed; the pointed-to payload remains
    outside the kernel's ownership. The retained world is the real first
    acquisition, not a snapshot promised to survive the later wait. *)
Definition mbox_pend_message_frame external platform environment critical saved_local
  sg original entered mask saved pe before entry eid observed current mailbox : Assertion :=
  coq_prop (mbox_pend_save_phase_observation (MboxPendAcquirePhase pe eid observed)
      external environment critical sg original entered mask saved before entry /\
    mbox_pend_acquire_facts critical sg original.(os_sched_call_invocation)
      eid mask saved before entry observed current /\ current.(mboxFields) = Some mailbox) &&
  (mbox_pend_masked_frame external platform environment critical saved_local sg
      entered saved entry entry **
    mbox_rep_no_message sg entry.(TskState) eid current **
    event_raw_rep_no_eid sg entry.(TskState) entry.(EventState) eid **
    queue_storage_rep sg entry.(EventState) ** UCOS2_raw_rep_missing_event_queue sg entry).

Definition mbox_pend_save_output phase external platform environment critical saved_local
  sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (mbox_pend_save_phase_observation phase external environment critical sg original returned
      mask saved before acquired) &&
    (mbox_pend_masked_frame external platform environment critical saved_local sg returned saved acquired acquired **
      UCOS2_inv sg acquired).

Definition mbox_pend_restore_input (phase : option MboxPendSchedPhase) external platform environment critical saved_local
  sg call mask saved acquired released : Assertion :=
  coq_prop (interrupt_saved_value mask saved /\
    match phase with None => True | Some waiting =>
      (exists owned, environment = Some owned /\ mbox_sched_clients owned critical) /\
      mbox_sched_restore_phase_pre waiting environment critical sg call mask released end) &&
  (mbox_pend_masked_frame external platform environment critical saved_local sg call saved acquired released ** UCOS2_inv sg released).

Definition mbox_pend_restore_output (phase : option MboxPendSchedPhase) external platform environment critical saved_local
  sg original mask released : Assertion :=
  EX returned current,
    coq_prop (q_pend_call_history external environment critical sg original released returned current /\
      match phase with None => True | Some waiting =>
        (exists owned, environment = Some owned /\ mbox_sched_clients owned critical) /\
        mbox_sched_restore_phase_pre waiting environment critical sg returned mask current end) &&
    (sem_pend_continuation_save_input external platform environment critical saved_local sg returned mask current **
      unmap_table_rep sg).

(** Pure cut observations record only source edges already traversed by
    this call. No continuation assertion entails that a future edge exists. *)
Definition mbox_pend_immediate_checkpoint external environment critical sg original before entered entry
  eid timeout message checkpoint : Prop :=
  q_pend_call_history external environment critical sg original before entered entry /\
  mbox_pend_first_critical sg eid timeout entry (MboxPendImmediate message) checkpoint.

Definition mbox_pend_first_wait_checkpoint external environment critical sg original before entered
  eid timeout waiting : Prop :=
  exists entry,
  q_pend_call_history external environment critical sg original before entered entry /\
  mbox_pend_first_critical sg eid timeout entry
    (MboxPendWaiting original.(os_sched_call_stack).(stackLeaseSlot)
      original.(os_sched_call_stack).(stackLeaseGeneration)) waiting.

Definition mbox_pend_released_checkpoint external environment critical sg original before entered
  eid timeout waiting released unmasked : Prop :=
  mbox_pend_first_wait_checkpoint external environment critical sg original before entered eid timeout waiting /\
  q_pend_call_history external environment critical sg entered waiting released unmasked.

Definition mbox_pend_scheduling_checkpoint external environment critical sg original before
  eid timeout released unmasked : Prop :=
  exists entered waiting, mbox_pend_released_checkpoint external environment critical sg original before entered
    eid timeout waiting released unmasked.

Definition mbox_pend_sched_admitted (environment : option TaskStackCallEnvironment) critical : Prop :=
  exists owned, environment = Some owned /\ mbox_sched_clients owned critical.

Definition mbox_pend_scheduled_checkpoint external environment critical sg original before eid timeout scheduled selected : Prop :=
  exists entered waiting released unmasked,
    mbox_pend_released_checkpoint external environment critical sg original before entered
      eid timeout waiting released unmasked /\
    mbox_sched_return environment critical sg released unmasked scheduled selected.

Definition mbox_pend_resume_checkpoint external environment critical sg original before eid timeout resumed resume_entry : Prop :=
  exists scheduled selected,
    mbox_pend_scheduled_checkpoint external environment critical sg original before eid timeout scheduled selected /\
    q_pend_call_history external environment critical sg scheduled selected resumed resume_entry.

Definition mbox_pend_first_owner external platform environment critical saved_local sg original entered
  mask saved pe before entry eid observed : Assertion :=
  coq_prop (mbox_pend_save_phase_observation (MboxPendAcquirePhase pe eid observed)
    external environment critical sg original entered mask saved before entry) &&
  (os_sched_context_resources external entered **
    sem_pend_optional_continuation_resources external platform environment saved_local entered entry **
    unmap_table_rep sg).

Definition mbox_pend_empty_snapshot external environment critical sg original entered
  mask saved pe before entry eid observed current tid old : Prop :=
  mbox_pend_save_phase_observation (MboxPendAcquirePhase pe eid observed)
    external environment critical sg original entered mask saved before entry /\
  mbox_pend_wait_entry sg entry eid current tid old /\
  kernel_call_task_source entered entry /\
  sched_current_consistency entry.(TskState) entry.(SchedState) /\
  sem_pend_blocking_call_stage sg entered entry /\
  (exists owned, environment = Some owned /\ mbox_sched_clients owned critical).

Lemma mbox_pend_empty_wait_phase : forall external environment critical sg original entered
  mask saved pe before entry eid observed current tid old timeout,
  mbox_pend_empty_snapshot external environment critical sg original entered
    mask saved pe before entry eid observed current tid old ->
  kernel_tcb_stack_field_layout sg ->
  let waiting := event_pend_state sg entry eid current tid old PendMbox timeout in
  mbox_pend_first_wait_checkpoint external environment critical sg original before entered
    eid timeout waiting /\
  mbox_sched_restore_phase_pre (MboxPendWaitPhase original mask eid)
    environment critical sg entered mask waiting.
Proof.
  intros * [Hobservation [Hentry [Hsource [Hcache [Hstage Howned]]]]] Hlayout waiting.
  pose proof (mbox_pend_wait_entry_prio _ _ _ _ _ _ Hentry) as Hprio.
  destruct (mbox_pend_wait_entry_resource_conditions _ _ _ _ _ _ Hentry)
    as [Hkind [Hunavailable Hnotowner]].
  pose proof Hentry as [Hvalid [Hcur [Hold [Hlookup [Htype [[mailbox [Hfields Hempty]]
    [Hnonidle [Hnull [Hmulti [Hflag [Hready Heventlayout]]]]]]]]]]].
  destruct (mbox_pend_event_wait_call_cut sg entered entry eid current tid old timeout
    Hvalid Hlookup Hcur Hold Hprio Hnull Hmulti Hflag Hready Hkind Hunavailable
    Hnotowner Hsource Hcache Hstage Hlayout) as [Hvalid' [Hcut Hwait]].
  pose proof (proj1 Hobservation) as Hhistory.
  pose proof (q_pend_call_history_same_call _ _ _ _ _ _ _ _ Hhistory) as Hsame.
  pose proof Hsame as [Hi [Ho Hstack]].
  pose proof (kernel_call_task_source_current_at entered entry Hsource)
    as [Hslot [node [Hnode Hgeneration]]].
  assert (Htid : tid = entered.(os_sched_call_stack).(stackLeaseSlot)) by congruence.
  assert (node = old) by (rewrite <- Htid in Hnode; congruence); subst node.
  split.
  - exists entry; split; [exact Hhistory|].
    exists current, mailbox; split; [exact Hlookup|]. split; [exact Hfields|].
    unfold mbox_message_ptr; rewrite Hempty; cbn [Z.eqb].
    exists tid, old; split; [exact Hcur|]. split; [exact Hold|]. split.
    + rewrite <- Hstack; f_equal; congruence.
    + reflexivity.
  - unfold mbox_sched_restore_phase_pre; split; [reflexivity|].
    split; [|exact Hcut].
    pose proof (proj1 (proj2 (proj2 Hcut))) as [Horigin [Hactive Hcurrent]].
    unfold mbox_sched_wait_at; split; [exact Hsame|].
    unfold mbox_sched_wait_state in Hwait |- *.
    rewrite <- Hi, <- Ho, <- Hstack; auto.
Qed.

Lemma mbox_pend_resume_checkpoint_owned : forall external environment critical sg original before eid timeout resumed resume_entry,
  mbox_pend_resume_checkpoint external environment critical sg original before eid timeout resumed resume_entry ->
  exists owned, environment = Some owned.
Proof.
  intros * [scheduled [selected [[entered [waiting [released [unmasked [Hreleased Hschedule]]]]] Hresume]]].
  destruct environment as [owned|]; [eauto|contradiction].
Qed.

Lemma mbox_pend_immediate_checkpoint_return : forall external environment critical sg original pe eid timeout mask
  before entered entry message checkpoint returned current,
  mbox_pend_api_prefix pe before eid ->
  mbox_pend_immediate_checkpoint external environment critical sg original before entered entry eid timeout message checkpoint ->
  q_pend_call_history external environment critical sg entered checkpoint returned current ->
  mbox_pend_api_program external environment critical sg original pe eid timeout mask before (OS_ERR_NONE, message) current.
Proof. intros * [Hprefix _] [Hsave Hfirst] Hrestore; eapply mbox_pend_api_immediate_return; eassumption. Qed.

Lemma mbox_pend_resume_checkpoint_return : forall external environment critical sg original pe eid timeout mask
  before resumed resume_entry message error cleaned returned current,
  mbox_pend_api_prefix pe before eid ->
  mbox_pend_resume_checkpoint external environment critical sg original before eid timeout resumed resume_entry ->
  mbox_pend_resume_critical sg eid resume_entry (message, error) cleaned ->
  q_pend_call_history external environment critical sg resumed cleaned returned current ->
  mbox_pend_api_program external environment critical sg original pe eid timeout mask before (error, message) current.
Proof.
  intros * [Hprefix _] Hcheckpoint Hcleanup Hreturn.
  destruct (mbox_pend_resume_checkpoint_owned _ _ _ _ _ _ _ _ _ _ Hcheckpoint) as [owned ->].
  destruct Hcheckpoint as [scheduled [selected [[entered [waiting [released [unmasked
    [[[entry [Hfirst_save Hfirst]] Hrelease] Hschedule]]]]] Hresume]]].
  eapply mbox_pend_api_waiting_return; eassumption.
Qed.

(** These consequences consume the common C-modular producers. The
    selected rely is an existing C-environment obligation, not a new
    promise of the CPU port; in the unowned arm only a real nonblocking
    acquisition can reach the Mailbox data path. *)
Lemma mbox_pend_modular_save_acquire_observation : forall environment critical sg call returned
  pe eid observed mask saved before acquired,
  UCOS2_state_inv sg before ->
  mbox_pend_save_phase_pre (MboxPendAcquirePhase pe eid observed)
    (Some environment) critical sg call mask before ->
  kernel_call_save_source environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical sg call returned mask saved before acquired ->
  kernel_call_normal_return call before returned acquired ->
  sem_pend_save_rely sg before acquired ->
  mbox_pend_save_phase_observation (MboxPendAcquirePhase pe eid observed)
    environment.(task_stack_call_external) (Some environment) critical sg call returned mask saved before acquired.
Proof.
  intros * Hvalid [Hinput [Hprefix Hadmit]] Hsave Hnormal Hrely.
  destruct (mbox_pend_save_acquire_facts _ _ _ _ _ _ _ _ _ _ _ _ _
    Hvalid Hinput Hprefix Hsave) as [current Hfacts].
  pose proof Hfacts as [Hinterval [Hvalid' [Hsaved [Hlookup [Hcurrent [Htype [Htype' Hgen]]]]]]].
  assert (Hhistory : sem_pend_modular_call_history environment critical sg call before returned acquired)
    by (split; [exact (proj1 Hsave)|exact Hnormal]).
  split; [exact Hhistory|]. split; [exact Hsaved|]. exists current; split; [exact Hfacts|].
  intros queue Hfields Hempty; split.
  - eapply mbox_pend_empty_acquire_owned; eassumption.
  - exact (mbox_pend_empty_acquire_stage environment critical sg call returned pe before eid
      acquired current queue Hvalid Hvalid' Hadmit Hprefix Hhistory Hrely Hcurrent Htype' Hfields Hempty).
Qed.

Lemma mbox_pend_modular_save_acquire_output : forall environment critical saved_local sg call
  pe eid observed mask saved before,
  UCOS2_state_inv sg before ->
  mbox_pend_save_phase_pre (MboxPendAcquirePhase pe eid observed)
    (Some environment) critical sg call mask before ->
  kernel_call_modular_save_post environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) critical sem_pend_save_rely
    sg call mask saved before |--
  mbox_pend_save_output (MboxPendAcquirePhase pe eid observed)
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg call mask saved before.
Proof.
  intros * Hvalid Hpre.
  unfold kernel_call_modular_save_post; Intros returned acquired.
  assert (Hsave : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call returned mask saved before acquired) by tauto.
  assert (Hnormal : kernel_call_normal_return call before returned acquired) by tauto.
  assert (Hrely : sem_pend_save_rely sg before acquired) by tauto.
  pose proof (mbox_pend_modular_save_acquire_observation environment critical sg call returned
    pe eid observed mask saved before acquired Hvalid Hpre Hsave Hnormal Hrely) as Hphase.
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_restore_input_masked_world
    environment critical saved_local sg returned saved acquired acquired)).
  sep_apply_l_atomic (proj2 (q_pend_masked_frame_owned
    environment critical saved_local sg returned saved acquired acquired)).
  unfold mbox_pend_save_output; Exists returned acquired; entailer!.
Qed.

Lemma mbox_pend_modular_save_resume_output : forall environment critical saved_local sg original initial_mask
  eid call mask saved before,
  mbox_pend_save_phase_pre
    (MboxPendResumePhase (MboxPendWaitPhase original initial_mask eid))
    (Some environment) critical sg call mask before ->
  kernel_call_modular_save_post environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) critical sem_pend_save_rely
    sg call mask saved before |--
  mbox_pend_save_output
    (MboxPendResumePhase (MboxPendWaitPhase original initial_mask eid))
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg call mask saved before.
Proof.
  intros * [Hmask [[owned [Howned Hclients]] Hselected]]; injection Howned as <-.
  unfold kernel_call_modular_save_post; Intros returned acquired.
  assert (Hsave : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call returned mask saved before acquired) by tauto.
  assert (Hhistory : sem_pend_modular_call_history environment critical sg call before returned acquired)
    by (split; [exact (proj1 Hsave)|tauto]).
  assert (Hrely : sem_pend_save_rely sg before acquired) by tauto.
  pose proof (mbox_sched_wait_selected_modular_return environment critical sg original eid call before returned acquired (proj1 Hclients) Hselected Hhistory Hrely) as Hselected'.
  pose proof (proj2 (proj2 (proj2 (proj2 Hsave)))) as Hsaved.
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_restore_input_masked_world
    environment critical saved_local sg returned saved acquired acquired)).
  sep_apply_l_atomic (proj2 (q_pend_masked_frame_owned
    environment critical saved_local sg returned saved acquired acquired)).
  unfold mbox_pend_save_output; Exists returned acquired; entailer!.
  split; [exact Hhistory|]. split; [exact Hsaved|]. split; [eauto|exact Hselected'].
Qed.

Lemma mbox_pend_modular_save_unowned_acquire_output : forall external platform port critical saved_local
  sg call returned pe eid observed mask saved before acquired,
  UCOS2_state_inv sg before ->
  mbox_pend_save_phase_pre (MboxPendAcquirePhase pe eid observed) None critical sg call mask before ->
  kernel_call_save_source external port critical sg call returned mask saved before acquired ->
  kernel_call_normal_return call before returned acquired ->
  critical_region_masked platform critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) saved acquired ** os_sched_context_resources external returned **
    UCOS2_inv sg acquired ** unmap_table_rep sg |--
  mbox_pend_save_output (MboxPendAcquirePhase pe eid observed)
    external platform None critical saved_local sg call mask saved before.
Proof.
  intros * Hvalid [Hinput [Hprefix Hadmit]] Hsave Hnormal.
  destruct (mbox_pend_save_acquire_facts _ _ _ _ _ _ _ _ _ _ _ _ _
    Hvalid Hinput Hprefix Hsave) as [current Hfacts].
  pose proof Hfacts as [Hinterval [Hvalid' [Hsaved [Hlookup [Hcurrent [Htype [Htype' Hgen]]]]]]].
  assert (Hphase : mbox_pend_save_phase_observation (MboxPendAcquirePhase pe eid observed)
    external None critical sg call returned mask saved before acquired).
  { split; [exists port; split; [exact (proj1 Hsave)|exact Hnormal]|].
    split; [exact Hsaved|]. exists current; split; [exact Hfacts|].
    intros queue Hfields Hempty.
    destruct (mbox_pend_empty_acquire_owned None critical sg call pe before eid acquired current queue
      Hadmit Hprefix Hinterval Hcurrent Htype' Hfields Hempty) as [owned [Howned _]]; discriminate. }
  pose proof (proj1 Hnormal) as [Hi [Ho Hs]].
  unfold mbox_pend_save_output; Exists returned acquired.
  unfold mbox_pend_masked_frame, q_pend_masked_frame,
    sem_pend_optional_continuation_resources; rewrite Hi, Ho; entailer!.
Qed.

Lemma mbox_pend_modular_restore_return_output : forall environment critical saved_local rely sg call mask released,
  kernel_call_modular_restore_post environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) critical rely
    sg call mask released |--
  mbox_pend_restore_output None environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg call mask released.
Proof.
  intros; unfold kernel_call_modular_restore_post; Intros returned current.
  assert (Hhistory : sem_pend_modular_call_history environment critical sg call released returned current)
    by (unfold sem_pend_modular_call_history; tauto).
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_save_input_closed_world
    environment critical saved_local sg returned mask current)).
  sep_apply_l_atomic (proj2 (sem_pend_continuation_save_input_owned
    environment critical saved_local sg returned mask current)).
  unfold mbox_pend_restore_output; Exists returned current; entailer!.
Qed.

Lemma mbox_pend_modular_restore_wait_output : forall environment critical saved_local sg original initial_mask
  eid call mask released,
  kernel_tcb_stack_field_layout sg -> UCOS2_state_inv sg released ->
  mbox_sched_clients environment critical ->
  mbox_sched_restore_phase_pre (MboxPendWaitPhase original initial_mask eid)
    (Some environment) critical sg call mask released ->
  kernel_call_modular_restore_post environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) critical sem_pend_blocking_rely
    sg call mask released |--
  mbox_pend_restore_output (Some (MboxPendWaitPhase original initial_mask eid))
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg call mask released.
Proof.
  intros * Hlayout Hvalid Hclients [Hmask [Hwait Hentry]].
  unfold kernel_call_modular_restore_post; Intros returned current.
  assert (Hhistory : sem_pend_modular_call_history environment critical sg call released returned current)
    by (unfold sem_pend_modular_call_history; tauto).
  assert (Hrely : sem_pend_blocking_rely sg released current) by tauto.
  pose proof (mbox_sched_wait_at_modular_return environment critical sg original eid call released returned current (proj1 Hclients) Hvalid Hwait Hhistory) as Hwait'.
  pose proof (sem_pend_wait_sched_entry_modular_return environment critical sg call released returned current
    Hlayout Hvalid (proj1 (proj2 (proj2 Hentry))) Hentry Hhistory Hrely) as Hentry'.
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_save_input_closed_world
    environment critical saved_local sg returned mask current)).
  sep_apply_l_atomic (proj2 (sem_pend_continuation_save_input_owned
    environment critical saved_local sg returned mask current)).
  assert (Hphase : mbox_sched_restore_phase_pre
    (MboxPendWaitPhase original initial_mask eid)
    (Some environment) critical sg returned mask current) by (unfold mbox_sched_restore_phase_pre; auto).
  assert (Howned : exists owned, Some environment = Some owned /\ mbox_sched_clients owned critical)
    by (exists environment; auto).
  unfold mbox_pend_restore_output; Exists returned current; entailer!.
Qed.

Lemma mbox_pend_modular_restore_unowned_output : forall external platform port critical saved_local
  sg call returned mask released current,
  kernel_resumption_task_source_trace external port critical.(critical_region_clients) sg
    call.(os_sched_call_invocation) None call.(os_sched_call_origin) released false
    returned.(os_sched_call_origin) current ->
  kernel_call_normal_return call released returned current ->
  mutex_query_closed platform critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) mask current ** os_sched_context_resources external returned ** unmap_table_rep sg |--
  mbox_pend_restore_output None external platform None critical saved_local sg call mask released.
Proof.
  intros * Htrace Hnormal; pose proof (proj1 Hnormal) as [Hi [Ho Hs]].
  assert (Hhistory : q_pend_call_history external None critical sg call released returned current)
    by (exists port; auto).
  unfold mbox_pend_restore_output; Exists returned current.
  unfold sem_pend_continuation_save_input, sem_pend_optional_continuation_resources.
  rewrite Hi, Ho; entailer!.
Qed.

Lemma mbox_pend_save_output_split_message : forall external platform environment critical saved_local
  sg original pe eid observed mask saved before,
  mbox_pend_save_output (MboxPendAcquirePhase pe eid observed) external platform environment
    critical saved_local sg original mask saved before |--
  EX entered entry current mailbox,
    mbox_pend_message_frame external platform environment critical saved_local sg original entered
      mask saved pe before entry eid observed current mailbox **
    (event_addr sg eid + OSEventPtr_off) # Ptr |-> mbox_message_ptr mailbox.
Proof.
  intros; unfold mbox_pend_save_output; Intros entered entry.
  assert (Hphase : mbox_pend_save_phase_observation (MboxPendAcquirePhase pe eid observed)
    external environment critical sg original entered mask saved before entry) by assumption.
  pose proof Hphase as [Hhistory [Hsaved [current [Hfacts Hempty]]]].
  pose proof Hfacts as [Hinterval [Hvalid [Hs [Hlookup [Hcurrent [Htype [Htype' Hgen]]]]]]].
  destruct (mbox_accept_current_payload sg entry eid current Hvalid Hcurrent Htype') as [mailbox Hmailbox].
  rewrite (UCOS2_inv_split_event_queue sg entry).
  Intros.
  sep_apply_l_atomic (event_raw_rep_split_eid sg entry.(TskState) entry.(EventState) eid current Hcurrent).
  sep_apply_l_atomic (mbox_rep_split_message sg entry.(TskState) eid current mailbox Htype' Hmailbox).
  Exists entered entry current mailbox; unfold mbox_pend_message_frame; entailer!.
Qed.

Lemma mbox_pend_message_merge : forall external platform environment critical saved_local
  sg original entered mask saved pe before entry eid observed current mailbox,
  mbox_pend_message_frame external platform environment critical saved_local sg original entered
    mask saved pe before entry eid observed current mailbox **
  (event_addr sg eid + OSEventPtr_off) # Ptr |-> mbox_message_ptr mailbox |--
  coq_prop (mbox_pend_save_phase_observation (MboxPendAcquirePhase pe eid observed)
    external environment critical sg original entered mask saved before entry /\
    mbox_pend_acquire_facts critical sg original.(os_sched_call_invocation)
      eid mask saved before entry observed current /\ current.(mboxFields) = Some mailbox) &&
  (mbox_pend_masked_frame external platform environment critical saved_local sg entered saved entry entry **
    UCOS2_inv sg entry).
Proof.
  intros; unfold mbox_pend_message_frame; Intros.
  assert (Hfacts : mbox_pend_acquire_facts critical sg original.(os_sched_call_invocation)
    eid mask saved before entry observed current) by tauto.
  assert (Hfields : current.(mboxFields) = Some mailbox) by tauto.
  pose proof Hfacts as [Hinterval [Hvalid [Hs [Hlookup [Hcurrent [Htype [Htype' Hgen]]]]]]].
  sep_apply_l_atomic (mbox_rep_merge_updated_message sg entry.(TskState) eid current mailbox Htype').
  rewrite (mbox_set_message_same current mailbox Hfields).
  sep_apply_l_atomic (event_raw_rep_merge_eid sg entry.(TskState) entry.(EventState) eid current Hcurrent).
  rewrite (UCOS2_inv_split_event_queue sg entry); entailer!.
Qed.

Lemma mbox_pend_message_take_checkpoint : forall external platform environment critical saved_local
  sg original entered mask saved pe before entry eid observed current mailbox timeout,
  mbox_message_ptr mailbox <> 0 ->
  mbox_pend_message_frame external platform environment critical saved_local sg original entered
    mask saved pe before entry eid observed current mailbox **
  (event_addr sg eid + OSEventPtr_off) # Ptr |-> 0 |--
  coq_prop (mbox_pend_immediate_checkpoint external environment critical sg original before entered entry
    eid timeout (mbox_message_ptr mailbox) (mbox_accept_update entry eid current mailbox)) &&
  mbox_pend_restore_input None external platform environment critical saved_local sg entered mask saved
    entry (mbox_accept_update entry eid current mailbox).
Proof.
  intros * Hnonzero; unfold mbox_pend_message_frame; Intros.
  assert (Hphase : mbox_pend_save_phase_observation (MboxPendAcquirePhase pe eid observed)
    external environment critical sg original entered mask saved before entry) by tauto.
  assert (Hfacts : mbox_pend_acquire_facts critical sg original.(os_sched_call_invocation)
    eid mask saved before entry observed current) by tauto.
  assert (Hfields : current.(mboxFields) = Some mailbox) by tauto.
  pose proof Hfacts as [Hinterval [Hvalid [Hs [Hlookup [Hcurrent [Htype [Htype' Hgen]]]]]]].
  assert (Hcheckpoint : mbox_pend_immediate_checkpoint external environment critical sg original before
    entered entry eid timeout (mbox_message_ptr mailbox) (mbox_accept_update entry eid current mailbox)).
  { split; [exact (proj1 Hphase)|].
    exists current, mailbox; split; [exact Hcurrent|]. split; [exact Hfields|].
    rewrite (proj2 (Z.eqb_neq _ _) Hnonzero); auto. }
  sep_apply_l_atomic (mbox_accept_message_merge_updated sg entry eid current mailbox Hvalid Hcurrent Htype').
  assert (Hframe : mbox_pend_masked_frame external platform environment critical saved_local sg entered saved entry entry =
    mbox_pend_masked_frame external platform environment critical saved_local sg entered saved entry
      (mbox_accept_update entry eid current mailbox)) by reflexivity.
  rewrite Hframe; unfold mbox_pend_restore_input; entailer!.
Qed.
