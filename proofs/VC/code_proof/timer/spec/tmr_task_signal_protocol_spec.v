Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_signal_handle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_api_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.lib.kernel_runtime_inv.
Require Import Coq.Lists.List Coq.ZArith.ZArith.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.

(** [mutex_query_handle_protocol] is already a static registration
    property of critical/sg/invocation/eid.  It has no current-state index
    and owns no second copy of ECB bytes.  These bridges carry that SAME
    property; they do not re-establish Task admission at every callback. *)

Lemma tmr_task_signal_protocol_same_call_iff : forall critical sg original returned eid,
  task_tcb_init_stack_same_call returned original ->
  (mutex_query_handle_protocol critical sg returned.(os_sched_call_invocation) eid <->
   mutex_query_handle_protocol critical sg original.(os_sched_call_invocation) eid).
Proof. intros critical sg original returned eid [Hinv _]; rewrite Hinv; reflexivity. Qed.

Lemma tmr_task_signal_protocol_registered_clients : forall registered service sg invocation eid,
  (forall action, service.(critical_region_clients) action ->
    registered.(critical_region_clients) action) ->
  mutex_query_handle_protocol registered sg invocation eid ->
  mutex_query_handle_protocol service sg invocation eid.
Proof.
  intros registered service sg invocation eid Hclients Hprotocol
    action before after previous Hin Hforeign Hvalid Hstep Hlookup.
  exact (Hprotocol action before after previous (Hclients action Hin)
    Hforeign Hvalid Hstep Hlookup).
Qed.

(** The Init/Create caller and the future Timer task are not generally
    the same invocation. Changing the excluded actor needs a real extra
    environment obligation: the old owner, now foreign, must also preserve
    the handle. This theorem neither invents that obligation nor equates
    the Task invocation with Event allocation's event_actor namespace. *)
Lemma tmr_task_signal_protocol_change_invocation : forall critical sg original returned eid,
  mutex_query_handle_protocol critical sg original eid ->
  (forall action before after previous,
    critical.(critical_region_clients) action ->
    kernel_client_actor action = Some original ->
    kernel_client_actor action <> Some returned ->
    UCOS2_state_inv sg before -> kernel_client_step action sg before after ->
    mutex_query_lookup before eid previous ->
    exists current, mutex_query_lookup after eid current /\
      current.(eventGeneration) = previous.(eventGeneration) /\
      current.(eventType) = previous.(eventType)) ->
  mutex_query_handle_protocol critical sg returned eid.
Proof.
  intros critical sg original returned eid Hprotocol Hformer
    action before after previous Hin Hforeign Hvalid Hstep Hlookup.
  destruct (kernel_client_actor action) as [actor|] eqn:Hactor.
  - destruct (Nat.eq_dec actor original) as [Heq|Hneq].
    + subst actor; eapply Hformer; try eassumption; congruence.
    + apply (Hprotocol action before after previous Hin); try assumption; congruence.
  - apply (Hprotocol action before after previous Hin); try assumption; congruence.
Qed.

Lemma tmr_task_signal_service_value : forall before after,
  tmr_task_service_frame before after -> after.(timerSignalSem) = before.(timerSignalSem).
Proof. intros before after [_ [_ [Hsignal _]]]; exact Hsignal. Qed.

Lemma tmr_task_signal_public_step_value : forall sg before after,
  timer_public_step sg before after -> after.(timerSignalSem) = before.(timerSignalSem).
Proof.
  intros sg before after Hstep; destruct Hstep.
  - reflexivity.
  - unfold timer_allocate in H.
    destruct before.(timerFree) as [|selected rest] in H; [discriminate|].
    destruct (before.(timerImages) selected) in H; [|discriminate].
    inversion H; subst; reflexivity.
  - reflexivity.
  - apply tmr_task_signal_service_value; eapply tmr_task_link_service_frame; exact H.
  - apply tmr_task_signal_service_value; eapply tmr_task_unlink_service_frame; exact H.
  - apply tmr_task_signal_service_value; eapply tmr_task_complete_service_frame; exact H.
  - reflexivity.
Qed.

Lemma tmr_task_signal_public_trace_value : forall sg before after,
  timer_public_trace sg before after -> after.(timerSignalSem) = before.(timerSignalSem).
Proof.
  intros sg before after Htrace; induction Htrace; [reflexivity|].
  rewrite IHHtrace; eapply tmr_task_signal_public_step_value; exact H.
Qed.

Lemma tmr_task_signal_interval_value : forall critical sg invocation before after,
  critical_region_interval critical sg invocation before after ->
  after.(TimerState).(timerSignalSem) = before.(TimerState).(timerSignalSem).
Proof.
  intros critical sg invocation before after Hinterval.
  apply (tmr_task_signal_public_trace_value sg).
  exact (critical_region_interval_timer_public_trace critical sg invocation before after Hinterval).
Qed.

Lemma tmr_task_signal_finish_value : forall before receipt after,
  timer_finish_initialization before receipt = Some after ->
  after.(timerSignalSem) = before.(timerSignalSem).
Proof.
  intros before receipt after Hfinish; unfold timer_finish_initialization in Hfinish.
  destruct before.(timerInitPhase) eqn:Hphase in Hfinish;
    try discriminate; inversion Hfinish; reflexivity.
Qed.

(** Registration supplies only the static live-handle protocol for the
    actual successful address, targeted at the SERVICE invocation.  Create
    itself supplies the pointer, current public SEM and ID bound. It cannot
    prove the behavior of future registered clients. The initializer's
    create_invocation is deliberately a different parameter. *)
Lemma tmr_task_signal_create_registered_handle :
  forall critical sg create_invocation service_invocation count before signal current timers,
  sem_create_api_program critical sg create_invocation count before signal current ->
  UCOS2_state_inv sg current -> signal <> 0 ->
  timer_record_signal_result current.(TimerState) signal = Some timers ->
  (forall eid, signal = event_addr sg eid ->
    mutex_query_handle_protocol critical sg service_invocation eid) ->
  exists eid observed,
    timers.(timerSignalSem) = event_addr sg eid /\ valid_event_id sg eid /\
    mutex_query_lookup current eid observed /\ observed.(eventType) = OS_EVENT_TYPE_SEM /\
    mutex_query_handle_protocol critical sg service_invocation eid.
Proof.
  intros critical sg create_invocation service_invocation count before signal current timers
    Hcreate Hvalid Hnonnull Hstore Hregister.
  destruct (tmr_task_signal_create_published_slot critical sg create_invocation count
    before signal current Hcreate Hnonnull) as [eid [observed [Haddress [Hlookup Htype]]]].
  pose proof Hvalid as [_ [_ [_ [[Hpool _] _]]]].
  pose proof (proj1 (event_pool_used_not_free sg current.(EventState) eid observed Hpool Hlookup)) as Hid.
  exists eid, observed.
  split; [rewrite (tmr_task_signal_recorded_value _ _ _ Hstore); exact Haddress|].
  split; [exact Hid|]. split; [exact Hlookup|]. split; [exact Htype|].
  apply Hregister; exact Haddress.
Qed.

Lemma tmr_task_signal_handle_after_service : forall critical sg original returned before after eid,
  task_tcb_init_stack_same_call returned original -> tmr_task_service_frame before after ->
  before.(timerSignalSem) = event_addr sg eid ->
  mutex_query_handle_protocol critical sg original.(os_sched_call_invocation) eid ->
  after.(timerSignalSem) = event_addr sg eid /\
  mutex_query_handle_protocol critical sg returned.(os_sched_call_invocation) eid.
Proof.
  intros critical sg original returned before after eid Hsame Hframe Haddress Hprotocol.
  split.
  - rewrite (tmr_task_signal_service_value _ _ Hframe); exact Haddress.
  - apply (proj2 (tmr_task_signal_protocol_same_call_iff critical sg original returned eid Hsame));
      exact Hprotocol.
Qed.

(** Public-slot ownership is a CURRENT endpoint fact. Its observed node
    may differ from the Create node and the public alternative may be FREE.
    Only the immutable numerical binding and static protocol are carried. *)
Lemma tmr_task_signal_input_after_service :
  forall critical sg original returned before current eid observed,
  task_tcb_init_stack_same_call returned original ->
  tmr_task_service_frame before current.(TimerState) ->
  before.(timerSignalSem) <> 0 -> before.(timerSignalSem) = event_addr sg eid ->
  valid_event_id sg eid ->
  mutex_query_handle_protocol critical sg original.(os_sched_call_invocation) eid ->
  sem_query_public_slot current eid observed ->
  sem_pend_call_input critical sg returned.(os_sched_call_invocation)
    current.(TimerState).(timerSignalSem) current eid observed.
Proof.
  intros critical sg original returned before current eid observed Hsame Hframe
    Hnonnull Haddress Hid Hprotocol Hpublic.
  destruct (tmr_task_signal_handle_after_service critical sg original returned before
    current.(TimerState) eid Hsame Hframe Haddress Hprotocol) as [Hcurrent Hcarried].
  right; split.
  - rewrite (tmr_task_signal_service_value _ _ Hframe); exact Hnonnull.
  - split; [exact Hcurrent|]. split; [exact Hid|]. split; [exact Hpublic|].
    intros; exact Hcarried.
Qed.

(** The actual Scheduler strong post exposes CURRENT_READY, rather than
    its source constructor. Consume that real post directly; do not create
    a ready-source receipt by reversing an implication. *)
Lemma tmr_task_pend_stage_from_current_ready : forall sg call state,
  kernel_call_task_source call state -> state.(SchedState).(isRunning) = true ->
  os_sched_task_current_ready call state ->
  (forall node,
    state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
    node.(curPrio) <> sg.(osLowestPrio) /\ sem_pend_task_unregistered node) ->
  sem_pend_task_call_stage sg call state.
Proof.
  intros sg call state Hsource Hrunning [node [Hready Hgeneration]] Hfields.
  destruct (Hfields node (proj1 Hready)) as [Hnonidle [Hevent [Hmulti Hflag]]].
  split; [exact Hsource|]. split; [exact Hrunning|]. exists node.
  split; [exact Hready|]. split; [exact Hgeneration|]. repeat split; assumption.
Qed.

Lemma tmr_task_signal_wait_after_service :
  forall Application environment critical sg original returned before
    (world : tmr_task_scan_world Application) eid observed,
  task_tcb_init_stack_same_call returned original ->
  tmr_task_service_frame before (tmr_task_timers world) ->
  before.(timerSignalSem) <> 0 -> before.(timerSignalSem) = event_addr sg eid ->
  valid_event_id sg eid ->
  mutex_query_handle_protocol critical sg original.(os_sched_call_invocation) eid ->
  sem_query_public_slot (fst world) eid observed ->
  sem_pend_task_call_stage sg returned (fst world) ->
  kernel_running_idle_ready sg (fst world) -> kernel_call_stack_available returned (fst world) ->
  event_table_layout_prop sg ->
  tmr_task_wait_instance environment critical sg returned world eid observed.
Proof.
  intros Application environment critical sg original returned before world eid observed
    Hsame Hframe Hnonnull Haddress Hid Hprotocol Hpublic Hstage Hidle Havailable Hlayout.
  apply tmr_task_wait_instance_task_boundary; try assumption.
  eapply tmr_task_signal_input_after_service; eassumption.
Qed.

(** Error consumers have NO static handle-protocol premise. Even if an
    environment has not registered that protocol, the real ordered early
    error can be composed once its current public Type bytes are owned. *)
Lemma tmr_task_signal_error_input : forall critical sg invocation signal current eid observed error,
  signal <> 0 -> signal = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot current eid observed ->
  sem_pend_precritical_error signal (event_slot_type_value current.(EventState) eid)
    current.(IntrState).(intNesting) current.(IntrState).(lockNesting) = Some error ->
  sem_pend_call_input critical sg invocation signal current eid observed.
Proof.
  intros critical sg invocation signal current eid observed error
    Hnonnull Haddress Hid Hpublic Herror.
  right; split; [exact Hnonnull|]. split; [exact Haddress|]. split; [exact Hid|].
  split; [exact Hpublic|]. intros Htype Hint Hlock.
  unfold sem_pend_precritical_error, sem_pend_context_error in Herror.
  rewrite (proj2 (Z.eqb_neq _ _) Hnonnull), Htype in Herror.
  cbn [encode_event_type] in Herror.
  rewrite (proj2 (Z.ltb_ge _ _) Hint), (proj2 (Z.ltb_ge _ _) Hlock) in Herror.
  discriminate.
Qed.

Lemma tmr_task_signal_error_wait :
  forall Application environment critical sg call (world : tmr_task_scan_world Application)
    eid observed error,
  (tmr_task_timers world).(timerSignalSem) <> 0 ->
  (tmr_task_timers world).(timerSignalSem) = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot (fst world) eid observed ->
  sem_pend_precritical_error (tmr_task_timers world).(timerSignalSem)
    (event_slot_type_value (fst world).(EventState) eid)
    (fst world).(IntrState).(intNesting) (fst world).(IntrState).(lockNesting) = Some error ->
  event_table_layout_prop sg ->
  tmr_task_wait_instance environment critical sg call world eid observed.
Proof.
  intros Application environment critical sg call world eid observed error
    Hnonnull Haddress Hid Hpublic Herror Hlayout.
  eapply tmr_task_wait_instance_early_error; [|exact Herror|exact Hlayout].
  eapply tmr_task_signal_error_input; eassumption.
Qed.

Lemma tmr_task_signal_null_wait :
  forall Application environment critical sg call (world : tmr_task_scan_world Application) eid observed,
  (tmr_task_timers world).(timerSignalSem) = 0 -> event_table_layout_prop sg ->
  tmr_task_wait_instance environment critical sg call world eid observed.
Proof.
  intros Application environment critical sg call world eid observed Hnull Hlayout.
  eapply tmr_task_wait_instance_early_error with (error := OS_ERR_PEVENT_NULL).
  - rewrite Hnull; apply tmr_task_pend_input_null.
  - rewrite Hnull; apply sem_pend_precritical_null.
  - exact Hlayout.
Qed.
