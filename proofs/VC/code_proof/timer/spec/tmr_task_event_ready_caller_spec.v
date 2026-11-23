Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Relations.Relation_Operators.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_sem_source_projection_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_api_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_abort_source_api_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_del_source_api_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_pend_abort_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_pend_abort_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_post_opt_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_del_spec.
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_post_opt_spec.
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_pend_abort_spec.
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_del_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_post_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_post_api_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_post_call_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_post_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.lib.borrowable_region.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Retain the actual caller's local information alongside its EXISTING
    source classification.  Only the raw EventReady constructor needs
    this information; no action, registry member or public helper domain
    is changed.  In particular the receipt never asserts a future return. *)
Inductive tmr_task_source_call_receipt external :
  KernelClientAction -> StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| TmrTaskCallNontimer : forall action sg before after,
    tmr_task_nontimer_source_client action -> kernel_client_step action sg before after ->
    tmr_task_source_call_receipt external action sg before after
| TmrTaskCallProfile : forall cut sg before after,
    kernel_client_step (kernel_full_profile_cut_client cut) sg before after ->
    tmr_task_source_call_receipt external (kernel_full_profile_cut_client cut) sg before after
| TmrTaskCallChangePrio : forall actor requested priority sg before after,
    kernel_client_step (task_change_prio_critical_client actor requested priority) sg before after ->
    tmr_task_source_call_receipt external (task_change_prio_critical_client actor requested priority) sg before after
| TmrTaskCallFlagReady : forall actor pointer bits result sg before after,
    kernel_client_step (flag_task_rdy_source_client actor pointer bits result) sg before after ->
    tmr_task_source_call_receipt external (flag_task_rdy_source_client actor pointer bits result) sg before after
| TmrTaskCallEventReady : forall actor event kind message result sg before after,
    tmr_task_sem_event_ready_call_input sg before event kind result ->
    kernel_client_step (event_task_rdy_source_client actor event kind message result) sg before after ->
    tmr_task_source_call_receipt external (event_task_rdy_source_client actor event kind message result) sg before after
| TmrTaskCallTickTask : forall slot previous sg before after,
    kernel_client_step (time_tick_task_source_client slot previous) sg before after ->
    tmr_task_source_call_receipt external (time_tick_task_source_client slot previous) sg before after
| TmrTaskCallInstall : forall context outgoing incoming resumed sg before after,
    kernel_client_step (os_sched_install_client external context outgoing incoming resumed) sg before after ->
    tmr_task_source_call_receipt external
      (os_sched_install_client external context outgoing incoming resumed) sg before after
| TmrTaskCallSem : forall action sg before after,
    tmr_task_sem_source_client action -> kernel_client_step action sg before after ->
    tmr_task_source_call_receipt external action sg before after
| TmrTaskCallCritical : forall action sg before after,
    tmr_task_critical_source_client action -> kernel_client_step action sg before after ->
    tmr_task_source_call_receipt external action sg before after
| TmrTaskCallTick : forall actor cut sg before after,
    kernel_client_step (tmr_task_tick_source_client actor cut) sg before after ->
    tmr_task_source_call_receipt external (tmr_task_tick_source_client actor cut) sg before after
| TmrTaskCallTimer : forall actor cut sg before after,
    kernel_client_step (tmr_task_timer_source_client actor cut) sg before after ->
    tmr_task_source_call_receipt external (tmr_task_timer_source_client actor cut) sg before after
| TmrTaskCallTimerCall : forall actor source_sg cut entry timers sg before after,
    kernel_client_step (tmr_task_timer_call_client actor source_sg cut entry timers) sg before after ->
    tmr_task_source_call_receipt external
      (tmr_task_timer_call_client actor source_sg cut entry timers) sg before after
| TmrTaskCallSemAbort : forall actor event option result sg before after,
    kernel_client_step (tmr_task_sem_abort_call_client actor event option result) sg before after ->
    tmr_task_source_call_receipt external (tmr_task_sem_abort_call_client actor event option result) sg before after
| TmrTaskCallSuspend : forall actor source_sg priority result entry returned sg before after,
    kernel_client_step (tmr_task_suspend_call_client actor source_sg priority result entry returned) sg before after ->
    tmr_task_source_call_receipt external
      (tmr_task_suspend_call_client actor source_sg priority result entry returned) sg before after.

Lemma tmr_task_source_call_receipt_source : forall external action sg before after,
  tmr_task_source_call_receipt external action sg before after -> tmr_task_source_client external action.
Proof.
  intros external action sg before after Hcall; destruct Hcall.
  - apply TmrTaskSourceScheduler, TmrTaskSchedulerNontimer; assumption.
  - apply TmrTaskSourceScheduler, TmrTaskSchedulerProfile.
  - apply TmrTaskSourceScheduler, TmrTaskSchedulerChangePrio.
  - apply TmrTaskSourceScheduler, TmrTaskSchedulerFlagReady.
  - apply TmrTaskSourceScheduler, TmrTaskSchedulerEventReady.
  - apply TmrTaskSourceScheduler, TmrTaskSchedulerTickTask.
  - apply TmrTaskSourceScheduler, TmrTaskSchedulerTaskInstall.
  - apply TmrTaskSourceSem; assumption.
  - apply TmrTaskSourceCritical; assumption.
  - apply TmrTaskSourceTick.
  - apply TmrTaskSourceTimer.
  - apply TmrTaskSourceTimerCall.
  - apply TmrTaskSourceSemAbortCall.
  - apply TmrTaskSourceSuspendCall.
Qed.

Lemma tmr_task_source_call_receipt_step : forall external action sg before after,
  tmr_task_source_call_receipt external action sg before after -> kernel_client_step action sg before after.
Proof. intros external action sg before after Hcall; destruct Hcall; assumption. Qed.

Lemma tmr_task_source_call_projection : forall external action sg before after tid old eid generation,
  tmr_task_source_call_receipt external action sg before after -> UCOS2_state_inv sg before ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros external action sg before after tid old eid generation Hcall Hvalid Hold Hcont.
  destruct Hcall as [action0 sg0 before0 after0 Hnontimer Hstep|cut sg0 before0 after0 Hstep|
    actor requested priority sg0 before0 after0 Hstep|actor pointer bits result sg0 before0 after0 Hstep|
    actor event kind message result sg0 before0 after0 Hinput Hstep|slot previous sg0 before0 after0 Hstep|
    context outgoing incoming resumed sg0 before0 after0 Hstep|action0 sg0 before0 after0 Hsem Hstep|
    action0 sg0 before0 after0 Hcritical Hstep|actor cut sg0 before0 after0 Hstep|
    actor cut sg0 before0 after0 Hstep|actor source_sg cut entry timers sg0 before0 after0 Hstep|
    actor event option result sg0 before0 after0 Hstep|
    actor source_sg priority result entry returned sg0 before0 after0 Hstep].
  - eapply tmr_task_sem_nontimer_projection; eassumption.
  - eapply tmr_task_sem_profile_projection; eassumption.
  - destruct Hstep as [code Hstep]; eapply tmr_task_sem_change_prio_projection; eassumption.
  - destruct Hstep as [schedule Hstep]; eapply tmr_task_sem_flag_ready_projection; eassumption.
  - eapply tmr_task_sem_event_ready_call_projection; eassumption.
  - destruct Hstep as [Hprevious ->]; eapply sem_pend_tick_task_projection; eassumption.
  - eapply sem_pend_source_client_projection;
      [apply SemPendSourceSchedulerInstall|exact Hstep|exact Hold].
  - eapply sem_pend_source_client_projection;
      [apply tmr_task_sem_source_client_wait_projection; exact Hsem|exact Hstep|exact Hold].
  - eapply tmr_task_sem_critical_projection; eassumption.
  - exact (tmr_task_sem_tick_projection _ cut _ _ _ _ Hstep Hold).
  - destruct Hstep as [timers [_ ->]]; eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - destruct Hstep as [_ [_ [_ ->]]]; eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - destruct Hstep as [node [_ [_ Habort]]]; eapply sem_pend_abort_critical_projection; eassumption.
  - eapply tmr_task_sem_suspend_projection; eassumption.
Qed.

Lemma tmr_task_event_ready_call_receipt : forall external actor event kind message result sg before after,
  tmr_task_sem_event_ready_call_input sg before event kind result ->
  kernel_client_step (event_task_rdy_source_client actor event kind message result) sg before after ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event kind message result) sg before after.
Proof.
  intros external actor event kind message result sg before after Hinput Hstep.
  apply TmrTaskCallEventReady; assumption.
Qed.

(** An annotation of the SAME resource-trace proof.  This is not another
    environment relation: there is no replacement of clients, actors,
    transitions, task/Event observers, stopped bit, or endpoints.  Call
    producers retain the receipt at each constructor when building Htrace. *)
Inductive tmr_task_source_trace_calls (external : OsSchedExternalResources)
  (clients : KernelClientAction -> Prop) (sg : StableGlobVars)
  (observer : nat) (event_observer : option nat) :
  forall before stopped after,
    kernel_client_resource_trace clients sg observer event_observer before stopped after -> Prop :=
| TmrTaskSourceTraceCallsNil : forall state,
    tmr_task_source_trace_calls external clients sg observer event_observer state false state
      (@KernelClientTraceNil clients sg observer event_observer state)
| TmrTaskSourceTraceCallsStep : forall action before middle after stopped
    (member : clients action) (foreign : kernel_client_actor action <> Some observer)
    (event_foreign : forall invocation, event_observer = Some invocation ->
      kernel_client_event_actor action <> Some invocation)
    (step : kernel_client_step action sg before middle)
    (tail : kernel_client_resource_trace clients sg observer event_observer middle stopped after),
    tmr_task_source_call_receipt external action sg before middle ->
    tmr_task_source_trace_calls external clients sg observer event_observer middle stopped after tail ->
    tmr_task_source_trace_calls external clients sg observer event_observer before
      (orb (kernel_client_stops action observer) stopped) after
      (@KernelClientTraceStep clients sg observer event_observer action before middle after stopped
        member foreign event_foreign step tail).

Lemma tmr_task_source_trace_calls_projection :
  forall external critical sg observer event_observer before stopped after
    (trace : kernel_client_resource_trace critical.(critical_region_clients)
      sg observer event_observer before stopped after),
  tmr_task_source_trace_calls external critical.(critical_region_clients) sg observer event_observer
    before stopped after trace ->
  UCOS2_state_inv sg before ->
  forall tid old eid generation,
    before.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros external critical sg observer event_observer before stopped after trace Hcalls.
  induction Hcalls as [state|action before middle after stopped Hin Hforeign Hevent Hstep Htail Hcall Hcalls IH];
    intros Hvalid tid old eid generation Hold Hcont.
  - apply sem_pend_task_projection_refl; exact Hold.
  - assert (Hmiddle : UCOS2_state_inv sg middle).
    { eapply kernel_client_preserves_validity;
        [apply (critical_region_client_certificates critical); exact Hin|exact Hvalid|exact Hstep]. }
    destruct (tmr_task_source_call_projection external action sg before middle tid old eid generation
      Hcall Hvalid Hold Hcont) as [current [Hcurrent Hfirst]].
    assert (Hcontinue : sem_pend_wait_continuation eid generation current).
    { eapply sem_pend_wait_trace_preserves_continuation; eassumption. }
    destruct (IH Hmiddle tid current eid generation Hcurrent Hcontinue) as [last [Hlast Hsecond]].
    exists last; split; [exact Hlast|eapply rt_trans; eassumption].
Qed.

Lemma tmr_task_source_trace_calls_preserves_continuation :
  forall external critical sg observer event_observer before stopped after
    (trace : kernel_client_resource_trace critical.(critical_region_clients)
      sg observer event_observer before stopped after) tid old eid generation,
  tmr_task_source_trace_calls external critical.(critical_region_clients) sg observer event_observer
    before stopped after trace ->
  UCOS2_state_inv sg before -> before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  exists current, after.(TskState).(inUsedTaskStates) tid = Some current /\
    sem_pend_wait_continuation eid generation current.
Proof.
  intros external critical sg observer event_observer before stopped after trace tid old eid generation
    Hcalls Hvalid Hold Hcont.
  destruct (tmr_task_source_trace_calls_projection external critical sg observer event_observer before
    stopped after trace Hcalls Hvalid tid old eid generation Hold Hcont)
    as [current [Hcurrent Heffects]].
  exists current; split; [exact Hcurrent|].
  eapply sem_pend_wait_trace_preserves_continuation; eassumption.
Qed.

(** The helper's protected call site has already read this EventGrp and
    retained this live object.  Its actual typed arguments are supplied
    here.  In particular the generic helper contract is not strengthened. *)
Lemma tmr_task_event_ready_group_call_receipt :
  forall external actor sg before after event node kind message result priority,
  before.(EventState).(inUsedEventStates) event = Some node ->
  encode_event_wait_grp node.(waitList) before.(TskState) <> 0 ->
  event_type_to_pend_type node.(eventType) = Some kind -> result <> PendTimeout ->
  event_task_rdy sg before event kind message result = Some (priority, after) ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event kind message result) sg before after.
Proof.
  intros external actor sg before after event node kind message result priority
    Hnode Hgroup Hkind Hresult Hcall.
  apply tmr_task_event_ready_call_receipt.
  - eapply tmr_task_sem_event_ready_call_input_from_group; eassumption.
  - exists priority; exact Hcall.
Qed.

Lemma tmr_task_sem_post_critical_call_receipt :
  forall external actor sg before after event node error,
  before.(EventState).(inUsedEventStates) event = Some node ->
  node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_critical sg event before (error, true) after ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event PendSem 0 PendOK) sg before after.
Proof.
  intros external actor sg before after event node error Hnode Htype [actual [Hactual Hsource]].
  assert (actual = node) by congruence; subst actual.
  destruct (Z.eqb (encode_event_wait_grp node.(waitList) before.(TskState)) 0) eqn:Hgroup.
  - destruct Hsource as [fields [_ Hsource]]; destruct (Z.ltb fields.(semCount) 65535);
      destruct Hsource as [Hresult _]; discriminate.
  - destruct Hsource as [_ [priority Hcall]].
    eapply tmr_task_event_ready_group_call_receipt;
      [exact Hnode|apply Z.eqb_neq; exact Hgroup|rewrite Htype; reflexivity|discriminate|exact Hcall].
Qed.

(** The acquired Sem type/generation come from the existing handle
    protocol through Save.  A pre-Save type observation is not reused as
    if Save had left the object unchanged. *)
Lemma tmr_task_sem_post_acquired_call_receipt :
  forall external actor environment critical sg original active mask saved before acquired after
    event observed current priority,
  sem_post_api_acquire_facts environment critical sg original active mask saved before acquired
    event observed current ->
  encode_event_wait_grp current.(waitList) acquired.(TskState) <> 0 ->
  event_task_rdy sg acquired event PendSem 0 PendOK = Some (priority, after) ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event PendSem 0 PendOK) sg acquired after /\
  current.(eventGeneration) = observed.(eventGeneration).
Proof.
  intros external actor environment critical sg original active mask saved before acquired after
    event observed current priority [_ [_ [_ [Hcurrent [Htype Hgeneration]]]]] Hgroup Hcall.
  split; [|exact Hgeneration].
  eapply tmr_task_event_ready_group_call_receipt;
    [exact Hcurrent|exact Hgroup|rewrite Htype; reflexivity|discriminate|exact Hcall].
Qed.

Lemma tmr_task_q_post_acquired_call_receipt :
  forall external actor environment critical sg original active mask saved before acquired after
    event observed current message priority,
  q_post_acquire_facts environment critical sg original active mask saved before acquired
    event observed current ->
  encode_event_wait_grp current.(waitList) acquired.(TskState) <> 0 ->
  event_task_rdy sg acquired event PendQ message PendOK = Some (priority, after) ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event PendQ message PendOK) sg acquired after /\
  current.(eventGeneration) = observed.(eventGeneration).
Proof.
  intros external actor environment critical sg original active mask saved before acquired after
    event observed current message priority [_ [_ [_ [Hcurrent [Htype Hgeneration]]]]] Hgroup Hcall.
  split; [|exact Hgeneration].
  eapply tmr_task_event_ready_group_call_receipt;
    [exact Hcurrent|exact Hgroup|rewrite Htype; reflexivity|discriminate|exact Hcall].
Qed.

Lemma tmr_task_mbox_post_acquired_call_receipt :
  forall external actor environment critical sg original active mask saved pe message before acquired after
    event observed current priority,
  mbox_post_acquire_facts environment critical sg original active mask saved pe message before acquired
    event observed current ->
  encode_event_wait_grp current.(waitList) acquired.(TskState) <> 0 ->
  event_task_rdy sg acquired event PendMbox message PendOK = Some (priority, after) ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event PendMbox message PendOK) sg acquired after /\
  current.(eventGeneration) = observed.(eventGeneration).
Proof.
  intros external actor environment critical sg original active mask saved pe message before acquired after
    event observed current priority
    [_ [_ [_ [_ [_ [_ [_ [Hcurrent [Htype Hgeneration]]]]]]]]] Hgroup Hcall.
  split; [|exact Hgeneration].
  eapply tmr_task_event_ready_group_call_receipt;
    [exact Hcurrent|exact Hgroup|rewrite Htype; reflexivity|discriminate|exact Hcall].
Qed.

(** Back, Front and all Options values retain their actual branch.  The
    NO_SCHED option does not prevent the wake call or its source receipt. *)
Lemma tmr_task_q_post_single_call_receipt :
  forall external actor sg post_kind before after event node message result,
  before.(EventState).(inUsedEventStates) event = Some node ->
  node.(eventType) = OS_EVENT_TYPE_Q ->
  encode_event_wait_grp node.(waitList) before.(TskState) <> 0 ->
  q_post_broadcast_requested post_kind = false ->
  q_post_critical sg post_kind event message before result after ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event PendQ message PendOK) sg before after.
Proof.
  intros external actor sg post_kind before after event node message result
    Hnode Htype Hgroup Hsingle [actual [Hactual Hsource]].
  assert (actual = node) by congruence; subst actual.
  rewrite (proj2 (Z.eqb_neq _ _) Hgroup) in Hsource.
  destruct Hsource as [_ Hsource]; rewrite Hsingle in Hsource.
  destruct Hsource as [priority Hcall].
  eapply tmr_task_event_ready_group_call_receipt;
    [exact Hnode|exact Hgroup|rewrite Htype; reflexivity|discriminate|exact Hcall].
Qed.

Lemma tmr_task_mbox_post_single_call_receipt :
  forall external actor sg before after event node message result,
  q_post_lookup before event node -> node.(eventType) = OS_EVENT_TYPE_MBOX ->
  q_post_group before node <> 0 -> mbox_post_critical sg event message before result after ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event PendMbox message PendOK) sg before after.
Proof.
  intros external actor sg before after event node message result Hnode Htype Hgroup
    [actual [Hactual Hsource]].
  assert (actual = node) by congruence; subst actual.
  rewrite (proj2 (Z.eqb_neq _ _) Hgroup) in Hsource.
  destruct Hsource as [_ [priority Hcall]].
  eapply tmr_task_event_ready_group_call_receipt;
    [exact Hnode|exact Hgroup|rewrite Htype; reflexivity|discriminate|exact Hcall].
Qed.

Lemma tmr_task_mbox_post_opt_single_call_receipt :
  forall external actor sg before after event node message options result,
  q_post_lookup before event node -> node.(eventType) = OS_EVENT_TYPE_MBOX ->
  q_post_group before node <> 0 -> Z.land options 1 = 0 ->
  mbox_post_opt_critical sg event message options before result after ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event PendMbox message PendOK) sg before after.
Proof.
  intros external actor sg before after event node message options result Hnode Htype Hgroup Hsingle
    [actual [Hactual Hsource]].
  assert (actual = node) by congruence; subst actual.
  rewrite (proj2 (Z.eqb_neq _ _) Hgroup) in Hsource.
  destruct Hsource as [_ Hsource]; rewrite Hsingle in Hsource; cbn [Z.eqb] in Hsource.
  destruct Hsource as [priority Hcall].
  eapply tmr_task_event_ready_group_call_receipt;
    [exact Hnode|exact Hgroup|rewrite Htype; reflexivity|discriminate|exact Hcall].
Qed.

Lemma tmr_task_pend_abort_single_call_receipt :
  forall external actor sg before after event node kind option result,
  before.(EventState).(inUsedEventStates) event = Some node ->
  event_type_to_pend_type node.(eventType) = Some kind ->
  encode_event_wait_grp node.(waitList) before.(TskState) <> 0 -> option <> 1 ->
  event_pend_abort_critical sg event kind option before result after ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event kind 0 PendAbort) sg before after.
Proof.
  intros external actor sg before after event node kind option result Hnode Hkind Hgroup Hsingle
    [actual [Hactual Hsource]].
  assert (actual = node) by congruence; subst actual.
  rewrite (proj2 (Z.eqb_neq _ _) Hgroup), (proj2 (Z.eqb_neq _ _) Hsingle) in Hsource.
  destruct Hsource as [priority [Hcall _]].
  eapply tmr_task_event_ready_group_call_receipt;
    [exact Hnode|exact Hgroup|exact Hkind|discriminate|exact Hcall].
Qed.

Lemma tmr_task_sem_abort_single_call_receipt :
  forall external actor sg before after event node option result,
  before.(EventState).(inUsedEventStates) event = Some node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  encode_event_wait_grp node.(waitList) before.(TskState) <> 0 -> option <> 1 ->
  event_pend_abort_critical sg event PendSem option before result after ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event PendSem 0 PendAbort) sg before after.
Proof.
  intros external actor sg before after event node option result Hnode Htype Hgroup Hsingle Hsource.
  eapply tmr_task_pend_abort_single_call_receipt;
    [exact Hnode|rewrite Htype; reflexivity|exact Hgroup|exact Hsingle|exact Hsource].
Qed.

Lemma tmr_task_q_abort_single_call_receipt :
  forall external actor sg before after event node option result,
  before.(EventState).(inUsedEventStates) event = Some node -> node.(eventType) = OS_EVENT_TYPE_Q ->
  encode_event_wait_grp node.(waitList) before.(TskState) <> 0 -> option <> 1 ->
  q_pend_abort_critical sg event option before result after ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event PendQ 0 PendAbort) sg before after.
Proof.
  intros external actor sg before after event node option result Hnode Htype Hgroup Hsingle Hsource.
  eapply tmr_task_pend_abort_single_call_receipt;
    [exact Hnode|rewrite Htype; reflexivity|exact Hgroup|exact Hsingle|exact Hsource].
Qed.

Lemma tmr_task_mbox_abort_single_call_receipt :
  forall external actor sg before after event node option result,
  before.(EventState).(inUsedEventStates) event = Some node -> node.(eventType) = OS_EVENT_TYPE_MBOX ->
  encode_event_wait_grp node.(waitList) before.(TskState) <> 0 -> option <> 1 ->
  mbox_pend_abort_critical sg event option before result after ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event PendMbox 0 PendAbort) sg before after.
Proof.
  intros external actor sg before after event node option result Hnode Htype Hgroup Hsingle Hsource.
  eapply tmr_task_pend_abort_single_call_receipt;
    [exact Hnode|rewrite Htype; reflexivity|exact Hgroup|exact Hsingle|exact Hsource].
Qed.

Lemma tmr_task_mutex_wake_call_receipt :
  forall external actor sg before after event node mutex priority,
  mutex_del_wake_state_inv sg event mutex before ->
  before.(EventState).(inUsedEventStates) event = Some node ->
  encode_event_wait_grp node.(waitList) before.(TskState) <> 0 ->
  event_task_rdy sg before event PendMutex 0 PendAbort = Some (priority, after) ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event PendMutex 0 PendAbort) sg before after.
Proof.
  intros external actor sg before after event node mutex priority
    [actual [Hactual [Htype _]]] Hnode Hgroup Hcall.
  assert (actual = node) by congruence; subst actual.
  eapply tmr_task_event_ready_group_call_receipt;
    [exact Hnode|exact Hgroup|rewrite Htype; reflexivity|discriminate|exact Hcall].
Qed.

(** Consume the already verified generic helper's actual pre/post pair.
    The caller provides type/result facts at this call; the helper still
    accepts its original full byte domain.  No C statement is reproved. *)
Lemma tmr_task_event_ready_c_post_receipt :
  forall external actor sg entry event node selected old kind message result returned frame before after,
  entry.(EventState).(inUsedEventStates) event = Some node ->
  event_type_to_pend_type node.(eventType) = Some kind -> result <> PendTimeout ->
  (WakeComponent.event_ready_c_input sg entry event node selected old kind result ** frame) before ->
  (WakeComponent.event_ready_c_output sg entry event node selected old kind message result returned ** frame) after ->
  WakeComponent.kernel_wake_c_segment sg entry before
    (WakeComponent.event_ready_c_input sg entry event node selected old kind result ** frame)
    (event_wake_state sg entry event node selected old kind message result) after
    (WakeComponent.event_ready_c_output sg entry event node selected old kind message result returned ** frame) /\
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event kind message result) sg entry
    (event_wake_state sg entry event node selected old kind message result).
Proof.
  intros external actor sg entry event node selected old kind message result returned frame before after
    Hnode Hkind Hresult Hpre Hpost.
  pose proof Hpre as [body [rest [Hjoin [[[Hentry Hbytes] Hbody] Hrest]]]].
  split.
  - eapply WakeComponent.event_task_rdy_c_post_segment; eassumption.
  - apply tmr_task_event_ready_call_receipt.
    + eapply tmr_task_sem_event_ready_call_input_from_c_entry; eassumption.
    + exists old.(curPrio); eapply WakeComponent.event_task_rdy_c_entry_source; eassumption.
Qed.

(** Receipt annotation of the actual finite broadcast proof.  The empty
    branch performs no helper call.  Every other branch carries its own
    current EventGrp, queue head, selected TCB and actual returned state. *)
Inductive tmr_task_event_broadcast_calls (external : OsSchedExternalResources) (actor : option nat)
  (sg : StableGlobVars) (event : EventID) (kind : PendType) (message : Z) (result : PendStatus) :
  forall before priorities after,
    event_broadcast sg event kind message result before priorities after -> Prop :=
| TmrTaskEventBroadcastCallsDone : forall state node
    (lookup : state.(EventState).(inUsedEventStates) event = Some node)
    (empty : encode_event_wait_grp node.(waitList) state.(TskState) = 0),
    tmr_task_event_broadcast_calls external actor sg event kind message result state [] state
      (@event_broadcast_done sg event kind message result state node lookup empty)
| TmrTaskEventBroadcastCallsNext : forall state node priority middle priorities final
    (lookup : state.(EventState).(inUsedEventStates) event = Some node)
    (nonempty : encode_event_wait_grp node.(waitList) state.(TskState) <> 0)
    (step : event_task_rdy sg state event kind message result = Some (priority, middle))
    (tail : event_broadcast sg event kind message result middle priorities final),
    tmr_task_source_call_receipt external
      (event_task_rdy_source_client actor event kind message result) sg state middle ->
    tmr_task_event_broadcast_calls external actor sg event kind message result middle priorities final tail ->
    tmr_task_event_broadcast_calls external actor sg event kind message result state (priority :: priorities) final
      (@event_broadcast_next sg event kind message result state node priority middle priorities final
        lookup nonempty step tail).

Lemma tmr_task_event_broadcast_call_receipts :
  forall external actor sg event kind message result before priorities after
    (source : event_broadcast sg event kind message result before priorities after),
  UCOS2_state_inv sg before ->
  (exists node, before.(EventState).(inUsedEventStates) event = Some node /\
    event_type_to_pend_type node.(eventType) = Some kind) ->
  result <> PendTimeout ->
  tmr_task_event_broadcast_calls external actor sg event kind message result before priorities after source.
Proof.
  intros external actor sg event kind message result.
  fix IH 4.
  intros before priorities after source.
  destruct source as [state node Hnode Hzero|
    state node priority middle priorities final Hnode Hgroup Hstep Htail];
    intros Hvalid [actual [Hactual Hkind]] Hresult.
  - constructor.
  - assert (actual = node) by congruence; subst actual.
    constructor.
    + eapply tmr_task_event_ready_group_call_receipt; eassumption.
    + destruct (event_wake_decompose sg state event node kind message result priority middle
        Hvalid Hnode Hkind Hgroup Hstep)
        as [head [tail [old [Hlist [Hold [Hpriority [Hafter [Hmiddle Hlookup]]]]]]]].
      apply (IH _ _ _ Htail); [exact Hmiddle| |exact Hresult].
      exists (event_set_wait_list node tail); split; [exact Hlookup|exact Hkind].
Qed.

Lemma tmr_task_mutex_broadcast_call_receipts :
  forall external actor sg event mutex before priorities after
    (source : event_broadcast sg event PendMutex 0 PendAbort before priorities after),
  mutex_del_wake_state_inv sg event mutex before ->
  tmr_task_event_broadcast_calls external actor sg event PendMutex 0 PendAbort before priorities after source.
Proof.
  intros external actor sg event mutex.
  fix IH 4.
  intros before priorities after source.
  destruct source as [state node Hnode Hzero|
    state node priority middle priorities final Hnode Hgroup Hstep Htail];
    intro Hphase.
  - constructor.
  - constructor.
    + eapply tmr_task_mutex_wake_call_receipt; eassumption.
    + destruct (mutex_del_wake_decompose sg event mutex state node priority middle
        Hphase Hnode Hgroup Hstep) as [selected [old [_ [_ [_ [_ Hmiddle]]]]]].
      apply (IH _ _ _ Htail); exact Hmiddle.
Qed.

Lemma tmr_task_pend_abort_broadcast_call_receipts :
  forall external actor sg event node kind before result after,
  UCOS2_state_inv sg before -> before.(EventState).(inUsedEventStates) event = Some node ->
  event_type_to_pend_type node.(eventType) = Some kind ->
  encode_event_wait_grp node.(waitList) before.(TskState) <> 0 ->
  event_pend_abort_critical sg event kind 1 before result after ->
  exists priorities (source : event_broadcast sg event kind 0 PendAbort before priorities after),
    tmr_task_event_broadcast_calls external actor sg event kind 0 PendAbort before priorities after source.
Proof.
  intros external actor sg event node kind before result after Hvalid Hnode Hkind Hgroup
    [actual [Hactual Hsource]].
  assert (actual = node) by congruence; subst actual.
  rewrite (proj2 (Z.eqb_neq _ _) Hgroup), Z.eqb_refl in Hsource.
  destruct Hsource as [priorities [Hloop Hresult]].
  exists priorities, Hloop; apply tmr_task_event_broadcast_call_receipts;
    [exact Hvalid|exists node; split; assumption|discriminate].
Qed.

Lemma tmr_task_q_post_broadcast_call_receipts :
  forall external actor sg post_kind event node message before result after,
  UCOS2_state_inv sg before -> before.(EventState).(inUsedEventStates) event = Some node ->
  node.(eventType) = OS_EVENT_TYPE_Q ->
  encode_event_wait_grp node.(waitList) before.(TskState) <> 0 ->
  q_post_broadcast_requested post_kind = true ->
  q_post_critical sg post_kind event message before result after ->
  exists priorities (source : event_broadcast sg event PendQ message PendOK before priorities after),
    tmr_task_event_broadcast_calls external actor sg event PendQ message PendOK before priorities after source.
Proof.
  intros external actor sg post_kind event node message before result after
    Hvalid Hnode Htype Hgroup Hbroadcast [actual [Hactual Hsource]].
  assert (actual = node) by congruence; subst actual.
  rewrite (proj2 (Z.eqb_neq _ _) Hgroup) in Hsource.
  destruct Hsource as [_ Hsource]; rewrite Hbroadcast in Hsource.
  destruct Hsource as [priorities Hloop].
  exists priorities, Hloop; apply tmr_task_event_broadcast_call_receipts;
    [exact Hvalid|exists node; split; [exact Hnode|rewrite Htype; reflexivity]|discriminate].
Qed.

Lemma tmr_task_mbox_post_broadcast_call_receipts :
  forall external actor sg event node message options before result after,
  UCOS2_state_inv sg before -> q_post_lookup before event node ->
  node.(eventType) = OS_EVENT_TYPE_MBOX -> q_post_group before node <> 0 ->
  Z.land options 1 <> 0 -> mbox_post_opt_critical sg event message options before result after ->
  exists priorities (source : event_broadcast sg event PendMbox message PendOK before priorities after),
    tmr_task_event_broadcast_calls external actor sg event PendMbox message PendOK before priorities after source.
Proof.
  intros external actor sg event node message options before result after
    Hvalid Hnode Htype Hgroup Hbroadcast [actual [Hactual Hsource]].
  assert (actual = node) by congruence; subst actual.
  rewrite (proj2 (Z.eqb_neq _ _) Hgroup) in Hsource.
  destruct Hsource as [_ Hsource]; rewrite (proj2 (Z.eqb_neq _ _) Hbroadcast) in Hsource.
  destruct Hsource as [priorities Hloop].
  exists priorities, Hloop; apply tmr_task_event_broadcast_call_receipts;
    [exact Hvalid|exists node; split; [exact Hnode|rewrite Htype; reflexivity]|discriminate].
Qed.

(** The following projections consume the loop facts that the current C
    carriers already retain at the actual call, including the default
    single-abort arm.  No initial queue head is reused after an iteration. *)
Lemma tmr_task_sem_abort_loop_call_receipt :
  forall external actor environment critical sg caller active mask saved before acquired event
    observed initial state node processed count priority after,
  sem_pend_abort_source_loop_facts environment critical sg caller active mask saved before acquired
    event observed initial state node processed count ->
  q_post_group state node <> 0 ->
  event_task_rdy sg state event PendSem 0 PendAbort = Some (priority, after) ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event PendSem 0 PendAbort) sg state after.
Proof.
  intros external actor environment critical sg caller active mask saved before acquired event
    observed initial state node processed count priority after
    [_ [_ [_ [_ [_ [Hnode [Htype _]]]]]]] Hgroup Hcall.
  eapply tmr_task_event_ready_group_call_receipt;
    [exact Hnode|exact Hgroup|rewrite Htype; reflexivity|discriminate|exact Hcall].
Qed.

Lemma tmr_task_q_abort_loop_call_receipt :
  forall external actor environment critical sg caller active mask saved before acquired event
    observed initial state node processed count priority after,
  q_pend_abort_loop_facts environment critical sg caller active mask saved before acquired
    event observed initial state node processed count ->
  q_post_group state node <> 0 ->
  event_task_rdy sg state event PendQ 0 PendAbort = Some (priority, after) ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event PendQ 0 PendAbort) sg state after.
Proof.
  intros external actor environment critical sg caller active mask saved before acquired event
    observed initial state node processed count priority after
    [_ [_ [_ [_ [_ [Hnode [Htype _]]]]]]] Hgroup Hcall.
  eapply tmr_task_event_ready_group_call_receipt;
    [exact Hnode|exact Hgroup|rewrite Htype; reflexivity|discriminate|exact Hcall].
Qed.

Lemma tmr_task_mbox_abort_loop_call_receipt :
  forall external actor environment critical sg caller active mask saved before acquired event
    observed initial state node processed count priority after,
  mbox_pend_abort_loop_facts environment critical sg caller active mask saved before acquired
    event observed initial state node processed count ->
  q_post_group state node <> 0 ->
  event_task_rdy sg state event PendMbox 0 PendAbort = Some (priority, after) ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event PendMbox 0 PendAbort) sg state after.
Proof.
  intros external actor environment critical sg caller active mask saved before acquired event
    observed initial state node processed count priority after
    [_ [_ [_ [_ [_ [Hnode [Htype _]]]]]]] Hgroup Hcall.
  eapply tmr_task_event_ready_group_call_receipt;
    [exact Hnode|exact Hgroup|rewrite Htype; reflexivity|discriminate|exact Hcall].
Qed.

Lemma tmr_task_q_post_loop_call_receipt :
  forall external actor environment critical sg caller active mask saved before acquired event
    observed initial message state node priority after,
  q_post_opt_loop_facts environment critical sg caller active mask saved before acquired
    event observed initial message state node ->
  q_post_group state node <> 0 ->
  event_task_rdy sg state event PendQ message PendOK = Some (priority, after) ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event PendQ message PendOK) sg state after.
Proof.
  intros external actor environment critical sg caller active mask saved before acquired event
    observed initial message state node priority after
    [_ [_ [_ [_ [_ [Hnode [Htype _]]]]]]] Hgroup Hcall.
  eapply tmr_task_event_ready_group_call_receipt;
    [exact Hnode|exact Hgroup|rewrite Htype; reflexivity|discriminate|exact Hcall].
Qed.

Lemma tmr_task_mbox_post_loop_call_receipt :
  forall external actor environment critical sg caller active mask saved pe before acquired event
    observed initial message state node priority after,
  mbox_post_opt_loop_facts environment critical sg caller active mask saved pe before acquired
    event observed initial message state node ->
  q_post_group state node <> 0 ->
  event_task_rdy sg state event PendMbox message PendOK = Some (priority, after) ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event PendMbox message PendOK) sg state after.
Proof.
  intros external actor environment critical sg caller active mask saved pe before acquired event
    observed initial message state node priority after
    [_ [_ [_ [_ [_ [Hnode [Htype _]]]]]]] Hgroup Hcall.
  eapply tmr_task_event_ready_group_call_receipt;
    [exact Hnode|exact Hgroup|rewrite Htype; reflexivity|discriminate|exact Hcall].
Qed.

(** Delete retains the event until its real wake loop completes.  These
    receipts concern the wake calls, not the later unlink/recycle cut. *)
Lemma tmr_task_sem_delete_loop_call_receipt :
  forall external actor environment critical sg caller active mask saved before acquired event
    observed initial state node waiting priority after,
  sem_del_source_api_loop_facts environment critical sg caller active mask saved before acquired
    event observed initial state node waiting ->
  q_post_group state node <> 0 ->
  event_task_rdy sg state event PendSem 0 PendAbort = Some (priority, after) ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event PendSem 0 PendAbort) sg state after.
Proof.
  intros external actor environment critical sg caller active mask saved before acquired event
    observed initial state node waiting priority after
    [_ [_ [_ [_ [_ [_ [_ [Hnode [Htype _]]]]]]]]] Hgroup Hcall.
  eapply tmr_task_event_ready_group_call_receipt;
    [exact Hnode|exact Hgroup|rewrite Htype; reflexivity|discriminate|exact Hcall].
Qed.

Lemma tmr_task_q_delete_loop_call_receipt :
  forall external actor environment critical sg caller active mask saved before acquired event
    observed initial state node processed waiting priority after,
  q_del_loop_facts environment critical sg caller active mask saved before acquired
    event observed initial state node processed waiting ->
  q_post_group state node <> 0 ->
  event_task_rdy sg state event PendQ 0 PendAbort = Some (priority, after) ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event PendQ 0 PendAbort) sg state after.
Proof.
  intros external actor environment critical sg caller active mask saved before acquired event
    observed initial state node processed waiting priority after
    [_ [_ [_ [_ [_ [_ [Hnode [Htype _]]]]]]]] Hgroup Hcall.
  eapply tmr_task_event_ready_group_call_receipt;
    [exact Hnode|exact Hgroup|rewrite Htype; reflexivity|discriminate|exact Hcall].
Qed.

Lemma tmr_task_mbox_delete_loop_call_receipt :
  forall external actor environment critical sg caller active mask saved before acquired event
    observed initial state node processed waiting priority after,
  mbox_del_loop_facts environment critical sg caller active mask saved before acquired
    event observed initial state node processed waiting ->
  q_post_group state node <> 0 ->
  event_task_rdy sg state event PendMbox 0 PendAbort = Some (priority, after) ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event PendMbox 0 PendAbort) sg state after.
Proof.
  intros external actor environment critical sg caller active mask saved before acquired event
    observed initial state node processed waiting priority after
    [_ [_ [_ [_ [_ [_ [Hnode [Htype _]]]]]]]] Hgroup Hcall.
  eapply tmr_task_event_ready_group_call_receipt;
    [exact Hnode|exact Hgroup|rewrite Htype; reflexivity|discriminate|exact Hcall].
Qed.

(** Priority restoration is a real preceding fragment of MutexPost.
    Its existing EventState frame supplies the same current event to the
    helper; this is not an equality across Save or a guessed end state. *)
Lemma tmr_task_mutex_post_prepare_call_receipt :
  forall external actor sg acquired prepared after event node mutex owner priority,
  acquired.(EventState).(inUsedEventStates) event = Some node ->
  node.(eventType) = OS_EVENT_TYPE_MUTEX ->
  mutex_post_prepare sg mutex owner acquired prepared ->
  encode_event_wait_grp node.(waitList) prepared.(TskState) <> 0 ->
  event_task_rdy sg prepared event PendMutex 0 PendOK = Some (priority, after) ->
  tmr_task_source_call_receipt external
    (event_task_rdy_source_client actor event PendMutex 0 PendOK) sg prepared after.
Proof.
  intros external actor sg acquired prepared after event node mutex owner priority
    Hnode Htype Hprepare Hgroup Hcall.
  eapply tmr_task_event_ready_group_call_receipt.
  - rewrite (mutex_post_prepare_event_state_eq sg mutex owner acquired prepared Hprepare); exact Hnode.
  - exact Hgroup.
  - rewrite Htype; reflexivity.
  - discriminate.
  - exact Hcall.
Qed.
