Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Relations.Relation_Operators.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Import TaskStateDef ListNotations.
Local Open Scope Z_scope.

(** Receipt annotations preserve the exact source proof, including its
    actor, execution-origin transition and Event observer.  They cannot be
    reconstructed from a trace whose caller facts have been erased. *)
Inductive sem_pend_client_source_calls external port clients sg observer event_observer :
  forall first before stopped last after,
    kernel_client_task_source_trace external port clients sg observer event_observer
      first before stopped last after -> Prop :=
| SemPendClientSourceCallsNil : forall origin state,
    sem_pend_client_source_calls external port clients sg observer event_observer
      origin state false origin state
      (@KernelClientTaskSourceNil external port clients sg observer event_observer origin state)
| SemPendClientSourceCallsStep : forall action first before middle transient last after stopped
    (member : clients action) (foreign : kernel_client_actor action <> Some observer)
    (event_foreign : forall invocation, event_observer = Some invocation ->
      kernel_client_event_actor action <> Some invocation)
    (step : kernel_client_step action sg before transient)
    (execution : task_execution_source_step external port sg first before middle transient)
    (tail : kernel_client_task_source_trace external port clients sg observer event_observer
      middle transient stopped last after),
    tmr_task_source_call_receipt external action sg before transient ->
    sem_pend_client_source_calls external port clients sg observer event_observer
      middle transient stopped last after tail ->
    sem_pend_client_source_calls external port clients sg observer event_observer
      first before (orb (kernel_client_stops action observer) stopped) last after
      (@KernelClientTaskSourceStep external port clients sg observer event_observer
        action first before middle transient last after stopped member foreign event_foreign
        step execution tail).

Lemma sem_pend_client_source_calls_projection :
  forall external port critical sg observer event_observer first before stopped last after
    (trace : kernel_client_task_source_trace external port critical.(critical_region_clients)
      sg observer event_observer first before stopped last after),
  sem_pend_client_source_calls external port critical.(critical_region_clients)
    sg observer event_observer first before stopped last after trace ->
  UCOS2_state_inv sg before -> forall tid old eid generation,
    before.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros external port critical sg observer event_observer first before stopped last after trace Hcalls.
  induction Hcalls as [origin state|action first before middle transient last after stopped
    Hin Hforeign Hevent Hstep Hsource Htail Hcall Hcalls IH];
    intros Hvalid tid old eid generation Hold Hcont.
  - apply sem_pend_task_projection_refl; exact Hold.
  - assert (Htransient : UCOS2_state_inv sg transient).
    { exact (kernel_client_preserves_validity action
        (critical.(critical_region_client_certificates) action Hin)
        sg before transient Hvalid Hstep). }
    destruct (tmr_task_source_call_projection external action sg before transient tid old eid generation
      Hcall Hvalid Hold Hcont) as [current [Hcurrent Hfirst]].
    assert (Hcontinue : sem_pend_wait_continuation eid generation current).
    { eapply sem_pend_wait_trace_preserves_continuation; eassumption. }
    destruct (IH Htransient tid current eid generation Hcurrent Hcontinue)
      as [last_node [Hlast Hsecond]].
    exists last_node; split; [exact Hlast|eapply rt_trans; eassumption].
Qed.

Inductive sem_pend_resumption_source_calls external port clients sg observer event_observer :
  forall first before stopped last after,
    kernel_resumption_task_source_trace external port clients sg observer event_observer
      first before stopped last after -> Prop :=
| SemPendResumptionSourceCallsNil : forall origin state,
    sem_pend_resumption_source_calls external port clients sg observer event_observer
      origin state false origin state
      (@KernelResumptionTaskSourceNil external port clients sg observer event_observer origin state)
| SemPendResumptionSourceCallsSegment : forall first before stopped1 middle transient stopped2 last after
    (segment : kernel_client_task_source_trace external port clients sg observer event_observer
      first before stopped1 middle transient)
    (timer : timer_public_trace sg before.(TimerState) transient.(TimerState))
    (tail : kernel_resumption_task_source_trace external port clients sg observer event_observer
      middle transient stopped2 last after),
    sem_pend_client_source_calls external port clients sg observer event_observer
      first before stopped1 middle transient segment ->
    sem_pend_resumption_source_calls external port clients sg observer event_observer
      middle transient stopped2 last after tail ->
    sem_pend_resumption_source_calls external port clients sg observer event_observer
      first before (orb stopped1 stopped2) last after
      (@KernelResumptionTaskSourceSegment external port clients sg observer event_observer
        first before stopped1 middle transient stopped2 last after segment timer tail).

Lemma sem_pend_resumption_source_calls_projection :
  forall external port critical sg observer event_observer first before stopped last after
    (trace : kernel_resumption_task_source_trace external port critical.(critical_region_clients)
      sg observer event_observer first before stopped last after),
  sem_pend_resumption_source_calls external port critical.(critical_region_clients)
    sg observer event_observer first before stopped last after trace ->
  UCOS2_state_inv sg before -> forall tid old eid generation,
    before.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros external port critical sg observer event_observer first before stopped last after trace Hcalls.
  induction Hcalls as [origin state|first before stopped1 middle transient stopped2 last after
    Hsegment Htimer Htail Hsegment_calls Htail_calls IH];
    intros Hvalid tid old eid generation Hold Hcont.
  - apply sem_pend_task_projection_refl; exact Hold.
  - destruct (kernel_client_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Hsegment)
      as [Hresources Hcontrol].
    assert (Htransient : UCOS2_state_inv sg transient).
    { exact (proj1 (kernel_client_resource_trace_transports_resources _ _ _ _ _ _ _
        critical.(critical_region_client_certificates) Hresources Hvalid)). }
    destruct (sem_pend_client_source_calls_projection external port critical sg observer
      event_observer first before stopped1 middle transient Hsegment Hsegment_calls Hvalid
      tid old eid generation Hold Hcont) as [current [Hcurrent Hfirst]].
    assert (Hcontinue : sem_pend_wait_continuation eid generation current).
    { eapply sem_pend_wait_trace_preserves_continuation; eassumption. }
    destruct (IH Htransient tid current eid generation Hcurrent Hcontinue)
      as [last_node [Hlast Hsecond]].
    exists last_node; split; [exact Hlast|eapply rt_trans; eassumption].
Qed.

(** A receipt is retained when the actual modular call history is built.
    Erasing it recovers the existing generic history; that erasure has no
    converse, so an unannotated callee post cannot establish this predicate. *)
Definition sem_pend_source_modular_call_history environment critical sg call before returned after : Prop :=
  exists trace : kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    call.(os_sched_call_invocation) None call.(os_sched_call_origin)
    before false returned.(os_sched_call_origin) after,
    sem_pend_resumption_source_calls environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      call.(os_sched_call_invocation) None call.(os_sched_call_origin)
      before false returned.(os_sched_call_origin) after trace /\
    kernel_call_normal_return call before returned after.

Lemma sem_pend_source_modular_call_history_from_save :
  forall environment critical sg call returned mask saved before acquired
    (save : kernel_call_save_source environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical sg call returned mask saved before acquired),
  sem_pend_resumption_source_calls environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    call.(os_sched_call_invocation) None call.(os_sched_call_origin)
    before false returned.(os_sched_call_origin) acquired (proj1 save) ->
  kernel_call_normal_return call before returned acquired ->
  sem_pend_source_modular_call_history environment critical sg call before returned acquired.
Proof. intros * Hcalls Hnormal; exists (proj1 save); split; assumption. Qed.

Lemma sem_pend_source_modular_call_history_forgets :
  forall environment critical sg call before returned after,
  sem_pend_source_modular_call_history environment critical sg call before returned after ->
  sem_pend_modular_call_history environment critical sg call before returned after.
Proof. intros * [trace [Hcalls Hnormal]]; split; assumption. Qed.

Lemma sem_pend_source_modular_call_history_timer_trace :
  forall environment critical sg call before returned after,
  sem_pend_source_modular_call_history environment critical sg call before returned after ->
  timer_public_trace sg before.(TimerState) after.(TimerState).
Proof.
  intros * [trace [Hcalls Hnormal]].
  eapply kernel_resumption_resource_trace_timer_projection.
  exact (proj1 (kernel_resumption_task_source_trace_erases
    _ _ _ _ _ _ _ _ _ _ _ trace)).
Qed.

(** A local extension of the source history.  The old type is unchanged.
    Old executions embed in one direction; no New-to-Old theorem is used.
    Scheduler C provenance and the projection of that actual source are
    separate premises.  Neither readiness nor an arbitrary endpoint can
    manufacture a history. *)
Inductive sem_pend_source_history environment critical sg original eid generation :
  UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| SemPendSourceHistoryLegacy : forall before after,
    sem_pend_wait_source_history environment critical sg original eid generation before after ->
    sem_pend_source_history environment critical sg original eid generation before after
| SemPendSourceHistoryClients : forall before after stopped returned_origin
    (trace : kernel_resumption_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None original.(os_sched_call_origin)
      before stopped returned_origin after),
    sem_pend_resumption_source_calls environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None original.(os_sched_call_origin)
      before stopped returned_origin after trace ->
    UCOS2_state_inv sg before ->
    sem_pend_source_history environment critical sg original eid generation before after
| SemPendSourceHistoryScheduler : forall before entered returned after,
    kernel_stack_call_same_call entered original ->
    os_sched_c_return environment.(task_stack_call_external) critical sg before entered returned after ->
    (forall previous,
      before.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some previous ->
      sem_pend_wait_continuation eid generation previous ->
      sem_pend_task_projection before.(TskState) after.(TskState)
        original.(os_sched_call_stack).(stackLeaseSlot) previous) ->
    sem_pend_source_history environment critical sg original eid generation before after
| SemPendSourceHistoryTrans : forall before middle after,
    sem_pend_source_history environment critical sg original eid generation before middle ->
    sem_pend_source_history environment critical sg original eid generation middle after ->
    sem_pend_source_history environment critical sg original eid generation before after.

Lemma sem_pend_source_history_refl : forall environment critical sg original eid generation state,
  sem_pend_source_history environment critical sg original eid generation state state.
Proof. intros; apply SemPendSourceHistoryLegacy, SemPendWaitSourceRefl. Qed.

(** Property transport uses the very same source constructors.  The client
    case exposes its existing timer trace; the Scheduler case exposes its
    C return.  In particular, a waiter projection is never used to infer a
    Timer property.  These are proof rules, not extra public preconditions. *)
Lemma sem_pend_source_history_preserves_property :
  forall environment critical sg original eid generation
    (property : UCOS2_Verify_State -> Prop),
  (forall before after,
    sem_pend_wait_source_history environment critical sg original eid generation before after ->
    property before -> property after) ->
  (forall before after,
    timer_public_trace sg before.(TimerState) after.(TimerState) ->
    property before -> property after) ->
  (forall before entered returned after,
    kernel_stack_call_same_call entered original ->
    os_sched_c_return environment.(task_stack_call_external) critical sg before entered returned after ->
    property before -> property after) ->
  forall before after,
  sem_pend_source_history environment critical sg original eid generation before after ->
  property before -> property after.
Proof.
  intros environment critical sg original eid generation property Hlegacy Htimer Hscheduler
    before after Hhistory.
  induction Hhistory as [before after Hpath|before after stopped returned_origin trace Hcalls Hvalid|
    before entered returned after Hsame Hbody Hprojection|before middle after Hfirst IHfirst Hsecond IHsecond];
    intro Hproperty.
  - eapply Hlegacy; eassumption.
  - eapply Htimer; [|exact Hproperty].
    eapply kernel_resumption_resource_trace_timer_projection.
    exact (proj1 (kernel_resumption_task_source_trace_erases
      _ _ _ _ _ _ _ _ _ _ _ trace)).
  - eapply Hscheduler; eassumption.
  - apply IHsecond, IHfirst; exact Hproperty.
Qed.

Lemma sem_pend_source_history_preserves_waiter : forall environment critical sg original
  eid generation before after,
  sem_pend_source_history environment critical sg original eid generation before after ->
  forall previous,
    before.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some previous ->
    sem_pend_wait_continuation eid generation previous ->
    exists current,
      after.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some current /\
      sem_pend_wait_continuation eid generation current.
Proof.
  intros environment critical sg original eid generation before after Hhistory.
  induction Hhistory as [before after Hlegacy|before after stopped returned_origin trace Hcalls Hvalid|
    before entered returned after Hsame Hbody Hprojection|before middle after Hfirst IHfirst Hsecond IHsecond];
    intros previous Hprevious Hwait.
  - eapply sem_pend_wait_source_history_preserves_waiter; eassumption.
  - destruct (sem_pend_resumption_source_calls_projection environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical sg original.(os_sched_call_invocation) None
      original.(os_sched_call_origin) before stopped returned_origin after trace Hcalls Hvalid
      original.(os_sched_call_stack).(stackLeaseSlot) previous eid generation Hprevious Hwait)
      as [current [Hcurrent Heffects]].
    exists current; split; [exact Hcurrent|].
    eapply sem_pend_wait_trace_preserves_continuation; eassumption.
  - destruct (Hprojection previous Hprevious Hwait) as [current [Hcurrent Heffects]].
    exists current; split; [exact Hcurrent|].
    eapply sem_pend_wait_trace_preserves_continuation; eassumption.
  - destruct (IHfirst previous Hprevious Hwait) as [current [Hcurrent Hcontinue]].
    exact (IHsecond current Hcurrent Hcontinue).
Qed.

Lemma sem_pend_source_switch_trace_projection :
  forall external critical sg entry entered installed stopped final
    (trace : kernel_client_resource_trace critical.(critical_region_clients) sg
      entered.(os_sched_call_invocation) None installed stopped final),
  sem_pend_projected_source_client external.(os_sched_hook_action) ->
  os_sched_switch_source external sg entry entered installed ->
  UCOS2_state_inv sg installed ->
  tmr_task_source_trace_calls external critical.(critical_region_clients) sg
    entered.(os_sched_call_invocation) None installed stopped final trace ->
  forall tid old eid generation,
    entry.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection entry.(TskState) final.(TskState) tid old.
Proof.
  intros external critical sg entry entered installed stopped final trace Hhook Hsource
    Hinstalled Hcalls tid old eid generation Hold Hwait.
  destruct (sem_pend_sched_switch_source_projection external sg entry entered installed
    tid old Hhook Hsource Hold) as [current [Hcurrent Hfirst]].
  assert (Hcontinue : sem_pend_wait_continuation eid generation current).
  { eapply sem_pend_wait_trace_preserves_continuation; eassumption. }
  destruct (tmr_task_source_trace_calls_projection external critical sg entered.(os_sched_call_invocation)
    None installed stopped final trace Hcalls Hinstalled tid current eid generation Hcurrent Hcontinue)
    as [last [Hlast Hsecond]].
  exists last; split; [exact Hlast|eapply rt_trans; eassumption].
Qed.

(** This is the existing C return with the receipt retained beside the
    exact foreign trace.  The installed-state invariant comes from its
    actual resource producer.  Forgetting this packet yields the ordinary
    C return; no reconstruction from erased endpoints is provided. *)
Definition sem_pend_source_scheduler_return external critical sg entry entered returned final : Prop :=
  if os_sched_requests_switch entry then
    exists installed,
      os_sched_switch_source external sg entry entered installed /\
      UCOS2_state_inv sg installed /\
      (exists stopped,
        exists trace : kernel_client_trace critical.(critical_region_clients) sg
          entered.(os_sched_call_invocation) installed stopped final,
        tmr_task_source_trace_calls external critical.(critical_region_clients) sg
          entered.(os_sched_call_invocation) None installed stopped final trace /\
        orb (kernel_client_stops external.(os_sched_hook_action)
          entered.(os_sched_call_invocation)) stopped = false) /\
      external.(os_sched_arch_resume_source) entered returned /\
      returned.(os_sched_call_invocation) = entered.(os_sched_call_invocation) /\
      returned.(os_sched_call_origin) = entered.(os_sched_call_origin) /\
      returned.(os_sched_call_stack) = entered.(os_sched_call_stack) /\
      task_invocation_active final.(TskState) entered.(os_sched_call_invocation)
        entered.(os_sched_call_origin) /\
      final.(SchedState).(curTaskID) = Some entered.(os_sched_call_stack).(stackLeaseSlot) /\
      final.(TskState).(parkedTaskStacks) (task_stack_key entered.(os_sched_call_stack)) = None
  else returned = entered /\ final = os_sched_prefix_state entry.

Lemma sem_pend_source_scheduler_return_forgets : forall external critical sg entry entered returned final,
  sem_pend_source_scheduler_return external critical sg entry entered returned final ->
  os_sched_c_return external critical sg entry entered returned final.
Proof.
  intros external critical sg entry entered returned final Hsource.
  unfold sem_pend_source_scheduler_return in Hsource; unfold os_sched_c_return.
  destruct (os_sched_requests_switch entry); [|exact Hsource].
  destruct Hsource as [installed [Hswitch [Hvalid [[stopped [trace [Hcalls Hnormal]]] Hreturn]]]].
  exists installed; split; [exact Hswitch|]. split; [|exact Hreturn].
  exists stopped; split; [exact trace|exact Hnormal].
Qed.

Lemma sem_pend_source_scheduler_return_projection : forall external critical sg entry entered returned final,
  sem_pend_projected_source_client external.(os_sched_hook_action) ->
  sem_pend_source_scheduler_return external critical sg entry entered returned final ->
  forall tid old eid generation,
    entry.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection entry.(TskState) final.(TskState) tid old.
Proof.
  intros external critical sg entry entered returned final Hhook Hsource tid old eid generation Hold Hwait.
  unfold sem_pend_source_scheduler_return in Hsource.
  destruct (os_sched_requests_switch entry).
  - destruct Hsource as [installed [Hswitch [Hvalid [[stopped [trace [Hcalls Hnormal]]] Hreturn]]]].
    eapply sem_pend_source_switch_trace_projection; eassumption.
  - destruct Hsource as [-> ->]; apply sem_pend_task_projection_refl; exact Hold.
Qed.

Lemma sem_pend_source_history_from_scheduler_return : forall environment critical sg original eid generation
  entry entered returned final,
  kernel_stack_call_same_call entered original ->
  sem_pend_projected_source_client environment.(task_stack_call_external).(os_sched_hook_action) ->
  sem_pend_source_scheduler_return environment.(task_stack_call_external) critical sg
    entry entered returned final ->
  sem_pend_source_history environment critical sg original eid generation entry final.
Proof.
  intros * Hsame Hhook Hsource.
  eapply SemPendSourceHistoryScheduler; [exact Hsame| |].
  - eapply sem_pend_source_scheduler_return_forgets; exact Hsource.
  - intros previous Hprevious Hwait.
    eapply sem_pend_source_scheduler_return_projection; eassumption.
Qed.
