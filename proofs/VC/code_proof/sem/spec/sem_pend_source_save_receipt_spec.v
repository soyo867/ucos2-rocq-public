Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_fields_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Build the source proof and its annotation at the actual action edge.
    All registration/actor/Event-actor, execution-origin, state, timer and
    stop data are retained. The call receipt is supplied by this edge's
    C producer; neither registry membership nor a later endpoint creates it. *)
Lemma sem_pend_resumption_source_calls_single_step :
  forall external port clients sg observer event_observer action first before last after
    (member : clients action)
    (foreign : kernel_client_actor action <> Some observer)
    (event_foreign : forall invocation, event_observer = Some invocation ->
      kernel_client_event_actor action <> Some invocation)
    (step : kernel_client_step action sg before after)
    (execution : task_execution_source_step external port sg first before last after)
    (timer : timer_public_trace sg before.(TimerState) after.(TimerState)),
  tmr_task_source_call_receipt external action sg before after ->
  exists trace : kernel_resumption_task_source_trace external port clients sg observer event_observer
      first before (kernel_client_stops action observer) last after,
    sem_pend_resumption_source_calls external port clients sg observer event_observer
      first before (kernel_client_stops action observer) last after trace.
Proof.
  intros external port clients sg observer event_observer action first before last after
    member foreign event_foreign step execution timer receipt.
  replace (kernel_client_stops action observer) with
    (orb (orb (kernel_client_stops action observer) false) false)
    by now rewrite !Bool.orb_false_r.
  exists (@KernelResumptionTaskSourceSegment external port clients sg observer event_observer
    first before (orb (kernel_client_stops action observer) false) last after false last after
    (@KernelClientTaskSourceStep external port clients sg observer event_observer
      action first before last after last after false member foreign event_foreign step execution
      (@KernelClientTaskSourceNil external port clients sg observer event_observer last after))
    timer (@KernelResumptionTaskSourceNil external port clients sg observer event_observer last after)).
  apply SemPendResumptionSourceCallsSegment.
  - apply SemPendClientSourceCallsStep; [exact receipt|constructor].
  - constructor.
Qed.



(** Append the actual annotated segments by their constructors. The new
    proof retains every prefix segment and its timer proof and appends the
    supplied suffix at the same middle state/origin. It does not transport
    an annotation between unrelated proofs using endpoint equality. *)
Lemma sem_pend_resumption_source_calls_append :
  forall external port clients sg observer event_observer first before stopped1 middle transient
    (prefix : kernel_resumption_task_source_trace external port clients sg observer event_observer
      first before stopped1 middle transient),
  sem_pend_resumption_source_calls external port clients sg observer event_observer
    first before stopped1 middle transient prefix ->
  forall stopped2 last after
    (suffix : kernel_resumption_task_source_trace external port clients sg observer event_observer
      middle transient stopped2 last after),
  sem_pend_resumption_source_calls external port clients sg observer event_observer
    middle transient stopped2 last after suffix ->
  exists trace : kernel_resumption_task_source_trace external port clients sg observer event_observer
      first before (orb stopped1 stopped2) last after,
    sem_pend_resumption_source_calls external port clients sg observer event_observer
      first before (orb stopped1 stopped2) last after trace.
Proof.
  intros external port clients sg observer event_observer first before stopped1 middle transient
    prefix Hprefix.
  induction Hprefix as [origin state|
    first before stop_head middle transient stop_tail next final segment timer tail Hsegment Htail IH];
    intros stopped2 last after suffix Hsuffix.
  - exists suffix; exact Hsuffix.
  - destruct (IH stopped2 last after suffix Hsuffix) as [joined Hjoined].
    rewrite <- Bool.orb_assoc.
    exists (@KernelResumptionTaskSourceSegment external port clients sg observer event_observer
      first before stop_head middle transient (orb stop_tail stopped2) last after segment timer joined).
    apply SemPendResumptionSourceCallsSegment; assumption.
Qed.

(** This fact is used only after the actual uninterrupted Save execution
    has established its unchanged kernel state and returned invocation.
    It is not a premise or conclusion for every public Save execution. *)
Lemma sem_pend_source_modular_call_history_uninterrupted :
  forall environment critical sg call state,
  sem_pend_source_modular_call_history environment critical sg call state call state.
Proof.
  intros environment critical sg call state.
  exists (@KernelResumptionTaskSourceNil environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    call.(os_sched_call_invocation) None call.(os_sched_call_origin) state).
  split; [constructor|apply kernel_call_normal_return_refl].
Qed.

(** The Save producer binds [save] once and retains the receipt for
    exactly [proj1 save]. This is the missing consequence at OSSemPend's
    first Save cut, once that producer has been linked. It does not add an
    Ensure to the primitive or derive receipts from its generic old post. *)
Lemma sem_pend_source_fields_save_acquire_from_receipt :
  forall environment local critical sg call returned pevent eid observed mask saved before acquired
    (save : kernel_call_save_source environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical sg call returned mask saved before acquired),
  UCOS2_state_inv sg before ->
  sem_pend_source_save_phase_pre (SemPendAcquirePhase pevent eid observed)
    (Some environment) critical sg call mask before ->
  sem_pend_resumption_source_calls environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    call.(os_sched_call_invocation) None call.(os_sched_call_origin) before false
    returned.(os_sched_call_origin) acquired (proj1 save) ->
  kernel_call_normal_return call before returned acquired ->
  sem_pend_save_rely sg before acquired ->
  sem_pend_fields_masked environment local critical sg returned saved acquired acquired |--
  sem_pend_source_fields_phase_save_output (SemPendAcquirePhase pevent eid observed)
    environment local critical sg call mask saved before.
Proof.
  intros environment local critical sg call returned pevent eid observed mask saved before acquired
    save Hvalid Hphase Hcalls Hnormal Hrely.
  eapply sem_pend_source_fields_save_acquire_from_source.
  - exact Hvalid.
  - exact Hphase.
  - exact save.
  - exact (sem_pend_source_modular_call_history_from_save environment critical sg call returned
      mask saved before acquired save Hcalls Hnormal).
  - exact Hrely.
Qed.

(** A proved current-pointer/Timer frame builds the execution constructor
    for this actual action edge. A classified receipt accompanies the same
    [step]; this is not a frame law for arbitrary registered operations. *)
Lemma sem_pend_framed_source_step_calls :
  forall external port clients sg observer event_observer origin action before after,
  clients action ->
  kernel_client_actor action <> Some observer ->
  (forall invocation, event_observer = Some invocation ->
    kernel_client_event_actor action <> Some invocation) ->
  kernel_client_step action sg before after ->
  before.(SchedState).(curTaskID) = after.(SchedState).(curTaskID) ->
  before.(TimerState) = after.(TimerState) ->
  tmr_task_source_call_receipt external action sg before after ->
  exists trace : kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin before (kernel_client_stops action observer) origin after,
    sem_pend_resumption_source_calls external port clients sg observer event_observer
      origin before (kernel_client_stops action observer) origin after trace.
Proof.
  intros external port clients sg observer event_observer origin action before after
    Hmember Hforeign Hevent Hstep Hcurrent Htimer Hcall.
  eapply sem_pend_resumption_source_calls_single_step.
  - exact Hmember.
  - exact Hforeign.
  - exact Hevent.
  - exact Hstep.
  - exact (@TaskExecutionClientFrame external port sg action origin before after Hstep Hcurrent).
  - rewrite Htimer; constructor.
  - exact Hcall.
Qed.

(** This is exactly the three built-in state projections produced by
    [Hmodules]. False describes only this built-in instance; it neither
    removes Extra executions from Save nor narrows the public registry. *)
Lemma sem_pend_builtin_heap_state_step_source_calls :
  forall external port Extra clients sg observer event_observer,
  clients (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, clients (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, clients (task_create_stack_publication_client publication)) ->
  forall (cut : KernelClientHeapCut Extra) state next returned origin,
  kernel_client_heap_observer_cut observer cut ->
  kernel_client_heap_state_step (fun _ _ _ _ _ => False) sg cut state next returned ->
  kernel_client_heap_observer_cut observer next /\
  exists stopped returned_origin,
    exists trace : kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin state stopped returned_origin returned,
      sem_pend_resumption_source_calls external port clients sg observer event_observer
        origin state stopped returned_origin returned trace.
Proof.
  intros external port Extra clients sg observer event_observer Henter Hexit Hpublish
    cut state next returned origin Hobserver Hstep.
  destruct Hstep.
  - assert (Haction : kernel_client_step (kernel_full_profile_cut_client KernelFullIntEnter)
        sg state (os_int_enter_state state)) by (split; [exact I|reflexivity]).
    split; [exact I|]. exists false, origin.
    eapply sem_pend_framed_source_step_calls with
      (action := kernel_full_profile_cut_client KernelFullIntEnter).
    + exact Henter.
    + discriminate.
    + intros; discriminate.
    + exact Haction.
    + reflexivity.
    + reflexivity.
    + apply TmrTaskCallProfile; exact Haction.
  - assert (Haction : kernel_client_step
        (kernel_full_profile_cut_client (KernelFullIntExitCounter state.(SchedState).(isRunning)))
        sg state (os_int_exit_counter_state state.(SchedState).(isRunning) state))
      by (split; [exact I|reflexivity]).
    split; [exact I|]. exists false, origin.
    eapply sem_pend_framed_source_step_calls with
      (action := kernel_full_profile_cut_client (KernelFullIntExitCounter state.(SchedState).(isRunning))).
    + apply Hexit.
    + discriminate.
    + intros; discriminate.
    + exact Haction.
    + reflexivity.
    + reflexivity.
    + apply TmrTaskCallProfile; exact Haction.
  - assert (Haction : kernel_client_step (task_create_stack_publication_client publication)
        sg state (task_create_stack_publication_state sg publication state))
      by (split; [assumption|reflexivity]).
    split; [exact I|]. exists false, origin.
    eapply sem_pend_framed_source_step_calls with
      (action := task_create_stack_publication_client publication).
    + apply Hpublish.
    + cbn [task_create_stack_publication_client kernel_client_actor].
      cbn [kernel_client_heap_observer_cut] in Hobserver; congruence.
    + intros; discriminate.
    + exact Haction.
    + apply task_create_stack_publication_current_pointer_eq.
    + reflexivity.
    + apply TmrTaskCallNontimer; [apply TmrTaskSourceTaskStackPublication|exact Haction].
  - contradiction.
Qed.

(** Interpret an actual built-in heap path through the caller's EXISTING
    resource guarantee. Its Hstep and returned owner come from the same
    application of Hmodules. No whole-world conversion or new source law is
    required of [resources]; a fields interpretation stays the same fields
    interpretation. An actual Extra path instead needs its concrete module's
    paired source/receipt/owner producer and is not covered by this instance. *)
Lemma sem_pend_builtin_heap_trace_source_resources :
  forall external port Extra resources clients sg observer event_observer,
  @kernel_client_heap_resource_guarantee Extra resources
    (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False) ->
  clients (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, clients (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, clients (task_create_stack_publication_client publication)) ->
  forall cut before next after (frame : Assertion),
  @kernel_client_heap_trace Extra (fun _ _ _ _ _ => False) sg cut before next after ->
  forall state origin,
  kernel_client_heap_observer_cut observer cut ->
  (resources sg cut state ** frame) before ->
  exists returned stopped returned_origin,
    kernel_client_heap_state_trace (fun _ _ _ _ _ => False) sg cut state next returned /\
    (exists trace : kernel_resumption_task_source_trace external port clients sg observer event_observer
        origin state stopped returned_origin returned,
      sem_pend_resumption_source_calls external port clients sg observer event_observer
        origin state stopped returned_origin returned trace) /\
    kernel_client_heap_observer_cut observer next /\
    (resources sg next returned ** frame) after.
Proof.
  intros external port Extra resources clients sg observer event_observer
    Hmodules Henter Hexit Hpublish cut before next after frame Htrace.
  induction Htrace; intros state origin Hobserver Hpre.
  - exists state, false, origin; split; [constructor|].
    split.
    + exists (@KernelResumptionTaskSourceNil external port clients sg observer event_observer origin state).
      constructor.
    + split; assumption.
  - destruct (Hmodules sg cut before middle_cut middle state frame H Hpre)
      as [middle_state [Hstep Hmiddle]].
    destruct (sem_pend_builtin_heap_state_step_source_calls external port Extra clients sg observer
      event_observer Henter Hexit Hpublish cut state middle_cut middle_state origin Hobserver Hstep)
      as [Hmiddle_observer [stop1 [middle_origin [Hsource Hcalls]]]].
    destruct (IHHtrace middle_state middle_origin Hmiddle_observer Hmiddle)
      as [returned [stop2 [returned_origin [Htail [[Htail_source Htail_calls] [Hfinal_observer Hpost]]]]]].
    destruct (sem_pend_resumption_source_calls_append external port clients sg observer event_observer
      origin state stop1 middle_origin middle_state Hsource Hcalls stop2 returned_origin returned
      Htail_source Htail_calls) as [Hjoined Hjoined_calls].
    exists returned, (orb stop1 stop2), returned_origin; split.
    + econstructor; eassumption.
    + split; [exists Hjoined; exact Hjoined_calls|]. split; assumption.
Qed.
