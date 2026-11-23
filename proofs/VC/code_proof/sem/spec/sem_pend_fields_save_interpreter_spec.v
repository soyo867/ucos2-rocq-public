Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_fields_resources_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_save_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_event_ready_source_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_wait_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations SemPendEventReadySource.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Client edges precede public Timer segmentation. A private allocation
    may occur here without itself being a timer_public_step. *)
Lemma sem_pend_client_source_calls_single_step :
  forall external port clients sg observer event_observer action first before last after
    (member : clients action)
    (foreign : kernel_client_actor action <> Some observer)
    (event_foreign : forall invocation, event_observer = Some invocation ->
      kernel_client_event_actor action <> Some invocation)
    (step : kernel_client_step action sg before after)
    (execution : task_execution_source_step external port sg first before last after),
  tmr_task_source_call_receipt external action sg before after ->
  exists trace : kernel_client_task_source_trace external port clients sg observer event_observer
      first before (kernel_client_stops action observer) last after,
    sem_pend_client_source_calls external port clients sg observer event_observer
      first before (kernel_client_stops action observer) last after trace.
Proof.
  intros external port clients sg observer event_observer action first before last after
    member foreign event_foreign step execution receipt.
  rewrite <- (Bool.orb_false_r (kernel_client_stops action observer)).
  exists (@KernelClientTaskSourceStep external port clients sg observer event_observer
    action first before last after last after false member foreign event_foreign step execution
    (@KernelClientTaskSourceNil external port clients sg observer event_observer last after)).
  apply SemPendClientSourceCallsStep; [exact receipt|constructor].
Qed.

Lemma sem_pend_client_source_calls_append :
  forall external port clients sg observer event_observer first before stopped1 middle transient
    (prefix : kernel_client_task_source_trace external port clients sg observer event_observer
      first before stopped1 middle transient),
  sem_pend_client_source_calls external port clients sg observer event_observer
    first before stopped1 middle transient prefix ->
  forall stopped2 last after
    (suffix : kernel_client_task_source_trace external port clients sg observer event_observer
      middle transient stopped2 last after),
  sem_pend_client_source_calls external port clients sg observer event_observer
    middle transient stopped2 last after suffix ->
  exists trace : kernel_client_task_source_trace external port clients sg observer event_observer
      first before (orb stopped1 stopped2) last after,
    sem_pend_client_source_calls external port clients sg observer event_observer
      first before (orb stopped1 stopped2) last after trace.
Proof.
  intros external port clients sg observer event_observer first before stopped1 middle transient prefix Hprefix.
  induction Hprefix as [origin state|action first before middle transient last after stopped
    member foreign event_foreign step execution tail receipt Htail IH];
    intros stopped2 final final_state suffix Hsuffix.
  - exists suffix; exact Hsuffix.
  - destruct (IH stopped2 final final_state suffix Hsuffix) as [joined Hjoined].
    rewrite <- Bool.orb_assoc.
    exists (@KernelClientTaskSourceStep external port clients sg observer event_observer
      action first before middle transient final final_state (orb stopped stopped2)
      member foreign event_foreign step execution joined).
    apply SemPendClientSourceCallsStep; assumption.
Qed.

(** The Timer witness belongs to this completed interval, not to each
    constituent client edge. Private prefixes can remain unsegmented. *)
Lemma sem_pend_client_source_calls_public_segment :
  forall external port clients sg observer event_observer first before stopped last after
    (segment : kernel_client_task_source_trace external port clients sg observer event_observer
      first before stopped last after),
  sem_pend_client_source_calls external port clients sg observer event_observer
    first before stopped last after segment ->
  timer_public_trace sg before.(TimerState) after.(TimerState) ->
  exists trace : kernel_resumption_task_source_trace external port clients sg observer event_observer
      first before stopped last after,
    sem_pend_resumption_source_calls external port clients sg observer event_observer
      first before stopped last after trace.
Proof.
  intros external port clients sg observer event_observer first before stopped last after segment Hcalls Htimer.
  rewrite <- (Bool.orb_false_r stopped).
  exists (@KernelResumptionTaskSourceSegment external port clients sg observer event_observer
    first before stopped last after false last after segment Htimer
    (@KernelResumptionTaskSourceNil external port clients sg observer event_observer last after)).
  apply SemPendResumptionSourceCallsSegment; [exact Hcalls|constructor].
Qed.

(** The old C relation and every old Atom remain unchanged. The parameter
    is evidence retained by actual leaf producers; the concrete SemPost
    instance below supplies it from the real C pre/post and execution.
    An unconstructed certificate is an open callsite obligation, not a
    reason to remove that execution from the original program. *)
Section SemPendCSequenceCertificates.
Context (segment : KernelCSegmentRelation).
Context (leaf : forall state before input stopped returned after output,
  segment state before input stopped returned after output ->
  TaskInvocationOrigin -> TaskInvocationOrigin -> Prop).

Inductive sem_pend_c_sequence_call_certificate :
  forall state before input stopped returned after output,
  kernel_c_sequence segment state before input stopped returned after output ->
  TaskInvocationOrigin -> TaskInvocationOrigin -> Prop :=
| SemPendCSequenceCallRefl : forall state heap owner (owned : owner heap) origin,
    sem_pend_c_sequence_call_certificate _ _ _ _ _ _ _
      (KernelCSequenceRefl segment state heap owner owned) origin origin
| SemPendCSequenceCallAtom : forall state before input stopped returned after output
    (step : segment state before input stopped returned after output) first last,
    leaf state before input stopped returned after output step first last ->
    sem_pend_c_sequence_call_certificate _ _ _ _ _ _ _
      (KernelCSequenceAtom segment state before input stopped returned after output step) first last
| SemPendCSequenceCallThen : forall state before input first_stopped middle middle_heap first_output
    next_input last_stopped returned after output
    (first_run : kernel_c_sequence segment state before input first_stopped middle middle_heap first_output)
    (bridge : first_output |-- next_input)
    (last_run : kernel_c_sequence segment middle middle_heap next_input last_stopped returned after output)
    first middle_origin last,
    sem_pend_c_sequence_call_certificate _ _ _ _ _ _ _ first_run first middle_origin ->
    sem_pend_c_sequence_call_certificate _ _ _ _ _ _ _ last_run middle_origin last ->
    sem_pend_c_sequence_call_certificate _ _ _ _ _ _ _
      (KernelCSequenceThen segment state before input first_stopped middle middle_heap first_output
        next_input last_stopped returned after output first_run bridge last_run) first last
| SemPendCSequenceCallAdapt : forall state before input inner_input stopped returned after inner_output output
    (owned : input before) (open_input : input |-- inner_input)
    (inner : kernel_c_sequence segment state before inner_input stopped returned after inner_output)
    (close_output : inner_output |-- output) first last,
    sem_pend_c_sequence_call_certificate _ _ _ _ _ _ _ inner first last ->
    sem_pend_c_sequence_call_certificate _ _ _ _ _ _ _
      (KernelCSequenceAdapt segment state before input inner_input stopped returned after inner_output output
        owned open_input inner close_output) first last.

Lemma sem_pend_c_sequence_client_calls : forall external port clients sg observer event_observer,
  (forall state before input stopped returned after output
    (step : segment state before input stopped returned after output) first last,
    leaf state before input stopped returned after output step first last ->
    exists trace : kernel_client_task_source_trace external port clients sg observer event_observer
        first state stopped last returned,
      sem_pend_client_source_calls external port clients sg observer event_observer
        first state stopped last returned trace) ->
  forall state before input stopped returned after output
    (run : kernel_c_sequence segment state before input stopped returned after output) first last,
  sem_pend_c_sequence_call_certificate state before input stopped returned after output run first last ->
  exists trace : kernel_client_task_source_trace external port clients sg observer event_observer
      first state stopped last returned,
    sem_pend_client_source_calls external port clients sg observer event_observer
      first state stopped last returned trace.
Proof.
  intros external port clients sg observer event_observer Hleaf state before input stopped returned after
    output run first last Hrun.
  induction Hrun.
  - exists (@KernelClientTaskSourceNil external port clients sg observer event_observer origin state).
    constructor.
  - eapply Hleaf; eassumption.
  - destruct IHHrun1 as [prefix Hprefix]; destruct IHHrun2 as [suffix Hsuffix].
    eapply sem_pend_client_source_calls_append; eassumption.
  - exact IHHrun.
Qed.
End SemPendCSequenceCertificates.

Lemma sem_pend_event_ready_entry_unique : forall sg tasks event node first old last updated,
  event_task_rdy_entry sg tasks event node first old ->
  event_task_rdy_entry sg tasks event node last updated -> first = last /\ old = updated.
Proof.
  intros sg tasks event node first old last updated
    [_ [_ [_ [_ [_ [Hfirst Hold]]]]]] [_ [_ [_ [_ [_ [Hlast Hupdated]]]]]].
  assert (Heq : first = last) by congruence.
  subst last; split; congruence.
Qed.

(** This certificate is attached to the original Wake Atom. Both C
    assertions and the literal SemPost helper execution are retained.
    The registered action is the surrounding Post, not an invented raw
    EventReady membership. It assumes no final source history or owner. *)
Section SemPendSemPostCLeaf.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (observer : nat) (observer_origin : TaskInvocationOrigin).
Let segment := kernel_program_c_step environment critical sg observer observer_origin.

Inductive sem_pend_sem_post_c_step_certificate :
  forall state before input stopped returned after output,
  segment state before input stopped returned after output ->
  TaskInvocationOrigin -> TaskInvocationOrigin -> Prop :=
| SemPendSemPostCStep : forall actor origin entry event node selected old returned frame before after
    (lookup : entry.(EventState).(inUsedEventStates) event = Some node)
    (selected_entry : event_task_rdy_entry sg entry.(TskState) event node selected old)
    (owned : (WakeComponent.event_ready_c_input sg entry event node selected old PendSem PendOK ** frame) before)
    (completed : (WakeComponent.event_ready_c_output sg entry event node selected old PendSem 0 PendOK returned ** frame) after),
    critical.(critical_region_clients) (sem_pend_post_source_client actor event) ->
    actor <> observer -> node.(eventType) = OS_EVENT_TYPE_SEM -> sem_post_group entry node <> 0 ->
    sem_post_waiter_execution sg (event_addr sg event) returned before after ->
    sem_pend_sem_post_c_step_certificate _ _ _ _ _ _ _
      (@KernelProgramCWake environment critical sg observer observer_origin _ _ _ _ _ _
        (@WakeComponent.KernelWakeCEventSegment sg entry event node selected old PendSem 0 PendOK returned
          frame before after lookup selected_entry owned completed)) origin origin.

Lemma sem_pend_sem_post_c_step_client_calls :
  forall state before input stopped returned after output
    (step : segment state before input stopped returned after output) first last,
  sem_pend_sem_post_c_step_certificate state before input stopped returned after output step first last ->
  exists trace : kernel_client_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
      first state stopped last returned,
    sem_pend_client_source_calls environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical.(critical_region_clients) sg observer None first state stopped last returned trace.
Proof.
  intros state before input stopped returned after output step first last Hcertificate.
  destruct Hcertificate as [actor origin entry event node selected old returned frame before after
    Hlookup Hentry Hpre Hpost Hmember Hforeign Htype Hgroup Hactual].
  set (wake := event_wake_state sg entry event node selected old PendSem 0 PendOK).
  assert (Hstep : kernel_client_step (sem_pend_post_source_client actor event) sg entry wake).
  { exists (OS_ERR_NONE, true).
    eapply sem_post_wake_result_critical; [exact Hlookup|exact Hgroup|].
    unfold sem_post_wake_result, wake.
    eapply WakeComponent.event_task_rdy_c_entry_source; eassumption. }
  assert (Hreceipt : tmr_task_source_call_receipt environment.(task_stack_call_external)
      (sem_pend_post_source_client actor event) sg entry wake).
  { eapply sem_pend_source_client_call_receipt with
      (source := TmrTaskSourceSem environment.(task_stack_call_external) _ (TmrTaskSemPost actor event));
      [constructor|exact Hstep]. }
  pose proof (@WakeComponent.KernelWakeCEventSegment sg entry event node selected old PendSem 0 PendOK
    returned frame before after Hlookup Hentry Hpre Hpost) as Hsegment.
  destruct (sem_pend_wake_source_current_timer_frame sg entry wake
    (WakeComponent.kernel_wake_c_segment_source _ _ _ _ _ _ _ Hsegment)) as [Hcurrent _].
  change (exists trace : kernel_client_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
      origin entry (kernel_client_stops (sem_pend_post_source_client actor event) observer) origin wake,
    sem_pend_client_source_calls environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical.(critical_region_clients) sg observer None origin entry
      (kernel_client_stops (sem_pend_post_source_client actor event) observer) origin wake trace).
  eapply sem_pend_client_source_calls_single_step with (action := sem_pend_post_source_client actor event).
  - exact Hmember.
  - cbn [sem_pend_post_source_client kernel_client_actor]; congruence.
  - intros; discriminate.
  - exact Hstep.
  - exact (@TaskExecutionClientFrame environment.(task_stack_call_external) environment.(task_stack_call_port)
      sg (sem_pend_post_source_client actor event) origin entry wake Hstep Hcurrent).
  - exact Hreceipt.
Qed.

(** The actual fields split chooses selected/old once. Uniqueness of the
    existing event entry justifies the original Adapt implication. The
    literal execution creates the helper post; its merge returns the same
    fields map and local family on the actual after heap. *)
Lemma sem_pend_sem_post_fields_c_sequence_certificate :
  forall local origin actor entry event node returned before after (frame : Assertion),
  critical.(critical_region_clients) (sem_pend_post_source_client actor event) -> actor <> observer ->
  sem_post_lookup entry event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group entry node <> 0 -> event_object_layout_prop sg event ->
  (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg entry ** frame) before ->
  sem_post_waiter_execution sg (event_addr sg event) returned before after ->
  exists selected old,
    let wake := event_wake_state sg entry event node selected old PendSem 0 PendOK in
    exists run : kernel_c_sequence segment entry before
        (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg entry ** frame)
        false wake after
        (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg wake ** frame),
      sem_pend_c_sequence_call_certificate segment sem_pend_sem_post_c_step_certificate
        _ _ _ _ _ _ _ run origin origin /\
      timer_public_trace sg entry.(TimerState) wake.(TimerState) /\
      (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg wake ** frame) after.
Proof.
  intros local origin actor entry event node returned before after frame
    Hmember Hforeign Hlookup Htype Hgroup Hlayout Hpre Hactual.
  set (abi := environment.(task_stack_call_continuations)).
  set (stacks := store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
    entry.(TskState).(parkedTaskStacks)).
  assert (Hopen : kernel_client_continuation_fields_world abi local sg entry ** frame |--
    coq_prop (UCOS2_state_inv sg entry /\ task_stack_live_coverage entry.(TskState) None) &&
    (kernel_program_fields_inv sg entry ** stacks ** frame)).
  { unfold kernel_client_continuation_fields_world, kernel_continuation_inv, kernel_program_fields_inv, stacks;
      entailer!. }
  destruct (Hopen before Hpre) as [[Hvalid Hcoverage] Hworld].
  assert (Hsplit : kernel_program_fields_inv sg entry ** stacks ** frame |--
    EX selected old, coq_prop (event_task_rdy_entry sg entry.(TskState) event node selected old) &&
      (WakeComponent.event_ready_c_input sg entry event node selected old PendSem PendOK **
        (sem_pend_event_ready_fields_frame sg entry event selected ** stacks ** frame))).
  { rewrite kernel_program_fields_inv_split_unmap.
    sep_apply_l_atomic (sem_pend_event_ready_fields_split sg entry event node Hvalid Hlookup Htype Hgroup Hlayout).
    Intros selected old; Exists selected old; entailer!. }
  destruct (Hsplit before Hworld) as [selected [old [Hentry Howned]]].
  set (residual := sem_pend_event_ready_fields_frame sg entry event selected ** stacks ** frame).
  assert (Hselected : kernel_client_continuation_fields_world abi local sg entry ** frame |--
      WakeComponent.event_ready_c_input sg entry event node selected old PendSem PendOK ** residual).
  { intros heap Hheap.
    destruct (Hopen heap Hheap) as [_ Hresources].
    destruct (Hsplit heap Hresources) as [other [previous [Hother Hraw]]].
    destruct (sem_pend_event_ready_entry_unique sg entry.(TskState) event node selected old other previous
      Hentry Hother) as [-> ->].
    exact Hraw. }
  pose proof (sem_post_waiter_source_post sg entry.(TskState) event node selected old
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) returned before after residual
    Howned Hactual) as Hpost.
  set (wake := event_wake_state sg entry event node selected old PendSem 0 PendOK).
  assert (Hclose : WakeComponent.event_ready_c_output sg entry event node selected old PendSem 0 PendOK returned **
      residual |-- kernel_client_continuation_fields_world abi local sg wake ** frame).
  { pose proof (sem_pend_event_ready_fields_merge_continuations environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port) abi sg entry event node
      selected old returned local None Hvalid Hlookup Htype Hentry Hcoverage) as Hjoin.
    cbn zeta in Hjoin; unfold residual, stacks, wake; sepcon_assoc_change; sep_apply_l_atomic Hjoin.
    unfold kernel_client_continuation_fields_world, kernel_continuation_inv; entailer!. }
  pose (body := @WakeComponent.KernelWakeCEventSegment sg entry event node selected old PendSem 0 PendOK
    returned residual before after Hlookup Hentry Howned Hpost).
  pose (step := @KernelProgramCWake environment critical sg observer observer_origin _ _ _ _ _ _ body).
  pose (atom := @KernelCSequenceAtom segment _ _ _ _ _ _ _ step).
  pose (run := @KernelCSequenceAdapt segment entry before
    (kernel_client_continuation_fields_world abi local sg entry ** frame)
    (WakeComponent.event_ready_c_input sg entry event node selected old PendSem PendOK ** residual)
    false wake after
    (WakeComponent.event_ready_c_output sg entry event node selected old PendSem 0 PendOK returned ** residual)
    (kernel_client_continuation_fields_world abi local sg wake ** frame) Hpre Hselected atom Hclose).
  exists selected, old, run; split.
  - unfold run; apply SemPendCSequenceCallAdapt.
    unfold atom; apply SemPendCSequenceCallAtom.
    unfold step, body; econstructor; eassumption.
  - split; [|exact (Hclose after Hpost)].
    destruct (sem_pend_wake_source_current_timer_frame sg entry wake
      (WakeComponent.kernel_wake_c_segment_source _ _ _ _ _ _ _ body)) as [_ Htimer].
    rewrite Htimer; constructor.
Qed.

Lemma sem_pend_sem_post_fields_c_sequence_source :
  forall local origin actor entry event node returned before after (frame : Assertion),
  critical.(critical_region_clients) (sem_pend_post_source_client actor event) -> actor <> observer ->
  sem_post_lookup entry event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group entry node <> 0 -> event_object_layout_prop sg event ->
  (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg entry ** frame) before ->
  sem_post_waiter_execution sg (event_addr sg event) returned before after ->
  exists selected old,
    let wake := event_wake_state sg entry event node selected old PendSem 0 PendOK in
    exists run : kernel_c_sequence segment entry before
        (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg entry ** frame)
        false wake after
        (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg wake ** frame),
      sem_pend_c_sequence_call_certificate segment sem_pend_sem_post_c_step_certificate
        _ _ _ _ _ _ _ run origin origin /\
      (exists trace : kernel_resumption_task_source_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
          origin entry false origin wake,
        sem_pend_resumption_source_calls environment.(task_stack_call_external) environment.(task_stack_call_port)
          critical.(critical_region_clients) sg observer None origin entry false origin wake trace) /\
      (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg wake ** frame) after.
Proof.
  intros local origin actor entry event node returned before after frame
    Hmember Hforeign Hlookup Htype Hgroup Hlayout Hpre Hactual.
  destruct (sem_pend_sem_post_fields_c_sequence_certificate local origin actor entry event node returned
    before after frame Hmember Hforeign Hlookup Htype Hgroup Hlayout Hpre Hactual)
    as [selected [old [run [Hcertificate [Htimer Howned]]]]].
  exists selected, old, run; split; [exact Hcertificate|]. split; [|exact Howned].
  destruct (sem_pend_c_sequence_client_calls segment sem_pend_sem_post_c_step_certificate
    environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer None sem_pend_sem_post_c_step_client_calls
    _ _ _ _ _ _ _ run origin origin Hcertificate) as [clients Hcalls].
  eapply sem_pend_client_source_calls_public_segment; eassumption.
Qed.
End SemPendSemPostCLeaf.
