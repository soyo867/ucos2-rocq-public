Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.Logic.PropExtensionality.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.task Ucos2Verify.lib.event Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_event_ready_source_receipt_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_return_fields_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_source_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_callee_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_irq_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_pending_irq_switch_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_fields_prefix_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.VC.code.sched.spec.sched_legacy_prefix_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_c_segment_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_parent_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations SemPendEventReadySource.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Only the opaque conjunction getter is removed. This local equality
    follows from the already used propositional extensionality boundary;
    it introduces no proof-irrelevance axiom and never changes a C run. *)
Local Lemma sem_pend_conjunction_second_proof_eq : forall (P Q : Prop) (first : P) (second : Q),
  proj2 (conj first second) = second.
Proof.
  intros P Q first second.
  assert (Heq : Q = True).
  { apply propositional_extensionality; split; [intros; exact I|intros; exact second]. }
  revert first second; rewrite Heq; intros first second.
  destruct second; destruct (proj2 (conj first I)); reflexivity.
Qed.

(** The actual fields producer's incoming world already contains validity.
    Its continuation map and arbitrary frame remain spatial resources. *)
Lemma sem_pend_fields_world_source_valid : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local sg state heap frame,
  (kernel_client_continuation_fields_world abi local sg state ** frame) heap ->
  UCOS2_state_inv sg state.
Proof.
  intros external platform port abi local sg state heap frame Hpre.
  assert (Hopen : kernel_client_continuation_fields_world abi local sg state ** frame |--
    coq_prop (UCOS2_state_inv sg state) &&
      (kernel_client_continuation_fields_world abi local sg state ** frame)).
  { unfold kernel_client_continuation_fields_world, kernel_continuation_inv,
      kernel_program_fields_inv; entailer!. }
  exact (proj1 (Hopen heap Hpre)).
Qed.

(** The physical split/call/merge is the same one used by the frozen Sem8
    producer. Here it directly retains the C prefix, without imposing the
    separate foreign-actor condition used when interpreting an outer public
    SemPost as a registered client. Both observers and stored origin remain
    arbitrary, and the returned fields owner is the actual merge result. *)
Lemma sem_pend_sem_post_fields_selected_prefix :
  forall environment critical sg observer (stored_origin : TaskInvocationOrigin) (event_observer : option nat)
    local active_key entry event node result before after
    (frame : Assertion),
  sem_post_lookup entry event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group entry node <> 0 -> event_object_layout_prop sg event ->
  (kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_fields_inv local sg active_key entry ** frame) before ->
  sem_post_waiter_execution sg (event_addr sg event) result before after ->
  exists selected old,
    let wake := event_wake_state sg entry event node selected old PendSem 0 PendOK in
    event_task_rdy_entry sg entry.(TskState) event node selected old /\
    sem_post_wake_result sg event entry wake result /\
    exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer entry wake after,
      sem_pend_sched_prefix_receipt environment critical sg observer entry wake after prefix /\
      (kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_fields_inv local sg active_key wake ** frame) after.
Proof.
  intros environment critical sg observer stored_origin event_observer local active_key entry event node result before after frame
    Hlookup Htype Hgroup Hlayout Hpre Hactual.
  set (abi := environment.(task_stack_call_continuations)).
  set (stacks := store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
    entry.(TskState).(parkedTaskStacks)).
  assert (Hopen : kernel_continuation_inv abi kernel_program_fields_inv local sg active_key entry ** frame |--
    coq_prop (UCOS2_state_inv sg entry /\ task_stack_live_coverage entry.(TskState) active_key) &&
    (kernel_program_fields_inv sg entry ** stacks ** frame)).
  { unfold kernel_continuation_inv, kernel_program_fields_inv, stacks;
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
  assert (Hselected : kernel_continuation_inv abi kernel_program_fields_inv local sg active_key entry ** frame |--
    WakeComponent.event_ready_c_input sg entry event node selected old PendSem PendOK ** residual).
  { intros heap Hheap; destruct (Hopen heap Hheap) as [_ Hresources].
    destruct (Hsplit heap Hresources) as [other [previous [Hother Hraw]]].
    destruct (sem_pend_event_ready_entry_unique sg entry.(TskState) event node selected old other previous
      Hentry Hother) as [-> ->]; exact Hraw. }
  pose proof (sem_post_waiter_source_post sg entry.(TskState) event node selected old
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) result before after residual
    Howned Hactual) as Hpost.
  set (wake := event_wake_state sg entry event node selected old PendSem 0 PendOK).
  assert (Hclose : WakeComponent.event_ready_c_output sg entry event node selected old PendSem 0 PendOK result ** residual
    |-- kernel_continuation_inv abi kernel_program_fields_inv local sg active_key wake ** frame).
  { pose proof (sem_pend_event_ready_fields_merge_continuations environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port) abi sg entry event node
      selected old result local active_key Hvalid Hlookup Htype Hentry Hcoverage) as Hjoin.
    cbn zeta in Hjoin; unfold residual, stacks, wake; sepcon_assoc_change; sep_apply_l_atomic Hjoin.
    unfold kernel_continuation_inv; entailer!. }
  assert (Hwake : sem_post_wake_result sg event entry wake result).
  { assert (Hpriority : result = old.(curPrio)).
    { destruct Hpost as [owned [rest [Hjoin [[[_ Hpriority] Hbody] Hframe]]]]; exact Hpriority. }
    unfold sem_post_wake_result, wake; rewrite Hpriority.
    eapply WakeComponent.event_task_rdy_c_entry_source; eassumption. }
  pose (body := @WakeComponent.KernelWakeCEventSegment sg entry event node selected old PendSem 0 PendOK
    result residual before after Hlookup Hentry Howned Hpost).
  pose (original_step := @KernelProgramCWake environment critical sg observer stored_origin _ _ _ _ _ _ body).
  pose (step := SelectedCProgram.kernel_program_selected_original_step environment critical sg observer stored_origin
    _ _ _ _ _ _ _ original_step).
  pose (segment := SelectedCProgram.kernel_program_selected_c_step environment critical sg observer stored_origin).
  pose (atom := @KernelCSequenceAtom segment _ _ _ _ _ _ _ step).
  pose (run := @KernelCSequenceAdapt segment entry before
    (kernel_continuation_inv abi kernel_program_fields_inv local sg active_key entry ** frame)
    (WakeComponent.event_ready_c_input sg entry event node selected old PendSem PendOK ** residual)
    false wake after
    (WakeComponent.event_ready_c_output sg entry event node selected old PendSem 0 PendOK result ** residual)
    (kernel_continuation_inv abi kernel_program_fields_inv local sg active_key wake ** frame) Hpre Hselected atom Hclose).
  assert (Hsource : SelectedCSource.kernel_program_selected_c_sequence_source environment critical sg observer
    stored_origin event_observer _ _ _ _ _ _ _ run).
  { unfold run; apply KernelCSourceAdapt; unfold atom; apply KernelCSourceAtom.
    unfold step, SelectedCProgram.kernel_program_selected_original_step, original_step.
    apply SelectedCSource.KernelSelectedProgramReturnSource, SelectedCompletionSource.KernelProgramReturnOriginalSource.
    left; constructor. }
  assert (Hreceipt : sem_pend_selected_c_sequence_receipt environment critical sg observer stored_origin
    _ _ _ _ _ _ _ run).
  { unfold run; apply KernelCSourceAdapt; unfold atom; apply KernelCSourceAtom.
    unfold step, SelectedCProgram.kernel_program_selected_original_step, original_step, body.
    apply SemPendSelectedReturnReceipt, SemPendReturnOriginalReceipt, SemPendProgramWakeReceipt,
      SemPendWakeEventReceipt.
    - apply sem_pend_source_state_facts_from_valid; exact Hvalid.
    - rewrite Htype; reflexivity.
    - discriminate. }
  exists selected, old; split; [exact Hentry|]. split; [exact Hwake|].
  exists (@SchedulerPhaseCandidate.OsSchedTaskReturnPrefixCSequence environment critical sg observer
    stored_origin event_observer _ _ _ _ _ _ _ run Hsource).
  split; [constructor; exact Hreceipt|exact (Hclose after Hpost)].
Qed.

Section SemPostFieldsReceipt.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (observer : nat) (stored_origin : TaskInvocationOrigin).
Let segment := kernel_program_c_step environment critical sg observer stored_origin.
Let leaf := sem_pend_sem_post_c_step_certificate environment critical sg observer stored_origin.

(** This is the very Wake proof constructed by the frozen physical SemPost
    producer. Its literal arguments and same pre/post are retained here. *)
Lemma sem_pend_sem_post_c_leaf_receipt : forall state before input stopped returned after output
  (step : segment state before input stopped returned after output) first last,
  leaf state before input stopped returned after output step first last ->
  UCOS2_state_inv sg state ->
  sem_pend_program_c_step_receipt environment critical sg observer stored_origin
    state before input stopped returned after output step /\ UCOS2_state_inv sg returned.
Proof.
  intros state before input stopped returned after output step first last Hcertificate Hvalid.
  destruct Hcertificate as [actor origin entry event node selected old result frame before after
    Hlookup Hentry Hpre Hpost Hmember Hforeign Htype Hgroup Hactual].
  split.
  - apply SemPendProgramWakeReceipt, SemPendWakeEventReceipt.
    + apply sem_pend_source_state_facts_from_valid; exact Hvalid.
    + rewrite Htype; reflexivity.
    + discriminate.
  - eapply kernel_client_preserves_validity.
    + apply (critical_region_client_certificates critical); exact Hmember.
    + exact Hvalid.
    + exists (OS_ERR_NONE, true); eapply sem_post_wake_result_critical;
        [exact Hlookup|exact Hgroup|].
      unfold sem_post_wake_result.
      eapply WakeComponent.event_task_rdy_c_entry_source; eassumption.
Qed.

(** Preserve the original run, including its actual Adapt owner and every
    Then heap. Validity at a later cut follows its registered actual edge. *)
Lemma sem_pend_sem_post_c_sequence_receipt : forall state before input stopped returned after output
  (run : kernel_c_sequence segment state before input stopped returned after output) first last,
  sem_pend_c_sequence_call_certificate segment leaf _ _ _ _ _ _ _ run first last ->
  UCOS2_state_inv sg state ->
  kernel_c_sequence_has_source segment
    (sem_pend_program_c_step_receipt environment critical sg observer stored_origin)
    _ _ _ _ _ _ _ run /\ UCOS2_state_inv sg returned.
Proof.
  intros state before input stopped returned after output run first last Hcertificate.
  induction Hcertificate; intro Hvalid.
  - split; [constructor|exact Hvalid].
  - destruct (sem_pend_sem_post_c_leaf_receipt _ _ _ _ _ _ _ step first last H Hvalid)
      as [Hreceipt Hreturned]; split; [constructor; exact Hreceipt|exact Hreturned].
  - destruct (IHHcertificate1 Hvalid) as [Hfirst Hmiddle].
    destruct (IHHcertificate2 Hmiddle) as [Hlast Hreturned].
    split; [constructor; assumption|exact Hreturned].
  - destruct (IHHcertificate Hvalid) as [Hreceipt Hreturned].
    split; [constructor; exact Hreceipt|exact Hreturned].
Qed.

(** The existing physical producer chooses selected/old and the C run once.
    The client trace is interpreted from that same run's certificate. The
    exact returned fields world is kept with both finite receipts. *)
Lemma sem_pend_sem_post_fields_source_receipts :
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
      sem_pend_c_sequence_call_certificate segment leaf _ _ _ _ _ _ _ run origin origin /\
      kernel_c_sequence_has_source segment
        (sem_pend_program_c_step_receipt environment critical sg observer stored_origin)
        _ _ _ _ _ _ _ run /\
      exists trace : kernel_client_task_source_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
          origin entry false origin wake,
        sem_pend_client_source_local_receipt environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
          origin entry false origin wake trace /\
        (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg wake ** frame) after.
Proof.
  intros local origin actor entry event node returned before after frame
    Hmember Hforeign Hlookup Htype Hgroup Hlayout Hpre Hactual.
  pose proof (sem_pend_fields_world_source_valid _ _ _ _ _ _ _ _ _ Hpre) as Hvalid.
  destruct (sem_pend_sem_post_fields_c_sequence_certificate environment critical sg observer stored_origin
    local origin actor entry event node returned before after frame Hmember Hforeign Hlookup Htype
    Hgroup Hlayout Hpre Hactual) as [selected [old [run [Hcertificate [Htimer Howned]]]]].
  exists selected, old, run; split; [exact Hcertificate|].
  split; [exact (proj1 (sem_pend_sem_post_c_sequence_receipt _ _ _ _ _ _ _ run origin origin Hcertificate Hvalid))|].
  destruct (sem_pend_c_sequence_client_calls segment leaf environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
    (sem_pend_sem_post_c_step_client_calls environment critical sg observer stored_origin)
    _ _ _ _ _ _ _ run origin origin Hcertificate) as [trace Hcalls].
  exists trace; split; [|exact Howned].
  eapply tmr_task_client_source_local_receipt_from_valid; eassumption.
Qed.
End SemPostFieldsReceipt.

(** Erase only the execution-origin annotation. Every original member,
    actor guard, state-step proof and local receipt is kept in the raw tree. *)
Lemma sem_pend_client_local_receipt_raw_trace :
  forall external port clients sg observer event_observer first before stopped last after
    (trace : kernel_client_task_source_trace external port clients sg observer event_observer
      first before stopped last after),
  sem_pend_client_source_local_receipt external port clients sg observer event_observer
    first before stopped last after trace ->
  exists raw : kernel_client_resource_trace clients sg observer event_observer before stopped after,
    sem_pend_source_trace_receipt external clients sg observer event_observer before stopped after raw.
Proof.
  intros external port clients sg observer event_observer first before stopped last after trace Hreceipt.
  induction Hreceipt as [origin state|action first before middle transient last after stopped
    member foreign event_foreign step execution tail Hcall Hfacts Htail IH].
  - exists (@KernelClientTraceNil clients sg observer event_observer state); constructor.
  - destruct IH as [raw Hraw].
    exists (@KernelClientTraceStep clients sg observer event_observer action before transient after stopped
      member foreign event_foreign step raw).
    constructor; assumption.
Qed.

(** This is an actual Legacy Clients prefix produced from the physical
    SemPost run above. It is not selected from an endpoint-only return. *)
Lemma sem_pend_sem_post_fields_prefix_receipt :
  forall environment critical sg observer stored_origin local (origin : TaskInvocationOrigin) actor entry event node returned before after
    (frame : Assertion),
  critical.(critical_region_clients) (sem_pend_post_source_client actor event) -> actor <> observer ->
  sem_post_lookup entry event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group entry node <> 0 -> event_object_layout_prop sg event ->
  (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg entry ** frame) before ->
  sem_post_waiter_execution sg (event_addr sg event) returned before after ->
  exists selected old,
    let wake := event_wake_state sg entry event node selected old PendSem 0 PendOK in
    exists run : kernel_c_sequence (kernel_program_c_step environment critical sg observer stored_origin)
        entry before
        (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg entry ** frame)
        false wake after
        (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg wake ** frame),
      kernel_c_sequence_has_source (kernel_program_c_step environment critical sg observer stored_origin)
        (sem_pend_program_c_step_receipt environment critical sg observer stored_origin)
        _ _ _ _ _ _ _ run /\
      exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix
          environment critical sg observer entry wake after,
        sem_pend_sched_prefix_receipt environment critical sg observer entry wake after prefix /\
        (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg wake ** frame) after.
Proof.
  intros environment critical sg observer stored_origin local origin actor entry event node returned before after frame
    Hmember Hforeign Hlookup Htype Hgroup Hlayout Hpre Hactual.
  destruct (sem_pend_sem_post_fields_source_receipts environment critical sg observer stored_origin
    local origin actor entry event node returned before after frame Hmember Hforeign Hlookup Htype Hgroup
    Hlayout Hpre Hactual) as [selected [old [run [Hcertificate [Hreceipt [trace [Htrace Howned]]]]]]].
  exists selected, old, run; split; [exact Hreceipt|].
  destruct (sem_pend_client_local_receipt_raw_trace _ _ _ _ _ _ _ _ _ _ _ trace Htrace) as [raw Hraw].
  exists (@SchedulerPhaseCandidate.OsSchedTaskReturnPrefixLegacy environment critical sg observer _ _ after
    (@LegacyTaskReturnPrefix.OsSchedTaskReturnPrefixClients environment critical sg observer _ _ after raw)).
  split; [constructor; exact Hraw|exact Howned].
Qed.

(** One concrete registered module component. The request stores only the
    actual caller and event argument. It does not replace the open Extra
    union or claim to interpret its other constructors. *)
Record SemPendFieldsPostCall : Type := {
  sem_pend_fields_post_actor : nat;
  sem_pend_fields_post_event : EventID
}.

Inductive sem_pend_fields_post_heap_execution (sg : StableGlobVars) :
  KernelClientHeapCut SemPendFieldsPostCall -> model ->
  KernelClientHeapCut SemPendFieldsPostCall -> model -> Prop :=
| SemPendFieldsPostHeapExecution : forall request result before after,
    sem_post_waiter_execution sg (event_addr sg request.(sem_pend_fields_post_event)) result before after ->
    sem_pend_fields_post_heap_execution sg (KernelClientHeapExtra request) before KernelClientHeapClosed after.

Inductive sem_pend_fields_post_heap_effect (sg : StableGlobVars) :
  KernelClientHeapCut SemPendFieldsPostCall -> UCOS2_Verify_State ->
  KernelClientHeapCut SemPendFieldsPostCall -> UCOS2_Verify_State -> Prop :=
| SemPendFieldsPostHeapEffect : forall request before after,
    kernel_client_step (sem_pend_post_source_client request.(sem_pend_fields_post_actor)
      request.(sem_pend_fields_post_event)) sg before after ->
    sem_pend_fields_post_heap_effect sg (KernelClientHeapExtra request) before KernelClientHeapClosed after.

(** At the actual Registered/Extra leaf the physical producer supplies the
    state step, receipt and successor owner together, before Hmodules can
    erase either observation. The source action is the outer SemPost. *)
Lemma sem_pend_fields_post_registered_resources :
  forall environment critical local sg observer origin request entry node result before after (frame : Assertion),
  critical.(critical_region_clients)
    (sem_pend_post_source_client request.(sem_pend_fields_post_actor) request.(sem_pend_fields_post_event)) ->
  request.(sem_pend_fields_post_actor) <> observer ->
  sem_post_lookup entry request.(sem_pend_fields_post_event) node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group entry node <> 0 -> event_object_layout_prop sg request.(sem_pend_fields_post_event) ->
  (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg entry ** frame) before ->
  sem_post_waiter_execution sg (event_addr sg request.(sem_pend_fields_post_event)) result before after ->
  kernel_client_heap_step sem_pend_fields_post_heap_execution sg
    (KernelClientHeapExtra request) before KernelClientHeapClosed after /\
  exists current,
    kernel_client_heap_state_step sem_pend_fields_post_heap_effect sg
      (KernelClientHeapExtra request) entry KernelClientHeapClosed current /\
    (exists priority, sem_post_wake_result sg request.(sem_pend_fields_post_event) entry current priority) /\
    (exists trace : kernel_client_task_source_trace environment.(task_stack_call_external)
        environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
        origin entry false origin current,
      sem_pend_client_source_local_receipt environment.(task_stack_call_external)
        environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
        origin entry false origin current trace) /\
    (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg current ** frame) after.
Proof.
  intros environment critical local sg observer origin request entry node result before after frame
    Hmember Hforeign Hlookup Htype Hgroup Hlayout Hpre Hactual.
  split; [apply KernelClientHeapRegistered; econstructor; exact Hactual|].
  pose proof (sem_pend_fields_world_source_valid _ _ _ _ _ _ _ _ _ Hpre) as Hvalid.
  destruct (sem_pend_sem_post_fields_execution_source_receipt environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port) environment.(task_stack_call_continuations)
    local critical.(critical_region_clients) sg observer None origin request.(sem_pend_fields_post_actor)
    entry request.(sem_pend_fields_post_event) node result before after frame
    Hmember Hforeign Hlookup Htype Hgroup Hlayout Hpre Hactual)
    as [selected [old [Hentry [Hhelper [Houter [Hpublic Howned]]]]]].
  pose proof (tmr_task_source_call_receipt_step _ _ _ _ _ Houter) as Hstep.
  destruct (tmr_task_source_call_receipt_step _ _ _ _ _ Hhelper) as [wake_priority Hraw].
  set (wake := event_wake_state sg entry request.(sem_pend_fields_post_event) node selected old PendSem 0 PendOK).
  exists wake; split; [apply KernelClientHeapExtraState, SemPendFieldsPostHeapEffect; exact Hstep|].
  split; [exists wake_priority; exact Hraw|].
  split; [|exact Howned].
  assert (Hactor : kernel_client_actor
    (sem_pend_post_source_client request.(sem_pend_fields_post_actor) request.(sem_pend_fields_post_event)) <>
    Some observer).
  { cbn [sem_pend_post_source_client kernel_client_actor]; congruence. }
  assert (Hevent : forall invocation, None = Some invocation ->
    kernel_client_event_actor
      (sem_pend_post_source_client request.(sem_pend_fields_post_actor) request.(sem_pend_fields_post_event)) <>
      Some invocation) by (intros; discriminate).
  assert (Hexecution : task_execution_source_step environment.(task_stack_call_external)
    environment.(task_stack_call_port) sg origin entry origin wake).
  { eapply TaskExecutionClientFrame; [exact Hstep|].
    exact (proj1 (sem_pend_wake_source_current_timer_frame sg entry wake
      (@WakeComponent.KernelWakeCEventSource sg entry request.(sem_pend_fields_post_event)
        PendSem 0 PendOK wake_priority wake Hraw))). }
  exists (@KernelClientTaskSourceStep environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer None
    (sem_pend_post_source_client request.(sem_pend_fields_post_actor) request.(sem_pend_fields_post_event))
    origin entry origin wake origin wake false Hmember Hactor Hevent Hstep Hexecution
    (@KernelClientTaskSourceNil environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical.(critical_region_clients) sg observer None origin wake)).
  refine (@SemPendClientSourceLocalStep environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer None
    (sem_pend_post_source_client request.(sem_pend_fields_post_actor) request.(sem_pend_fields_post_event))
    origin entry origin wake origin wake false Hmember Hactor Hevent Hstep Hexecution _ Houter _ _).
  - apply sem_pend_source_state_facts_from_valid; exact Hvalid.
  - constructor.
Qed.

(** This producer retains the real prepared heap that exists before the
    literal EventReady call. Its invariant is read there, before the
    critical segment packages only its entry and committed endpoint. *)
Lemma sem_pend_mutex_post_handover_segment_receipt :
  forall environment critical source_env local sg observer origin frame context saved
    entry eid caller caller_node event mutex prepared priority woken found owner before after
    prepared_heap prepared_frame
    Hlookup Htype Hfields Howner Hprepare Hnonempty Hwake Hfound Htable,
  let checkpoint := mutex_post_owner_state woken eid found mutex (Some owner) (Some priority) in
  let call := {| PostComponent.mutex_post_critical_context := context;
    PostComponent.mutex_post_critical_saved := saved;
    PostComponent.mutex_post_critical_entry := entry;
    PostComponent.mutex_post_critical_checkpoint := checkpoint;
    PostComponent.mutex_post_critical_eid := eid;
    PostComponent.mutex_post_critical_caller := caller;
    PostComponent.mutex_post_critical_node := caller_node;
    PostComponent.mutex_post_critical_result := mutex_post_handover_error sg mutex priority;
    PostComponent.mutex_post_critical_schedule := true |} in
  mutex_post_native_caller sg context.(os_sched_call_invocation) context.(os_sched_call_origin)
    entry context caller caller_node ->
  (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical local sg call entry ** frame) before ->
  (UCOS2_inv sg prepared ** prepared_frame) prepared_heap ->
  (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical local sg call checkpoint ** frame) after ->
  exists segment : PostComponent.mutex_post_critical_c_segment source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg frame call before after,
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCMutexPost environment critical sg observer origin source_env local frame call before after segment) /\
    proj2 (PostComponent.mutex_post_critical_segment_source source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg frame call before after segment) =
      (@mutex_post_handover sg eid caller entry event mutex prepared priority woken found owner
        Hlookup Htype Hfields Howner Hprepare Hnonempty Hwake Hfound Htable).
Proof.
  intros environment critical source_env local sg observer origin frame context saved
    entry eid caller caller_node event mutex prepared priority woken found owner before after
    prepared_heap prepared_frame Hlookup Htype Hfields Howner Hprepare Hnonempty Hwake Hfound Htable
    checkpoint call Hnative Hinput Hprepared Houtput.
  assert (Hvalid : UCOS2_state_inv sg prepared).
  { assert (Hopen : UCOS2_inv sg prepared ** prepared_frame |--
        coq_prop (UCOS2_state_inv sg prepared) && (UCOS2_inv sg prepared ** prepared_frame)).
    { unfold UCOS2_inv; entailer!. }
    exact (proj1 (Hopen prepared_heap Hprepared)). }
  pose (Hcritical := @mutex_post_handover sg eid caller entry event mutex prepared priority woken found owner
    Hlookup Htype Hfields Howner Hprepare Hnonempty Hwake Hfound Htable).
  pose (segment := @PostComponent.Build_mutex_post_critical_c_segment source_env
    environment.(task_stack_call_external) environment.(task_stack_call_platform) critical local sg frame call before after
    (conj Hnative Hcritical) Hinput Houtput).
  exists segment; split.
  - apply SemPendProgramMutexPostReceipt.
    unfold segment, call, checkpoint, PostComponent.mutex_post_critical_segment_source.
    cbn.
    rewrite sem_pend_conjunction_second_proof_eq.
    unfold Hcritical; apply sem_pend_mutex_post_handover_c_receipt; exact Hvalid.
  - unfold segment, PostComponent.mutex_post_critical_segment_source.
    rewrite sem_pend_conjunction_second_proof_eq; reflexivity.
Qed.

Import SchedulerCalleePhaseComponent SchedulerPhaseCandidate FlagPendSchedulerResources.

(** The literal C result names the same wake state as the physical producer.
    This equation transports its already constructed prefix and owner; no
    source is chosen from endpoints after forgetting the execution. *)
Lemma sem_pend_sem_post_fields_prefix_returned :
  forall environment critical sg observer (stored_origin : TaskInvocationOrigin) (event_observer : option nat)
    local active_key entry event node result before after current (frame : Assertion),
  sem_post_lookup entry event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group entry node <> 0 -> event_object_layout_prop sg event ->
  (kernel_continuation_inv environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg active_key entry ** frame) before ->
  sem_post_waiter_execution sg (event_addr sg event) result before after ->
  sem_post_wake_result sg event entry current result ->
  exists prefix : os_sched_task_return_prefix environment critical sg observer entry current after,
    sem_pend_sched_prefix_receipt environment critical sg observer entry current after prefix /\
    (kernel_continuation_inv environment.(task_stack_call_continuations)
      kernel_program_fields_inv local sg active_key current ** frame) after.
Proof.
  intros environment critical sg observer stored_origin event_observer local active_key entry event node
    result before after current frame Hlookup Htype Hgroup Hlayout Hpre Hactual Hresult.
  destruct (sem_pend_sem_post_fields_selected_prefix environment critical sg observer stored_origin
    event_observer local active_key entry event node result before after frame
    Hlookup Htype Hgroup Hlayout Hpre Hactual)
    as [selected [old [Hentry [Hwake [prefix [Hreceipt Howned]]]]]].
  assert (Heq : current = event_wake_state sg entry event node selected old PendSem 0 PendOK).
  { unfold sem_post_wake_result in Hresult, Hwake; congruence. }
  subst current; exists prefix; exact (conj Hreceipt Howned).
Qed.

(** Actual Task install/restore after the typed SemPost prefix.  The prefix
    factory's returned fields/map owner is rearranged into the install input
    on that same heap.  Hrestore supplies one selected call, and Hclose
    retains its very body proof together with its finite receipt. *)
Lemma sem_pend_sem_post_task_switch_body_receipt : forall environment critical
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg entry first_installed initial_local active initial_heap context outgoing hooked original saved acquired
  receipt other resumed prefix_before before event node result (stored_origin : TaskInvocationOrigin) (event_observer : option nat),
  let abi := environment.(task_stack_call_continuations) in
  let local := kernel_sched_saved_local_resource_at environment.(task_stack_call_platform) critical sg
    hooked.(TskState) original saved acquired receipt other in
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  os_sched_task_switch_pre environment critical initial_local active sg original saved acquired entry initial_heap ->
  os_sched_switch_source environment.(task_stack_call_external) sg entry original first_installed ->
  kernel_client_stops environment.(task_stack_call_external).(os_sched_hook_action)
    original.(os_sched_call_invocation) = false ->
  kernel_call_control_rely sg entry hooked ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding environment.(task_stack_call_external)
    context outgoing hooked original.(os_sched_call_stack) resumed ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  (forall returned, task_tcb_init_stack_same_call returned original -> kernel_call_task_source returned current ->
    os_sched_task_current_ready returned current -> receipt |-- active returned current) ->
  sem_post_lookup first_installed event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group first_installed node <> 0 -> event_object_layout_prop sg event ->
  (kernel_continuation_inv abi kernel_program_fields_inv local sg
    (Some (task_stack_key context.(os_sched_call_stack))) first_installed **
    (task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
     resource (task_stack_key context.(os_sched_call_stack)) (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
     armv7a_task_switch_control task_abi context)) prefix_before ->
  sem_post_waiter_execution sg (event_addr sg event) result prefix_before before ->
  sem_post_wake_result sg event first_installed hooked result ->
  exists installed selected,
    sched_install_heap_fragment sg before installed (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    (forall restored, armv7a_task_restore_transition task_abi context selected installed restored ->
      os_sched_task_switch_pre environment critical initial_local active sg original saved acquired entry initial_heap /\
      (EX returned current next_local,
        coq_prop (exists body : os_sched_task_body_source environment critical sg entry original returned current,
          sem_pend_sched_body_receipt environment critical sg entry original returned current body /\
          os_sched_task_current_ready returned current /\
          kernel_call_normal_return original entry returned current /\ kernel_call_control_rely sg entry current /\
          (kernel_call_task_source original entry -> kernel_call_task_source returned current)) &&
        (kernel_continuation_call_masked abi kernel_program_fields_inv next_local critical sg
          (task_stack_call_active_key returned) returned saved acquired current ** active returned current)) restored).
Proof.
  intros environment critical task_abi sg entry first_installed initial_local active initial_heap context outgoing hooked
    original saved acquired receipt other resumed prefix_before before event node result stored_origin event_observer
    abi local resource current Hinitial Hfirst Hhook Hcontrol Hhigh Hsaved Hdestination Haddress Hactive
    Hlookup Htype Hgroup Hlayout Hprefix_pre Hactual_post Hresult.
  destruct (sem_pend_sem_post_fields_prefix_returned environment critical sg original.(os_sched_call_invocation)
    stored_origin event_observer local (Some (task_stack_key context.(os_sched_call_stack)))
    first_installed event node result prefix_before before hooked _ Hlookup Htype Hgroup Hlayout Hprefix_pre
    Hactual_post Hresult) as [prefix [Hprefix_receipt Hprefix_owner]].
  assert (Hopen : kernel_continuation_inv abi kernel_program_fields_inv local sg
      (Some (task_stack_key context.(os_sched_call_stack))) hooked **
      (task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
       resource (task_stack_key context.(os_sched_call_stack)) (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
       armv7a_task_switch_control task_abi context) |--
    coq_prop (UCOS2_state_inv sg hooked /\ task_stack_live_coverage hooked.(TskState)
      (Some (task_stack_key context.(os_sched_call_stack)))) &&
    (UCOS2_fields_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
     resource (task_stack_key context.(os_sched_call_stack)) (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
     store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
     (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** emp))).
  { unfold kernel_continuation_inv; rewrite kernel_program_fields_inv_split_unmap.
    unfold resource, UCOS2_fields_inv; entailer!. }
  destruct (Hopen before Hprefix_owner) as [[Hvalid Hcoverage] Hpre].
  destruct (os_sched_task_selected_masked_return_source environment critical task_abi sg context outgoing hooked
    original saved acquired receipt other resumed before emp Hvalid Hhigh Hsaved Hdestination Haddress Hcoverage Hpre)
    as [installed [selected [Hinstall [Hreads [Hlease Hrestore]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  intros restored Hactual.
  destruct (Hrestore restored Hactual) as [Hcall [Hsame [Hsource [Hready [Hnormal [Hcontrols [Hresume Howned]]]]]]].
  set (returned := kernel_selected_call selected current) in *.
  pose (body := @OsSchedTaskBodyTaskLastInstall environment critical sg entry original first_installed
    context outgoing hooked resumed returned before Hfirst prefix Hhook Hsaved Hdestination Hhigh Hsame).
  assert (Hbody_receipt : sem_pend_sched_body_receipt environment critical sg entry original returned current body).
  { unfold body; constructor; exact Hprefix_receipt. }
  pose proof (os_sched_task_selected_body_observation environment critical sg original entry context outgoing hooked
    original.(os_sched_call_stack) resumed returned Hvalid Hhigh Hdestination (proj2 (proj2 Hsame))
    Hsource Hsame Hcontrol body) as Hobserved.
  split; [exact Hinitial|]. exists returned, current, other; split.
  - exists body; split; [exact Hbody_receipt|exact (proj2 Hobserved)].
  - match type of Howned with ?P restored => match goal with |- ?Q restored => assert (Hclose : P |-- Q) end end.
    { sep_apply_l_atomic (Hactive returned Hsame Hsource
        (os_sched_task_ready_source_current_ready environment sg returned current Hready)); entailer!. }
    exact (Hclose restored Howned).
Qed.

(** The IRQ case additionally consumes the actual counter/selector and
    configured no-write hook. Their existing fields producer carries the
    SemPost owner's continuation map to the precise install cut. *)
Lemma sem_pend_sem_post_irq_switch_body_receipt : forall environment critical
  sg entry first_installed initial_local active initial_heap handler irq_entry transfer
  original saved acquired receipt other prefix_before irq_before prepared before event node result
  (stored_origin : TaskInvocationOrigin) (event_observer : option nat),
  let configured := task_sw_hook_call_environment environment in
  let abi := configured.(task_stack_call_continuations) in
  let hooked := transfer.(os_int_exit_hooked_state) in
  let local := kernel_sched_saved_local_resource_at configured.(task_stack_call_platform) critical sg
    irq_entry.(TskState) original saved acquired receipt other in
  let current := os_int_exit_installed_state transfer in
  os_sched_task_switch_pre configured critical initial_local active sg original saved acquired entry initial_heap ->
  os_sched_switch_source configured.(task_stack_call_external) sg entry original first_installed ->
  forall (transfer_source : os_int_exit_transfer_source configured.(task_stack_call_external)
      configured.(task_stack_call_port) sg handler irq_entry transfer)
    (irq_prefix : os_int_exit_source_switch_prefix_execution sg irq_before prepared)
    (irq_hook : kernel_heap_execution [] prepared before),
  kernel_call_control_rely sg entry hooked ->
  transfer.(os_int_exit_incoming_stack) = original.(os_sched_call_stack) ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  (forall returned, task_tcb_init_stack_same_call returned original -> kernel_call_task_source returned current ->
    os_sched_task_current_ready returned current ->
    receipt ** task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments)
      |-- active returned current) ->
  sem_post_lookup first_installed event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group first_installed node <> 0 -> event_object_layout_prop sg event ->
  (kernel_continuation_inv abi kernel_program_fields_inv local sg None first_installed **
    (interrupt_platform_running configured.(task_stack_call_platform)
       handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources configured.(task_stack_call_port) handler)) prefix_before ->
  sem_post_waiter_execution sg (event_addr sg event) result prefix_before irq_before ->
  sem_post_wake_result sg event first_installed irq_entry result ->
  exists installed selected,
    sched_install_heap_fragment sg before installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    (forall irq_return, armv7a_restore_transition abi handler selected installed irq_return ->
      os_sched_task_switch_pre configured critical initial_local active sg original saved acquired entry initial_heap /\
      (EX returned current next_local,
        coq_prop (exists body : os_sched_task_body_source configured critical sg entry original returned current,
          sem_pend_sched_body_receipt configured critical sg entry original returned current body /\
          os_sched_task_current_ready returned current /\
          kernel_call_normal_return original entry returned current /\ kernel_call_control_rely sg entry current /\
          (kernel_call_task_source original entry -> kernel_call_task_source returned current)) &&
        (kernel_continuation_call_masked abi kernel_program_fields_inv next_local critical sg
          (task_stack_call_active_key returned) returned saved acquired current ** active returned current)) irq_return).
Proof.
  intros environment critical sg entry first_installed initial_local active initial_heap handler irq_entry transfer
    original saved acquired receipt other prefix_before irq_before prepared before event node result stored_origin event_observer
    configured abi hooked local current Hinitial Hfirst transfer_source irq_prefix irq_hook Hcontrol Hincoming Haddress Hactive
    Hlookup Htype Hgroup Hlayout Hprefix_pre Hactual_post Hresult.
  destruct (sem_pend_sem_post_fields_prefix_returned configured critical sg original.(os_sched_call_invocation)
    stored_origin event_observer local None first_installed event node result prefix_before irq_before irq_entry _
    Hlookup Htype Hgroup Hlayout Hprefix_pre Hactual_post Hresult) as [prefix [Hprefix_receipt Hprefix_owner]].
  assert (Hopen : kernel_continuation_inv abi kernel_program_fields_inv local sg None irq_entry **
      (interrupt_platform_running configured.(task_stack_call_platform)
         handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources configured.(task_stack_call_port) handler) |--
    coq_prop (task_stack_live_coverage irq_entry.(TskState) None) &&
      IRQCPrefix.os_int_exit_prefix_fields_owner configured critical sg handler irq_entry
        original saved acquired receipt other emp).
  { unfold kernel_continuation_inv, IRQCPrefix.os_int_exit_prefix_fields_owner, local;
      rewrite kernel_program_fields_inv_split_unmap; entailer!. }
  destruct (Hopen irq_before Hprefix_owner) as [Hcoverage Hirq_input].
  destruct (IRQCPrefix.os_int_exit_configured_c_prefix_fields_resources environment critical sg handler irq_entry transfer
    original saved acquired receipt other emp irq_before prepared before transfer_source irq_prefix irq_hook Hirq_input)
    as [Hhigh Hpre].
  assert (Hcoverage_hooked : task_stack_live_coverage hooked.(TskState) None).
  { pose proof transfer_source as [_ [_ [_ [Hhook _]]]].
    change (hooked = os_int_exit_ready_checkpoint true irq_entry) in Hhook.
    rewrite Hhook; exact Hcoverage. }
  destruct (os_sched_task_irq_selected_masked_return_source configured critical sg handler irq_entry transfer
    original saved acquired receipt other before emp transfer_source Hhigh Hincoming Haddress Hcoverage_hooked Hpre)
    as [installed [selected [Hlease [Hsp [Hfragments [Hcall [Hpc [Hmask
      [Hinstall [Hpointers [Hreads Hrestore]]]]]]]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  intros irq_return Hactual.
  destruct (Hrestore irq_return Hactual) as [Hmemory [Hsame [Hsource [Hready [Hcurrent_ready
    [Hnormal [Hcontrols Howned]]]]]]].
  set (returned := armv7a_continuation_resumed_call selected original) in *.
  pose (irq_source_prefix := @or_intror
    (kernel_client_trace critical.(critical_region_clients) sg original.(os_sched_call_invocation)
      first_installed false irq_entry)
    (exists final_heap, os_sched_task_return_prefix configured critical sg original.(os_sched_call_invocation)
      first_installed irq_entry final_heap) (ex_intro _ irq_before prefix)).
  assert (Hhook : kernel_client_stops configured.(task_stack_call_external).(os_sched_hook_action)
      original.(os_sched_call_invocation) = false) by reflexivity.
  pose (body := @OsSchedTaskBodyIRQLastInstall configured critical sg entry original first_installed handler irq_entry transfer
    returned Hfirst irq_source_prefix Hhook transfer_source Hincoming Hsame).
  assert (Hbody_receipt : sem_pend_sched_body_receipt configured critical sg entry original returned current body).
  { unfold body; constructor; unfold irq_source_prefix; constructor; exact Hprefix_receipt. }
  assert (Hreturned_normal : kernel_call_normal_return original entry returned current).
  { split; [exact Hsame|]. intro Havailable.
    unfold kernel_call_stack_available; rewrite (proj1 Hsource).
    change (task_stack_take hooked.(TskState).(parkedTaskStacks) transfer.(os_int_exit_incoming_stack)
      (task_stack_key returned.(os_sched_call_stack)) = None).
    assert (Hstack : returned.(os_sched_call_stack) = transfer.(os_int_exit_incoming_stack)).
    { unfold returned; cbn; congruence. }
    rewrite Hstack; apply task_stack_take_lookup. }
  split; [exact Hinitial|]. exists returned, current, other; split.
  - exists body; split; [exact Hbody_receipt|]. split; [exact Hcurrent_ready|].
    split; [exact Hreturned_normal|]. split; [eapply kernel_call_control_rely_trans; eassumption|intros; exact Hsource].
  - match type of Howned with ?P irq_return => match goal with |- ?Q irq_return => assert (Hclose : P |-- Q) end end.
    { sep_apply_l_atomic (Hactive returned Hsame Hsource Hcurrent_ready); entailer!. }
    exact (Hclose irq_return Howned).
Qed.

(** The complete last-call constructor uses the same physical prefix and
    the last invocation's actual switch source. Its normal returned-call
    identity and Task source are the existing callee contract observations;
    no task-ABI arch_resume observation is required here. *)
Lemma sem_pend_sem_post_last_call_body_receipt :
  forall environment critical sg entry original first_installed last_entry last_context returned current
    local active_key event node result before after (frame : Assertion)
    (stored_origin : TaskInvocationOrigin) (event_observer : option nat),
  os_sched_switch_source environment.(task_stack_call_external) sg entry original first_installed ->
  sem_post_lookup first_installed event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group first_installed node <> 0 -> event_object_layout_prop sg event ->
  (kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_fields_inv
    local sg active_key first_installed ** frame) before ->
  sem_post_waiter_execution sg (event_addr sg event) result before after ->
  sem_post_wake_result sg event first_installed last_entry result ->
  os_sched_switch_source environment.(task_stack_call_external) sg last_entry last_context current ->
  task_tcb_init_stack_same_call returned original -> kernel_call_task_source returned current ->
  exists body : os_sched_task_body_source environment critical sg entry original returned current,
    sem_pend_sched_body_receipt environment critical sg entry original returned current body /\
    (kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_fields_inv
      local sg active_key last_entry ** frame) after.
Proof.
  intros environment critical sg entry original first_installed last_entry last_context returned current
    local active_key event node result before after frame stored_origin event_observer Hfirst
    Hlookup Htype Hgroup Hlayout Hpre Hactual Hresult Hlast Hsame Htask.
  destruct (sem_pend_sem_post_fields_prefix_returned environment critical sg original.(os_sched_call_invocation)
    stored_origin event_observer local active_key first_installed event node result before after last_entry frame
    Hlookup Htype Hgroup Hlayout Hpre Hactual Hresult) as [prefix [Hreceipt Howned]].
  assert (Hvalid : UCOS2_state_inv sg last_entry).
  { match type of Howned with ?P after => assert (Hopen : P |-- coq_prop (UCOS2_state_inv sg last_entry) && P) end.
    { unfold kernel_continuation_inv, kernel_program_fields_inv; entailer!. }
    exact (proj1 (Hopen after Howned)). }
  exists (@OsSchedTaskBodyTaskLastCall environment critical sg entry original first_installed last_entry
    last_context returned current after Hfirst prefix Hvalid Hlast Hsame Htask).
  split; [constructor; exact Hreceipt|exact Howned].
Qed.

(** At the unchanged equal-priority C branch the selector observations
    already produce the NoSwitch body, so its finite receipt is immediate. *)
Lemma sem_pend_nonswitch_body_receipt : forall environment critical sg original entry,
  UCOS2_state_inv sg entry -> kernel_call_task_source original entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  os_sched_selection_enabled entry = true -> os_sched_requests_switch entry = false ->
  entry.(SchedState).(readyList) <> [] ->
  exists body : os_sched_task_body_source environment critical sg entry original original (os_sched_prefix_state entry),
    sem_pend_sched_body_receipt environment critical sg entry original original (os_sched_prefix_state entry) body /\
    os_sched_task_current_ready original (os_sched_prefix_state entry) /\
    kernel_call_normal_return original entry original (os_sched_prefix_state entry) /\
    kernel_call_control_rely sg entry (os_sched_prefix_state entry) /\
    (kernel_call_task_source original entry -> kernel_call_task_source original (os_sched_prefix_state entry)).
Proof.
  intros environment critical sg original entry Hvalid Htask Hcurrent Henabled Hrequest Hnonempty.
  pose proof (os_sched_task_nonswitch_body_observation environment critical sg original entry
    Hvalid Htask Hcurrent Henabled Hrequest Hnonempty) as Hobserved.
  exists (@OsSchedTaskBodyNoSwitch environment critical sg entry original Hrequest).
  split; [constructor|exact (proj2 Hobserved)].
Qed.

(** The prepared-cut packet is consumed immediately by the unchanged
    selected C prefix constructor. The literal critical execution proof,
    its input/output owners and its intermediate prepared owner stay tied
    to the same segment produced above. *)
Lemma sem_pend_mutex_post_handover_prefix_receipt :
  forall environment critical source_env local sg observer (origin : TaskInvocationOrigin) (event_observer : option nat)
    frame context saved entry eid caller caller_node event mutex prepared priority woken found owner before after
    prepared_heap prepared_frame
    Hlookup Htype Hfields Howner Hprepare Hnonempty Hwake Hfound Htable,
  let checkpoint := mutex_post_owner_state woken eid found mutex (Some owner) (Some priority) in
  let call := {| PostComponent.mutex_post_critical_context := context;
    PostComponent.mutex_post_critical_saved := saved;
    PostComponent.mutex_post_critical_entry := entry;
    PostComponent.mutex_post_critical_checkpoint := checkpoint;
    PostComponent.mutex_post_critical_eid := eid;
    PostComponent.mutex_post_critical_caller := caller;
    PostComponent.mutex_post_critical_node := caller_node;
    PostComponent.mutex_post_critical_result := mutex_post_handover_error sg mutex priority;
    PostComponent.mutex_post_critical_schedule := true |} in
  mutex_post_native_caller sg context.(os_sched_call_invocation) context.(os_sched_call_origin)
    entry context caller caller_node ->
  (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical local sg call entry ** frame) before ->
  (UCOS2_inv sg prepared ** prepared_frame) prepared_heap ->
  (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical local sg call checkpoint ** frame) after ->
  exists segment : PostComponent.mutex_post_critical_c_segment source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg frame call before after,
    (exists prefix : os_sched_task_return_prefix environment critical sg observer entry checkpoint after,
      sem_pend_sched_prefix_receipt environment critical sg observer entry checkpoint after prefix) /\
    proj2 (PostComponent.mutex_post_critical_segment_source source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg frame call before after segment) =
      (@mutex_post_handover sg eid caller entry event mutex prepared priority woken found owner
        Hlookup Htype Hfields Howner Hprepare Hnonempty Hwake Hfound Htable).
Proof.
  intros environment critical source_env local sg observer origin event_observer frame context saved entry eid caller
    caller_node event mutex prepared priority woken found owner before after prepared_heap prepared_frame
    Hlookup Htype Hfields Howner Hprepare Hnonempty Hwake Hfound Htable checkpoint call
    Hnative Hinput Hprepared Houtput.
  destruct (sem_pend_mutex_post_handover_segment_receipt environment critical source_env local sg observer origin
    frame context saved entry eid caller caller_node event mutex prepared priority woken found owner before after
    prepared_heap prepared_frame Hlookup Htype Hfields Howner Hprepare Hnonempty Hwake Hfound Htable
    Hnative Hinput Hprepared Houtput) as [segment [Hreceipt Hcritical]].
  pose (step := @KernelProgramCMutexPost environment critical sg observer origin source_env local frame call before after segment).
  pose (selected_step := SelectedCProgram.kernel_program_selected_original_step environment critical sg observer origin
    _ _ _ _ _ _ _ step).
  pose (run := @KernelCSequenceAtom (SelectedCProgram.kernel_program_selected_c_step environment critical sg observer origin)
    _ _ _ _ _ _ _ selected_step).
  assert (Hsource : SelectedCSource.kernel_program_selected_c_sequence_source environment critical sg observer
    origin event_observer _ _ _ _ _ _ _ run).
  { unfold run; constructor; unfold selected_step, SelectedCProgram.kernel_program_selected_original_step, step.
    apply SelectedCSource.KernelSelectedProgramReturnSource, SelectedCompletionSource.KernelProgramReturnOriginalSource.
    right; constructor. }
  assert (Hrun_receipt : sem_pend_selected_c_sequence_receipt environment critical sg observer origin _ _ _ _ _ _ _ run).
  { unfold run; constructor; unfold selected_step, SelectedCProgram.kernel_program_selected_original_step, step.
    apply SemPendSelectedReturnReceipt, SemPendReturnOriginalReceipt; exact Hreceipt. }
  exists segment; split; [|exact Hcritical].
  exists (@OsSchedTaskReturnPrefixCSequence environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ run Hsource); constructor; exact Hrun_receipt.
Qed.
