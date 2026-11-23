Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_call_value_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_return_facts_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_wake_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_source_spec.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.task.spec.task_sw_hook_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_idle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_history_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_idle_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_completion_composition_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_fields_resources_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_idle_return_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_registered_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_api_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_c_step_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_selected_c_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_callee_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.lib.kernel_program_storage.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Import CriticalComponent PrimitiveComponent SelectedReturnPrimitive SelectedCProgram.
Import SelectedIdleComposition SelectedIdleFrames SelectedIdleWakeStatus SelectedIdleBuiltin.
Import SelectedIdleCritical SelectedMutexIdle SelectedDeleteIdle SelectedControlComposition.
Import SchedulerPhaseCandidate SchedulerCalleePhaseComponent FlagPendSchedulerResources TerminalCallValue.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition tmr_task_actual_body_idle_post environment critical active sg original saved acquired entry : Assertion :=
  EX returned current next_local,
    coq_prop (exists body : os_sched_task_body_source environment critical sg entry original returned current,
      sem_pend_sched_body_receipt environment critical sg entry original returned current body /\
      os_sched_task_body_observation environment critical sg original entry returned current /\
      task_idle_ready sg current.(TskState) /\ flag_pend_non_idle_at sg returned current) &&
    (kernel_continuation_call_masked environment.(task_stack_call_continuations) kernel_program_fields_inv
      next_local critical sg (task_stack_call_active_key returned) returned saved acquired current ** active returned current).

(** Eight of the original thirteen constructors are the existing
    remaining-source family. Their actual C segments need no Idle guard. *)
Lemma tmr_task_remaining_c_source_idle_receipt :
  forall environment critical sg observer origin state before input stopped current after output step,
  kernel_program_c_step_remaining_source environment critical sg observer origin
    state before input stopped current after output step ->
  tmr_task_program_c_idle_receipt environment critical sg observer origin
    state before input stopped current after output step.
Proof.
  intros environment critical sg observer origin state before input stopped current after output step Hsource.
  destruct Hsource; apply TmrTaskProgramExistingIdleReceipt; constructor.
Qed.

Lemma tmr_task_wake_c_source_idle_receipt : forall environment critical sg observer origin
  state before input current after output
  (actual : WakeComponent.kernel_wake_c_segment sg state before input current after output),
  tmr_task_program_c_idle_receipt environment critical sg observer origin _ _ _ _ _ _ _
    (@KernelProgramCWake environment critical sg observer origin state before input current after output actual).
Proof. intros; apply TmrTaskProgramExistingIdleReceipt; constructor. Qed.

Lemma tmr_task_creation_c_source_idle_receipt : forall environment critical sg observer origin
  state before input current after output
  (actual : CreationComponent.kernel_task_creation_c_segment sg state before input current after output),
  tmr_task_program_c_idle_receipt environment critical sg observer origin _ _ _ _ _ _ _
    (@KernelProgramCTaskCreation environment critical sg observer origin state before input current after output actual).
Proof. intros; apply TmrTaskProgramExistingIdleReceipt; constructor. Qed.

Lemma tmr_task_event_creation_c_source_idle_receipt : forall environment critical sg observer origin
  state before input current after output
  (actual : EventCreationComponent.kernel_event_creation_c_segment sg state before input current after output),
  tmr_task_program_c_idle_receipt environment critical sg observer origin _ _ _ _ _ _ _
    (@KernelProgramCEventCreation environment critical sg observer origin state before input current after output actual).
Proof. intros; apply TmrTaskProgramExistingIdleReceipt; constructor. Qed.

Lemma tmr_task_queue_creation_c_source_idle_receipt : forall environment critical sg observer origin
  state before input current after output
  (actual : QueueCreationComponent.kernel_queue_creation_c_segment sg state before input current after output),
  tmr_task_program_c_idle_receipt environment critical sg observer origin _ _ _ _ _ _ _
    (@KernelProgramCQueueCreation environment critical sg observer origin state before input current after output actual).
Proof. intros; apply TmrTaskProgramExistingIdleReceipt; constructor. Qed.

(** A local atomic composition rule. The source and Idle observations are
    about the same step; the C sequence and old prefix are constructed once. *)
Lemma tmr_task_original_c_idle_prefix : forall environment critical sg observer origin event_observer
  state before input stopped current after output
  (step : kernel_program_c_step environment critical sg observer origin state before input stopped current after output),
  kernel_program_c_step_call_source environment critical sg observer origin event_observer
    state before input stopped current after output step ->
  tmr_task_program_c_idle_receipt environment critical sg observer origin
    state before input stopped current after output step ->
  exists (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    state before input stopped current after output),
    SelectedCSource.kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
      _ _ _ _ _ _ _ run /\
    tmr_task_selected_sequence_idle_receipt environment critical sg observer origin _ _ _ _ _ _ _ run /\
    SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer state current after.
Proof.
  intros environment critical sg observer origin event_observer state before input stopped current after output step Hsource Hidle.
  pose (returned := @KernelProgramReturnOriginal environment critical sg observer origin _ _ _ _ _ _ _ step).
  pose (selected := @KernelSelectedProgramReturn critical sg observer origin environment _ _ _ _ _ _ _ returned).
  pose (run := KernelCSequenceAtom _ _ _ _ _ _ _ _ selected).
  assert (Hrun : SelectedCSource.kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ run).
  { apply KernelCSourceAtom; unfold selected, returned; constructor; constructor; exact Hsource. }
  exists run; split; [exact Hrun|]. split.
  - apply KernelCSourceAtom; unfold selected, returned.
    constructor; constructor; exact Hidle.
  - eapply SchedulerPhaseCandidate.os_sched_task_c_sequence_prefix; exact Hrun.
Qed.

(** This is the old Status factory's real input/post cut. The protected
    fact is retained before the segment record hides it. No final public
    owner is used to reconstruct either intermediate heap. *)
Lemma tmr_task_suspend_protected_c_post_prefix :
  forall environment critical sg observer (origin : TaskInvocationOrigin) (event_observer : option nat) request priority error scheduled
    entry before legacy_result current after frame,
  (UCOS2_inv sg entry ** frame) before ->
  (coq_prop (task_suspend_critical sg request entry legacy_result current /\
     task_suspend_protected sg request priority entry (error, scheduled) current) &&
    (UCOS2_inv sg current ** frame)) after ->
  exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer entry current after,
    sem_pend_sched_prefix_receipt environment critical sg observer entry current after prefix /\
    (forall observed,
      (task_idle_ready sg entry.(TskState) -> task_idle_ready sg current.(TskState)) /\
      (flag_pend_non_idle_at sg observed entry -> flag_pend_non_idle_at sg observed current)).
Proof.
  intros environment critical sg observer origin event_observer request priority error scheduled
    entry before legacy_result current after frame Hinput [[Hlegacy Hprotected] Houtput].
  pose (segment := {| StatusComponent.kernel_status_c_segment_code :=
    StatusComponent.KernelStatusCSuspendSource sg entry request legacy_result current Hlegacy;
    StatusComponent.kernel_status_c_segment_input := Hinput;
    StatusComponent.kernel_status_c_segment_output := Houtput |}).
  exact (tmr_task_protected_status_prefix environment critical sg observer origin event_observer
    entry before current after frame segment request priority error scheduled legacy_result Hlegacy eq_refl Hprotected).
Qed.

Lemma tmr_task_resume_critical_c_post_prefix :
  forall environment critical sg observer origin event_observer priority entry before result current after frame,
  (UCOS2_inv sg entry ** frame) before ->
  (coq_prop (task_resume_critical sg priority entry result current) && (UCOS2_inv sg current ** frame)) after ->
  exists (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    entry before (UCOS2_inv sg entry ** frame) false current after (UCOS2_inv sg current ** frame)),
    SelectedCSource.kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
      _ _ _ _ _ _ _ run /\
    tmr_task_selected_sequence_idle_receipt environment critical sg observer origin _ _ _ _ _ _ _ run /\
    SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer entry current after.
Proof.
  intros environment critical sg observer origin event_observer priority entry before result current after frame Hinput [Hcode Houtput].
  pose (segment := {| StatusComponent.kernel_status_c_segment_code :=
    StatusComponent.KernelStatusCResumeSource sg entry priority result current Hcode;
    StatusComponent.kernel_status_c_segment_input := Hinput;
    StatusComponent.kernel_status_c_segment_output := Houtput |}).
  eapply tmr_task_original_c_idle_prefix with (step := @KernelProgramCStatus environment critical sg observer origin
    entry before current after frame segment).
  - left; constructor.
  - apply TmrTaskProgramExistingIdleReceipt; constructor; unfold segment; cbn; constructor.
Qed.

Lemma tmr_task_sem_accept_critical_c_post_prefix :
  forall environment critical sg observer origin event_observer eid entry before count current after frame,
  (UCOS2_inv sg entry ** frame) before ->
  (coq_prop (sem_accept_critical sg eid entry count current) && (UCOS2_inv sg current ** frame)) after ->
  exists (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    entry before (UCOS2_inv sg entry ** frame) false current after (UCOS2_inv sg current ** frame)),
    SelectedCSource.kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
      _ _ _ _ _ _ _ run /\
    tmr_task_selected_sequence_idle_receipt environment critical sg observer origin _ _ _ _ _ _ _ run /\
    SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer entry current after.
Proof.
  intros environment critical sg observer origin event_observer eid entry before count current after frame Hinput [Hcode Houtput].
  pose (segment := {| StatusComponent.kernel_status_c_segment_code :=
    StatusComponent.KernelStatusCSemAcceptSource sg entry eid count current Hcode;
    StatusComponent.kernel_status_c_segment_input := Hinput;
    StatusComponent.kernel_status_c_segment_output := Houtput |}).
  eapply tmr_task_original_c_idle_prefix with (step := @KernelProgramCStatus environment critical sg observer origin
    entry before current after frame segment).
  - left; constructor.
  - apply TmrTaskProgramExistingIdleReceipt; constructor; unfold segment; cbn; constructor.
Qed.

(** The three non-Original return constructors and the two non-Return
    selected constructors already retain their actual completion source. *)
Lemma tmr_task_selected_return_primitive_idle_receipt : forall environment critical sg observer origin
  state before input stopped current after output actual,
  tmr_task_return_c_idle_receipt environment critical sg observer origin _ _ _ _ _ _ _
    (@KernelProgramReturnSelected environment critical sg observer origin state before input stopped current after output actual).
Proof. intros; apply TmrTaskReturnExistingIdleReceipt; constructor. Qed.

Lemma tmr_task_selected_task_install_idle_receipt : forall environment critical sg observer origin
  local frame call before installed sp actual complete selected terminal owner,
  tmr_task_return_c_idle_receipt environment critical sg observer origin _ _ _ _ _ _ _
    (@KernelProgramReturnTaskSelectedInstall environment critical sg observer origin local frame call before installed sp actual
      complete selected terminal owner).
Proof. intros; apply TmrTaskReturnExistingIdleReceipt; constructor. Qed.

Lemma tmr_task_selected_irq_suffix_idle_receipt : forall environment critical sg observer origin
  handler entry transfer original saved acquired receipt other frame before installed selected after source install restore complete,
  tmr_task_return_c_idle_receipt environment critical sg observer origin _ _ _ _ _ _ _
    (@KernelProgramReturnIRQSelectedSuffix environment critical sg observer origin handler entry transfer original saved acquired
      receipt other frame before installed selected after source install restore complete).
Proof. intros; apply TmrTaskReturnExistingIdleReceipt; constructor. Qed.

Lemma tmr_task_acquired_irq_idle_receipt : forall environment critical sg observer origin
  state before input stopped current after output actual,
  tmr_task_selected_c_idle_receipt critical sg observer origin (task_sw_hook_call_environment environment) _ _ _ _ _ _ _
    (@KernelSelectedProgramIRQ critical sg observer origin environment state before input stopped current after output actual).
Proof. intros; apply TmrTaskSelectedExistingIdleReceipt; constructor. Qed.

Lemma tmr_task_masked_suspend_idle_receipt : forall environment critical sg observer origin
  state before input stopped current after output actual,
  tmr_task_selected_c_idle_receipt critical sg observer origin environment _ _ _ _ _ _ _
    (@KernelSelectedProgramSuspend critical sg observer origin environment state before input stopped current after output actual).
Proof. intros; apply TmrTaskSelectedExistingIdleReceipt; constructor. Qed.

Lemma tmr_task_existing_selected_sequence_idle_receipt :
  forall environment critical sg observer origin state before input stopped current after output run,
  kernel_program_selected_sequence_idle_source environment critical sg observer origin
    state before input stopped current after output run ->
  tmr_task_selected_sequence_idle_receipt environment critical sg observer origin
    state before input stopped current after output run.
Proof.
  intros environment critical sg observer origin state before input stopped current after output run Hsource.
  induction Hsource; constructor; try assumption.
  apply TmrTaskSelectedExistingIdleReceipt; exact H.
Qed.

(** This public-C acquired cut includes the actual read view and both
    masked heaps. It covers the real selected Suspend constructor without
    converting the public protected relation to the older critical model. *)
Lemma tmr_task_suspend_acquired_c_post_prefix :
  forall environment critical saved_local sg original mask original_state caller saved call frame before after
    observer origin event_observer,
  task_suspend_acquired_facts critical sg original call.(TaskSuspendActualC.suspend_actual_request) mask original_state
    saved caller call.(TaskSuspendActualC.suspend_actual_entry) call.(TaskSuspendActualC.suspend_actual_current_pointer)
    call.(TaskSuspendActualC.suspend_actual_current_priority) call.(TaskSuspendActualC.suspend_actual_read_residual) ->
  (task_suspend_masked environment critical saved_local sg caller saved
    call.(TaskSuspendActualC.suspend_actual_entry) call.(TaskSuspendActualC.suspend_actual_entry) ** frame) before ->
  (coq_prop (task_suspend_step sg call.(TaskSuspendActualC.suspend_actual_request)
    call.(TaskSuspendActualC.suspend_actual_current_priority) call.(TaskSuspendActualC.suspend_actual_entry)
    call.(TaskSuspendActualC.suspend_actual_result) call.(TaskSuspendActualC.suspend_actual_self)
    call.(TaskSuspendActualC.suspend_actual_checkpoint)) &&
    (task_suspend_masked environment critical saved_local sg caller saved
      call.(TaskSuspendActualC.suspend_actual_entry) call.(TaskSuspendActualC.suspend_actual_checkpoint) ** frame)) after ->
  exists (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    call.(TaskSuspendActualC.suspend_actual_entry) before
    (task_suspend_masked environment critical saved_local sg caller saved
      call.(TaskSuspendActualC.suspend_actual_entry) call.(TaskSuspendActualC.suspend_actual_entry) ** frame) false
    call.(TaskSuspendActualC.suspend_actual_checkpoint) after
    (task_suspend_masked environment critical saved_local sg caller saved
      call.(TaskSuspendActualC.suspend_actual_entry) call.(TaskSuspendActualC.suspend_actual_checkpoint) ** frame)),
    SelectedCSource.kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
      _ _ _ _ _ _ _ run /\
    tmr_task_selected_sequence_idle_receipt environment critical sg observer origin _ _ _ _ _ _ _ run /\
    SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer
      call.(TaskSuspendActualC.suspend_actual_entry) call.(TaskSuspendActualC.suspend_actual_checkpoint) after.
Proof.
  intros environment critical saved_local sg original mask original_state caller saved call frame before after
    observer origin event_observer Hfacts Hinput Houtput.
  destruct (SelectedSuspendComposition.task_suspend_acquired_c_post_selected_sequence environment critical saved_local sg
    original mask original_state caller saved call frame before after observer origin event_observer Hfacts Hinput Houtput)
    as [run [Hsource Hidle]].
  exists run; split; [exact Hsource|]. split.
  - eapply tmr_task_existing_selected_sequence_idle_receipt; exact Hidle.
  - eapply SchedulerPhaseCandidate.os_sched_task_c_sequence_prefix; exact Hsource.
Qed.

(** These factories retain evidence from the real input and post cuts.
    Prepared never becomes a quiescent invariant. The old unrestricted
    Status and Environment source domains are not changed. *)
Lemma tmr_task_delete_phase_valid_task_range : forall phase sg state,
  task_delete_phase_valid phase sg state -> task_in_range sg state.(TskState).
Proof.
  intros phase sg state Hvalid; destruct phase; cbn in Hvalid.
  - exact (proj1 (proj2 Hvalid)).
  - exact (proj1 (proj2 (proj1 Hvalid))).
  - exact (proj1 (proj2 Hvalid)).
Qed.

Lemma tmr_task_delete_phase_ready_slot : forall phase sg state slot node,
  task_delete_phase_valid phase sg state ->
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  In slot state.(SchedState).(readyList) ->
  is_effectively_ready node.(stat) node.(dly) = true.
Proof.
  intros phase sg state slot node Hvalid Hnode Hin.
  destruct phase as [|requested|deleting generation]; cbn in Hvalid.
  - pose proof (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid))))) as Hsound.
    destruct (Hsound slot Hin) as [current [Hcurrent [Hpriority Hready]]].
    assert (current = node) by congruence; subst current; exact Hready.
  - destruct Hvalid as [Hvalid Hdomain].
    pose proof (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid))))) as Hsound.
    destruct (Hsound slot Hin) as [current [Hcurrent [Hpriority Hready]]].
    assert (current = node) by congruence; subst current; exact Hready.
  - pose proof (proj1 (proj1 (proj2 (proj2 Hvalid)))) as Hprepared.
    destruct Hprepared as [[Hstructure Hmembership] Hretiring].
    exact (proj1 (proj1 (Hmembership slot node Hnode) Hin)).
Qed.

Lemma tmr_task_delete_running_protocol_idle : forall phase sg call state,
  task_delete_phase_valid phase sg state ->
  state.(SchedState).(isRunning) = true ->
  task_delete_running_protocol sg call state -> task_idle_ready sg state.(TskState).
Proof.
  intros phase sg call state Hvalid Hrunning Hprotocol.
  destruct (Hprotocol Hrunning) as [[idle [node [Hnode [Hpriority Hin]]]] Hcaller].
  exists idle, node; split; [exact Hnode|]. split; [exact Hpriority|].
  eapply tmr_task_delete_phase_ready_slot; eassumption.
Qed.

Lemma tmr_task_closed_delete_owner_phase_valid : forall environment local phase loan sg call mask state heap frame,
  (task_delete_call_closed environment local phase loan sg call mask state ** frame) heap ->
  task_delete_phase_valid phase sg state.
Proof.
  intros environment local phase loan sg call mask state heap frame Howner.
  assert (Hopen : task_delete_call_closed environment local phase loan sg call mask state ** frame |--
    coq_prop (task_delete_phase_valid phase sg state)).
  { unfold task_delete_call_closed, kernel_continuation_call_closed,
      kernel_continuation_inv, task_delete_phase_resources; entailer!. }
  exact (Hopen heap Howner).
Qed.

Lemma tmr_task_masked_delete_owner_phase_valid :
  forall environment critical local phase loan sg call saved acquired state heap frame,
  (task_delete_call_masked environment critical local phase loan sg call saved acquired state ** frame) heap ->
  task_delete_phase_valid phase sg state.
Proof.
  intros environment critical local phase loan sg call saved acquired state heap frame Howner.
  assert (Hopen : task_delete_call_masked environment critical local phase loan
      sg call saved acquired state ** frame |-- coq_prop (task_delete_phase_valid phase sg state)).
  { unfold task_delete_call_masked, kernel_continuation_call_masked,
      kernel_continuation_inv, task_delete_phase_resources; entailer!. }
  exact (Hopen heap Howner).
Qed.

(** The actual final active observation names the same invocation and
    generation. A reused slot alone cannot discharge this transport. *)
Lemma tmr_task_phase_same_table_active_non_idle : forall sg observed before after,
  task_in_range sg before.(TskState) -> task_in_range sg after.(TskState) ->
  after.(TskState).(prioTbl) = before.(TskState).(prioTbl) ->
  task_idle_ready sg before.(TskState) -> flag_pend_non_idle_at sg observed before ->
  task_invocation_active after.(TskState) observed.(os_sched_call_invocation)
    (RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot) observed.(os_sched_call_stack).(stackLeaseGeneration)) ->
  flag_pend_non_idle_at sg observed after.
Proof.
  intros sg observed before after Hbefore Hafter Htable Hidle Hnonidle Hactive.
  destruct Hbefore as [_ [_ [_ [_ [_ [Hregistered_before Hrest_before]]]]]].
  destruct Hafter as [_ [_ [_ [_ [_ [Hregistered_after Hrest_after]]]]]].
  destruct Hidle as [idle [idle_node [Hidle_node [Hidle_priority Hidle_ready]]]].
  destruct Hnonidle as [old [Hold [Hgeneration Hpriority]]].
  assert (Hdifferent : observed.(os_sched_call_stack).(stackLeaseSlot) <> idle).
  { intro Heq; rewrite Heq in Hold.
    assert (old = idle_node) by congruence; subst old; contradiction. }
  destruct Hactive as [Hregistered [Hretired [node [Hnode Hnode_generation]]]].
  exists node; split; [exact Hnode|]. split; [exact Hnode_generation|].
  intro Hidle_after.
  pose proof (Hregistered_before idle idle_node Hidle_node) as Hidle_table.
  rewrite Hidle_priority in Hidle_table.
  pose proof (Hregistered_after _ _ Hnode) as Hreturned_table.
  rewrite Hidle_after, Htable, Hidle_table in Hreturned_table.
  injection Hreturned_table as Hslots; apply Hdifferent; symmetry; exact Hslots.
Qed.

(** Literal prepare/wake/recycle execution, including the same output
    heap. No registered-client classification is used for this edge. *)
Lemma tmr_task_mutex_delete_heap_return_idle_non_idle :
  forall (environment : TaskStackCallEnvironment) sg observed eid entry prepared event mutex before_heap after_heap frame,
  mutex_del_parent_layout sg -> event_object_layout_prop sg eid ->
  mutex_del_parent_entry sg eid entry event mutex ->
  (kernel_program_inv sg entry ** frame) before_heap ->
  sched_task_mutex_del_always_execution sg eid entry prepared before_heap after_heap ->
  entry.(SchedState).(isRunning) = true ->
  (task_idle_ready sg entry.(TskState) ->
    task_idle_ready sg (mutex_del_always_checkpoint sg eid event prepared).(TskState)) /\
  (flag_pend_non_idle_at sg observed entry ->
    flag_pend_non_idle_at sg observed (mutex_del_always_checkpoint sg eid event prepared)).
Proof.
  intros environment sg observed eid entry prepared event mutex before_heap after_heap frame
    Hlayout Hobject Hentry Hbefore Hactual Hrunning.
  destruct (sched_task_mutex_del_always_source_resources environment.(task_stack_call_external)
    sg eid entry prepared event mutex before_heap after_heap frame Hlayout Hobject Hentry Hbefore Hactual)
    as [Hphase [Hcritical Hafter]].
  destruct Hbefore as [owned [rest [Hjoin [[Hvalid Hrep] Hframe]]]].
  destruct Hafter as [owned_after [rest_after [Hjoin_after [[Hvalid_after Hrep_after] Hframe_after]]]].
  eapply tmr_task_mutex_delete_preserves_idle_non_idle; eassumption.
Qed.

Lemma tmr_task_delete_window_entry_task_range : forall environment critical sg before before_heap after after_heap,
  sched_task_delete_window_execution environment critical sg before before_heap after after_heap ->
  task_in_range sg before.(TskState).
Proof.
  intros environment critical sg before before_heap after after_heap Hactual.
  destruct Hactual as [local requested completed arch restore save original initial first acquired
    priority tid node prepared loan saved cursor initial_heap written prefix_heap middle between
    restore_environment_heap final_cursor middle_heap registers returned resumed save_environment_heap
    final_registers reacquired final_heap frame Henv Hprep Hr0 Hmask Howner Hprefix Hrestore
    Hrestore_suffix Hsave Hreturn Hvalid Hsaved_mask Hsave_suffix].
  eapply tmr_task_delete_phase_valid_task_range.
  eapply tmr_task_masked_delete_owner_phase_valid; exact Howner.
Qed.

(** The original raw client branch is used unchanged, including its
    observer and foreign-action condition. Registration supplies the
    actual per-client preservation proof; it is not a new source domain. *)
Lemma tmr_task_registered_clients_idle_prefix :
  forall environment critical sg observer entry current final_heap,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  UCOS2_state_inv sg entry -> entry.(SchedState).(isRunning) = true ->
  kernel_client_trace critical.(critical_region_clients) sg observer entry false current ->
  exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer entry current final_heap,
    forall observed,
      task_idle_ready sg entry.(TskState) -> flag_pend_non_idle_at sg observed entry ->
      task_idle_ready sg current.(TskState) /\ flag_pend_non_idle_at sg observed current.
Proof.
  intros environment critical sg observer entry current final_heap Hcoverage Hvalid Hrunning Htrace.
  exists (SchedulerPhaseCandidate.OsSchedTaskReturnPrefixClients environment critical sg observer entry current final_heap Htrace).
  intros observed Hidle Hnonidle.
  pose proof (proj1 (kernel_client_resource_trace_transports_invariant
    (os_sched_fields_running_idle_non_idle_inv observed) critical.(critical_region_clients)
    sg observer None entry false current
    (fun action Hin => tmr_task_registered_source_idle_non_idle_clients
      environment.(task_stack_call_external) critical observed action Hcoverage Hin) Htrace
    (conj Hvalid (conj Hrunning (conj Hidle Hnonidle))))) as Hafter.
  exact (proj2 (proj2 Hafter)).
Qed.

Local Lemma tmr_task_closed_environment_idle_prefix :
  forall environment critical local requested sg observer completed phase loan deleting entry deleted current
    mask before_heap after_heap frame,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  sched_task_delete_environment_execution environment critical local requested sg completed phase loan
    deleting entry deleted current mask before_heap after_heap frame ->
  UCOS2_state_inv sg entry -> entry.(SchedState).(isRunning) = true ->
  exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer entry current after_heap,
    forall observed,
      task_idle_ready sg entry.(TskState) -> flag_pend_non_idle_at sg observed entry ->
      task_idle_ready sg current.(TskState) /\ flag_pend_non_idle_at sg observed current.
Proof.
  intros environment critical local requested sg observer completed phase loan deleting entry deleted current
    mask before_heap after_heap frame Hcoverage Hactual Hvalid Hrunning.
  destruct (sched_task_delete_environment_source_resources environment critical local requested sg completed phase loan
    deleting entry deleted current mask before_heap after_heap frame Hactual) as [Hsource Hrest].
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Hsource) as [Htrace Hcontrol].
  apply kernel_resumption_resource_trace_erases in Htrace.
  pose (step := @SchedTaskPhaseHeapDeleteEnvironment environment critical sg local requested completed phase loan
    deleting entry deleted current mask before_heap after_heap frame Hactual).
  pose (source := @SchedTaskPhaseHeapSourceNext environment critical sg entry before_heap current after_heap current after_heap
    step (@SchedTaskPhaseHeapSourceRefl environment critical sg current after_heap)).
  exists (SchedulerPhaseCandidate.OsSchedTaskReturnPrefixPhases environment critical sg observer entry before_heap current after_heap source).
  intros observed Hidle Hnonidle.
  pose proof (proj1 (kernel_client_resource_trace_transports_invariant
    (os_sched_fields_running_idle_non_idle_inv observed) critical.(critical_region_clients)
    sg deleting.(os_sched_call_invocation) None entry false current
    (fun action Hin => tmr_task_registered_source_idle_non_idle_clients
      environment.(task_stack_call_external) critical observed action Hcoverage Hin) Htrace
    (conj Hvalid (conj Hrunning (conj Hidle Hnonidle))))) as Hafter.
  exact (proj2 (proj2 Hafter)).
Qed.

Lemma tmr_task_stable_environment_idle_prefix :
  forall environment critical local requested sg observer completed loan deleting entry deleted current
    mask before_heap after_heap frame,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  sched_task_delete_environment_execution environment critical local requested sg completed TaskDeleteStable loan
    deleting entry deleted current mask before_heap after_heap frame ->
  entry.(SchedState).(isRunning) = true ->
  exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer entry current after_heap,
    forall observed,
      task_idle_ready sg entry.(TskState) -> flag_pend_non_idle_at sg observed entry ->
      task_idle_ready sg current.(TskState) /\ flag_pend_non_idle_at sg observed current.
Proof.
  intros environment critical local requested sg observer completed loan deleting entry deleted current
    mask before_heap after_heap frame Hcoverage Hactual Hrunning.
  eapply tmr_task_closed_environment_idle_prefix; [exact Hcoverage|exact Hactual| |exact Hrunning].
  exact (tmr_task_closed_delete_owner_phase_valid environment local TaskDeleteStable loan sg deleting mask entry
    before_heap frame (proj2 (proj2 Hactual))).
Qed.

Lemma tmr_task_lookup_environment_idle_prefix :
  forall environment critical local requested sg observer completed selected loan deleting entry deleted current
    mask before_heap after_heap frame,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  sched_task_delete_environment_execution environment critical local requested sg completed (TaskDeleteLookup selected) loan
    deleting entry deleted current mask before_heap after_heap frame ->
  entry.(SchedState).(isRunning) = true ->
  exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer entry current after_heap,
    forall observed,
      task_idle_ready sg entry.(TskState) -> flag_pend_non_idle_at sg observed entry ->
      task_idle_ready sg current.(TskState) /\ flag_pend_non_idle_at sg observed current.
Proof.
  intros environment critical local requested sg observer completed selected loan deleting entry deleted current
    mask before_heap after_heap frame Hcoverage Hactual Hrunning.
  eapply tmr_task_closed_environment_idle_prefix; [exact Hcoverage|exact Hactual| |exact Hrunning].
  exact (proj1 (tmr_task_closed_delete_owner_phase_valid environment local (TaskDeleteLookup selected) loan
    sg deleting mask entry before_heap frame (proj2 (proj2 Hactual)))).
Qed.

Lemma tmr_task_mutex_delete_actual_idle_prefix :
  forall environment critical sg observer eid entry prepared event mutex before_heap after_heap frame,
  mutex_del_parent_layout sg -> event_object_layout_prop sg eid ->
  mutex_del_parent_entry sg eid entry event mutex ->
  (kernel_program_inv sg entry ** frame) before_heap ->
  sched_task_mutex_del_always_execution sg eid entry prepared before_heap after_heap ->
  entry.(SchedState).(isRunning) = true ->
  exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer
    entry (mutex_del_always_checkpoint sg eid event prepared) after_heap,
    forall observed,
      (task_idle_ready sg entry.(TskState) ->
        task_idle_ready sg (mutex_del_always_checkpoint sg eid event prepared).(TskState)) /\
      (flag_pend_non_idle_at sg observed entry ->
        flag_pend_non_idle_at sg observed (mutex_del_always_checkpoint sg eid event prepared)).
Proof.
  intros environment critical sg observer eid entry prepared event mutex before_heap after_heap frame
    Hlayout Hobject Hentry Howner Hactual Hrunning.
  pose (step := @SchedTaskPhaseHeapMutexDeleteAlways environment critical sg eid entry prepared event mutex
    before_heap after_heap frame Hlayout Hobject Hentry Howner Hactual).
  pose (source := @SchedTaskPhaseHeapSourceNext environment critical sg entry before_heap
    (mutex_del_always_checkpoint sg eid event prepared) after_heap
    (mutex_del_always_checkpoint sg eid event prepared) after_heap step
    (@SchedTaskPhaseHeapSourceRefl environment critical sg (mutex_del_always_checkpoint sg eid event prepared) after_heap)).
  exists (SchedulerPhaseCandidate.OsSchedTaskReturnPrefixPhases environment critical sg observer
    entry before_heap _ after_heap source).
  intro observed; eapply tmr_task_mutex_delete_heap_return_idle_non_idle; eassumption.
Qed.

(** The Prepared input protocol comes from the real preparation history.
    No desired return Idle property and no quiescent Prepared invariant is
    added. The same completed environment and two heaps form the old edge. *)
Lemma tmr_task_preparation_environment_idle_prefix :
  forall environment critical local requested sg observer completed original initial deleting acquired
    priority tid node prepared loan deleted current mask before_heap after_heap frame,
  task_delete_preparation_history sg requested original initial deleting acquired priority tid node prepared loan ->
  sched_task_delete_environment_execution environment critical local requested sg completed
    (TaskDeletePrepared tid node.(taskGeneration)) loan deleting (task_delete_locked prepared)
    deleted current mask before_heap after_heap frame ->
  (task_delete_locked prepared).(SchedState).(isRunning) = true ->
  exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer
    (task_delete_locked prepared) current after_heap,
    task_idle_ready sg current.(TskState) /\
    (forall observed,
      task_idle_ready sg (task_delete_locked prepared).(TskState) ->
      flag_pend_non_idle_at sg observed (task_delete_locked prepared) ->
      task_invocation_active current.(TskState) observed.(os_sched_call_invocation)
        (RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot) observed.(os_sched_call_stack).(stackLeaseGeneration)) ->
      flag_pend_non_idle_at sg observed current).
Proof.
  intros environment critical local requested sg observer completed original initial deleting acquired
    priority tid node prepared loan deleted current mask before_heap after_heap frame Hpreparation Hactual Hrunning.
  pose proof (proj2 (proj2 Hpreparation)) as Hprotocol.
  destruct (sched_task_delete_environment_source_resources environment critical local requested sg completed
    (TaskDeletePrepared tid node.(taskGeneration)) loan deleting (task_delete_locked prepared)
    deleted current mask before_heap after_heap frame Hactual) as [Htrace [Hsame [Hrely [Htransport Howner]]]].
  destruct Hrely as [Hints [Hrunning_eq [Hvalid [Htable Hselected]]]].
  pose (step := @SchedTaskPhaseHeapDeleteEnvironment environment critical sg local requested completed
    (TaskDeletePrepared tid node.(taskGeneration)) loan deleting (task_delete_locked prepared)
    deleted current mask before_heap after_heap frame Hactual).
  pose (source := @SchedTaskPhaseHeapSourceNext environment critical sg (task_delete_locked prepared) before_heap
    current after_heap current after_heap step (@SchedTaskPhaseHeapSourceRefl environment critical sg current after_heap)).
  exists (SchedulerPhaseCandidate.OsSchedTaskReturnPrefixPhases environment critical sg observer
    (task_delete_locked prepared) before_heap current after_heap source).
  split.
  - eapply tmr_task_delete_running_protocol_idle; [exact Hvalid| |exact (proj1 Htransport Hprotocol)].
    rewrite Hrunning_eq; exact Hrunning.
  - intros observed Hidle Hnonidle Hactive.
    eapply tmr_task_phase_same_table_active_non_idle; [| |exact Htable|exact Hidle|exact Hnonidle|exact Hactive].
    + eapply tmr_task_delete_phase_valid_task_range, tmr_task_closed_delete_owner_phase_valid.
      exact (proj2 (proj2 Hactual)).
    + eapply tmr_task_delete_phase_valid_task_range; exact Hvalid.
Qed.

(** The actual public prepared body retains the protocol before Restore.
    The same existential values, masked owner, frame and heap are kept. *)
Lemma tmr_task_prepared_body_protocol : forall environment critical local sg requested original initial
  deleting saved acquired priority pointer tid node added frame,
  task_delete_prepared_body environment critical local sg requested original initial
    deleting saved acquired priority pointer tid node added ** frame |--
  EX prepared loan,
    coq_prop (task_delete_live_history sg requested original initial deleting acquired priority pointer tid node /\
      task_delete_prepare_single_wait acquired tid node = Some (prepared, loan) /\
      added = (if task_delete_lock_added prepared.(IntrState) then 1 else 0) /\
      task_delete_running_protocol sg deleting (task_delete_locked prepared)) &&
    (task_delete_call_masked environment critical local (TaskDeletePrepared tid node.(taskGeneration)) loan
      sg deleting saved acquired (task_delete_locked prepared) ** frame).
Proof.
  intros until frame; intros heap [owned [rest [Hjoin [Hbody Hframe]]]].
  destruct Hbody as [prepared [loan [Hfacts Hmasked]]].
  exists prepared, loan; split; [exact Hfacts|].
  exists owned, rest; exact (conj Hjoin (conj Hmasked Hframe)).
Qed.

Lemma tmr_task_delete_window_actual_idle_prefix :
  forall environment critical sg observer entry before current after,
  sched_task_delete_window_execution environment critical sg entry before current after ->
  entry.(SchedState).(isRunning) = true ->
  exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer entry current after,
    task_idle_ready sg current.(TskState) /\
    (forall observed,
      task_idle_ready sg entry.(TskState) -> flag_pend_non_idle_at sg observed entry ->
      task_invocation_active current.(TskState) observed.(os_sched_call_invocation)
        (RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot) observed.(os_sched_call_stack).(stackLeaseGeneration)) ->
      flag_pend_non_idle_at sg observed current).
Proof.
  intros environment critical sg observer entry before current after Hactual Hrunning.
  destruct (sched_task_delete_window_source_resources environment critical sg entry before current after Hactual)
    as (local & requested & deleting & initial & first & acquired & priority & tid & node & prepared & loan &
        deleted & saved & frame & Hentry & Hwindow & Hresources).
  destruct Hwindow as [Hpreparation [Hsame [Hrely Hprotocol]]].
  rewrite <- Hentry in Hrely.
  destruct Hrely as [Hints [Hrunning_eq [Hvalid [Htable Hselected]]]].
  pose (step := @SchedTaskPhaseHeapDeleteWindow environment critical sg entry before current after Hactual).
  pose (source := @SchedTaskPhaseHeapSourceNext environment critical sg entry before current after current after step
    (@SchedTaskPhaseHeapSourceRefl environment critical sg current after)).
  exists (SchedulerPhaseCandidate.OsSchedTaskReturnPrefixPhases environment critical sg observer entry before current after source).
  split.
  - eapply tmr_task_delete_running_protocol_idle; [exact Hvalid| |exact Hprotocol].
    rewrite Hrunning_eq; exact Hrunning.
  - intros observed Hidle Hnonidle Hactive.
    eapply tmr_task_phase_same_table_active_non_idle;
      [eapply tmr_task_delete_window_entry_task_range; exact Hactual|
       eapply tmr_task_delete_phase_valid_task_range; exact Hvalid|exact Htable|exact Hidle|exact Hnonidle|exact Hactive].
Qed.

(** Local composition of already produced packets. The exact intermediate
    heap, bridge entailment and original run tree remain in the result. *)
Lemma tmr_task_selected_idle_sequences_compose :
  forall environment critical sg observer origin event_observer entry before input first_stop middle middle_heap
    first_output next_input last_stop current after output
    (first : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      entry before input first_stop middle middle_heap first_output)
    (bridge : first_output |-- next_input)
    (last : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      middle middle_heap next_input last_stop current after output),
  SelectedCSource.kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ first ->
  tmr_task_selected_sequence_idle_receipt environment critical sg observer origin _ _ _ _ _ _ _ first ->
  SelectedCSource.kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ last ->
  tmr_task_selected_sequence_idle_receipt environment critical sg observer origin _ _ _ _ _ _ _ last ->
  let run := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ first bridge last in
  SelectedCSource.kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ run /\
  tmr_task_selected_sequence_idle_receipt environment critical sg observer origin _ _ _ _ _ _ _ run.
Proof. intros; split; constructor; assumption. Qed.

Lemma tmr_task_selected_idle_sequence_adapt :
  forall environment critical sg observer origin event_observer entry before input inner_input stopped current after inner_output output
    (owned : input before) (open_input : input |-- inner_input)
    (inner : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      entry before inner_input stopped current after inner_output)
    (close_output : inner_output |-- output),
  SelectedCSource.kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ inner ->
  tmr_task_selected_sequence_idle_receipt environment critical sg observer origin _ _ _ _ _ _ _ inner ->
  let run := KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ owned open_input inner close_output in
  SelectedCSource.kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ run /\
  tmr_task_selected_sequence_idle_receipt environment critical sg observer origin _ _ _ _ _ _ _ run.
Proof. intros; split; constructor; assumption. Qed.

(** This is the actual Task completion producer's Hclose cut. Its prefix
    is produced from the concrete protected Status post above; it is not a
    new assumption that every old prefix has an Idle receipt. The selected
    descriptor, restored heap and continuation owner are unpacked once. *)
Lemma tmr_task_protected_status_task_completion_idle_post :
  forall environment critical
    (task_abi : Armv7aTaskContextABI (task_sw_hook_call_environment environment).(task_stack_call_external)
      (task_sw_hook_call_environment environment).(task_stack_call_platform)
      (task_sw_hook_call_environment environment).(task_stack_call_port)
      (task_sw_hook_call_environment environment).(task_stack_call_continuations))
    sg entry first_installed initial_local active initial_heap last_entry context saved_sp outgoing hooked resumed
    original saved acquired receipt other frame prefix_heap prefix_frame before_heap installed sp actual,
  let configured := task_sw_hook_call_environment environment in
  let call := {| InstallComponent.task_install_fields_context := context;
                 InstallComponent.task_install_fields_outgoing := outgoing;
                 InstallComponent.task_install_fields_incoming := original.(os_sched_call_stack);
                 InstallComponent.task_install_fields_resumed := resumed;
                 InstallComponent.task_install_fields_entry := hooked |} in
  let local := kernel_sched_saved_local_resource_at configured.(task_stack_call_platform) critical sg
    hooked.(TskState) original saved acquired receipt other in
  let rest := armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame in
  forall (segment : StatusComponent.kernel_status_c_segment sg first_installed prefix_heap hooked before_heap prefix_frame)
    request priority error scheduled legacy_result
    (legacy : task_suspend_critical sg request first_installed legacy_result hooked)
    (complete : InstallComponent.task_install_c_segment configured local sg rest call before_heap installed sp actual),
  os_sched_task_switch_pre configured critical initial_local active sg original saved acquired entry initial_heap ->
  os_sched_switch_source configured.(task_stack_call_external) sg entry original first_installed ->
  os_sched_requests_switch last_entry = true ->
  configured.(task_stack_call_external).(os_sched_arch_save_source) context saved_sp outgoing ->
  kernel_client_step configured.(task_stack_call_external).(os_sched_hook_action) sg
    (os_sched_save_current_sp (os_sched_prefix_state last_entry) context.(os_sched_call_stack).(stackLeaseSlot) saved_sp) hooked ->
  os_sched_destination_binding configured.(task_stack_call_external)
    context outgoing hooked original.(os_sched_call_stack) resumed ->
  StatusComponent.kernel_status_c_segment_code _ _ _ _ _ _ segment =
    StatusComponent.KernelStatusCSuspendSource sg first_installed request legacy_result hooked legacy ->
  task_suspend_protected sg request priority first_installed (error, scheduled) hooked ->
  UCOS2_inv sg hooked ** prefix_frame |-- InstallComponent.task_install_fields_entry_owner configured local sg call ** rest ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (forall returned, task_tcb_init_stack_same_call returned original ->
    kernel_call_task_source returned (InstallComponent.task_install_fields_current call) ->
    os_sched_task_current_ready returned (InstallComponent.task_install_fields_current call) ->
    receipt ** frame |-- active returned (InstallComponent.task_install_fields_current call)) ->
  task_idle_ready sg entry.(TskState) -> flag_pend_non_idle_at sg original entry ->
  exists selected, forall restored,
    armv7a_task_restore_transition task_abi context selected installed restored ->
    let current := InstallComponent.task_install_fields_current call in
    let returned := kernel_selected_call selected current in
    tmr_task_actual_body_idle_post configured critical active sg original saved acquired entry restored /\
    (forall X, safeExec (fun state => state = entry) (os_sched_task_body_program configured critical sg original) X ->
      safeExec (fun state => state = current) (StateRelMonad.ret returned) X).
Proof.
  intros environment critical task_abi sg entry first_installed initial_local active initial_heap last_entry context saved_sp
    outgoing hooked resumed original saved acquired receipt other frame prefix_heap prefix_frame before_heap installed sp actual
    configured call local rest segment request priority error scheduled legacy_result legacy complete
    Hinitial Hfirst Hswitch Hsave Hhook Hdestination Hcode Hprotected Hbridge Hcoverage Hreceipt Hidle Hnonidle.
  destruct (tmr_task_protected_status_selected_sequence configured critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None first_installed prefix_heap hooked before_heap prefix_frame segment
    request priority error scheduled legacy_result legacy Hcode Hprotected) as [prefix [Hprefix [Hsem Hprefix_idle]]].
  destruct (SelectedCompletionComposition.task_selected_completion_environment_sequence configured critical task_abi sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None frame call original saved acquired receipt other
    before_heap installed sp actual complete eq_refl Hcoverage) as [selected Hterminal].
  exists selected; intros restored Hrestore current returned.
  destruct (Hterminal restored Hrestore) as [last [Hlast [Htask Hsame]]].
  change (kernel_call_task_source returned current) in Htask.
  change (task_tcb_init_stack_same_call returned original) in Hsame.
  destruct (kernel_program_selected_c_sequence_resources configured critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ last)
    as [Hlast_input [Hendpoint Howned]].
  pose proof (proj1 (flag_pend_caller_restore_input_state_inv configured critical other
    (fun _ _ => receipt ** frame) sg (FlagPendTaskCaller returned) returned saved acquired current restored Howned)) as Hvalid.
  pose proof complete as [Hstate Hcompletion].
  destruct Hstate as [Hsaved [Hdestination' [Hhigh Hcurrent]]].
  assert (Hready : os_sched_task_current_ready returned current).
  { eapply SchedulerReturnFacts.os_sched_install_current_ready; try eassumption.
    exact (proj2 (proj2 Hsame)). }
  pose (history := @SchedulerPhaseCandidate.OsSchedTaskReturnPrefixCSequence configured critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix Hprefix).
  pose (Hbody := @SchedulerPhaseCandidate.OsSchedTaskBodyTaskLastInstall configured critical sg entry original first_installed
    context outgoing hooked resumed returned before_heap Hfirst history eq_refl Hsaved Hdestination Hhigh Hsame).
  assert (Hbody_receipt : sem_pend_sched_body_receipt configured critical sg entry original returned current Hbody).
  { unfold Hbody; constructor; unfold history; constructor; exact Hsem. }
  assert (Hnormal : kernel_call_normal_return original entry returned current).
  { split; [exact Hsame|]. intro Havailable.
    unfold kernel_call_stack_available; rewrite (proj1 Htask).
    unfold current, InstallComponent.task_install_fields_current, call.
    change (task_stack_take
      (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks) context.(os_sched_call_stack) outgoing)
      original.(os_sched_call_stack) (task_stack_key returned.(os_sched_call_stack)) = None).
    rewrite (proj2 (proj2 Hsame)); apply task_stack_take_lookup. }
  assert (Hcontrol : kernel_call_control_rely sg entry current).
  { unfold current, call.
    eapply SelectedControlComposition.task_last_call_selected_sequence_control with
      (first_installed := first_installed) (last_entry := last_entry) (saved_sp := saved_sp)
      (observer := original.(os_sched_call_invocation)) (origin := original.(os_sched_call_origin)); eassumption. }
  assert (Hobservations : os_sched_task_body_observation configured critical sg original entry returned current).
  { exact (conj Hbody (conj Hready (conj Hnormal (conj Hcontrol (fun _ => Htask))))). }
  assert (Hbinding : task_sw_hook_source_binding configured.(task_stack_call_external)).
  { apply task_sw_hook_external_source_binding. }
  destruct (tmr_task_bound_switch_idle_non_idle _ _ _ _ _ original Hbinding Hfirst) as [Hfirst_idle Hfirst_nonidle].
  destruct (tmr_task_status_segment_protected_idle_non_idle sg original first_installed prefix_heap hooked before_heap prefix_frame
    segment request priority error scheduled Hprotected) as [Hcut_idle Hcut_nonidle].
  assert (Hidle_current : task_idle_ready sg current.(TskState)).
  { apply Hcut_idle, Hfirst_idle; exact Hidle. }
  assert (Hnonidle_current : flag_pend_non_idle_at sg returned current).
  { unfold flag_pend_non_idle_at; rewrite (proj2 (proj2 Hsame)).
    exact (Hcut_nonidle (Hfirst_nonidle Hnonidle)). }
  split.
  - exists returned, current, other; split.
    + exists Hbody; exact (conj Hbody_receipt (conj Hobservations (conj Hidle_current Hnonidle_current))).
    + pose proof (proj1 (flag_pend_task_restore_input_masked_equiv configured critical other
      (fun _ _ => receipt ** frame) sg returned saved acquired current) restored Howned) as Hmasked.
    match type of Hmasked with ?P restored => match goal with |- ?Q restored => assert (Hclose : P |-- Q) end end.
    { sep_apply_l_atomic (Hreceipt returned Hsame Htask Hready); entailer!. }
    exact (Hclose restored Hmasked).
  - intros X Hsafe; eapply SchedulerPhaseCandidate.os_sched_task_body_return_safeexec; eassumption.
Qed.

Lemma tmr_task_protected_status_irq_completion_idle_post :
  forall environment critical sg entry first_installed initial_local active initial_heap handler irq_entry transfer
    original saved acquired receipt other frame prefix_heap prefix_frame before_heap
    prepared hooked_heap installed selected after source prefix hook install restore,
  let configured := task_sw_hook_call_environment environment in
  forall (segment : StatusComponent.kernel_status_c_segment sg first_installed prefix_heap irq_entry before_heap prefix_frame)
    request priority error scheduled legacy_result
    (legacy : task_suspend_critical sg request first_installed legacy_result irq_entry),
  IRQAcquiredReturn.kernel_irq_acquired_c_completion environment critical sg handler irq_entry transfer original saved acquired
    receipt other frame before_heap prepared hooked_heap installed selected after source prefix hook install restore ->
  os_sched_task_switch_pre configured critical initial_local active sg original saved acquired entry initial_heap ->
  os_sched_switch_source configured.(task_stack_call_external) sg entry original first_installed ->
  StatusComponent.kernel_status_c_segment_code _ _ _ _ _ _ segment =
    StatusComponent.KernelStatusCSuspendSource sg first_installed request legacy_result irq_entry legacy ->
  task_suspend_protected sg request priority first_installed (error, scheduled) irq_entry ->
  UCOS2_inv sg irq_entry ** prefix_frame |-- IRQCPrefix.os_int_exit_prefix_fields_owner configured critical sg handler irq_entry
    original saved acquired receipt other frame ->
  (forall returned, task_tcb_init_stack_same_call returned original ->
    kernel_call_task_source returned (os_int_exit_installed_state transfer) ->
    os_sched_task_current_ready returned (os_int_exit_installed_state transfer) ->
    IRQSelectedCompletion.irq_selected_suffix_receipt handler receipt frame |--
      active returned (os_int_exit_installed_state transfer)) ->
  task_idle_ready sg entry.(TskState) -> flag_pend_non_idle_at sg original entry ->
  let current := os_int_exit_installed_state transfer in
  let returned := kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack) transfer.(os_int_exit_incoming_fragments) in
  tmr_task_actual_body_idle_post configured critical active sg original saved acquired entry after /\
  (forall X, safeExec (fun state => state = entry) (os_sched_task_body_program configured critical sg original) X ->
    safeExec (fun state => state = current) (StateRelMonad.ret returned) X).
Proof.
  intros environment critical sg entry first_installed initial_local active initial_heap handler irq_entry transfer original saved
    acquired receipt other frame prefix_heap prefix_frame before_heap prepared hooked_heap installed selected after source prefix hook install
    restore configured segment request priority error scheduled legacy_result legacy complete Hinitial Hfirst Hcode Hprotected
    Hbridge Hreceipt Hidle Hnonidle current returned.
  destruct (tmr_task_protected_status_selected_sequence configured critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None first_installed prefix_heap irq_entry before_heap prefix_frame segment
    request priority error scheduled legacy_result legacy Hcode Hprotected) as [earlier [Hearlier [Hsem Hprefix_idle]]].
  destruct (SelectedCompletionComposition.irq_acquired_completion_environment_sequence environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None handler irq_entry transfer original saved acquired
    receipt other frame before_heap prepared hooked_heap installed selected after source prefix hook install restore complete)
    as [last [Hlast [Htask [Hsame [Hready [Hidle_tail [Hnonidle_tail [Hnormal [Hrunning Henabled]]]]]]]]].
  pose (history := @SchedulerPhaseCandidate.OsSchedTaskReturnPrefixCSequence configured critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None _ _ _ _ _ _ _ earlier Hearlier).
  pose (irq_history := @or_intror
    (kernel_client_trace critical.(critical_region_clients) sg original.(os_sched_call_invocation) first_installed false irq_entry)
    (exists final_heap, SchedulerPhaseCandidate.os_sched_task_return_prefix configured critical sg
      original.(os_sched_call_invocation) first_installed irq_entry final_heap) (ex_intro _ before_heap history)).
  pose (Hbody := @SchedulerPhaseCandidate.OsSchedTaskBodyIRQLastInstall configured critical sg entry original first_installed
    handler irq_entry transfer returned Hfirst irq_history eq_refl source (proj2 (proj2 Hsame)) Hsame).
  assert (Hbody_receipt : sem_pend_sched_body_receipt configured critical sg entry original returned current Hbody).
  { unfold Hbody; constructor; unfold irq_history; constructor; unfold history; constructor; exact Hsem. }
  assert (Hfirst_running : first_installed.(SchedState).(isRunning) = entry.(SchedState).(isRunning)).
  { destruct Hfirst as [Hswitch [old_sp [outgoing [hooked [incoming [resumed [Hsave [Hhook [Hdest Hinstalled]]]]]]]]].
    change (hooked = os_sched_save_current_sp (os_sched_prefix_state entry)
      original.(os_sched_call_stack).(stackLeaseSlot) old_sp) in Hhook.
    rewrite Hinstalled, Hhook; exact (proj2 (proj2 (proj2 (os_sched_ready_checkpoint_frame entry)))). }
  assert (Hentry_enabled : os_sched_selection_enabled entry = true).
  { exact (proj1 (proj1 (os_sched_requests_switch_iff entry) (proj1 Hfirst))). }
  pose proof (SelectedControlComposition.kernel_program_selected_c_sequence_running configured critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ earlier) as Hprefix_running.
  assert (Hcontrol : kernel_call_control_rely sg entry current).
  { apply SelectedEndpointObservations.kernel_call_enabled_control_rely; [exact Hentry_enabled|exact Henabled|].
    change ((os_int_exit_installed_state transfer).(SchedState).(isRunning) = entry.(SchedState).(isRunning)).
    etransitivity; [exact Hrunning|]. etransitivity; [exact Hprefix_running|exact Hfirst_running]. }
  assert (Hobservations : os_sched_task_body_observation configured critical sg original entry returned current).
  { exact (conj Hbody (conj Hready (conj (Hnormal entry) (conj Hcontrol (fun _ => Htask))))). }
  assert (Hbinding : task_sw_hook_source_binding configured.(task_stack_call_external)).
  { apply task_sw_hook_external_source_binding. }
  destruct (tmr_task_bound_switch_idle_non_idle _ _ _ _ _ original Hbinding Hfirst) as [Hfirst_idle Hfirst_nonidle].
  destruct (tmr_task_status_segment_protected_idle_non_idle sg original first_installed prefix_heap irq_entry before_heap prefix_frame
    segment request priority error scheduled Hprotected) as [Hcut_idle Hcut_nonidle].
  assert (Hidle_current : task_idle_ready sg current.(TskState)).
  { apply Hidle_tail, Hcut_idle, Hfirst_idle; exact Hidle. }
  assert (Hnonidle_current : flag_pend_non_idle_at sg returned current).
  { apply Hnonidle_tail, Hcut_nonidle, Hfirst_nonidle; exact Hnonidle. }
  pose proof (proj2 (kernel_program_selected_c_sequence_resources configured critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ last)) as Howned.
  split.
  - exists returned, current, other; split.
    + exists Hbody; exact (conj Hbody_receipt (conj Hobservations (conj Hidle_current Hnonidle_current))).
    + pose proof (proj1 (flag_pend_task_restore_input_masked_equiv configured critical other
      (fun _ _ => IRQSelectedCompletion.irq_selected_suffix_receipt handler receipt frame)
      sg returned saved acquired current) after Howned) as Hmasked.
    match type of Hmasked with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
    { sep_apply_l_atomic (Hreceipt returned Hsame Htask Hready); entailer!. }
    exact (Hclose after Hmasked).
  - intros X Hsafe; eapply SchedulerPhaseCandidate.os_sched_task_body_return_safeexec; eassumption.
Qed.

Lemma tmr_task_actual_body_idle_post_forget : forall environment critical active sg original saved acquired entry,
  tmr_task_actual_body_idle_post environment critical active sg original saved acquired entry |--
  os_sched_task_body_post environment critical active sg original saved acquired entry.
Proof.
  intros environment critical active sg original saved acquired entry heap
    [returned [current [next_local [[body [Hreceipt [Hbody Hidle]]] Howner]]]].
  exists returned, current, next_local; exact (conj Hbody Howner).
Qed.
