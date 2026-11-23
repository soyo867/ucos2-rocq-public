Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.sched Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_api_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_idle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_selected_c_spec.
Require Import Ucos2Verify.lib.task_retirement.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Import CriticalComponent PrimitiveComponent SelectedReturnPrimitive SelectedCProgram.
Import DeleteComponent.
Import SelectedIdleFrames SelectedIdleWakeStatus SelectedIdleBuiltin SelectedMutexIdle.
Import SelectedIdleCritical SelectedDeleteIdle SelectedControlComposition.
Import SelectedIdleComposition.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Idle is independent of the stored observer. Recycle supplies its real
    resumed running protocol; no stopped=false or future Idle is assumed. *)
Lemma tmr_task_delete_c_source_preserves_idle :
  forall environment critical sg observer origin state before input stopped current after output,
  DeleteComponent.task_delete_own_c_segment environment critical sg observer origin
    state before input stopped current after output ->
  state.(SchedState).(isRunning) = true ->
  task_idle_ready sg state.(TskState) -> task_idle_ready sg current.(TskState).
Proof.
  intros environment critical sg observer origin state before input stopped current after output Hstep.
  destruct Hstep as [inputs before_heap prepared_heap Hcontext Hcompletion|
                    capture after_heap Hcontext Hcompletion]; intros Hrunning Hidle.
  - destruct Hcontext as [Henv [Hcritical Hsg]]; subst sg.
    destruct Hcompletion as [[Hlookup [Hprepare Hprotocol]] Hinput Houtput].
    destruct Hlookup as [Htable [Hselected [Hlive Hpointer]]].
    change (task_idle_ready inputs.(delete_capture_globals) inputs.(delete_capture_prepared).(TskState)).
    exact (proj1 (task_delete_prepare_single_wait_idle_non_idle _ inputs.(delete_capture_first)
      _ _ _ _ _ (proj2 (task_delete_table_lookup_live _ _ _ _ Hlive)) Hprepare) Hidle).
  - destruct Hcontext as [Henv [Hcritical Hsg]]; subst sg.
    apply task_delete_capture_recycle_idle; exact Hrunning.
Qed.

(** This is a single real leaf. Its live output lookup excludes deletion of
    the observed slot. Across a sequence that lookup must come from the same
    incarnation's backwards-active transport, not slot reuse. *)
Lemma tmr_task_delete_c_source_preserves_non_idle :
  forall environment critical sg observer origin state before input stopped current after output,
  DeleteComponent.task_delete_own_c_segment environment critical sg observer origin
    state before input stopped current after output ->
  forall observed,
    (exists live, current.(TskState).(inUsedTaskStates)
      observed.(os_sched_call_stack).(stackLeaseSlot) = Some live) ->
    flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed current.
Proof.
  intros environment critical sg observer origin state before input stopped current after output Hstep.
  destruct Hstep as [inputs before_heap prepared_heap Hcontext Hcompletion|
                    capture after_heap Hcontext Hcompletion]; intros observed Hlive Hnonidle.
  - destruct Hcontext as [Henv [Hcritical Hsg]]; subst sg.
    destruct Hcompletion as [[Hlookup [Hprepare Hprotocol]] Hinput Houtput].
    destruct Hlookup as [Htable [Hselected [Hnode Hpointer]]].
    change (flag_pend_non_idle_at inputs.(delete_capture_globals) observed inputs.(delete_capture_prepared)).
    revert Hnonidle; eapply proj2; eapply task_delete_prepare_single_wait_idle_non_idle;
      [exact (proj2 (task_delete_table_lookup_live _ _ _ _ Hnode))|exact Hprepare].
  - destruct Hcontext as [Henv [Hcritical Hsg]]; subst sg.
    destruct Hlive as [live Hlive].
    destruct (task_unlink_used_map_lookup_origin _ _ _ _ _ Hlive) as [Hdifferent Hprevious].
    eapply task_delete_cut_non_idle; [exact Hdifferent|exact Hnonidle].
Qed.

(** All thirteen original C constructors are covered. In particular Status
    does not need the additional Idle guard to preserve a live caller's
    non-Idle priority, and ownDelete is retained with its real lifetime. *)
Lemma tmr_task_program_c_step_preserves_non_idle :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_program_c_step environment critical sg observer origin
    state before input stopped current after output ->
  state.(SchedState).(isRunning) = true ->
  forall observed,
    (exists live, current.(TskState).(inUsedTaskStates)
      observed.(os_sched_call_stack).(stackLeaseSlot) = Some live) ->
    flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed current.
Proof.
  intros environment critical sg observer origin state before input stopped current after output Hstep.
  destruct Hstep; intros Hrunning observed Hlive Hnonidle.
  - revert Hnonidle; eapply proj2; eapply kernel_critical_c_segment_idle_non_idle; eassumption.
  - revert Hnonidle; eapply proj2; eapply kernel_builtin_c_segment_idle_non_idle; eassumption.
  - revert Hnonidle; eapply proj2; eapply task_install_c_step_idle_non_idle; eassumption.
  - revert Hnonidle; eapply proj2; eapply kernel_wake_c_segment_idle_non_idle; eassumption.
  - eapply task_used_priority_transport_non_idle; [|exact Hnonidle].
    eapply kernel_status_c_source_used_priority_transport.
    exact (StatusComponent.kernel_status_c_segment_code _ _ _ _ _ _ H).
  - revert Hnonidle; eapply proj2; eapply kernel_task_creation_c_segment_idle_non_idle; eassumption.
  - revert Hnonidle; eapply proj2; eapply kernel_event_creation_c_segment_idle_non_idle; eassumption.
  - revert Hnonidle; eapply proj2; eapply kernel_queue_creation_c_segment_idle_non_idle; eassumption.
  - revert Hnonidle; eapply proj2; eapply mutex_pend_inheritance_c_segment_idle_non_idle; eassumption.
  - revert Hnonidle; eapply proj2; eapply mutex_post_critical_c_segment_idle_non_idle; eassumption.
  - revert Hnonidle; eapply proj2; eapply task_delete_primitive_c_segment_idle_non_idle; eassumption.
  - revert Hnonidle; eapply proj2; eapply flag_pend_task_primitive_c_step_idle_non_idle; eassumption.
  - eapply tmr_task_delete_c_source_preserves_non_idle; eassumption.
Qed.

Lemma tmr_task_return_c_step_preserves_non_idle :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_program_return_c_step environment critical sg observer origin
    state before input stopped current after output ->
  state.(SchedState).(isRunning) = true ->
  forall observed,
    (exists live, current.(TskState).(inUsedTaskStates)
      observed.(os_sched_call_stack).(stackLeaseSlot) = Some live) ->
    flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed current.
Proof.
  intros environment critical sg observer origin state before input stopped current after output Hstep.
  destruct Hstep; intros Hrunning observed Hlive Hnonidle.
  - eapply tmr_task_program_c_step_preserves_non_idle; eassumption.
  - destruct (kernel_selected_return_c_step_state_stop _ _ _ _ _ _ _ _ H) as [-> _]; exact Hnonidle.
  - exact Hnonidle.
  - exact Hnonidle.
Qed.

Lemma tmr_task_selected_c_step_preserves_non_idle :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_program_selected_c_step environment critical sg observer origin
    state before input stopped current after output ->
  state.(SchedState).(isRunning) = true ->
  forall observed,
    (exists live, current.(TskState).(inUsedTaskStates)
      observed.(os_sched_call_stack).(stackLeaseSlot) = Some live) ->
    flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed current.
Proof.
  intros environment critical sg observer origin state before input stopped current after output Hstep.
  destruct Hstep; intros Hrunning observed Hlive Hnonidle.
  - eapply tmr_task_return_c_step_preserves_non_idle; eassumption.
  - destruct H.
    apply (proj2 (task_used_map_eq_idle_non_idle sg observed entry
      (os_int_exit_installed_state transfer)
      (proj1 (BuiltinComponent.os_int_exit_configured_transfer_state_frame
        environment sg handler entry transfer source)))); exact Hnonidle.
  - revert Hnonidle; eapply proj2; eapply TaskSuspendMaskedC.task_suspend_masked_c_step_idle_non_idle; eassumption.
Qed.

(** stored_origin is arbitrary. The actual observed caller's generation is
    propagated separately, so stopped need not describe this incarnation. *)
Lemma tmr_task_selected_c_sequence_preserves_non_idle :
  forall environment critical sg stored_observer stored_origin state before input stopped current after output,
  kernel_c_sequence (kernel_program_selected_c_step environment critical sg stored_observer stored_origin)
    state before input stopped current after output ->
  state.(SchedState).(isRunning) = true ->
  forall observed,
    task_observer_lifetime state.(TskState) observed.(os_sched_call_invocation)
      (RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot)
        observed.(os_sched_call_stack).(stackLeaseGeneration)) ->
    task_invocation_active current.(TskState) observed.(os_sched_call_invocation)
      (RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot)
        observed.(os_sched_call_stack).(stackLeaseGeneration)) ->
    flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed current.
Proof.
  intros environment critical sg stored_observer stored_origin state before input stopped current after output run.
  induction run; intros Hrunning observed Hlife Hactive Hnonidle.
  - exact Hnonidle.
  - eapply tmr_task_selected_c_step_preserves_non_idle; [exact H|exact Hrunning| |exact Hnonidle].
    destruct Hactive as [Hregistered [Hretired [live [Hlive Hgeneration]]]]; eauto.
  - destruct (sem_pend_selected_c_sequence_lifetime_transport environment critical sg stored_observer stored_origin
      _ _ _ _ _ _ _ run1 observed.(os_sched_call_invocation)
      (RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot)
        observed.(os_sched_call_stack).(stackLeaseGeneration)) Hlife) as [Hmiddle_life Hfirst_back].
    pose proof (proj2 (sem_pend_selected_c_sequence_lifetime_transport environment critical sg
      stored_observer stored_origin _ _ _ _ _ _ _ run2 observed.(os_sched_call_invocation)
      (RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot)
        observed.(os_sched_call_stack).(stackLeaseGeneration)) Hmiddle_life) Hactive) as Hmiddle_active.
    assert (Hmiddle_running : middle.(SchedState).(isRunning) = true).
    { rewrite (kernel_program_selected_c_sequence_running environment critical sg stored_observer stored_origin
        _ _ _ _ _ _ _ run1); exact Hrunning. }
    eapply IHrun2; [exact Hmiddle_running|exact Hmiddle_life|exact Hactive|].
    eapply IHrun1; eassumption.
  - eapply IHrun; eassumption.
Qed.

(** The completed consumer derives final active from the actual normal
    return and Task source. It does not constrain the internal stop bit. *)
Lemma tmr_task_selected_c_return_preserves_non_idle :
  forall environment critical sg stored_observer stored_origin state before input stopped current after output
    original returned,
  kernel_c_sequence (kernel_program_selected_c_step environment critical sg stored_observer stored_origin)
    state before input stopped current after output ->
  task_in_range sg state.(TskState) -> kernel_call_task_source original state ->
  state.(SchedState).(isRunning) = true ->
  kernel_call_normal_return original state returned current -> kernel_call_task_source returned current ->
  flag_pend_non_idle_at sg original state -> flag_pend_non_idle_at sg returned current.
Proof.
  intros environment critical sg stored_observer stored_origin state before input stopped current after output
    original returned Hrun Hrange Hsource Hrunning Hnormal Hreturned Hnonidle.
  assert (Hlife : task_observer_lifetime state.(TskState) original.(os_sched_call_invocation)
    (RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
      original.(os_sched_call_stack).(stackLeaseGeneration))).
  { rewrite <- (proj1 Hsource); apply task_observer_lifetime_from_active with sg;
      [exact Hrange|exact (proj1 (proj2 Hsource))]. }
  assert (Hactive : task_invocation_active current.(TskState) original.(os_sched_call_invocation)
    (RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
      original.(os_sched_call_stack).(stackLeaseGeneration))).
  { rewrite <- (proj1 Hsource); eapply kernel_call_same_return_observer_active;
      [exact (proj1 Hnormal)|exact Hreturned]. }
  pose proof (tmr_task_selected_c_sequence_preserves_non_idle environment critical sg stored_observer stored_origin
    _ _ _ _ _ _ _ Hrun Hrunning original Hlife Hactive Hnonidle) as Hresult.
  unfold flag_pend_non_idle_at in *.
  rewrite (proj2 (proj2 (proj1 Hnormal))); exact Hresult.
Qed.

(** This concrete producer consumes the protected task_suspend_step and
    both actual masked heaps. It keeps the original selected-program source
    and the same run, including every actual Suspend result branch. *)
Lemma tmr_task_suspend_actual_c_post_idle_non_idle :
  forall environment critical saved_local sg original mask original_state caller saved call frame before after
    observer origin event_observer observed,
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
    (task_idle_ready sg call.(TaskSuspendActualC.suspend_actual_entry).(TskState) ->
      task_idle_ready sg call.(TaskSuspendActualC.suspend_actual_checkpoint).(TskState)) /\
    (flag_pend_non_idle_at sg observed call.(TaskSuspendActualC.suspend_actual_entry) ->
      flag_pend_non_idle_at sg observed call.(TaskSuspendActualC.suspend_actual_checkpoint)).
Proof.
  intros environment critical saved_local sg original mask original_state caller saved call frame before after
    observer origin event_observer observed Hfacts Hinput Houtput.
  destruct (SelectedSuspendComposition.task_suspend_acquired_c_post_selected_sequence environment critical saved_local sg
    original mask original_state caller saved call frame before after observer origin event_observer Hfacts Hinput Houtput)
    as [run [Hsource Hidle_source]].
  exists run; split; [exact Hsource|].
  eapply TaskSuspendMaskedC.task_suspend_masked_c_step_idle_non_idle.
  eapply TaskSuspendMaskedC.task_suspend_masked_c_step_from_acquired_c_post; eassumption.
Qed.

(** The existing Idle source marker is consumed on its exact C step. The
    observed caller is independent of the program's stored origin. Status
    retains its real protected guard; no blanket marker producer is asserted. *)
Lemma tmr_task_program_c_idle_source_transport :
  forall environment critical sg stored_observer stored_origin state before input stopped current after output
    (step : kernel_program_c_step environment critical sg stored_observer stored_origin
      state before input stopped current after output),
  kernel_program_original_idle_source environment critical sg stored_observer stored_origin
    _ _ _ _ _ _ _ step ->
  state.(SchedState).(isRunning) = true ->
  forall observed,
    (exists live, current.(TskState).(inUsedTaskStates)
      observed.(os_sched_call_stack).(stackLeaseSlot) = Some live) ->
    (task_idle_ready sg state.(TskState) -> task_idle_ready sg current.(TskState)) /\
    (flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed current).
Proof.
  intros environment critical sg stored_observer stored_origin state before input stopped current after output
    step Hsource Hrunning observed Hlive.
  destruct Hsource.
  - eapply kernel_critical_c_segment_idle_non_idle; eassumption.
  - eapply kernel_builtin_c_segment_idle_non_idle; eassumption.
  - eapply task_install_c_step_idle_non_idle; eassumption.
  - eapply kernel_wake_c_segment_idle_non_idle; eassumption.
  - eapply kernel_status_c_segment_idle_non_idle; eassumption.
  - eapply kernel_task_creation_c_segment_idle_non_idle; eassumption.
  - eapply kernel_event_creation_c_segment_idle_non_idle; eassumption.
  - eapply kernel_queue_creation_c_segment_idle_non_idle; eassumption.
  - eapply mutex_pend_inheritance_c_segment_idle_non_idle; eassumption.
  - eapply mutex_post_critical_c_segment_idle_non_idle; eassumption.
  - eapply task_delete_primitive_c_segment_idle_non_idle; eassumption.
  - eapply flag_pend_task_primitive_c_step_idle_non_idle; eassumption.
  - split; intro Hinitial.
    + eapply tmr_task_delete_c_source_preserves_idle; eassumption.
    + eapply tmr_task_delete_c_source_preserves_non_idle; eassumption.
Qed.

Lemma tmr_task_return_c_idle_source_transport :
  forall environment critical sg stored_observer stored_origin state before input stopped current after output
    (step : kernel_program_return_c_step environment critical sg stored_observer stored_origin
      state before input stopped current after output),
  kernel_program_return_idle_source environment critical sg stored_observer stored_origin
    _ _ _ _ _ _ _ step ->
  state.(SchedState).(isRunning) = true ->
  forall observed,
    (exists live, current.(TskState).(inUsedTaskStates)
      observed.(os_sched_call_stack).(stackLeaseSlot) = Some live) ->
    (task_idle_ready sg state.(TskState) -> task_idle_ready sg current.(TskState)) /\
    (flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed current).
Proof.
  intros environment critical sg stored_observer stored_origin state before input stopped current after output
    step Hsource Hrunning observed Hlive.
  destruct Hsource.
  - eapply tmr_task_program_c_idle_source_transport; eassumption.
  - destruct (kernel_selected_return_c_step_state_stop _ _ _ _ _ _ _ _ actual) as [-> _]; split; trivial.
  - apply task_used_map_eq_idle_non_idle; reflexivity.
  - apply task_used_map_eq_idle_non_idle; reflexivity.
Qed.

Lemma tmr_task_selected_c_idle_source_transport :
  forall environment critical sg stored_observer stored_origin state before input stopped current after output
    (step : kernel_program_selected_c_step environment critical sg stored_observer stored_origin
      state before input stopped current after output),
  kernel_program_selected_idle_source environment critical sg stored_observer stored_origin
    _ _ _ _ _ _ _ step ->
  state.(SchedState).(isRunning) = true ->
  forall observed,
    (exists live, current.(TskState).(inUsedTaskStates)
      observed.(os_sched_call_stack).(stackLeaseSlot) = Some live) ->
    (task_idle_ready sg state.(TskState) -> task_idle_ready sg current.(TskState)) /\
    (flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed current).
Proof.
  intros environment critical sg stored_observer stored_origin state before input stopped current after output
    step Hsource Hrunning observed Hlive.
  destruct Hsource.
  - eapply tmr_task_return_c_idle_source_transport; eassumption.
  - destruct actual; apply task_used_map_eq_idle_non_idle.
    exact (proj1 (BuiltinComponent.os_int_exit_configured_transfer_state_frame
      environment sg handler entry transfer source)).
  - eapply TaskSuspendMaskedC.task_suspend_masked_c_step_idle_non_idle; exact actual.
Qed.

Lemma tmr_task_selected_sequence_idle_source_transport :
  forall environment critical sg stored_observer stored_origin state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg stored_observer stored_origin)
      state before input stopped current after output),
  kernel_program_selected_sequence_idle_source environment critical sg stored_observer stored_origin
    _ _ _ _ _ _ _ run ->
  state.(SchedState).(isRunning) = true ->
  forall observed,
    task_observer_lifetime state.(TskState) observed.(os_sched_call_invocation)
      (RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot)
        observed.(os_sched_call_stack).(stackLeaseGeneration)) ->
    task_invocation_active current.(TskState) observed.(os_sched_call_invocation)
      (RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot)
        observed.(os_sched_call_stack).(stackLeaseGeneration)) ->
    (task_idle_ready sg state.(TskState) -> task_idle_ready sg current.(TskState)) /\
    (flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed current).
Proof.
  intros environment critical sg stored_observer stored_origin state before input stopped current after output
    run Hsource.
  induction Hsource; intros Hrunning observed Hlife Hactive.
  - split; trivial.
  - eapply tmr_task_selected_c_idle_source_transport; [exact H|exact Hrunning|].
    destruct Hactive as [Hregistered [Hretired [live [Hlive Hgeneration]]]]; eauto.
  - destruct (sem_pend_selected_c_sequence_lifetime_transport environment critical sg stored_observer stored_origin
      _ _ _ _ _ _ _ first observed.(os_sched_call_invocation)
      (RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot)
        observed.(os_sched_call_stack).(stackLeaseGeneration)) Hlife) as [Hmiddle_life Hfirst_back].
    pose proof (proj2 (sem_pend_selected_c_sequence_lifetime_transport environment critical sg
      stored_observer stored_origin _ _ _ _ _ _ _ last observed.(os_sched_call_invocation)
      (RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot)
        observed.(os_sched_call_stack).(stackLeaseGeneration)) Hmiddle_life) Hactive) as Hmiddle_active.
    assert (Hmiddle_running : middle.(SchedState).(isRunning) = true).
    { rewrite (kernel_program_selected_c_sequence_running environment critical sg stored_observer stored_origin
        _ _ _ _ _ _ _ first); exact Hrunning. }
    destruct (IHHsource1 Hrunning observed Hlife Hmiddle_active) as [Hfirst_idle Hfirst_non_idle].
    destruct (IHHsource2 Hmiddle_running observed Hmiddle_life Hactive) as [Hlast_idle Hlast_non_idle].
    split; auto.
  - eapply IHHsource; eassumption.
Qed.

Lemma tmr_task_selected_return_idle_source_transport :
  forall environment critical sg stored_observer stored_origin state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg stored_observer stored_origin)
      state before input stopped current after output) original returned,
  kernel_program_selected_sequence_idle_source environment critical sg stored_observer stored_origin
    _ _ _ _ _ _ _ run ->
  task_in_range sg state.(TskState) -> kernel_call_task_source original state ->
  state.(SchedState).(isRunning) = true ->
  kernel_call_normal_return original state returned current -> kernel_call_task_source returned current ->
  (task_idle_ready sg state.(TskState) -> task_idle_ready sg current.(TskState)) /\
  (flag_pend_non_idle_at sg original state -> flag_pend_non_idle_at sg returned current).
Proof.
  intros environment critical sg stored_observer stored_origin state before input stopped current after output
    run original returned Hidle_source Hrange Hsource Hrunning Hnormal Hreturned.
  assert (Hlife : task_observer_lifetime state.(TskState) original.(os_sched_call_invocation)
    (RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
      original.(os_sched_call_stack).(stackLeaseGeneration))).
  { rewrite <- (proj1 Hsource); apply task_observer_lifetime_from_active with sg;
      [exact Hrange|exact (proj1 (proj2 Hsource))]. }
  assert (Hactive : task_invocation_active current.(TskState) original.(os_sched_call_invocation)
    (RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
      original.(os_sched_call_stack).(stackLeaseGeneration))).
  { rewrite <- (proj1 Hsource); eapply kernel_call_same_return_observer_active;
      [exact (proj1 Hnormal)|exact Hreturned]. }
  destruct (tmr_task_selected_sequence_idle_source_transport environment critical sg stored_observer stored_origin
    _ _ _ _ _ _ _ run Hidle_source Hrunning original Hlife Hactive) as [Hidle Hnonidle].
  split; [exact Hidle|].
  unfold flag_pend_non_idle_at in *.
  rewrite (proj2 (proj2 (proj1 Hnormal))); exact Hnonidle.
Qed.
