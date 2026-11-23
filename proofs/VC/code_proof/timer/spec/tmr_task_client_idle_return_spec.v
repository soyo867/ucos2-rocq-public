Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_api_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_c_step_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_sw_hook_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_idle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_history_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_idle_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Import CriticalComponent PrimitiveComponent SelectedReturnPrimitive SelectedCProgram.
Import SelectedIdleComposition SelectedIdleFrames SelectedIdleWakeStatus SelectedIdleBuiltin.
Import SelectedIdleCritical SelectedMutexIdle SelectedDeleteIdle SelectedControlComposition.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The public refined post already retains this protected relation. Its
    local self value is reconstructed from the observed scheduling bit,
    without replacing the actual result or the acquired/released states. *)
Lemma tmr_task_suspend_protected_step : forall sg request priority acquired error scheduled released,
  task_suspend_protected sg request priority acquired (error, scheduled) released ->
  task_suspend_step sg request priority acquired (encode_os_err_code error)
    (if scheduled then 1 else 0) released.
Proof.
  intros; exists error; split; [reflexivity|].
  destruct scheduled; exact H.
Qed.

Lemma tmr_task_suspend_protected_idle_non_idle : forall sg observed request priority acquired error scheduled released,
  UCOS2_state_inv sg acquired ->
  task_suspend_protected sg request priority acquired (error, scheduled) released ->
  (task_idle_ready sg acquired.(TskState) -> task_idle_ready sg released.(TskState)) /\
  (flag_pend_non_idle_at sg observed acquired -> flag_pend_non_idle_at sg observed released).
Proof.
  intros; eapply TaskSuspendActualC.task_suspend_step_idle_non_idle; [exact H|].
  eapply tmr_task_suspend_protected_step; exact H0.
Qed.

(** This is a proved consequence of the unchanged API post, preserving
    its same existential tuple, arbitrary X, tail assertion and frame.
    It records only the protected cut; Save/Restore/Scheduler remain the
    separate actual source intervals already carried by the old post. *)
Definition tmr_task_suspend_refined_idle_post environment critical saved_local sg original mask before request
  (frame : Assertion) (result : Z) (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  match task_suspend_argument_error sg request with
  | Some error => coq_prop (result = encode_os_err_code error /\
      safeExec (fun state => state = before) (StateRelMonad.ret result) X) && frame
  | None => EX saved acquired_call acquired pointer priority residual released checkpoint_call checkpoint scheduled error,
      coq_prop (task_suspend_save_observation critical sg original acquired_call mask saved before acquired /\
        task_suspend_current_read_view sg request acquired pointer priority residual /\
        result = encode_os_err_code error /\
        task_suspend_protected sg request priority acquired (error, scheduled) released /\
        task_suspend_restore_observation critical sg acquired_call checkpoint_call released checkpoint /\
        task_suspend_step sg request priority acquired result (if scheduled then 1 else 0) released /\
        (forall observed, UCOS2_state_inv sg acquired ->
          (task_idle_ready sg acquired.(TskState) -> task_idle_ready sg released.(TskState)) /\
          (flag_pend_non_idle_at sg observed acquired -> flag_pend_non_idle_at sg observed released))) &&
      (task_suspend_refined_tail_post environment critical saved_local sg checkpoint_call mask checkpoint scheduled result X ** frame)
  end.

Lemma tmr_task_suspend_refined_post_idle_cut :
  forall environment critical saved_local sg original mask before request frame result X,
  task_suspend_refined_call_post environment critical saved_local sg original mask before request frame result X |--
  tmr_task_suspend_refined_idle_post environment critical saved_local sg original mask before request frame result X.
Proof.
  intros environment critical saved_local sg original mask before request frame result X heap Hpost.
  unfold task_suspend_refined_call_post, tmr_task_suspend_refined_idle_post in *.
  destruct (task_suspend_argument_error sg request); [exact Hpost|].
  destruct Hpost as (saved & acquired_call & acquired & pointer & priority & residual & released &
    checkpoint_call & checkpoint & scheduled & error & Hfacts & Htail).
  destruct Hfacts as [Hsave [Hread [Hresult [Hprotected Hrestore]]]].
  exists saved, acquired_call, acquired, pointer, priority, residual, released,
    checkpoint_call, checkpoint, scheduled, error; split; [|exact Htail].
  split; [exact Hsave|]. split; [exact Hread|]. split; [exact Hresult|].
  split; [exact Hprotected|]. split; [exact Hrestore|]. split.
  - rewrite Hresult; eapply tmr_task_suspend_protected_step; exact Hprotected.
  - intros observed Hvalid; eapply tmr_task_suspend_protected_idle_non_idle; eassumption.
Qed.

Lemma tmr_task_suspend_refined_idle_post_forget :
  forall environment critical saved_local sg original mask before request frame result X,
  tmr_task_suspend_refined_idle_post environment critical saved_local sg original mask before request frame result X |--
  task_suspend_refined_call_post environment critical saved_local sg original mask before request frame result X.
Proof.
  intros environment critical saved_local sg original mask before request frame result X heap Hpost.
  unfold task_suspend_refined_call_post, tmr_task_suspend_refined_idle_post in *.
  destruct (task_suspend_argument_error sg request); [exact Hpost|].
  destruct Hpost as (saved & acquired_call & acquired & pointer & priority & residual & released &
    checkpoint_call & checkpoint & scheduled & error & Hfacts & Htail).
  destruct Hfacts as [Hsave [Hread [Hresult [Hprotected [Hrestore Hrest]]]]].
  exists saved, acquired_call, acquired, pointer, priority, residual, released,
    checkpoint_call, checkpoint, scheduled, error; split; [|exact Htail].
  exact (conj Hsave (conj Hread (conj Hresult (conj Hprotected Hrestore)))).
Qed.

(** The old Status source is not replaced. An actual protected relation
    may be retained on that same segment, at the same endpoints. In
    particular no live-current premise is fabricated from the API's
    reversible read view, and its pointer-based self result is retained. *)
Lemma tmr_task_status_segment_protected_idle_non_idle :
  forall sg observed entry before current after frame
    (segment : StatusComponent.kernel_status_c_segment sg entry before current after frame)
    request priority error scheduled,
  task_suspend_protected sg request priority entry (error, scheduled) current ->
  (task_idle_ready sg entry.(TskState) -> task_idle_ready sg current.(TskState)) /\
  (flag_pend_non_idle_at sg observed entry -> flag_pend_non_idle_at sg observed current).
Proof.
  intros sg observed entry before current after frame [Hsource Hinput Houtput]
    request priority error scheduled Hprotected.
  destruct Hinput as [owned [rest [Hjoin [[Hvalid Hraw] Hframe]]]].
  eapply tmr_task_suspend_protected_idle_non_idle; eassumption.
Qed.

Inductive tmr_task_program_c_idle_receipt environment critical sg observer origin :
  forall state before input stopped current after output,
  kernel_program_c_step environment critical sg observer origin state before input stopped current after output -> Prop :=
| TmrTaskProgramExistingIdleReceipt : forall state before input stopped current after output step,
    kernel_program_original_idle_source environment critical sg observer origin
      state before input stopped current after output step ->
    tmr_task_program_c_idle_receipt environment critical sg observer origin _ _ _ _ _ _ _ step
| TmrTaskProgramProtectedStatusReceipt : forall entry before current after frame
    (segment : StatusComponent.kernel_status_c_segment sg entry before current after frame)
    request priority error scheduled legacy_result
    (legacy : task_suspend_critical sg request entry legacy_result current),
    StatusComponent.kernel_status_c_segment_code _ _ _ _ _ _ segment =
      StatusComponent.KernelStatusCSuspendSource sg entry request legacy_result current legacy ->
    task_suspend_protected sg request priority entry (error, scheduled) current ->
    tmr_task_program_c_idle_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCStatus environment critical sg observer origin entry before current after frame segment).

Lemma tmr_task_program_c_idle_receipt_transport :
  forall environment critical sg observer origin state before input stopped current after output step,
  tmr_task_program_c_idle_receipt environment critical sg observer origin
    state before input stopped current after output step ->
  state.(SchedState).(isRunning) = true ->
  forall observed,
    (exists live, current.(TskState).(inUsedTaskStates) observed.(os_sched_call_stack).(stackLeaseSlot) = Some live) ->
    (task_idle_ready sg state.(TskState) -> task_idle_ready sg current.(TskState)) /\
    (flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed current).
Proof.
  intros environment critical sg observer origin state before input stopped current after output step Hreceipt.
  destruct Hreceipt; intros Hrunning observed Hlive.
  - eapply tmr_task_program_c_idle_source_transport; eassumption.
  - eapply tmr_task_status_segment_protected_idle_non_idle; eassumption.
Qed.

Inductive tmr_task_return_c_idle_receipt environment critical sg observer origin :
  forall state before input stopped current after output,
  kernel_program_return_c_step environment critical sg observer origin state before input stopped current after output -> Prop :=
| TmrTaskReturnOriginalIdleReceipt : forall state before input stopped current after output step,
    tmr_task_program_c_idle_receipt environment critical sg observer origin state before input stopped current after output step ->
    tmr_task_return_c_idle_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramReturnOriginal environment critical sg observer origin state before input stopped current after output step)
| TmrTaskReturnExistingIdleReceipt : forall state before input stopped current after output step,
    kernel_program_return_idle_source environment critical sg observer origin state before input stopped current after output step ->
    tmr_task_return_c_idle_receipt environment critical sg observer origin _ _ _ _ _ _ _ step.

Lemma tmr_task_return_c_idle_receipt_transport :
  forall environment critical sg observer origin state before input stopped current after output step,
  tmr_task_return_c_idle_receipt environment critical sg observer origin
    state before input stopped current after output step ->
  state.(SchedState).(isRunning) = true ->
  forall observed,
    (exists live, current.(TskState).(inUsedTaskStates) observed.(os_sched_call_stack).(stackLeaseSlot) = Some live) ->
    (task_idle_ready sg state.(TskState) -> task_idle_ready sg current.(TskState)) /\
    (flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed current).
Proof.
  intros environment critical sg observer origin state before input stopped current after output step Hreceipt.
  destruct Hreceipt; intros Hrunning observed Hlive.
  - eapply tmr_task_program_c_idle_receipt_transport; eassumption.
  - eapply tmr_task_return_c_idle_source_transport; eassumption.
Qed.

Inductive tmr_task_selected_c_idle_receipt critical sg observer origin :
  forall environment state before input stopped current after output,
  kernel_program_selected_c_step environment critical sg observer origin state before input stopped current after output -> Prop :=
| TmrTaskSelectedReturnIdleReceipt : forall environment state before input stopped current after output step,
    tmr_task_return_c_idle_receipt environment critical sg observer origin state before input stopped current after output step ->
    tmr_task_selected_c_idle_receipt critical sg observer origin environment _ _ _ _ _ _ _
      (@KernelSelectedProgramReturn critical sg observer origin environment state before input stopped current after output step)
| TmrTaskSelectedExistingIdleReceipt : forall environment state before input stopped current after output step,
    kernel_program_selected_idle_source environment critical sg observer origin state before input stopped current after output step ->
    tmr_task_selected_c_idle_receipt critical sg observer origin environment _ _ _ _ _ _ _ step.

Lemma tmr_task_selected_c_idle_receipt_transport :
  forall environment critical sg observer origin state before input stopped current after output step,
  tmr_task_selected_c_idle_receipt critical sg observer origin environment
    state before input stopped current after output step ->
  state.(SchedState).(isRunning) = true ->
  forall observed,
    (exists live, current.(TskState).(inUsedTaskStates) observed.(os_sched_call_stack).(stackLeaseSlot) = Some live) ->
    (task_idle_ready sg state.(TskState) -> task_idle_ready sg current.(TskState)) /\
    (flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed current).
Proof.
  intros environment critical sg observer origin state before input stopped current after output step Hreceipt.
  destruct Hreceipt; intros Hrunning observed Hlive.
  - eapply tmr_task_return_c_idle_receipt_transport; eassumption.
  - eapply tmr_task_selected_c_idle_source_transport; eassumption.
Qed.

Definition tmr_task_selected_sequence_idle_receipt environment critical sg observer origin
  state before input stopped current after output
  (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    state before input stopped current after output) : Prop :=
  kernel_c_sequence_has_source (kernel_program_selected_c_step environment critical sg observer origin)
    (tmr_task_selected_c_idle_receipt critical sg observer origin environment)
    state before input stopped current after output run.

Lemma tmr_task_selected_sequence_idle_receipt_transport :
  forall environment critical sg stored_observer stored_origin state before input stopped current after output run,
  tmr_task_selected_sequence_idle_receipt environment critical sg stored_observer stored_origin
    state before input stopped current after output run ->
  state.(SchedState).(isRunning) = true ->
  forall observed,
    task_observer_lifetime state.(TskState) observed.(os_sched_call_invocation)
      (RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot) observed.(os_sched_call_stack).(stackLeaseGeneration)) ->
    task_invocation_active current.(TskState) observed.(os_sched_call_invocation)
      (RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot) observed.(os_sched_call_stack).(stackLeaseGeneration)) ->
    (task_idle_ready sg state.(TskState) -> task_idle_ready sg current.(TskState)) /\
    (flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed current).
Proof.
  intros environment critical sg stored_observer stored_origin state before input stopped current after output run Hreceipt.
  induction Hreceipt; intros Hrunning observed Hlife Hactive.
  - split; trivial.
  - eapply tmr_task_selected_c_idle_receipt_transport; [exact H|exact Hrunning|].
    destruct Hactive as [Hregistered [Hretired [live [Hlive Hgeneration]]]]; eauto.
  - destruct (sem_pend_selected_c_sequence_lifetime_transport environment critical sg stored_observer stored_origin
      _ _ _ _ _ _ _ first observed.(os_sched_call_invocation)
      (RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot)
        observed.(os_sched_call_stack).(stackLeaseGeneration)) Hlife) as [Hmiddle_life Hfirst_back].
    pose proof (proj2 (sem_pend_selected_c_sequence_lifetime_transport environment critical sg stored_observer stored_origin
      _ _ _ _ _ _ _ last observed.(os_sched_call_invocation)
      (RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot)
        observed.(os_sched_call_stack).(stackLeaseGeneration)) Hmiddle_life) Hactive) as Hmiddle_active.
    assert (Hmiddle_running : middle.(SchedState).(isRunning) = true).
    { rewrite (kernel_program_selected_c_sequence_running environment critical sg stored_observer stored_origin
        _ _ _ _ _ _ _ first); exact Hrunning. }
    destruct (IHHreceipt1 Hrunning observed Hlife Hmiddle_active) as [Hfirst_idle Hfirst_non_idle].
    destruct (IHHreceipt2 Hmiddle_running observed Hmiddle_life Hactive) as [Hlast_idle Hlast_non_idle].
    split; auto.
  - eapply IHHreceipt; eassumption.
Qed.

(** This constructor consumes the actual protected relation obtained by
    opening the public post. It decorates the SAME existing Status segment
    and constructs one old selected run with both finite receipts. No heap
    is invented and no old source proof is cast to a different execution. *)
Lemma tmr_task_protected_status_selected_sequence :
  forall environment critical sg observer origin event_observer entry before current after frame
    (segment : StatusComponent.kernel_status_c_segment sg entry before current after frame)
    request priority error scheduled legacy_result
    (legacy : task_suspend_critical sg request entry legacy_result current),
  StatusComponent.kernel_status_c_segment_code _ _ _ _ _ _ segment =
    StatusComponent.KernelStatusCSuspendSource sg entry request legacy_result current legacy ->
  task_suspend_protected sg request priority entry (error, scheduled) current ->
  exists (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    entry before (UCOS2_inv sg entry ** frame) false current after (UCOS2_inv sg current ** frame)),
    SelectedCSource.kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
      _ _ _ _ _ _ _ run /\
    sem_pend_selected_c_sequence_receipt environment critical sg observer origin _ _ _ _ _ _ _ run /\
    tmr_task_selected_sequence_idle_receipt environment critical sg observer origin _ _ _ _ _ _ _ run.
Proof.
  intros environment critical sg observer origin event_observer entry before current after frame segment
    request priority error scheduled legacy_result legacy Hcode Hprotected.
  pose (original := @KernelProgramCStatus environment critical sg observer origin entry before current after frame segment).
  pose (return_step := @KernelProgramReturnOriginal environment critical sg observer origin _ _ _ _ _ _ _ original).
  pose (selected := @KernelSelectedProgramReturn critical sg observer origin environment _ _ _ _ _ _ _ return_step).
  exists (KernelCSequenceAtom _ _ _ _ _ _ _ _ selected); split.
  - apply KernelCSourceAtom; unfold selected, return_step, original.
    constructor; constructor; left; constructor.
  - split.
    + apply KernelCSourceAtom; unfold selected, return_step, original.
      constructor; constructor; constructor.
    + apply KernelCSourceAtom; unfold selected, return_step, original.
      apply TmrTaskSelectedReturnIdleReceipt, TmrTaskReturnOriginalIdleReceipt.
      eapply TmrTaskProgramProtectedStatusReceipt; [exact Hcode|exact Hprotected].
Qed.

(** This actual-source factory keeps the original prefix constructor and
    the exact Status segment; the finite Sem receipt is not lost when the
    selected run is hidden in that prefix. *)
Lemma tmr_task_protected_status_prefix :
  forall environment critical sg observer (origin : TaskInvocationOrigin) (event_observer : option nat)
    entry before current after frame
    (segment : StatusComponent.kernel_status_c_segment sg entry before current after frame)
    request priority error scheduled legacy_result
    (legacy : task_suspend_critical sg request entry legacy_result current),
  StatusComponent.kernel_status_c_segment_code _ _ _ _ _ _ segment =
    StatusComponent.KernelStatusCSuspendSource sg entry request legacy_result current legacy ->
  task_suspend_protected sg request priority entry (error, scheduled) current ->
  exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer entry current after,
    sem_pend_sched_prefix_receipt environment critical sg observer entry current after prefix /\
    (forall observed,
      (task_idle_ready sg entry.(TskState) -> task_idle_ready sg current.(TskState)) /\
      (flag_pend_non_idle_at sg observed entry -> flag_pend_non_idle_at sg observed current)).
Proof.
  intros environment critical sg observer origin event_observer entry before current after frame segment
    request priority error scheduled legacy_result legacy Hcode Hprotected.
  destruct (tmr_task_protected_status_selected_sequence environment critical sg observer origin event_observer
    entry before current after frame segment request priority error scheduled legacy_result legacy Hcode Hprotected)
    as [run [Hsource [Hsem Hidle]]].
  exists (@SchedulerPhaseCandidate.OsSchedTaskReturnPrefixCSequence environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ run Hsource); split.
  - constructor; exact Hsem.
  - intro observed; eapply tmr_task_status_segment_protected_idle_non_idle; eassumption.
Qed.

(** Only the literal SP save can change an existing TCB here; the bound
    hook and final install do not change its priority or readiness. *)
Lemma tmr_task_bound_switch_idle_non_idle : forall external sg entry call installed observed,
  task_sw_hook_source_binding external -> os_sched_switch_source external sg entry call installed ->
  (task_idle_ready sg entry.(TskState) -> task_idle_ready sg installed.(TskState)) /\
  (flag_pend_non_idle_at sg observed entry -> flag_pend_non_idle_at sg observed installed).
Proof.
  intros external sg entry call installed observed Hbinding
    [Hrequest [sp [saved [hooked [incoming [resumed [Hsave [Hhook [Hdestination Hinstalled]]]]]]]]].
  unfold task_sw_hook_source_binding in Hbinding; rewrite Hbinding in Hhook.
  change (hooked = os_sched_save_current_sp (os_sched_prefix_state entry)
    call.(os_sched_call_stack).(stackLeaseSlot) sp) in Hhook.
  rewrite Hinstalled, Hhook; unfold os_sched_save_current_sp.
  cbn [os_sched_prefix_state replace_SchedS TskState].
  destruct (entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot)) as [node|] eqn:Hnode.
  - split.
    + intro Hidle; eapply task_update_ready_preserves_idle_ready;
        [exact Hnode|reflexivity|intros; assumption|exact Hidle].
    + apply task_used_priority_transport_non_idle.
      eapply task_update_used_priority_transport; [exact Hnode|reflexivity|reflexivity].
  - apply task_used_map_eq_idle_non_idle; reflexivity.
Qed.

Lemma tmr_task_nonswitch_body_idle_receipt : forall environment critical sg entry original,
  os_sched_requests_switch entry = false ->
  exists body : SchedulerPhaseCandidate.os_sched_task_body_source environment critical sg
    entry original original (os_sched_prefix_state entry),
    sem_pend_sched_body_receipt environment critical sg entry original original (os_sched_prefix_state entry) body /\
    (task_idle_ready sg entry.(TskState) -> task_idle_ready sg (os_sched_prefix_state entry).(TskState)) /\
    (flag_pend_non_idle_at sg original entry -> flag_pend_non_idle_at sg original (os_sched_prefix_state entry)).
Proof.
  intros environment critical sg entry original Hrequest.
  exists (@SchedulerPhaseCandidate.OsSchedTaskBodyNoSwitch environment critical sg entry original Hrequest).
  split; [constructor|]; split; trivial.
Qed.

(** The three switched body factories below consume one real protected
    Status cut. They keep each original body constructor, its actual call
    identities and install/transfer facts. Other prefix producers remain
    separate; these are not a classification of all broad body sources. *)
Lemma tmr_task_protected_status_task_install_body :
  forall environment critical sg entry original first_installed context outgoing hooked resumed returned
    prefix_before before frame
    (segment : StatusComponent.kernel_status_c_segment sg first_installed prefix_before hooked before frame)
    request priority error scheduled legacy_result
    (legacy : task_suspend_critical sg request first_installed legacy_result hooked)
    (origin : TaskInvocationOrigin) (event_observer : option nat),
  task_sw_hook_source_binding environment.(task_stack_call_external) ->
  os_sched_switch_source environment.(task_stack_call_external) sg entry original first_installed ->
  StatusComponent.kernel_status_c_segment_code _ _ _ _ _ _ segment =
    StatusComponent.KernelStatusCSuspendSource sg first_installed request legacy_result hooked legacy ->
  task_suspend_protected sg request priority first_installed (error, scheduled) hooked ->
  kernel_client_stops environment.(task_stack_call_external).(os_sched_hook_action) original.(os_sched_call_invocation) = false ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding environment.(task_stack_call_external) context outgoing hooked original.(os_sched_call_stack) resumed ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  task_tcb_init_stack_same_call returned original ->
  exists body : SchedulerPhaseCandidate.os_sched_task_body_source environment critical sg entry original returned
    (os_sched_install_context context outgoing original.(os_sched_call_stack) hooked),
    sem_pend_sched_body_receipt environment critical sg _ _ _ _ body /\
    (task_idle_ready sg entry.(TskState) ->
      task_idle_ready sg (os_sched_install_context context outgoing original.(os_sched_call_stack) hooked).(TskState)) /\
    (flag_pend_non_idle_at sg original entry ->
      flag_pend_non_idle_at sg returned (os_sched_install_context context outgoing original.(os_sched_call_stack) hooked)).
Proof.
  intros environment critical sg entry original first_installed context outgoing hooked resumed returned prefix_before before frame
    segment request priority error scheduled legacy_result legacy origin event_observer Hbinding Hfirst Hcode Hprotected
    Hstop Hsaved Hdestination Hhigh Hsame.
  destruct (tmr_task_protected_status_prefix environment critical sg original.(os_sched_call_invocation) origin event_observer
    first_installed prefix_before hooked before frame segment request priority error scheduled legacy_result legacy Hcode Hprotected)
    as [prefix [Hreceipt Hcut]].
  exists (@SchedulerPhaseCandidate.OsSchedTaskBodyTaskLastInstall environment critical sg entry original first_installed
    context outgoing hooked resumed returned before Hfirst prefix Hstop Hsaved Hdestination Hhigh Hsame).
  split; [constructor; exact Hreceipt|].
  destruct (tmr_task_bound_switch_idle_non_idle _ _ _ _ _ original Hbinding Hfirst) as [Hfirst_idle Hfirst_non_idle].
  destruct (Hcut original) as [Hcut_idle Hcut_non_idle].
  split.
  - intro Hidle; apply Hcut_idle, Hfirst_idle; exact Hidle.
  - intro Hnonidle; specialize (Hcut_non_idle (Hfirst_non_idle Hnonidle)).
    unfold flag_pend_non_idle_at in *; rewrite (proj2 (proj2 Hsame)); exact Hcut_non_idle.
Qed.

Lemma tmr_task_protected_status_irq_install_body :
  forall environment critical sg entry original first_installed handler irq_entry transfer returned
    prefix_before before frame
    (segment : StatusComponent.kernel_status_c_segment sg first_installed prefix_before irq_entry before frame)
    request priority error scheduled legacy_result
    (legacy : task_suspend_critical sg request first_installed legacy_result irq_entry)
    (origin : TaskInvocationOrigin) (event_observer : option nat),
  task_sw_hook_source_binding environment.(task_stack_call_external) ->
  os_sched_switch_source environment.(task_stack_call_external) sg entry original first_installed ->
  StatusComponent.kernel_status_c_segment_code _ _ _ _ _ _ segment =
    StatusComponent.KernelStatusCSuspendSource sg first_installed request legacy_result irq_entry legacy ->
  task_suspend_protected sg request priority first_installed (error, scheduled) irq_entry ->
  kernel_client_stops environment.(task_stack_call_external).(os_sched_hook_action) original.(os_sched_call_invocation) = false ->
  os_int_exit_transfer_source environment.(task_stack_call_external) environment.(task_stack_call_port) sg handler irq_entry transfer ->
  transfer.(os_int_exit_incoming_stack) = original.(os_sched_call_stack) ->
  task_tcb_init_stack_same_call returned original ->
  exists body : SchedulerPhaseCandidate.os_sched_task_body_source environment critical sg entry original returned
    (os_int_exit_installed_state transfer),
    sem_pend_sched_body_receipt environment critical sg _ _ _ _ body /\
    (task_idle_ready sg entry.(TskState) -> task_idle_ready sg (os_int_exit_installed_state transfer).(TskState)) /\
    (flag_pend_non_idle_at sg original entry -> flag_pend_non_idle_at sg returned (os_int_exit_installed_state transfer)).
Proof.
  intros environment critical sg entry original first_installed handler irq_entry transfer returned prefix_before before frame
    segment request priority error scheduled legacy_result legacy origin event_observer Hbinding Hfirst Hcode Hprotected
    Hstop Htransfer Hincoming Hsame.
  destruct (tmr_task_protected_status_prefix environment critical sg original.(os_sched_call_invocation) origin event_observer
    first_installed prefix_before irq_entry before frame segment request priority error scheduled legacy_result legacy Hcode Hprotected)
    as [prefix [Hreceipt Hcut]].
  pose (irq_prefix := @or_intror
    (kernel_client_trace critical.(critical_region_clients) sg original.(os_sched_call_invocation) first_installed false irq_entry)
    (exists final_heap, SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg
      original.(os_sched_call_invocation) first_installed irq_entry final_heap) (ex_intro _ before prefix)).
  exists (@SchedulerPhaseCandidate.OsSchedTaskBodyIRQLastInstall environment critical sg entry original first_installed
    handler irq_entry transfer returned Hfirst irq_prefix Hstop Htransfer Hincoming Hsame).
  split; [constructor; unfold irq_prefix; constructor; exact Hreceipt|].
  destruct (tmr_task_bound_switch_idle_non_idle _ _ _ _ _ original Hbinding Hfirst) as [Hfirst_idle Hfirst_non_idle].
  destruct (Hcut original) as [Hcut_idle Hcut_non_idle].
  pose proof (proj1 (sem_pend_bound_irq_transfer_task_map _ _ _ _ _ _ Hbinding Htransfer)) as Hmap.
  destruct (task_used_map_eq_idle_non_idle sg original irq_entry (os_int_exit_installed_state transfer) Hmap)
    as [Hlast_idle Hlast_non_idle].
  split.
  - intro Hidle; apply Hlast_idle, Hcut_idle, Hfirst_idle; exact Hidle.
  - intro Hnonidle; specialize (Hlast_non_idle (Hcut_non_idle (Hfirst_non_idle Hnonidle))).
    unfold flag_pend_non_idle_at in *; rewrite (proj2 (proj2 Hsame)); exact Hlast_non_idle.
Qed.

Lemma tmr_task_protected_status_last_call_body :
  forall environment critical sg entry original first_installed last_entry last_context returned current
    prefix_before before frame
    (segment : StatusComponent.kernel_status_c_segment sg first_installed prefix_before last_entry before frame)
    request priority error scheduled legacy_result
    (legacy : task_suspend_critical sg request first_installed legacy_result last_entry)
    (origin : TaskInvocationOrigin) (event_observer : option nat),
  task_sw_hook_source_binding environment.(task_stack_call_external) ->
  os_sched_switch_source environment.(task_stack_call_external) sg entry original first_installed ->
  StatusComponent.kernel_status_c_segment_code _ _ _ _ _ _ segment =
    StatusComponent.KernelStatusCSuspendSource sg first_installed request legacy_result last_entry legacy ->
  task_suspend_protected sg request priority first_installed (error, scheduled) last_entry ->
  UCOS2_state_inv sg last_entry ->
  os_sched_switch_source environment.(task_stack_call_external) sg last_entry last_context current ->
  task_tcb_init_stack_same_call returned original -> kernel_call_task_source returned current ->
  exists body : SchedulerPhaseCandidate.os_sched_task_body_source environment critical sg entry original returned current,
    sem_pend_sched_body_receipt environment critical sg _ _ _ _ body /\
    (task_idle_ready sg entry.(TskState) -> task_idle_ready sg current.(TskState)) /\
    (flag_pend_non_idle_at sg original entry -> flag_pend_non_idle_at sg returned current).
Proof.
  intros environment critical sg entry original first_installed last_entry last_context returned current prefix_before before frame
    segment request priority error scheduled legacy_result legacy origin event_observer Hbinding Hfirst Hcode Hprotected
    Hvalid Hlast Hsame Hreturned.
  destruct (tmr_task_protected_status_prefix environment critical sg original.(os_sched_call_invocation) origin event_observer
    first_installed prefix_before last_entry before frame segment request priority error scheduled legacy_result legacy Hcode Hprotected)
    as [prefix [Hreceipt Hcut]].
  exists (@SchedulerPhaseCandidate.OsSchedTaskBodyTaskLastCall environment critical sg entry original first_installed
    last_entry last_context returned current before Hfirst prefix Hvalid Hlast Hsame Hreturned).
  split; [constructor; exact Hreceipt|].
  destruct (tmr_task_bound_switch_idle_non_idle _ _ _ _ _ original Hbinding Hfirst) as [Hfirst_idle Hfirst_non_idle].
  destruct (Hcut original) as [Hcut_idle Hcut_non_idle].
  destruct (tmr_task_bound_switch_idle_non_idle _ _ _ _ _ original Hbinding Hlast) as [Hlast_idle Hlast_non_idle].
  split.
  - intro Hidle; apply Hlast_idle, Hcut_idle, Hfirst_idle; exact Hidle.
  - intro Hnonidle; specialize (Hlast_non_idle (Hcut_non_idle (Hfirst_non_idle Hnonidle))).
    unfold flag_pend_non_idle_at in *; rewrite (proj2 (proj2 Hsame)); exact Hlast_non_idle.
Qed.

