Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.Lists.List Coq.Relations.Relation_Operators.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.timer Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.task_retirement Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_wrapper_completion_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_returned_c_segment_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_acquire_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_sem_source_projection_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_idle_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_c_segment_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_c_idle_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_critical_control_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_idle_frames_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_c_step_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_masked_c_step_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_c_segment_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_history_spec.
Import TaskStateDef ListNotations DeleteComponent.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual C observation contains registered calls with their receipts
    and the existing IRQ completion modules at their acquired cuts. Normal
    return is the actual saved-descriptor result. The broader source relation
    is a semantic change; no new architecture-source law is assumed. *)
Definition sem_pend_client_return_source environment critical sg call before returned after : Prop :=
  sem_pend_observed_client_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    call.(os_sched_call_invocation) None call.(os_sched_call_origin)
    before false returned.(os_sched_call_origin) after /\
  kernel_call_normal_return call before returned after.

Lemma sem_pend_client_return_source_from_legacy : forall environment critical sg call before returned after
  (trace : kernel_client_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    call.(os_sched_call_invocation) None call.(os_sched_call_origin)
    before false returned.(os_sched_call_origin) after),
  sem_pend_client_source_calls environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    call.(os_sched_call_invocation) None call.(os_sched_call_origin)
    before false returned.(os_sched_call_origin) after trace ->
  kernel_call_normal_return call before returned after ->
  sem_pend_client_return_source environment critical sg call before returned after.
Proof. intros; split; [eapply SemPendObservedLegacy; eassumption|assumption]. Qed.

Lemma sem_pend_resumption_source_calls_client_trace :
  forall external port clients sg observer event_observer first before stopped last after
    (source : kernel_resumption_task_source_trace external port clients sg observer event_observer
      first before stopped last after),
  sem_pend_resumption_source_calls external port clients sg observer event_observer
    first before stopped last after source ->
  exists trace : kernel_client_task_source_trace external port clients sg observer event_observer
      first before stopped last after,
    sem_pend_client_source_calls external port clients sg observer event_observer
      first before stopped last after trace.
Proof.
  intros external port clients sg observer event_observer first before stopped last after source Hcalls.
  induction Hcalls as [origin state|first before stop_head middle transient stop_tail last after
    segment timer tail Hsegment Htail IH].
  - exists (@KernelClientTaskSourceNil external port clients sg observer event_observer origin state).
    constructor.
  - destruct IH as [suffix Hsuffix].
    eapply sem_pend_client_source_calls_append; eassumption.
Qed.

Lemma sem_pend_source_modular_history_implies_client_return :
  forall environment critical sg call before returned after,
  sem_pend_source_modular_call_history environment critical sg call before returned after ->
  sem_pend_client_return_source environment critical sg call before returned after.
Proof.
intros * [source [Hcalls Hnormal]].
  destruct (sem_pend_resumption_source_calls_client_trace _ _ _ _ _ _ _ _ _ _ _ source Hcalls)
    as [trace Htrace].
  eapply sem_pend_client_return_source_from_legacy; eassumption.
Qed.

Lemma sem_pend_client_return_source_same_call : forall environment critical sg call before returned after,
  sem_pend_client_return_source environment critical sg call before returned after ->
  kernel_stack_call_same_call returned call.
Proof. intros * [Htrace [Hsame Havailable]]; exact Hsame. Qed.

Lemma sem_pend_client_return_source_traces : forall environment critical sg call before returned after,
  sem_pend_client_return_source environment critical sg call before returned after ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg call.(os_sched_call_invocation) None
    call.(os_sched_call_origin) before false returned.(os_sched_call_origin) after /\
  (task_execution_current call.(os_sched_call_origin) before ->
    task_execution_current returned.(os_sched_call_origin) after).
Proof.
intros * [Htrace Hnormal]; split; [exact Htrace|].
  eapply sem_pend_observed_client_trace_preserves_current; exact Htrace.
Qed.

Lemma sem_pend_client_return_source_preserves_validity : forall environment critical sg call before returned after,
  sem_pend_client_return_source environment critical sg call before returned after ->
  UCOS2_state_inv sg before -> UCOS2_state_inv sg after.
Proof.
intros * [Htrace Hnormal] Hvalid.
  exact (proj1 (sem_pend_observed_client_trace_resources _ _ _ _ _ _ _ _ _ _ _
    critical.(critical_region_client_certificates) Htrace Hvalid)).
Qed.

Lemma sem_pend_mutex_post_preserves_unregistered : forall sg eid caller before result schedule after,
  mutex_post_critical sg eid caller before result schedule after ->
  sem_pend_source_unregistered_transport before after.
Proof.
  intros sg eid caller before result schedule after Hcritical.
  destruct Hcritical as [entry event mutex Hlookup Htype Hfields Howner
    |entry event mutex prepared Hlookup Htype Hfields Howner Hprepare Hempty
    |entry event mutex prepared priority woken found owner Hlookup Htype Hfields Howner
       Hprepare Hnonempty Hwake Hfound Htable].
  - apply sem_pend_source_unregistered_transport_map_eq; reflexivity.
  - change (sem_pend_source_unregistered_transport entry prepared).
    apply sem_pend_source_projection_preserves_unregistered; intros slot old Hold.
    eapply sem_pend_mutex_post_prepare_projection; eassumption.
  - change (sem_pend_source_unregistered_transport entry woken).
    eapply sem_pend_source_unregistered_transport_trans with (middle := prepared).
    + apply sem_pend_source_projection_preserves_unregistered; intros slot old Hold.
      eapply sem_pend_mutex_post_prepare_projection; eassumption.
    + eapply sem_pend_source_event_ready_preserves_unregistered; exact Hwake.
Qed.

(** This is a local field consequence of the existing finite C modules.
    A recycled slot is observed only when the actual caller is still live;
    no all-slots survival property is imposed on Delete. *)
Local Lemma sem_pend_program_step_preserves_unregistered :
  forall environment critical sg stored_observer stored_origin before before_heap input stopped after after_heap output,
  kernel_program_c_step environment critical sg stored_observer stored_origin
    before before_heap input stopped after after_heap output ->
  forall slot old, before.(TskState).(inUsedTaskStates) slot = Some old ->
    sem_pend_task_unregistered old ->
    (exists live, after.(TskState).(inUsedTaskStates) slot = Some live) ->
    exists current, after.(TskState).(inUsedTaskStates) slot = Some current /\
      sem_pend_task_unregistered current.
Proof.
  intros environment critical sg stored_observer stored_origin before before_heap input stopped after after_heap output Hstep.
  destruct Hstep; intros slot old Hold Hclear Hlive.
  - destruct H as [Hcompletion [Hphysical [Hsource Hpacket]]].
    clear Hpacket Hphysical Hcompletion.
    destruct call as [actual|actual]; cbn in *.
    + destruct Hsource as [error [Hcritical Hcode]].
      eapply sem_pend_source_projection_preserves_unregistered;
        [|exact Hold|exact Hclear]. intros tid node Hnode.
      eapply tmr_task_sem_change_prio_projection; eassumption.
    + unfold CriticalComponent.mutex_del_critical_fields_observation in Hsource.
      destruct Hsource.
      * destruct H0 as [error [scheduled [Hcritical Hcode]]].
        eapply sem_pend_source_mutex_delete_preserves_unregistered; eassumption.
      * exists old; auto.
  - eapply sem_pend_source_projection_preserves_unregistered;
      [|exact Hold|exact Hclear]. intros tid node Hnode.
    eapply sem_pend_builtin_c_projection; eassumption.
  - eapply sem_pend_source_projection_preserves_unregistered;
      [|exact Hold|exact Hclear]. intros tid node Hnode.
    eapply sem_pend_install_c_projection; eassumption.
  - pose proof (WakeComponent.kernel_wake_c_segment_source _ _ _ _ _ _ _ H) as Hsource.
    destruct Hsource.
    + destruct (flag_task_rdy_result _ _ _ _ _ _ _ H0)
        as [waiter [flags [previous [Hunlink [Hprevious [-> Hschedule]]]]]].
      eapply sem_pend_source_update_preserves_unregistered; [exact Hprevious|reflexivity| |exact Hold|exact Hclear].
      intros [Hevent [Hmulti Hflag]]; unfold sem_pend_task_unregistered; repeat split; assumption || reflexivity.
    + eapply sem_pend_source_event_ready_preserves_unregistered; eassumption.
    + eapply sem_pend_source_projection_preserves_unregistered;
        [|exact Hold|exact Hclear]. intros tid node Hnode.
      eapply sem_pend_tick_task_projection; eassumption.
  - eapply sem_pend_source_projection_preserves_unregistered;
      [|exact Hold|exact Hclear]. intros tid node Hnode.
    eapply sem_pend_status_c_source_projection;
      [exact (StatusComponent.kernel_status_c_segment_code _ _ _ _ _ _ H)|exact Hnode].
  - eapply sem_pend_source_projection_preserves_unregistered;
      [|exact Hold|exact Hclear]. intros tid node Hnode.
    eapply sem_pend_task_creation_c_source_projection;
      [eapply CreationComponent.kernel_task_creation_c_segment_source; exact H|exact Hnode].
  - eapply sem_pend_source_unregistered_transport_map_eq; [|exact Hold|exact Hclear].
    rewrite (proj1 (NamedSourceFrames.kernel_event_creation_c_source_other_fields _ _
      (EventCreationComponent.kernel_event_creation_c_segment_source _ _ _ _ _ _ _ H))); reflexivity.
  - eapply sem_pend_source_unregistered_transport_map_eq; [|exact Hold|exact Hclear].
    rewrite (proj1 (NamedSourceFrames.kernel_queue_creation_c_source_other_fields _ _ _
      (QueueCreationComponent.kernel_queue_creation_c_segment_source _ _ _ _ _ _ _ H))); reflexivity.
  - destruct H as [Hsource Hinput Houtput].
    eapply sem_pend_source_projection_preserves_unregistered;
      [|exact Hold|exact Hclear]. intros tid node Hnode.
    eapply sem_pend_mutex_inheritance_c_projection; eassumption.
  - destruct H as [[Hcaller Hsource] Hinput Houtput].
    eapply sem_pend_mutex_post_preserves_unregistered; eassumption.
  - destruct H; exists old; auto.
  - destruct H; [destruct H| |]; exists old; auto.
  - destruct H as [inputs before_heap prepared_heap Hcontext Hcompletion|capture after_heap Hcontext Hcompletion].
    + destruct Hcompletion as [[Hhistory [Hprepare Hprotocol]] Hinput Houtput].
      destruct Hhistory as [Hlookup [Hselected [Hnode Hpointer]]].
      pose proof (proj2 (task_delete_table_lookup_live _ _ _ _ Hnode)) as Hselected_node.
      change (exists current, inputs.(delete_capture_prepared).(TskState).(inUsedTaskStates) slot = Some current /\
        sem_pend_task_unregistered current).
      destruct (Z.eq_dec slot inputs.(delete_capture_tid)) as [->|Hdifferent].
      * exists (task_delete_prepared_node inputs.(delete_capture_node)); split.
        -- exact (proj2 (task_delete_preparation_task_projections__release_and_recycle_resources
            _ _ _ _ _ Hprepare)).
        -- assert (Hsame : inputs.(delete_capture_node) = old) by congruence.
           rewrite Hsame; destruct Hclear as [Hevent [Hmulti Hflag]].
           unfold sem_pend_task_unregistered; repeat split; assumption || reflexivity.
      * destruct (task_delete_prepare_single_wait_frame _ _ _ _ _ Hprepare) as [next [Hstate Hfields]].
        exists old; split; [|exact Hclear].
        rewrite Hstate; cbn [replace_FlagS replace_EventS replace_SchedS replace_TskS TskState
          glob_task_set_usedtask inUsedTaskStates].
        rewrite (proj2 (Z.eqb_neq slot inputs.(delete_capture_tid)) Hdifferent); exact Hold.
    + destruct (sem_pend_delete_recycle_live_wait_projection _ _ _ _ _ _ _ _ Hold Hlive)
        as [current [Hcurrent Hprojection]].
      exists current; split; [exact Hcurrent|].
      eapply sem_pend_wait_trace_preserves_unregistered; eassumption.
Qed.

Local Lemma sem_pend_program_sequence_preserves_unregistered :
  forall environment critical sg stored_observer stored_origin state before input stopped current after output,
  kernel_c_sequence (kernel_program_c_step environment critical sg stored_observer stored_origin)
    state before input stopped current after output ->
  forall observer tid old generation,
    task_observer_lifetime state.(TskState) observer (RunningInvocation tid generation) ->
    task_invocation_active current.(TskState) observer (RunningInvocation tid generation) ->
    state.(TskState).(inUsedTaskStates) tid = Some old -> sem_pend_task_unregistered old ->
    exists node, current.(TskState).(inUsedTaskStates) tid = Some node /\ sem_pend_task_unregistered node.
Proof.
  intros environment critical sg stored_observer stored_origin state before input stopped current after output run.
  induction run; intros observer tid old generation Hlife Hactive Hold Hclear.
  - exists old; auto.
  - eapply sem_pend_program_step_preserves_unregistered; [exact H|exact Hold|exact Hclear|].
    destruct Hactive as [_ [_ [live [Hlive _]]]]; eauto.
  - destruct (sem_pend_delete_interval_lifetime environment critical sg stored_observer stored_origin
      _ _ _ _ _ _ _ run1 observer (RunningInvocation tid generation) Hlife) as [Hmiddle_life Hfirst_back].
    pose proof (proj2 (sem_pend_delete_interval_lifetime environment critical sg stored_observer stored_origin
      _ _ _ _ _ _ _ run2 observer (RunningInvocation tid generation) Hmiddle_life) Hactive) as Hmiddle_active.
    destruct (IHrun1 observer tid old generation Hlife Hmiddle_active Hold Hclear) as [middle_node [Hmiddle Hfields]].
    eapply IHrun2; eassumption.
  - eapply IHrun; eassumption.
Qed.

Local Lemma sem_pend_program_sequence_preserves_non_idle :
  forall environment critical sg stored_observer stored_origin state before input stopped current after output,
  kernel_c_sequence (kernel_program_c_step environment critical sg stored_observer stored_origin)
    state before input stopped current after output ->
  state.(SchedState).(isRunning) = true -> forall observed,
  task_observer_lifetime state.(TskState) observed.(os_sched_call_invocation)
    (RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot)
      observed.(os_sched_call_stack).(stackLeaseGeneration)) ->
  task_invocation_active current.(TskState) observed.(os_sched_call_invocation)
    (RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot)
      observed.(os_sched_call_stack).(stackLeaseGeneration)) ->
  flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed current.
Proof.
  intros environment critical sg stored_observer stored_origin state before input stopped current after output
    run Hrunning observed Hlife Hactive Hnonidle.
  assert (Hselected : kernel_c_sequence
    (SelectedCProgram.kernel_program_selected_c_step environment critical sg stored_observer stored_origin)
    state before input stopped current after output).
  { clear Hrunning Hlife Hactive Hnonidle.
    induction run.
    - constructor; exact H.
    - apply KernelCSequenceAtom; apply SelectedCProgram.kernel_program_selected_original_step; exact H.
    - eapply KernelCSequenceThen; eassumption.
    - eapply KernelCSequenceAdapt; eassumption. }
  eapply tmr_task_selected_c_sequence_preserves_non_idle; eassumption.
Qed.

Lemma sem_pend_client_return_source_preserves_call_fields :
  forall environment critical sg call before returned after,
  sem_pend_client_return_source environment critical sg call before returned after ->
  UCOS2_state_inv sg before ->
  kernel_call_task_source call before ->
  sem_pend_source_call_fields sg call before -> sem_pend_source_call_fields sg call after.
Proof.
intros environment critical sg call before returned after [Htrace Hnormal] Hvalid Htask Hfields.
  eapply sem_pend_observed_client_trace_preserves with
    (property := sem_pend_source_call_fields sg call) (caller_origin := call.(os_sched_call_origin));
    [apply critical_region_client_certificates| | | | | | | | |exact Htrace|reflexivity|
      exact (proj1 (proj2 Htask))|exact Hvalid|exact Hfields].
  2: { intros initial final Hframe Hbefore.
    unfold sem_pend_source_call_fields, flag_pend_non_idle_at in *.
    rewrite (sem_pend_irq_cut_running _ _ Hframe), (sem_pend_irq_cut_tasks _ _ Hframe); exact Hbefore. }
  2: { intros entry_environment entry_sg initial node handler suspended publication local frame
      before_heap saved_heap body_heap Hentry [Hrunning [Hnonidle [old [Hold Hclear]]]].
    destruct (sem_pend_irq_entry_frames _ _ _ _ _ _ _ _ _ _ _ _ Hentry)
      as [Hlife [Hevents [Hnames [Htimers Hsched]]]].
    split; [rewrite Hsched; exact Hrunning|]. split.
    - destruct Hnonidle as [active [Hactive [Hgeneration Hpriority]]].
      destruct (sem_pend_irq_entry_task_at _ _ _ _ _ _ _ _ _ _ _ _ Hentry _ active Hactive)
        as [current [Hcurrent Hsame_fields]].
      exists current; split; [exact Hcurrent|].
      rewrite (sem_pend_saved_sp_fields_update active current Hsame_fields).
      exact (conj Hgeneration Hpriority).
    - destruct (sem_pend_irq_entry_task_at _ _ _ _ _ _ _ _ _ _ _ _ Hentry _ old Hold)
        as [current [Hcurrent Hsame_fields]].
      exists current; split; [exact Hcurrent|].
      rewrite (sem_pend_saved_sp_fields_update old current Hsame_fields).
      exact Hclear. }
  2: { intros post_environment post_critical source_env local frame post_call before_heap after_heap
      segment Hreceipt [Hrunning [Hnonidle [old [Hold Hclear]]]].
    split.
    - rewrite (SelectedCriticalControl.mutex_post_critical_c_segment_running _ _ _ _ _ _ _ _ _ _ segment).
      exact Hrunning.
    - split.
      + exact (proj2 (SelectedMutexIdle.mutex_post_critical_c_segment_idle_non_idle
          _ _ _ _ _ _ _ _ _ _ call segment Hrunning) Hnonidle).
      + eapply sem_pend_mutex_post_preserves_unregistered; [|exact Hold|exact Hclear].
        exact (proj2 (PostComponent.mutex_post_critical_segment_source _ _ _ _ _ _ _ _ _ _ segment)). }
  2: { intros pend_environment pend_critical local frame pend_call before_heap after_heap
      segment [Hrunning [Hnonidle [old [Hold Hclear]]]].
    split.
    - rewrite (SelectedCriticalControl.mutex_pend_inheritance_c_segment_running _ _ _ _ _ _ _ _ segment).
      exact Hrunning.
    - split.
      + exact (proj2 (SelectedMutexIdle.mutex_pend_inheritance_c_segment_idle_non_idle
          _ _ _ _ _ _ _ _ call segment Hrunning) Hnonidle).
      + eapply sem_pend_source_projection_preserves_unregistered; [|exact Hold|exact Hclear].
        intros slot previous Hprevious; eapply sem_pend_mutex_inheritance_c_projection;
          [exact (PendComponent.mutex_pend_inheritance_segment_source _ _ _ _ _ _ _ _ segment)|exact Hprevious]. }
  2: { intros suspend_environment suspend_critical saved_local caller saved suspend_call frame before_heap after_heap
      completion [Hrunning [Hnonidle [old [Hold Hclear]]]].
    pose proof (TaskSuspendMaskedC.TaskSuspendMaskedCStep suspend_environment suspend_critical sg
      saved_local caller saved suspend_call frame before_heap after_heap completion) as Hstep.
    split.
    - rewrite (proj1 (TaskSuspendMaskedC.task_suspend_masked_c_step_control_fields _ _ _ _ _ _ _ _ _ _ Hstep));
        exact Hrunning.
    - split.
      + exact (proj2 (TaskSuspendMaskedC.task_suspend_masked_c_step_idle_non_idle
          _ _ _ call _ _ _ _ _ _ _ Hstep) Hnonidle).
      + destruct completion as [[Hread Hcode] Hinput Houtput].
        eapply sem_pend_source_projection_preserves_unregistered; [|exact Hold|exact Hclear].
        intros slot previous Hprevious; eapply sem_pend_suspend_step_projection; eassumption. }
  2: { intros install_environment local frame install_call before_heap after_heap sp Hactual
      segment [Hrunning [Hnonidle [old [Hold Hclear]]]].
    pose proof (InstallComponent.TaskInstallCStep install_environment local sg frame install_call
      before_heap after_heap sp Hactual segment) as Hstep.
    destruct segment as [Hsource Hcompletion].
    destruct (os_sched_install_client_state_frame _ _ _ _ _ sg _ _ Hsource)
      as [Hnodes [Hlife [Hevents [Hrun Hrest]]]].
    split; [rewrite Hrun; exact Hrunning|]. split.
    - exact (proj2 (SelectedIdleFrames.task_install_c_step_idle_non_idle
        _ _ _ call _ _ _ _ _ _ _ Hstep) Hnonidle).
    - exists old; split; [rewrite Hnodes; exact Hold|exact Hclear]. }
  2: { intros capture body_heap restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
      source Hsg Hstop Hactive Hactive_after Hvalid0 [Hrunning [Hnonidle [old [Hold Hclear]]]].
    pose proof (sem_pend_delete_call_run None _ _ _ _ _ _ _ _ _ _ source) as Hrun.
    rewrite (proj1 Htask) in Hactive, Hactive_after.
    split.
    - rewrite (sem_pend_delete_capture_body_running None _ _ _ _ _ _ _ _ _ _ source); exact Hrunning.
    - split.
      + rewrite <- Hsg in *.
        eapply sem_pend_program_sequence_preserves_non_idle;
          [exact Hrun|exact Hrunning|eapply task_observer_lifetime_from_active;
            [exact (proj1 (proj2 Hvalid0))|exact Hactive]|
            exact Hactive_after|exact Hnonidle].
      + eapply sem_pend_program_sequence_preserves_unregistered;
          [exact Hrun|eapply task_observer_lifetime_from_active;
            [exact (proj1 (proj2 Hvalid0))|exact Hactive]|exact Hactive_after|
            exact Hold|exact Hclear]. }
  intros action initial final Hmember Hvalid0 Hstep Hreceipt [Hrunning [Hnonidle [old [Hold Hclear]]]].
  pose proof (kernel_client_preserves_validity action
    (critical.(critical_region_client_certificates) action Hmember) sg initial final Hvalid0 Hstep) as Hvalid1.
  pose proof (tmr_task_source_call_receipt_source _ _ _ _ _ Hreceipt) as Hclassification.
  split.
  - rewrite (tmr_task_source_client_running_eq _ _ _ _ _ Hvalid0 Hclassification Hstep); exact Hrunning.
  - split.
    + apply (proj2 (tmr_task_source_client_preserves_idle_non_idle _ _ _ _ _ _
        Hvalid0 Hvalid1 Hrunning Hclassification Hstep)); exact Hnonidle.
    + eapply sem_pend_source_call_receipt_preserves_unregistered; eassumption.
Qed.

Lemma sem_pend_client_return_source_waiter_projection :
  forall environment critical sg call before returned after old eid generation,
  sem_pend_client_return_source environment critical sg call before returned after ->
  UCOS2_state_inv sg before ->
  kernel_call_task_source call before -> kernel_call_task_source returned after ->
  before.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some old ->
  sem_pend_wait_continuation eid generation old ->
  sem_pend_task_projection before.(TskState) after.(TskState) call.(os_sched_call_stack).(stackLeaseSlot) old.
Proof.
intros environment critical sg call before returned after old eid generation [Htrace Hnormal]
  Hvalid Htask Hreturned Hold Hwait.
  destruct Htask as [Horigin [Hactive Hcurrent]].
  rewrite Horigin in Hactive.
  destruct (proj2 (proj2 Hactive)) as [initial_node [Hinitial Hgeneration]].
  assert (initial_node = old) by congruence; subst initial_node.
  assert (Hgeneration' : generation = call.(os_sched_call_stack).(stackLeaseGeneration)).
  { pose proof (proj1 Hwait); congruence. }
  subst generation.
  set (tid := call.(os_sched_call_stack).(stackLeaseSlot)) in *.
  clear Hnormal Hreturned Horigin Hcurrent Hinitial Hgeneration.
  remember false as stopped eqn:Hstop in Htrace.
  revert old Hvalid Hold Hwait Hactive Hstop.
  induction Htrace as [first before stopped last after trace Hcalls
    |action first before last after Hmember Htyped Hevent Hstep Hcontrol Hreceipt
    |irq_environment irq_critical first before before_heap input last after after_heap output Hexternal Hport Hclients Hcompletion
    |entry_environment first initial node handler suspended publication local frame before_heap saved_heap body_heap Hexternal Hport Hentry
    |post_environment post_critical source_env local frame post_call before_heap after_heap origin segment Hexternal Hport Hclients Hreceipt
    |pend_environment pend_critical local frame pend_call before_heap after_heap origin segment Hexternal Hport Hclients
    |suspend_environment suspend_critical saved_local caller saved suspend_call frame before_heap after_heap origin completion Hexternal Hport Hclients
    |install_environment local frame install_call before_heap after_heap sp Hactual segment Hexternal Hport
    |stored_origin capture body_heap restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
      source Hexternal Hport Hclients Hsg Hregistered
    |first before stopped1 middle transient stopped2 last after Hfirst IHfirst Hlast IHlast];
    intros old Hvalid Hold Hwait Hactive Hstop.
  - eapply sem_pend_client_source_calls_projection; eassumption.
  - eapply tmr_task_source_call_projection; eassumption.
  - pose proof (sem_pend_irq_cut_tasks _ _
      (sem_pend_irq_completion_source_frame _ _ _ _ _ _ _ _ _ _ _ Hcompletion)) as Htasks.
    exists old; split; [rewrite Htasks; exact Hold|apply rt_refl].
  - eapply sem_pend_irq_entry_waiter_projection; eassumption.
  - eapply sem_pend_mutex_post_receipt_projection; [exact Hreceipt|exact Hold|exact Hwait].
  - eapply sem_pend_mutex_inheritance_c_projection;
      [exact (PendComponent.mutex_pend_inheritance_segment_source _ _ _ _ _ _ _ _ segment)|exact Hold].
  - destruct completion as [[Hread Hstep] Hinput Houtput].
    eapply sem_pend_suspend_step_projection; eassumption.
  - eapply sem_pend_install_c_projection; [|exact Hold].
    exact (InstallComponent.TaskInstallCStep install_environment local sg frame install_call
      before_heap after_heap sp Hactual segment).
  - assert (Hactive_after : task_invocation_active (task_delete_capture_cut capture).(TskState)
      call.(os_sched_call_invocation) (RunningInvocation tid call.(os_sched_call_stack).(stackLeaseGeneration))).
    { assert (Hstored : RunningInvocation tid call.(os_sched_call_stack).(stackLeaseGeneration) = stored_origin).
      { pose proof (proj1 Hactive) as Hpast; congruence. }
      rewrite Hstored in *.
      eapply sem_pend_delete_capture_body_preserves_active; eassumption. }
    eapply sem_pend_delete_call_waiter_projection;
      [exact source|eapply task_observer_lifetime_from_active;
        [exact (proj1 (proj2 Hvalid))|exact Hactive]|exact Hactive_after|exact Hold|exact Hwait].
  - apply orb_false_iff in Hstop; destruct Hstop as [Hstop1 Hstop2].
    destruct (IHfirst old Hvalid Hold Hwait Hactive Hstop1) as [current [Hcurrent Hprojection]].
    assert (Hvalid' : UCOS2_state_inv sg transient).
    { exact (proj1 (sem_pend_observed_client_trace_resources _ _ _ _ _ _ _ _ _ _ _
        critical.(critical_region_client_certificates) Hfirst Hvalid)). }
    assert (Hactive' : task_invocation_active transient.(TskState) call.(os_sched_call_invocation)
      (RunningInvocation tid call.(os_sched_call_stack).(stackLeaseGeneration))).
    { eapply (proj2 (proj2 (proj2 (sem_pend_observed_client_trace_resources _ _ _ _ _ _ _ _ _ _ _
        critical.(critical_region_client_certificates) Hfirst Hvalid)))); eassumption. }
    destruct (IHlast current Hvalid' Hcurrent ltac:(eapply sem_pend_wait_trace_preserves_continuation; eassumption)
      Hactive' Hstop2)
      as [final [Hfinal Hlast_projection]].
    exists final; split; [exact Hfinal|eapply rt_trans; eassumption].
Qed.

(** Initialization is proved from each actual action and receipt. It
    does not require the stronger public image-presence frame. *)
Lemma sem_pend_client_source_calls_preserves_timer_initialized :
  forall external port clients sg observer event_observer first before stopped last after
    (trace : kernel_client_task_source_trace external port clients sg observer event_observer
      first before stopped last after),
  sem_pend_client_source_calls external port clients sg observer event_observer
    first before stopped last after trace ->
  timer_api_initialized before.(TimerState) -> timer_api_initialized after.(TimerState).
Proof.
  intros external port clients sg observer event_observer first before stopped last after trace Hcalls.
  induction Hcalls as [origin state|action first before middle transient last after stopped
    member foreign event_foreign step execution tail receipt Htail IH]; intro Hinitialized.
  - exact Hinitialized.
  - apply IH.
    exact (tmr_task_source_client_preserves_initialized external action sg
      (tmr_task_source_call_receipt_source _ _ _ _ _ receipt) before transient step Hinitialized).
Qed.

Lemma sem_pend_client_return_source_preserves_timer_initialized :
  forall environment critical sg call before returned after,
  sem_pend_client_return_source environment critical sg call before returned after ->
  timer_api_initialized before.(TimerState) -> timer_api_initialized after.(TimerState).
Proof.
intros environment critical sg call before returned after [Htrace Hnormal].
  clear Hnormal; induction Htrace as [first before stopped last after trace Hcalls
    |action first before last after Hmember Htyped Hevent Hstep Hcontrol Hreceipt
    |irq_environment irq_critical first before before_heap input last after after_heap output Hexternal Hport Hclients Hcompletion
    |entry_environment first initial node handler suspended publication local frame before_heap saved_heap body_heap Hexternal Hport Hentry
    |post_environment post_critical source_env local frame post_call before_heap after_heap origin segment Hexternal Hport Hclients Hreceipt
    |pend_environment pend_critical local frame pend_call before_heap after_heap origin segment Hexternal Hport Hclients
    |suspend_environment suspend_critical saved_local caller saved suspend_call frame before_heap after_heap origin completion Hexternal Hport Hclients
    |install_environment local frame install_call before_heap after_heap sp Hactual segment Hexternal Hport
    |stored_origin capture body_heap restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
      source Hexternal Hport Hclients Hsg Hregistered
    |first before stopped1 middle transient stopped2 last after Hfirst IHfirst Hlast IHlast]; intro Hinitialized.
  - eapply sem_pend_client_source_calls_preserves_timer_initialized; eassumption.
  - eapply tmr_task_source_client_preserves_initialized; [eapply tmr_task_source_call_receipt_source; eassumption|eassumption|exact Hinitialized].
  - rewrite (sem_pend_irq_cut_timers _ _
      (sem_pend_irq_completion_source_frame _ _ _ _ _ _ _ _ _ _ _ Hcompletion)); exact Hinitialized.
  - destruct (sem_pend_irq_entry_frames _ _ _ _ _ _ _ _ _ _ _ _ Hentry)
      as [Hlife [Hevents [Hnames [Htimers Hsched]]]].
    rewrite Htimers; exact Hinitialized.
  - pose proof (proj2 (PostComponent.mutex_post_critical_segment_source _ _ _ _ _ _ _ _ _ _ segment)) as Hcritical.
    rewrite <- (proj2 (mutex_post_critical_name_timer_fields _ _ _ _ _ _ _ Hcritical)); exact Hinitialized.
  - pose proof (proj2 (proj2 (PendComponent.mutex_pend_inheritance_segment_source _ _ _ _ _ _ _ _ segment))) as Hstep.
    rewrite (sem_pend_mutex_inheritance_timer_frame _ _ _ _ _ _ _ _ Hstep); exact Hinitialized.
  - destruct completion as [[Hread Hstep] Hinput Houtput].
    rewrite (proj2 (sem_pend_suspend_step_event_timer_fields _ _ _ _ _ _ _ Hstep)); exact Hinitialized.
  - destruct segment as [Hsource Hcompletion].
    destruct (os_sched_install_client_state_frame _ _ _ _ _ sg _ _ Hsource)
      as [Hnodes [Hlife [Hevents [Hrunning [Hinterrupt [Hnames Htimers]]]]]].
    rewrite Htimers; exact Hinitialized.
  - destruct (sem_pend_delete_call_frames None _ _ _ _ _ _ _ _ _ _ source)
      as [Htask [Hevent [Hname [Htimer Hsem]]]].
    eapply timer_public_storage_frame_initialized;
      [eapply timer_public_trace_public_storage_frame; exact Htimer|exact Hinitialized].
  - apply IHlast, IHfirst; exact Hinitialized.
Qed.

(** These factories consume the original module completion, including its
    input owner and actual transition. The resources are its exact output;
    no desired Sem phase or final owner is an input. Prefixes are composed
    separately on their original C-run certificate. *)
Lemma sem_pend_irq_wrapper_client_return : forall environment critical sg state local suspended receipt original node
  handler frame before after,
  SelectedIRQWrapperCompletion.irq_wrapper_c_completion environment sg state local suspended receipt original node
    handler frame before after ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  sem_pend_client_return_source environment critical sg original state
    (armv7a_continuation_resumed_call suspended original)
    (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) /\
  SelectedIRQWrapperCompletion.irq_wrapper_c_output environment sg state local suspended receipt original handler frame after.
Proof.
  intros until after; intros Hcompletion Horigin.
  assert (Hstack : original.(os_sched_call_stack) = suspended.(armv7a_continuation_stack)).
  { pose proof (SelectedIRQWrapperCompletion.irq_wrapper_c_binding _ _ _ _ _ _ _ _ _ _ _ _ Hcompletion)
      as [_ Hbinding].
    rewrite (SelectedIRQWrapperCompletion.irq_wrapper_c_saved_call _ _ _ _ _ _ _ _ _ _ _ _ Hcompletion)
      in Hbinding; exact Hbinding. }
  assert (Hreturned : (armv7a_continuation_resumed_call suspended original).(os_sched_call_origin) =
    RunningInvocation suspended.(armv7a_continuation_stack).(stackLeaseSlot)
      suspended.(armv7a_continuation_stack).(stackLeaseGeneration)).
  { cbn; rewrite Horigin, Hstack; reflexivity. }
  split.
  - split.
    + rewrite Hreturned. eapply SemPendObservedIRQ; try reflexivity.
      eapply SemPendIRQWrapperCompletion; exact Hcompletion.
    + eapply SelectedIRQWrapperCompletion.irq_wrapper_c_completion_normal_return; eassumption.
  - exact (proj2 (SelectedIRQWrapperCompletion.irq_wrapper_c_completion_resources _ _ _ _ _ _ _ _ _ _ _ _ Hcompletion)).
Qed.

Lemma sem_pend_irq_returned_client_return : forall environment critical sg observed read_heap observation_frame
  entry local suspended receipt original node handler frame before middle after,
  OSIntExitReturnedC.os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
    entry local suspended receipt original node handler frame before middle after ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  sem_pend_client_return_source environment critical sg original entry
    (armv7a_continuation_resumed_call suspended original)
    (os_int_exit_wrapper_restored_state (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
      suspended.(armv7a_continuation_stack)) /\
  SelectedIRQWrapperCompletion.irq_wrapper_c_output environment sg
    (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
    local suspended receipt original handler (unmap_table_rep sg ** frame) after.
Proof.
  intros until after; intros Hcompletion Horigin.
  pose proof (OSIntExitReturnedC.os_int_exit_returned_c_completion_wrapper
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcompletion) as Hwrapper.
  assert (Hstack : original.(os_sched_call_stack) = suspended.(armv7a_continuation_stack)).
  { pose proof (SelectedIRQWrapperCompletion.irq_wrapper_c_binding _ _ _ _ _ _ _ _ _ _ _ _ Hwrapper)
      as [_ Hbinding].
    rewrite (SelectedIRQWrapperCompletion.irq_wrapper_c_saved_call _ _ _ _ _ _ _ _ _ _ _ _ Hwrapper)
      in Hbinding; exact Hbinding. }
  assert (Hreturned : (armv7a_continuation_resumed_call suspended original).(os_sched_call_origin) =
    RunningInvocation suspended.(armv7a_continuation_stack).(stackLeaseSlot)
      suspended.(armv7a_continuation_stack).(stackLeaseGeneration)).
  { cbn; rewrite Horigin, Hstack; reflexivity. }
  split.
  - split.
    + rewrite Hreturned. eapply SemPendObservedIRQ; try reflexivity.
      eapply SemPendIRQReturnedCompletion; exact Hcompletion.
    + eapply SelectedIRQWrapperCompletion.irq_wrapper_c_completion_normal_return;
        [exact Hwrapper|exact Horigin].
  - exact (proj2 (OSIntExitReturnedC.os_int_exit_returned_c_completion_resources
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcompletion)).
Qed.

(** Consume the original C run and its leaf certificate. The original
    C resource theorem supplies its output on the same heap. Coverage of
    each original leaf remains a producer obligation; the theorem does
    not assert that every old leaf has a certificate. *)
Lemma sem_pend_client_return_source_from_c_sequence : forall environment critical sg call
  (leaf : forall state before input stopped returned after output,
    kernel_program_c_step environment critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin)
      state before input stopped returned after output ->
    TaskInvocationOrigin -> TaskInvocationOrigin -> Prop),
  (forall state before input stopped returned after output
    (step : kernel_program_c_step environment critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) state before input stopped returned after output) first last,
    leaf state before input stopped returned after output step first last ->
    exists trace : kernel_client_task_source_trace environment.(task_stack_call_external)
        environment.(task_stack_call_port) critical.(critical_region_clients) sg
        call.(os_sched_call_invocation) None first state stopped last returned,
      sem_pend_client_source_calls environment.(task_stack_call_external) environment.(task_stack_call_port)
        critical.(critical_region_clients) sg call.(os_sched_call_invocation) None
        first state stopped last returned trace) ->
  forall state before input current after output returned
    (run : kernel_c_sequence
      (kernel_program_c_step environment critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin))
      state before input false current after output),
  sem_pend_c_sequence_call_certificate
    (kernel_program_c_step environment critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin))
    leaf state before input false current after output run call.(os_sched_call_origin) returned.(os_sched_call_origin) ->
  kernel_call_normal_return call state returned current ->
  sem_pend_client_return_source environment critical sg call state returned current /\ output after.
Proof.
  intros environment critical sg call leaf Hleaf state before input current after output returned run Hcalls Hnormal.
  destruct (sem_pend_c_sequence_client_calls
    (kernel_program_c_step environment critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin))
    leaf environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg call.(os_sched_call_invocation) None Hleaf
    state before input false current after output run call.(os_sched_call_origin) returned.(os_sched_call_origin) Hcalls)
    as [trace Htrace].
  split; [eapply sem_pend_client_return_source_from_legacy; eassumption|].
  exact (proj2 (kernel_c_sequence_resources _
    (kernel_program_c_step_resources environment critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin))
    state before input false current after output run)).
Qed.
