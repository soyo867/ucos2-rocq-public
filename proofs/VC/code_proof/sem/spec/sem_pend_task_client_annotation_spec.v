Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_context Ucos2Verify.lib.task_retirement Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.sched Ucos2Verify.lib.event Ucos2Verify.lib.sem.
Require Import Ucos2Verify.lib.kernel_runtime_inv Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_idle_frames_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_critical_control_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_c_idle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_delete_call_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_delete_return_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_idle_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_masked_c_step_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_acquire_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_restore_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_program_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_multi_pointer_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_return_fields_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The original registered trace and its actual receipts are folded once.
    The observer remains fixed while the executing descriptor may change. *)
Lemma sem_pend_task_client_source_preserves_non_idle :
  forall external port critical sg observer event_observer first before stopped last after
    (trace : kernel_client_task_source_trace external port critical.(critical_region_clients)
      sg observer event_observer first before stopped last after),
  sem_pend_client_source_calls external port critical.(critical_region_clients)
    sg observer event_observer first before stopped last after trace ->
  forall call, UCOS2_state_inv sg before -> before.(SchedState).(isRunning) = true ->
  flag_pend_non_idle_at sg call before ->
  UCOS2_state_inv sg after /\ after.(SchedState).(isRunning) = true /\ flag_pend_non_idle_at sg call after.
Proof.
  intros external port critical sg observer event_observer first before stopped last after trace Hcalls.
  induction Hcalls as [origin state|action first before middle transient last after stopped
    Hin Hforeign Hevent Hstep Hsource Htail Hcall Hcalls IH]; intros call Hvalid Hrunning Hnonidle.
  - exact (conj Hvalid (conj Hrunning Hnonidle)).
  - pose proof (kernel_client_preserves_validity action
      (critical.(critical_region_client_certificates) action Hin) sg before transient Hvalid Hstep) as Hvalid'.
    pose proof (tmr_task_source_call_receipt_source _ _ _ _ _ Hcall) as Hclassification.
    apply (IH call Hvalid').
    + rewrite (tmr_task_source_client_running_eq external action sg before transient
        Hvalid Hclassification Hstep); exact Hrunning.
    + apply (proj2 (tmr_task_source_client_preserves_idle_non_idle external action sg call before transient
        Hvalid Hvalid' Hrunning Hclassification Hstep)); exact Hnonidle.
Qed.

(** This local body consequence uses the original two captured windows.
    Its final active premise must come from the same actual completion;
    it is not a claim that every pre-existing task survives TaskDelete. *)
Lemma sem_pend_task_client_delete_non_idle :
  forall event_observer stored_observer stored_origin capture after_heap restore_selected restore_rely
    save_selected save_rely restore_stopped save_stopped,
  sem_pend_delete_call_source event_observer stored_observer stored_origin capture after_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped ->
  forall observed,
    task_in_range
      capture.(DeleteComponent.delete_save_restore).(DeleteComponent.delete_restore_inputs).(DeleteComponent.delete_capture_globals)
      capture.(DeleteComponent.delete_save_restore).(DeleteComponent.delete_restore_inputs).(DeleteComponent.delete_capture_acquired).(TskState) ->
    capture.(DeleteComponent.delete_save_restore).(DeleteComponent.delete_restore_inputs).(DeleteComponent.delete_capture_acquired).(SchedState).(isRunning) = true ->
    task_invocation_active
      capture.(DeleteComponent.delete_save_restore).(DeleteComponent.delete_restore_inputs).(DeleteComponent.delete_capture_acquired).(TskState)
      observed.(os_sched_call_invocation)
      (RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot)
        observed.(os_sched_call_stack).(stackLeaseGeneration)) ->
    task_invocation_active (DeleteComponent.task_delete_capture_cut capture).(TskState)
      observed.(os_sched_call_invocation)
      (RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot)
        observed.(os_sched_call_stack).(stackLeaseGeneration)) ->
    flag_pend_non_idle_at
      capture.(DeleteComponent.delete_save_restore).(DeleteComponent.delete_restore_inputs).(DeleteComponent.delete_capture_globals) observed
      capture.(DeleteComponent.delete_save_restore).(DeleteComponent.delete_restore_inputs).(DeleteComponent.delete_capture_acquired) ->
    flag_pend_non_idle_at
      capture.(DeleteComponent.delete_save_restore).(DeleteComponent.delete_restore_inputs).(DeleteComponent.delete_capture_globals)
      observed (DeleteComponent.task_delete_capture_cut capture).
Proof.
  intros * Hsource observed Hrange Hrunning Hinitial Hactive Hnonidle.
  pose proof (sem_pend_delete_call_run event_observer _ _ _ _ _ _ _ _ _ _ Hsource) as Hrun.
  assert (Hselected : kernel_c_sequence_spec.kernel_c_sequence
    (SelectedCProgram.kernel_program_selected_c_step
      capture.(DeleteComponent.delete_save_restore).(DeleteComponent.delete_restore_inputs).(DeleteComponent.delete_capture_environment)
      capture.(DeleteComponent.delete_save_restore).(DeleteComponent.delete_restore_inputs).(DeleteComponent.delete_capture_critical)
      capture.(DeleteComponent.delete_save_restore).(DeleteComponent.delete_restore_inputs).(DeleteComponent.delete_capture_globals)
      stored_observer stored_origin)
    capture.(DeleteComponent.delete_save_restore).(DeleteComponent.delete_restore_inputs).(DeleteComponent.delete_capture_acquired)
    capture.(DeleteComponent.delete_save_restore).(DeleteComponent.delete_restore_before_heap)
    (DeleteComponent.task_delete_capture_before_owner
      capture.(DeleteComponent.delete_save_restore).(DeleteComponent.delete_restore_inputs))
    (DeleteComponent.task_delete_capture_observer_stopped capture stored_origin restore_stopped save_stopped)
    (DeleteComponent.task_delete_capture_cut capture) after_heap
    (DeleteComponent.task_delete_capture_recycled_owner capture)).
  { clear Hsource Hrange Hrunning Hinitial Hactive Hnonidle.
    induction Hrun.
    - constructor; exact H.
    - apply KernelCSequenceAtom; apply SelectedCProgram.kernel_program_selected_original_step; exact H.
    - eapply KernelCSequenceThen; eassumption.
    - eapply KernelCSequenceAdapt; eassumption. }
  eapply tmr_task_selected_c_sequence_preserves_non_idle;
    [exact Hselected|exact Hrunning| |exact Hactive|exact Hnonidle].
  eapply task_observer_lifetime_from_active; eassumption.
Qed.

Lemma sem_pend_task_client_return_preserves_non_idle :
  forall environment critical sg call before returned after observer,
  sem_pend_client_return_source environment critical sg call before returned after ->
  UCOS2_state_inv sg before -> before.(SchedState).(isRunning) = true ->
  kernel_call_task_source call before -> kernel_stack_call_same_call call observer ->
  flag_pend_non_idle_at sg observer before -> flag_pend_non_idle_at sg observer after.
Proof.
intros environment critical sg call before returned after observer [Htrace Hnormal]
  Hvalid Hrunning Htask Hsame Hnonidle.
  assert (Hboth : after.(SchedState).(isRunning) = true /\ flag_pend_non_idle_at sg observer after).
  { eapply sem_pend_observed_client_trace_preserves with
      (property := fun state => state.(SchedState).(isRunning) = true /\ flag_pend_non_idle_at sg observer state)
      (caller_origin := call.(os_sched_call_origin));
      [exact critical.(critical_region_client_certificates)| | | | | | | | |exact Htrace|reflexivity|
       exact (proj1 (proj2 Htask))|exact Hvalid|auto].
    - intros action initial final Hmember Hvalid0 Hstep Hreceipt [Hrunning0 Hnonidle0].
      pose proof (kernel_client_preserves_validity action
        (critical.(critical_region_client_certificates) action Hmember) sg initial final Hvalid0 Hstep) as Hvalid1.
      pose proof (tmr_task_source_call_receipt_source _ _ _ _ _ Hreceipt) as Hclassification.
      split.
      + rewrite (tmr_task_source_client_running_eq _ _ _ _ _ Hvalid0 Hclassification Hstep); exact Hrunning0.
      + exact (proj2 (tmr_task_source_client_preserves_idle_non_idle _ _ _ observer _ _
          Hvalid0 Hvalid1 Hrunning0 Hclassification Hstep) Hnonidle0).
    - intros initial final Hframe [Hrunning0 Hnonidle0].
      split.
      + rewrite (sem_pend_irq_cut_running _ _ Hframe); exact Hrunning0.
      + unfold flag_pend_non_idle_at in *; rewrite (sem_pend_irq_cut_tasks _ _ Hframe); exact Hnonidle0.
    - intros entry_environment entry_sg initial entry_node handler suspended publication
        entry_local frame before_heap saved_heap body_heap Hentry [Hrunning0 Hnonidle0].
      destruct (sem_pend_irq_entry_frames _ _ _ _ _ _ _ _ _ _ _ _ Hentry)
        as [_ [_ [_ [_ Hsched]]]].
      split; [rewrite Hsched; exact Hrunning0|].
      destruct Hnonidle0 as [old [Hold [Hg Hnonidle1]]].
      destruct (sem_pend_irq_entry_task_at _ _ _ _ _ _ _ _ _ _ _ _ Hentry
        observer.(os_sched_call_stack).(stackLeaseSlot) old Hold)
        as [current [Hlookup Hfields]].
      pose proof (f_equal taskGeneration Hfields) as Hg_eq.
      pose proof (f_equal curPrio Hfields) as Hprio_eq.
      change (current.(taskGeneration) = old.(taskGeneration)) in Hg_eq.
      change (current.(curPrio) = old.(curPrio)) in Hprio_eq.
      exists current; split; [exact Hlookup|]. rewrite Hg_eq, Hprio_eq; exact (conj Hg Hnonidle1).
    - intros post_environment post_critical source_env local frame post_call before_heap after_heap
        segment Hreceipt [Hrunning0 Hnonidle0].
      split.
      + rewrite (SelectedCriticalControl.mutex_post_critical_c_segment_running _ _ _ _ _ _ _ _ _ _ segment).
        exact Hrunning0.
      + exact (proj2 (SelectedMutexIdle.mutex_post_critical_c_segment_idle_non_idle
          _ _ _ _ _ _ _ _ _ _ observer segment Hrunning0) Hnonidle0).
    - intros pend_environment pend_critical local frame pend_call before_heap after_heap segment
        [Hrunning0 Hnonidle0].
      split.
      + rewrite (SelectedCriticalControl.mutex_pend_inheritance_c_segment_running _ _ _ _ _ _ _ _ segment).
        exact Hrunning0.
      + exact (proj2 (SelectedMutexIdle.mutex_pend_inheritance_c_segment_idle_non_idle
          _ _ _ _ _ _ _ _ observer segment Hrunning0) Hnonidle0).
    - intros suspend_environment suspend_critical saved_local caller saved suspend_call frame
        before_heap after_heap completion [Hrunning0 Hnonidle0].
      pose (step := @TaskSuspendMaskedC.TaskSuspendMaskedCStep suspend_environment suspend_critical sg
        saved_local caller saved suspend_call frame before_heap after_heap completion).
      split.
      + rewrite (proj1 (TaskSuspendMaskedC.task_suspend_masked_c_step_control_fields
          _ _ _ _ _ _ _ _ _ _ step)); exact Hrunning0.
      + exact (proj2 (TaskSuspendMaskedC.task_suspend_masked_c_step_idle_non_idle
          _ _ _ observer _ _ _ _ _ _ _ step) Hnonidle0).
    - intros install_environment local frame install_call before_heap after_heap sp Hactual segment
        [Hrunning0 Hnonidle0].
      pose (step := @InstallComponent.TaskInstallCStep install_environment local sg frame install_call
        before_heap after_heap sp Hactual segment).
      split.
      + change (install_call.(InstallComponent.task_install_fields_entry).(SchedState).(isRunning) = true).
        exact Hrunning0.
      + exact (proj2 (SelectedIdleFrames.task_install_c_step_idle_non_idle
          _ _ _ observer _ _ _ _ _ _ _ step) Hnonidle0).
    - intros capture body_heap restore_selected restore_rely save_selected save_rely
        restore_stopped save_stopped Hsource Hsg Hstop Hinitial Hactive Hvalid0
        [Hrunning0 Hnonidle0].
      split.
      + rewrite (sem_pend_delete_capture_body_running _ _ _ _ _ _ _ _ _ _ _ Hsource).
        exact Hrunning0.
      + rewrite <- Hsg.
        pose proof Hsame as [Hinvocation [_ Hstack]].
        eapply sem_pend_task_client_delete_non_idle;
          [exact Hsource| |exact Hrunning0| | |].
        * rewrite Hsg; exact (proj1 (proj2 Hvalid0)).
        * rewrite <- Hinvocation, <- Hstack, <- (proj1 Htask); exact Hinitial.
        * rewrite <- Hinvocation, <- Hstack, <- (proj1 Htask); exact Hactive.
        * rewrite Hsg; exact Hnonidle0. }
  exact (proj2 Hboth).
Qed.

Lemma sem_pend_task_client_stage_same_call : forall sg original returned state,
  kernel_stack_call_same_call returned original ->
  sem_pend_task_call_stage sg original state -> sem_pend_task_call_stage sg returned state.
Proof.
  intros sg original returned state Hsame [Hsource [Hrunning Hready]].
  split.
  - apply (proj2 (task_tcb_init_stack_same_call_source_iff returned original state Hsame)); exact Hsource.
  - split; [exact Hrunning|]. rewrite (proj2 (proj2 Hsame)); exact Hready.
Qed.

(** The initial zero belongs to the real Task caller. The new entry is on
    the exact returned descriptor from the Save source and observation. *)
Lemma sem_pend_task_client_acquire_entry : forall environment critical sg original returned pevent eid observed
  mask saved before acquired,
  UCOS2_state_inv sg before -> tmr_task_client_pend_entry sg original before ->
  sem_pend_client_return_source environment critical sg original before returned acquired ->
  sem_pend_client_phase_save_observation (SemPendAcquirePhase pevent eid observed)
    environment critical sg original returned mask saved before acquired ->
  tmr_task_client_pend_entry sg returned acquired /\
  (forall node, acquired.(TskState).(inUsedTaskStates)
    returned.(os_sched_call_stack).(stackLeaseSlot) = Some node -> node.(tcbEventMultiPtr) = 0) /\
  flag_pend_non_idle_at sg original acquired.
Proof.
  intros * Hvalid [Hinitial [Hidle [Havailable Hzero]]] Hsource
    [Hcontext [current [Hacquire [Hstage Hblocking]]]].
  pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hsource) as Hsame.
  pose proof Hinitial as [_ [_ [old [Hold [Hg Hrest]]]]].
  destruct (tmr_task_client_return_multi_zero environment critical sg original before returned acquired old
    Hsource Hvalid (proj1 Hinitial) (proj1 Hold) Hg (Hzero old (proj1 Hold)))
    as [node [Hnode [Hgen [Hpointer Hall]]]].
  split.
  - split; [eapply sem_pend_task_client_stage_same_call; eassumption|].
    exact (conj (proj1 (proj2 (proj2 (proj2 Hcontext))))
      (conj (proj1 (proj2 (proj2 (proj2 (proj2 Hcontext))))) Hall)).
  - split; [exact Hall|].
    destruct Hstage as [_ [_ [active [Hready [Hgeneration [Hnonidle Hnone]]]]]].
    exists active; exact (conj (proj1 Hready) (conj Hgeneration Hnonidle)).
Qed.

Lemma sem_pend_task_client_count_checkpoint : forall sg call entry eid current,
  UCOS2_state_inv sg entry -> tmr_task_client_pend_entry sg call entry ->
  mutex_query_lookup entry eid current -> current.(eventType) = OS_EVENT_TYPE_SEM ->
  0 < encode_event_cnt_value current ->
  UCOS2_state_inv sg (sem_count_update_state entry eid current (encode_event_cnt_value current - 1)) /\
  tmr_task_client_pend_entry sg call (sem_count_update_state entry eid current (encode_event_cnt_value current - 1)).
Proof.
  intros sg call entry eid current Hvalid [Hstage [Hidle [Havailable Hzero]]] Hlookup Htype Hpositive.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  specialize (Hpayload eid current Hlookup); unfold event_payload_consistency in Hpayload.
  rewrite Htype in Hpayload; destruct current.(semFields) as [fields|] eqn:Hfields; [|contradiction].
  assert (Hcount : encode_event_cnt_value current = fields.(semCount)).
  { unfold encode_event_cnt_value; rewrite Htype, Hfields; reflexivity. }
  assert (Hstep : sem_pend_first_critical sg eid 0 entry SemPendAcquired
    (sem_count_update_state entry eid current (encode_event_cnt_value current - 1))).
  { rewrite Hcount; eapply sem_pend_immediate_first_critical; eauto; lia. }
  destruct (sem_pend_client_immediate_checkpoint sg call entry eid current fields 0 _
    Hvalid Hstage Hidle Havailable Hlookup Htype Hfields Hstep) as [Hvalid' [_ [Hstage' [Hidle' Havailable']]]].
  exact (conj Hvalid' (conj Hstage' (conj Hidle' (conj Havailable' Hzero)))).
Qed.

Lemma sem_pend_task_client_wait_context : forall environment critical sg original returned mask saved
  before observed entry eid event tid old timeout,
  sem_pend_client_wait_origin environment critical sg original returned mask saved before observed
    entry eid event tid old ->
  sem_pend_client_phase_context sg returned entry -> flag_pend_non_idle_at sg original entry ->
  sem_pend_client_phase_context sg returned (event_pend_state sg entry eid event tid old PendSem timeout) /\
  flag_pend_non_idle_at sg original (event_pend_state sg entry eid event tid old PendSem timeout) /\
  tmr_task_multi_pointer_transport entry (event_pend_state sg entry eid event tid old PendSem timeout).
Proof.
  intros * Horigin [Hvalid [Hsource [Hrunning [Hidle [Havailable Hcache]]]]] Hnonidle.
  pose proof (proj1 (proj2 (proj1 Horigin))) as Hsame.
  assert (Havailable_original : kernel_call_stack_available original entry).
  { unfold kernel_call_stack_available in *; rewrite (proj1 (proj2 Hsame)) in Havailable; exact Havailable. }
  pose proof (sem_pend_client_phase_wait_restore_returned_pre environment critical sg original returned mask saved
    before observed entry eid event tid old timeout Horigin Hrunning Hidle Havailable_original) as [_ [Hcontext Hwait]].
  pose proof Horigin as [_ [[_ [_ [_ [Hold Hrest]]]] _]].
  split; [exact Hcontext|]. split.
  - eapply SelectedIdleFrames.task_used_priority_transport_non_idle; [|exact Hnonidle].
    change (SelectedIdleFrames.task_used_priority_transport entry.(TskState)
      (glob_task_set_usedtask entry.(TskState) tid (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)))).
    eapply SelectedIdleFrames.task_update_used_priority_transport; [exact Hold|reflexivity|reflexivity].
  - apply tmr_task_event_pend_multi_pointer_transport; exact Hold.
Qed.

Lemma sem_pend_task_client_resume_fields : forall sg original returned initial resumed tid old,
  tmr_task_client_pend_entry sg original initial ->
  tmr_task_multi_pointer_transport initial resumed -> kernel_stack_call_same_call returned original ->
  sem_pend_client_phase_context sg returned resumed -> flag_pend_non_idle_at sg original resumed ->
  resumed.(SchedState).(curTaskID) = Some tid -> resumed.(TskState).(inUsedTaskStates) tid = Some old ->
  old.(tcbEventMultiPtr) = 0 /\ old.(curPrio) <> sg.(osLowestPrio).
Proof.
  intros sg original returned initial resumed tid old [Hstage [Hidle [Havailable Hzero]]]
    Htransport Hsame [_ [Hsource Hrest]] [nonidle [Hnonidle [Hg Hp]]] Hcurrent Hold.
  destruct (kernel_call_task_source_current_at returned resumed Hsource) as [Hcurrent' Hnode].
  assert (Htid : tid = original.(os_sched_call_stack).(stackLeaseSlot)).
  { rewrite (proj2 (proj2 Hsame)) in Hcurrent'; congruence. }
  subst tid; assert (nonidle = old) by congruence; subst nonidle.
  split; [|exact Hp].
  destruct Hstage as [_ [_ [first [Hfirst Hfirstrest]]]].
  eapply tmr_task_multi_pointer_transport_slot_zero; [exact Htransport|exact (proj1 Hfirst)| |exact Hold].
  exact (Hzero first (proj1 Hfirst)).
Qed.

Lemma sem_pend_task_client_cleanup_without_timeout : forall environment critical sg context mask before observed
  eid timeout resumed tid old,
  sem_pend_client_resume_origin environment critical sg context mask before observed eid timeout resumed tid old ->
  old.(statPend) <> PendTimeout ->
  sem_pend_client_cleanup_origin environment critical sg context mask before observed eid timeout
    (encode_os_err_code (sem_pend_resume_error (encode_pend_status old.(statPend)))) resumed tid old.
Proof.
  intros * Horigin Hnotimeout.
  pose proof Horigin as [[Hvalid [Hcur [Hold [[Hmulti [Hflag Hregistration]] Hready]]]] Hhistory].
  split.
  - unfold sem_pend_cleanup_entry.
    split; [exact Hvalid|]; split; [exact Hcur|]; split; [exact Hold|].
    split; [destruct old.(statPend); assumption || contradiction|].
    split; [exact Hmulti|]; split; assumption.
  - exists resumed, old, (sem_pend_resume_error (encode_pend_status old.(statPend))).
    split; [exact Horigin|]; split; [reflexivity|].
    exists tid, old; split; [exact Hcur|]; split; [exact Hold|]; split; [reflexivity|].
    destruct old.(statPend); reflexivity || contradiction.
Qed.

Lemma sem_pend_task_client_cleanup_timeout : forall environment critical sg context mask before observed
  eid timeout resumed tid old current,
  sem_pend_client_resume_origin environment critical sg context mask before observed eid timeout resumed tid old ->
  old.(statPend) = PendTimeout -> mutex_query_lookup resumed eid current ->
  sem_pend_client_cleanup_origin environment critical sg context mask before observed eid timeout 10
    (event_task_remove_state resumed eid current tid old) tid (task_set_event_ptr old None).
Proof.
  intros * Horigin Htimeout He.
  pose proof Horigin as [[Hvalid [Hcur [Hold [[Hmulti [Hflag Hregistration]] Hready]]]] Hhistory].
  rewrite Htimeout in Hregistration.
  destruct (sem_pend_resume_timeout_event sg resumed eid tid old Hvalid Hold Hregistration)
    as [found [Hfound Hin]].
  assert (found = current) by congruence; subst found.
  split.
  - unfold sem_pend_cleanup_entry.
    split; [eapply UCOS2_event_task_remove_preserves_validity; eassumption|].
    split; [exact Hcur|]. split.
    + cbn [event_task_remove_state replace_TskS replace_EventS TskState glob_task_set_usedtask inUsedTaskStates].
      rewrite Z.eqb_refl; reflexivity.
    + split; [reflexivity|]; split; [exact Hmulti|]; split; assumption.
  - exists resumed, old, OS_ERR_TIMEOUT; split; [exact Horigin|]; split; [reflexivity|].
    exists tid, old; split; [exact Hcur|]; split; [exact Hold|].
    rewrite Htimeout; split; [reflexivity|]; exists current; auto.
Qed.

Lemma sem_pend_task_client_remove_context : forall sg call resumed eid event tid old,
  sem_pend_client_phase_context sg call resumed ->
  resumed.(TskState).(inUsedTaskStates) tid = Some old ->
  resumed.(EventState).(inUsedEventStates) eid = Some event -> In tid event.(waitList) ->
  sem_pend_client_phase_context sg call (event_task_remove_state resumed eid event tid old) /\
  tmr_task_multi_pointer_transport resumed (event_task_remove_state resumed eid event tid old) /\
  (flag_pend_non_idle_at sg call resumed -> flag_pend_non_idle_at sg call (event_task_remove_state resumed eid event tid old)).
Proof.
  intros sg call resumed eid event tid old [Hvalid [Hsource [Hrunning [Hidle [Havailable Hcache]]]]] Hold Hevent Hin.
  assert (Hpriority : SelectedIdleFrames.task_used_priority_transport resumed.(TskState)
    (event_task_remove_state resumed eid event tid old).(TskState)).
  { eapply SelectedIdleFrames.task_update_used_priority_transport; [exact Hold|reflexivity|reflexivity]. }
  split.
  - split; [eapply UCOS2_event_task_remove_preserves_validity; eassumption|]. split.
    + destruct Hsource as [Horigin [Hactive Hcurrent]].
      split; [exact Horigin|]. split; [|exact Hcurrent].
      eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hold|reflexivity|exact Hactive].
    + split; [exact Hrunning|]. split.
      * intros _; eapply SelectedIdleFrames.task_update_ready_preserves_idle_ready;
          [exact Hold|reflexivity|exact (fun H => H)|exact (Hidle Hrunning)].
      * split; [exact Havailable|].
        change (sched_current_consistency (event_task_remove_state resumed eid event tid old).(TskState) resumed.(SchedState)).
        unfold sched_current_consistency in *; destruct resumed.(SchedState).(curTaskID) as [current|] eqn:Hcurrent; [|exact Hcache].
        destruct Hcache as [node [Hnode Hp]].
        destruct (Hpriority current node Hnode) as [after [Hafter [Hg Hprio]]].
        exists after; split; [exact Hafter|rewrite Hprio; exact Hp].
  - split.
    + eapply tmr_task_update_multi_pointer_transport; [exact Hold|reflexivity|reflexivity|reflexivity].
    + eapply SelectedIdleFrames.task_used_priority_transport_non_idle; exact Hpriority.
Qed.

(** These are the three actual cleanup stores. The predecessor supplies
    its real fields, current cache and active invocation, not final stage. *)
Lemma sem_pend_task_client_cleanup_checkpoint : forall sg call cleaning tid node,
  sem_pend_cleanup_entry sg cleaning tid node -> sem_pend_client_phase_context sg call cleaning ->
  node.(curPrio) <> sg.(osLowestPrio) -> node.(tcbEventMultiPtr) = 0 ->
  UCOS2_state_inv sg (event_pend_cleanup_state sg false cleaning tid node) /\
  tmr_task_client_pend_entry sg call (event_pend_cleanup_state sg false cleaning tid node).
Proof.
  intros sg call cleaning tid node [Hvalid [Hcurrent [Hold [Hnone [Hmulti [Hflag Hmember]]]]]]
    [_ [Hsource [Hrunning [Hidle [Havailable Hcache]]]]] Hnonidle Hzero.
  assert (Hvalid' : UCOS2_state_inv sg (event_pend_cleanup_state sg false cleaning tid node)).
  { eapply UCOS2_event_pend_cleanup_preserves_validity; eassumption. }
  destruct (kernel_call_task_source_current_at call cleaning Hsource) as [Hcurrent' [found [Hfound Hg]]].
  assert (tid = call.(os_sched_call_stack).(stackLeaseSlot)) by congruence; subst tid.
  assert (found = node) by congruence; subst found.
  destruct Hsource as [Horigin [Hactive Hcontrol]].
  set (cleaned := task_event_pend_cleanup sg.(osKernelConfig).(cfgEventMultiEnabled) false node).
  assert (Hcleaned : (event_pend_cleanup_state sg false cleaning call.(os_sched_call_stack).(stackLeaseSlot) node).(TskState).(inUsedTaskStates)
    call.(os_sched_call_stack).(stackLeaseSlot) = Some cleaned).
  { cbn [event_pend_cleanup_state replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
    rewrite Z.eqb_refl; reflexivity. }
  assert (Heffective : is_effectively_ready node.(stat) node.(dly) = true).
  { destruct (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid)))) _ Hmember)
      as [ready_node [Hready_node [_ Heffective]]];
    assert (ready_node = node) by congruence; subst ready_node; exact Heffective. }
  assert (Hpriority : cleaning.(SchedState).(curSchedPrio) = Some node.(curPrio)).
  { unfold sched_current_consistency in Hcache; rewrite Hcurrent in Hcache.
    destruct Hcache as [cached [Hcached Hpriority]];
    assert (cached = node) by congruence; subst cached; exact Hpriority. }
  split; [exact Hvalid'|]. split.
  - split.
    + split; [exact Horigin|]. split; [|exact Hcontrol].
      eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hold| |exact Hactive].
      destruct sg.(osKernelConfig).(cfgEventMultiEnabled); reflexivity.
    + split; [exact Hrunning|]. exists cleaned; split.
      * unfold sched_current_ready_at; split; [exact Hcleaned|]. split; [exact Hcurrent|]. split.
        -- unfold cleaned, task_event_pend_cleanup; destruct sg.(osKernelConfig).(cfgEventMultiEnabled); exact Hpriority.
        -- split; [exact Hmember|]. apply task_event_pend_cleanup_preserves_ready; exact Heffective.
      * unfold cleaned, task_event_pend_cleanup; destruct sg.(osKernelConfig).(cfgEventMultiEnabled);
          repeat split; assumption || reflexivity.
  - split.
    + intros _; eapply task_update_non_idle_preserves_idle_ready; [exact Hold|exact Hnonidle|exact (Hidle Hrunning)].
    + split; [exact Havailable|]. intros current Hnode.
      assert (current = cleaned) by congruence; subst current.
      unfold cleaned, task_event_pend_cleanup; destruct sg.(osKernelConfig).(cfgEventMultiEnabled); assumption || reflexivity.
Qed.
