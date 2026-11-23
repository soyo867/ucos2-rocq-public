Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.interrupt Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.kernel_runtime_inv Ucos2Verify.lib.sem Ucos2Verify.lib.event.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_acquire_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_acquire_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_critical_control_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_c_segment_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_c_idle_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_api_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_masked_c_step_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_client_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_c_segment_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_delete_return_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations DeleteComponent.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The same registered source and receipts preserve Idle, running and
    the cached current priority. Ready membership is deliberately absent:
    the real Suspend critical cut can remove the current task before its
    subsequent scheduling/return. *)
Lemma sem_pend_client_source_calls_preserves_runtime :
  forall external port critical sg observer event_observer first before stopped last after
    (trace : kernel_client_task_source_trace external port critical.(critical_region_clients)
      sg observer event_observer first before stopped last after),
  sem_pend_client_source_calls external port critical.(critical_region_clients)
    sg observer event_observer first before stopped last after trace ->
  forall (call : OsSchedCallContext),
  UCOS2_state_inv sg before -> before.(SchedState).(isRunning) = true ->
  task_idle_ready sg before.(TskState) ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  UCOS2_state_inv sg after /\ after.(SchedState).(isRunning) = true /\
  task_idle_ready sg after.(TskState) /\
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros external port critical sg observer event_observer first before stopped last after trace Hcalls.
  induction Hcalls as [origin state|action first before middle transient last after stopped
    Hin Hforeign Hevent Hstep Hsource Htail Hcall Hcalls IH];
    intros call Hvalid Hrunning Hidle Hcurrent.
  - exact (conj Hvalid (conj Hrunning (conj Hidle Hcurrent))).
  - pose proof (kernel_client_preserves_validity action
      (critical.(critical_region_client_certificates) action Hin)
      sg before transient Hvalid Hstep) as Hvalid'.
    pose proof (tmr_task_source_call_receipt_source _ _ _ _ _ Hcall) as Hclassification.
    apply (IH call Hvalid').
    + rewrite (tmr_task_source_client_running_eq external action sg before transient
        Hvalid Hclassification Hstep); exact Hrunning.
    + apply (proj1 (tmr_task_source_client_preserves_idle_non_idle external action sg call before transient
        Hvalid Hvalid' Hrunning Hclassification Hstep)); exact Hidle.
    + exact (tmr_task_source_client_preserves_current_consistency external action sg before transient
        Hvalid Hclassification Hstep Hcurrent).
Qed.

Lemma sem_pend_client_return_source_preserves_runtime :
  forall environment critical sg call before returned after,
  sem_pend_client_return_source environment critical sg call before returned after ->
  UCOS2_state_inv sg before -> kernel_call_task_source call before ->
  before.(SchedState).(isRunning) = true ->
  kernel_running_idle_ready sg before ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  UCOS2_state_inv sg after /\ after.(SchedState).(isRunning) = true /\
  kernel_running_idle_ready sg after /\
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
intros environment critical sg call before returned after [Htrace Hnormal] Hvalid Htask Hrunning Hidle Hcurrent.
  pose proof (proj1 (sem_pend_observed_client_trace_resources _ _ _ _ _ _ _ _ _ _ _
    critical.(critical_region_client_certificates) Htrace Hvalid)) as Hvalid'.
  assert (Hruntime : after.(SchedState).(isRunning) = true /\ task_idle_ready sg after.(TskState)).
  { eapply sem_pend_observed_client_trace_preserves with
      (caller_origin := call.(os_sched_call_origin))
      (property := fun state => state.(SchedState).(isRunning) = true /\ task_idle_ready sg state.(TskState));
      [exact critical.(critical_region_client_certificates)| | | | | | | | |exact Htrace|reflexivity|
       exact (proj1 (proj2 Htask))|exact Hvalid|auto].
    - intros action initial final Hmember Hvalid0 Hstep Hreceipt [Hrunning0 Hidle0].
      pose proof (kernel_client_preserves_validity action
        (critical.(critical_region_client_certificates) action Hmember) sg initial final Hvalid0 Hstep) as Hvalid1.
      pose proof (tmr_task_source_call_receipt_source _ _ _ _ _ Hreceipt) as Hclassification.
      split.
      + rewrite (tmr_task_source_client_running_eq _ _ _ _ _ Hvalid0 Hclassification Hstep); exact Hrunning0.
      + exact (proj1 (tmr_task_source_client_preserves_idle_non_idle _ _ _ call _ _
          Hvalid0 Hvalid1 Hrunning0 Hclassification Hstep) Hidle0).
    - intros initial final Hframe [Hrunning0 Hidle0].
      destruct Hframe as [Htasks Hlifecycle Hevents Hnames Htimers Hrunning_cut Hcurrent_cut Hpriority_cut].
      split; [rewrite Hrunning_cut; exact Hrunning0|].
      unfold task_idle_ready in *; rewrite Htasks; exact Hidle0.
    - intros entry_environment entry_sg initial entry_node handler suspended publication
        entry_local frame before_heap saved_heap body_heap Hentry [Hrunning0 Hidle0].
      destruct (sem_pend_irq_entry_frames _ _ _ _ _ _ _ _ _ _ _ _ Hentry)
        as [_ [_ [_ [_ Hsched]]]].
      split; [rewrite Hsched; exact Hrunning0|].
      destruct Hidle0 as [idle [old [Hold [Hprio Hready]]]].
      destruct (sem_pend_irq_entry_task_at _ _ _ _ _ _ _ _ _ _ _ _ Hentry idle old Hold)
        as [current [Hlookup Hfields]].
      pose proof (f_equal curPrio Hfields) as Hprio_eq.
      pose proof (f_equal stat Hfields) as Hstat_eq.
      pose proof (f_equal dly Hfields) as Hdly_eq.
      change (current.(curPrio) = old.(curPrio)) in Hprio_eq.
      change (current.(stat) = old.(stat)) in Hstat_eq.
      change (current.(dly) = old.(dly)) in Hdly_eq.
      exists idle, current; split; [exact Hlookup|].
      rewrite Hprio_eq, Hstat_eq, Hdly_eq; exact (conj Hprio Hready).
    - intros post_environment post_critical source_env local frame post_call before_heap after_heap
        Hsegment Hreceipt [Hrunning0 Hidle0].
      split.
      + rewrite (SelectedCriticalControl.mutex_post_critical_c_segment_running _ _ _ _ _ _ _ _ _ _ Hsegment); exact Hrunning0.
      + exact (proj1 (SelectedMutexIdle.mutex_post_critical_c_segment_idle_non_idle
          _ _ _ _ _ _ _ _ _ _ call Hsegment Hrunning0) Hidle0).
    - intros inherit_environment inherit_critical local frame inherit_call before_heap after_heap
        Hsegment [Hrunning0 Hidle0].
      split.
      + rewrite (SelectedCriticalControl.mutex_pend_inheritance_c_segment_running _ _ _ _ _ _ _ _ Hsegment); exact Hrunning0.
      + exact (proj1 (SelectedMutexIdle.mutex_pend_inheritance_c_segment_idle_non_idle
          _ _ _ _ _ _ _ _ call Hsegment Hrunning0) Hidle0).
    - intros suspend_environment suspend_critical local caller saved suspend_call frame before_heap after_heap
        Hcompletion [Hrunning0 Hidle0].
      pose proof (@TaskSuspendMaskedC.TaskSuspendMaskedCStep suspend_environment suspend_critical sg
        local caller saved suspend_call frame before_heap after_heap Hcompletion) as Hstep.
      split.
      + rewrite (proj1 (TaskSuspendMaskedC.task_suspend_masked_c_step_control_fields
          _ _ _ _ _ _ _ _ _ _ Hstep)); exact Hrunning0.
      + exact (proj1 (TaskSuspendMaskedC.task_suspend_masked_c_step_idle_non_idle
          _ _ _ call _ _ _ _ _ _ _ Hstep) Hidle0).
    - intros install_environment local frame install_call before_heap after_heap sp Hactual
        Hsegment [Hrunning0 Hidle0].
      destruct Hsegment as [Hsource Hcompletion].
      destruct (os_sched_install_client_state_frame _ _ _ _ _ sg _ _ Hsource)
        as [Hmap [_ [_ [Hrunning_frame _]]]].
      split; [rewrite Hrunning_frame; exact Hrunning0|].
      unfold task_idle_ready in *; rewrite Hmap; exact Hidle0.
    - intros capture body_heap restore_selected restore_rely save_selected save_rely
        restore_stopped save_stopped Hsource Hsg Hstop Hinitial Hactive Hvalid0 [Hrunning0 Hidle0].
      split.
      + rewrite (sem_pend_delete_capture_body_running _ _ _ _ _ _ _ _ _ _ _ Hsource); exact Hrunning0.
      + rewrite <- Hsg; eapply sem_pend_delete_capture_body_idle; eassumption. }
  destruct Hruntime as [Hrunning' Hidle'].
  split; [exact Hvalid'|]. split; [exact Hrunning'|]. split; [intros _; exact Hidle'|].
  eapply kernel_call_task_source_observer_cache with (call := call).
  - eapply sem_pend_client_return_source_preserves_task_source;
      [exact (conj Htrace Hnormal)|exact Hvalid|exact Htask].
  - eapply sem_pend_observed_client_trace_preserves_observer_cache;
      [exact critical.(critical_region_client_certificates)|exact Htrace|reflexivity|
       exact (proj1 (proj2 Htask))|exact Hvalid|].
    apply sched_current_consistency_implies_observer_cache; exact Hcurrent.
Qed.

Definition sem_pend_client_task_return_observation sg original initial returned current : Prop :=
  kernel_call_normal_return original initial returned current /\
  sem_pend_task_call_stage sg returned current /\
  kernel_running_idle_ready sg current /\ kernel_call_stack_available returned current.

(** The readiness witness is the existing source relation with concrete
    nonswitch/selected-install constructors. It is tied to the same
    returned descriptor and state; no final Task stage or final owner is
    an input. Its real callsite producer remains mandatory. *)
Lemma sem_pend_client_restore_from_ready_source :
  forall environment critical sg original initial call checkpoint returned current,
  kernel_call_normal_return original initial call checkpoint ->
  sem_pend_client_return_source environment critical sg call checkpoint returned current ->
  UCOS2_state_inv sg checkpoint -> sem_pend_task_call_stage sg call checkpoint ->
  kernel_running_idle_ready sg checkpoint -> kernel_call_stack_available call checkpoint ->
  os_sched_task_ready_source environment sg returned current ->
  sem_pend_client_task_return_observation sg original initial returned current.
Proof.
  intros environment critical sg original initial call checkpoint returned current
    Hinitial Hreturn Hvalid Hstage Hidle Havailable Hready_source.
  pose proof Hstage as [Htask [Hrunning [old [Hready [Hg [Hnonidle Hnone]]]]]].
  assert (Hfields : sem_pend_source_call_fields sg call checkpoint).
  { split; [exact Hrunning|]. split.
    - exists old; split; [exact (proj1 Hready)|]. split; assumption.
    - exists old; split; [exact (proj1 Hready)|exact Hnone]. }
  destruct (sem_pend_client_return_source_preserves_call_fields environment critical sg call checkpoint returned
    current Hreturn Hvalid Htask Hfields)
    as [Hrunning' [[nonidle [Hnonidle_node [Hnonidle_gen Hnonidle']]] [node [Hnode Hnone']]]].
  destruct (sem_pend_client_return_source_preserves_runtime environment critical sg call checkpoint returned current
    Hreturn Hvalid Htask Hrunning Hidle (sched_current_ready_at_implies_current_consistency _ _ _ _ Hready))
    as [Hvalid' [Hrun Hidle_cache]].
  pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hreturn) as Hsame.
  pose proof (sem_pend_client_return_source_preserves_task_source _ _ _ _ _ _ _ Hreturn Hvalid Htask) as Htask'.
  pose proof (proj2 (task_tcb_init_stack_same_call_source_iff returned call current Hsame) Htask') as Hreturned_task.
  pose proof Hsame as [Hi [Ho Hstack]].
  destruct (os_sched_task_ready_source_current_ready environment sg returned current Hready_source)
    as [selected [Hselected Hselected_gen]].
  rewrite Hstack in Hselected, Hselected_gen.
  assert (nonidle = node) by congruence; subst nonidle.
  assert (selected = node) by (pose proof (proj1 Hselected); congruence); subst selected.
  destruct Hreturn as [Htrace Hnormal].
  unfold sem_pend_client_task_return_observation.
  split; [eapply kernel_call_normal_return_trans; eassumption|].
  split.
  - split; [exact Hreturned_task|]. split; [exact Hrunning'|].
    rewrite Hstack; exists node; exact (conj Hselected (conj Hselected_gen (conj Hnonidle' Hnone'))).
  - split; [exact (proj1 Hidle_cache)|exact (proj2 Hnormal Havailable)].
Qed.

(** A real enabled/no-switch comparison determines readiness from the
    current cache and the fresh selected priority. Idle supplies the
    nonempty ready list through the actual state invariant. *)
Lemma sem_pend_client_restore_nonswitch :
  forall environment critical sg original initial call checkpoint returned current,
  kernel_call_normal_return original initial call checkpoint ->
  sem_pend_client_return_source environment critical sg call checkpoint returned current ->
  UCOS2_state_inv sg checkpoint -> sem_pend_task_call_stage sg call checkpoint ->
  kernel_running_idle_ready sg checkpoint -> kernel_call_stack_available call checkpoint ->
  os_sched_selection_enabled current = true -> os_sched_requests_switch current = false ->
  sem_pend_client_task_return_observation sg original initial returned current.
Proof.
  intros environment critical sg original initial call checkpoint returned current
    Hinitial Hreturn Hvalid Hstage Hidle Havailable Henabled Hsameprio.
  pose proof Hstage as [Htask [Hrunning [node [Hready Hrest]]]].
  destruct (sem_pend_client_return_source_preserves_runtime environment critical sg call checkpoint returned current
    Hreturn Hvalid Htask Hrunning Hidle (sched_current_ready_at_implies_current_consistency _ _ _ _ Hready))
    as [Hvalid' [Hrunning' [Hidle' Hcache']]].
  pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hreturn) as Hsame.
  pose proof (sem_pend_client_return_source_preserves_task_source _ _ _ _ _ _ _ Hreturn Hvalid Htask) as Htask'.
  assert (Hreturned : kernel_call_task_source returned current).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff returned call current Hsame)); exact Htask'. }
  assert (Hnonempty : current.(SchedState).(readyList) <> []).
  { eapply sched_idle_ready_nonempty.
    - exact (proj1 (proj1 (proj2 (proj2 Hvalid')))).
    - exact (Hidle' Hrunning'). }
  eapply sem_pend_client_restore_from_ready_source; try eassumption.
  apply OsSchedTaskReadyNonswitch; assumption.
Qed.

Lemma sem_pend_client_restore_task_selected :
  forall environment critical sg original initial call checkpoint context outgoing hooked incoming resumed returned,
  kernel_call_normal_return original initial call checkpoint ->
  sem_pend_client_return_source environment critical sg call checkpoint returned
    (os_sched_install_context context outgoing incoming hooked) ->
  UCOS2_state_inv sg checkpoint -> sem_pend_task_call_stage sg call checkpoint ->
  kernel_running_idle_ready sg checkpoint -> kernel_call_stack_available call checkpoint ->
  UCOS2_state_inv sg hooked -> sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  os_sched_destination_binding environment.(task_stack_call_external) context outgoing hooked incoming resumed ->
  returned.(os_sched_call_stack) = incoming ->
  sem_pend_client_task_return_observation sg original initial returned
    (os_sched_install_context context outgoing incoming hooked).
Proof.
  intros; eapply sem_pend_client_restore_from_ready_source; try eassumption.
  eapply OsSchedTaskReadySelected; eassumption.
Qed.

Lemma sem_pend_client_restore_irq_selected :
  forall environment critical sg original initial call checkpoint transfer returned,
  kernel_call_normal_return original initial call checkpoint ->
  sem_pend_client_return_source environment critical sg call checkpoint returned (os_int_exit_installed_state transfer) ->
  UCOS2_state_inv sg checkpoint -> sem_pend_task_call_stage sg call checkpoint ->
  kernel_running_idle_ready sg checkpoint -> kernel_call_stack_available call checkpoint ->
  UCOS2_state_inv sg transfer.(os_int_exit_hooked_state) ->
  sched_high_ready_consistency transfer.(os_int_exit_hooked_state).(TskState)
    transfer.(os_int_exit_hooked_state).(SchedState) ->
  os_int_exit_destination_binding environment.(task_stack_call_external) transfer ->
  returned.(os_sched_call_stack) = transfer.(os_int_exit_incoming_stack) ->
  sem_pend_client_task_return_observation sg original initial returned (os_int_exit_installed_state transfer).
Proof.
  intros; eapply sem_pend_client_restore_from_ready_source; try eassumption.
  eapply OsSchedTaskReadyInterruptSelected; eassumption.
Qed.

(** Only the actual count decrement changes the state in the fast branch.
    The Task/Scheduler and parked-stack fields are literal frames. *)
Lemma sem_pend_client_immediate_checkpoint : forall sg call before eid event fields timeout checkpoint,
  UCOS2_state_inv sg before -> sem_pend_task_call_stage sg call before ->
  kernel_running_idle_ready sg before -> kernel_call_stack_available call before ->
  before.(EventState).(inUsedEventStates) eid = Some event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
  event.(semFields) = Some fields -> sem_pend_first_critical sg eid timeout before SemPendAcquired checkpoint ->
  UCOS2_state_inv sg checkpoint /\ sem_pend_client_task_return_observation sg call before call checkpoint.
Proof.
  intros sg call before eid event fields timeout checkpoint Hvalid Hstage Hidle Havailable Hevent Htype Hfields Hstep.
  pose proof (sem_pend_immediate_preserves_validity sg before eid event fields timeout checkpoint
    Hvalid Hevent Htype Hfields Hstep) as Hvalid'.
  destruct (sem_pend_immediate_count_update sg before eid event fields timeout checkpoint Hevent Hfields Hstep)
    as [Hpositive ->].
  split; [exact Hvalid'|]. unfold sem_pend_client_task_return_observation.
  split.
  - split; [unfold task_tcb_init_stack_same_call; auto|exact (fun H => H)].
  - exact (conj Hstage (conj Hidle Havailable)).
Qed.

(** The resume entry is the registered waiter selected by the actual
    Scheduler/second Save. Success, abort and timeout share this proof;
    the timeout's real Event removal is inside sem_pend_resume_critical. *)
Lemma sem_pend_client_cleanup_checkpoint : forall sg call resumed eid old result checkpoint,
  sem_pend_resume_entry sg resumed eid call.(os_sched_call_stack).(stackLeaseSlot) old ->
  kernel_call_task_source call resumed -> resumed.(SchedState).(isRunning) = true ->
  old.(curPrio) <> sg.(osLowestPrio) ->
  sched_current_consistency resumed.(TskState) resumed.(SchedState) ->
  kernel_running_idle_ready sg resumed -> kernel_call_stack_available call resumed ->
  sem_pend_resume_critical sg eid resumed result checkpoint ->
  UCOS2_state_inv sg checkpoint /\ sem_pend_client_task_return_observation sg call resumed call checkpoint.
Proof.
  intros sg call resumed eid old result checkpoint
    [Hvalid [Hcurrent [Hold [Hregistration Hmember]]]] Hsource Hrunning Hnonidle Hcache Hidle Havailable Hcleanup.
  pose proof (sem_pend_resume_critical_preserves_validity sg resumed eid _ old result checkpoint
    Hvalid Hcurrent Hold Hregistration Hmember Hcleanup) as Hvalid'.
  destruct (sem_pend_resume_critical_task_update sg eid resumed _ old result checkpoint Hcurrent Hold Hcleanup)
    as [Htasks Hscheduler].
  destruct (kernel_call_task_source_current_at call resumed Hsource) as [Hcurrent' [found [Hfound Hgeneration]]].
  assert (found = old) by congruence; subst found.
  destruct Hsource as [Horigin [Hactive Hcontrol]].
  pose proof (sem_pend_resume_critical_preserves_invocation sg eid resumed _ old result checkpoint
    call.(os_sched_call_invocation) call.(os_sched_call_origin) Hcurrent Hold Hcleanup Hactive) as Hactive'.
  pose proof Hregistration as [Hmulti [Hflag Hpointer]].
  assert (Heffective : is_effectively_ready old.(stat) old.(dly) = true).
  { destruct (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid)))) _ Hmember)
      as [ready_node [Hready_node [_ Heffective]]];
    assert (ready_node = old) by congruence; subst ready_node; exact Heffective. }
  assert (Hpriority : resumed.(SchedState).(curSchedPrio) = Some old.(curPrio)).
  { unfold sched_current_consistency in Hcache; rewrite Hcurrent in Hcache.
    destruct Hcache as [cached [Hcached Hpriority]];
    assert (cached = old) by congruence; subst cached; exact Hpriority. }
  set (cleaned := task_event_pend_cleanup sg.(osKernelConfig).(cfgEventMultiEnabled) false old).
  assert (Hcleaned : checkpoint.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some cleaned).
  { rewrite Htasks; cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity. }
  assert (Hstage : sem_pend_task_call_stage sg call checkpoint).
  { split.
    - split; [exact Horigin|]. split; [exact Hactive'|].
      unfold task_execution_current; rewrite Horigin, Hscheduler; exact Hcurrent.
    - split; [rewrite Hscheduler; exact Hrunning|]. exists cleaned; split.
      + unfold sched_current_ready_at; split; [exact Hcleaned|]. rewrite Hscheduler.
        split; [exact Hcurrent|]. split.
        * unfold cleaned, task_event_pend_cleanup; destruct sg.(osKernelConfig).(cfgEventMultiEnabled); exact Hpriority.
        * split; [exact Hmember|]. apply task_event_pend_cleanup_preserves_ready; exact Heffective.
      + unfold cleaned, task_event_pend_cleanup; destruct sg.(osKernelConfig).(cfgEventMultiEnabled);
          repeat split; assumption || reflexivity. }
  assert (Hnormal : kernel_call_normal_return call resumed call checkpoint).
  { split; [unfold task_tcb_init_stack_same_call; auto|].
    unfold kernel_call_stack_available; rewrite Horigin, Htasks; exact (fun H => H). }
  assert (Hidle' : kernel_running_idle_ready sg checkpoint).
  { intros _; rewrite Htasks.
    eapply task_update_non_idle_preserves_idle_ready; [exact Hold|exact Hnonidle|exact (Hidle Hrunning)]. }
  split; [exact Hvalid'|]. unfold sem_pend_client_task_return_observation.
  exact (conj Hnormal (conj Hstage (conj Hidle' (proj2 Hnormal Havailable)))).
Qed.

Lemma sem_pend_client_immediate_restore :
  forall environment critical sg call before eid event fields timeout checkpoint returned current,
  UCOS2_state_inv sg before -> sem_pend_task_call_stage sg call before ->
  kernel_running_idle_ready sg before -> kernel_call_stack_available call before ->
  before.(EventState).(inUsedEventStates) eid = Some event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
  event.(semFields) = Some fields -> sem_pend_first_critical sg eid timeout before SemPendAcquired checkpoint ->
  sem_pend_client_return_source environment critical sg call checkpoint returned current ->
  os_sched_task_ready_source environment sg returned current ->
  sem_pend_client_task_return_observation sg call before returned current.
Proof.
  intros environment critical sg call before eid event fields timeout checkpoint returned current
    Hvalid Hstage Hidle Havailable Hevent Htype Hfields Hstep Hreturn Hready.
  destruct (sem_pend_client_immediate_checkpoint sg call before eid event fields timeout checkpoint
    Hvalid Hstage Hidle Havailable Hevent Htype Hfields Hstep)
    as [Hvalid' [Hnormal [Hstage' [Hidle' Havailable']]]].
  eapply sem_pend_client_restore_from_ready_source; eassumption.
Qed.

Lemma sem_pend_client_cleanup_restore :
  forall environment critical sg call resumed eid old result checkpoint returned current,
  sem_pend_resume_entry sg resumed eid call.(os_sched_call_stack).(stackLeaseSlot) old ->
  kernel_call_task_source call resumed -> resumed.(SchedState).(isRunning) = true ->
  old.(curPrio) <> sg.(osLowestPrio) ->
  sched_current_consistency resumed.(TskState) resumed.(SchedState) ->
  kernel_running_idle_ready sg resumed -> kernel_call_stack_available call resumed ->
  sem_pend_resume_critical sg eid resumed result checkpoint ->
  sem_pend_client_return_source environment critical sg call checkpoint returned current ->
  os_sched_task_ready_source environment sg returned current ->
  sem_pend_client_task_return_observation sg call resumed returned current.
Proof.
  intros environment critical sg call resumed eid old result checkpoint returned current
    Hentry Hsource Hrunning Hnonidle Hcache Hidle Havailable Hcleanup Hreturn Hready.
  destruct (sem_pend_client_cleanup_checkpoint sg call resumed eid old result checkpoint
    Hentry Hsource Hrunning Hnonidle Hcache Hidle Havailable Hcleanup)
    as [Hvalid' [Hnormal [Hstage' [Hidle' Havailable']]]].
  eapply sem_pend_client_restore_from_ready_source; eassumption.
Qed.

(** This branch consumes two actual adjacent Restore transitions, so no
    foreign client is interposed. Its unchanged fields owner fixes the
    same checkpoint. It remains usable when scheduling is disabled and
    is not a claim that every public Restore follows an empty trace. *)
Lemma sem_pend_client_restore_uninterrupted :
  forall environment critical arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg original initial call checkpoint saved acquired cursor before written middle final_cursor after
    (frame : Assertion),
  kernel_call_normal_return original initial call checkpoint ->
  sem_pend_task_call_stage sg call checkpoint -> kernel_running_idle_ready sg checkpoint ->
  kernel_call_stack_available call checkpoint ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved acquired **
   os_sched_context_resources environment.(task_stack_call_external) call **
   (kernel_program_fields_inv sg checkpoint ** frame)) before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  sem_pend_client_return_source environment critical sg call checkpoint call checkpoint /\
  sem_pend_client_task_return_observation sg original initial call checkpoint /\
  (kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
     call (armv7a_irq_fiq_mask saved) ** (kernel_program_fields_inv sg checkpoint ** frame)) after.
Proof.
  intros environment critical arch restore sg original initial call checkpoint saved acquired cursor before
    written middle final_cursor after frame Hnormal Hstage Hidle Havailable Hr0 Hmask Hpre Hprefix Hsuffix.
  destruct (armv7a_restore_uninterrupted_transports_owned_execution environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch restore sg call saved acquired cursor before written middle
    final_cursor after (kernel_program_fields_inv sg checkpoint ** frame) Hr0 Hmask Hpre Hprefix Hsuffix)
    as [Hexecution [Hvalue [Hmemory Howned]]].
  split; [exact Hexecution|]. split; [exact Hvalue|]. split; [exact Hmemory|]. split.
  - split; [apply sem_pend_observed_client_trace_refl|apply kernel_call_normal_return_refl].
  - split; [exact (conj Hnormal (conj Hstage (conj Hidle Havailable)))|exact Howned].
Qed.
