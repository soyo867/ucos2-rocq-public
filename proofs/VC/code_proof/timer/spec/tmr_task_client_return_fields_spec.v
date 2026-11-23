Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_multi_pointer_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_scan_unlock_entry_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_unlock_fields_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fresh_fields_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_source_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_restore_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.kernel_client_invariants Ucos2Verify.lib.kernel_runtime_inv.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sem.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_irq_completion_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_irq_entry_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_history_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_c_segment_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_masked_c_step_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_c_segment_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_delete_call_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_delete_return_source_spec.
Import TaskStateDef ListNotations DeleteComponent.
Local Open Scope Z_scope.

(** Decorate the SAME execution-origin trace with the actual input facts.
    The original registered membership supplies each validity certificate.
    This does not add a public Timer trace or replace any source proof. *)
Lemma tmr_task_client_source_local_receipt_from_valid :
  forall external port critical sg observer event_observer first before stopped last after
    (trace : kernel_client_task_source_trace external port critical.(critical_region_clients)
      sg observer event_observer first before stopped last after),
  sem_pend_client_source_calls external port critical.(critical_region_clients)
    sg observer event_observer first before stopped last after trace ->
  UCOS2_state_inv sg before ->
  sem_pend_client_source_local_receipt external port critical.(critical_region_clients)
    sg observer event_observer first before stopped last after trace.
Proof.
  intros external port critical sg observer event_observer first before stopped last after trace Hcalls.
  induction Hcalls; intro Hvalid; [constructor|].
  constructor; [assumption|apply sem_pend_source_state_facts_from_valid; exact Hvalid|].
  apply IHHcalls; eapply kernel_client_preserves_validity;
    [apply (critical_region_client_certificates critical); eassumption|exact Hvalid|eassumption].
Qed.

Lemma tmr_task_observed_caller_multi_pointer :
  forall external port critical sg observer event_observer first before stopped last after,
  sem_pend_observed_client_trace external port critical.(critical_region_clients) sg
    observer event_observer first before stopped last after ->
  stopped = false -> UCOS2_state_inv sg before ->
  forall tid generation old,
  task_invocation_active before.(TskState) observer (RunningInvocation tid generation) ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  exists current, after.(TskState).(inUsedTaskStates) tid = Some current /\
    current.(taskGeneration) = old.(taskGeneration) /\
    current.(tcbEventMultiPtr) = old.(tcbEventMultiPtr).
Proof.
  intros external port critical sg observer event_observer first before stopped last after Htrace.
  induction Htrace as [first before stopped last after trace Hcalls
    |action first before last after Hmember Htyped Hevent Hstep Hcontrol Hreceipt
    |irq_environment irq_critical first before before_heap input last after after_heap output
      Hexternal Hport Hclients Hcompletion
    |entry_environment first initial node handler suspended publication local frame
      entry_heap saved_heap body_heap Hexternal Hport Hentry
    |post_environment post_critical source_env post_local post_frame post_call
      before_heap after_heap post_origin Hsegment Hexternal Hport Hclients Hreceipt
    |inherit_environment inherit_critical inherit_local inherit_frame inherit_call
      before_heap after_heap inherit_origin Hsegment Hexternal Hport Hclients
    |suspend_environment suspend_critical suspend_local suspend_caller suspend_saved suspend_call
      suspend_frame before_heap after_heap suspend_origin Hcompletion Hexternal Hport Hclients
    |install_environment install_local install_frame install_call before_heap after_heap sp Hactual
      Hsegment Hexternal Hport
    |stored_origin capture body_heap restore_selected restore_rely save_selected save_rely
      restore_stopped save_stopped Hdelete_source Hexternal Hport Hclients Hsg Hregistered
    |first before stopped1 middle transient stopped2 last after Hfirst IHfirst Hlast IHlast];
    intros Hstop Hvalid tid generation old Hactive Hold.
  - assert (Htransport : tmr_task_multi_pointer_transport before after).
    { eapply tmr_task_client_source_multi_pointer_transport.
      eapply tmr_task_client_source_local_receipt_from_valid with (critical := critical); eassumption. }
    exact (Htransport tid old Hold).
  - pose proof (tmr_task_source_call_multi_pointer_transport _ _ _ _ _ Hreceipt
      (proj1 (proj2 (sem_pend_source_state_facts_from_valid _ _ Hvalid)))) as Htransport.
    exact (Htransport tid old Hold).
  - exists old; split.
    + rewrite (sem_pend_irq_cut_tasks _ _
        (sem_pend_irq_completion_source_frame _ _ _ _ _ _ _ _ _ _ _ Hcompletion)); exact Hold.
    + split; reflexivity.
  - destruct (sem_pend_irq_entry_task_at _ _ _ _ _ _ _ _ _ _ _ _ Hentry tid old Hold)
      as [current [Hcurrent Hfields]].
    exists current; split; [exact Hcurrent|].
    rewrite (sem_pend_saved_sp_fields_update old current Hfields); split; reflexivity.
  - pose proof (sem_pend_mutex_post_multi_pointer_transport _ _ _ _ _ _ _
      (proj2 (PostComponent.mutex_post_critical_segment_source source_env
      post_environment.(task_stack_call_external) post_environment.(task_stack_call_platform)
      post_critical post_local sg post_frame post_call before_heap after_heap Hsegment))) as Htransport.
    exact (Htransport tid old Hold).
  - pose proof (sem_pend_mutex_inheritance_c_multi_pointer_transport sg inherit_call
      (PendComponent.mutex_pend_inheritance_segment_source inherit_environment inherit_critical
        inherit_local sg inherit_frame inherit_call before_heap after_heap Hsegment)) as Htransport.
    exact (Htransport tid old Hold).
  - pose proof (TaskSuspendMaskedC.suspend_masked_source _ _ _ _ _ _ _ _ _ _ Hcompletion)
      as [_ Hcode].
    exact (sem_pend_suspend_step_multi_pointer_transport _ _ _ _ _ _ _ Hcode tid old Hold).
  - destruct Hsegment as [Hsource Hcompletion].
    destruct (os_sched_install_client_state_frame _ _ _ _ _ sg _ _ Hsource) as [Hmap _].
    exists old; split; [rewrite Hmap; exact Hold|]. split; reflexivity.
  - assert (Horigin : stored_origin = RunningInvocation tid generation).
    { pose proof (proj1 Hactive) as Hactual_registered; congruence. }
    subst stored_origin.
    eapply sem_pend_delete_call_multi_pointer.
    + exact Hdelete_source.
    + eapply task_observer_lifetime_from_active with (sg := sg);
        [exact (proj1 (proj2 Hvalid))|exact Hactive].
    + eapply sem_pend_delete_capture_body_preserves_active; eassumption.
    + exact Hold.
  - apply orb_false_iff in Hstop; destruct Hstop as [Hstop1 Hstop2].
    destruct (sem_pend_observed_client_trace_resources _ _ _ _ _ _ _ _ _ _ _
      critical.(critical_region_client_certificates) Hfirst Hvalid) as [Hvalid' [_ [_ Hlive]]].
    destruct (IHfirst Hstop1 Hvalid tid generation old Hactive Hold)
      as [middle_node [Hmiddle [Hgeneration Hpointer]]].
    destruct (IHlast Hstop2 Hvalid' tid generation middle_node
      (Hlive Hstop1 (RunningInvocation tid generation) Hactive) Hmiddle)
      as [current [Hcurrent [Hgeneration' Hpointer']]].
    exists current; split; [exact Hcurrent|]. split; congruence.
Qed.

(** The same old task incarnation survives at the actual returned lease.
    Its zero is an input observation, not a consequence of cfgMulti=false. *)
Lemma tmr_task_client_return_multi_zero :
  forall environment critical sg call before returned after old,
  sem_pend_client_return_source environment critical sg call before returned after ->
  UCOS2_state_inv sg before ->
  kernel_call_task_source call before ->
  before.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some old ->
  old.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  old.(tcbEventMultiPtr) = 0 ->
  exists current,
    after.(TskState).(inUsedTaskStates) returned.(os_sched_call_stack).(stackLeaseSlot) = Some current /\
    current.(taskGeneration) = returned.(os_sched_call_stack).(stackLeaseGeneration) /\
    current.(tcbEventMultiPtr) = 0 /\
    (forall node, after.(TskState).(inUsedTaskStates)
      returned.(os_sched_call_stack).(stackLeaseSlot) = Some node -> node.(tcbEventMultiPtr) = 0).
Proof.
  intros environment critical sg call before returned after old Hsource Hvalid Htask Hold Hgen Hzero.
  pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hsource) as [_ [_ Hstack]].
  destruct Hsource as [Htrace Hnormal].
  destruct Htask as [Horigin [Hactive Hcurrent_before]]; rewrite Horigin in Hactive.
  destruct (tmr_task_observed_caller_multi_pointer environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call.(os_sched_call_invocation) None
    call.(os_sched_call_origin) before false returned.(os_sched_call_origin) after
    Htrace eq_refl Hvalid call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) old Hactive Hold)
    as [current [Hcurrent [Hgeneration Hpointer]]].
  rewrite Hstack; exists current; split; [exact Hcurrent|].
  split; [congruence|]. split; [congruence|].
  intros node Hnode; assert (node = current) by congruence; subst node; congruence.
Qed.

Lemma tmr_task_multi_pointer_transport_slot_zero : forall before after slot old,
  tmr_task_multi_pointer_transport before after ->
  before.(TskState).(inUsedTaskStates) slot = Some old -> old.(tcbEventMultiPtr) = 0 ->
  forall node, after.(TskState).(inUsedTaskStates) slot = Some node -> node.(tcbEventMultiPtr) = 0.
Proof.
  intros before after slot old Htransport Hold Hzero node Hnode.
  destruct (Htransport slot old Hold) as [current [Hcurrent [Hgen Hpointer]]].
  assert (node = current) by congruence; subst node; congruence.
Qed.

(** The caller's three stores precede OS_EventTaskWait. This transient
    endpoint needs only the actual old lookup, not a stable ready Inv. *)
Lemma tmr_task_wait_prefix_multi_pointer_transport : forall before tid old kind timeout,
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  tmr_task_multi_pointer_transport before
    (replace_TskS (glob_task_set_usedtask before.(TskState) tid
      (task_prepare_event_wait old kind timeout)) before).
Proof.
  intros before tid old kind timeout Hold.
  eapply tmr_task_update_multi_pointer_transport; [exact Hold|reflexivity|reflexivity|reflexivity].
Qed.

Lemma tmr_task_event_wait_multi_pointer_transport : forall sg before eid event tid old,
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  tmr_task_multi_pointer_transport before (event_wait_state sg before eid event tid old).
Proof.
  intros sg before eid event tid old Hold.
  eapply tmr_task_update_multi_pointer_transport; [exact Hold|reflexivity|reflexivity|reflexivity].
Qed.

Lemma tmr_task_event_pend_multi_pointer_transport : forall sg before eid event tid old kind timeout,
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  tmr_task_multi_pointer_transport before (event_pend_state sg before eid event tid old kind timeout).
Proof.
  intros sg before eid event tid old kind timeout Hold.
  eapply tmr_task_update_multi_pointer_transport; [exact Hold|reflexivity|reflexivity|reflexivity].
Qed.

Lemma tmr_task_sem_count_multi_pointer_transport : forall before eid event count,
  tmr_task_multi_pointer_transport before (sem_count_update_state before eid event count).
Proof. intros; apply tmr_task_multi_pointer_transport_map_eq; reflexivity. Qed.

(** Both actual first-critical branches are retained: count decrement and
    waiter publication. This result says nothing about the later Scheduler. *)
Lemma tmr_task_pend_first_critical_multi_pointer_transport : forall sg eid timeout before result after,
  sem_pend_first_critical sg eid timeout before result after ->
  tmr_task_multi_pointer_transport before after.
Proof.
  intros sg eid timeout before result after [event [fields [Hevent [Hfields Hstep]]]].
  lazymatch type of Hstep with
  | if ?guard then _ else _ => destruct guard in Hstep
  end.
  - destruct Hstep as [Hresult ->]; apply tmr_task_sem_count_multi_pointer_transport.
  - destruct Hstep as [tid [old [Hcurrent [Hold [Hresult ->]]]]].
    apply tmr_task_event_pend_multi_pointer_transport; exact Hold.
Qed.

(** Success, abort and timeout use the same real cleanup endpoint. Enabled
    Multi writes zero; disabled Multi retains the old zero. The timeout's
    actual Event removal is included in sem_pend_resume_critical. *)
Lemma tmr_task_pend_cleanup_multi_pointer_transport : forall sg eid before tid old result after,
  before.(SchedState).(curTaskID) = Some tid ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  old.(tcbEventMultiPtr) = 0 -> sem_pend_resume_critical sg eid before result after ->
  tmr_task_multi_pointer_transport before after.
Proof.
  intros sg eid before tid old result after Hcurrent Hold Hzero Hcleanup.
  pose proof (proj1 (sem_pend_resume_critical_task_update sg eid before tid old result after
    Hcurrent Hold Hcleanup)) as Htasks.
  eapply tmr_task_update_multi_pointer_transport; [exact Hold|rewrite Htasks; reflexivity| |].
  - destruct sg.(osKernelConfig).(cfgEventMultiEnabled); reflexivity.
  - rewrite tmr_task_pend_cleanup_multi_value.
    destruct sg.(osKernelConfig).(cfgEventMultiEnabled); congruence.
Qed.

(** Consume the actual Restore source and its existing concrete readiness
    source. No final stage, final owner or future Pend success is assumed. *)
Lemma tmr_task_pend_restore_unlock_entry :
  forall environment critical sg call checkpoint returned current,
  UCOS2_state_inv sg checkpoint -> sem_pend_task_call_stage sg call checkpoint ->
  kernel_running_idle_ready sg checkpoint -> kernel_call_stack_available call checkpoint ->
  (forall node, checkpoint.(TskState).(inUsedTaskStates)
    call.(os_sched_call_stack).(stackLeaseSlot) = Some node -> node.(tcbEventMultiPtr) = 0) ->
  sem_pend_client_return_source environment critical sg call checkpoint returned current ->
  os_sched_task_ready_source environment sg returned current ->
  tmr_task_unlock_entry sg returned current.
Proof.
  intros environment critical sg call checkpoint returned current
    Hvalid Hstage Hidle Havailable Hzero Hreturn Hready.
  destruct (sem_pend_client_restore_from_ready_source environment critical sg call checkpoint call checkpoint
    returned current (kernel_call_normal_return_refl call checkpoint) Hreturn Hvalid Hstage Hidle Havailable Hready)
    as [Hnormal [Hstage' [Hidle' Havailable']]].
  pose proof Hstage as [_ [_ [old [Hold [Hgen Hrest]]]]].
  destruct (tmr_task_client_return_multi_zero environment critical sg call checkpoint returned current old
    Hreturn Hvalid (proj1 Hstage) (proj1 Hold) Hgen (Hzero old (proj1 Hold))) as [node [Hnode [Hg [Hp Hzeros]]]].
  eapply (tmr_task_pend_return_unlock_entry sg call checkpoint returned current); eassumption.
Qed.

Lemma tmr_task_pend_immediate_unlock_entry :
  forall environment critical sg call before eid event fields timeout checkpoint returned current,
  UCOS2_state_inv sg before -> sem_pend_task_call_stage sg call before ->
  kernel_running_idle_ready sg before -> kernel_call_stack_available call before ->
  (forall node, before.(TskState).(inUsedTaskStates)
    call.(os_sched_call_stack).(stackLeaseSlot) = Some node -> node.(tcbEventMultiPtr) = 0) ->
  before.(EventState).(inUsedEventStates) eid = Some event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
  event.(semFields) = Some fields -> sem_pend_first_critical sg eid timeout before SemPendAcquired checkpoint ->
  sem_pend_client_return_source environment critical sg call checkpoint returned current ->
  os_sched_task_ready_source environment sg returned current ->
  tmr_task_unlock_entry sg returned current.
Proof.
  intros environment critical sg call before eid event fields timeout checkpoint returned current
    Hvalid Hstage Hidle Havailable Hzero Hevent Htype Hfields Hstep Hreturn Hready.
  destruct (sem_pend_client_immediate_checkpoint sg call before eid event fields timeout checkpoint
    Hvalid Hstage Hidle Havailable Hevent Htype Hfields Hstep)
    as [Hvalid' [Hnormal [Hstage' [Hidle' Havailable']]]].
  eapply (tmr_task_pend_restore_unlock_entry environment critical sg call checkpoint returned current); try eassumption.
  pose proof Hstage as [_ [_ [old [Hold Hrest]]]].
  eapply tmr_task_multi_pointer_transport_slot_zero; [|exact (proj1 Hold)|apply Hzero; exact (proj1 Hold)].
  eapply tmr_task_pend_first_critical_multi_pointer_transport; exact Hstep.
Qed.

Lemma tmr_task_pend_cleanup_unlock_entry :
  forall environment critical sg call resumed eid old result checkpoint returned current,
  sem_pend_resume_entry sg resumed eid call.(os_sched_call_stack).(stackLeaseSlot) old ->
  kernel_call_task_source call resumed -> resumed.(SchedState).(isRunning) = true ->
  old.(curPrio) <> sg.(osLowestPrio) -> old.(tcbEventMultiPtr) = 0 ->
  sched_current_consistency resumed.(TskState) resumed.(SchedState) ->
  kernel_running_idle_ready sg resumed -> kernel_call_stack_available call resumed ->
  sem_pend_resume_critical sg eid resumed result checkpoint ->
  sem_pend_client_return_source environment critical sg call checkpoint returned current ->
  os_sched_task_ready_source environment sg returned current ->
  tmr_task_unlock_entry sg returned current.
Proof.
  intros environment critical sg call resumed eid old result checkpoint returned current
    Hentry Hsource Hrunning Hnonidle Hzero Hcache Hidle Havailable Hcleanup Hreturn Hready.
  destruct (sem_pend_client_cleanup_checkpoint sg call resumed eid old result checkpoint
    Hentry Hsource Hrunning Hnonidle Hcache Hidle Havailable Hcleanup)
    as [Hvalid' [Hnormal [Hstage' [Hidle' Havailable']]]].
  eapply (tmr_task_pend_restore_unlock_entry environment critical sg call checkpoint returned current); try eassumption.
  pose proof Hentry as [Hvalid [Hcurrent [Hold Hrest]]].
  eapply tmr_task_multi_pointer_transport_slot_zero; [|exact Hold|exact Hzero].
  eapply tmr_task_pend_cleanup_multi_pointer_transport; eassumption.
Qed.
