Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Relations.Relation_Operators.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.task Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_status Ucos2Verify.lib.task_retirement.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_sw_hook_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec Ucos2Verify.VC.code.mutex.spec.mutex_post_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_api_spec.
Require Import Ucos2Verify.lib.sem.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_source_receipt_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_sem_source_projection_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_multi_pointer_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_legacy_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_c_segment_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_wake_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The original Mutex phase already supplies these concrete resources.
    Its non-sentinel guard is derived from the owned Task fields. *)
Lemma sem_pend_mutex_delete_phase_projection : forall (external : OsSchedExternalResources) sg eid entry prepared event mutex
  before after frame tid old waiting_event generation,
  mutex_del_parent_layout sg -> event_object_layout_prop sg eid ->
  mutex_del_parent_entry sg eid entry event mutex ->
  (kernel_program_inv sg entry ** frame) before ->
  sched_task_mutex_del_always_execution sg eid entry prepared before after ->
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation waiting_event generation old ->
  sem_pend_task_projection entry.(TskState)
    (mutex_del_always_checkpoint sg eid event prepared).(TskState) tid old /\
  (kernel_program_inv sg (mutex_del_always_checkpoint sg eid event prepared) ** frame) after.
Proof.
  intros external sg eid entry prepared event mutex before after frame tid old waiting_event generation
    Hlayout Hobject Hentry Hpre Hactual Hold Hcont.
  destruct (sched_task_mutex_del_always_source_resources external sg eid entry prepared event mutex
    before after frame Hlayout Hobject Hentry Hpre Hactual) as [_ [Hcritical Hpost]].
  pose proof Hpre as [owned [rest [Hjoin [Hprogram Hframe]]]].
  pose proof (proj1 (CriticalComponent.mutex_del_program_call_guard sg eid entry event mutex
    Hlayout Hentry owned Hprogram)) as Hguard.
  split; [|exact Hpost].
  eapply tmr_task_sem_mutex_delete_projection;
    [exact (proj1 Hentry)|exact Hguard|exact Hcritical|exact Hold|exact Hcont].
Qed.

(** The stop bit of a C tree belongs to its own stored observer origin.
    Lifetime TRANSPORT is also available for any other observed incarnation.
    This is the fact used to carry an actual final return backwards through
    a prefix whose internal origin is not the surrounding Sem caller. *)
Lemma sem_pend_program_c_step_lifetime_transport :
  forall environment critical sg stored_observer stored_origin state before input stopped current after output,
  kernel_program_c_step environment critical sg stored_observer stored_origin
    state before input stopped current after output ->
  forall observer origin,
    task_observer_lifetime_transport observer origin state.(TskState) current.(TskState).
Proof.
  intros environment critical sg stored_observer stored_origin state before input stopped current after output Hstep.
  destruct Hstep; intros observer origin.
  - eapply proj1; eapply CriticalComponent.kernel_critical_c_segment_observer_lifetime_result; eassumption.
  - eapply proj1; eapply BuiltinComponent.kernel_builtin_c_segment_lifetime_result; eassumption.
  - eapply proj1; eapply InstallComponent.task_install_c_step_observer_lifetime_result; eassumption.
  - eapply proj1; eapply WakeComponent.kernel_wake_c_segment_lifetime_result; eassumption.
  - eapply proj1; eapply StatusComponent.kernel_status_c_segment_lifetime_result; eassumption.
  - eapply proj1; eapply CreationComponent.kernel_task_creation_c_segment_lifetime_result; eassumption.
  - eapply proj1; eapply EventCreationComponent.kernel_event_creation_c_segment_lifetime_result; eassumption.
  - eapply proj1; eapply QueueCreationComponent.kernel_queue_creation_c_segment_lifetime_result; eassumption.
  - eapply proj1; eapply PendComponent.mutex_pend_inheritance_c_segment_lifetime_result; eassumption.
  - eapply proj1; eapply PostComponent.mutex_post_critical_c_segment_lifetime_result; eassumption.
  - eapply proj1; eapply DeleteComponent.task_delete_primitive_c_segment_observer_lifetime; eassumption.
  - eapply proj1; eapply PrimitiveComponent.flag_pend_task_primitive_c_step_observer_lifetime; eassumption.
  - destruct H as [inputs before_heap prepared_heap Hcontext Hcompletion|capture after_heap Hcontext Hcompletion].
    + destruct Hcompletion as [Hprep Hinput Houtput].
      eapply DeleteComponent.task_delete_preparation_observer_lifetime_transport; exact Hprep.
    + eapply proj1; apply DeleteComponent.task_delete_cut_observer_lifetime_result.
Qed.

Lemma sem_pend_return_c_step_lifetime_transport :
  forall environment critical sg stored_observer stored_origin state before input stopped current after output,
  SelectedReturnPrimitive.kernel_program_return_c_step environment critical sg stored_observer stored_origin
    state before input stopped current after output ->
  forall observer origin,
    task_observer_lifetime_transport observer origin state.(TskState) current.(TskState).
Proof.
  intros environment critical sg stored_observer stored_origin state before input stopped current after output Hstep.
  destruct Hstep; intros observer origin.
  - eapply sem_pend_program_c_step_lifetime_transport; eassumption.
  - destruct (SelectedReturnPrimitive.kernel_selected_return_c_step_state_stop _ _ _ _ _ _ _ _ H)
      as [-> Hstop]; apply task_observer_lifetime_transport_refl.
  - eapply proj1; eapply InstallComponent.task_install_c_segment_observer_lifetime_result; exact complete.
  - eapply proj1; eapply IRQSelectedCompletion.kernel_irq_selected_suffix_c_completion_lifetime; exact H.
Qed.

Lemma sem_pend_selected_c_step_lifetime_transport :
  forall environment critical sg stored_observer stored_origin state before input stopped current after output,
  SelectedCProgram.kernel_program_selected_c_step environment critical sg stored_observer stored_origin
    state before input stopped current after output ->
  forall observer origin,
    task_observer_lifetime_transport observer origin state.(TskState) current.(TskState).
Proof.
  intros environment critical sg stored_observer stored_origin state before input stopped current after output Hstep.
  destruct Hstep; intros observer origin.
  - eapply sem_pend_return_c_step_lifetime_transport; eassumption.
  - eapply proj1; eapply IRQAcquiredReturn.kernel_irq_acquired_return_c_step_lifetime; eassumption.
  - eapply proj1; eapply TaskSuspendMaskedC.task_suspend_masked_c_step_observer_lifetime; eassumption.
Qed.

Lemma sem_pend_selected_c_sequence_lifetime_transport :
  forall environment critical sg stored_observer stored_origin state before input stopped current after output,
  kernel_c_sequence
    (SelectedCProgram.kernel_program_selected_c_step environment critical sg stored_observer stored_origin)
    state before input stopped current after output ->
  forall observer origin,
    task_observer_lifetime_transport observer origin state.(TskState) current.(TskState).
Proof.
  intros environment critical sg stored_observer stored_origin state before input stopped current after output Hrun.
  induction Hrun; intros observer origin.
  - apply task_observer_lifetime_transport_refl.
  - eapply sem_pend_selected_c_step_lifetime_transport; eassumption.
  - eapply task_observer_lifetime_transport_trans; [apply IHHrun1|apply IHHrun2].
  - apply IHHrun.
Qed.

(** Prepare's literal writes clear pending/suspend, delay and event link.
    On an existing Sem continuation they have the observed effect of wake
    followed by resume.  The MultiPtr scalar is untouched by these writes. *)
Lemma sem_pend_delete_prepared_node_wait_trace : forall node eid generation,
  sem_pend_wait_continuation eid generation node ->
  clos_refl_trans TaskAbstractState sem_pend_wait_effect node (task_delete_prepared_node node).
Proof.
  intros node eid generation [Hg [Hm [Hflag Hphase]]].
  assert (Hclear : task_non_suspension_bits (task_clear_pending_status node.(stat) PendSem) = 0).
  { destruct Hphase as [[Hptr [Hpending|[Hpending Hrest]]]|[Hptr [Hpending Hresult]]].
    - apply task_clear_pending_status_same_kind; exact Hpending.
    - rewrite task_clear_pending_status_none by exact Hpending; exact Hpending.
    - rewrite task_clear_pending_status_none by exact Hpending; exact Hpending. }
  assert (Hresume : task_status_resume (task_clear_pending_status node.(stat) PendSem) = Byte.zero).
  { rewrite (task_status_single_of_mask (task_clear_pending_status node.(stat) PendSem) None Hclear).
    destruct (task_is_suspended (task_clear_pending_status node.(stat) PendSem)); reflexivity. }
  eapply rt_trans with (y := task_event_wake_single node PendSem 0 PendOK).
  - apply rt_step, SemPendWaitWake; discriminate.
  - eapply rt_trans with (y := task_resume (task_event_wake_single node PendSem 0 PendOK)).
    + apply rt_step, SemPendWaitResume.
    + apply rt_step, SemPendWaitOtherFields.
      unfold sem_pend_wait_fields_equal; repeat split; try reflexivity.
      * change (Byte.zero = task_status_resume (task_clear_pending_status node.(stat) PendSem));
          symmetry; exact Hresume.
      * change (0 = node.(tcbFlagNode)); symmetry; exact Hflag.
Qed.

Lemma sem_pend_delete_prepare_wait_projection : forall state selected node prepared loan tid old eid generation,
  state.(TskState).(inUsedTaskStates) selected = Some node ->
  task_delete_prepare_single_wait state selected node = Some (prepared, loan) ->
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  sem_pend_task_projection state.(TskState) prepared.(TskState) tid old.
Proof.
  intros state selected node prepared loan tid old eid generation Hselected Hprepare Hold Hcont.
  destruct (Z.eq_dec tid selected) as [->|Hdifferent].
  - assert (old = node) by congruence; subst old.
    exists (task_delete_prepared_node node); split.
    + exact (proj2 (task_delete_preparation_task_projections__release_and_recycle_resources
        state selected node prepared loan Hprepare)).
    + eapply sem_pend_delete_prepared_node_wait_trace; exact Hcont.
  - destruct (task_delete_prepare_single_wait_frame state selected node prepared loan Hprepare)
      as [next [Hstate Hfields]].
    exists old; split; [|apply rt_refl].
    rewrite Hstate; cbn [replace_FlagS replace_EventS replace_SchedS replace_TskS TskState
      glob_task_set_usedtask inUsedTaskStates].
    rewrite (proj2 (Z.eqb_neq tid selected) Hdifferent); exact Hold.
Qed.

Lemma sem_pend_delete_recycle_live_wait_projection : forall sg tasks deleted priority node name tid old,
  tasks.(inUsedTaskStates) tid = Some old ->
  (exists current, (task_recycle sg tasks deleted priority node name).(inUsedTaskStates) tid = Some current) ->
  sem_pend_task_projection tasks (task_recycle sg tasks deleted priority node name) tid old.
Proof.
  intros sg tasks deleted priority node name tid old Hold [actual Hactual].
  destruct (task_unlink_used_map_lookup_origin tasks.(inUsedTaskStates) deleted node tid actual Hactual)
    as [Hdifferent Hprevious].
  destruct (task_unlink_used_map_preserves_other_fields tasks.(inUsedTaskStates) deleted node tid old
    Hdifferent Hold) as [current [Hcurrent Hfields]].
  exists current; split; [exact Hcurrent|apply rt_step; apply tmr_task_sem_links_equal_wait_effect; exact Hfields].
Qed.

(** These are the two actual owners at the window's environment entries.
    The first comes from its literal Restore prefix; the second is that
    first interval's returned owner transported by the literal suffix. *)
Lemma sem_pend_delete_window_interval_owners :
  forall environment critical saved_local requested sg completed arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    phase loan first saved acquired released cursor initial_heap written prefix_heap
    middle between environment_heap final_cursor middle_heap frame,
  task_delete_c_environment environment critical saved_local requested sg completed ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (task_delete_call_masked environment critical saved_local phase loan
    sg first saved acquired released ** frame) initial_heap ->
  armv7a_restore_prefix_transition restore cursor initial_heap written prefix_heap ->
  completed.(task_delete_environment_execution) phase first released middle between
    prefix_heap environment_heap ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor middle_heap ->
  (task_delete_call_closed environment saved_local phase loan sg first
    (armv7a_irq_fiq_mask saved) released ** frame) prefix_heap /\
  (task_delete_call_closed environment saved_local phase loan sg middle
    (armv7a_irq_fiq_mask saved) between ** frame) middle_heap.
Proof.
  intros environment critical saved_local requested sg completed arch restore phase loan first saved
    acquired released cursor initial_heap written prefix_heap middle between environment_heap
    final_cursor middle_heap frame Henv Hr0 Hmask Hpre Hprefix Hactual Hsuffix.
  destruct (DeleteComponent.task_delete_restore_prefix_closed_resources environment critical sg
    saved_local arch restore phase loan first saved acquired released cursor initial_heap written
    prefix_heap frame Hr0 Hmask Hpre Hprefix) as [Hwritten Hclosed].
  split; [exact Hclosed|].
  destruct (task_delete_actual_environment_return environment critical saved_local requested sg completed
    phase loan first released middle between (armv7a_irq_fiq_mask saved) prefix_heap environment_heap
    frame Henv Hactual Hclosed) as [_ [_ [_ [_ Hmiddle]]]].
  assert (Hword : written.(kernel_restore_msr_word) = Some
    (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) saved)).
  { rewrite Hwritten; cbn [kernel_restore_write_cpsr kernel_restore_msr_word]; rewrite Hr0; reflexivity. }
  rewrite <- (armv7a_cpsr_restore_mask_eq cursor.(kernel_restore_current_cpsr) saved) in Hmiddle.
  pose proof (proj2 (DeleteComponent.task_delete_restore_suffix_closed_resources environment critical sg
    saved_local arch restore phase loan middle between _ written environment_heap final_cursor
    middle_heap frame Hword Hmiddle Hsuffix)) as Hfinal.
  rewrite armv7a_cpsr_restore_mask_eq in Hfinal; exact Hfinal.
Qed.

(** This annotation has the SAME original window constructor.  Its extra
    fields are its two real input owners and finite receipts for its two
    real completed intervals.  The two interval observers are unchanged. *)
Inductive sem_pend_delete_window_receipt environment critical sg :
  forall before before_heap after after_heap,
  sched_task_delete_window_execution environment critical sg before before_heap after after_heap -> Prop :=
| SemPendDeleteWindowReceipt :
  forall saved_local requested completed arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    original initial first acquired priority tid node prepared loan saved
    cursor initial_heap written prefix_heap middle between restore_environment_heap
    final_cursor middle_heap registers returned resumed save_environment_heap
    final_registers reacquired final_heap frame
    (Henv : task_delete_c_environment environment critical saved_local requested sg completed)
    (Hprep : task_delete_preparation_history sg requested original initial first acquired
      priority tid node prepared loan)
    (Hr0 : cursor.(kernel_restore_r0) = saved)
    (Hmask : armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192)
    (Hpre : (task_delete_call_masked environment critical saved_local
      (TaskDeletePrepared tid node.(taskGeneration)) loan
      sg first saved acquired (task_delete_locked prepared) ** frame) initial_heap)
    (Hprefix : armv7a_restore_prefix_transition restore cursor initial_heap written prefix_heap)
    (Hactual_restore : completed.(task_delete_environment_execution)
      (TaskDeletePrepared tid node.(taskGeneration)) first (task_delete_locked prepared)
      middle between prefix_heap restore_environment_heap)
    (Hsuffix_restore : armv7a_restore_suffix_transition restore written restore_environment_heap
      final_cursor middle_heap)
    (Hactual_save : completed.(task_delete_environment_execution)
      (TaskDeletePrepared tid node.(taskGeneration)) middle between
      returned resumed middle_heap save_environment_heap)
    (Hreturn : registers.(kernel_save_return_word) = None)
    (Hvalid : valid_os_cpu_sr registers.(kernel_save_cpsr))
    (Hsave_mask : armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved)
    (Hsuffix_save : armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) resumed
      save_environment_heap final_registers reacquired final_heap)
    (Hfirst_closed : (task_delete_call_closed environment saved_local
      (TaskDeletePrepared tid node.(taskGeneration)) loan sg first
      (armv7a_irq_fiq_mask saved) (task_delete_locked prepared) ** frame) prefix_heap)
    (Hmiddle_closed : (task_delete_call_closed environment saved_local
      (TaskDeletePrepared tid node.(taskGeneration)) loan sg middle
      (armv7a_irq_fiq_mask saved) between ** frame) middle_heap),
    sem_pend_delete_environment_receipt environment critical saved_local requested sg completed
      (TaskDeletePrepared tid node.(taskGeneration)) loan first (task_delete_locked prepared)
      middle between (armv7a_irq_fiq_mask saved) prefix_heap restore_environment_heap frame
      (conj Henv (conj Hactual_restore Hfirst_closed)) ->
    sem_pend_delete_environment_receipt environment critical saved_local requested sg completed
      (TaskDeletePrepared tid node.(taskGeneration)) loan middle between
      returned resumed (armv7a_irq_fiq_mask saved) middle_heap save_environment_heap frame
      (conj Henv (conj Hactual_save Hmiddle_closed)) ->
    sem_pend_delete_window_receipt environment critical sg _ _ _ _
      (@SchedTaskDeleteWindowExecution environment critical sg saved_local requested completed arch
        restore save original initial first acquired priority tid node prepared loan saved
        cursor initial_heap written prefix_heap middle between restore_environment_heap
        final_cursor middle_heap registers returned resumed save_environment_heap
        final_registers reacquired final_heap frame Henv Hprep Hr0 Hmask Hpre Hprefix
        Hactual_restore Hsuffix_restore Hactual_save Hreturn Hvalid Hsave_mask Hsuffix_save).

Lemma sem_pend_delete_window_receipt_projection :
  forall environment critical sg before before_heap after after_heap
    (window : sched_task_delete_window_execution environment critical sg before before_heap after after_heap),
  sem_pend_delete_window_receipt environment critical sg before before_heap after after_heap window ->
  forall tid old eid generation,
    before.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros environment critical sg before before_heap after after_heap window Hreceipt.
  destruct Hreceipt as [saved_local requested completed arch restore save original initial first acquired
    priority deleted node prepared loan saved cursor initial_heap written prefix_heap middle between
    restore_environment_heap final_cursor middle_heap registers returned resumed save_environment_heap
    final_registers reacquired final_heap frame Henv Hprep Hr0 Hmask Hpre Hprefix Hactual_restore
    Hsuffix_restore Hactual_save Hreturn Hvalid Hsave_mask Hsuffix_save Hfirst_closed Hmiddle_closed
    Hfirst_receipt Hmiddle_receipt].
  intros tid old eid generation Hold Hcont.
  destruct (sem_pend_delete_environment_receipt_projection environment critical saved_local requested sg
    completed (TaskDeletePrepared deleted node.(taskGeneration)) loan first (task_delete_locked prepared)
    middle between (armv7a_irq_fiq_mask saved) prefix_heap restore_environment_heap frame
    (conj Henv (conj Hactual_restore Hfirst_closed)) Hfirst_receipt tid old eid generation Hold Hcont)
    as [[current [Hcurrent Hfirst]] Howned].
  assert (Hcontinue : sem_pend_wait_continuation eid generation current).
  { eapply sem_pend_wait_trace_preserves_continuation; eassumption. }
  destruct (sem_pend_delete_environment_receipt_projection environment critical saved_local requested sg
    completed (TaskDeletePrepared deleted node.(taskGeneration)) loan middle between returned resumed
    (armv7a_irq_fiq_mask saved) middle_heap save_environment_heap frame
    (conj Henv (conj Hactual_save Hmiddle_closed)) Hmiddle_receipt tid current eid generation Hcurrent Hcontinue)
    as [[last [Hlast Hsecond]] Hfinal].
  exists last; split; [exact Hlast|eapply rt_trans; eassumption].
Qed.

Inductive sem_pend_sched_phase_step_receipt environment critical sg :
  forall before before_heap after after_heap,
  sched_task_phase_heap_step environment critical sg before before_heap after after_heap -> Prop :=
| SemPendSchedPhaseMutexDelete : forall eid entry prepared event mutex before_heap after_heap frame
    (Hlayout : mutex_del_parent_layout sg) (Hobject : event_object_layout_prop sg eid)
    (Hentry : mutex_del_parent_entry sg eid entry event mutex)
    (Hpre : (kernel_program_inv sg entry ** frame) before_heap)
    (Hactual : sched_task_mutex_del_always_execution sg eid entry prepared before_heap after_heap),
    sem_pend_sched_phase_step_receipt environment critical sg _ _ _ _
      (@SchedTaskPhaseHeapMutexDeleteAlways environment critical sg eid entry prepared event mutex
        before_heap after_heap frame Hlayout Hobject Hentry Hpre Hactual)
| SemPendSchedPhaseDeleteEnvironment : forall saved_local requested completed phase loan original
    before returned after mask before_heap after_heap frame
    (execution : sched_task_delete_environment_execution environment critical saved_local requested
      sg completed phase loan original before returned after mask before_heap after_heap frame),
    sem_pend_delete_environment_receipt environment critical saved_local requested sg completed phase loan
      original before returned after mask before_heap after_heap frame execution ->
    sem_pend_sched_phase_step_receipt environment critical sg _ _ _ _
      (@SchedTaskPhaseHeapDeleteEnvironment environment critical sg saved_local requested completed phase
        loan original before returned after mask before_heap after_heap frame execution)
| SemPendSchedPhaseDeleteWindow : forall before before_heap after after_heap
    (window : sched_task_delete_window_execution environment critical sg before before_heap after after_heap),
    sem_pend_delete_window_receipt environment critical sg before before_heap after after_heap window ->
    sem_pend_sched_phase_step_receipt environment critical sg _ _ _ _
      (@SchedTaskPhaseHeapDeleteWindow environment critical sg before before_heap after after_heap window).

Lemma sem_pend_sched_phase_step_projection :
  forall environment critical sg before before_heap after after_heap
    (step : sched_task_phase_heap_step environment critical sg before before_heap after after_heap),
  sem_pend_sched_phase_step_receipt environment critical sg before before_heap after after_heap step ->
  forall tid old eid generation,
    before.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros environment critical sg before before_heap after after_heap step Hreceipt.
  destruct Hreceipt; intros tid old waiting_event generation Hold Hcont.
  - exact (proj1 (sem_pend_mutex_delete_phase_projection environment.(task_stack_call_external)
      sg eid entry prepared event mutex before_heap after_heap frame tid old waiting_event generation
      Hlayout Hobject Hentry Hpre Hactual Hold Hcont)).
  - exact (proj1 (sem_pend_delete_environment_receipt_projection environment critical saved_local
      requested sg completed phase loan original before returned after mask before_heap after_heap
      frame execution H tid old waiting_event generation Hold Hcont)).
  - eapply sem_pend_delete_window_receipt_projection; eassumption.
Qed.

Inductive sem_pend_sched_phase_receipt environment critical sg :
  forall before before_heap after after_heap,
  sched_task_phase_heap_source environment critical sg before before_heap after after_heap -> Prop :=
| SemPendSchedPhaseReceiptRefl : forall state heap,
    sem_pend_sched_phase_receipt environment critical sg state heap state heap
      (@SchedTaskPhaseHeapSourceRefl environment critical sg state heap)
| SemPendSchedPhaseReceiptNext : forall before before_heap middle middle_heap after after_heap
    (step : sched_task_phase_heap_step environment critical sg before before_heap middle middle_heap)
    (tail : sched_task_phase_heap_source environment critical sg middle middle_heap after after_heap),
    sem_pend_sched_phase_step_receipt environment critical sg before before_heap middle middle_heap step ->
    sem_pend_sched_phase_receipt environment critical sg middle middle_heap after after_heap tail ->
    sem_pend_sched_phase_receipt environment critical sg before before_heap after after_heap
      (@SchedTaskPhaseHeapSourceNext environment critical sg before before_heap middle middle_heap
        after after_heap step tail).

Lemma sem_pend_sched_phase_projection :
  forall environment critical sg before before_heap after after_heap
    (source : sched_task_phase_heap_source environment critical sg before before_heap after after_heap),
  sem_pend_sched_phase_receipt environment critical sg before before_heap after after_heap source ->
  forall tid old eid generation,
    before.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros environment critical sg before before_heap after after_heap source Hreceipt.
  induction Hreceipt as [state heap|before before_heap middle middle_heap after after_heap step tail
    Hstep Htail IH]; intros tid old eid generation Hold Hcont.
  - apply sem_pend_task_projection_refl; exact Hold.
  - destruct (sem_pend_sched_phase_step_projection environment critical sg before before_heap middle
      middle_heap step Hstep tid old eid generation Hold Hcont) as [current [Hcurrent Hfirst]].
    assert (Hcontinue : sem_pend_wait_continuation eid generation current).
    { eapply sem_pend_wait_trace_preserves_continuation; eassumption. }
    destruct (IH tid current eid generation Hcurrent Hcontinue) as [last [Hlast Hsecond]].
    exists last; split; [exact Hlast|eapply rt_trans; eassumption].
Qed.

(** The annotation is on the original Wake proof.  Event callers provide
    their literal typed argument and Post/Abort result; the generic helper
    keeps its original wider byte domain.  No waiter is named here. *)
Inductive sem_pend_wake_c_receipt sg : forall state before input current after output,
  WakeComponent.kernel_wake_c_segment sg state before input current after output -> Prop :=
| SemPendWakeFlagReceipt : forall entry pointer waiter old bits result returned schedule checkpoint
    frame before after Hpre Hsource Hpost,
    task_flag_waiter_consistency sg entry.(TskState) entry.(FlagState) ->
    sem_pend_wake_c_receipt sg _ _ _ _ _ _
      (@WakeComponent.KernelWakeCFlagSegment sg entry pointer waiter old bits result returned schedule
        checkpoint frame before after Hpre Hsource Hpost)
| SemPendWakeEventReceipt : forall entry eid event slot old kind message result returned frame before after
    Hlookup Hentry Hpre Hpost,
    sem_pend_source_state_facts sg entry ->
    event_type_to_pend_type event.(eventType) = Some kind -> result <> PendTimeout ->
    sem_pend_wake_c_receipt sg _ _ _ _ _ _
      (@WakeComponent.KernelWakeCEventSegment sg entry eid event slot old kind message result returned
        frame before after Hlookup Hentry Hpre Hpost)
| SemPendWakeTickReceipt : forall entry slot old frame before after Hlookup Hpre Hpost,
    sem_pend_wake_c_receipt sg _ _ _ _ _ _
      (@WakeComponent.KernelWakeCTickSegment sg entry slot old frame before after Hlookup Hpre Hpost).

Lemma sem_pend_wake_c_receipt_projection :
  forall (external : OsSchedExternalResources) sg state before input current after output
    (segment : WakeComponent.kernel_wake_c_segment sg state before input current after output),
  sem_pend_wake_c_receipt sg state before input current after output segment ->
  forall tid old eid generation,
    state.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection state.(TskState) current.(TskState) tid old.
Proof.
  intros external sg state before input current after output segment Hreceipt.
  destruct Hreceipt; intros tid observed waiting_event generation Hold Hcont.
  - eapply sem_pend_flag_ready_call_projection; eassumption.
  - destruct (tmr_task_event_ready_c_post_receipt external None sg entry eid event slot old kind message
      result returned frame before after Hlookup H0 H1 Hpre Hpost) as [Hsegment Hcall].
    eapply sem_pend_source_call_local_projection; eassumption.
  - eapply sem_pend_tick_task_projection; eassumption.
Qed.

Lemma sem_pend_critical_c_source_projection : forall sg call,
  CriticalComponent.kernel_critical_c_source sg call ->
  forall tid old eid generation,
    (CriticalComponent.kernel_critical_c_entry call).(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection (CriticalComponent.kernel_critical_c_entry call).(TskState)
      (CriticalComponent.kernel_critical_c_returned call).(TskState) tid old.
Proof.
  intros sg [actual|actual] Hsource tid old eid generation Hold Hcont; cbn in Hsource, Hold |- *.
  - destruct Hsource as [error [Hcritical Hcode]].
    eapply tmr_task_sem_change_prio_projection; eassumption.
  - unfold CriticalComponent.mutex_del_critical_fields_observation in Hsource.
    destruct Hsource.
    + destruct H0 as [error [scheduled [Hcritical Hcode]]].
      eapply tmr_task_sem_mutex_delete_projection;
        [eapply sem_pend_mutex_delete_call_entry_valid; exact H|exact H|exact Hcritical|exact Hold|exact Hcont].
    + apply sem_pend_task_projection_refl; exact Hold.
Qed.

Lemma sem_pend_task_creation_c_source_projection : forall sg entry current,
  CreationComponent.kernel_task_creation_c_source sg entry current ->
  forall tid old, entry.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_task_projection entry.(TskState) current.(TskState) tid old.
Proof.
  intros sg entry current Hsource; destruct Hsource; intros tid old Hold;
    try (eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold]).
  - unfold task_create_critical in H; destruct (Z.ltb 0 entry.(IntrState).(intNesting)).
    + destruct H as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
    + destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority);
        destruct Hstep as [_ ->]; (eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold]).
  - destruct H2 as [_ ->]; eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
Qed.

Lemma sem_pend_status_c_source_projection : forall sg entry current,
  StatusComponent.kernel_status_c_source sg entry current ->
  forall tid old, entry.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_task_projection entry.(TskState) current.(TskState) tid old.
Proof.
  intros sg entry current Hsource; destruct Hsource; intros tid old Hold.
  - destruct H as [cid [running [_ [_ [_ Hstep]]]]].
    destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg priority running))).
    + destruct Hstep as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
    + destruct Hstep as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
    + destruct Hstep as [previous [Hprevious [_ ->]]].
      eapply sem_pend_updated_task_projection; [exact Hprevious|exact Hold|apply SemPendWaitSuspend].
  - destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority).
    + destruct Hstep as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
    + destruct Hstep as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
    + destruct Hstep as [previous [Hprevious Hstep]].
      destruct (task_is_suspended previous.(stat)); destruct Hstep as [_ ->].
      * eapply sem_pend_updated_task_projection; [exact Hprevious|exact Hold|apply SemPendWaitResume].
      * apply sem_pend_task_projection_refl; exact Hold.
  - destruct H as [event [fields [Hlookup [Htype [Hfields ->]]]]].
    destruct (Z.ltb 0 fields.(semCount)); (eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold]).
Qed.

Lemma sem_pend_delete_own_c_projection :
  forall environment critical sg stored_observer stored_origin state before input stopped current after output,
  DeleteComponent.task_delete_own_c_segment environment critical sg stored_observer stored_origin
    state before input stopped current after output ->
  forall tid old eid generation,
    state.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    (exists live, current.(TskState).(inUsedTaskStates) tid = Some live) ->
    sem_pend_task_projection state.(TskState) current.(TskState) tid old.
Proof.
  intros environment critical sg stored_observer stored_origin state before input stopped current after output Hstep.
  destruct Hstep as [inputs before_heap prepared_heap Hcontext Hcompletion|capture after_heap Hcontext Hcompletion];
    intros tid old eid generation Hold Hcont Hlive.
  - destruct Hcompletion as [[Hlive_history [Hprepare Hprotocol]] Hinput Houtput].
    destruct Hlive_history as [Hlookup [Hselected [Hnode Hpointer]]].
    change (sem_pend_task_projection inputs.(DeleteComponent.delete_capture_acquired).(TskState)
      inputs.(DeleteComponent.delete_capture_prepared).(TskState) tid old).
    eapply sem_pend_delete_prepare_wait_projection;
      [exact (proj2 (task_delete_table_lookup_live _ _ _ _ Hnode))|exact Hprepare|exact Hold|exact Hcont].
  - eapply sem_pend_delete_recycle_live_wait_projection; [exact Hold|exact Hlive].
Qed.

Lemma sem_pend_publication_c_projection : forall sg publication entry current tid old,
  task_in_range sg entry.(TskState) ->
  kernel_client_step (task_create_stack_publication_client publication) sg entry current ->
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection entry.(TskState) current.(TskState) tid old.
Proof.
  intros sg publication entry current tid old Htasks Hsource Hold.
  destruct (task_create_stack_publication_raw_projection sg publication entry current Hsource) as [Hraw ->].
  destruct (sem_pend_creation_call_projection _ sg entry _ tid old Htasks Hraw Hold)
    as [node [Hnode Htrace]].
  exists node; split; assumption.
Qed.

Lemma sem_pend_builtin_c_projection :
  forall environment critical local sg state before current after input output,
  BuiltinComponent.kernel_builtin_c_segment environment critical local sg state before current after input output ->
  forall tid old, state.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_task_projection state.(TskState) current.(TskState) tid old.
Proof.
  intros environment critical local sg state before current after input output Hsegment.
  destruct Hsegment; intros tid old Hold.
  - destruct operation; apply sem_pend_task_projection_refl; exact Hold.
  - destruct H as [Hinput Houtput].
    destruct Hinput as [owned [rest [Hjoin [[[Hvalid Hfacts] Hbody] Hframe]]]].
    eapply sem_pend_publication_c_projection; [exact (proj1 (proj2 Hvalid))|exact effect|exact Hold].
  - pose proof (BuiltinComponent.kernel_irq_transfer_c_completion_source environment critical sg
      handler saved entry transfer frame before after H) as Hsource.
    pose proof (proj1 (BuiltinComponent.os_int_exit_configured_transfer_state_frame environment
      sg handler entry transfer Hsource)) as Hnodes.
    eapply tmr_task_sem_projection_map_eq; [exact Hnodes|exact Hold].
Qed.

Lemma sem_pend_install_c_projection : forall environment local sg state before input stopped current after output,
  InstallComponent.task_install_c_step environment local sg state before input stopped current after output ->
  forall tid old, state.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_task_projection state.(TskState) current.(TskState) tid old.
Proof.
  intros environment local sg state before input stopped current after output Hstep.
  destruct Hstep as [frame call before_heap after_heap sp Hactual [Hsource Hcompletion]]; intros tid old Hold.
  pose proof (proj1 (os_sched_install_client_state_frame environment.(task_stack_call_external)
    call.(InstallComponent.task_install_fields_context) call.(InstallComponent.task_install_fields_outgoing)
    call.(InstallComponent.task_install_fields_incoming) call.(InstallComponent.task_install_fields_resumed)
    sg call.(InstallComponent.task_install_fields_entry) (InstallComponent.task_install_fields_current call) Hsource))
    as Hnodes.
  eapply tmr_task_sem_projection_map_eq; [exact Hnodes|exact Hold].
Qed.

Lemma sem_pend_mutex_inheritance_c_projection : forall sg call,
  PendComponent.mutex_pend_inheritance_c_source sg call ->
  forall tid old,
    call.(PendComponent.mutex_pend_inheritance_entry).(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_task_projection call.(PendComponent.mutex_pend_inheritance_entry).(TskState)
      call.(PendComponent.mutex_pend_inheritance_returned).(TskState) tid old.
Proof.
  intros sg call [Hselected [Hnonowner Hsource]] tid old Hold.
  unfold mutex_pend_inherit_step in Hsource.
  destruct (mutex_pend_inherit_action sg.(osPrioMutexCeilDis)
    call.(PendComponent.mutex_pend_inheritance_base) call.(PendComponent.mutex_pend_inheritance_node).(curPrio)
    call.(PendComponent.mutex_pend_inheritance_waiter) call.(PendComponent.mutex_pend_inheritance_ceiling)).
  - rewrite Hsource; apply sem_pend_task_projection_refl; exact Hold.
  - rewrite Hsource; apply sem_pend_task_projection_refl; exact Hold.
  - destruct Hsource as [events [Hevents ->]].
    change (sem_pend_task_projection call.(PendComponent.mutex_pend_inheritance_entry).(TskState)
      (glob_task_set_usedtask call.(PendComponent.mutex_pend_inheritance_entry).(TskState)
        call.(PendComponent.mutex_pend_inheritance_owner)
        (mutex_priority_task call.(PendComponent.mutex_pend_inheritance_node)
          call.(PendComponent.mutex_pend_inheritance_ceiling))) tid old).
    eapply sem_pend_mutex_priority_task_projection; eassumption.
Qed.

Lemma sem_pend_mutex_post_prepare_projection : forall sg mutex selected entry current tid old,
  mutex_post_prepare sg mutex selected entry current ->
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection entry.(TskState) current.(TskState) tid old.
Proof.
  intros sg mutex selected entry current tid old Hprepare Hold.
  unfold mutex_post_prepare in Hprepare; destruct Z.eq_dec.
  - subst current; apply sem_pend_task_projection_refl; exact Hold.
  - destruct Hprepare as [node [priority [Hnode [Hscan ->]]]].
    unfold mutex_post_owner_priority_state; destruct Z.eq_dec.
    + eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
    + change (sem_pend_task_projection entry.(TskState)
        (glob_task_set_usedtask entry.(TskState) selected (mutex_priority_task node priority)) tid old).
      eapply sem_pend_mutex_priority_task_projection; eassumption.
Qed.

(** The prepared state is an actual C cut before the nested EventReady.
    Only its current representation facts are retained, on the original
    handover constructor and original wake proof. *)
Inductive sem_pend_mutex_post_receipt sg event caller : forall entry result schedule current,
  mutex_post_critical sg event caller entry result schedule current -> Prop :=
| SemPendMutexPostNotOwnerReceipt : forall entry node mutex Hlookup Htype Hfields Howner,
    sem_pend_mutex_post_receipt sg event caller _ _ _ _
      (@mutex_post_not_owner sg event caller entry node mutex Hlookup Htype Hfields Howner)
| SemPendMutexPostEmptyReceipt : forall entry node mutex prepared Hlookup Htype Hfields Howner Hprepare Hempty,
    sem_pend_mutex_post_receipt sg event caller _ _ _ _
      (@mutex_post_empty sg event caller entry node mutex prepared Hlookup Htype Hfields Howner Hprepare Hempty)
| SemPendMutexPostHandoverReceipt : forall entry node mutex prepared priority woken found owner
    Hlookup Htype Hfields Howner Hprepare Hnonempty Hwake Hfound Htable,
    sem_pend_source_state_facts sg prepared ->
    sem_pend_mutex_post_receipt sg event caller _ _ _ _
      (@mutex_post_handover sg event caller entry node mutex prepared priority woken found owner
        Hlookup Htype Hfields Howner Hprepare Hnonempty Hwake Hfound Htable).

Lemma sem_pend_mutex_post_handover_c_receipt :
  forall sg event caller entry node mutex prepared priority woken found owner
    Hlookup Htype Hfields Howner Hprepare Hnonempty Hwake Hfound Htable,
  UCOS2_state_inv sg prepared ->
  sem_pend_mutex_post_receipt sg event caller _ _ _ _
    (@mutex_post_handover sg event caller entry node mutex prepared priority woken found owner
      Hlookup Htype Hfields Howner Hprepare Hnonempty Hwake Hfound Htable).
Proof. intros; constructor; apply sem_pend_source_state_facts_from_valid; assumption. Qed.

Lemma sem_pend_mutex_post_receipt_projection :
  forall sg event caller entry result schedule current
    (source : mutex_post_critical sg event caller entry result schedule current),
  sem_pend_mutex_post_receipt sg event caller entry result schedule current source ->
  forall tid old eid generation,
    entry.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection entry.(TskState) current.(TskState) tid old.
Proof.
  intros sg event caller entry result schedule current source Hreceipt.
  destruct Hreceipt; intros tid old eid generation Hold Hcont.
  - apply sem_pend_task_projection_refl; exact Hold.
  - change (sem_pend_task_projection entry.(TskState) prepared.(TskState) tid old).
    eapply sem_pend_mutex_post_prepare_projection; eassumption.
  - destruct (sem_pend_mutex_post_prepare_projection sg mutex caller entry prepared tid old Hprepare Hold)
      as [middle [Hmiddle Hfirst]].
    assert (Hcontinue : sem_pend_wait_continuation eid generation middle).
    { eapply sem_pend_wait_trace_preserves_continuation; eassumption. }
    assert (Hinput : tmr_task_sem_event_ready_call_input sg prepared event PendMutex PendOK).
    { destruct node.(waitList) as [|head tail] eqn:Hlist.
      - simpl in Hnonempty; contradiction.
      - exists node, head, tail; split.
        + rewrite (mutex_post_prepare_event_state_eq sg mutex caller entry prepared Hprepare); exact Hlookup.
        + split; [exact Hlist|]. split; [rewrite Htype; reflexivity|discriminate]. }
    destruct (sem_pend_event_ready_local_call_projection sg prepared woken None event PendMutex 0 PendOK
      tid middle eid generation H Hinput (ex_intro _ priority Hwake) Hmiddle Hcontinue)
      as [last [Hlast Hsecond]].
    exists last; split; [exact Hlast|eapply rt_trans; eassumption].
Qed.

(** All thirteen original C families are retained.  Most need no extra
    field: their original segment already owns its concrete source.  The
    added fields are local input representation and literal caller facts. *)
Inductive sem_pend_program_c_step_receipt environment critical sg observer origin :
  forall state before input stopped current after output,
  kernel_program_c_step environment critical sg observer origin
    state before input stopped current after output -> Prop :=
| SemPendProgramCriticalReceipt : forall local frame call before after segment,
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCCritical environment critical sg observer origin local frame call before after segment)
| SemPendProgramBuiltinReceipt : forall local state before current after input output segment,
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCBuiltin environment critical sg observer origin local state before current after input output segment)
| SemPendProgramInstallReceipt : forall local state before input stopped current after output segment,
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCInstall environment critical sg observer origin local state before input stopped current after output segment)
| SemPendProgramWakeReceipt : forall state before input current after output segment,
    sem_pend_wake_c_receipt sg state before input current after output segment ->
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCWake environment critical sg observer origin state before input current after output segment)
| SemPendProgramStatusReceipt : forall state before current after frame segment,
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCStatus environment critical sg observer origin state before current after frame segment)
| SemPendProgramTaskCreationReceipt : forall state before input current after output segment,
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCTaskCreation environment critical sg observer origin state before input current after output segment)
| SemPendProgramEventCreationReceipt : forall state before input current after output segment,
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCEventCreation environment critical sg observer origin state before input current after output segment)
| SemPendProgramQueueCreationReceipt : forall state before input current after output segment,
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCQueueCreation environment critical sg observer origin state before input current after output segment)
| SemPendProgramMutexPendReceipt : forall local frame call before after segment,
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCMutexPend environment critical sg observer origin local frame call before after segment)
| SemPendProgramMutexPostReceipt : forall source_env local frame call before after segment,
    sem_pend_mutex_post_receipt sg call.(PostComponent.mutex_post_critical_eid)
      call.(PostComponent.mutex_post_critical_caller) call.(PostComponent.mutex_post_critical_entry)
      call.(PostComponent.mutex_post_critical_result) call.(PostComponent.mutex_post_critical_schedule)
      call.(PostComponent.mutex_post_critical_checkpoint)
      (proj2 (PostComponent.mutex_post_critical_segment_source source_env environment.(task_stack_call_external)
        environment.(task_stack_call_platform) critical local sg frame call before after segment)) ->
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCMutexPost environment critical sg observer origin source_env local frame call before after segment)
| SemPendProgramDeletePrimitiveReceipt : forall state before input stopped current after output segment,
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCDeletePrimitive environment critical sg observer origin state before input stopped current after output segment)
| SemPendProgramPairedPrimitiveReceipt : forall state before input stopped current after output segment,
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCPairedPrimitive environment critical sg observer origin state before input stopped current after output segment)
| SemPendProgramDeleteReceipt : forall state before input stopped current after output segment,
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCDelete environment critical sg observer origin state before input stopped current after output segment).

Lemma sem_pend_program_c_step_receipt_projection :
  forall environment critical sg observer origin state before input stopped current after output
    (step : kernel_program_c_step environment critical sg observer origin
      state before input stopped current after output),
  sem_pend_program_c_step_receipt environment critical sg observer origin
    state before input stopped current after output step ->
  forall tid old eid generation,
    state.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    (exists live, current.(TskState).(inUsedTaskStates) tid = Some live) ->
    sem_pend_task_projection state.(TskState) current.(TskState) tid old.
Proof.
  intros environment critical sg observer origin state before input stopped current after output step Hreceipt.
  destruct Hreceipt; intros tid old eid generation Hold Hcont Hlive.
  - destruct segment as [Hcompletion [Hphysical [Hsource Hpacket]]].
    eapply sem_pend_critical_c_source_projection; eassumption.
  - eapply sem_pend_builtin_c_projection; eassumption.
  - eapply sem_pend_install_c_projection; eassumption.
  - eapply (sem_pend_wake_c_receipt_projection environment.(task_stack_call_external)); eassumption.
  - eapply sem_pend_status_c_source_projection;
      [exact (StatusComponent.kernel_status_c_segment_code _ _ _ _ _ _ segment)|exact Hold].
  - eapply sem_pend_task_creation_c_source_projection;
      [eapply CreationComponent.kernel_task_creation_c_segment_source; exact segment|exact Hold].
  - pose proof (proj1 (NamedSourceFrames.kernel_event_creation_c_source_other_fields _ _
      (EventCreationComponent.kernel_event_creation_c_segment_source _ _ _ _ _ _ _ segment))) as Htasks.
    eapply tmr_task_sem_projection_map_eq; [rewrite Htasks; reflexivity|exact Hold].
  - pose proof (proj1 (NamedSourceFrames.kernel_queue_creation_c_source_other_fields _ _ _
      (QueueCreationComponent.kernel_queue_creation_c_segment_source _ _ _ _ _ _ _ segment))) as Htasks.
    eapply tmr_task_sem_projection_map_eq; [rewrite Htasks; reflexivity|exact Hold].
  - destruct segment as [Hsource Hinput Houtput].
    eapply sem_pend_mutex_inheritance_c_projection; eassumption.
  - eapply sem_pend_mutex_post_receipt_projection; eassumption.
  - destruct segment; apply sem_pend_task_projection_refl; exact Hold.
  - destruct segment; [destruct H| |]; apply sem_pend_task_projection_refl; exact Hold.
  - eapply sem_pend_delete_own_c_projection; eassumption.
Qed.

Inductive sem_pend_return_c_step_receipt environment critical sg observer origin :
  forall state before input stopped current after output,
  SelectedReturnPrimitive.kernel_program_return_c_step environment critical sg observer origin
    state before input stopped current after output -> Prop :=
| SemPendReturnOriginalReceipt : forall state before input stopped current after output step,
    sem_pend_program_c_step_receipt environment critical sg observer origin
      state before input stopped current after output step ->
    sem_pend_return_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@SelectedReturnPrimitive.KernelProgramReturnOriginal environment critical sg observer origin
        state before input stopped current after output step)
| SemPendReturnPrimitiveReceipt : forall state before input stopped current after output step,
    sem_pend_return_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@SelectedReturnPrimitive.KernelProgramReturnSelected environment critical sg observer origin
        state before input stopped current after output step)
| SemPendReturnInstallReceipt : forall local frame call before installed sp actual complete selected Hterminal Hselected,
    sem_pend_return_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@SelectedReturnPrimitive.KernelProgramReturnTaskSelectedInstall environment critical sg observer origin
        local frame call before installed sp actual complete selected Hterminal Hselected)
| SemPendReturnIRQReceipt : forall handler entry transfer original saved acquired receipt other frame before installed
    selected after source install restore complete,
    sem_pend_return_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@SelectedReturnPrimitive.KernelProgramReturnIRQSelectedSuffix environment critical sg observer origin
        handler entry transfer original saved acquired receipt other frame before installed selected after source install restore complete).

Lemma sem_pend_return_c_step_receipt_projection :
  forall environment critical sg observer origin state before input stopped current after output
    (step : SelectedReturnPrimitive.kernel_program_return_c_step environment critical sg observer origin
      state before input stopped current after output),
  sem_pend_return_c_step_receipt environment critical sg observer origin
    state before input stopped current after output step ->
  forall tid old eid generation,
    state.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    (exists live, current.(TskState).(inUsedTaskStates) tid = Some live) ->
    sem_pend_task_projection state.(TskState) current.(TskState) tid old.
Proof.
  intros environment critical sg observer origin state before input stopped current after output step Hreceipt.
  destruct Hreceipt; intros tid old eid generation Hold Hcont Hlive.
  - eapply sem_pend_program_c_step_receipt_projection; eassumption.
  - destruct (SelectedReturnPrimitive.kernel_selected_return_c_step_state_stop _ _ _ _ _ _ _ _ step)
      as [-> Hstop]; apply sem_pend_task_projection_refl; exact Hold.
  - eapply sem_pend_install_c_projection;
      [exact (@InstallComponent.TaskInstallCStep environment local sg frame call before installed sp actual complete)|exact Hold].
  - apply sem_pend_task_projection_refl; exact Hold.
Qed.

Inductive sem_pend_selected_step_receipt critical sg observer origin :
  forall environment state before input stopped current after output,
  SelectedCProgram.kernel_program_selected_c_step environment critical sg observer origin
    state before input stopped current after output -> Prop :=
| SemPendSelectedReturnReceipt : forall environment state before input stopped current after output step,
    sem_pend_return_c_step_receipt environment critical sg observer origin
      state before input stopped current after output step ->
    sem_pend_selected_step_receipt critical sg observer origin environment _ _ _ _ _ _ _
      (@SelectedCProgram.KernelSelectedProgramReturn critical sg observer origin environment
        state before input stopped current after output step)
| SemPendSelectedIRQReceipt : forall environment state before input stopped current after output step,
    sem_pend_selected_step_receipt critical sg observer origin (task_sw_hook_call_environment environment) _ _ _ _ _ _ _
      (@SelectedCProgram.KernelSelectedProgramIRQ critical sg observer origin environment
        state before input stopped current after output step)
| SemPendSelectedSuspendReceipt : forall environment state before input stopped current after output step,
    sem_pend_selected_step_receipt critical sg observer origin environment _ _ _ _ _ _ _
      (@SelectedCProgram.KernelSelectedProgramSuspend critical sg observer origin environment
        state before input stopped current after output step).

Definition sem_pend_selected_c_step_receipt environment critical sg observer origin :=
  sem_pend_selected_step_receipt critical sg observer origin environment.

Lemma sem_pend_suspend_step_projection : forall sg request priority state result self current,
  task_suspend_step sg request priority state result self current ->
  forall tid old, state.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_task_projection state.(TskState) current.(TskState) tid old.
Proof.
  intros sg request priority state result self current [error [Herror [Hpriority Hstep]]] tid old Hold.
  destruct (Z.eqb (task_suspend_resolved_priority sg request priority) sg.(osTaskIdlePrio)).
  - destruct Hstep as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
  - destruct (state.(TskState).(prioTbl) (task_suspend_resolved_priority sg request priority)).
    + destruct Hstep as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
    + destruct Hstep as [_ ->]; apply sem_pend_task_projection_refl; exact Hold.
    + destruct Hstep as [previous [Hprevious [_ ->]]].
      eapply sem_pend_updated_task_projection; [exact Hprevious|exact Hold|apply SemPendWaitSuspend].
Qed.

Lemma sem_pend_selected_c_step_receipt_projection :
  forall environment critical sg observer origin state before input stopped current after output
    (step : SelectedCProgram.kernel_program_selected_c_step environment critical sg observer origin
      state before input stopped current after output),
  sem_pend_selected_c_step_receipt environment critical sg observer origin
    state before input stopped current after output step ->
  forall tid old eid generation,
    state.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    (exists live, current.(TskState).(inUsedTaskStates) tid = Some live) ->
    sem_pend_task_projection state.(TskState) current.(TskState) tid old.
Proof.
  intros environment critical sg observer origin state before input stopped current after output step Hreceipt.
  destruct Hreceipt; intros tid old eid generation Hold Hcont Hlive.
  - eapply sem_pend_return_c_step_receipt_projection; eassumption.
  - destruct step.
    pose proof (proj1 (BuiltinComponent.os_int_exit_configured_transfer_state_frame environment sg handler entry transfer source))
      as Hnodes.
    eapply tmr_task_sem_projection_map_eq; [exact Hnodes|exact Hold].
  - destruct step as [saved_local caller saved call frame before after [[Hread Hcode] Hinput Houtput]].
    eapply sem_pend_suspend_step_projection; eassumption.
Qed.

Definition sem_pend_selected_c_sequence_receipt environment critical sg observer origin
  state before input stopped current after output
  (run : kernel_c_sequence (SelectedCProgram.kernel_program_selected_c_step environment critical sg observer origin)
    state before input stopped current after output) : Prop :=
  kernel_c_sequence_has_source (SelectedCProgram.kernel_program_selected_c_step environment critical sg observer origin)
    (sem_pend_selected_c_step_receipt environment critical sg observer origin)
    state before input stopped current after output run.

Lemma sem_pend_selected_c_sequence_receipt_projection :
  forall environment critical sg observer stored_origin state before input stopped current after output
    (run : kernel_c_sequence (SelectedCProgram.kernel_program_selected_c_step environment critical sg observer stored_origin)
      state before input stopped current after output),
  sem_pend_selected_c_sequence_receipt environment critical sg observer stored_origin
    state before input stopped current after output run ->
  forall tid old eid generation,
    task_observer_lifetime state.(TskState) observer (RunningInvocation tid generation) ->
    task_invocation_active current.(TskState) observer (RunningInvocation tid generation) ->
    state.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection state.(TskState) current.(TskState) tid old.
Proof.
  intros environment critical sg observer stored_origin state before input stopped current after output run Hreceipt.
  induction Hreceipt; intros tid old eid generation Hlife Hactive Hold Hcont.
  - apply sem_pend_task_projection_refl; exact Hold.
  - eapply sem_pend_selected_c_step_receipt_projection; [exact H|exact Hold|exact Hcont|].
    destruct Hactive as [Hregistered [Hretired [live [Hlive Hgeneration]]]]; eauto.
  - destruct (sem_pend_selected_c_sequence_lifetime_transport environment critical sg observer stored_origin
      _ _ _ _ _ _ _ first observer (RunningInvocation tid generation) Hlife) as [Hmiddle_life Hfirst_back].
    pose proof (proj2 (sem_pend_selected_c_sequence_lifetime_transport environment critical sg observer stored_origin
      _ _ _ _ _ _ _ last observer (RunningInvocation tid generation) Hmiddle_life) Hactive) as Hmiddle_active.
    destruct (IHHreceipt1 tid old eid generation Hlife Hmiddle_active Hold Hcont) as [middle_node [Hmiddle Hfirst]].
    assert (Hcontinue : sem_pend_wait_continuation eid generation middle_node).
    { eapply sem_pend_wait_trace_preserves_continuation; eassumption. }
    destruct (IHHreceipt2 tid middle_node eid generation Hmiddle_life Hactive Hmiddle Hcontinue)
      as [last_node [Hlast Hsecond]].
    exists last_node; split; [exact Hlast|eapply rt_trans; eassumption].
  - eapply IHHreceipt; eassumption.
Qed.

(** The three original prefix families, retaining the actual legacy trace,
    heap phase proof, or selected C tree.  No prefix is reselected from its
    endpoints and the C tree keeps its own arbitrary stored origin. *)
Inductive sem_pend_sched_prefix_receipt environment critical sg observer :
  forall before current final_heap,
  SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer before current final_heap -> Prop :=
| SemPendSchedPrefixClientsReceipt : forall before current final_heap trace,
    sem_pend_source_trace_receipt environment.(task_stack_call_external) critical.(critical_region_clients)
      sg observer None before false current trace ->
    sem_pend_sched_prefix_receipt environment critical sg observer _ _ _
      (@SchedulerPhaseCandidate.OsSchedTaskReturnPrefixLegacy environment critical sg observer before current final_heap
        (@LegacyTaskReturnPrefix.OsSchedTaskReturnPrefixClients environment critical sg observer before current final_heap trace))
| SemPendSchedPrefixPhasesReceipt : forall before initial_heap current final_heap source,
    sem_pend_sched_phase_receipt environment critical sg before initial_heap current final_heap source ->
    sem_pend_sched_prefix_receipt environment critical sg observer _ _ _
      (@SchedulerPhaseCandidate.OsSchedTaskReturnPrefixLegacy environment critical sg observer before current final_heap
        (@LegacyTaskReturnPrefix.OsSchedTaskReturnPrefixPhases environment critical sg observer before initial_heap current final_heap source))
| SemPendSchedPrefixCSequenceReceipt : forall origin event_observer state before input stopped current after output run source,
    sem_pend_selected_c_sequence_receipt environment critical sg observer origin state before input stopped current after output run ->
    sem_pend_sched_prefix_receipt environment critical sg observer _ _ _
      (@SchedulerPhaseCandidate.OsSchedTaskReturnPrefixCSequence environment critical sg observer origin event_observer
        state before input stopped current after output run source).

Lemma sem_pend_sched_prefix_receipt_projection :
  forall environment critical sg observer before current final_heap
    (prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer before current final_heap),
  sem_pend_sched_prefix_receipt environment critical sg observer before current final_heap prefix ->
  forall tid old eid generation,
    task_observer_lifetime before.(TskState) observer (RunningInvocation tid generation) ->
    task_invocation_active current.(TskState) observer (RunningInvocation tid generation) ->
    before.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection before.(TskState) current.(TskState) tid old.
Proof.
  intros environment critical sg observer before current final_heap prefix Hreceipt.
  destruct Hreceipt; intros tid old eid generation Hlife Hactive Hold Hcont.
  - eapply sem_pend_source_trace_local_projection; eassumption.
  - eapply sem_pend_sched_phase_projection; eassumption.
  - eapply sem_pend_selected_c_sequence_receipt_projection; eassumption.
Qed.

Inductive sem_pend_sched_irq_prefix_receipt environment critical sg observer before current :
  SchedulerPhaseCandidate.os_sched_task_irq_return_prefix environment critical sg observer before current -> Prop :=
| SemPendSchedIRQClientsReceipt : forall trace,
    sem_pend_source_trace_receipt environment.(task_stack_call_external) critical.(critical_region_clients)
      sg observer None before false current trace ->
    sem_pend_sched_irq_prefix_receipt environment critical sg observer before current (or_introl trace)
| SemPendSchedIRQPrefixReceipt : forall final_heap prefix,
    sem_pend_sched_prefix_receipt environment critical sg observer before current final_heap prefix ->
    sem_pend_sched_irq_prefix_receipt environment critical sg observer before current
      (or_intror (ex_intro _ final_heap prefix)).

Lemma sem_pend_sched_irq_prefix_receipt_projection :
  forall environment critical sg observer before current
    (prefix : SchedulerPhaseCandidate.os_sched_task_irq_return_prefix environment critical sg observer before current),
  sem_pend_sched_irq_prefix_receipt environment critical sg observer before current prefix ->
  forall tid old eid generation,
    task_observer_lifetime before.(TskState) observer (RunningInvocation tid generation) ->
    task_invocation_active current.(TskState) observer (RunningInvocation tid generation) ->
    before.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection before.(TskState) current.(TskState) tid old.
Proof.
  intros environment critical sg observer before current prefix Hreceipt.
  destruct Hreceipt; intros tid old eid generation Hlife Hactive Hold Hcont.
  - eapply sem_pend_source_trace_local_projection; eassumption.
  - eapply sem_pend_sched_prefix_receipt_projection; eassumption.
Qed.

(** Four constructors on the unchanged body union.  Its only new payload
    is the finite receipt of that body's original prefix.  Task call/IRQ
    install arguments and their actual source proofs remain the originals. *)
Inductive sem_pend_sched_body_receipt environment critical sg :
  forall entry original returned current,
  SchedulerPhaseCandidate.os_sched_task_body_source environment critical sg entry original returned current -> Prop :=
| SemPendSchedBodyNoSwitchReceipt : forall entry original Hrequest,
    sem_pend_sched_body_receipt environment critical sg _ _ _ _
      (@SchedulerPhaseCandidate.OsSchedTaskBodyNoSwitch environment critical sg entry original Hrequest)
| SemPendSchedBodyTaskInstallReceipt : forall entry original first_installed context outgoing hooked resumed returned before_heap
    Hfirst prefix Hstop Hsaved Hdestination Hhigh Hsame,
    sem_pend_sched_prefix_receipt environment critical sg original.(os_sched_call_invocation)
      first_installed hooked before_heap prefix ->
    sem_pend_sched_body_receipt environment critical sg _ _ _ _
      (@SchedulerPhaseCandidate.OsSchedTaskBodyTaskLastInstall environment critical sg entry original first_installed
        context outgoing hooked resumed returned before_heap Hfirst prefix Hstop Hsaved Hdestination Hhigh Hsame)
| SemPendSchedBodyIRQInstallReceipt : forall entry original first_installed handler irq_entry transfer returned
    Hfirst prefix Hstop Htransfer Hincoming Hsame,
    sem_pend_sched_irq_prefix_receipt environment critical sg original.(os_sched_call_invocation)
      first_installed irq_entry prefix ->
    sem_pend_sched_body_receipt environment critical sg _ _ _ _
      (@SchedulerPhaseCandidate.OsSchedTaskBodyIRQLastInstall environment critical sg entry original first_installed
        handler irq_entry transfer returned Hfirst prefix Hstop Htransfer Hincoming Hsame)
| SemPendSchedBodyTaskCallReceipt : forall entry original first_installed last_entry last_context returned current last_heap
    Hfirst prefix Hvalid Hlast Hsame Hreturned,
    sem_pend_sched_prefix_receipt environment critical sg original.(os_sched_call_invocation)
      first_installed last_entry last_heap prefix ->
    sem_pend_sched_body_receipt environment critical sg _ _ _ _
      (@SchedulerPhaseCandidate.OsSchedTaskBodyTaskLastCall environment critical sg entry original first_installed
        last_entry last_context returned current last_heap Hfirst prefix Hvalid Hlast Hsame Hreturned).

Lemma sem_pend_bound_switch_projection : forall external sg entry call installed,
  task_sw_hook_source_binding external -> os_sched_switch_source external sg entry call installed ->
  forall tid old, entry.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_task_projection entry.(TskState) installed.(TskState) tid old.
Proof.
  intros external sg entry call installed Hbinding
    [Hrequest [sp [saved [hooked [incoming [resumed [Hsave [Hhook [Hdestination Hinstalled]]]]]]]]]
    tid old Hold.
  unfold task_sw_hook_source_binding in Hbinding; rewrite Hbinding in Hhook.
  change (hooked = os_sched_save_current_sp (os_sched_prefix_state entry) call.(os_sched_call_stack).(stackLeaseSlot) sp) in Hhook.
  rewrite Hinstalled, Hhook.
  eapply sem_pend_sched_save_sp_projection; exact Hold.
Qed.

Lemma sem_pend_bound_switch_lifetime_transport : forall external sg entry call installed,
  task_sw_hook_source_binding external -> os_sched_switch_source external sg entry call installed ->
  forall observer origin,
    task_observer_lifetime_transport observer origin entry.(TskState) installed.(TskState).
Proof.
  intros external sg entry call installed Hbinding
    [Hrequest [sp [saved [hooked [incoming [resumed [Hsave [Hhook [Hdestination Hinstalled]]]]]]]]]
    observer origin.
  unfold task_sw_hook_source_binding in Hbinding; rewrite Hbinding in Hhook.
  change (hooked = os_sched_save_current_sp (os_sched_prefix_state entry) call.(os_sched_call_stack).(stackLeaseSlot) sp) in Hhook.
  rewrite Hinstalled, Hhook; unfold os_sched_save_current_sp.
  cbn [os_sched_prefix_state replace_SchedS TskState].
  destruct (entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot)) as [node|] eqn:Hnode.
  - change (task_observer_lifetime_transport observer origin entry.(TskState)
      (glob_task_set_usedtask entry.(TskState) call.(os_sched_call_stack).(stackLeaseSlot) (task_set_saved_sp node sp))).
    eapply task_update_observer_lifetime_transport; [exact Hnode|reflexivity].
  - intros Hlife; split; [exact Hlife|intros Hactive; exact Hactive].
Qed.

Lemma sem_pend_bound_switch_active_back : forall external sg entry call installed,
  task_sw_hook_source_binding external -> os_sched_switch_source external sg entry call installed ->
  forall observer origin,
    task_invocation_active installed.(TskState) observer origin ->
    task_invocation_active entry.(TskState) observer origin.
Proof.
  intros external sg entry call installed Hbinding
    [Hrequest [sp [saved [hooked [incoming [resumed [Hsave [Hhook [Hdestination Hinstalled]]]]]]]]]
    observer origin.
  unfold task_sw_hook_source_binding in Hbinding; rewrite Hbinding in Hhook.
  change (hooked = os_sched_save_current_sp (os_sched_prefix_state entry) call.(os_sched_call_stack).(stackLeaseSlot) sp) in Hhook.
  rewrite Hinstalled, Hhook; unfold os_sched_save_current_sp.
  cbn [os_sched_prefix_state replace_SchedS TskState].
  destruct (entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot)) as [node|] eqn:Hnode;
    intros [Hreg [Hret Hlive]]; (split; [exact Hreg|]; split; [exact Hret|]).
  - destruct origin as [|slot generation]; [exact I|].
    destruct Hlive as [current [Hcurrent Hgeneration]].
    change ((if Z.eqb slot call.(os_sched_call_stack).(stackLeaseSlot) then Some (task_set_saved_sp node sp)
      else entry.(TskState).(inUsedTaskStates) slot) = Some current) in Hcurrent.
    destruct (Z.eqb slot call.(os_sched_call_stack).(stackLeaseSlot)) eqn:Heq.
    + apply Z.eqb_eq in Heq; subst slot; injection Hcurrent as Hcurrent; subst current.
      exists node; split; [exact Hnode|exact Hgeneration].
    + exists current; split; assumption.
  - exact Hlive.
Qed.

Lemma sem_pend_bound_irq_transfer_task_map : forall external port sg handler entry transfer,
  task_sw_hook_source_binding external -> os_int_exit_transfer_source external port sg handler entry transfer ->
  (os_int_exit_installed_state transfer).(TskState).(inUsedTaskStates) = entry.(TskState).(inUsedTaskStates) /\
  (os_int_exit_installed_state transfer).(TskState).(taskLifecycle) = entry.(TskState).(taskLifecycle).
Proof.
  intros external port sg handler entry transfer Hbinding [Hrequest [_ [_ [Hhook Hrest]]]].
  unfold task_sw_hook_source_binding in Hbinding; rewrite Hbinding in Hhook.
  change (transfer.(os_int_exit_hooked_state) = os_int_exit_ready_checkpoint true entry) in Hhook.
  unfold os_int_exit_installed_state; rewrite Hhook; split; reflexivity.
Qed.

Lemma sem_pend_sched_body_receipt_projection :
  forall environment critical sg entry original returned current
    (body : SchedulerPhaseCandidate.os_sched_task_body_source environment critical sg entry original returned current),
  sem_pend_sched_body_receipt environment critical sg entry original returned current body ->
  task_sw_hook_source_binding environment.(task_stack_call_external) ->
  forall tid old eid generation,
    task_observer_lifetime entry.(TskState) original.(os_sched_call_invocation) (RunningInvocation tid generation) ->
    task_invocation_active current.(TskState) original.(os_sched_call_invocation) (RunningInvocation tid generation) ->
    entry.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection entry.(TskState) current.(TskState) tid old.
Proof.
  intros environment critical sg entry original returned current body Hreceipt Hbinding.
  destruct Hreceipt; intros tid old eid generation Hlife Hactive Hold Hcont.
  - apply sem_pend_task_projection_refl; exact Hold.
  - pose proof (proj1 (sem_pend_bound_switch_lifetime_transport _ _ _ _ _ Hbinding Hfirst
      original.(os_sched_call_invocation) (RunningInvocation tid generation) Hlife)) as Hfirst_life.
    destruct (sem_pend_bound_switch_projection _ _ _ _ _ Hbinding Hfirst tid old Hold)
      as [first_node [Hfirst_node Hfirst_trace]].
    assert (Hcontinue : sem_pend_wait_continuation eid generation first_node).
    { eapply sem_pend_wait_trace_preserves_continuation; eassumption. }
    destruct (sem_pend_sched_prefix_receipt_projection environment critical sg original.(os_sched_call_invocation)
      first_installed hooked before_heap prefix H tid first_node eid generation Hfirst_life Hactive Hfirst_node Hcontinue)
      as [last_node [Hlast_node Hlast_trace]].
    exists last_node; split; [exact Hlast_node|eapply rt_trans; eassumption].
  - destruct (sem_pend_bound_irq_transfer_task_map _ _ _ _ _ _ Hbinding Htransfer) as [Hmap Hlifecycle].
    assert (Hirq_active : task_invocation_active irq_entry.(TskState) original.(os_sched_call_invocation)
      (RunningInvocation tid generation)).
    { unfold task_invocation_active, task_invocation_origin_live in *; rewrite Hmap, Hlifecycle in Hactive; exact Hactive. }
    pose proof (proj1 (sem_pend_bound_switch_lifetime_transport _ _ _ _ _ Hbinding Hfirst
      original.(os_sched_call_invocation) (RunningInvocation tid generation) Hlife)) as Hfirst_life.
    destruct (sem_pend_bound_switch_projection _ _ _ _ _ Hbinding Hfirst tid old Hold)
      as [first_node [Hfirst_node Hfirst_trace]].
    assert (Hcontinue : sem_pend_wait_continuation eid generation first_node).
    { eapply sem_pend_wait_trace_preserves_continuation; eassumption. }
    destruct (sem_pend_sched_irq_prefix_receipt_projection environment critical sg original.(os_sched_call_invocation)
      first_installed irq_entry prefix H tid first_node eid generation Hfirst_life Hirq_active Hfirst_node Hcontinue)
      as [last_node [Hlast_node Hlast_trace]].
    exists last_node; split; [rewrite Hmap; exact Hlast_node|eapply rt_trans; eassumption].
  - pose proof (sem_pend_bound_switch_active_back _ _ _ _ _ Hbinding Hlast
      original.(os_sched_call_invocation) (RunningInvocation tid generation) Hactive) as Hlast_active.
    pose proof (proj1 (sem_pend_bound_switch_lifetime_transport _ _ _ _ _ Hbinding Hfirst
      original.(os_sched_call_invocation) (RunningInvocation tid generation) Hlife)) as Hfirst_life.
    destruct (sem_pend_bound_switch_projection _ _ _ _ _ Hbinding Hfirst tid old Hold)
      as [first_node [Hfirst_node Hfirst_trace]].
    assert (Hcontinue : sem_pend_wait_continuation eid generation first_node).
    { eapply sem_pend_wait_trace_preserves_continuation; eassumption. }
    destruct (sem_pend_sched_prefix_receipt_projection environment critical sg original.(os_sched_call_invocation)
      first_installed last_entry last_heap prefix H tid first_node eid generation Hfirst_life Hlast_active Hfirst_node Hcontinue)
      as [last_node [Hlast_node Hlast_trace]].
    destruct (sem_pend_bound_switch_projection _ _ _ _ _ Hbinding Hlast tid last_node Hlast_node)
      as [current_node [Hcurrent_node Hcurrent_trace]].
    exists current_node; split; [exact Hcurrent_node|eapply rt_trans; [exact Hfirst_trace|eapply rt_trans; eassumption]].
Qed.

(** Actual entry/return Task source fixes the SAME incarnation; a final
    active premise is derived from that return, never added to a leaf. *)
Lemma sem_pend_sched_body_return_projection :
  forall environment critical sg entry original returned current
    (body : SchedulerPhaseCandidate.os_sched_task_body_source environment critical sg entry original returned current),
  sem_pend_sched_body_receipt environment critical sg entry original returned current body ->
  task_sw_hook_source_binding environment.(task_stack_call_external) ->
  task_in_range sg entry.(TskState) -> kernel_call_task_source original entry ->
  task_tcb_init_stack_same_call returned original -> kernel_call_task_source returned current ->
  forall old eid,
    entry.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some old ->
    sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) old ->
    sem_pend_task_projection entry.(TskState) current.(TskState)
      original.(os_sched_call_stack).(stackLeaseSlot) old.
Proof.
  intros environment critical sg entry original returned current body Hreceipt Hbinding Htasks Hsource
    Hsame Hreturned old eid Hold Hcont.
  eapply sem_pend_sched_body_receipt_projection; [exact Hreceipt|exact Hbinding| | |exact Hold|exact Hcont].
  - rewrite <- (proj1 Hsource); apply task_observer_lifetime_from_active with sg;
      [exact Htasks|exact (proj1 (proj2 Hsource))].
  - rewrite <- (proj1 Hsource); eapply kernel_call_same_return_observer_active; eassumption.
Qed.

(** MultiPtr is a separate observation of the actual writes.  The old
    OtherFields waiter relation intentionally does not constrain it. *)
Lemma sem_pend_critical_c_multi_pointer_transport : forall sg call,
  CriticalComponent.kernel_critical_c_source sg call ->
  tmr_task_multi_pointer_transport (CriticalComponent.kernel_critical_c_entry call)
    (CriticalComponent.kernel_critical_c_returned call).
Proof.
  intros sg [actual|actual] Hsource; cbn in Hsource |- *.
  - destruct Hsource as [error [Hcritical Hcode]].
    eapply tmr_task_change_prio_multi_pointer_transport; exact Hcritical.
  - unfold CriticalComponent.mutex_del_critical_fields_observation in Hsource; destruct Hsource.
    + destruct H0 as [error [scheduled [Hcritical Hcode]]].
      eapply tmr_task_mutex_delete_multi_pointer_transport; exact Hcritical.
    + apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
Qed.

Lemma sem_pend_task_creation_c_multi_pointer_transport : forall sg entry current,
  CreationComponent.kernel_task_creation_c_source sg entry current ->
  tmr_task_multi_pointer_transport entry current.
Proof.
  intros sg entry current Hsource; destruct Hsource;
    try (apply tmr_task_multi_pointer_transport_map_eq; reflexivity).
  - unfold task_create_critical in H; destruct (Z.ltb 0 entry.(IntrState).(intNesting)).
    + destruct H as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
    + destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority);
        destruct Hstep as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - destruct H2 as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
Qed.

Lemma sem_pend_status_c_multi_pointer_transport : forall sg entry current,
  StatusComponent.kernel_status_c_source sg entry current ->
  tmr_task_multi_pointer_transport entry current.
Proof.
  intros sg entry current Hsource; destruct Hsource.
  - destruct H as [cid [running [_ [_ [_ Hstep]]]]].
    destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg priority running))).
    + destruct Hstep as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
    + destruct Hstep as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
    + destruct Hstep as [previous [Hprevious [_ ->]]].
      eapply tmr_task_update_multi_pointer_transport; [exact Hprevious|reflexivity|reflexivity|reflexivity].
  - destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority).
    + destruct Hstep as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
    + destruct Hstep as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
    + destruct Hstep as [previous [Hprevious Hstep]].
      destruct (task_is_suspended previous.(stat)); destruct Hstep as [_ ->].
      * eapply tmr_task_update_multi_pointer_transport; [exact Hprevious|reflexivity|reflexivity|reflexivity].
      * apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - destruct H as [event [fields [Hlookup [Htype [Hfields ->]]]]].
    destruct (Z.ltb 0 fields.(semCount)); apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
Qed.

Lemma sem_pend_wake_c_multi_pointer_transport : forall sg entry current,
  WakeComponent.kernel_wake_c_source sg entry current ->
  tmr_task_multi_pointer_transport entry current.
Proof.
  intros sg entry current Hsource; destruct Hsource.
  - destruct (flag_task_rdy_result _ _ _ _ _ _ _ H)
      as [waiter [flags [node [Hunlink [Hnode [-> Hschedule]]]]]].
    eapply tmr_task_update_multi_pointer_transport; [exact Hnode|reflexivity|reflexivity|reflexivity].
  - eapply tmr_task_event_ready_multi_pointer_transport; exact H.
  - eapply tmr_task_update_multi_pointer_transport;
      [exact H|rewrite (tick_task_step_task_state_eq _ _ _ _ H); reflexivity| |];
      unfold tick_task_update; destruct (Z.eqb old.(dly) 0); reflexivity.
Qed.

Lemma sem_pend_builtin_c_multi_pointer_transport :
  forall environment critical local sg state before current after input output,
  BuiltinComponent.kernel_builtin_c_segment environment critical local sg state before current after input output ->
  tmr_task_multi_pointer_transport state current.
Proof.
  intros environment critical local sg state before current after input output Hsegment; destruct Hsegment.
  - destruct operation; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - destruct H as [Hinput Houtput].
    destruct Hinput as [owned [rest [Hjoin [[[Hvalid Hfacts] Hbody] Hframe]]]].
    destruct (task_create_stack_publication_raw_projection sg publication state _ effect) as [Hraw Hstate].
    rewrite Hstate; change (tmr_task_multi_pointer_transport state (task_create_stack_publication_raw_state sg publication state)).
    eapply tmr_task_creation_multi_pointer_transport; [exact (proj1 (proj2 Hvalid))|exact Hraw].
  - pose proof (BuiltinComponent.kernel_irq_transfer_c_completion_source environment critical sg
      handler saved entry transfer frame before after H) as Hsource.
    apply tmr_task_multi_pointer_transport_map_eq.
    exact (proj1 (BuiltinComponent.os_int_exit_configured_transfer_state_frame environment sg handler entry transfer Hsource)).
Qed.

Lemma sem_pend_install_c_multi_pointer_transport : forall environment local sg state before input stopped current after output,
  InstallComponent.task_install_c_step environment local sg state before input stopped current after output ->
  tmr_task_multi_pointer_transport state current.
Proof.
  intros environment local sg state before input stopped current after output Hstep.
  destruct Hstep as [frame call before_heap after_heap sp Hactual [Hsource Hcompletion]].
  apply tmr_task_multi_pointer_transport_map_eq.
  exact (proj1 (os_sched_install_client_state_frame environment.(task_stack_call_external)
    call.(InstallComponent.task_install_fields_context) call.(InstallComponent.task_install_fields_outgoing)
    call.(InstallComponent.task_install_fields_incoming) call.(InstallComponent.task_install_fields_resumed)
    sg call.(InstallComponent.task_install_fields_entry) (InstallComponent.task_install_fields_current call) Hsource)).
Qed.

Lemma sem_pend_mutex_inheritance_c_multi_pointer_transport : forall sg call,
  PendComponent.mutex_pend_inheritance_c_source sg call ->
  tmr_task_multi_pointer_transport call.(PendComponent.mutex_pend_inheritance_entry)
    call.(PendComponent.mutex_pend_inheritance_returned).
Proof.
  intros sg call [Hselected [Hnonowner Hsource]]; unfold mutex_pend_inherit_step in Hsource.
  destruct (mutex_pend_inherit_action sg.(osPrioMutexCeilDis)
    call.(PendComponent.mutex_pend_inheritance_base) call.(PendComponent.mutex_pend_inheritance_node).(curPrio)
    call.(PendComponent.mutex_pend_inheritance_waiter) call.(PendComponent.mutex_pend_inheritance_ceiling)).
  - rewrite Hsource; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - rewrite Hsource; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - destruct Hsource as [events [Hevents ->]].
    eapply tmr_task_update_multi_pointer_transport; [exact Hselected|reflexivity|reflexivity|reflexivity].
Qed.

Lemma sem_pend_mutex_post_prepare_multi_pointer_transport : forall sg mutex selected entry current,
  mutex_post_prepare sg mutex selected entry current -> tmr_task_multi_pointer_transport entry current.
Proof.
  intros sg mutex selected entry current Hprepare; unfold mutex_post_prepare in Hprepare; destruct Z.eq_dec.
  - subst current; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - destruct Hprepare as [node [priority [Hnode [Hscan ->]]]].
    unfold mutex_post_owner_priority_state; destruct Z.eq_dec.
    + apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
    + eapply tmr_task_update_multi_pointer_transport; [exact Hnode|reflexivity|reflexivity|reflexivity].
Qed.

Lemma sem_pend_mutex_post_multi_pointer_transport : forall sg event caller entry result schedule current,
  mutex_post_critical sg event caller entry result schedule current ->
  tmr_task_multi_pointer_transport entry current.
Proof.
  intros sg event caller entry result schedule current Hsource; destruct Hsource.
  - apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - change (tmr_task_multi_pointer_transport entry prepared).
    eapply sem_pend_mutex_post_prepare_multi_pointer_transport; exact H3.
  - change (tmr_task_multi_pointer_transport entry woken).
    eapply tmr_task_multi_pointer_transport_trans.
    + eapply sem_pend_mutex_post_prepare_multi_pointer_transport; exact H3.
    + eapply tmr_task_event_ready_multi_pointer_transport; exact H5.
Qed.

Lemma sem_pend_delete_prepare_multi_pointer_transport : forall state selected node prepared loan,
  state.(TskState).(inUsedTaskStates) selected = Some node ->
  task_delete_prepare_single_wait state selected node = Some (prepared, loan) ->
  tmr_task_multi_pointer_transport state prepared.
Proof.
  intros state selected node prepared loan Hselected Hprepare.
  pose proof (proj2 (task_delete_preparation_task_projections__release_and_recycle_resources
    state selected node prepared loan Hprepare)) as Hprepared.
  destruct (task_delete_prepare_single_wait_frame state selected node prepared loan Hprepare)
    as [next [Hstate Hfields]].
  assert (Hnext : next = task_delete_prepared_node node).
  { rewrite Hstate in Hprepared; cbn [replace_FlagS replace_EventS replace_SchedS replace_TskS TskState
      glob_task_set_usedtask inUsedTaskStates] in Hprepared.
    rewrite Z.eqb_refl in Hprepared; congruence. }
  subst next; eapply tmr_task_update_multi_pointer_transport;
    [exact Hselected|rewrite Hstate; reflexivity|reflexivity|reflexivity].
Qed.

Lemma sem_pend_delete_own_c_multi_pointer :
  forall environment critical sg observer origin state before input stopped current after output,
  DeleteComponent.task_delete_own_c_segment environment critical sg observer origin
    state before input stopped current after output ->
  forall tid old, state.(TskState).(inUsedTaskStates) tid = Some old ->
    (exists live, current.(TskState).(inUsedTaskStates) tid = Some live) ->
    exists node, current.(TskState).(inUsedTaskStates) tid = Some node /\
      node.(taskGeneration) = old.(taskGeneration) /\ node.(tcbEventMultiPtr) = old.(tcbEventMultiPtr).
Proof.
  intros environment critical sg observer origin state before input stopped current after output Hstep.
  destruct Hstep as [inputs before_heap prepared_heap Hcontext Hcompletion|capture after_heap Hcontext Hcompletion];
    intros tid old Hold Hlive.
  - destruct Hcompletion as [[Hhistory [Hprepare Hprotocol]] Hinput Houtput].
    destruct Hhistory as [Hlookup [Hselected [Hnode Hpointer]]].
    exact (sem_pend_delete_prepare_multi_pointer_transport _ _ _ _ _
      (proj2 (task_delete_table_lookup_live _ _ _ _ Hnode)) Hprepare tid old Hold).
  - destruct Hlive as [live Hlive].
    destruct (task_unlink_used_map_lookup_origin _ _ _ _ _ Hlive) as [Hdifferent Hprevious].
    destruct Hprevious as [previous [Hprevious Hfields]].
    assert (previous = old) by congruence; subst previous.
    exists live; split; [exact Hlive|].
    exact (conj (f_equal taskGeneration Hfields) (f_equal tcbEventMultiPtr Hfields)).
Qed.

Lemma sem_pend_program_c_step_multi_pointer :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_program_c_step environment critical sg observer origin state before input stopped current after output ->
  forall tid old, state.(TskState).(inUsedTaskStates) tid = Some old ->
    (exists live, current.(TskState).(inUsedTaskStates) tid = Some live) ->
    exists node, current.(TskState).(inUsedTaskStates) tid = Some node /\
      node.(taskGeneration) = old.(taskGeneration) /\ node.(tcbEventMultiPtr) = old.(tcbEventMultiPtr).
Proof.
  intros environment critical sg observer origin state before input stopped current after output Hstep.
  destruct Hstep; intros tid old Hold Hlive.
  - destruct H as [Hcompletion [Hphysical [Hsource Hpacket]]].
    exact (sem_pend_critical_c_multi_pointer_transport sg call Hsource tid old Hold).
  - exact (sem_pend_builtin_c_multi_pointer_transport _ _ _ _ _ _ _ _ _ _ H tid old Hold).
  - exact (sem_pend_install_c_multi_pointer_transport _ _ _ _ _ _ _ _ _ _ H tid old Hold).
  - exact (sem_pend_wake_c_multi_pointer_transport sg _ _
      (WakeComponent.kernel_wake_c_segment_source _ _ _ _ _ _ _ H) tid old Hold).
  - exact (sem_pend_status_c_multi_pointer_transport sg _ _
      (StatusComponent.kernel_status_c_segment_code _ _ _ _ _ _ H) tid old Hold).
  - exact (sem_pend_task_creation_c_multi_pointer_transport sg _ _
      (CreationComponent.kernel_task_creation_c_segment_source _ _ _ _ _ _ _ H) tid old Hold).
  - eapply tmr_task_multi_pointer_transport_map_eq; [|exact Hold].
    rewrite (proj1 (NamedSourceFrames.kernel_event_creation_c_source_other_fields _ _
      (EventCreationComponent.kernel_event_creation_c_segment_source _ _ _ _ _ _ _ H))); reflexivity.
  - eapply tmr_task_multi_pointer_transport_map_eq; [|exact Hold].
    rewrite (proj1 (NamedSourceFrames.kernel_queue_creation_c_source_other_fields _ _ _
      (QueueCreationComponent.kernel_queue_creation_c_segment_source _ _ _ _ _ _ _ H))); reflexivity.
  - destruct H as [Hsource Hinput Houtput].
    exact (sem_pend_mutex_inheritance_c_multi_pointer_transport sg call Hsource tid old Hold).
  - destruct H as [[Hcaller Hsource] Hinput Houtput].
    exact (sem_pend_mutex_post_multi_pointer_transport _ _ _ _ _ _ _ Hsource tid old Hold).
  - destruct H; exists old; repeat split; try reflexivity; exact Hold.
  - destruct H; [destruct H| |]; exists old; repeat split; try reflexivity; exact Hold.
  - eapply sem_pend_delete_own_c_multi_pointer; eassumption.
Qed.

Lemma sem_pend_return_c_step_multi_pointer :
  forall environment critical sg observer origin state before input stopped current after output,
  SelectedReturnPrimitive.kernel_program_return_c_step environment critical sg observer origin
    state before input stopped current after output ->
  forall tid old, state.(TskState).(inUsedTaskStates) tid = Some old ->
    (exists live, current.(TskState).(inUsedTaskStates) tid = Some live) ->
    exists node, current.(TskState).(inUsedTaskStates) tid = Some node /\
      node.(taskGeneration) = old.(taskGeneration) /\ node.(tcbEventMultiPtr) = old.(tcbEventMultiPtr).
Proof.
  intros environment critical sg observer origin state before input stopped current after output Hstep.
  destruct Hstep; intros tid old Hold Hlive.
  - eapply sem_pend_program_c_step_multi_pointer; eassumption.
  - destruct (SelectedReturnPrimitive.kernel_selected_return_c_step_state_stop _ _ _ _ _ _ _ _ H)
      as [-> Hstop]; exists old; auto.
  - exact (sem_pend_install_c_multi_pointer_transport _ _ _ _ _ _ _ _ _ _
      (@InstallComponent.TaskInstallCStep environment local sg frame call before installed sp actual complete) tid old Hold).
  - exists old; auto.
Qed.

Lemma sem_pend_suspend_step_multi_pointer_transport : forall sg request priority state result self current,
  task_suspend_step sg request priority state result self current -> tmr_task_multi_pointer_transport state current.
Proof.
  intros sg request priority state result self current [error [Herror [Hpriority Hstep]]].
  destruct (Z.eqb (task_suspend_resolved_priority sg request priority) sg.(osTaskIdlePrio)).
  - destruct Hstep as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - destruct (state.(TskState).(prioTbl) (task_suspend_resolved_priority sg request priority)).
    + destruct Hstep as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
    + destruct Hstep as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
    + destruct Hstep as [previous [Hprevious [_ ->]]].
      eapply tmr_task_update_multi_pointer_transport; [exact Hprevious|reflexivity|reflexivity|reflexivity].
Qed.

Lemma sem_pend_selected_c_step_multi_pointer :
  forall environment critical sg observer origin state before input stopped current after output,
  SelectedCProgram.kernel_program_selected_c_step environment critical sg observer origin
    state before input stopped current after output ->
  forall tid old, state.(TskState).(inUsedTaskStates) tid = Some old ->
    (exists live, current.(TskState).(inUsedTaskStates) tid = Some live) ->
    exists node, current.(TskState).(inUsedTaskStates) tid = Some node /\
      node.(taskGeneration) = old.(taskGeneration) /\ node.(tcbEventMultiPtr) = old.(tcbEventMultiPtr).
Proof.
  intros environment critical sg observer origin state before input stopped current after output Hstep.
  destruct Hstep; intros tid old Hold Hlive.
  - eapply sem_pend_return_c_step_multi_pointer; eassumption.
  - destruct H.
    pose proof (proj1 (BuiltinComponent.os_int_exit_configured_transfer_state_frame environment sg handler entry transfer source))
      as Hnodes.
    exists old; rewrite Hnodes; auto.
  - destruct H as [saved_local caller saved call frame before after [[Hread Hcode] Hinput Houtput]].
    exact (sem_pend_suspend_step_multi_pointer_transport _ _ _ _ _ _ _ Hcode tid old Hold).
Qed.

Lemma sem_pend_selected_c_sequence_multi_pointer :
  forall environment critical sg observer stored_origin state before input stopped current after output,
  kernel_c_sequence (SelectedCProgram.kernel_program_selected_c_step environment critical sg observer stored_origin)
    state before input stopped current after output ->
  forall tid old generation,
    task_observer_lifetime state.(TskState) observer (RunningInvocation tid generation) ->
    task_invocation_active current.(TskState) observer (RunningInvocation tid generation) ->
    state.(TskState).(inUsedTaskStates) tid = Some old ->
    exists node, current.(TskState).(inUsedTaskStates) tid = Some node /\
      node.(taskGeneration) = old.(taskGeneration) /\ node.(tcbEventMultiPtr) = old.(tcbEventMultiPtr).
Proof.
  intros environment critical sg observer stored_origin state before input stopped current after output run.
  induction run; intros tid old generation Hlife Hactive Hold.
  - exists old; auto.
  - eapply sem_pend_selected_c_step_multi_pointer; [exact H|exact Hold|].
    destruct Hactive as [Hregistered [Hretired [live [Hlive Hgeneration]]]]; eauto.
  - destruct (sem_pend_selected_c_sequence_lifetime_transport environment critical sg observer stored_origin
      _ _ _ _ _ _ _ run1 observer (RunningInvocation tid generation) Hlife) as [Hmiddle_life Hfirst_back].
    pose proof (proj2 (sem_pend_selected_c_sequence_lifetime_transport environment critical sg observer stored_origin
      _ _ _ _ _ _ _ run2 observer (RunningInvocation tid generation) Hmiddle_life) Hactive) as Hmiddle_active.
    destruct (IHrun1 tid old generation Hlife Hmiddle_active Hold) as [middle_node [Hmiddle [Hgen Hptr]]].
    destruct (IHrun2 tid middle_node generation Hmiddle_life Hactive Hmiddle)
      as [last_node [Hlast [Hgen' Hptr']]].
    exists last_node; split; [exact Hlast|]. split; congruence.
  - eapply IHrun; eassumption.
Qed.

Lemma sem_pend_delete_environment_multi_pointer_transport :
  forall environment critical saved_local requested sg completed phase loan original before returned after
    mask before_heap after_heap frame
    (execution : sched_task_delete_environment_execution environment critical saved_local requested
      sg completed phase loan original before returned after mask before_heap after_heap frame),
  sem_pend_delete_environment_receipt environment critical saved_local requested sg completed phase loan
    original before returned after mask before_heap after_heap frame execution ->
  tmr_task_multi_pointer_transport before after.
Proof.
  intros; eapply tmr_task_resumption_source_multi_pointer_transport; exact H.
Qed.

Lemma sem_pend_delete_window_multi_pointer_transport :
  forall environment critical sg before before_heap after after_heap
    (window : sched_task_delete_window_execution environment critical sg before before_heap after after_heap),
  sem_pend_delete_window_receipt environment critical sg before before_heap after after_heap window ->
  tmr_task_multi_pointer_transport before after.
Proof.
  intros environment critical sg before before_heap after after_heap window Hreceipt.
  destruct Hreceipt; eapply tmr_task_multi_pointer_transport_trans.
  - eapply sem_pend_delete_environment_multi_pointer_transport; exact H.
  - eapply sem_pend_delete_environment_multi_pointer_transport; exact H0.
Qed.

Lemma sem_pend_sched_phase_step_multi_pointer_transport :
  forall environment critical sg before before_heap after after_heap
    (step : sched_task_phase_heap_step environment critical sg before before_heap after after_heap),
  sem_pend_sched_phase_step_receipt environment critical sg before before_heap after after_heap step ->
  tmr_task_multi_pointer_transport before after.
Proof.
  intros environment critical sg before before_heap after after_heap step Hreceipt; destruct Hreceipt.
  - destruct (sched_task_mutex_del_always_source_resources environment.(task_stack_call_external)
      sg eid entry prepared event mutex before_heap after_heap frame Hlayout Hobject Hentry Hpre Hactual)
      as [Hcontrol [Hsource Hpost]].
    eapply tmr_task_mutex_delete_multi_pointer_transport; exact Hsource.
  - eapply sem_pend_delete_environment_multi_pointer_transport; exact H.
  - eapply sem_pend_delete_window_multi_pointer_transport; exact H.
Qed.

Lemma sem_pend_sched_phase_multi_pointer_transport :
  forall environment critical sg before before_heap after after_heap
    (source : sched_task_phase_heap_source environment critical sg before before_heap after after_heap),
  sem_pend_sched_phase_receipt environment critical sg before before_heap after after_heap source ->
  tmr_task_multi_pointer_transport before after.
Proof.
  intros environment critical sg before before_heap after after_heap source Hreceipt; induction Hreceipt.
  - apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - eapply tmr_task_multi_pointer_transport_trans; [|exact IHHreceipt].
    eapply sem_pend_sched_phase_step_multi_pointer_transport; exact H.
Qed.

Lemma sem_pend_sched_prefix_multi_pointer :
  forall environment critical sg observer before current final_heap
    (prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer before current final_heap),
  sem_pend_sched_prefix_receipt environment critical sg observer before current final_heap prefix ->
  forall tid old generation,
    task_observer_lifetime before.(TskState) observer (RunningInvocation tid generation) ->
    task_invocation_active current.(TskState) observer (RunningInvocation tid generation) ->
    before.(TskState).(inUsedTaskStates) tid = Some old ->
    exists node, current.(TskState).(inUsedTaskStates) tid = Some node /\
      node.(taskGeneration) = old.(taskGeneration) /\ node.(tcbEventMultiPtr) = old.(tcbEventMultiPtr).
Proof.
  intros environment critical sg observer before current final_heap prefix Hreceipt.
  destruct Hreceipt; intros tid old generation Hlife Hactive Hold.
  - exact (tmr_task_source_trace_multi_pointer_transport _ _ _ _ _ _ _ _ trace H tid old Hold).
  - exact (sem_pend_sched_phase_multi_pointer_transport _ _ _ _ _ _ _ source H tid old Hold).
  - eapply sem_pend_selected_c_sequence_multi_pointer; eassumption.
Qed.

Lemma sem_pend_sched_irq_prefix_multi_pointer :
  forall environment critical sg observer before current
    (prefix : SchedulerPhaseCandidate.os_sched_task_irq_return_prefix environment critical sg observer before current),
  sem_pend_sched_irq_prefix_receipt environment critical sg observer before current prefix ->
  forall tid old generation,
    task_observer_lifetime before.(TskState) observer (RunningInvocation tid generation) ->
    task_invocation_active current.(TskState) observer (RunningInvocation tid generation) ->
    before.(TskState).(inUsedTaskStates) tid = Some old ->
    exists node, current.(TskState).(inUsedTaskStates) tid = Some node /\
      node.(taskGeneration) = old.(taskGeneration) /\ node.(tcbEventMultiPtr) = old.(tcbEventMultiPtr).
Proof.
  intros environment critical sg observer before current prefix Hreceipt.
  destruct Hreceipt; intros tid old generation Hlife Hactive Hold.
  - exact (tmr_task_source_trace_multi_pointer_transport _ _ _ _ _ _ _ _ trace H tid old Hold).
  - eapply sem_pend_sched_prefix_multi_pointer; eassumption.
Qed.

Lemma sem_pend_bound_switch_multi_pointer_transport : forall external sg entry call installed,
  task_sw_hook_source_binding external -> os_sched_switch_source external sg entry call installed ->
  tmr_task_multi_pointer_transport entry installed.
Proof.
  intros external sg entry call installed Hbinding
    [Hrequest [sp [saved [hooked [incoming [resumed [Hsave [Hhook [Hdestination Hinstalled]]]]]]]]].
  unfold task_sw_hook_source_binding in Hbinding; rewrite Hbinding in Hhook.
  change (hooked = os_sched_save_current_sp (os_sched_prefix_state entry) call.(os_sched_call_stack).(stackLeaseSlot) sp) in Hhook.
  rewrite Hinstalled, Hhook; unfold os_sched_save_current_sp; cbn [os_sched_prefix_state replace_SchedS TskState].
  destruct (entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot)) as [node|] eqn:Hnode.
  - eapply tmr_task_update_multi_pointer_transport; [exact Hnode|reflexivity|reflexivity|reflexivity].
  - apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
Qed.

Lemma sem_pend_sched_body_multi_pointer :
  forall environment critical sg entry original returned current
    (body : SchedulerPhaseCandidate.os_sched_task_body_source environment critical sg entry original returned current),
  sem_pend_sched_body_receipt environment critical sg entry original returned current body ->
  task_sw_hook_source_binding environment.(task_stack_call_external) ->
  forall tid old generation,
    task_observer_lifetime entry.(TskState) original.(os_sched_call_invocation) (RunningInvocation tid generation) ->
    task_invocation_active current.(TskState) original.(os_sched_call_invocation) (RunningInvocation tid generation) ->
    entry.(TskState).(inUsedTaskStates) tid = Some old ->
    exists node, current.(TskState).(inUsedTaskStates) tid = Some node /\
      node.(taskGeneration) = old.(taskGeneration) /\ node.(tcbEventMultiPtr) = old.(tcbEventMultiPtr).
Proof.
  intros environment critical sg entry original returned current body Hreceipt Hbinding.
  destruct Hreceipt; intros tid old generation Hlife Hactive Hold.
  - exists old; auto.
  - pose proof (proj1 (sem_pend_bound_switch_lifetime_transport _ _ _ _ _ Hbinding Hfirst
      original.(os_sched_call_invocation) (RunningInvocation tid generation) Hlife)) as Hfirst_life.
    destruct (sem_pend_bound_switch_multi_pointer_transport _ _ _ _ _ Hbinding Hfirst tid old Hold)
      as [first_node [Hfirst_node [Hgen Hptr]]].
    destruct (sem_pend_sched_prefix_multi_pointer environment critical sg original.(os_sched_call_invocation)
      first_installed hooked before_heap prefix H tid first_node generation Hfirst_life Hactive Hfirst_node)
      as [last_node [Hlast_node [Hgen' Hptr']]].
    exists last_node; split; [exact Hlast_node|]. split; congruence.
  - destruct (sem_pend_bound_irq_transfer_task_map _ _ _ _ _ _ Hbinding Htransfer) as [Hmap Hlifecycle].
    assert (Hirq_active : task_invocation_active irq_entry.(TskState) original.(os_sched_call_invocation)
      (RunningInvocation tid generation)).
    { unfold task_invocation_active, task_invocation_origin_live in *; rewrite Hmap, Hlifecycle in Hactive; exact Hactive. }
    pose proof (proj1 (sem_pend_bound_switch_lifetime_transport _ _ _ _ _ Hbinding Hfirst
      original.(os_sched_call_invocation) (RunningInvocation tid generation) Hlife)) as Hfirst_life.
    destruct (sem_pend_bound_switch_multi_pointer_transport _ _ _ _ _ Hbinding Hfirst tid old Hold)
      as [first_node [Hfirst_node [Hgen Hptr]]].
    destruct (sem_pend_sched_irq_prefix_multi_pointer environment critical sg original.(os_sched_call_invocation)
      first_installed irq_entry prefix H tid first_node generation Hfirst_life Hirq_active Hfirst_node)
      as [last_node [Hlast_node [Hgen' Hptr']]].
    exists last_node; split; [rewrite Hmap; exact Hlast_node|]. split; congruence.
  - pose proof (sem_pend_bound_switch_active_back _ _ _ _ _ Hbinding Hlast
      original.(os_sched_call_invocation) (RunningInvocation tid generation) Hactive) as Hlast_active.
    pose proof (proj1 (sem_pend_bound_switch_lifetime_transport _ _ _ _ _ Hbinding Hfirst
      original.(os_sched_call_invocation) (RunningInvocation tid generation) Hlife)) as Hfirst_life.
    destruct (sem_pend_bound_switch_multi_pointer_transport _ _ _ _ _ Hbinding Hfirst tid old Hold)
      as [first_node [Hfirst_node [Hgen Hptr]]].
    destruct (sem_pend_sched_prefix_multi_pointer environment critical sg original.(os_sched_call_invocation)
      first_installed last_entry last_heap prefix H tid first_node generation Hfirst_life Hlast_active Hfirst_node)
      as [last_node [Hlast_node [Hgen' Hptr']]].
    destruct (sem_pend_bound_switch_multi_pointer_transport _ _ _ _ _ Hbinding Hlast tid last_node Hlast_node)
      as [current_node [Hcurrent_node [Hgen'' Hptr'']]].
    exists current_node; split; [exact Hcurrent_node|]. split; congruence.
Qed.

(** Both observations identify the SAME actual node by its original slot.
    Its incoming MultiPtr value is propagated, including when it is zero. *)
Lemma sem_pend_sched_body_return_waiter_multi_pointer :
  forall environment critical sg entry original returned current
    (body : SchedulerPhaseCandidate.os_sched_task_body_source environment critical sg entry original returned current),
  sem_pend_sched_body_receipt environment critical sg entry original returned current body ->
  task_sw_hook_source_binding environment.(task_stack_call_external) ->
  task_in_range sg entry.(TskState) -> kernel_call_task_source original entry ->
  task_tcb_init_stack_same_call returned original -> kernel_call_task_source returned current ->
  forall old eid,
    entry.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some old ->
    sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) old ->
    exists node, current.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
      clos_refl_trans TaskAbstractState sem_pend_wait_effect old node /\
      node.(taskGeneration) = old.(taskGeneration) /\ node.(tcbEventMultiPtr) = old.(tcbEventMultiPtr).
Proof.
  intros environment critical sg entry original returned current body Hreceipt Hbinding Htasks Hsource
    Hsame Hreturned old eid Hold Hcont.
  destruct (sem_pend_sched_body_return_projection environment critical sg entry original returned current body
    Hreceipt Hbinding Htasks Hsource Hsame Hreturned old eid Hold Hcont) as [node [Hnode Htrace]].
  assert (Hlife : task_observer_lifetime entry.(TskState) original.(os_sched_call_invocation)
    (RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration))).
  { rewrite <- (proj1 Hsource); apply task_observer_lifetime_from_active with sg;
      [exact Htasks|exact (proj1 (proj2 Hsource))]. }
  assert (Hactive : task_invocation_active current.(TskState) original.(os_sched_call_invocation)
    (RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration))).
  { rewrite <- (proj1 Hsource); eapply kernel_call_same_return_observer_active; eassumption. }
  destruct (sem_pend_sched_body_multi_pointer environment critical sg entry original returned current body
    Hreceipt Hbinding _ old _ Hlife Hactive Hold) as [same_node [Hsame_node [Hgen Hptr]]].
  assert (same_node = node) by congruence; subst same_node.
  exists node; exact (conj Hnode (conj Htrace (conj Hgen Hptr))).
Qed.
