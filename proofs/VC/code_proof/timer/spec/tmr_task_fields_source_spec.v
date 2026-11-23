Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Ucos2Verify.lib.timer Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.task Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.tick.
Require Import Ucos2Verify.VC.code.core.spec.kernel_client_resumption.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_lock_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_effect_properties_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_phase_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_legacy_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_lock_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_continuation_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_sw_hook_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_acquire_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_checkpoint_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Import TaskStateDef.
Local Open Scope Z_scope.

(** Initialization at the actual returning source boundary.

    Save/Restore source histories and selected C sequences already carry
    timer_public_trace. The existing timer_public_trace_public_storage_frame
    and timer_public_storage_frame_initialized consume that evidence here.
    No ready-state, endpoint world, application callback, or new platform
    law is substituted for a source history.

    One older source constructor still consumes kernel_client_trace, which
    does NOT contain a Timer projection. Its remaining obligation is the
    following property of each registered action's ACTUAL step relation.
    It is not a new OSTmr_Task Require. An environment linking proof must
    establish it from those registered bodies. KernelClientCertificate and
    sem_pend_projected_source_client alone do not establish it. *)
Definition tmr_task_fields_action_preserves_initialized sg
  (action : KernelClientAction) : Prop :=
  forall before after, kernel_client_step action sg before after ->
    timer_api_initialized before.(TimerState) ->
    timer_api_initialized after.(TimerState).

Lemma tmr_task_fields_action_initialized_from_timer_frame : forall sg action,
  (forall before after, kernel_client_step action sg before after ->
    after.(TimerState) = before.(TimerState)) ->
  tmr_task_fields_action_preserves_initialized sg action.
Proof.
  intros sg action Hframe before after Hstep Hinit.
  rewrite (Hframe before after Hstep); exact Hinit.
Qed.

Lemma tmr_task_fields_action_initialized_from_timer_trace : forall sg action,
  (forall before after, kernel_client_step action sg before after ->
    timer_public_trace sg before.(TimerState) after.(TimerState)) ->
  tmr_task_fields_action_preserves_initialized sg action.
Proof.
  intros sg action Hsource before after Hstep Hinit.
  eapply timer_public_storage_frame_initialized; [|exact Hinit].
  eapply timer_public_trace_public_storage_frame; exact (Hsource before after Hstep).
Qed.

(** The configured Scheduler hook has a checked identity body. This is a
    concrete producer for that action only, not a property of arbitrary
    Timer callbacks or arbitrary external hooks. *)
Lemma tmr_task_fields_bound_hook_preserves_initialized : forall sg external,
  task_sw_hook_source_binding external ->
  tmr_task_fields_action_preserves_initialized sg external.(os_sched_hook_action).
Proof.
  intros sg external Hbinding.
  apply tmr_task_fields_action_initialized_from_timer_frame.
  intros before after Hstep.
  unfold task_sw_hook_source_binding in Hbinding; rewrite Hbinding in Hstep.
  change (after = before) in Hstep; subst after; reflexivity.
Qed.

Lemma tmr_task_fields_client_trace_preserves_initialized :
  forall clients sg observer event_observer before stopped after,
  (forall action, clients action -> tmr_task_fields_action_preserves_initialized sg action) ->
  kernel_client_resource_trace clients sg observer event_observer before stopped after ->
  timer_api_initialized before.(TimerState) -> timer_api_initialized after.(TimerState).
Proof.
  intros clients sg observer event_observer before stopped after Hclients Htrace.
  induction Htrace as [state|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intro Hinit.
  - exact Hinit.
  - apply IH; exact (Hclients action Hin before middle Hstep Hinit).
Qed.

Lemma tmr_task_fields_sched_switch_preserves_initialized : forall external sg entry call installed,
  tmr_task_fields_action_preserves_initialized sg external.(os_sched_hook_action) ->
  os_sched_switch_source external sg entry call installed ->
  timer_api_initialized entry.(TimerState) -> timer_api_initialized installed.(TimerState).
Proof.
  intros external sg entry call installed Hhook
    [_ (sp & saved & hooked & incoming & resumed & Hsave & Hstep & Hdestination & Hinstalled)] Hinit.
  subst installed.
  change (timer_api_initialized hooked.(TimerState)).
  eapply Hhook; [exact Hstep|exact Hinit].
Qed.

Lemma tmr_task_fields_sched_c_return_preserves_initialized :
  forall external critical sg entry call returned current,
  (forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action) ->
  tmr_task_fields_action_preserves_initialized sg external.(os_sched_hook_action) ->
  os_sched_c_return external critical sg entry call returned current ->
  timer_api_initialized entry.(TimerState) -> timer_api_initialized current.(TimerState).
Proof.
  intros external critical sg entry call returned current Hclients Hhook Hreturn Hinit.
  unfold os_sched_c_return in Hreturn; destruct (os_sched_requests_switch entry).
  - destruct Hreturn as [installed [Hswitch [[stopped [Htrace Hnormal]] Hreturned]]].
    eapply tmr_task_fields_client_trace_preserves_initialized;
      [exact Hclients|exact Htrace|].
    eapply tmr_task_fields_sched_switch_preserves_initialized; eassumption.
  - destruct Hreturn as [_ ->]; exact Hinit.
Qed.

Lemma tmr_task_fields_pend_save_timer_trace : forall environment critical sg
  original before returned acquired,
  sem_pend_save_call_history environment critical sg original before returned acquired ->
  timer_public_trace sg before.(TimerState) acquired.(TimerState).
Proof.
  intros environment critical sg original before returned acquired [Hhistory|[Hsource Hnormal]].
  - exact (proj2 (ContinuationEffectProjections.kernel_call_save_history_name_timer
      environment critical sg original before returned acquired Hhistory)).
  - exact (proj2 (ContinuationEffectProjections.kernel_resumption_task_source_name_timer
      _ _ critical _ _ _ _ _ _ _ _ Hsource)).
Qed.

Lemma tmr_task_fields_pend_restore_timer_trace : forall environment critical sg
  original released returned current,
  sem_pend_restore_call_history environment critical sg original released returned current ->
  timer_public_trace sg released.(TimerState) current.(TimerState).
Proof.
  intros environment critical sg original released returned current [Hhistory|[Hsource Hnormal]].
  - exact (proj2 (ContinuationEffectProjections.kernel_call_restore_history_name_timer
      environment critical sg original released returned current Hhistory)).
  - exact (proj2 (ContinuationEffectProjections.kernel_resumption_task_source_name_timer
      _ _ critical _ _ _ _ _ _ _ _ Hsource)).
Qed.

Lemma tmr_task_fields_pend_first_timer_state_eq : forall sg eid timeout before result after,
  sem_pend_first_critical sg eid timeout before result after ->
  after.(TimerState) = before.(TimerState).
Proof.
  intros sg eid timeout before result after [event [fields [_ [_ Hstep]]]].
  destruct (Z.ltb 0 fields.(semCount)).
  - destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [tid [old [_ [_ [_ ->]]]]]; reflexivity.
Qed.

Lemma tmr_task_fields_pend_cleanup_timer_state_eq : forall sg eid before result after,
  sem_pend_resume_critical sg eid before result after ->
  after.(TimerState) = before.(TimerState).
Proof.
  intros sg eid before result after [tid [old [_ [_ [_ Hstep]]]]].
  destruct old.(statPend).
  - subst after; reflexivity.
  - destruct Hstep as [event [_ ->]]; reflexivity.
  - subst after; reflexivity.
Qed.

(** All twelve existing waiting-history constructors are retained. Only
    CScheduler needs the action premises, because it is the constructor
    whose old os_sched_c_return contains a bare client trace. *)
Lemma tmr_task_fields_pend_wait_preserves_initialized : forall environment critical sg
  original eid generation before after,
  (forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action) ->
  tmr_task_fields_action_preserves_initialized sg
    environment.(task_stack_call_external).(os_sched_hook_action) ->
  sem_pend_wait_source_history environment critical sg original eid generation before after ->
  timer_api_initialized before.(TimerState) -> timer_api_initialized after.(TimerState).
Proof.
  intros environment critical sg original eid generation before after Hclients Hhook Hhistory.
  induction Hhistory; intro Hinit.
  - exact Hinit.
  - eapply timer_public_storage_frame_initialized; [|exact Hinit].
    eapply timer_public_trace_public_storage_frame.
    exact (proj2 (ContinuationEffectProjections.kernel_resumption_task_source_name_timer
      _ _ critical _ _ _ _ _ _ _ _ H)).
  - exact Hinit.
  - exact Hinit.
  - unfold os_int_exit_installed_state; rewrite H; exact Hinit.
  - eapply timer_public_storage_frame_initialized; [|exact Hinit].
    eapply timer_public_trace_public_storage_frame.
    exact (proj2 (ContinuationEffectProjections.kernel_call_save_history_name_timer
      environment critical sg call before returned after H0)).
  - eapply timer_public_storage_frame_initialized; [|exact Hinit].
    eapply timer_public_trace_public_storage_frame.
    exact (proj2 (ContinuationEffectProjections.kernel_call_restore_history_name_timer
      environment critical sg call before returned after H0)).
  - exact Hinit.
  - exact Hinit.
  - eapply timer_public_storage_frame_initialized; [|exact Hinit].
    eapply timer_public_trace_public_storage_frame.
    eapply critical_region_interval_timer_public_trace; exact H0.
  - eapply tmr_task_fields_sched_c_return_preserves_initialized; eassumption.
  - apply IHHhistory2; apply IHHhistory1; exact Hinit.
Qed.

Lemma tmr_task_fields_pend_checkpoint_preserves_initialized : forall environment critical sg
  call pevent timeout before error checkpoint,
  (forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action) ->
  tmr_task_fields_action_preserves_initialized sg
    environment.(task_stack_call_external).(os_sched_hook_action) ->
  sem_pend_checkpoint_result (Some environment) critical sg call pevent timeout before error checkpoint ->
  timer_api_initialized before.(TimerState) -> timer_api_initialized checkpoint.(TimerState).
Proof.
  intros environment critical sg call pevent timeout before error checkpoint Hclients Hhook
    (eid & observed & returned & mask & saved & entry & current & start & waiting &
      Hnonnull & Haddress & Hid & Hslot & Hcontext & Hacquire & Hfirst & Hresult) Hinit.
  change (sem_pend_acquire_observation environment critical sg call returned mask saved
    before entry eid observed current) in Hacquire.
  assert (Hentry : timer_api_initialized entry.(TimerState)).
  { eapply timer_public_storage_frame_initialized; [|exact Hinit].
    eapply timer_public_trace_public_storage_frame.
    eapply tmr_task_fields_pend_save_timer_trace; exact (proj1 Hacquire). }
  assert (Hwaiting : timer_api_initialized waiting.(TimerState)).
  { rewrite (tmr_task_fields_pend_first_timer_state_eq sg eid timeout entry start waiting Hfirst).
    exact Hentry. }
  destruct start as [|tid generation].
  - destruct Hresult as [_ ->]; exact Hwaiting.
  - destruct Hresult as [_ [owned [resumed [node [code
      [Howned [Hwait [_ [_ [_ Hcleanup]]]]]]]]]].
    injection Howned as Howned; subst owned.
    rewrite (tmr_task_fields_pend_cleanup_timer_state_eq sg eid resumed code checkpoint Hcleanup).
    eapply tmr_task_fields_pend_wait_preserves_initialized; eassumption.
Qed.

(** NULL, FREE/wrong type, ISR and locked outcomes take the original early
    branch and return the identical state. Their proof needs no success,
    live event, acquired readiness, or blocking-input assumption. *)
Lemma tmr_task_fields_pend_runtime_preserves_initialized :
  forall external platform environment critical sg call pevent timeout before error current,
  (forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action) ->
  tmr_task_fields_action_preserves_initialized sg
    environment.(task_stack_call_external).(os_sched_hook_action) ->
  sem_pend_runtime_program external platform (Some environment) critical sg call
    pevent timeout before error current ->
  timer_api_initialized before.(TimerState) -> timer_api_initialized current.(TimerState).
Proof.
  intros external platform environment critical sg call pevent timeout before error current
    Hclients Hhook Hrun Hinit.
  destruct Hrun as [[Hearly [Hguard ->]]|
    [checkpoint [entered [returned [eid [Hcheckpoint [_ [_ [_ [_ Hrestore]]]]]]]]]].
  - exact Hinit.
  - eapply timer_public_storage_frame_initialized.
    + eapply timer_public_trace_public_storage_frame.
      eapply tmr_task_fields_pend_restore_timer_trace; exact Hrestore.
    + eapply tmr_task_fields_pend_checkpoint_preserves_initialized; eassumption.
Qed.

Lemma tmr_task_fields_pend_program_preserves_initialized :
  forall environment critical sg call pevent timeout before error current,
  (forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action) ->
  tmr_task_fields_action_preserves_initialized sg
    environment.(task_stack_call_external).(os_sched_hook_action) ->
  sem_pend_fields_program environment critical sg call pevent timeout before error current ->
  timer_api_initialized before.(TimerState) -> timer_api_initialized current.(TimerState).
Proof.
  intros; eapply tmr_task_fields_pend_runtime_preserves_initialized; eassumption.
Qed.

Lemma tmr_task_fields_lock_history_timer_trace : forall environment critical sg
  original mask before returned current,
  os_sched_lock_continuation_history environment critical sg original mask before returned current ->
  timer_public_trace sg before.(TimerState) current.(TimerState).
Proof.
  intros environment critical sg original mask before returned current Hhistory.
  unfold os_sched_lock_continuation_history in Hhistory; destruct before.(SchedState).(isRunning).
  - destruct Hhistory as [entered [acquired [saved [Hsave Hrestore]]]].
    pose proof (proj2 (ContinuationEffectProjections.os_sched_continuation_save_effect_name_timer
      environment critical sg original mask saved before entered acquired Hsave)) as Hfirst.
    pose proof (proj2 (ContinuationEffectProjections.os_sched_continuation_restore_effect_name_timer
      environment critical sg entered (os_sched_lock_checkpoint true acquired) returned current Hrestore))
      as Hlast.
    change (timer_public_trace sg acquired.(TimerState) current.(TimerState)) in Hlast.
    eapply timer_public_trace_trans; eassumption.
  - destruct Hhistory as [_ <-]; constructor.
Qed.

Lemma tmr_task_fields_lock_program_preserves_initialized : forall environment critical sg
  original mask before returned current,
  os_sched_lock_continuation_program environment critical sg original mask before returned current ->
  timer_api_initialized before.(TimerState) -> timer_api_initialized current.(TimerState).
Proof.
  intros environment critical sg original mask before returned current Hrun Hinit.
  eapply timer_public_storage_frame_initialized; [|exact Hinit].
  eapply timer_public_trace_public_storage_frame.
  eapply tmr_task_fields_lock_history_timer_trace.
  apply (proj1 (os_sched_lock_continuation_program_iff
    environment critical sg original mask before returned current)); exact Hrun.
Qed.

Lemma tmr_task_fields_unlock_prefix_timer_trace : forall environment critical sg
  original mask before acquired restored unlocked,
  os_sched_unlock_continuation_prefix environment critical sg original mask
    before acquired restored unlocked ->
  timer_public_trace sg before.(TimerState) unlocked.(TimerState).
Proof.
  intros environment critical sg original mask before acquired restored unlocked
    [_ [entered [saved [Hsave Hrestore]]]].
  pose proof (proj2 (ContinuationEffectProjections.os_sched_continuation_save_effect_name_timer
    environment critical sg original mask saved before entered acquired Hsave)) as Hfirst.
  pose proof (proj2 (ContinuationEffectProjections.os_sched_continuation_restore_effect_name_timer
    environment critical sg entered (os_sched_unlock_checkpoint true acquired) restored unlocked Hrestore))
    as Hlast.
  change (timer_public_trace sg acquired.(TimerState) unlocked.(TimerState)) in Hlast.
  eapply timer_public_trace_trans; eassumption.
Qed.

(** The legacy heap-indexed phase family has three concrete source edges.
    MutexDel's actual critical result has an existing Timer frame theorem.
    TaskDel's actual environment and Restore/Save window supply their real
    task-source traces. No additional phase-preservation premise is needed. *)
Lemma tmr_task_fields_delete_window_timer_trace : forall environment critical sg
  before initial_heap after final_heap,
  sched_task_delete_window_execution environment critical sg before initial_heap after final_heap ->
  timer_public_trace sg before.(TimerState) after.(TimerState).
Proof.
  intros environment critical sg before initial_heap after final_heap Hsource.
  destruct Hsource as [saved_local requested completed arch restore save original initial
    first acquired priority tid node prepared loan saved cursor initial_heap written
    prefix_heap middle between restore_environment_heap final_cursor middle_heap registers
    returned resumed save_environment_heap final_registers reacquired final_heap frame
    Henv Hprep Hr0 Hmask Hpre Hprefix Hactual_restore Hsuffix_restore Hactual_save
    Hreturn Hvalid Hsave_mask Hsuffix_save].
  destruct (task_delete_prepared_restore_save_window environment critical saved_local
    requested sg completed arch restore save original initial first acquired priority
    tid node prepared loan saved cursor initial_heap written prefix_heap middle between
    restore_environment_heap final_cursor middle_heap registers returned resumed
    save_environment_heap final_registers reacquired final_heap frame Henv Hprep Hr0 Hmask
    Hpre Hprefix Hactual_restore Hsuffix_restore Hactual_save Hreturn Hvalid Hsave_mask Hsuffix_save)
    as [Hreturn_word [Hstate [Hrestore_history [Hsave_history Hrest]]]].
  pose proof (proj2 (ContinuationEffectProjections.kernel_resumption_task_source_name_timer
    _ _ critical _ _ _ _ _ _ _ _ (proj1 Hrestore_history))) as Hfirst.
  pose proof (proj2 (ContinuationEffectProjections.kernel_resumption_task_source_name_timer
    _ _ critical _ _ _ _ _ _ _ _ (proj1 Hsave_history))) as Hlast.
  eapply timer_public_trace_trans; eassumption.
Qed.

Lemma tmr_task_fields_phase_step_timer_trace : forall environment critical sg
  before before_heap after after_heap,
  sched_task_phase_heap_step environment critical sg before before_heap after after_heap ->
  timer_public_trace sg before.(TimerState) after.(TimerState).
Proof.
  intros environment critical sg before before_heap after after_heap Hsource; destruct Hsource.
  - destruct (sched_task_mutex_del_always_source_resources environment.(task_stack_call_external)
      sg eid entry prepared event mutex before_heap after_heap frame H H0 H1 H2 H3)
      as [Hphase [Hcritical Howned]].
    pose proof (proj2 (CriticalComponent.mutex_del_critical_name_timer_frame
      _ _ _ _ _ _ Hcritical)) as Htimer.
    rewrite Htimer; constructor.
  - destruct (sched_task_delete_environment_source_resources environment critical saved_local
      requested sg completed phase loan original before returned after mask before_heap
      after_heap frame H) as [Htrace Hrest].
    exact (proj2 (ContinuationEffectProjections.kernel_resumption_task_source_name_timer
      _ _ critical _ _ _ _ _ _ _ _ Htrace)).
  - eapply tmr_task_fields_delete_window_timer_trace; exact H.
Qed.

Lemma tmr_task_fields_phase_source_timer_trace : forall environment critical sg
  before before_heap after after_heap,
  sched_task_phase_heap_source environment critical sg before before_heap after after_heap ->
  timer_public_trace sg before.(TimerState) after.(TimerState).
Proof.
  intros environment critical sg before before_heap after after_heap Hsource; induction Hsource.
  - constructor.
  - eapply timer_public_trace_trans; [|exact IHHsource].
    eapply tmr_task_fields_phase_step_timer_trace; exact H.
Qed.

Lemma tmr_task_fields_legacy_prefix_preserves_initialized : forall environment critical sg
  observer before current final_heap,
  (forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action) ->
  LegacyTaskReturnPrefix.os_sched_task_return_prefix environment critical sg observer
    before current final_heap ->
  timer_api_initialized before.(TimerState) -> timer_api_initialized current.(TimerState).
Proof.
  intros environment critical sg observer before current final_heap Hclients Hprefix Hinit.
  destruct Hprefix.
  - eapply tmr_task_fields_client_trace_preserves_initialized; eassumption.
  - eapply timer_public_storage_frame_initialized; [|exact Hinit].
    eapply timer_public_trace_public_storage_frame.
    eapply tmr_task_fields_phase_source_timer_trace; exact H.
Qed.

Lemma tmr_task_fields_sched_prefix_preserves_initialized : forall environment critical sg
  observer before current final_heap,
  (forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action) ->
  SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer
    before current final_heap ->
  timer_api_initialized before.(TimerState) -> timer_api_initialized current.(TimerState).
Proof.
  intros environment critical sg observer before current final_heap Hclients Hprefix Hinit.
  destruct Hprefix.
  - eapply tmr_task_fields_legacy_prefix_preserves_initialized; eassumption.
  - pose proof (SelectedCSource.kernel_program_selected_c_sequence_source_frames
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as [_ [_ [_ Htimer]]].
    eapply timer_public_storage_frame_initialized; [|exact Hinit].
    eapply timer_public_trace_public_storage_frame; exact Htimer.
Qed.

Lemma tmr_task_fields_sched_irq_prefix_preserves_initialized : forall environment critical sg
  observer before current,
  (forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action) ->
  SchedulerPhaseCandidate.os_sched_task_irq_return_prefix environment critical sg observer before current ->
  timer_api_initialized before.(TimerState) -> timer_api_initialized current.(TimerState).
Proof.
  intros environment critical sg observer before current Hclients [Hclients_trace|[final_heap Hprefix]] Hinit.
  - eapply tmr_task_fields_client_trace_preserves_initialized; eassumption.
  - eapply tmr_task_fields_sched_prefix_preserves_initialized; eassumption.
Qed.

Lemma tmr_task_fields_irq_transfer_preserves_initialized : forall external port sg handler entry transfer,
  tmr_task_fields_action_preserves_initialized sg external.(os_sched_hook_action) ->
  os_int_exit_transfer_source external port sg handler entry transfer ->
  timer_api_initialized entry.(TimerState) ->
  timer_api_initialized (os_int_exit_installed_state transfer).(TimerState).
Proof.
  intros external port sg handler entry transfer Hhook [_ [_ [_ [Hstep Hrest]]]] Hinit.
  change (timer_api_initialized transfer.(os_int_exit_hooked_state).(TimerState)).
  eapply Hhook; [exact Hstep|exact Hinit].
Qed.

Lemma tmr_task_fields_sched_body_preserves_initialized : forall environment critical sg
  entry original returned current,
  (forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action) ->
  tmr_task_fields_action_preserves_initialized sg
    environment.(task_stack_call_external).(os_sched_hook_action) ->
  SchedulerPhaseCandidate.os_sched_task_body_source environment critical sg entry original returned current ->
  timer_api_initialized entry.(TimerState) -> timer_api_initialized current.(TimerState).
Proof.
  intros environment critical sg entry original returned current Hclients Hhook Hbody Hinit.
  destruct Hbody.
  - exact Hinit.
  - change (timer_api_initialized hooked.(TimerState)).
    eapply tmr_task_fields_sched_prefix_preserves_initialized; [exact Hclients|exact H0|].
    eapply tmr_task_fields_sched_switch_preserves_initialized; eassumption.
  - eapply tmr_task_fields_irq_transfer_preserves_initialized; [exact Hhook|exact H2|].
    eapply tmr_task_fields_sched_irq_prefix_preserves_initialized; [exact Hclients|exact H0|].
    eapply tmr_task_fields_sched_switch_preserves_initialized; eassumption.
  - eapply tmr_task_fields_sched_switch_preserves_initialized; [exact Hhook|exact H2|].
    eapply tmr_task_fields_sched_prefix_preserves_initialized; [exact Hclients|exact H0|].
    eapply tmr_task_fields_sched_switch_preserves_initialized; eassumption.
Qed.

Lemma tmr_task_fields_sched_program_preserves_initialized : forall environment critical sg
  original mask before returned current,
  (forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action) ->
  tmr_task_fields_action_preserves_initialized sg
    environment.(task_stack_call_external).(os_sched_hook_action) ->
  SchedulerPhaseCandidate.os_sched_task_program environment critical sg original mask before returned current ->
  timer_api_initialized before.(TimerState) -> timer_api_initialized current.(TimerState).
Proof.
  intros environment critical sg original mask before returned current Hclients Hhook Hrun Hinit.
  apply (proj1 (SchedulerPhaseCandidate.os_sched_task_program_iff
    environment critical sg original mask before returned current)) in Hrun.
  destruct Hrun as [scheduled [entry [resumed [released [saved [Hsave [Hbody Hrestore]]]]]]].
  assert (Hentry : timer_api_initialized entry.(TimerState)).
  { eapply timer_public_storage_frame_initialized; [|exact Hinit].
    eapply timer_public_trace_public_storage_frame.
    exact (proj2 (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect_name_timer
      environment critical sg original mask saved before scheduled entry Hsave)). }
  assert (Hreleased : timer_api_initialized released.(TimerState)).
  { eapply tmr_task_fields_sched_body_preserves_initialized; eassumption. }
  eapply timer_public_storage_frame_initialized; [|exact Hreleased].
  eapply timer_public_trace_public_storage_frame.
  exact (proj2 (ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect_name_timer
    environment critical sg resumed released returned current Hrestore)).
Qed.

(** Unlock's real scheduled tail selects task_sw_hook_call_environment.
    Its hook obligation therefore has the concrete producer above. The
    remaining clients premise belongs only to the old raw trace branch;
    the selected C sequence and all three legacy phase edges are proved. *)
Lemma tmr_task_fields_unlock_program_preserves_initialized : forall environment critical sg
  original mask before returned current,
  (forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action) ->
  os_sched_unlock_continuation_program environment critical sg original mask before returned current ->
  timer_api_initialized before.(TimerState) -> timer_api_initialized current.(TimerState).
Proof.
  intros environment critical sg original mask before returned current Hclients Hrun Hinit.
  apply (proj1 (os_sched_unlock_continuation_program_iff
    environment critical sg original mask before returned current)) in Hrun.
  unfold os_sched_unlock_continuation_history in Hrun; destruct before.(SchedState).(isRunning).
  - destruct Hrun as [acquired [restored [unlocked [Hprefix Htail]]]].
    assert (Hunlocked : timer_api_initialized unlocked.(TimerState)).
    { eapply timer_public_storage_frame_initialized; [|exact Hinit].
      eapply timer_public_trace_public_storage_frame.
      eapply tmr_task_fields_unlock_prefix_timer_trace; exact Hprefix. }
    unfold os_sched_unlock_tail_program in Htail; destruct (os_sched_unlock_requests acquired).
    + eapply tmr_task_fields_sched_program_preserves_initialized;
        [exact Hclients| |exact Htail|exact Hunlocked].
      apply tmr_task_fields_bound_hook_preserves_initialized.
      apply task_sw_hook_call_environment_source_binding.
    + destruct Htail as [_ Hcurrent]; subst current; exact Hunlocked.
  - destruct Hrun as [_ <-]; exact Hinit.
Qed.

(** Concrete Task consumers use the kernel projection of the same actual
    program, preserving the returned call descriptor and application pair.
    These are pure source consequences alongside the existing same-X rules;
    they neither replace safeExec nor manufacture a callback proof. *)



(** Integration status of this independent candidate:

    * E3 now retains initialization of the old world in the C assertion,
      including both sides of the following Lock resource split.
    * E4 can transport it to waited and locked using the two Task consumers
      above once the actual Pend CScheduler action properties are linked.
      Lock itself has no new environment premise.
    * E13 can transport initialization through actual Unlock to its current
      returned world once the registered raw-client property is linked.
    * For Pend's generic environment the configured hook binding must also
      be supplied from its actual selected implementation. Unlock already
      selects that implementation and discharges this item internally.
    * KernelClientCertificate, ready/current facts, the C pointer type, and
      a normal-return owner do not imply either missing action property.
      In particular SemPendSourceTaskEventRunningFrame leaves TimerState
      unrestricted. Registering an application/kernel action requires its
      body proof; this file does not add that proof to a public Require.

    The callback registry, next-Pend admission/handle ownership, Scheduler
    Fresh/source producers, and all generated manual VCs remain separate.
    This file has proof scripts but has not been compiled in this batch. *)

(** Concrete registration producers. Membership below identifies the
    existing named source action, not an assertion about all future worlds.
    In particular the proof of sched_task_source_client uses none of the
    ready/resource fields packaged by sched_task_registered_client. *)
Lemma tmr_task_fields_nontimer_source_preserves_initialized : forall sg action,
  kernel_nontimer_source_client action ->
  tmr_task_fields_action_preserves_initialized sg action.
Proof.
  intros sg action Hsource; apply tmr_task_fields_action_initialized_from_timer_frame.
  intros before after Hstep.
  eapply kernel_nontimer_source_client_timer_state_eq; eassumption.
Qed.

Lemma tmr_task_fields_sched_source_timer_state_eq : forall external action sg before after,
  sched_task_source_client external action -> kernel_client_step action sg before after ->
  after.(TimerState) = before.(TimerState).
Proof.
  intros external action sg before after Hsource; destruct Hsource; intro Hstep.
  - eapply kernel_nontimer_source_client_timer_state_eq; eassumption.
  - destruct Hstep as [_ ->]; destruct cut; reflexivity.
  - destruct Hstep as [code Hcritical].
    symmetry; exact (proj2 (CriticalComponent.task_change_prio_critical_current_timer_frame
      sg requested priority before code after Hcritical)).
  - destruct Hstep as [schedule Hready].
    destruct (flag_task_rdy_result sg before pointer bits result schedule after Hready)
      as [waiter [flags [old [_ [_ [-> Hschedule]]]]]].
    reflexivity.
  - destruct Hstep as [priority Hready].
    symmetry; exact (proj2 (CriticalComponent.mutex_del_wake_name_timer_frame
      sg before eid kind message result priority after Hready)).
  - destruct Hstep as [_ ->].
    exact (f_equal TimerState (tick_task_step_non_task_sched_state_eq sg slot old before)).
  - pose proof (os_sched_install_client_state_frame external context outgoing incoming resumed
      sg before after Hstep) as (Hused & Hlife & Hevents & Hrunning & Hints & Hname & Htimer).
    exact Htimer.
Qed.

Lemma tmr_task_fields_sched_source_preserves_initialized : forall external sg action,
  sched_task_source_client external action ->
  tmr_task_fields_action_preserves_initialized sg action.
Proof.
  intros external sg action Hsource; apply tmr_task_fields_action_initialized_from_timer_frame.
  intros before after Hstep; eapply tmr_task_fields_sched_source_timer_state_eq; eassumption.
Qed.

Lemma tmr_task_fields_registered_source_preserves_initialized : forall external sg action,
  sched_task_registered_client external action ->
  tmr_task_fields_action_preserves_initialized sg action.
Proof.
  intros external sg action [Hsource Hcertificate].
  eapply tmr_task_fields_sched_source_preserves_initialized; exact Hsource.
Qed.

(** This consumes the EXACT region whose definition registers those named
    actions. It does not transport a trace from an arbitrary old critical
    region, and it does not use sched_task_source_region_ready_clients. *)
Lemma tmr_task_fields_source_region_clients_preserve_initialized : forall external resources sg,
  forall action, (sched_task_source_region external resources).(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action.
Proof.
  intros external resources sg action Hregistered.
  change (sched_task_registered_client external action) in Hregistered.
  eapply tmr_task_fields_registered_source_preserves_initialized; exact Hregistered.
Qed.

(** For an already chosen region the remaining linking fact is source
    classification of its actual registered actions. This is weaker than
    replacing the region or supplying a full endpoint/future-wait law. *)
Lemma tmr_task_fields_named_clients_preserve_initialized : forall external critical sg,
  (forall action, critical.(critical_region_clients) action -> sched_task_source_client external action) ->
  forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action.
Proof.
  intros external critical sg Hsource action Hregistered.
  eapply tmr_task_fields_sched_source_preserves_initialized; exact (Hsource action Hregistered).
Qed.



(** Actual Timer public source endpoints. Existing source-composition
    theorems supply the trace; no callback behavior is inferred. Start and
    Del include their error alternatives, and Stop/expire stop at dispatch
    before the requested arbitrary callback. There is currently no named
    KernelClientAction/registration constructor for these four endpoints in
    sched_task_source_client. These lemmas do not invent that dispatcher
    binding or identify an entire callback with its dispatch prefix. *)
Lemma tmr_task_fields_timer_start_preserves_initialized : forall sg before i ret err after,
  timer_start_locked sg before i = Some (ret, err, after) ->
  timer_api_initialized before -> timer_api_initialized after.
Proof.
  intros sg before i ret err after Hsource Hinit.
  eapply timer_public_storage_frame_initialized; [|exact Hinit].
  eapply timer_public_trace_public_storage_frame.
  eapply timer_start_locked_public_trace; exact Hsource.
Qed.

Lemma tmr_task_fields_timer_stop_dispatch_preserves_initialized :
  forall sg before i opt arg ret err request after,
  timer_stop_dispatch sg before i opt arg = Some (ret, err, request, after) ->
  timer_api_initialized before -> timer_api_initialized after.
Proof.
  intros sg before i opt arg ret err request after Hsource Hinit.
  eapply timer_public_storage_frame_initialized; [|exact Hinit].
  eapply timer_public_trace_public_storage_frame.
  eapply timer_stop_dispatch_public_trace; exact Hsource.
Qed.

Lemma tmr_task_fields_timer_delete_preserves_initialized : forall sg before i name ret err after,
  timer_delete_locked sg before i name = Some (ret, err, after) ->
  timer_api_initialized before -> timer_api_initialized after.
Proof.
  intros sg before i name ret err after Hsource Hinit.
  eapply timer_public_storage_frame_initialized; [|exact Hinit].
  eapply timer_public_trace_public_storage_frame.
  eapply timer_delete_locked_public_trace; exact Hsource.
Qed.

Lemma tmr_task_fields_timer_expire_dispatch_preserves_initialized :
  forall sg before i next request after,
  timer_expire_dispatch sg before i = Some (next, request, after) ->
  timer_api_initialized before -> timer_api_initialized after.
Proof.
  intros sg before i next request after Hsource Hinit.
  eapply timer_public_storage_frame_initialized; [|exact Hinit].
  eapply timer_public_trace_public_storage_frame.
  eapply timer_expire_dispatch_public_trace; exact Hsource.
Qed.

(** Remaining registration boundary after the named producers above:

    The current Task/fields APIs still quantify over critical; no actual
    source-family membership for every critical_region_clients action has
    been connected at their entry. sched_task_source_region proves its
    own registration only. The original traces cannot be relabelled as
    that region without the actual module dispatch/source binding.

    The thirteen nontimer sources and all seven Scheduler source cases
    are covered here. The separate SemPend projected family also contains
    named Post/Abort/delay-resume/tick cuts and a generic
    SemPendSourceTaskEventRunningFrame case; those are not automatically
    members of sched_task_source_client. Timer public dispatch endpoints
    above likewise require a real registration edge, and their callback
    suffixes keep the explicitly proved callback body contract.

    Thus the remaining task is the existing kernel dispatch/link layer's
    source coverage, plus Pend's configured hook binding. No new Task
    public premise, filtering of real actions, C edit, or axiom was added. *)
