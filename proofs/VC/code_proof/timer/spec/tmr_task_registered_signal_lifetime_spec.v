Require Import Coq.Lists.List Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_registered_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_signal_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_delete_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_protocol_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_handle_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_repaired_scan_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_pend_abort_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_api_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_sw_hook_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_legacy_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_callee_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.queue_core Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Import SchedulerPhaseCandidate SelectedCProgram SelectedCSource.
Import SchedulerCalleePhaseComponent.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** One CURRENT public semaphore incarnation.  The last two facts are
    projections of the existing Event pool partition.  They carry no heap
    copy, future-step obligation, stable-ready premise or observer change. *)
Definition tmr_task_signal_public_slot (events : Glob_EventAbstractState)
  (eid : EventID) (generation : nat) : Prop :=
  exists node, events.(inUsedEventStates) eid = Some node /\
    node.(eventGeneration) = generation /\ node.(eventType) = OS_EVENT_TYPE_SEM /\
    events.(eventLifecycle).(eventPrivate) eid = None /\
    ~ In eid events.(unUsedEventStates).

Lemma tmr_task_signal_public_slot_from_pool : forall sg events eid node,
  event_pool_partition sg events -> events.(inUsedEventStates) eid = Some node ->
  node.(eventType) = OS_EVENT_TYPE_SEM ->
  tmr_task_signal_public_slot events eid node.(eventGeneration).
Proof.
  intros sg events eid node Hpool Hnode Hsem.
  destruct (event_pool_used_not_free sg events eid node Hpool Hnode)
    as [_ [Hfree Hprivate]].
  exists node; repeat split; assumption || reflexivity.
Qed.

Lemma tmr_task_signal_public_slot_live_frame : forall before after eid generation,
  tmr_task_live_sem_identity before after ->
  after.(EventState).(eventLifecycle).(eventPrivate) =
    before.(EventState).(eventLifecycle).(eventPrivate) ->
  after.(EventState).(unUsedEventStates) = before.(EventState).(unUsedEventStates) ->
  tmr_task_signal_public_slot before.(EventState) eid generation ->
  tmr_task_signal_public_slot after.(EventState) eid generation.
Proof.
  intros before after eid generation Hidentity Hprivate Hfree
    [previous [Hlookup [Hgeneration [Hsem [Hnone Hnot]]]]].
  destruct (Hidentity eid previous Hlookup Hsem) as [current [Hcurrent [Hgen Htype]]].
  exists current; split; [exact Hcurrent|]. split; [congruence|].
  split; [congruence|]. rewrite Hprivate, Hfree; split; assumption.
Qed.

Lemma tmr_task_signal_public_slot_private_write : forall events selected allocation field value eid generation,
  events.(eventLifecycle).(eventPrivate) selected = Some allocation ->
  tmr_task_signal_public_slot events eid generation ->
  tmr_task_signal_public_slot (event_private_write events selected allocation field value) eid generation.
Proof.
  intros events selected allocation field value eid generation Hselected
    [node [Hnode [Hgen [Hsem [Hprivate Hfree]]]]].
  assert (Hdifferent : eid <> selected) by (intro H; subst selected; congruence).
  exists node; cbn [event_private_write event_set_lifecycle inUsedEventStates
    eventLifecycle eventPrivate unUsedEventStates].
  rewrite kernel_map_set_other by exact Hdifferent; repeat split; assumption.
Qed.

Lemma tmr_task_signal_public_slot_publish : forall events selected allocation node eid generation,
  events.(eventLifecycle).(eventPrivate) selected = Some allocation ->
  tmr_task_signal_public_slot events eid generation ->
  tmr_task_signal_public_slot (event_publish events selected node) eid generation.
Proof.
  intros events selected allocation node eid generation Hselected
    [previous [Hnode [Hgen [Hsem [Hprivate Hfree]]]]].
  assert (Hdifferent : eid <> selected) by (intro H; subst selected; congruence).
  exists previous; cbn [event_publish inUsedEventStates eventLifecycle eventPrivate unUsedEventStates].
  repeat rewrite kernel_map_set_other by exact Hdifferent; repeat split; assumption.
Qed.

Lemma tmr_task_signal_public_slot_detach : forall events selected rest image eid generation,
  events.(unUsedEventStates) = selected :: rest ->
  tmr_task_signal_public_slot events eid generation ->
  tmr_task_signal_public_slot (event_detach_head events selected rest image) eid generation.
Proof.
  intros events selected rest image eid generation Hhead
    [node [Hnode [Hgen [Hsem [Hprivate Hfree]]]]].
  assert (Hdifferent : eid <> selected).
  { intro H; subst selected; apply Hfree; rewrite Hhead; left; reflexivity. }
  exists node; cbn [event_detach_head inUsedEventStates eventLifecycle eventPrivate unUsedEventStates].
  rewrite kernel_map_set_other by exact Hdifferent.
  repeat split; try assumption. intro Hin; apply Hfree; rewrite Hhead; right; exact Hin.
Qed.

Lemma tmr_task_signal_public_slot_rollback : forall sg events selected allocation eid generation,
  events.(eventLifecycle).(eventPrivate) selected = Some allocation ->
  tmr_task_signal_public_slot events eid generation ->
  tmr_task_signal_public_slot (event_rollback sg events selected allocation) eid generation.
Proof.
  intros sg events selected allocation eid generation Hselected
    [node [Hnode [Hgen [Hsem [Hprivate Hfree]]]]].
  assert (Hdifferent : eid <> selected) by (intro H; subst selected; congruence).
  exists node; cbn [event_rollback inUsedEventStates eventLifecycle eventPrivate unUsedEventStates].
  rewrite kernel_map_set_other by exact Hdifferent.
  repeat split; try assumption. simpl; intuition congruence.
Qed.

Lemma tmr_task_signal_public_slot_queue_reserve : forall events selected allocation qid eid generation,
  events.(eventLifecycle).(eventPrivate) selected = Some allocation ->
  tmr_task_signal_public_slot events eid generation ->
  tmr_task_signal_public_slot (queue_reserve_control_block events selected allocation qid) eid generation.
Proof.
  intros events selected allocation qid eid generation Hselected
    [node [Hnode [Hgen [Hsem [Hprivate Hfree]]]]].
  assert (Hdifferent : eid <> selected) by (intro H; subst selected; congruence).
  exists node; cbn [queue_reserve_control_block event_set_lifecycle inUsedEventStates
    eventLifecycle eventPrivate unUsedEventStates].
  rewrite kernel_map_set_other by exact Hdifferent; repeat split; assumption.
Qed.

Lemma tmr_task_signal_public_slot_queue_publish : forall events selected allocation node qid slots eid generation,
  events.(eventLifecycle).(eventPrivate) selected = Some allocation ->
  tmr_task_signal_public_slot events eid generation ->
  tmr_task_signal_public_slot (queue_publish events selected node qid slots) eid generation.
Proof.
  intros events selected allocation node qid slots eid generation Hselected Hslot.
  change (tmr_task_signal_public_slot (event_publish events selected node) eid generation).
  eapply tmr_task_signal_public_slot_publish; eassumption.
Qed.

Lemma tmr_task_signal_public_slot_event_ready : forall sg before selected kind message result priority after eid generation,
  event_task_rdy sg before selected kind message result = Some (priority, after) ->
  tmr_task_signal_public_slot before.(EventState) eid generation ->
  tmr_task_signal_public_slot after.(EventState) eid generation.
Proof.
  intros sg before selected kind message result priority after eid generation Hstep Hslot.
  eapply tmr_task_signal_public_slot_live_frame; [eapply tmr_task_event_ready_source_preserves_live_sem; exact Hstep| | |exact Hslot].
  all: unfold event_task_rdy in Hstep;
    destruct (before.(EventState).(inUsedEventStates) selected) as [node|]; [|discriminate];
    destruct (before.(TskState).(prioTbl) (event_wait_priority before.(TskState) node))
      as [| |tid]; try discriminate;
    destruct (before.(TskState).(inUsedTaskStates) tid); [|discriminate];
    inversion Hstep; reflexivity.
Qed.

Lemma tmr_task_signal_public_slot_broadcast : forall sg selected kind message result before priorities after eid generation,
  event_broadcast sg selected kind message result before priorities after ->
  tmr_task_signal_public_slot before.(EventState) eid generation ->
  tmr_task_signal_public_slot after.(EventState) eid generation.
Proof.
  intros sg selected kind message result before priorities after eid generation Hsource.
  induction Hsource; intro Hslot; [exact Hslot|].
  apply IHHsource; eapply tmr_task_signal_public_slot_event_ready; eassumption.
Qed.

Lemma tmr_task_signal_public_slot_recycle_other : forall sg events selected image eid generation,
  eid <> selected -> tmr_task_signal_public_slot events eid generation ->
  tmr_task_signal_public_slot (event_recycle sg events selected image) eid generation.
Proof.
  intros sg events selected image eid generation Hdifferent
    [node [Hnode [Hgen [Hsem [Hprivate Hfree]]]]].
  exists node; cbn [event_recycle inUsedEventStates eventLifecycle eventPrivate unUsedEventStates].
  rewrite kernel_map_set_other by exact Hdifferent.
  repeat split; try assumption. simpl; intuition congruence.
Qed.

Lemma tmr_task_signal_public_slot_mutex_delete : forall sg selected option before result after eid generation,
  mutex_del_critical sg selected option before result after ->
  tmr_task_signal_public_slot before.(EventState) eid generation ->
  tmr_task_signal_public_slot after.(EventState) eid generation.
Proof.
  intros sg selected option before result after eid generation
    [event [mutex [Hselected [Htype [Hfields Hsource]]]]] Hslot.
  assert (Hdifferent : eid <> selected).
  { destruct Hslot as [node [Hnode [_ [Hsem _]]]].
    intro H; subst selected; assert (node = event) by congruence; subst; congruence. }
  assert (Hprepared : forall prepared, mutex_del_prepare sg mutex before prepared ->
    tmr_task_signal_public_slot prepared.(EventState) eid generation).
  { intros prepared Hprepare; rewrite (mutex_del_prepare_event_state_eq sg mutex before prepared Hprepare); exact Hslot. }
  destruct (Z.eq_dec option 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
    + destruct Hsource as [prepared [Hprepare [-> Hresult]]].
      apply tmr_task_signal_public_slot_recycle_other; [exact Hdifferent|apply Hprepared; exact Hprepare].
    + destruct Hsource as [-> Hresult]; exact Hslot.
  - destruct (Z.eq_dec option 1).
    + destruct Hsource as [prepared [priorities [drained [Hprepare [Hbroadcast [-> Hresult]]]]]].
      apply tmr_task_signal_public_slot_recycle_other; [exact Hdifferent|].
      eapply tmr_task_signal_public_slot_broadcast; [exact Hbroadcast|apply Hprepared; exact Hprepare].
    + destruct Hsource as [-> Hresult]; exact Hslot.
Qed.

Lemma tmr_task_signal_public_slot_count : forall state selected event count eid generation,
  mutex_query_lookup state selected event ->
  tmr_task_signal_public_slot state.(EventState) eid generation ->
  tmr_task_signal_public_slot (sem_count_update_state state selected event count).(EventState) eid generation.
Proof.
  intros state selected event count eid generation Hselected Hslot.
  eapply tmr_task_signal_public_slot_live_frame with (before := state); [|reflexivity|reflexivity|exact Hslot].
  intros target previous Hlookup Hsem.
  eapply tmr_task_signal_count_update_preserves_identity; eassumption.
Qed.

Lemma tmr_task_signal_public_slot_sem_post : forall sg selected before result after eid generation,
  sem_post_critical sg selected before result after ->
  tmr_task_signal_public_slot before.(EventState) eid generation ->
  tmr_task_signal_public_slot after.(EventState) eid generation.
Proof.
  intros sg selected before result after eid generation [event [Hlookup Hsource]] Hslot.
  destruct (Z.eqb (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
  - destruct Hsource as [fields [_ Hsource]].
    destruct (Z.ltb fields.(semCount) 65535); destruct Hsource as [_ ->]; [|exact Hslot].
    eapply tmr_task_signal_public_slot_count; eassumption.
  - destruct Hsource as [_ [priority Hready]].
    eapply tmr_task_signal_public_slot_event_ready; eassumption.
Qed.

Lemma tmr_task_signal_public_slot_abort : forall sg selected kind option before result after eid generation,
  event_pend_abort_critical sg selected kind option before result after ->
  tmr_task_signal_public_slot before.(EventState) eid generation ->
  tmr_task_signal_public_slot after.(EventState) eid generation.
Proof.
  intros sg selected kind option before result after eid generation [event [Hlookup Hsource]] Hslot.
  destruct (Z.eqb (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
  - destruct Hsource as [_ ->]; exact Hslot.
  - destruct (Z.eqb option 1).
    + destruct Hsource as [priorities [Hbroadcast _]].
      eapply tmr_task_signal_public_slot_broadcast; eassumption.
    + destruct Hsource as [priority [Hready _]].
      eapply tmr_task_signal_public_slot_event_ready; eassumption.
Qed.

Lemma tmr_task_nontimer_source_preserves_signal_public_slot : forall action sg before after eid generation,
  tmr_task_nontimer_source_client action -> kernel_client_step action sg before after ->
  tmr_task_signal_public_slot before.(EventState) eid generation ->
  tmr_task_signal_public_slot after.(EventState) eid generation.
Proof.
  intros action sg before after eid generation Hsource; destruct Hsource; intros Hstep Hslot.
  - destruct Hstep as [_ [_ ->]]; destruct action; exact Hslot.
  - destruct Hstep as [_ ->]; exact Hslot.
  - destruct Hstep as [_ ->]; exact Hslot.
  - destruct Hstep as [_ ->]; exact Hslot.
  - destruct Hstep as [_ ->]; exact Hslot.
  - destruct Hstep as [_ [result Hstep]]. unfold event_create_allocate_critical in Hstep.
    destruct before.(EventState).(unUsedEventStates) as [|selected rest] eqn:Hfree.
    + destruct Hstep as [_ ->]; exact Hslot.
    + destruct Hstep as [image [_ [_ ->]]].
      eapply tmr_task_signal_public_slot_detach; eassumption.
  - destruct Hstep as [Hprivate ->]. eapply tmr_task_signal_public_slot_private_write; eassumption.
  - destruct Hstep as [Hprivate [_ ->]]. eapply tmr_task_signal_public_slot_publish; eassumption.
  - destruct Hstep as [_ [_ [_ [_ [result [actual [Hprivate Hstep]]]]]]].
    destruct free as [|qid rest]; destruct Hstep as [_ ->].
    + eapply tmr_task_signal_public_slot_rollback; eassumption.
    + eapply tmr_task_signal_public_slot_queue_reserve; eassumption.
  - destruct Hstep as [Hprivate [_ [_ [_ ->]]]].
    eapply tmr_task_signal_public_slot_queue_publish; eassumption.
  - destruct Hstep as [_ [result Hstep]].
    rewrite (task_resume_critical_event_frame sg prio before result after Hstep); exact Hslot.
  - destruct Hstep as [event [_ [_ [node [fields [Hnode [_ [_ ->]]]]]]]].
    destruct (Z.ltb 0 fields.(semCount)); [|exact Hslot].
    eapply tmr_task_signal_public_slot_count; eassumption.
Qed.

Lemma tmr_task_change_priority_preserves_signal_public_slot :
  forall sg state selected old oldprio newprio eid generation,
  tmr_task_signal_public_slot state.(EventState) eid generation ->
  tmr_task_signal_public_slot
    (task_change_priority_state sg state selected old oldprio newprio).(EventState) eid generation.
Proof.
  intros sg state selected old oldprio newprio eid generation Hslot.
  eapply tmr_task_signal_public_slot_live_frame;
    [apply tmr_task_change_priority_preserves_live_sem| | |exact Hslot].
  all: cbn [task_change_priority_state replace_SchedS replace_EventS EventState];
    unfold task_change_priority_events;
    destruct old.(eventPtr) as [target|];
    [destruct (state.(EventState).(inUsedEventStates) target)|]; reflexivity.
Qed.

Lemma tmr_task_change_prio_critical_preserves_signal_public_slot :
  forall sg requested priority before result after eid generation,
  task_change_prio_critical sg requested priority before result after ->
  tmr_task_signal_public_slot before.(EventState) eid generation ->
  tmr_task_signal_public_slot after.(EventState) eid generation.
Proof.
  intros sg requested priority before result after eid generation Hstep Hslot.
  unfold task_change_prio_critical in Hstep.
  destruct (before.(TskState).(prioTbl) priority).
  - destruct Hstep as [selected [Hselection Hstep]]. unfold task_change_prio_selected_effect in Hstep.
    destruct (Z.eqb selected sg.(osLowestPrio)); [destruct Hstep as [_ ->]; exact Hslot|].
    destruct (before.(TskState).(prioTbl) selected).
    + destruct Hstep as [_ ->]; exact Hslot.
    + destruct Hstep as [_ ->]; exact Hslot.
    + destruct Hstep as [old [_ [_ ->]]]. apply tmr_task_change_priority_preserves_signal_public_slot; exact Hslot.
  - destruct Hstep as [_ ->]; exact Hslot.
  - destruct Hstep as [_ ->]; exact Hslot.
Qed.

Lemma tmr_task_scheduler_source_preserves_signal_public_slot : forall external action sg before after eid generation,
  tmr_task_scheduler_source_client external action -> kernel_client_step action sg before after ->
  tmr_task_signal_public_slot before.(EventState) eid generation ->
  tmr_task_signal_public_slot after.(EventState) eid generation.
Proof.
  intros external action sg before after eid generation Hsource; destruct Hsource; intros Hstep Hslot.
  - eapply tmr_task_nontimer_source_preserves_signal_public_slot; eassumption.
  - destruct Hstep as [_ ->]; destruct cut; exact Hslot.
  - destruct Hstep as [result Hstep]. eapply tmr_task_change_prio_critical_preserves_signal_public_slot; eassumption.
  - destruct Hstep as [schedule Hready].
    destruct (flag_task_rdy_result sg before pointer bits result schedule after Hready)
      as [waiter [flags [old [_ [_ [-> Hschedule]]]]]]. exact Hslot.
  - destruct Hstep as [priority Hready]. eapply tmr_task_signal_public_slot_event_ready; eassumption.
  - destruct Hstep as [_ ->].
    pose proof (f_equal EventState (tick_task_step_non_task_sched_state_eq sg slot old before)) as Hevents.
    cbn [replace_TskS replace_SchedS EventState] in Hevents; rewrite Hevents; exact Hslot.
  - pose proof (os_sched_install_client_state_frame external context outgoing incoming resumed sg before after Hstep)
      as [_ [_ [Hevents _]]]. rewrite Hevents; exact Hslot.
Qed.

Lemma tmr_task_sem_source_preserves_signal_public_slot : forall action sg before after eid generation,
  tmr_task_sem_source_client action -> kernel_client_step action sg before after ->
  tmr_task_signal_public_slot before.(EventState) eid generation ->
  tmr_task_signal_public_slot after.(EventState) eid generation.
Proof.
  intros action sg before after eid generation Hsource; destruct Hsource; intros Hstep Hslot.
  - destruct Hstep as [old [_ ->]].
    pose proof (f_equal EventState (tick_task_step_non_task_sched_state_eq sg selected old before)) as Hevents.
    cbn [replace_TskS replace_SchedS EventState] in Hevents; rewrite Hevents; exact Hslot.
  - destruct Hstep as [result Hstep]. eapply tmr_task_signal_public_slot_sem_post; eassumption.
  - destruct Hstep as [result Hstep]. eapply tmr_task_signal_public_slot_abort; eassumption.
  - change (after = os_sched_save_current_sp before selected sp) in Hstep; subst after.
    unfold os_sched_save_current_sp; destruct (before.(TskState).(inUsedTaskStates) selected); exact Hslot.
  - destruct Hstep as [_ [result [_ Hstep]]]. destruct (before.(TskState).(prioTbl) priority).
    + destruct Hstep as [_ ->]; exact Hslot.
    + destruct Hstep as [_ ->]; exact Hslot.
    + destruct Hstep as [old [_ Hstep]]. destruct (Z.eqb old.(dly) 0); destruct Hstep as [_ ->]; exact Hslot.
Qed.

Lemma tmr_task_critical_source_preserves_signal_public_slot : forall action sg before after eid generation,
  tmr_task_critical_source_client action -> kernel_client_step action sg before after ->
  tmr_task_signal_public_slot before.(EventState) eid generation ->
  tmr_task_signal_public_slot after.(EventState) eid generation.
Proof.
  intros action sg before after eid generation Hsource; destruct Hsource; intros Hstep Hslot.
  - destruct Hstep as [_ [result [code [request [error [scheduled [Hcritical Hencoding]]]]]]].
    eapply tmr_task_signal_public_slot_mutex_delete; eassumption.
  - destruct Hstep as [result [code [request Hstep]]].
    destruct Hstep.
    + destruct H0 as [error [scheduled [Hcritical [Hcode Hrequest]]]].
      eapply tmr_task_signal_public_slot_mutex_delete; eassumption.
    + exact Hslot.
  - destruct Hstep as [_ [error Hstep]]. eapply tmr_task_change_prio_critical_preserves_signal_public_slot; eassumption.
Qed.

Lemma tmr_task_tick_scan_event_state_eq : forall sg visited before,
  (time_tick_scan sg before visited).(EventState) = before.(EventState).
Proof.
  intros sg visited; induction visited as [|selected rest IH]; intros before; [reflexivity|].
  change ((time_tick_scan sg (time_tick_visit sg before selected) rest).(EventState) = before.(EventState)).
  rewrite IH; unfold time_tick_visit.
  destruct (before.(TskState).(inUsedTaskStates) selected) as [old|]; [|reflexivity].
  exact (f_equal EventState (tick_task_step_non_task_sched_state_eq sg selected old before)).
Qed.

Lemma tmr_task_tick_source_preserves_signal_public_slot : forall sg cut before after eid generation,
  tmr_task_tick_cut_source sg cut before after ->
  tmr_task_signal_public_slot before.(EventState) eid generation ->
  tmr_task_signal_public_slot after.(EventState) eid generation.
Proof.
  intros sg cut before after eid generation; destruct cut; cbn [tmr_task_tick_cut_source]; intros Hstep Hslot.
  - subst after; unfold time_tick_clock_step_state; destruct (tick_step_advance _ _); exact Hslot.
  - subst after; unfold time_tick_serialized_after_hook; destruct (time_tick_process_tasks before).
    + rewrite tmr_task_tick_scan_event_state_eq; unfold time_tick_clock_step_state;
        destruct (tick_step_advance _ _); exact Hslot.
    + unfold time_tick_clock_step_state; destruct (tick_step_advance _ _); exact Hslot.
  - destruct Hstep; try exact Hslot.
    eapply tmr_task_signal_public_slot_sem_post; eassumption.
Qed.

Lemma tmr_task_suspend_call_event_state_eq :
  forall actor source_sg priority result entry returned sg before after,
  kernel_client_step (tmr_task_suspend_call_client actor source_sg priority result entry returned)
    sg before after -> after.(EventState) = before.(EventState).
Proof.
  intros * [_ [_ [_ [Hargument Hsource]]]].
  destruct (task_suspend_idle_guard_original_or_unchanged _ _ _ _ _ Hsource) as [->|Horiginal]; [reflexivity|].
  unfold task_suspend_critical in Horiginal.
  destruct Horiginal as [cid [current [_ [_ [_ Hstep]]]]].
  destruct (before.(TskState).(prioTbl) (fst (task_suspend_selection sg priority current))).
  - destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [node [_ [_ ->]]]; reflexivity.
Qed.

Lemma tmr_task_source_client_preserves_signal_public_slot : forall external action sg before after eid generation,
  tmr_task_source_client external action -> kernel_client_step action sg before after ->
  tmr_task_signal_public_slot before.(EventState) eid generation ->
  tmr_task_signal_public_slot after.(EventState) eid generation.
Proof.
  intros external action sg before after eid generation Hsource; destruct Hsource; intros Hstep Hslot.
  - eapply tmr_task_scheduler_source_preserves_signal_public_slot; eassumption.
  - eapply tmr_task_sem_source_preserves_signal_public_slot; eassumption.
  - eapply tmr_task_critical_source_preserves_signal_public_slot; eassumption.
  - exact (tmr_task_tick_source_preserves_signal_public_slot sg cut before after eid generation Hstep Hslot).
  - destruct Hstep as [timers [_ ->]]; exact Hslot.
  - destruct Hstep as [_ [_ [_ ->]]]; exact Hslot.
  - destruct Hstep as [event [_ [_ Hstep]]]. eapply tmr_task_signal_public_slot_abort; eassumption.
  - rewrite (tmr_task_suspend_call_event_state_eq _ _ _ _ _ _ _ _ _ Hstep); exact Hslot.
Qed.

Lemma tmr_task_timer_cut_signal_value : forall sg cut before after,
  tmr_task_timer_cut_source sg cut before after ->
  after.(timerSignalSem) = before.(timerSignalSem).
Proof.
  intros sg cut before after; destruct cut; cbn [tmr_task_timer_cut_source]; intro Hsource.
  - unfold timer_allocate in Hsource.
    destruct before.(timerFree) as [|slot rest]; [discriminate|].
    destruct (before.(timerImages) slot); [|discriminate]. inversion Hsource; reflexivity.
  - subst after; reflexivity.
  - destruct Hsource as [_ ->]; reflexivity.
  - apply tmr_task_signal_service_value; eapply tmr_task_link_service_frame; exact Hsource.
  - apply tmr_task_signal_service_value; eapply tmr_task_unlink_service_frame; exact Hsource.
  - apply tmr_task_signal_service_value; eapply tmr_task_complete_service_frame; exact Hsource.
  - subst after; reflexivity.
  - eapply tmr_task_signal_public_trace_value; eapply timer_start_locked_public_trace; exact Hsource.
  - eapply tmr_task_signal_public_trace_value; eapply timer_stop_dispatch_public_trace; exact Hsource.
  - eapply tmr_task_signal_public_trace_value; eapply timer_delete_locked_public_trace; exact Hsource.
  - eapply tmr_task_signal_public_trace_value; eapply timer_expire_dispatch_public_trace; exact Hsource.
Qed.

Lemma tmr_task_source_client_signal_value : forall external action sg before after,
  tmr_task_source_client external action -> kernel_client_step action sg before after ->
  after.(TimerState).(timerSignalSem) = before.(TimerState).(timerSignalSem).
Proof.
  intros external action sg before after Hsource; destruct Hsource; intro Hstep.
  - rewrite (tmr_task_fields_sched_source_timer_state_eq external action sg before after
      (tmr_task_scheduler_source_client_original external action H) Hstep); reflexivity.
  - rewrite <- (proj2 (tmr_task_sem_source_client_name_timer_frame action sg before after H Hstep)); reflexivity.
  - destruct H.
    + destruct Hstep as [_ [result [code [request [error [scheduled [Hcritical Hencoding]]]]]]].
      rewrite (proj1 (tmr_task_mutex_delete_critical_signal_frame _ _ _ _ _ _ Hcritical)); reflexivity.
    + destruct Hstep as [result [code [request Hstep]]].
      rewrite <- (proj2 (proj2 (CriticalComponent.mutex_del_critical_call_observation_fields
        _ _ _ _ _ _ _ _ Hstep))); reflexivity.
    + destruct Hstep as [_ [error Hstep]].
      rewrite <- (proj2 (CriticalComponent.task_change_prio_critical_current_timer_frame
        _ _ _ _ _ _ Hstep)); reflexivity.
  - rewrite <- (proj2 (tmr_task_tick_cut_name_timer_frame sg cut before after Hstep)); reflexivity.
  - destruct Hstep as [timers [Hsource ->]]. eapply tmr_task_timer_cut_signal_value; exact Hsource.
  - destruct Hstep as [_ [_ [Hsource ->]]]. eapply tmr_task_timer_cut_signal_value; exact Hsource.
  - destruct Hstep as [event [_ [_ Hstep]]].
    rewrite <- (proj2 (tmr_task_sem_abort_name_timer_frame _ _ _ _ _ _ Hstep)); reflexivity.
  - rewrite <- (proj2 (tmr_task_suspend_call_name_timer_frame _ _ _ _ _ _ _ _ _ Hstep)); reflexivity.
Qed.

(** The original trace, clients, both observer indices, stop bit and
    endpoints are unchanged.  Every actual action is classified by the
    caller's existing registry coverage.  No stable-invariant induction
    or renaming of the excluded actor is used. *)
Lemma tmr_task_registered_trace_preserves_signal_public_slot :
  forall external critical sg observer event_observer before stopped after eid generation,
  tmr_task_registered_source_coverage external critical ->
  kernel_client_resource_trace critical.(critical_region_clients) sg observer event_observer before stopped after ->
  tmr_task_signal_public_slot before.(EventState) eid generation ->
  tmr_task_signal_public_slot after.(EventState) eid generation.
Proof.
  intros external critical sg observer event_observer before stopped after eid generation Hcoverage Htrace.
  induction Htrace as [state|action first middle last stopped Hin Hforeign Hevent Hstep Htail IH]; intro Hslot.
  - exact Hslot.
  - apply IH. eapply tmr_task_source_client_preserves_signal_public_slot;
      [exact (proj1 (Hcoverage action Hin))|exact Hstep|exact Hslot].
Qed.

Lemma tmr_task_registered_trace_signal_value :
  forall external critical sg observer event_observer before stopped after,
  tmr_task_registered_source_coverage external critical ->
  kernel_client_resource_trace critical.(critical_region_clients) sg observer event_observer before stopped after ->
  after.(TimerState).(timerSignalSem) = before.(TimerState).(timerSignalSem).
Proof.
  intros external critical sg observer event_observer before stopped after Hcoverage Htrace.
  induction Htrace as [state|action first middle last stopped Hin Hforeign Hevent Hstep Htail IH]; [reflexivity|].
  rewrite IH. eapply tmr_task_source_client_signal_value; [exact (proj1 (Hcoverage action Hin))|exact Hstep].
Qed.

Lemma tmr_task_registered_trace_preserves_signal_lifetime :
  forall external critical sg observer event_observer invocation before stopped after,
  tmr_task_registered_source_coverage external critical ->
  kernel_client_resource_trace critical.(critical_region_clients) sg observer event_observer before stopped after ->
  event_pool_partition sg before.(EventState) ->
  tmr_task_signal_lifetime critical sg invocation before ->
  tmr_task_signal_lifetime critical sg invocation after.
Proof.
  intros external critical sg observer event_observer invocation before stopped after Hcoverage Htrace Hpool Hlife.
  pose proof (tmr_task_registered_trace_signal_value external critical sg observer event_observer
    before stopped after Hcoverage Htrace) as Hsignal.
  destruct Hlife as [Hnull|[eid [previous [Hnonnull [Haddress [Hid [Hlookup [Hsem Hprotocol]]]]]]]].
  - left; rewrite Hsignal; exact Hnull.
  - pose proof (tmr_task_signal_public_slot_from_pool sg before.(EventState) eid previous Hpool Hlookup Hsem) as Hslot.
    destruct (tmr_task_registered_trace_preserves_signal_public_slot external critical sg observer event_observer
      before stopped after eid previous.(eventGeneration) Hcoverage Htrace Hslot)
      as [current [Hcurrent [Hgeneration [Htype Hrest]]]].
    right; exists eid, current.
    split; [rewrite Hsignal; exact Hnonnull|]. split; [rewrite Hsignal; exact Haddress|].
    split; [exact Hid|]. split; [exact Hcurrent|]. split; assumption.
Qed.

Lemma tmr_task_registered_resumption_preserves_signal_lifetime :
  forall external port critical sg observer event_observer origin invocation before stopped next_origin after,
  tmr_task_registered_source_coverage external critical ->
  kernel_resumption_task_source_trace external port critical.(critical_region_clients) sg
    observer event_observer origin before stopped next_origin after ->
  event_pool_partition sg before.(EventState) ->
  tmr_task_signal_lifetime critical sg invocation before ->
  tmr_task_signal_lifetime critical sg invocation after.
Proof.
  intros external port critical sg observer event_observer origin invocation before stopped next_origin after
    Hcoverage Htrace Hpool Hlife.
  eapply tmr_task_registered_trace_preserves_signal_lifetime; [exact Hcoverage| |exact Hpool|exact Hlife].
  apply kernel_resumption_resource_trace_erases.
  exact (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)).
Qed.

Lemma tmr_task_delete_phase_valid_event_pool : forall phase sg state,
  task_delete_phase_valid phase sg state -> event_pool_partition sg state.(EventState).
Proof.
  intros phase sg state; destruct phase; cbn [task_delete_phase_valid]; intro Hvalid.
  - exact (proj1 (proj1 (proj2 (proj2 (proj2 Hvalid))))).
  - exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj1 Hvalid)))))).
  - exact (proj1 (proj1 (proj2 (proj2 (proj2 Hvalid))))).
Qed.

Lemma tmr_task_delete_closed_event_pool :
  forall environment saved_local phase loan sg call mask state frame,
  task_delete_call_closed environment saved_local phase loan sg call mask state ** frame |--
  coq_prop (event_pool_partition sg state.(EventState)) && TT.
Proof.
  intros; unfold task_delete_call_closed, kernel_continuation_call_closed,
    kernel_continuation_inv, task_delete_phase_resources.
  entailer!; eapply tmr_task_delete_phase_valid_event_pool; eassumption.
Qed.

Lemma tmr_task_delete_masked_event_pool :
  forall environment critical saved_local phase loan sg call saved acquired state frame,
  task_delete_call_masked environment critical saved_local phase loan sg call saved acquired state ** frame |--
  coq_prop (event_pool_partition sg state.(EventState)) && TT.
Proof.
  intros; unfold task_delete_call_masked, kernel_continuation_call_masked,
    kernel_continuation_inv, task_delete_phase_resources.
  entailer!; eapply tmr_task_delete_phase_valid_event_pool; eassumption.
Qed.

Lemma tmr_task_registered_delete_environment_preserves_signal_lifetime :
  forall environment critical saved_local requested sg completed phase loan original before returned after
    mask before_heap after_heap frame invocation,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  sched_task_delete_environment_execution environment critical saved_local requested sg completed
    phase loan original before returned after mask before_heap after_heap frame ->
  tmr_task_signal_lifetime critical sg invocation before ->
  tmr_task_signal_lifetime critical sg invocation after.
Proof.
  intros environment critical saved_local requested sg completed phase loan original before returned after
    mask before_heap after_heap frame invocation Hcoverage Hsource Hlife.
  pose proof Hsource as [Henvironment [Hactual Howned]].
  pose proof (proj1 (tmr_task_delete_closed_event_pool environment saved_local phase loan sg original
    mask before frame before_heap Howned)) as Hpool.
  destruct (sched_task_delete_environment_source_resources environment critical saved_local requested sg completed
    phase loan original before returned after mask before_heap after_heap frame Hsource) as [Htrace Hrest].
  eapply tmr_task_registered_resumption_preserves_signal_lifetime; eassumption.
Qed.

(** Both intervals below are recovered from the SAME original window
    execution and its actual middle heap.  Prepared contributes Event pool
    partition, never the incompatible stable ready invariant. *)
Lemma tmr_task_registered_delete_window_preserves_signal_lifetime :
  forall environment critical sg before before_heap after after_heap invocation,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  sched_task_delete_window_execution environment critical sg before before_heap after after_heap ->
  tmr_task_signal_lifetime critical sg invocation before ->
  tmr_task_signal_lifetime critical sg invocation after.
Proof.
  intros environment critical sg before before_heap after after_heap invocation Hcoverage Hsource Hlife.
  destruct Hsource as [saved_local requested completed arch restore save original initial
    first acquired priority tid node prepared loan saved cursor initial_heap written
    prefix_heap middle between restore_environment_heap final_cursor middle_heap registers
    returned resumed save_environment_heap final_registers reacquired final_heap frame
    Henv Hprep Hr0 Hmask Hpre Hprefix Hactual_restore Hsuffix_restore Hactual_save
    Hreturn Hvalid Hsave_mask Hsuffix_save].
  pose proof (proj1 (tmr_task_delete_masked_event_pool environment critical saved_local
    (TaskDeletePrepared tid node.(taskGeneration)) loan sg first saved acquired
    (task_delete_locked prepared) frame initial_heap Hpre)) as Hpool.
  destruct (task_delete_prepared_restore_save_window environment critical saved_local
    requested sg completed arch restore save original initial first acquired priority
    tid node prepared loan saved cursor initial_heap written prefix_heap middle between
    restore_environment_heap final_cursor middle_heap registers returned resumed
    save_environment_heap final_registers reacquired final_heap frame Henv Hprep Hr0 Hmask
    Hpre Hprefix Hactual_restore Hsuffix_restore Hactual_save Hreturn Hvalid Hsave_mask Hsuffix_save)
    as [Hreturn_word [Hstate [Hrestore_history [Hsave_history Hrest]]]].
  destruct Hrestore_history as [Hrestore_trace [Hrestore_normal [Hrestore_rely Hrestore_transport]]].
  destruct Hsave_history as [Hsave_trace Hsave_rest].
  pose proof (tmr_task_delete_phase_valid_event_pool _ _ _
    (proj1 (proj2 (proj2 Hrestore_rely)))) as Hmiddle_pool.
  eapply tmr_task_registered_resumption_preserves_signal_lifetime;
    [exact Hcoverage|exact Hsave_trace|exact Hmiddle_pool|].
  eapply tmr_task_registered_resumption_preserves_signal_lifetime;
    [exact Hcoverage|exact Hrestore_trace|exact Hpool|exact Hlife].
Qed.

Lemma tmr_task_registered_phase_heap_step_preserves_signal_lifetime :
  forall environment critical sg before before_heap after after_heap invocation,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  sched_task_phase_heap_step environment critical sg before before_heap after after_heap ->
  tmr_task_signal_lifetime critical sg invocation before ->
  tmr_task_signal_lifetime critical sg invocation after.
Proof.
  intros environment critical sg before before_heap after after_heap invocation Hcoverage Hsource Hlife.
  destruct Hsource.
  - eapply (tmr_task_mutex_delete_heap_source_preserves_signal_lifetime environment.(task_stack_call_external)); eassumption.
  - eapply tmr_task_registered_delete_environment_preserves_signal_lifetime; eassumption.
  - eapply tmr_task_registered_delete_window_preserves_signal_lifetime; eassumption.
Qed.

Lemma tmr_task_registered_phase_heap_source_preserves_signal_lifetime :
  forall environment critical sg before before_heap after after_heap invocation,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  sched_task_phase_heap_source environment critical sg before before_heap after after_heap ->
  tmr_task_signal_lifetime critical sg invocation before ->
  tmr_task_signal_lifetime critical sg invocation after.
Proof.
  intros environment critical sg before before_heap after after_heap invocation Hcoverage Hsource.
  induction Hsource; intro Hlife; [exact Hlife|].
  apply IHHsource; eapply tmr_task_registered_phase_heap_step_preserves_signal_lifetime; eassumption.
Qed.

Lemma tmr_task_registered_return_prefix_preserves_signal_lifetime :
  forall environment critical sg observer invocation before after after_heap,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  event_pool_partition sg before.(EventState) ->
  os_sched_task_return_prefix environment critical sg observer before after after_heap ->
  tmr_task_signal_lifetime critical sg invocation before ->
  tmr_task_signal_lifetime critical sg invocation after.
Proof.
  intros environment critical sg observer invocation before after after_heap Hcoverage Hpool Hsource Hlife.
  destruct Hsource.
  - destruct H.
    + eapply tmr_task_registered_trace_preserves_signal_lifetime; eassumption.
    + eapply tmr_task_registered_phase_heap_source_preserves_signal_lifetime; eassumption.
  - eapply tmr_task_live_sem_identity_preserves_lifetime; [exact Hlife| |].
    + eapply tmr_task_signal_public_trace_value.
      exact (proj2 (proj2 (proj2 (kernel_program_selected_c_sequence_source_frames
        _ _ _ _ _ _ _ _ _ _ _ _ _ run H)))).
    + eapply tmr_task_selected_c_sequence_source_preserves_live_sem; exact H.
Qed.

Lemma tmr_task_registered_irq_return_prefix_preserves_signal_lifetime :
  forall environment critical sg observer invocation before after,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  event_pool_partition sg before.(EventState) ->
  os_sched_task_irq_return_prefix environment critical sg observer before after ->
  tmr_task_signal_lifetime critical sg invocation before ->
  tmr_task_signal_lifetime critical sg invocation after.
Proof.
  intros environment critical sg observer invocation before after Hcoverage Hpool [Htrace|[heap Hprefix]] Hlife.
  - eapply tmr_task_registered_trace_preserves_signal_lifetime; eassumption.
  - eapply tmr_task_registered_return_prefix_preserves_signal_lifetime; eassumption.
Qed.

Lemma tmr_task_bound_switch_event_timer_eq : forall external sg entry original installed,
  task_sw_hook_source_binding external -> os_sched_switch_source external sg entry original installed ->
  installed.(EventState) = entry.(EventState) /\ installed.(TimerState) = entry.(TimerState).
Proof.
  intros external sg entry original installed Hbinding
    [Hrequest [sp [saved [hooked [incoming [resumed [Hsave [Hhook [Hdestination Hinstalled]]]]]]]]].
  unfold task_sw_hook_source_binding in Hbinding; rewrite Hbinding in Hhook.
  change (hooked = os_sched_save_current_sp (os_sched_prefix_state entry)
    original.(os_sched_call_stack).(stackLeaseSlot) sp) in Hhook.
  rewrite Hinstalled, Hhook; split; reflexivity.
Qed.

Lemma tmr_task_bound_irq_transfer_event_timer_eq : forall external port sg handler entry transfer,
  task_sw_hook_source_binding external -> os_int_exit_transfer_source external port sg handler entry transfer ->
  (os_int_exit_installed_state transfer).(EventState) = entry.(EventState) /\
  (os_int_exit_installed_state transfer).(TimerState) = entry.(TimerState).
Proof.
  intros external port sg handler entry transfer Hbinding [Hrequest [_ [_ [Hhook Hrest]]]].
  unfold task_sw_hook_source_binding in Hbinding; rewrite Hbinding in Hhook.
  change (transfer.(os_int_exit_hooked_state) = os_int_exit_ready_checkpoint true entry) in Hhook.
  unfold os_int_exit_installed_state; rewrite Hhook; split; reflexivity.
Qed.

Lemma tmr_task_event_timer_eq_preserves_signal_lifetime : forall critical sg invocation before after,
  after.(EventState) = before.(EventState) -> after.(TimerState) = before.(TimerState) ->
  tmr_task_signal_lifetime critical sg invocation before ->
  tmr_task_signal_lifetime critical sg invocation after.
Proof.
  intros critical sg invocation before after Hevents Htimers Hlife.
  eapply tmr_task_live_sem_identity_preserves_lifetime; [exact Hlife|rewrite Htimers; reflexivity|].
  apply tmr_task_event_state_eq_preserves_live_sem; exact Hevents.
Qed.

(** All four ORIGINAL constructors are covered.  Each last install/call
    uses its given source witness; the Legacy and generic TaskDelete
    domains are retained.  The only initial representation fact is the
    current Event pool partition, already in the actual caller's world. *)
Lemma tmr_task_registered_body_source_preserves_signal_lifetime :
  forall environment critical sg entry original returned current,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  task_sw_hook_source_binding environment.(task_stack_call_external) ->
  event_pool_partition sg entry.(EventState) ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) entry ->
  os_sched_task_body_source environment critical sg entry original returned current ->
  tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current.
Proof.
  intros environment critical sg entry original returned current Hcoverage Hbinding Hpool Hlife Hbody.
  destruct Hbody.
  - exact Hlife.
  - destruct (tmr_task_bound_switch_event_timer_eq _ _ _ _ _ Hbinding H) as [Hevents Htimers].
    eapply tmr_task_signal_lifetime_same_call; [exact H5|].
    change (tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) hooked).
    eapply tmr_task_registered_return_prefix_preserves_signal_lifetime;
      [exact Hcoverage|rewrite Hevents; exact Hpool|exact H0|].
    eapply tmr_task_event_timer_eq_preserves_signal_lifetime; eassumption.
  - destruct (tmr_task_bound_switch_event_timer_eq _ _ _ _ _ Hbinding H) as [Hevents Htimers].
    destruct (tmr_task_bound_irq_transfer_event_timer_eq _ _ _ _ _ _ Hbinding H2) as [Hlast_event Hlast_timer].
    eapply tmr_task_signal_lifetime_same_call; [exact H4|].
    eapply tmr_task_event_timer_eq_preserves_signal_lifetime; [exact Hlast_event|exact Hlast_timer|].
    eapply tmr_task_registered_irq_return_prefix_preserves_signal_lifetime;
      [exact Hcoverage|rewrite Hevents; exact Hpool|exact H0|].
    eapply tmr_task_event_timer_eq_preserves_signal_lifetime; eassumption.
  - destruct (tmr_task_bound_switch_event_timer_eq _ _ _ _ _ Hbinding H) as [Hevents Htimers].
    destruct (tmr_task_bound_switch_event_timer_eq _ _ _ _ _ Hbinding H2) as [Hlast_event Hlast_timer].
    eapply tmr_task_signal_lifetime_same_call; [exact H3|].
    eapply tmr_task_event_timer_eq_preserves_signal_lifetime; [exact Hlast_event|exact Hlast_timer|].
    eapply tmr_task_registered_return_prefix_preserves_signal_lifetime;
      [exact Hcoverage|rewrite Hevents; exact Hpool|exact H0|].
    eapply tmr_task_event_timer_eq_preserves_signal_lifetime; eassumption.
Qed.

Lemma tmr_task_switch_pre_event_pool :
  forall environment critical local active sg original saved acquired entry,
  os_sched_task_switch_pre environment critical local active sg original saved acquired entry |--
  coq_prop (event_pool_partition sg entry.(EventState)) && TT.
Proof.
  intros; unfold os_sched_task_switch_pre, os_sched_active_switch_pre, os_sched_fields_switch_pre,
    kernel_continuation_call_masked, kernel_continuation_inv, kernel_program_fields_inv.
  entailer!.
  match goal with H : UCOS2_state_inv sg (os_sched_prefix_state entry) |- _ =>
    exact (proj1 (proj1 (proj2 (proj2 (proj2 H))))) end.
Qed.

(** Opening the actual output once retains its original/current/local
    existential tuple and BOTH spatial owners.  The source proof is read
    from that same tuple.  No selected run is chosen from a broad post. *)
Lemma tmr_task_registered_switch_output_signal :
  forall environment critical local active sg original saved acquired entry before_heap,
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  task_sw_hook_source_binding environment.(task_stack_call_external) ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) entry ->
  os_sched_task_switch_output environment critical local active sg original saved acquired entry before_heap |--
  tmr_task_sched_switch_signal_output environment critical local active sg original saved acquired entry before_heap.
Proof.
  intros environment critical local active sg original saved acquired entry before_heap
    Hcoverage Hbinding Hlife heap [Hpre [returned [current [next_local [Hbody Howned]]]]].
  pose proof (proj1 (tmr_task_switch_pre_event_pool environment critical local active sg original
    saved acquired entry before_heap Hpre)) as Hpool.
  split; [exact Hpre|]. exists returned, current, next_local; split; [|exact Howned].
  split; [exact Hbody|].
  eapply tmr_task_registered_body_source_preserves_signal_lifetime;
    [exact Hcoverage|exact Hbinding|exact Hpool|exact Hlife|exact (proj1 Hbody)].
Qed.

(** The classifier's sole external-indexed action is TaskInstall.  Its
    actual source reads arch_restore_source, copied unchanged by the hook
    selection.  All original registry members and ready certificates stay
    in place; this does not relabel an arbitrary registry or C run. *)
Lemma tmr_task_source_client_task_sw_hook : forall external action,
  tmr_task_source_client external action ->
  tmr_task_source_client (task_sw_hook_external external) action.
Proof.
  intros external action Hsource; destruct Hsource.
  - apply TmrTaskSourceScheduler; destruct H.
    + apply TmrTaskSchedulerNontimer; exact H.
    + apply TmrTaskSchedulerProfile.
    + apply TmrTaskSchedulerChangePrio.
    + apply TmrTaskSchedulerFlagReady.
    + apply TmrTaskSchedulerEventReady.
    + apply TmrTaskSchedulerTickTask.
    + change (tmr_task_scheduler_source_client (task_sw_hook_external external)
        (os_sched_install_client (task_sw_hook_external external) context outgoing incoming resumed)).
      apply TmrTaskSchedulerTaskInstall.
  - apply TmrTaskSourceSem; exact H.
  - apply TmrTaskSourceCritical; exact H.
  - apply TmrTaskSourceTick.
  - apply TmrTaskSourceTimer.
  - apply TmrTaskSourceTimerCall.
  - apply TmrTaskSourceSemAbortCall.
  - apply TmrTaskSourceSuspendCall.
Qed.

Lemma tmr_task_registered_source_coverage_task_sw_hook : forall external critical,
  tmr_task_registered_source_coverage external critical ->
  tmr_task_registered_source_coverage (task_sw_hook_external external) critical.
Proof.
  intros external critical Hcoverage action Hin.
  destruct (Hcoverage action Hin) as [Hsource Hready]; split; [|exact Hready].
  apply tmr_task_source_client_task_sw_hook; exact Hsource.
Qed.

Lemma tmr_task_registered_switch_source_output_signal :
  forall environment critical local active sg original saved acquired entry before_heap,
  let configured := task_sw_hook_call_environment environment in
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) entry ->
  os_sched_task_switch_source_output configured critical local active sg original saved acquired entry before_heap |--
  tmr_task_sched_switch_signal_output configured critical local active sg original saved acquired entry before_heap.
Proof.
  intros environment critical local active sg original saved acquired entry before_heap configured Hcoverage Hlife
    heap Houtput.
  assert (Hconfigured : tmr_task_registered_source_coverage configured.(task_stack_call_external) critical).
  { apply tmr_task_registered_source_coverage_task_sw_hook; exact Hcoverage. }
  apply (tmr_task_registered_switch_output_signal configured critical local active sg original saved acquired entry
    before_heap Hconfigured (task_sw_hook_call_environment_source_binding environment) Hlife heap).
  exact (os_sched_task_switch_source_output_observation environment critical local active sg original saved acquired
    entry before_heap heap Houtput).
Qed.
