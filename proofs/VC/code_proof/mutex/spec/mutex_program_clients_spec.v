Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.event Ucos2Verify.lib.event_pool Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.sem.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.tick.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_publication_environment_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Import TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.

Lemma mutex_program_task_fields_source : forall sg before after tid old new,
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  new.(eventPtr) = old.(eventPtr) -> new.(eventMultiWaitEvents) = old.(eventMultiWaitEvents) ->
  after.(TskState).(inUsedTaskStates) =
    (glob_task_set_usedtask before.(TskState) tid new).(inUsedTaskStates) ->
  after.(EventState).(inUsedEventStates) = before.(EventState).(inUsedEventStates) ->
  mutex_owner_source_history sg before after.
Proof.
  intros sg before after tid old new Hold Hptr Hmulti Htasks Hevents.
  eapply MutexOwnerHistoryStep with
    (before := replace_TskS (glob_task_set_usedtask before.(TskState) tid new) before).
  - apply mutex_owner_source_step_history; eapply MutexOwnerSourceTaskField;
      [exact Hold|exact Hptr|exact Hmulti|reflexivity|reflexivity].
  - apply MutexOwnerSourceFrame; assumption.
Qed.

Lemma mutex_program_event_fields_source : forall sg before after eid old new,
  before.(EventState).(inUsedEventStates) eid = Some old ->
  new.(eventType) = old.(eventType) -> new.(mutexFields) = old.(mutexFields) ->
  after.(EventState).(inUsedEventStates) =
    (update_event_field_raw before.(EventState) eid new).(inUsedEventStates) ->
  after.(TskState).(inUsedTaskStates) = before.(TskState).(inUsedTaskStates) ->
  mutex_owner_source_history sg before after.
Proof.
  intros sg before after eid old new Hold Htype Hmutex Hevents Htasks.
  eapply MutexOwnerHistoryStep with
    (before := replace_EventS (update_event_field_raw before.(EventState) eid new) before).
  - apply mutex_owner_source_step_history; eapply MutexOwnerSourceEventField;
      [exact Hold|exact Htype|exact Hmutex|reflexivity|reflexivity].
  - apply MutexOwnerSourceFrame; assumption.
Qed.

(** This file classifies actual state-transformer edges.  It does not
    replace their ordinary validity, physical heap, actor or stop proofs.
    One registered critical operation can contain several owner-field
    steps (for example a broadcast), all in the same ordered history. *)
Lemma mutex_program_event_task_rdy_source : forall sg state eid kind message result priority after,
  event_task_rdy sg state eid kind message result = Some (priority, after) ->
  mutex_owner_source_history sg state after.
Proof.
  intros sg state eid kind message result priority after Hstep.
  unfold event_task_rdy in Hstep.
  destruct (state.(EventState).(inUsedEventStates) eid) as [event|] eqn:He; [|discriminate].
  destruct (state.(TskState).(prioTbl) (event_wait_priority state.(TskState) event))
    as [| |tid]; try discriminate.
  destruct (state.(TskState).(inUsedTaskStates) tid) as [old|] eqn:Hold; [|discriminate].
  injection Hstep as Hpriority Hafter; subst after.
  apply mutex_owner_source_step_history; eapply MutexOwnerSourceWake; eassumption.
Qed.

Lemma mutex_program_event_broadcast_source : forall sg eid kind message result state priorities after,
  event_broadcast sg eid kind message result state priorities after ->
  mutex_owner_source_history sg state after.
Proof.
  intros sg eid kind message result state priorities after Hloop; induction Hloop.
  - constructor.
  - eapply mutex_owner_source_history_trans; [|exact IHHloop].
    eapply mutex_program_event_task_rdy_source; eassumption.
Qed.

Lemma mutex_program_del_critical_source : forall sg eid option state result after,
  mutex_del_critical sg eid option state result after ->
  mutex_owner_source_history sg state after.
Proof.
  intros sg eid option state result after [event [mutex [He [Htype [Hfields Hstep]]]]].
  destruct (Z.eq_dec option 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) state.(TskState)) 0).
    + destruct Hstep as [prepared [Hprepare [-> Hresult]]].
      eapply MutexOwnerHistoryStep.
      * apply mutex_owner_source_step_history; eapply MutexOwnerSourcePrepare; eassumption.
      * apply MutexOwnerSourceRecycle.
    + destruct Hstep as [-> _]; constructor.
  - destruct (Z.eq_dec option 1).
    + destruct Hstep as [prepared [priorities [drained [Hprepare [Hloop [-> Hresult]]]]]].
      eapply MutexOwnerHistoryStep; [|apply MutexOwnerSourceRecycle].
      eapply mutex_owner_source_history_trans.
      * apply mutex_owner_source_step_history; eapply MutexOwnerSourcePrepare; eassumption.
      * eapply mutex_program_event_broadcast_source; eassumption.
    + destruct Hstep as [-> _]; constructor.
Qed.

Lemma mutex_program_suspend_source : forall actor priority sg before after,
  kernel_client_step (task_suspend_critical_client actor priority) sg before after ->
  mutex_owner_source_history sg before after.
Proof.
  intros actor priority sg before after [_ [result [tid [current [_ [_ [_ Hstep]]]]]]].
  destruct (before.(TskState).(prioTbl) (fst (task_suspend_selection sg priority current))).
  - destruct Hstep as [_ ->]; constructor.
  - destruct Hstep as [_ ->]; constructor.
  - destruct Hstep as [old [Hold [_ ->]]].
    apply mutex_owner_source_step_history; eapply MutexOwnerSourceTaskField with (new := task_suspend old);
      [exact Hold|reflexivity|reflexivity|reflexivity|reflexivity].
Qed.

Lemma mutex_program_resume_source : forall actor priority sg before after,
  kernel_client_step (task_resume_critical_client actor priority) sg before after ->
  mutex_owner_source_history sg before after.
Proof.
  intros actor priority sg before after [_ [result [_ Hstep]]].
  destruct (before.(TskState).(prioTbl) priority).
  - destruct Hstep as [_ ->]; constructor.
  - destruct Hstep as [_ ->]; constructor.
  - destruct Hstep as [old [Hold Hstep]].
    destruct (task_is_suspended old.(stat)); destruct Hstep as [_ ->]; [|constructor].
    apply mutex_owner_source_step_history; eapply MutexOwnerSourceTaskField with (new := task_resume old);
      [exact Hold|reflexivity|reflexivity|reflexivity|reflexivity].
Qed.

Lemma mutex_program_tick_source : forall selected sg before after,
  kernel_client_step (sem_pend_tick_source_client selected) sg before after ->
  mutex_owner_source_history sg before after.
Proof.
  intros selected sg before after [old [Hold ->]].
  apply mutex_owner_source_step_history.
  eapply MutexOwnerSourceTaskField with (old := old) (new := tick_task_update old).
  - exact Hold.
  - pose proof (tick_task_preserves_non_timeout_fields old) as Hfields; cbv zeta in Hfields; tauto.
  - pose proof (tick_task_preserves_non_timeout_fields old) as Hfields; cbv zeta in Hfields; tauto.
  - apply tick_task_step_task_state_eq; exact Hold.
  - unfold tick_task_step; destruct (Z.eqb old.(dly) 0); [reflexivity|].
    destruct (Z.eqb (tick_task_update old).(dly) 0); reflexivity.
Qed.

Lemma mutex_program_sem_count_source : forall sg before eid event count,
  before.(EventState).(inUsedEventStates) eid = Some event ->
  mutex_owner_source_history sg before (sem_count_update_state before eid event count).
Proof.
  intros; apply mutex_owner_source_step_history; eapply MutexOwnerSourceEventField with
    (new := sem_set_count event count);
    [eassumption|reflexivity|reflexivity|reflexivity|reflexivity].
Qed.

Lemma mutex_program_sem_accept_source : forall actor eid count sg before after,
  kernel_client_step (sem_accept_critical_client actor eid count) sg before after ->
  mutex_owner_source_history sg before after.
Proof.
  intros actor eid count sg before after [event [He [Htype [node [fields [Hnode [_ [_ ->]]]]]]]].
  destruct (Z.ltb 0 fields.(semCount)); [eapply mutex_program_sem_count_source; exact Hnode|constructor].
Qed.

Lemma mutex_program_sem_post_source : forall actor eid sg before after,
  kernel_client_step (sem_pend_post_source_client actor eid) sg before after ->
  mutex_owner_source_history sg before after.
Proof.
  intros actor eid sg before after [result [event [He Hstep]]].
  destruct (Z.eqb (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
  - destruct Hstep as [fields [_ Hstep]].
    destruct (Z.ltb fields.(semCount) 65535); destruct Hstep as [_ ->].
    + eapply mutex_program_sem_count_source; exact He.
    + constructor.
  - destruct Hstep as [_ [priority Hstep]]; eapply mutex_program_event_task_rdy_source; eassumption.
Qed.

Lemma mutex_program_sem_abort_source : forall actor eid option sg before after,
  kernel_client_step (sem_pend_abort_source_client actor eid option) sg before after ->
  mutex_owner_source_history sg before after.
Proof.
  intros actor eid option sg before after [result [event [He Hstep]]].
  destruct (Z.eqb (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
  - destruct Hstep as [_ ->]; constructor.
  - destruct (Z.eqb option 1).
    + destruct Hstep as [priorities [Hloop _]]; eapply mutex_program_event_broadcast_source; eassumption.
    + destruct Hstep as [priority [Hstep _]]; eapply mutex_program_event_task_rdy_source; eassumption.
Qed.

Lemma mutex_program_saved_sp_source : forall actor selected sp sg before after,
  kernel_client_step (sem_pend_saved_sp_source_client actor selected sp) sg before after ->
  mutex_owner_source_history sg before after.
Proof.
  intros actor selected sp sg before after Hstep.
  change (after = os_sched_save_current_sp before selected sp) in Hstep; subst after.
  unfold os_sched_save_current_sp.
  destruct (before.(TskState).(inUsedTaskStates) selected) as [old|] eqn:Hold.
  2: { apply mutex_owner_source_step_history; apply MutexOwnerSourceFrame; reflexivity. }
  apply mutex_owner_source_step_history; eapply MutexOwnerSourceTaskField with (new := task_set_saved_sp old sp);
    [exact Hold|reflexivity|reflexivity|reflexivity|reflexivity].
Qed.

Lemma mutex_program_delay_resume_source : forall actor priority sg before after,
  kernel_client_step (sem_pend_delay_resume_source_client actor priority) sg before after ->
  mutex_owner_source_history sg before after.
Proof.
  intros actor priority sg before after [_ [result [_ Hstep]]].
  destruct (before.(TskState).(prioTbl) priority).
  - destruct Hstep as [_ ->]; constructor.
  - destruct Hstep as [_ ->]; constructor.
  - destruct Hstep as [old [Hold Hstep]].
    destruct (Z.eqb old.(dly) 0); destruct Hstep as [_ ->]; [constructor|].
    apply mutex_owner_source_step_history; eapply MutexOwnerSourceTaskField with
      (old := old) (new := sem_pend_delay_resume_task old).
    + exact Hold.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
Qed.

Lemma mutex_program_change_priority_state_source : forall sg before tid old oldprio newprio,
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  mutex_owner_source_history sg before (task_change_priority_state sg before tid old oldprio newprio).
Proof.
  intros sg before tid old oldprio newprio Hold.
  eapply mutex_owner_source_history_trans with
    (middle := replace_TskS (task_change_priority_tasks before.(TskState) tid old oldprio newprio) before).
  - eapply mutex_program_task_fields_source with (old := old) (new := mutex_priority_task old newprio);
      [exact Hold|reflexivity|reflexivity|reflexivity|reflexivity].
  - unfold task_change_priority_state, task_change_priority_events.
    destruct old.(eventPtr) as [eid|].
    + destruct (before.(EventState).(inUsedEventStates) eid) as [event|] eqn:He.
      * eapply mutex_program_event_fields_source with
          (new := event_insert_waiter sg
            (task_change_priority_tasks before.(TskState) tid old oldprio newprio) event tid);
          [exact He|reflexivity|reflexivity|reflexivity|reflexivity].
      * apply mutex_owner_source_step_history; apply MutexOwnerSourceFrame; reflexivity.
    + apply mutex_owner_source_step_history; apply MutexOwnerSourceFrame; reflexivity.
Qed.

Lemma mutex_program_change_priority_source : forall actor oldprio newprio sg before after,
  kernel_client_step (task_change_priority_source_client actor oldprio newprio) sg before after ->
  mutex_owner_source_history sg before after.
Proof.
  intros actor oldprio newprio sg before after [_ [code [_ Hstep]]].
  destruct (before.(TskState).(prioTbl) newprio).
  - destruct Hstep as [selected [_ [_ Hstep]]].
    destruct (before.(TskState).(prioTbl) selected).
    + destruct Hstep as [_ ->]; constructor.
    + destruct Hstep as [_ ->]; constructor.
    + destruct Hstep as [old [Hold [_ [_ [_ ->]]]]].
      apply mutex_program_change_priority_state_source; exact Hold.
  - destruct Hstep as [_ ->]; constructor.
  - destruct Hstep as [_ ->]; constructor.
Qed.

Lemma mutex_program_projected_client_source : forall action sg before after,
  sem_pend_projected_source_client action -> kernel_client_step action sg before after ->
  mutex_owner_source_history sg before after.
Proof.
  intros action sg before after Hclient Hstep.
  destruct Hclient as
    [actor oldprio newprio | actor priority | actor priority | selected |
     actor eid | actor eid option | actor selected sp | actor priority | client Hframe |
     external context outgoing incoming resumed].
  - eapply mutex_program_change_priority_source; eassumption.
  - eapply mutex_program_suspend_source; eassumption.
  - eapply mutex_program_resume_source; eassumption.
  - eapply mutex_program_tick_source; eassumption.
  - eapply mutex_program_sem_post_source; eassumption.
  - eapply mutex_program_sem_abort_source; eassumption.
  - eapply mutex_program_saved_sp_source; eassumption.
  - eapply mutex_program_delay_resume_source; eassumption.
  - destruct (Hframe sg before after Hstep) as [Htasks [Hevents Hrunning]].
    apply mutex_owner_source_step_history; apply MutexOwnerSourceFrame.
    + rewrite Htasks; reflexivity.
    + rewrite Hevents; reflexivity.
  - destruct (os_sched_install_client_state_frame external context outgoing incoming resumed
      sg before after Hstep) as [Htasks [_ [Hevents _]]].
    apply mutex_owner_source_step_history; apply MutexOwnerSourceFrame.
    + exact Htasks.
    + rewrite Hevents; reflexivity.
Qed.
