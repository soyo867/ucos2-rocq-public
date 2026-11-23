Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_fresh_recovery_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_retirement.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_api_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_call_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_acquired_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_masked_c_step_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagPendFreshSource.
Import FlagPendFreshRecovery NamedSourceFrames.

(** These observations retain the original slot and generation.  Removal
    makes the observation vacuous; returning to that caller is established
    separately by the actual completed-call source. *)
Definition flag_pend_task_fields_clear (task : TaskAbstractState) : Prop :=
  flag_active_event_clear task /\ task.(tcbFlagNode) = 0.

Lemma flag_pend_fresh_fields_used_eq : forall origin before after,
  after.(TskState).(inUsedTaskStates) = before.(TskState).(inUsedTaskStates) ->
  flag_pend_fresh_fields_at_origin origin before ->
  flag_pend_fresh_fields_at_origin origin after.
Proof.
  intros [|slot generation] before after Hused Hfields; [exact I|].
  unfold flag_pend_fresh_fields_at_origin in *; rewrite Hused; exact Hfields.
Qed.

Lemma flag_pend_fresh_fields_task_update : forall origin before after slot old replacement,
  before.(TskState).(inUsedTaskStates) slot = Some old ->
  replacement.(taskGeneration) = old.(taskGeneration) ->
  (flag_pend_task_fields_clear old -> flag_pend_task_fields_clear replacement) ->
  after.(TskState).(inUsedTaskStates) =
    (glob_task_set_usedtask before.(TskState) slot replacement).(inUsedTaskStates) ->
  flag_pend_fresh_fields_at_origin origin before ->
  flag_pend_fresh_fields_at_origin origin after.
Proof.
  intros [|observed generation] before after slot old replacement Hold Hgen Hclear Hused Hfields;
    [exact I|].
  unfold flag_pend_fresh_fields_at_origin in *.
  intros task Htask Hg; rewrite Hused in Htask.
  cbn [glob_task_set_usedtask inUsedTaskStates] in Htask.
  destruct (Z.eqb observed slot) eqn:Heq.
  - apply Z.eqb_eq in Heq; subst observed.
    injection Htask as Htask; subst task.
    apply Hclear; apply (Hfields old Hold); congruence.
  - exact (Hfields task Htask Hg).
Qed.

Lemma task_flag_wake_preserves_fresh_fields : forall task bits result,
  flag_pend_task_fields_clear task ->
  flag_pend_task_fields_clear (task_flag_wake task bits result).
Proof.
  intros task bits result [Hclear Hnode]; split; [exact Hclear|reflexivity].
Qed.

Lemma task_event_wake_single_preserves_fresh_fields : forall task kind message result,
  flag_pend_task_fields_clear task ->
  flag_pend_task_fields_clear (task_event_wake_single task kind message result).
Proof.
  intros task kind message result [[Hptr [Hmulti Harray]] Hnode].
  split; [unfold flag_active_event_clear; split; [reflexivity|split; assumption]|exact Hnode].
Qed.

Lemma tick_task_update_preserves_fresh_fields : forall task,
  flag_pend_task_fields_clear task -> flag_pend_task_fields_clear (tick_task_update task).
Proof.
  intros task Hfields; unfold tick_task_update.
  destruct (Z.eqb task.(dly) 0); exact Hfields.
Qed.

Lemma kernel_wake_c_source_preserves_fresh_fields : forall sg entry returned origin,
  WakeComponent.kernel_wake_c_source sg entry returned ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros sg entry returned origin Hsource Hfields; destruct Hsource.
  - destruct (flag_task_rdy_result _ _ _ _ _ _ _ H)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]].
    eapply flag_pend_fresh_fields_task_update with (replacement := task_flag_wake old bits result);
      [exact Hold|reflexivity|apply task_flag_wake_preserves_fresh_fields|reflexivity|exact Hfields].
  - unfold event_task_rdy in H.
    destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
    destruct (entry.(TskState).(prioTbl) (event_wait_priority entry.(TskState) event))
      as [| |slot]; try discriminate.
    destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
    injection H as Hpriority Hreturned; subst returned.
    eapply flag_pend_fresh_fields_task_update with (replacement := task_event_wake_single old kind message result);
      [exact Hold|reflexivity|apply task_event_wake_single_preserves_fresh_fields|reflexivity|exact Hfields].
  - eapply flag_pend_fresh_fields_task_update with (slot := slot) (old := old)
      (replacement := tick_task_update old).
    + exact H.
    + unfold tick_task_update; destruct (Z.eqb old.(dly) 0); reflexivity.
    + apply tick_task_update_preserves_fresh_fields.
    + rewrite (tick_task_step_task_state_eq sg slot old entry H); reflexivity.
    + exact Hfields.
Qed.

Lemma task_suspend_state_preserves_fresh_fields : forall entry slot node origin,
  entry.(TskState).(inUsedTaskStates) slot = Some node ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin (task_suspend_state entry slot node).
Proof.
  intros entry slot node origin Hnode Hfields.
  eapply flag_pend_fresh_fields_task_update with (replacement := task_suspend node);
    [exact Hnode|reflexivity|intros H; exact H|reflexivity|exact Hfields].
Qed.

Lemma task_suspend_step_preserves_fresh_fields : forall sg request priority entry result self returned origin,
  task_suspend_step sg request priority entry result self returned ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros sg request priority entry result self returned origin Hstep Hfields.
  destruct (TaskSuspendActualC.task_suspend_step_state_cases _ _ _ _ _ _ _ Hstep)
    as [->|[slot [node [Hnode ->]]]]; [exact Hfields|].
  eapply task_suspend_state_preserves_fresh_fields; eassumption.
Qed.

Lemma kernel_status_c_source_preserves_fresh_fields : forall sg entry returned origin,
  StatusComponent.kernel_status_c_source sg entry returned ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros sg entry returned origin Hsource Hfields; destruct Hsource.
  - destruct H as [cid [current [_ [_ [_ Hstep]]]]].
    destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg priority current))).
    + destruct Hstep as [_ ->]; exact Hfields.
    + destruct Hstep as [_ ->]; exact Hfields.
    + destruct Hstep as [old [Hold [_ ->]]].
      eapply task_suspend_state_preserves_fresh_fields; eassumption.
  - destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority).
    + destruct Hstep as [_ ->]; exact Hfields.
    + destruct Hstep as [_ ->]; exact Hfields.
    + destruct Hstep as [old [Hold Hstep]]; destruct (task_is_suspended old.(stat)).
      * destruct Hstep as [_ ->].
        eapply flag_pend_fresh_fields_task_update with (replacement := task_resume old);
          [exact Hold|reflexivity|intros H; exact H|reflexivity|exact Hfields].
      * destruct Hstep as [_ ->]; exact Hfields.
  - destruct H as [event [fields [_ [_ [_ ->]]]]]; destruct (Z.ltb 0 fields.(semCount)); exact Hfields.
Qed.

Lemma kernel_task_creation_c_source_preserves_fresh_fields : forall sg entry returned origin,
  CreationComponent.kernel_task_creation_c_source sg entry returned ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros sg entry returned origin Hsource Hfields.
  apply (flag_pend_fresh_fields_used_eq origin entry returned); [|exact Hfields].
  destruct Hsource; try reflexivity.
  - unfold task_create_critical in H; destruct (Z.ltb 0 entry.(IntrState).(intNesting)).
    + destruct H as [_ ->]; reflexivity.
    + destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority);
        destruct Hstep as [_ ->]; reflexivity.
  - destruct H2 as [_ ->]; reflexivity.
Qed.

Lemma kernel_event_creation_c_source_preserves_fresh_fields : forall entry returned origin,
  EventCreationComponent.kernel_event_creation_c_source entry returned ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros entry returned origin Hsource Hfields.
  pose proof (kernel_event_creation_c_source_other_fields entry returned Hsource) as [Htasks _].
  eapply flag_pend_fresh_fields_used_eq; [rewrite Htasks; reflexivity|exact Hfields].
Qed.

Lemma kernel_queue_creation_c_source_preserves_fresh_fields : forall sg entry returned origin,
  QueueCreationComponent.kernel_queue_creation_c_source sg entry returned ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros sg entry returned origin Hsource Hfields.
  pose proof (kernel_queue_creation_c_source_other_fields sg entry returned Hsource) as [Htasks _].
  eapply flag_pend_fresh_fields_used_eq; [rewrite Htasks; reflexivity|exact Hfields].
Qed.

Lemma task_delete_primitive_c_segment_preserves_fresh_fields :
  forall environment critical sg entry before input stopped returned after output origin,
  DeleteComponent.task_delete_primitive_c_segment environment critical sg
    entry before input stopped returned after output ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros environment critical sg entry before input stopped returned after output origin Hstep Hfields.
  destruct Hstep; exact Hfields.
Qed.

Lemma flag_pend_task_primitive_c_step_preserves_fresh_fields :
  forall environment critical sg entry before input stopped returned after output origin,
  PrimitiveComponent.flag_pend_task_primitive_c_step environment critical sg
    entry before input stopped returned after output ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros environment critical sg entry before input stopped returned after output origin Hstep Hfields.
  destruct Hstep; try exact Hfields.
  destruct H; exact Hfields.
Qed.

Lemma mutex_priority_task_preserves_fresh_fields : forall task priority,
  flag_pend_task_fields_clear task ->
  flag_pend_task_fields_clear (mutex_priority_task task priority).
Proof. intros task priority Hfields; exact Hfields. Qed.

Lemma task_change_prio_critical_preserves_fresh_fields :
  forall sg requested priority entry result returned origin,
  task_change_prio_critical sg requested priority entry result returned ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros sg requested priority entry result returned origin Hcode Hfields.
  unfold task_change_prio_critical in Hcode.
  destruct (entry.(TskState).(prioTbl) priority).
  - destruct Hcode as [selected [Hselection Hstep]].
    unfold task_change_prio_selected_effect in Hstep.
    destruct (Z.eqb selected sg.(osLowestPrio)).
    + destruct Hstep as [_ ->]; exact Hfields.
    + destruct (entry.(TskState).(prioTbl) selected).
      * destruct Hstep as [_ ->]; exact Hfields.
      * destruct Hstep as [_ ->]; exact Hfields.
      * destruct Hstep as [old [Hold [_ ->]]].
        eapply flag_pend_fresh_fields_task_update with (replacement := mutex_priority_task old priority);
          [exact Hold|reflexivity|apply mutex_priority_task_preserves_fresh_fields|reflexivity|exact Hfields].
  - destruct Hcode as [_ ->]; exact Hfields.
  - destruct Hcode as [_ ->]; exact Hfields.
Qed.

Lemma mutex_del_prepare_preserves_fresh_fields : forall sg mutex entry returned origin,
  mutex_del_prepare sg mutex entry returned ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros sg mutex entry returned origin Hprepare Hfields.
  unfold mutex_del_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)); [subst returned; exact Hfields|].
  destruct mutex.(mfOwner) as [owner|].
  - destruct Hprepare as [node [priority [Hnode [Hpriority ->]]]].
    unfold mutex_del_owner_priority_state; destruct (Z.eq_dec node.(curPrio) priority).
    + exact Hfields.
    + eapply flag_pend_fresh_fields_task_update with (replacement := mutex_priority_task node priority);
        [exact Hnode|reflexivity|apply mutex_priority_task_preserves_fresh_fields|reflexivity|exact Hfields].
  - subst returned; exact Hfields.
Qed.

Lemma event_broadcast_preserves_fresh_fields : forall sg eid kind message result entry priorities returned origin,
  event_broadcast sg eid kind message result entry priorities returned ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros sg eid kind message result entry priorities returned origin Hbroadcast.
  induction Hbroadcast; intro Hfields; [exact Hfields|].
  apply IHHbroadcast.
  eapply kernel_wake_c_source_preserves_fresh_fields;
    [eapply WakeComponent.KernelWakeCEventSource; eassumption|exact Hfields].
Qed.

Lemma mutex_del_critical_preserves_fresh_fields : forall sg eid option entry result returned origin,
  mutex_del_critical sg eid option entry result returned ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros sg eid option entry result returned origin
    [event [mutex [Hevent [Htype [Hmutex Hstep]]]]] Hfields.
  destruct (Z.eq_dec option 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) entry.(TskState)) 0).
    + destruct Hstep as [prepared [Hprepare [-> Hresult]]].
      change (flag_pend_fresh_fields_at_origin origin prepared).
      eapply mutex_del_prepare_preserves_fresh_fields; eassumption.
    + destruct Hstep as [-> Hresult]; exact Hfields.
  - destruct (Z.eq_dec option 1).
    + destruct Hstep as [prepared [priorities [drained [Hprepare [Hbroadcast [-> Hresult]]]]]].
      change (flag_pend_fresh_fields_at_origin origin drained).
      eapply event_broadcast_preserves_fresh_fields; [exact Hbroadcast|].
      eapply mutex_del_prepare_preserves_fresh_fields; eassumption.
    + destruct Hstep as [-> Hresult]; exact Hfields.
Qed.

Lemma kernel_critical_c_source_preserves_fresh_fields : forall sg call origin,
  CriticalComponent.kernel_critical_c_source sg call ->
  flag_pend_fresh_fields_at_origin origin (CriticalComponent.kernel_critical_c_entry call) ->
  flag_pend_fresh_fields_at_origin origin (CriticalComponent.kernel_critical_c_returned call).
Proof.
  intros sg [actual|actual] origin Hsource Hfields; cbn in *.
  - destruct Hsource as [error [Hcritical Hresult]].
    eapply task_change_prio_critical_preserves_fresh_fields; eassumption.
  - destruct Hsource.
    + destruct H0 as [error [scheduled [Hcritical Hencoding]]].
      eapply mutex_del_critical_preserves_fresh_fields; eassumption.
    + exact Hfields.
Qed.

Lemma mutex_pend_inherit_step_preserves_fresh_fields :
  forall sg entry owner node base waiter ceiling returned origin,
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  mutex_pend_inherit_step sg entry owner node base waiter ceiling returned ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros sg entry owner node base waiter ceiling returned origin Hnode Hstep Hfields.
  unfold mutex_pend_inherit_step in Hstep.
  destruct (mutex_pend_inherit_action sg.(osPrioMutexCeilDis) base node.(curPrio) waiter ceiling).
  - subst returned; exact Hfields.
  - subst returned; exact Hfields.
  - destruct Hstep as [events [Hevents ->]].
    eapply flag_pend_fresh_fields_task_update with (replacement := mutex_priority_task node ceiling);
      [exact Hnode|reflexivity|apply mutex_priority_task_preserves_fresh_fields|reflexivity|exact Hfields].
Qed.

Lemma mutex_post_prepare_preserves_fresh_fields : forall sg mutex owner entry returned origin,
  mutex_post_prepare sg mutex owner entry returned ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros sg mutex owner entry returned origin Hprepare Hfields.
  unfold mutex_post_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)); [subst returned; exact Hfields|].
  destruct Hprepare as [node [priority [Hnode [Hpriority ->]]]].
  unfold mutex_post_owner_priority_state; destruct (Z.eq_dec node.(curPrio) priority).
  - exact Hfields.
  - eapply flag_pend_fresh_fields_task_update with (replacement := mutex_priority_task node priority);
      [exact Hnode|reflexivity|apply mutex_priority_task_preserves_fresh_fields|reflexivity|exact Hfields].
Qed.

Lemma mutex_post_critical_preserves_fresh_fields : forall sg eid caller entry result schedule returned origin,
  mutex_post_critical sg eid caller entry result schedule returned ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros sg eid caller entry result schedule returned origin Hcritical Hfields; destruct Hcritical.
  - exact Hfields.
  - change (flag_pend_fresh_fields_at_origin origin prepared).
    eapply mutex_post_prepare_preserves_fresh_fields; eassumption.
  - change (flag_pend_fresh_fields_at_origin origin woken).
    eapply kernel_wake_c_source_preserves_fresh_fields;
      [eapply WakeComponent.KernelWakeCEventSource; eassumption|].
    eapply mutex_post_prepare_preserves_fresh_fields; eassumption.
Qed.

Lemma flag_pend_fresh_fields_task_commit : forall origin before after priority invocation node,
  flag_pend_task_fields_clear node ->
  after.(TskState).(inUsedTaskStates) =
    (task_commit before.(TskState) priority invocation node).(inUsedTaskStates) ->
  flag_pend_fresh_fields_at_origin origin before ->
  flag_pend_fresh_fields_at_origin origin after.
Proof.
  intros [|slot generation] before after priority invocation node Hclear Hused Hfields; [exact I|].
  unfold flag_pend_fresh_fields_at_origin in *.
  intros task Htask Hg; rewrite Hused in Htask.
  cbn [task_commit inUsedTaskStates] in Htask.
  destruct (Z.eq_dec slot node.(taskID)).
  - injection Htask as Htask; subst task; exact Hclear.
  - destruct before.(TskState).(tcbListHead) as [head|].
    + destruct (before.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
      destruct (Z.eq_dec slot head); injection Htask as Htask; subst task;
        exact (Hfields old eq_refl Hg).
    + exact (Hfields task Htask Hg).
Qed.

Lemma task_create_stack_publication_preserves_fresh_fields : forall sg publication entry origin,
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin (task_create_stack_publication_state sg publication entry).
Proof.
  intros sg publication entry origin Hfields.
  eapply flag_pend_fresh_fields_task_commit with
    (priority := (task_create_stack_publication_args publication).(initPrio))
    (invocation := publication.(stack_publication_invocation))
    (node := task_tcb_init_commit_node (task_create_stack_publication_args publication)
      publication.(stack_publication_acquired) publication.(stack_publication_slot)
      publication.(stack_publication_image));
    [unfold flag_pend_task_fields_clear, flag_active_event_clear; repeat split; reflexivity
    |reflexivity|exact Hfields].
Qed.

Lemma flag_pend_fresh_fields_task_recycle : forall sg origin before after tid priority node name,
  after.(TskState).(inUsedTaskStates) =
    (task_recycle sg before.(TskState) tid priority node name).(inUsedTaskStates) ->
  flag_pend_fresh_fields_at_origin origin before ->
  flag_pend_fresh_fields_at_origin origin after.
Proof.
  intros sg [|slot generation] before after tid priority node name Hused Hfields; [exact I|].
  unfold flag_pend_fresh_fields_at_origin in *.
  intros task Htask Hg; rewrite Hused in Htask.
  cbn [task_recycle inUsedTaskStates] in Htask; unfold task_unlink_used_map in Htask.
  destruct (Z.eq_dec slot tid); [discriminate|].
  destruct (before.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
  injection Htask as Htask; subst task; exact (Hfields old eq_refl Hg).
Qed.

Lemma task_delete_prepare_after_unlink_preserves_fresh_fields :
  forall entry after tid old updated origin,
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  after.(TskState).(inUsedTaskStates) = entry.(TskState).(inUsedTaskStates) ->
  updated.(taskGeneration) = old.(taskGeneration) ->
  (flag_pend_task_fields_clear old -> flag_pend_task_fields_clear updated) ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin (task_delete_prepare_after_unlink after tid updated).
Proof.
  intros entry after tid old updated origin Hold Hused Hgen Hclear Hfields.
  eapply flag_pend_fresh_fields_task_update with (before := entry)
    (replacement := task_prepare_delete updated).
  - exact Hold.
  - exact Hgen.
  - intro H; exact (Hclear H).
  - cbn [task_delete_prepare_after_unlink replace_SchedS replace_TskS TskState glob_task_set_usedtask
      inUsedTaskStates]; rewrite Hused; reflexivity.
  - exact Hfields.
Qed.

Lemma task_delete_prepare_single_wait_preserves_fresh_fields :
  forall entry tid old prepared loan origin,
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  task_delete_prepare_single_wait entry tid old = Some (prepared, loan) ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin prepared.
Proof.
  intros entry tid old prepared loan origin Hold Hstep Hfields.
  unfold task_delete_prepare_single_wait in Hstep.
  destruct old.(eventPtr) as [eid|].
  - destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
    cbn [task_set_event_ptr tcbFlagNode] in Hstep.
    destruct (Z.eqb old.(tcbFlagNode) 0).
    + injection Hstep as Hprepared Hloan; subst prepared.
      eapply task_delete_prepare_after_unlink_preserves_fresh_fields;
        [exact Hold|reflexivity|reflexivity| |exact Hfields].
      intros [[Hptr [Hmulti Harray]] Hnode]; unfold flag_pend_task_fields_clear, flag_active_event_clear;
        repeat split; try assumption; reflexivity.
    + destruct (flag_unlink_node entry.(FlagState) old.(tcbFlagNode)) as [[waiter flags]|]; [|discriminate].
      injection Hstep as Hprepared Hloan; subst prepared.
      eapply task_delete_prepare_after_unlink_preserves_fresh_fields;
        [exact Hold|reflexivity|reflexivity| |exact Hfields].
      intros [[Hptr [Hmulti Harray]] Hnode]; unfold flag_pend_task_fields_clear, flag_active_event_clear;
        repeat split; try assumption; reflexivity.
  - destruct (Z.eqb old.(tcbFlagNode) 0).
    + injection Hstep as Hprepared Hloan; subst prepared.
      eapply task_delete_prepare_after_unlink_preserves_fresh_fields;
        [exact Hold|reflexivity|reflexivity|intros H; exact H|exact Hfields].
    + destruct (flag_unlink_node entry.(FlagState) old.(tcbFlagNode)) as [[waiter flags]|]; [|discriminate].
      injection Hstep as Hprepared Hloan; subst prepared.
      eapply task_delete_prepare_after_unlink_preserves_fresh_fields;
        [exact Hold|reflexivity|reflexivity| |exact Hfields].
      intros [Hclear Hnode]; split; [exact Hclear|reflexivity].
Qed.

Lemma task_delete_own_c_segment_preserves_fresh_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  DeleteComponent.task_delete_own_c_segment environment critical sg observer observer_origin
    entry before input stopped returned after output ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin
    Hstep Hfields; destruct Hstep.
  - destruct H0 as [Hprep Hinput Houtput].
    destruct Hprep as [[Hlookup [Hselected [Hlive Hpointer]]] [Hprepare Hrunning]].
    change (flag_pend_fresh_fields_at_origin origin inputs.(DeleteComponent.delete_capture_prepared)).
    eapply task_delete_prepare_single_wait_preserves_fresh_fields;
      [exact (proj2 (task_delete_table_lookup_live _ _ _ _ Hlive))|exact Hprepare|exact Hfields].
  - pose (inputs := capture.(DeleteComponent.delete_save_restore).(DeleteComponent.delete_restore_inputs)).
    exact (flag_pend_fresh_fields_task_recycle inputs.(DeleteComponent.delete_capture_globals) origin
      capture.(DeleteComponent.delete_save_resumed) (DeleteComponent.task_delete_capture_cut capture)
      inputs.(DeleteComponent.delete_capture_tid) inputs.(DeleteComponent.delete_capture_priority)
      (task_delete_prepared_node inputs.(DeleteComponent.delete_capture_node))
      inputs.(DeleteComponent.delete_capture_name) eq_refl Hfields).
Qed.

Lemma kernel_builtin_c_segment_preserves_fresh_fields :
  forall environment critical local sg entry before returned after input output origin,
  BuiltinComponent.kernel_builtin_c_segment environment critical local sg
    entry before returned after input output ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros environment critical local sg entry before returned after input output origin Hstep Hfields.
  destruct Hstep.
  - destruct operation; exact Hfields.
  - apply task_create_stack_publication_preserves_fresh_fields; exact Hfields.
  - pose proof (BuiltinComponent.kernel_irq_transfer_c_completion_source environment critical sg
      handler saved entry transfer frame before after H) as Hsource.
    eapply flag_pend_fresh_fields_used_eq; [|exact Hfields].
    exact (proj1 (BuiltinComponent.os_int_exit_configured_transfer_state_frame
      environment sg handler entry transfer Hsource)).
Qed.

Lemma task_install_c_step_preserves_fresh_fields :
  forall environment local sg entry before input stopped returned after output origin,
  InstallComponent.task_install_c_step environment local sg
    entry before input stopped returned after output ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros environment local sg entry before input stopped returned after output origin Hstep Hfields.
  destruct Hstep; eapply flag_pend_fresh_fields_used_eq; [reflexivity|exact Hfields].
Qed.

Lemma task_suspend_masked_c_step_preserves_fresh_fields :
  forall environment critical sg entry before input stopped returned after output origin,
  TaskSuspendMaskedC.task_suspend_masked_c_step environment critical sg
    entry before input stopped returned after output ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros environment critical sg entry before input stopped returned after output origin Hstep Hfields.
  destruct Hstep as [saved_local caller saved call frame before after [[Hread Hcode] Hinput Houtput]].
  eapply task_suspend_step_preserves_fresh_fields; eassumption.
Qed.

(** All thirteen original constructors retain their actual C source and
    resource completion.  No stop, current-task or target-inequality guard
    is needed for these four fields. *)
Lemma kernel_program_c_step_preserves_fresh_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  kernel_program_c_step environment critical sg observer observer_origin
    entry before input stopped returned after output ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin
    Hstep Hfields; destruct Hstep.
  - destruct H as [Hcompletion [Hphysical [Hsource Hpacket]]].
    eapply kernel_critical_c_source_preserves_fresh_fields; eassumption.
  - eapply kernel_builtin_c_segment_preserves_fresh_fields; eassumption.
  - eapply task_install_c_step_preserves_fresh_fields; eassumption.
  - eapply kernel_wake_c_source_preserves_fresh_fields;
      [eapply WakeComponent.kernel_wake_c_segment_source; exact H|exact Hfields].
  - destruct H as [Hsource Hinput Houtput].
    eapply kernel_status_c_source_preserves_fresh_fields; eassumption.
  - eapply kernel_task_creation_c_source_preserves_fresh_fields;
      [eapply CreationComponent.kernel_task_creation_c_segment_source; exact H|exact Hfields].
  - eapply kernel_event_creation_c_source_preserves_fresh_fields;
      [eapply EventCreationComponent.kernel_event_creation_c_segment_source; exact H|exact Hfields].
  - eapply kernel_queue_creation_c_source_preserves_fresh_fields;
      [eapply QueueCreationComponent.kernel_queue_creation_c_segment_source; exact H|exact Hfields].
  - destruct H as [[Hnode [Hforeign Hsource]] Hinput Houtput].
    eapply mutex_pend_inherit_step_preserves_fresh_fields; eassumption.
  - destruct H as [[Hcaller Hsource] Hinput Houtput].
    eapply mutex_post_critical_preserves_fresh_fields; eassumption.
  - eapply task_delete_primitive_c_segment_preserves_fresh_fields; eassumption.
  - eapply flag_pend_task_primitive_c_step_preserves_fresh_fields; eassumption.
  - eapply task_delete_own_c_segment_preserves_fresh_fields; eassumption.
Qed.

Lemma kernel_program_return_c_step_preserves_fresh_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  SelectedReturnPrimitive.kernel_program_return_c_step environment critical sg observer observer_origin
    entry before input stopped returned after output ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin
    Hstep Hfields; destruct Hstep.
  - eapply kernel_program_c_step_preserves_fresh_fields; eassumption.
  - destruct (SelectedReturnPrimitive.kernel_selected_return_c_step_state_stop _ _ _ _ _ _ _ _ H)
      as [-> Hstop]; exact Hfields.
  - eapply flag_pend_fresh_fields_used_eq; [reflexivity|exact Hfields].
  - eapply flag_pend_fresh_fields_used_eq; [reflexivity|exact Hfields].
Qed.

Lemma kernel_program_selected_c_step_preserves_fresh_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  SelectedCProgram.kernel_program_selected_c_step environment critical sg observer observer_origin
    entry before input stopped returned after output ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin
    Hstep Hfields; destruct Hstep.
  - eapply kernel_program_return_c_step_preserves_fresh_fields; eassumption.
  - destruct H.
    eapply flag_pend_fresh_fields_used_eq; [|exact Hfields].
    exact (proj1 (BuiltinComponent.os_int_exit_configured_transfer_state_frame
      environment sg handler entry transfer source)).
  - eapply task_suspend_masked_c_step_preserves_fresh_fields; eassumption.
Qed.

(** Induction consumes the given sequence, including its actual middle
    heaps and post-to-pre entailments.  The observer origin is fixed across
    every atom even when the execution's selected caller changes. *)
Lemma kernel_program_selected_c_sequence_preserves_fresh_fields :
  forall environment critical sg observer observer_origin entry before input stopped returned after output origin,
  kernel_c_sequence
    (SelectedCProgram.kernel_program_selected_c_step environment critical sg observer observer_origin)
    entry before input stopped returned after output ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin returned.
Proof.
  intros environment critical sg observer observer_origin entry before input stopped returned after output origin Hrun.
  induction Hrun; intro Hfields.
  - exact Hfields.
  - eapply kernel_program_selected_c_step_preserves_fresh_fields; eassumption.
  - apply IHHrun2, IHHrun1, Hfields.
  - apply IHHrun, Hfields.
Qed.

End FlagPendFreshSource.
