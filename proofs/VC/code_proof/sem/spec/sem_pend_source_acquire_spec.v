Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_call_spec.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_sched_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_sem_source_projection_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Import TaskStateDef ListNotations.
Local Open Scope Z_scope.

(** The ordinary Sem caller is not yet a waiter.  Its original admission
    promises precisely these three registration fields; it does not promise
    a value for the disabled Multi pointer or a non-timeout old statPend. *)
Definition sem_pend_source_unregistered_transport before after : Prop :=
  forall slot old, before.(TskState).(inUsedTaskStates) slot = Some old ->
  sem_pend_task_unregistered old ->
  exists current, after.(TskState).(inUsedTaskStates) slot = Some current /\
    sem_pend_task_unregistered current.

Lemma sem_pend_source_unregistered_transport_map_eq : forall before after,
  after.(TskState).(inUsedTaskStates) = before.(TskState).(inUsedTaskStates) ->
  sem_pend_source_unregistered_transport before after.
Proof. intros before after Hmap slot old Hold Hclear; exists old; rewrite Hmap; auto. Qed.

Lemma sem_pend_source_unregistered_transport_trans : forall before middle after,
  sem_pend_source_unregistered_transport before middle ->
  sem_pend_source_unregistered_transport middle after ->
  sem_pend_source_unregistered_transport before after.
Proof.
  intros before middle after Hfirst Hsecond slot old Hold Hclear.
  destruct (Hfirst slot old Hold Hclear) as [current [Hcurrent Hclear']].
  exact (Hsecond slot current Hcurrent Hclear').
Qed.

Lemma sem_pend_source_projection_preserves_unregistered : forall before after,
  (forall slot old, before.(TskState).(inUsedTaskStates) slot = Some old ->
    sem_pend_task_projection before.(TskState) after.(TskState) slot old) ->
  sem_pend_source_unregistered_transport before after.
Proof.
  intros before after Hprojection slot old Hold Hclear.
  destruct (Hprojection slot old Hold) as [current [Hcurrent Htrace]].
  exists current; split; [exact Hcurrent|].
  eapply sem_pend_wait_trace_preserves_unregistered; eassumption.
Qed.

Lemma sem_pend_source_update_preserves_unregistered : forall before after selected old updated,
  before.(TskState).(inUsedTaskStates) selected = Some old ->
  after.(TskState).(inUsedTaskStates) =
    (glob_task_set_usedtask before.(TskState) selected updated).(inUsedTaskStates) ->
  (sem_pend_task_unregistered old -> sem_pend_task_unregistered updated) ->
  sem_pend_source_unregistered_transport before after.
Proof.
  intros before after selected old updated Hold Htasks Hupdate slot node Hnode Hclear.
  rewrite Htasks.
  change (exists current,
    (if Z.eqb slot selected then Some updated
      else before.(TskState).(inUsedTaskStates) slot) = Some current /\
    sem_pend_task_unregistered current).
  destruct (Z.eqb slot selected) eqn:Heq.
  - apply Z.eqb_eq in Heq; subst slot. assert (node = old) by congruence; subst node.
    exists updated; split; [reflexivity|apply Hupdate; exact Hclear].
  - exists node; split; [exact Hnode|exact Hclear].
Qed.

Lemma sem_pend_source_event_ready_preserves_unregistered : forall sg before eid kind message result priority after,
  event_task_rdy sg before eid kind message result = Some (priority, after) ->
  sem_pend_source_unregistered_transport before after.
Proof.
  intros sg before eid kind message result priority after Hsource.
  unfold event_task_rdy in Hsource.
  destruct (before.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
  destruct (before.(TskState).(prioTbl) (event_wait_priority before.(TskState) event)) as [| |selected]; try discriminate.
  destruct (before.(TskState).(inUsedTaskStates) selected) as [old|] eqn:Hold; [|discriminate].
  injection Hsource as Hpriority Hafter; subst after.
  eapply sem_pend_source_update_preserves_unregistered; [exact Hold|reflexivity|].
  intros [Hevent [Hmulti Hflag]]; unfold sem_pend_task_unregistered; repeat split; assumption || reflexivity.
Qed.

Lemma sem_pend_source_broadcast_preserves_unregistered : forall sg eid kind message result before priorities after,
  event_broadcast sg eid kind message result before priorities after ->
  sem_pend_source_unregistered_transport before after.
Proof.
  intros sg eid kind message result before priorities after Hsource; induction Hsource.
  - apply sem_pend_source_unregistered_transport_map_eq; reflexivity.
  - eapply sem_pend_source_unregistered_transport_trans; [|exact IHHsource].
    eapply sem_pend_source_event_ready_preserves_unregistered; eassumption.
Qed.

Lemma sem_pend_source_mutex_prepare_preserves_unregistered : forall sg mutex before after,
  mutex_del_prepare sg mutex before after -> sem_pend_source_unregistered_transport before after.
Proof.
  intros sg mutex before after Hprepare.
  apply sem_pend_source_projection_preserves_unregistered; intros slot old Hold.
  eapply tmr_task_sem_mutex_prepare_projection; eassumption.
Qed.

Lemma sem_pend_source_mutex_delete_preserves_unregistered : forall sg eid option before result after,
  mutex_del_critical sg eid option before result after -> sem_pend_source_unregistered_transport before after.
Proof.
  intros sg eid option before result after [event [mutex [_ [_ [_ Hsource]]]]].
  destruct (Z.eq_dec option 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
    + destruct Hsource as [prepared [Hprepare [-> Hresult]]].
      change (sem_pend_source_unregistered_transport before prepared).
      eapply sem_pend_source_mutex_prepare_preserves_unregistered; exact Hprepare.
    + destruct Hsource as [-> Hresult]; apply sem_pend_source_unregistered_transport_map_eq; reflexivity.
  - destruct (Z.eq_dec option 1).
    + destruct Hsource as [prepared [priorities [drained [Hprepare [Hbroadcast [-> Hresult]]]]]].
      change (sem_pend_source_unregistered_transport before drained).
      eapply sem_pend_source_unregistered_transport_trans.
      * eapply sem_pend_source_mutex_prepare_preserves_unregistered; exact Hprepare.
      * eapply sem_pend_source_broadcast_preserves_unregistered; exact Hbroadcast.
    + destruct Hsource as [-> Hresult]; apply sem_pend_source_unregistered_transport_map_eq; reflexivity.
Qed.

Lemma sem_pend_source_critical_preserves_unregistered : forall action sg before after,
  tmr_task_critical_source_client action -> kernel_client_step action sg before after ->
  sem_pend_source_unregistered_transport before after.
Proof.
  intros action sg before after Hsource; destruct Hsource; intro Hstep.
  - destruct Hstep as [_ [result [code [request [error [scheduled [Hcritical Hencoding]]]]]]].
    eapply sem_pend_source_mutex_delete_preserves_unregistered; exact Hcritical.
  - destruct Hstep as [result [code [request Hsource]]].
    destruct Hsource as [result code request checkpoint Hguard Hobservation|kind Htype Hnotmutex].
    + destruct Hobservation as [error [scheduled [Hcritical Hencoding]]].
      eapply sem_pend_source_mutex_delete_preserves_unregistered; exact Hcritical.
    + apply sem_pend_source_unregistered_transport_map_eq; reflexivity.
  - destruct Hstep as [_ [error Hsource]].
    apply sem_pend_source_projection_preserves_unregistered; intros slot old Hold.
    eapply tmr_task_sem_change_prio_projection; eassumption.
Qed.

Lemma sem_pend_source_call_receipt_preserves_unregistered : forall external action sg before after,
  tmr_task_source_call_receipt external action sg before after -> UCOS2_state_inv sg before ->
  sem_pend_source_unregistered_transport before after.
Proof.
  intros external action sg before after Hcall Hvalid.
  destruct Hcall as [action0 sg0 before0 after0 Hnontimer Hstep|cut sg0 before0 after0 Hstep|
    actor requested priority sg0 before0 after0 Hstep|actor pointer bits result sg0 before0 after0 Hstep|
    actor event kind message result sg0 before0 after0 Hinput Hstep|slot previous sg0 before0 after0 Hstep|
    context outgoing incoming resumed sg0 before0 after0 Hstep|action0 sg0 before0 after0 Hsem Hstep|
    action0 sg0 before0 after0 Hcritical Hstep|actor cut sg0 before0 after0 Hstep|
    actor cut sg0 before0 after0 Hstep|actor source_sg cut entry timers sg0 before0 after0 Hstep|
    actor event option result sg0 before0 after0 Hstep|
    actor source_sg priority result entry returned sg0 before0 after0 Hstep].
  - apply sem_pend_source_projection_preserves_unregistered; intros slot old Hold.
    eapply tmr_task_sem_nontimer_projection; eassumption.
  - apply sem_pend_source_projection_preserves_unregistered; intros slot old Hold.
    eapply tmr_task_sem_profile_projection; eassumption.
  - destruct Hstep as [code Hchange].
    apply sem_pend_source_projection_preserves_unregistered; intros slot old Hold.
    eapply tmr_task_sem_change_prio_projection; eassumption.
  - destruct Hstep as [schedule Hready].
    destruct (flag_task_rdy_result _ _ _ _ _ _ _ Hready)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]].
    eapply sem_pend_source_update_preserves_unregistered; [exact Hold|reflexivity|].
    intros [Hevent [Hmulti Hflag]]; unfold sem_pend_task_unregistered; repeat split; assumption || reflexivity.
  - destruct Hstep as [priority Hready].
    eapply sem_pend_source_event_ready_preserves_unregistered; exact Hready.
  - destruct Hstep as [Hold ->].
    apply sem_pend_source_projection_preserves_unregistered; intros tid node Hnode.
    eapply sem_pend_tick_task_projection; eassumption.
  - apply sem_pend_source_projection_preserves_unregistered; intros slot old Hold.
    eapply sem_pend_source_client_projection; [apply SemPendSourceSchedulerInstall|exact Hstep|exact Hold].
  - apply sem_pend_source_projection_preserves_unregistered; intros slot old Hold.
    eapply sem_pend_source_client_projection;
      [apply tmr_task_sem_source_client_wait_projection; exact Hsem|exact Hstep|exact Hold].
  - eapply sem_pend_source_critical_preserves_unregistered; eassumption.
  - apply sem_pend_source_projection_preserves_unregistered; intros slot old Hold.
    exact (tmr_task_sem_tick_projection _ cut _ _ _ _ Hstep Hold).
  - destruct Hstep as [timers [_ ->]]; apply sem_pend_source_unregistered_transport_map_eq; reflexivity.
  - destruct Hstep as [_ [_ [_ ->]]]; apply sem_pend_source_unregistered_transport_map_eq; reflexivity.
  - destruct Hstep as [node [_ [_ Habort]]].
    apply sem_pend_source_projection_preserves_unregistered; intros slot old Hold.
    eapply sem_pend_abort_critical_projection; eassumption.
  - apply sem_pend_source_projection_preserves_unregistered; intros slot old Hold.
    eapply tmr_task_sem_suspend_projection; eassumption.
Qed.

Definition sem_pend_source_call_fields sg call state : Prop :=
  state.(SchedState).(isRunning) = true /\ flag_pend_non_idle_at sg call state /\
  exists node, state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
    sem_pend_task_unregistered node.

Lemma sem_pend_client_source_calls_preserves_call_fields :
  forall external port critical sg observer event_observer first before stopped last after
    (trace : kernel_client_task_source_trace external port critical.(critical_region_clients)
      sg observer event_observer first before stopped last after),
  sem_pend_client_source_calls external port critical.(critical_region_clients)
    sg observer event_observer first before stopped last after trace ->
  UCOS2_state_inv sg before -> forall call,
  sem_pend_source_call_fields sg call before -> sem_pend_source_call_fields sg call after.
Proof.
  intros external port critical sg observer event_observer first before stopped last after trace Hcalls.
  induction Hcalls as [origin state|action first before middle transient last after stopped
    Hin Hforeign Hevent Hstep Hsource Htail Hcall Hcalls IH];
    intros Hvalid call Hfields.
  - exact Hfields.
  - assert (Htransient : UCOS2_state_inv sg transient).
    { exact (kernel_client_preserves_validity action
        (critical.(critical_region_client_certificates) action Hin)
        sg before transient Hvalid Hstep). }
    apply IH; [exact Htransient|].
    destruct Hfields as [Hrunning [Hnonidle [old [Hold Hclear]]]].
    pose proof (tmr_task_source_call_receipt_source _ _ _ _ _ Hcall) as Hclassification.
    split.
    + rewrite (tmr_task_source_client_running_eq external action sg before transient Hvalid Hclassification Hstep).
      exact Hrunning.
    + split.
      * apply (proj2 (tmr_task_source_client_preserves_idle_non_idle external action sg call before transient
          Hvalid Htransient Hrunning Hclassification Hstep)); exact Hnonidle.
      * eapply sem_pend_source_call_receipt_preserves_unregistered; eassumption.
Qed.

Lemma sem_pend_resumption_source_calls_preserves_call_fields :
  forall external port critical sg observer event_observer first before stopped last after
    (trace : kernel_resumption_task_source_trace external port critical.(critical_region_clients)
      sg observer event_observer first before stopped last after),
  sem_pend_resumption_source_calls external port critical.(critical_region_clients)
    sg observer event_observer first before stopped last after trace ->
  UCOS2_state_inv sg before -> forall call,
  sem_pend_source_call_fields sg call before -> sem_pend_source_call_fields sg call after.
Proof.
  intros external port critical sg observer event_observer first before stopped last after trace Hcalls.
  induction Hcalls as [origin state|first before stopped1 middle transient stopped2 last after
    Hsegment Htimer Htail Hsegment_calls Htail_calls IH]; intros Hvalid call Hfields.
  - exact Hfields.
  - destruct (kernel_client_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Hsegment)
      as [Hresources Hcontrol].
    apply IH.
    + exact (proj1 (kernel_client_resource_trace_transports_resources _ _ _ _ _ _ _
        critical.(critical_region_client_certificates) Hresources Hvalid)).
    + eapply sem_pend_client_source_calls_preserves_call_fields; eassumption.
Qed.

Lemma sem_pend_source_save_preserves_call_stage : forall environment critical sg call returned
  mask saved before acquired,
  UCOS2_state_inv sg before -> sem_pend_task_call_stage sg call before ->
  kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call returned mask saved before acquired ->
  sem_pend_source_modular_call_history environment critical sg call before returned acquired ->
  sem_pend_save_rely sg before acquired -> sem_pend_task_call_stage sg call acquired.
Proof.
  intros * Hvalid Hstage Hsave [trace [Hcalls Hnormal]]
    [Hcontrol [Hruntime [Hcache_rely Hready_rely]]].
  pose proof Hstage as [Hsource [Hrunning [old [Hready [Hg [Hnonidle Hnone]]]]]].
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsave) as Hinterval.
  destruct (critical_region_interval_transports_resources critical sg
    call.(os_sched_call_invocation) before acquired Hinterval Hvalid) as [Hvalid' _].
  assert (Hfields : sem_pend_source_call_fields sg call before).
  { split; [exact Hrunning|]. split.
    - exists old; split; [exact (proj1 Hready)|]. split; assumption.
    - exists old; split; [exact (proj1 Hready)|exact Hnone]. }
  destruct (sem_pend_resumption_source_calls_preserves_call_fields environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call.(os_sched_call_invocation) None
    call.(os_sched_call_origin) before false returned.(os_sched_call_origin) acquired trace Hcalls Hvalid
    call Hfields) as [Hrunning' [[nonidle [Hnonidle_node [Hnonidle_gen Hnonidle']]] [node [Hnode Hnone']]]].
  assert (nonidle = node) by congruence; subst nonidle.
  pose proof (proj1 Hnormal) as Hsame.
  assert (Hsource' : kernel_call_task_source call acquired).
  { exact (task_tcb_init_stack_registered_source_preserved
      environment.(task_stack_call_external) environment.(task_stack_call_port) critical sg
      call returned before acquired Hvalid Hsame trace Hsource). }
  destruct (kernel_call_task_source_current_at call acquired Hsource') as [Hcurrent [found [Hfound Hgen]]].
  assert (found = node) by congruence; subst found.
  assert (Hmember : In call.(os_sched_call_stack).(stackLeaseSlot) acquired.(SchedState).(readyList)).
  { apply Hready_rely; [exact (proj1 (proj2 Hready))|exact (proj1 (proj2 (proj2 (proj2 Hready))))]. }
  pose proof (Hcache_rely (sched_current_ready_at_implies_current_consistency _ _ _ _ Hready)) as Hcache.
  unfold sched_current_consistency in Hcache; rewrite Hcurrent in Hcache.
  destruct Hcache as [cached [Hcached Hpriority]].
  assert (cached = node) by congruence; subst cached.
  destruct (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid')))) _ Hmember)
    as [ready_node [Hready_node [_ Heffective]]].
  assert (ready_node = node) by congruence; subst ready_node.
  assert (Hready' : sched_current_ready_at acquired.(TskState) acquired.(SchedState)
    call.(os_sched_call_stack).(stackLeaseSlot) node) by (repeat split; assumption).
  split; [exact Hsource'|]. split; [exact Hrunning'|]. exists node; auto.
Qed.

Lemma sem_pend_source_acquire_phase_observation : forall environment critical sg call returned
  pevent eid observed mask saved before acquired,
  sem_pend_source_modular_call_history environment critical sg call before returned acquired ->
  UCOS2_state_inv sg before -> interrupt_in_range acquired.(IntrState) ->
  sem_pend_save_phase_pre (SemPendAcquirePhase pevent eid observed)
    (Some environment) critical sg call mask before ->
  kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call returned mask saved before acquired ->
  kernel_call_normal_return call before returned acquired ->
  sem_pend_save_rely sg before acquired ->
  sem_pend_save_phase_observation (SemPendAcquirePhase pevent eid observed)
    (Some environment) critical sg call returned mask saved before acquired.
Proof.
  intros * Hsource Hvalid Hrange Hpre Hsave Hnormal Hrely.
  destruct (sem_pend_modular_acquire_observation environment critical sg call returned
    pevent eid observed mask saved before acquired Hvalid Hpre Hsave Hnormal)
    as [current Hacquire].
  exists current; split; [exact Hacquire|]. intro Hzero.
  pose proof Hpre as [_ [Hnonnull [Hclear [Hadmit Hnonblocking]]]].
  assert (Hpreclear : sem_pend_precritical_error pevent (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None).
  { unfold sem_pend_precritical_error; rewrite (proj2 (Z.eqb_neq _ _) Hnonnull); exact Hclear. }
  destruct (Hadmit Hpreclear) as [[Hstage [Hruntime Havailable]]|Hpositive].
  2: { specialize (Hpositive returned mask saved acquired observed current Hacquire); lia. }
  pose proof (sem_pend_source_save_preserves_call_stage environment critical sg call returned
    mask saved before acquired Hvalid Hstage Hsave Hsource Hrely) as Hstage'.
  split; [exact Hstage'|].
  destruct Hrely as [[Hrunning Hcounters] [Hruntime_rely [Hcache Hready]]].
  assert (Hidle : task_idle_ready sg acquired.(TskState)).
  { apply (Hruntime_rely Hruntime); exact (proj1 (proj2 Hstage')). }
  assert (Havailable' : kernel_call_stack_available call acquired).
  { pose proof (proj2 Hnormal Havailable) as Hreturned.
    unfold kernel_call_stack_available in *; rewrite (proj1 (proj2 (proj1 Hnormal))) in Hreturned;
      exact Hreturned. }
  unfold sem_pend_optional_blocking_call_stage, sem_pend_blocking_call_stage.
  split; [exact Hidle|]. split; [exact Havailable'|].
  unfold interrupt_in_range in Hrange; rewrite Hcounters in Hrange.
  unfold sem_pend_context_error in Hclear.
  repeat match type of Hclear with
  | (if ?condition then _ else _) = None =>
      destruct condition eqn:? in Hclear; try discriminate Hclear
  end.
  repeat match goal with
  | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
  end.
  rewrite Hcounters; lia.
Qed.

