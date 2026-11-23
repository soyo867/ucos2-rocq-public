Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Relations.Relation_Operators.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fresh_fields_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_source_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_pend_abort_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_idle_guard_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.flag Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.sem Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_client_invariants.
Import TaskStateDef ListNotations.
Local Open Scope Z_scope.

(** Observe an OLD live slot and its generation. Publication may create a
    new slot, so equality of entire optional-pointer maps is not claimed.
    This property neither grants a source step nor asserts any initial zero. *)
Definition tmr_task_multi_pointer_transport before after : Prop :=
  forall slot old, before.(TskState).(inUsedTaskStates) slot = Some old ->
  exists current, after.(TskState).(inUsedTaskStates) slot = Some current /\
    current.(taskGeneration) = old.(taskGeneration) /\
    current.(tcbEventMultiPtr) = old.(tcbEventMultiPtr).

Lemma tmr_task_multi_pointer_transport_map_eq : forall before after,
  after.(TskState).(inUsedTaskStates) = before.(TskState).(inUsedTaskStates) ->
  tmr_task_multi_pointer_transport before after.
Proof. intros before after Hmap slot old Hold; exists old; rewrite Hmap; auto. Qed.

Lemma tmr_task_multi_pointer_transport_trans : forall before middle after,
  tmr_task_multi_pointer_transport before middle ->
  tmr_task_multi_pointer_transport middle after -> tmr_task_multi_pointer_transport before after.
Proof.
  intros before middle after Hfirst Hsecond slot old Hold.
  destruct (Hfirst slot old Hold) as [node [Hnode [Hgen Hptr]]].
  destruct (Hsecond slot node Hnode) as [current [Hcurrent [Hgen' Hptr']]].
  exists current; split; [exact Hcurrent|]. split; congruence.
Qed.

Lemma tmr_task_update_multi_pointer_transport : forall before after selected old updated,
  before.(TskState).(inUsedTaskStates) selected = Some old ->
  after.(TskState).(inUsedTaskStates) =
    (glob_task_set_usedtask before.(TskState) selected updated).(inUsedTaskStates) ->
  updated.(taskGeneration) = old.(taskGeneration) ->
  updated.(tcbEventMultiPtr) = old.(tcbEventMultiPtr) ->
  tmr_task_multi_pointer_transport before after.
Proof.
  intros before after selected old updated Hold Hmap Hgen Hptr slot node Hnode.
  rewrite Hmap; cbn [glob_task_set_usedtask inUsedTaskStates].
  destruct (Z.eqb slot selected) eqn:Heq.
  - apply Z.eqb_eq in Heq; subst slot. assert (node = old) by congruence; subst node.
    exists updated; auto.
  - exists node; auto.
Qed.

(** The old waiter projection is used ONLY for generation here. It has no
    observation of MultiPtr and is never used to derive its value. *)
Lemma tmr_task_wait_trace_generation_eq : forall before after,
  clos_refl_trans TaskAbstractState sem_pend_wait_effect before after ->
  after.(taskGeneration) = before.(taskGeneration).
Proof.
  intros before after Htrace; induction Htrace.
  - destruct H; try reflexivity.
    + pose proof (tick_task_preserves_non_timeout_fields t) as Hfields; cbv zeta in Hfields; tauto.
    + exact (proj1 (proj2 H)).
  - reflexivity.
  - congruence.
Qed.

Lemma tmr_task_projected_source_multi_pointer_transport : forall action sg before after,
  sem_pend_projected_source_client action -> kernel_client_step action sg before after ->
  tmr_task_multi_pointer_transport before after.
Proof.
  intros action sg before after Hsource Hstep slot old Hold.
  destruct (sem_pend_source_client_projection action sg before after slot old Hsource Hstep Hold)
    as [current [Hcurrent Htrace]].
  pose proof (tmr_task_source_client_multi_pointer action sg before after Hsource Hstep slot) as Hptr.
  rewrite Hcurrent, Hold in Hptr; cbn in Hptr.
  exists current; split; [exact Hcurrent|]. split.
  - eapply tmr_task_wait_trace_generation_eq; exact Htrace.
  - congruence.
Qed.

Lemma tmr_task_creation_multi_pointer_transport : forall action sg before after,
  task_in_range sg before.(TskState) ->
  kernel_client_step (task_creation_client action) sg before after ->
  tmr_task_multi_pointer_transport before after.
Proof.
  intros action sg before after Htasks [Hguard [_ ->]].
  destruct action as [priority entry slot rest image|priority entry allocation image|
    priority invocation node|invocation].
  - apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - pose proof (task_commit_identity_private before.(TskState) priority invocation node
      (proj1 Hguard)) as Hprivate.
    pose proof (proj1 (task_private_excludes_public sg before.(TskState) node.(taskID)
      (proj1 Htasks) Hprivate)) as Hfresh.
    intros slot old Hold.
    destruct (task_commit_transports_old_fields before.(TskState) priority invocation node slot old
      Hfresh Hold) as [current [Hcurrent Hfields]].
    exists current; split; [exact Hcurrent|].
    pose proof (f_equal taskGeneration Hfields) as Hgen.
    pose proof (f_equal tcbEventMultiPtr Hfields) as Hptr.
    exact (conj Hgen Hptr).
  - apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
Qed.

Lemma tmr_task_nontimer_multi_pointer_transport : forall action sg before after,
  tmr_task_nontimer_source_client action -> task_in_range sg before.(TskState) ->
  kernel_client_step action sg before after -> tmr_task_multi_pointer_transport before after.
Proof.
  intros action sg before after Hsource Htasks; destruct Hsource; intro Hstep.
  - eapply tmr_task_creation_multi_pointer_transport; eassumption.
  - destruct (task_create_stack_publication_raw_projection sg publication before after Hstep)
      as [Hraw ->].
    change (tmr_task_multi_pointer_transport before
      (task_create_stack_publication_raw_state sg publication before)).
    eapply tmr_task_creation_multi_pointer_transport; eassumption.
  - destruct Hstep as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - destruct Hstep as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - destruct Hstep as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - destruct Hstep as [_ [result Hstep]]. unfold event_create_allocate_critical in Hstep.
    destruct before.(EventState).(unUsedEventStates).
    + destruct Hstep as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
    + destruct Hstep as [image [_ [_ ->]]]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - destruct Hstep as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - destruct Hstep as [_ [_ ->]]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - destruct Hstep as [_ [_ [_ [_ [result [a [Ha Hstep]]]]]]].
    destruct free; destruct Hstep as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - destruct Hstep as [_ [_ [_ [_ ->]]]]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - eapply tmr_task_projected_source_multi_pointer_transport; [apply SemPendSourceResume|exact Hstep].
  - destruct Hstep as [event [_ [_ [node [fields [_ [_ [_ ->]]]]]]]].
    destruct (Z.ltb 0 fields.(semCount)); apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
Qed.

Lemma tmr_task_change_prio_multi_pointer_transport : forall sg requested priority before code after,
  task_change_prio_critical sg requested priority before code after ->
  tmr_task_multi_pointer_transport before after.
Proof.
  intros sg requested priority before code after Hsource; unfold task_change_prio_critical in Hsource.
  destruct (before.(TskState).(prioTbl) priority).
  - destruct Hsource as [selected [Hselection Hsource]]. unfold task_change_prio_selected_effect in Hsource.
    destruct (Z.eqb selected sg.(osLowestPrio)).
    + destruct Hsource as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
    + destruct (before.(TskState).(prioTbl) selected) as [| |slot].
      * destruct Hsource as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
      * destruct Hsource as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
      * destruct Hsource as [old [Hold [_ ->]]].
        eapply tmr_task_update_multi_pointer_transport; [exact Hold|reflexivity|reflexivity|reflexivity].
  - destruct Hsource as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - destruct Hsource as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
Qed.

Lemma tmr_task_event_ready_multi_pointer_transport : forall sg before eid kind message result priority after,
  event_task_rdy sg before eid kind message result = Some (priority, after) ->
  tmr_task_multi_pointer_transport before after.
Proof.
  intros sg before eid kind message result priority after Hsource.
  unfold event_task_rdy in Hsource.
  destruct (before.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
  destruct (before.(TskState).(prioTbl) (event_wait_priority before.(TskState) event))
    as [| |selected]; try discriminate.
  destruct (before.(TskState).(inUsedTaskStates) selected) as [old|] eqn:Hold; [|discriminate].
  injection Hsource as Hpriority Hafter; subst after.
  eapply tmr_task_update_multi_pointer_transport; [exact Hold|reflexivity|reflexivity|reflexivity].
Qed.

Lemma tmr_task_event_broadcast_multi_pointer_transport : forall sg eid kind message result before priorities after,
  event_broadcast sg eid kind message result before priorities after ->
  tmr_task_multi_pointer_transport before after.
Proof.
  intros sg eid kind message result before priorities after Hsource; induction Hsource.
  - apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - eapply tmr_task_multi_pointer_transport_trans; [|exact IHHsource].
    eapply tmr_task_event_ready_multi_pointer_transport; eassumption.
Qed.

Lemma tmr_task_tick_scan_multi_pointer_transport : forall sg visited before,
  tmr_task_multi_pointer_transport before (time_tick_scan sg before visited).
Proof.
  intros sg visited; induction visited as [|selected rest IH]; intros before.
  - apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - change (tmr_task_multi_pointer_transport before
      (time_tick_scan sg (time_tick_visit sg before selected) rest)).
    eapply tmr_task_multi_pointer_transport_trans; [|apply IH].
    unfold time_tick_visit; destruct (before.(TskState).(inUsedTaskStates) selected) as [old|] eqn:Hold.
    + eapply (tmr_task_projected_source_multi_pointer_transport (sem_pend_tick_source_client selected) sg);
        [constructor|exists old; split; [exact Hold|reflexivity]].
    + apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
Qed.

Lemma tmr_task_tick_cut_multi_pointer_transport : forall sg cut before after,
  tmr_task_tick_cut_source sg cut before after -> tmr_task_multi_pointer_transport before after.
Proof.
  intros sg cut before after; destruct cut; cbn [tmr_task_tick_cut_source]; intro Hsource.
  - subst after; unfold time_tick_clock_step_state; destruct (tick_step_advance _ _);
      apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - subst after; unfold time_tick_serialized_after_hook.
    assert (Hclock : tmr_task_multi_pointer_transport before (time_tick_clock_step_state before)).
    { unfold time_tick_clock_step_state; destruct (tick_step_advance _ _);
        apply tmr_task_multi_pointer_transport_map_eq; reflexivity. }
    destruct (time_tick_process_tasks before); [|exact Hclock].
    eapply tmr_task_multi_pointer_transport_trans; [exact Hclock|apply tmr_task_tick_scan_multi_pointer_transport].
  - destruct Hsource as [state error Herror|state eid event error Hargument Hpointer Hlookup Htype|
      state eid event actual current Hargument Hpointer Hlookup Htype Hcritical];
      try (apply tmr_task_multi_pointer_transport_map_eq; reflexivity).
    destruct Hcritical as [node [_ Hstep]].
    lazymatch type of Hstep with | (if ?condition then _ else _) => destruct condition in Hstep end.
    + destruct Hstep as [fields [_ Hstep]].
      lazymatch type of Hstep with | (if ?condition then _ else _) => destruct condition in Hstep end;
        destruct Hstep as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
    + destruct Hstep as [_ [priority Hstep]].
      eapply tmr_task_event_ready_multi_pointer_transport; exact Hstep.
Qed.

Lemma tmr_task_mutex_prepare_multi_pointer_transport : forall sg mutex before after,
  mutex_del_prepare sg mutex before after -> tmr_task_multi_pointer_transport before after.
Proof.
  intros sg mutex before after Hprepare; unfold mutex_del_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis));
    [subst; apply tmr_task_multi_pointer_transport_map_eq; reflexivity|].
  destruct mutex.(mfOwner) as [owner|].
  - destruct Hprepare as [node [priority [Hnode [_ ->]]]].
    unfold mutex_del_owner_priority_state; destruct Z.eq_dec.
    + apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
    + eapply tmr_task_update_multi_pointer_transport; [exact Hnode|reflexivity|reflexivity|reflexivity].
  - subst; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
Qed.

Lemma tmr_task_mutex_delete_multi_pointer_transport : forall sg eid opt before result after,
  mutex_del_critical sg eid opt before result after -> tmr_task_multi_pointer_transport before after.
Proof.
  intros sg eid opt before result after [event [mutex [_ [_ [_ Hsource]]]]].
  destruct (Z.eq_dec opt 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
    + destruct Hsource as [prepared [Hprepare [-> Hresult]]].
      change (tmr_task_multi_pointer_transport before prepared).
      eapply tmr_task_mutex_prepare_multi_pointer_transport; exact Hprepare.
    + destruct Hsource as [-> Hresult]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - destruct (Z.eq_dec opt 1).
    + destruct Hsource as [prepared [priorities [drained [Hprepare [Hbroadcast [-> Hresult]]]]]].
      change (tmr_task_multi_pointer_transport before drained).
      eapply tmr_task_multi_pointer_transport_trans.
      * eapply tmr_task_mutex_prepare_multi_pointer_transport; exact Hprepare.
      * eapply tmr_task_event_broadcast_multi_pointer_transport; exact Hbroadcast.
    + destruct Hsource as [-> Hresult]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
Qed.

Lemma tmr_task_critical_multi_pointer_transport : forall action sg before after,
  tmr_task_critical_source_client action -> kernel_client_step action sg before after ->
  tmr_task_multi_pointer_transport before after.
Proof.
  intros action sg before after Hsource; destruct Hsource; intro Hstep.
  - destruct Hstep as [_ [result [code [request [error [scheduled [Hcritical Hencoding]]]]]]].
    eapply tmr_task_mutex_delete_multi_pointer_transport; exact Hcritical.
  - destruct Hstep as [result [code [request Hsource]]].
    destruct Hsource as [result code request checkpoint Hguard Hobservation|kind Htype Hnotmutex].
    + destruct Hobservation as [error [scheduled [Hcritical Hencoding]]].
      eapply tmr_task_mutex_delete_multi_pointer_transport; exact Hcritical.
    + apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - destruct Hstep as [_ [error Hsource]]; eapply tmr_task_change_prio_multi_pointer_transport; exact Hsource.
Qed.

(** All fourteen original constructors. Only creation/publication needs
    the actual input Task range, to exclude overwriting this old live slot.
    TaskDelete's own Prepare/Recycle leaves are NOT constructors here. *)
Lemma tmr_task_source_call_multi_pointer_transport : forall external action sg before after,
  tmr_task_source_call_receipt external action sg before after ->
  task_in_range sg before.(TskState) -> tmr_task_multi_pointer_transport before after.
Proof.
  intros external action sg before after Hcall Htasks.
  destruct Hcall as [action0 sg0 before0 after0 Hnontimer Hstep|cut sg0 before0 after0 Hstep|
    actor requested priority sg0 before0 after0 Hstep|actor pointer bits result sg0 before0 after0 Hstep|
    actor event kind message result sg0 before0 after0 Hinput Hstep|slot previous sg0 before0 after0 Hstep|
    context outgoing incoming resumed sg0 before0 after0 Hstep|action0 sg0 before0 after0 Hsem Hstep|
    action0 sg0 before0 after0 Hcritical Hstep|actor cut sg0 before0 after0 Hstep|
    actor cut sg0 before0 after0 Hstep|actor source_sg cut entry timers sg0 before0 after0 Hstep|
    actor event option result sg0 before0 after0 Hstep|
    actor source_sg priority result entry returned sg0 before0 after0 Hstep].
  - eapply tmr_task_nontimer_multi_pointer_transport; eassumption.
  - destruct Hstep as [Hinput ->]; destruct cut as [|running|slot node].
    + apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
    + apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
    + destruct Hinput as [_ Hnode].
      eapply tmr_task_update_multi_pointer_transport; [exact Hnode|reflexivity|reflexivity|reflexivity].
  - destruct Hstep as [code Hstep]; eapply tmr_task_change_prio_multi_pointer_transport; exact Hstep.
  - destruct Hstep as [schedule Hstep].
    destruct (flag_task_rdy_result _ _ _ _ _ _ _ Hstep)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]].
    eapply tmr_task_update_multi_pointer_transport; [exact Hold|reflexivity|reflexivity|reflexivity].
  - destruct Hstep as [priority Hstep]; eapply tmr_task_event_ready_multi_pointer_transport; exact Hstep.
  - destruct Hstep as [Hold ->].
    eapply (tmr_task_projected_source_multi_pointer_transport (sem_pend_tick_source_client slot) sg0);
      [constructor|exists previous; split; [exact Hold|reflexivity]].
  - eapply tmr_task_projected_source_multi_pointer_transport; [apply SemPendSourceSchedulerInstall|exact Hstep].
  - eapply tmr_task_projected_source_multi_pointer_transport;
      [apply tmr_task_sem_source_client_wait_projection; exact Hsem|exact Hstep].
  - eapply tmr_task_critical_multi_pointer_transport; eassumption.
  - eapply tmr_task_tick_cut_multi_pointer_transport; exact Hstep.
  - destruct Hstep as [timers [_ ->]]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - destruct Hstep as [_ [_ [_ ->]]]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - destruct Hstep as [node [Hnode [_ Habort]]].
    destruct Habort as [actual [Hactual Habort]].
    lazymatch type of Habort with | (if ?condition then _ else _) => destruct condition in Habort end.
    + destruct Habort as [_ ->]; apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
    + lazymatch type of Habort with | (if ?condition then _ else _) => destruct condition in Habort end.
      * destruct Habort as [priorities [Hloop Hresult]].
        eapply tmr_task_event_broadcast_multi_pointer_transport; exact Hloop.
      * destruct Habort as [priority [Hready Hresult]].
        eapply tmr_task_event_ready_multi_pointer_transport; exact Hready.
  - destruct Hstep as [_ [_ [_ [Hargument Hcritical]]]].
    destruct (task_suspend_idle_guard_original_or_unchanged _ _ _ _ _ Hcritical) as [->|Horiginal].
    + apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
    + eapply (tmr_task_projected_source_multi_pointer_transport (task_suspend_critical_client actor priority) sg0);
        [apply SemPendSourceSuspend|split; [exact Hargument|exists result; exact Horiginal]].
Qed.

(** The receipts below are already indexed by the original proofs. Their
    actors, task/Event observers, stopped bits, origins and intermediate
    states are retained; no new execution relation or public domain is used. *)
Lemma tmr_task_source_trace_multi_pointer_transport :
  forall external clients sg observer event_observer before stopped after
    (trace : kernel_client_resource_trace clients sg observer event_observer before stopped after),
  sem_pend_source_trace_receipt external clients sg observer event_observer before stopped after trace ->
  tmr_task_multi_pointer_transport before after.
Proof.
  intros external clients sg observer event_observer before stopped after trace Hreceipt.
  induction Hreceipt as [state|action before middle after stopped Hin Hforeign Hevent Hstep Htail
    Hcall Hfacts Hreceipt IH].
  - apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - eapply tmr_task_multi_pointer_transport_trans; [|exact IH].
    eapply tmr_task_source_call_multi_pointer_transport; [exact Hcall|exact (proj1 (proj2 Hfacts))].
Qed.

Lemma tmr_task_registered_trace_multi_pointer_transport :
  forall external critical sg observer event_observer before stopped after
    (trace : kernel_client_resource_trace critical.(critical_region_clients)
      sg observer event_observer before stopped after),
  tmr_task_source_trace_calls external critical.(critical_region_clients)
    sg observer event_observer before stopped after trace ->
  UCOS2_state_inv sg before -> tmr_task_multi_pointer_transport before after.
Proof.
  intros external critical sg observer event_observer before stopped after trace Hcalls Hvalid.
  eapply tmr_task_source_trace_multi_pointer_transport.
  eapply sem_pend_source_trace_receipt_from_valid; eassumption.
Qed.

Lemma tmr_task_client_source_multi_pointer_transport :
  forall external port clients sg observer event_observer first before stopped last after
    (trace : kernel_client_task_source_trace external port clients sg observer event_observer
      first before stopped last after),
  sem_pend_client_source_local_receipt external port clients sg observer event_observer
    first before stopped last after trace -> tmr_task_multi_pointer_transport before after.
Proof.
  intros external port clients sg observer event_observer first before stopped last after trace Hreceipt.
  induction Hreceipt as [origin state|action first before middle transient last after stopped
    Hin Hforeign Hevent Hstep Hexecution Htail Hcall Hfacts Hreceipt IH].
  - apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - eapply tmr_task_multi_pointer_transport_trans; [|exact IH].
    eapply tmr_task_source_call_multi_pointer_transport; [exact Hcall|exact (proj1 (proj2 Hfacts))].
Qed.

Lemma tmr_task_resumption_source_multi_pointer_transport :
  forall external port clients sg observer event_observer first before stopped last after
    (trace : kernel_resumption_task_source_trace external port clients sg observer event_observer
      first before stopped last after),
  sem_pend_resumption_source_local_receipt external port clients sg observer event_observer
    first before stopped last after trace -> tmr_task_multi_pointer_transport before after.
Proof.
  intros external port clients sg observer event_observer first before stopped last after trace Hreceipt.
  induction Hreceipt as [origin state|first before stopped1 middle transient stopped2 last after
    segment timer tail Hsegment Htail IH].
  - apply tmr_task_multi_pointer_transport_map_eq; reflexivity.
  - eapply tmr_task_multi_pointer_transport_trans; [|exact IH].
    eapply tmr_task_client_source_multi_pointer_transport; exact Hsegment.
Qed.

(** A Pend consumer at the SAME actual returned call. Its zero comes from
    the old live caller, never from cfgMulti=false, a physical owner, or
    the old waiter projection. The source packet must still be produced at
    the actual interpreter; this theorem does not infer it from plain post. *)
Lemma tmr_task_resumption_return_multi_zero :
  forall external port clients sg observer event_observer original returned before stopped after old
    (trace : kernel_resumption_task_source_trace external port clients sg observer event_observer
      original.(os_sched_call_origin) before stopped returned.(os_sched_call_origin) after),
  sem_pend_resumption_source_local_receipt external port clients sg observer event_observer
    original.(os_sched_call_origin) before stopped returned.(os_sched_call_origin) after trace ->
  kernel_stack_call_same_call returned original ->
  before.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some old ->
  old.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) ->
  old.(tcbEventMultiPtr) = 0 ->
  exists current,
    after.(TskState).(inUsedTaskStates) returned.(os_sched_call_stack).(stackLeaseSlot) = Some current /\
    current.(taskGeneration) = returned.(os_sched_call_stack).(stackLeaseGeneration) /\
    current.(tcbEventMultiPtr) = 0 /\
    (forall node, after.(TskState).(inUsedTaskStates)
      returned.(os_sched_call_stack).(stackLeaseSlot) = Some node -> node.(tcbEventMultiPtr) = 0).
Proof.
  intros external port clients sg observer event_observer original returned before stopped after old
    trace Hreceipt [_ [_ Hstack]] Hold Hgen Hzero.
  destruct (tmr_task_resumption_source_multi_pointer_transport external port clients sg observer
    event_observer _ _ _ _ _ trace Hreceipt _ old Hold)
    as [current [Hcurrent [Hgeneration Hpointer]]].
  rewrite Hstack; exists current; split; [exact Hcurrent|].
  split; [congruence|]. split; [congruence|].
  intros node Hnode; assert (node = current) by congruence; subst node; congruence.
Qed.
