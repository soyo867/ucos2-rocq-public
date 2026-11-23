Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.Lists.List.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_c_segment_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_c_idle_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_api_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_inherit_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_critical_control_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_client_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_pend_abort_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_idle_guard_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_api_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_c_step_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_masked_c_step_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_history_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_delete_call_source_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_delete_return_source_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_irq_completion_source_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_irq_entry_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_envelope_spec.
Import DeleteComponent TaskStateDef ListNotations CriticalComponent.
Local Open Scope Z_scope.

(** Only the two existing complete acquired Critical C operations receive
    the additional admission. Their actual actor and source step are retained. *)
Inductive sem_pend_framed_critical_client : KernelClientAction -> Prop :=
| SemPendFramedChangePrio : forall actor requested priority,
    sem_pend_framed_critical_client
      (task_change_prio_critical_call_client actor requested priority)
| SemPendFramedMutexDel : forall actor eid option,
    sem_pend_framed_critical_client (mutex_del_critical_call_client actor eid option).

Definition sem_pend_sem_handle_frame (before after : UCOS2_Verify_State) : Prop :=
  forall eid previous, mutex_query_lookup before eid previous ->
    previous.(eventType) = OS_EVENT_TYPE_SEM ->
    exists current, mutex_query_lookup after eid current /\
      current.(eventGeneration) = previous.(eventGeneration) /\
      current.(eventType) = previous.(eventType).

Definition sem_pend_client_observer_frame observer before after : Prop :=
  task_creation_frame observer before.(TskState) after.(TskState) /\
  sem_pend_sem_handle_frame before after.

Lemma sem_pend_change_prio_sem_handle_frame : forall sg requested priority before error after,
  task_change_prio_critical sg requested priority before error after ->
  sem_pend_sem_handle_frame before after.
Proof.
  intros sg requested priority before error after Hcritical.
  unfold task_change_prio_critical in Hcritical.
  destruct (before.(TskState).(prioTbl) priority).
  - destruct Hcritical as [selected [Hselection Hcritical]].
    unfold task_change_prio_selected_effect in Hcritical.
    lazymatch type of Hcritical with
    | context [if ?test then _ else _] => destruct test eqn:Hselected in Hcritical
    end.
    + destruct Hcritical as [_ ->]; intros eid previous Hlookup Htype; exists previous; auto.
    + destruct (before.(TskState).(prioTbl) selected).
      * destruct Hcritical as [_ ->]; intros eid previous Hlookup Htype; exists previous; auto.
      * destruct Hcritical as [_ ->]; intros eid previous Hlookup Htype; exists previous; auto.
      * destruct Hcritical as [old [Hold [_ ->]]].
        intros eid previous Hlookup Htype.
        unfold mutex_query_lookup in *.
        unfold task_change_priority_state, task_change_priority_events; cbn.
        destruct old.(eventPtr) as [changed|]; [|exists previous; auto].
        destruct (before.(EventState).(inUsedEventStates) changed) as [event|] eqn:Hchanged;
          [|exists previous; auto].
        unfold update_event_field_raw; cbn [inUsedEventStates].
        lazymatch goal with
        | |- context [if ?test then _ else _] => destruct test eqn:Heq
        end.
        -- apply Z.eqb_eq in Heq; subst changed.
           assert (event = previous) by congruence; subst event.
           eexists; split; [reflexivity|].
           unfold event_insert_waiter, event_set_wait_list; cbn; auto.
        -- exists previous; auto.
  - destruct Hcritical as [_ ->]; intros eid previous Hlookup Htype; exists previous; auto.
  - destruct Hcritical as [_ ->]; intros eid previous Hlookup Htype; exists previous; auto.
Qed.

Lemma sem_pend_event_ready_other_lookup : forall sg before changed kind message result priority after eid,
  event_task_rdy sg before changed kind message result = Some (priority, after) ->
  eid <> changed ->
  after.(EventState).(inUsedEventStates) eid = before.(EventState).(inUsedEventStates) eid.
Proof.
  intros sg before changed kind message result priority after eid Hstep Hneq.
  unfold event_task_rdy in Hstep.
  destruct (before.(EventState).(inUsedEventStates) changed) as [event|]; [|discriminate].
  destruct (before.(TskState).(prioTbl) (event_wait_priority before.(TskState) event))
    as [| |tid]; try discriminate.
  destruct (before.(TskState).(inUsedTaskStates) tid) as [node|]; [|discriminate].
  injection Hstep as _ <-.
  unfold event_wake_state; cbn [replace_SchedS replace_EventS replace_TskS EventState update_event_field_raw inUsedEventStates].
  apply Z.eqb_neq in Hneq; rewrite Hneq; reflexivity.
Qed.

Lemma sem_pend_broadcast_other_lookup : forall sg changed kind message result before priorities after eid,
  event_broadcast sg changed kind message result before priorities after -> eid <> changed ->
  after.(EventState).(inUsedEventStates) eid = before.(EventState).(inUsedEventStates) eid.
Proof.
  intros sg changed kind message result before priorities after eid Hrun Hneq.
  induction Hrun; [reflexivity|].
  rewrite IHHrun; eapply sem_pend_event_ready_other_lookup; eassumption.
Qed.

Lemma sem_pend_mutex_del_sem_handle_frame : forall sg changed option before result after,
  mutex_del_critical sg changed option before result after -> sem_pend_sem_handle_frame before after.
Proof.
  intros sg changed option before result after [event [mutex [Hlookup [Hmutex [_ Hrun]]]]]
    eid previous Hprevious Hsem.
  unfold mutex_query_lookup in *.
  assert (Hneq : eid <> changed).
  { intro Heq; subst eid; assert (previous = event) by congruence; subst previous; congruence. }
  assert (Hrecycle : forall state image,
    (mutex_del_recycle_state sg changed image state).(EventState).(inUsedEventStates) eid =
      state.(EventState).(inUsedEventStates) eid).
  { intros; unfold mutex_del_recycle_state, event_recycle; cbn.
    unfold kernel_map_set; destruct (Z.eq_dec eid changed); congruence. }
  destruct (Z.eq_dec option 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
    + destruct Hrun as [prepared [Hprepare [-> Hresult]]].
      exists previous; split; [|auto]. rewrite Hrecycle.
      rewrite (mutex_del_prepare_event_state_eq _ _ _ _ Hprepare); exact Hprevious.
    + destruct Hrun as [-> Hresult]; exists previous; auto.
  - destruct (Z.eq_dec option 1).
    + destruct Hrun as [prepared [priorities [drained [Hprepare [Hbroadcast [-> Hresult]]]]]].
      exists previous; split; [|auto]. rewrite Hrecycle.
      rewrite (sem_pend_broadcast_other_lookup _ _ _ _ _ _ _ _ _ Hbroadcast Hneq).
      rewrite (mutex_del_prepare_event_state_eq _ _ _ _ Hprepare); exact Hprevious.
    + destruct Hrun as [-> Hresult]; exists previous; auto.
Qed.

Lemma sem_pend_framed_critical_observer_frame : forall action sg before after observer,
  sem_pend_framed_critical_client action -> kernel_client_step action sg before after ->
  sem_pend_client_observer_frame observer before after.
Proof.
  intros action sg before after observer Htyped Hstep; destruct Htyped.
  - destruct Hstep as [Hguard [error Hcritical]]; split.
    + exact (proj1 (task_change_prio_critical_creation_name_frames
        sg requested priority before error after observer observer Hcritical)).
    + eapply sem_pend_change_prio_sem_handle_frame; exact Hcritical.
  - destruct Hstep as [result [code [request Hobservation]]]; split.
    + destruct (proj1 (mutex_del_critical_call_observation_fields
        sg eid option before result code request after Hobservation))
        as [Hnodes [Hparked [Hlife Hrest]]].
      unfold task_creation_frame, task_creation_view; rewrite Hlife; reflexivity.
    + destruct Hobservation as [result code request after Hguard [error [scheduled [Hcritical Hencoding]]]
        |kind Htype Hnotmutex].
      * eapply sem_pend_mutex_del_sem_handle_frame; exact Hcritical.
      * intros watched previous Hlookup Htype'; exists previous; auto.
Qed.

Lemma sem_pend_mutex_post_sem_handle_frame : forall sg changed caller before result schedule after,
  mutex_post_critical sg changed caller before result schedule after ->
  sem_pend_sem_handle_frame before after.
Proof.
  intros sg changed caller before result schedule after Hcritical watched previous Hprevious Hsem.
  unfold mutex_query_lookup in *.
  assert (Hcommit : forall state event mutex owner snapshot,
    watched <> changed ->
    (mutex_post_owner_state state changed event mutex owner snapshot).(EventState).(inUsedEventStates) watched =
      state.(EventState).(inUsedEventStates) watched).
  { intros; cbn [mutex_post_owner_state replace_EventS EventState update_event_field_raw inUsedEventStates].
    rewrite (proj2 (Z.eqb_neq watched changed) H); reflexivity. }
  destruct Hcritical as [entry event mutex Hlookup Htype Hfields Howner
    |entry event mutex prepared Hlookup Htype Hfields Howner Hprepare Hempty
    |entry event mutex prepared priority woken found owner Hlookup Htype Hfields Howner
       Hprepare Hnonempty Hwake Hfound Htable].
  - exists previous; auto.
  - assert (Hneq : watched <> changed).
    { intro Heq; subst watched; assert (previous = event) by congruence; subst previous; congruence. }
    exists previous; split; [|auto]. rewrite Hcommit by exact Hneq.
    rewrite (mutex_post_prepare_event_state_eq _ _ _ _ _ Hprepare); exact Hprevious.
  - assert (Hneq : watched <> changed).
    { intro Heq; subst watched; assert (previous = event) by congruence; subst previous; congruence. }
    exists previous; split; [|auto]. rewrite Hcommit by exact Hneq.
    rewrite (sem_pend_event_ready_other_lookup _ _ _ _ _ _ _ _ _ Hwake Hneq).
    rewrite (mutex_post_prepare_event_state_eq _ _ _ _ _ Hprepare); exact Hprevious.
Qed.

Lemma sem_pend_mutex_inheritance_sem_handle_frame : forall sg before owner node base waiter ceiling after,
  mutex_pend_inherit_step sg before owner node base waiter ceiling after ->
  sem_pend_sem_handle_frame before after.
Proof.
  intros sg before owner node base waiter ceiling after Hstep watched previous Hlookup Hsem.
  unfold mutex_pend_inherit_step in Hstep; destruct (mutex_pend_inherit_action _ _ _ _ _).
  - subst after; exists previous; auto.
  - subst after; exists previous; auto.
  - destruct Hstep as [events [Hevents ->]].
    unfold mutex_query_lookup in *; cbn [replace_EventS EventState].
    unfold mutex_pend_promoted_events in Hevents.
    destruct (mutex_pend_owner_was_ready before node).
    + subst events; exists previous; auto.
    + destruct node.(eventPtr) as [changed|].
      * destruct Hevents as [event [Hchanged ->]].
        cbn [update_event_field_raw inUsedEventStates].
        lazymatch goal with
        | |- context [if ?test then _ else _] => destruct test eqn:Heq
        end.
        -- apply Z.eqb_eq in Heq; subst watched.
           assert (previous = event) by congruence; subst previous.
           eexists; split; [reflexivity|]. unfold event_set_wait_list; cbn; auto.
        -- exists previous; auto.
      * subst events; exists previous; auto.
Qed.

Lemma sem_pend_mutex_inheritance_timer_frame : forall sg before owner node base waiter ceiling after,
  mutex_pend_inherit_step sg before owner node base waiter ceiling after ->
  after.(TimerState) = before.(TimerState).
Proof.
  intros sg before owner node base waiter ceiling after Hstep.
  unfold mutex_pend_inherit_step in Hstep; destruct (mutex_pend_inherit_action _ _ _ _ _).
  - subst after; reflexivity.
  - subst after; reflexivity.
  - destruct Hstep as [events [_ ->]]; reflexivity.
Qed.

Lemma sem_pend_suspend_step_event_timer_fields : forall sg request priority before result self after,
  task_suspend_step sg request priority before result self after ->
  after.(EventState) = before.(EventState) /\ after.(TimerState) = before.(TimerState).
Proof.
  intros sg request priority before result self after Hstep.
  destruct (TaskSuspendActualC.task_suspend_step_state_cases _ _ _ _ _ _ _ Hstep)
    as [->|[slot [node [Hnode ->]]]]; split; reflexivity.
Qed.

(** The receipt is tied to this physical complete call's own source proof.
    It retains the actual Prepare/wake/commit cuts, including all results. *)
Definition sem_pend_mutex_post_call_receipt environment critical source_env local sg frame call before after
  (segment : PostComponent.mutex_post_critical_c_segment source_env environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical local sg frame call before after) : Prop :=
  sem_pend_mutex_post_receipt sg call.(PostComponent.mutex_post_critical_eid)
    call.(PostComponent.mutex_post_critical_caller) call.(PostComponent.mutex_post_critical_entry)
    call.(PostComponent.mutex_post_critical_result) call.(PostComponent.mutex_post_critical_schedule)
    call.(PostComponent.mutex_post_critical_checkpoint)
    (proj2 (PostComponent.mutex_post_critical_segment_source source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg frame call before after segment)).

(** Unlike a structural field equality, a complete MutexPost may change
    priority and wake a waiter. Each concrete C property must be preserved
    by that actual operation, at the same configuration and call. *)
Definition sem_pend_mutex_post_preserves (sg : StableGlobVars)
  (property : UCOS2_Verify_State -> Prop) : Prop :=
  forall environment critical source_env local frame call before after
    (segment : PostComponent.mutex_post_critical_c_segment source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg frame call before after),
  sem_pend_mutex_post_call_receipt environment critical source_env local sg frame call before after segment ->
  property call.(PostComponent.mutex_post_critical_entry) ->
  property call.(PostComponent.mutex_post_critical_checkpoint).

Definition sem_pend_mutex_inheritance_preserves (sg : StableGlobVars)
  (property : UCOS2_Verify_State -> Prop) : Prop :=
  forall environment critical local frame call before after
    (segment : PendComponent.mutex_pend_inheritance_c_segment environment critical local sg frame call before after),
  property call.(PendComponent.mutex_pend_inheritance_entry) ->
  property call.(PendComponent.mutex_pend_inheritance_returned).

Definition sem_pend_suspend_preserves (sg : StableGlobVars)
  (property : UCOS2_Verify_State -> Prop) : Prop :=
  forall environment critical saved_local caller saved call frame before after
    (completion : TaskSuspendMaskedC.task_suspend_masked_completion
      environment critical saved_local sg caller saved call frame before after),
  property call.(TaskSuspendActualC.suspend_actual_entry) ->
  property call.(TaskSuspendActualC.suspend_actual_checkpoint).

Definition sem_pend_install_preserves (sg : StableGlobVars)
  (property : UCOS2_Verify_State -> Prop) : Prop :=
  forall environment local frame call before after sp Hactual
    (segment : InstallComponent.task_install_c_segment environment local sg frame call before after sp Hactual),
  property call.(InstallComponent.task_install_fields_entry) ->
  property (InstallComponent.task_install_fields_current call).

(** The body cut is not an API return.  Its property closure is for the
    already registered observer, and uses the active facts proved from the
    same completed body and its actual false stop index. *)
Definition sem_pend_delete_body_preserves (sg : StableGlobVars)
  observer event_observer caller_origin (property : UCOS2_Verify_State -> Prop) : Prop :=
  forall capture body_heap restore_selected restore_rely save_selected save_rely
    restore_stopped save_stopped
    (source : sem_pend_delete_call_source event_observer observer caller_origin capture body_heap
      restore_selected restore_rely save_selected save_rely restore_stopped save_stopped),
  capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_globals) = sg ->
  task_delete_capture_observer_stopped capture caller_origin restore_stopped save_stopped = false ->
  task_invocation_active
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState)
    observer caller_origin ->
  task_invocation_active (task_delete_capture_cut capture).(TskState) observer caller_origin ->
  UCOS2_state_inv sg capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired) ->
  property capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired) ->
  property (task_delete_capture_cut capture).

(** A legacy segment retains its original proof and same-index receipts.
    A typed edge retains the real action, registration, step, control and
    receipt; it derives the narrow frames above instead of inventing a
    numeric inequality. Then composes the actual intermediate endpoint. *)
Inductive sem_pend_observed_client_trace external port clients sg observer event_observer :
  TaskInvocationOrigin -> UCOS2_Verify_State -> bool -> TaskInvocationOrigin -> UCOS2_Verify_State -> Prop :=
| SemPendObservedLegacy : forall first before stopped last after
    (trace : kernel_client_task_source_trace external port clients sg observer event_observer
      first before stopped last after),
    sem_pend_client_source_calls external port clients sg observer event_observer
      first before stopped last after trace ->
    sem_pend_observed_client_trace external port clients sg observer event_observer
      first before stopped last after
| SemPendObservedCritical : forall action first before last after,
    clients action -> sem_pend_framed_critical_client action ->
    (forall invocation, event_observer = Some invocation -> kernel_client_event_actor action <> Some invocation) ->
    kernel_client_step action sg before after ->
    task_execution_source_step external port sg first before last after ->
    tmr_task_source_call_receipt external action sg before after ->
    sem_pend_observed_client_trace external port clients sg observer event_observer
      first before (kernel_client_stops action observer) last after
| SemPendObservedIRQ : forall environment critical first before before_heap input last after after_heap output,
    environment.(task_stack_call_external) = external ->
    environment.(task_stack_call_port) = port ->
    critical.(critical_region_clients) = clients ->
    sem_pend_irq_completion_source environment critical sg
      first before before_heap input last after after_heap output ->
    sem_pend_observed_client_trace external port clients sg observer event_observer
      first before false last after
| SemPendObservedIRQEntry : forall environment first initial node handler suspended publication local frame
    before_heap saved_heap body_heap,
    environment.(task_stack_call_external) = external ->
    environment.(task_stack_call_port) = port ->
    OSIntExitCCallEnvelope.os_int_exit_first_level_entry_c_completion environment sg
      initial node handler suspended publication local frame before_heap saved_heap body_heap ->
    sem_pend_observed_client_trace external port clients sg observer event_observer
      first initial false first (sem_pend_irq_entry_state initial handler suspended)
| SemPendObservedMutexPost : forall environment critical source_env local frame call before_heap after_heap origin
    (segment : PostComponent.mutex_post_critical_c_segment source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg frame call before_heap after_heap),
    environment.(task_stack_call_external) = external ->
    environment.(task_stack_call_port) = port ->
    critical.(critical_region_clients) = clients ->
    sem_pend_mutex_post_call_receipt environment critical source_env local sg frame call before_heap after_heap segment ->
    sem_pend_observed_client_trace external port clients sg observer event_observer
      origin call.(PostComponent.mutex_post_critical_entry) false origin call.(PostComponent.mutex_post_critical_checkpoint)
| SemPendObservedMutexInheritance : forall environment critical local frame call before_heap after_heap origin
    (segment : PendComponent.mutex_pend_inheritance_c_segment environment critical local sg frame call before_heap after_heap),
    environment.(task_stack_call_external) = external ->
    environment.(task_stack_call_port) = port ->
    critical.(critical_region_clients) = clients ->
    sem_pend_observed_client_trace external port clients sg observer event_observer
      origin call.(PendComponent.mutex_pend_inheritance_entry) false origin call.(PendComponent.mutex_pend_inheritance_returned)
| SemPendObservedSuspend : forall environment critical saved_local caller saved call frame before_heap after_heap origin
    (completion : TaskSuspendMaskedC.task_suspend_masked_completion
      environment critical saved_local sg caller saved call frame before_heap after_heap),
    environment.(task_stack_call_external) = external ->
    environment.(task_stack_call_port) = port ->
    critical.(critical_region_clients) = clients ->
    sem_pend_observed_client_trace external port clients sg observer event_observer
      origin call.(TaskSuspendActualC.suspend_actual_entry) false
      origin call.(TaskSuspendActualC.suspend_actual_checkpoint)
| SemPendObservedInstall : forall environment local frame call before_heap after_heap sp Hactual
    (segment : InstallComponent.task_install_c_segment environment local sg frame call before_heap after_heap sp Hactual),
    environment.(task_stack_call_external) = external ->
    environment.(task_stack_call_port) = port ->
    sem_pend_observed_client_trace external port clients sg observer event_observer
      call.(InstallComponent.task_install_fields_context).(os_sched_call_origin)
      call.(InstallComponent.task_install_fields_entry) false
      (RunningInvocation call.(InstallComponent.task_install_fields_incoming).(stackLeaseSlot)
        call.(InstallComponent.task_install_fields_incoming).(stackLeaseGeneration))
      (InstallComponent.task_install_fields_current call)
| SemPendObservedDeleteBody : forall stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
    (source : sem_pend_delete_call_source event_observer observer stored_origin capture body_heap
      restore_selected restore_rely save_selected save_rely restore_stopped save_stopped),
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_environment).(task_stack_call_external) = external ->
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_environment).(task_stack_call_port) = port ->
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_critical).(critical_region_clients) = clients ->
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_globals) = sg ->
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState).(taskLifecycle).(taskInvocations)
      observer = Some stored_origin ->
    sem_pend_observed_client_trace external port clients sg observer event_observer
      capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_first).(os_sched_call_origin)
      capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired)
      (task_delete_capture_observer_stopped capture stored_origin restore_stopped save_stopped)
      capture.(delete_save_returned).(os_sched_call_origin) (task_delete_capture_cut capture)
| SemPendObservedThen : forall first before stopped1 middle transient stopped2 last after,
    sem_pend_observed_client_trace external port clients sg observer event_observer
      first before stopped1 middle transient ->
    sem_pend_observed_client_trace external port clients sg observer event_observer
      middle transient stopped2 last after ->
    sem_pend_observed_client_trace external port clients sg observer event_observer
      first before (orb stopped1 stopped2) last after.

Lemma sem_pend_observed_client_trace_refl : forall external port clients sg observer event_observer origin state,
  sem_pend_observed_client_trace external port clients sg observer event_observer origin state false origin state.
Proof.
  intros; eapply SemPendObservedLegacy with (trace := KernelClientTaskSourceNil _ _ _ _ _ _ _ _); constructor.
Qed.

Lemma sem_pend_observed_client_trace_preserves_current : forall external port clients sg observer event_observer
  first before stopped last after,
  sem_pend_observed_client_trace external port clients sg observer event_observer first before stopped last after ->
  task_execution_current first before -> task_execution_current last after.
Proof.
  intros * Htrace; induction Htrace; intro Hcurrent.
  - eapply task_execution_source_trace_preserves_current;
      [exact (proj2 (kernel_client_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ trace))|exact Hcurrent].
  - eapply task_execution_source_step_preserves_current; eassumption.
  - eapply sem_pend_irq_completion_source_preserves_current; eassumption.
  - eapply sem_pend_irq_entry_preserves_current; eassumption.
  - pose proof (proj2 (PostComponent.mutex_post_critical_segment_source _ _ _ _ _ _ _ _ _ _ segment)) as Hcritical.
    destruct (mutex_post_critical_call_fields_eq _ _ _ _ _ _ _ Hcritical)
      as [Hnodes [Hparked [Hlife [Hcurrent_id Hprivate]]]].
    unfold task_execution_current in *; destruct origin; [exact I|].
    rewrite Hcurrent_id; exact Hcurrent.
  - pose proof (proj2 (proj2 (PendComponent.mutex_pend_inheritance_segment_source _ _ _ _ _ _ _ _ segment))) as Hstep.
    pose proof (proj1 (mutex_pend_inherit_preserves_scheduler_caches _ _ _ _ _ _ _ _ Hstep)) as Hcurrent_id.
    unfold task_execution_current in *; destruct origin; [exact I|].
    rewrite Hcurrent_id; exact Hcurrent.
  - destruct completion as [[Hread Hstep] Hinput Houtput].
    destruct (TaskSuspendActualC.task_suspend_step_state_cases _ _ _ _ _ _ _ Hstep)
      as [->|[slot [node [Hnode ->]]]]; exact Hcurrent.
  - destruct segment as [Hsource Hcompletion].
    destruct Hsource as [Hsaved [Hdestination [Hhigh Hstate]]].
    exact (proj1 Hdestination).
  - eapply sem_pend_delete_capture_body_current; eassumption.
  - apply IHHtrace2, IHHtrace1; exact Hcurrent.
Qed.

Lemma sem_pend_observed_client_trace_resources : forall external port clients sg observer event_observer
  first before stopped last after,
  (forall action, clients action -> KernelClientCertificate action) ->
  sem_pend_observed_client_trace external port clients sg observer event_observer first before stopped last after ->
  UCOS2_state_inv sg before ->
  UCOS2_state_inv sg after /\ task_creation_frame observer before.(TskState) after.(TskState) /\
  (forall invocation, event_observer = Some invocation ->
    event_creation_frame invocation before.(EventState) after.(EventState)) /\
  (stopped = false -> forall origin,
    task_invocation_active before.(TskState) observer origin ->
    task_invocation_active after.(TskState) observer origin).
Proof.
  intros external port clients sg observer event_observer first before stopped last after Hcert Htrace.
  induction Htrace as [first before stopped last after trace Hcalls
    |action first before last after Hmember Htyped Hevent Hstep Hcontrol Hreceipt
    |environment irq_critical first before before_heap input last after after_heap output Hexternal Hport Hclients Hcompletion
    |entry_environment first initial node handler suspended publication local frame before_heap saved_heap body_heap Hexternal Hport Hentry
    |post_environment post_critical source_env local frame call before_heap after_heap origin segment Hexternal Hport Hclients Hreceipt
    |pend_environment pend_critical local frame call before_heap after_heap origin segment Hexternal Hport Hclients
    |suspend_environment suspend_critical saved_local caller saved call frame before_heap after_heap origin completion Hexternal Hport Hclients
    |install_environment local frame call before_heap after_heap sp Hactual segment Hexternal Hport
    |stored_origin capture body_heap restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
      source Hexternal Hport Hclients Hsg Hregistered
    |first before stopped1 middle transient stopped2 last after Hfirst IHfirst Hlast IHlast]; intro Hvalid.
  - eapply kernel_client_resource_trace_transports_resources; [exact Hcert| |exact Hvalid].
    exact (proj1 (kernel_client_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ trace)).
  - pose proof (Hcert action Hmember) as Hcertificate.
    split; [eapply kernel_client_preserves_validity; eassumption|].
    split; [exact (proj1 (sem_pend_framed_critical_observer_frame _ _ _ _ _ Htyped Hstep))|].
    split.
    + intros invocation Hobserver; eapply kernel_client_frames_event_creation; eauto.
    + intros Hstop origin Hactive; eapply kernel_client_preserves_continuation; eassumption.
  - pose proof (sem_pend_irq_completion_source_frame _ _ _ _ _ _ _ _ _ _ _ Hcompletion) as Hframe.
    destruct (sem_pend_irq_structural_frame_resources _ _ Hframe) as [Htask [Hevent Hactive]].
    split; [eapply sem_pend_irq_completion_source_preserves_validity; eassumption|].
    split; [apply Htask|]. split; [intros; apply Hevent|intros _; exact (Hactive observer)].
  - destruct (sem_pend_irq_entry_frames _ _ _ _ _ _ _ _ _ _ _ _ Hentry)
      as [Hlife [Hevents [Hnames [Htimers Hsched]]]].
    split; [eapply sem_pend_irq_entry_preserves_validity; exact Hentry|].
    split.
    + unfold task_creation_frame, task_creation_view; rewrite Hlife; reflexivity.
    + split.
      * intros invocation Hobserver; unfold event_creation_frame; rewrite Hevents; reflexivity.
      * intros Hstop origin Hactive; eapply sem_pend_irq_entry_preserves_active; eassumption.
  - pose proof (PostComponent.mutex_post_critical_segment_source _ _ _ _ _ _ _ _ _ _ segment) as Hsource.
    destruct (mutex_post_critical_c_source_creation_frames _ _ observer Hsource)
      as [Htask [Hevent Hrest]].
    split.
    + eapply SelectedMutexIdle.mutex_post_critical_c_owner_valid.
      exact (PostComponent.mutex_post_critical_segment_output _ _ _ _ _ _ _ _ _ _ segment).
    + split; [exact Htask|]. split; [intros; apply Hevent|].
      intros _ active_origin Hactive.
      eapply PostComponent.mutex_post_critical_preserves_observer_active; [exact (proj2 Hsource)|exact Hactive].
  - pose proof (PendComponent.mutex_pend_inheritance_segment_source _ _ _ _ _ _ _ _ segment) as Hsource.
    destruct (mutex_pend_inheritance_c_source_creation_frames _ _ observer Hsource)
      as [Htask [Hevent Hrest]].
    split.
    + eapply SelectedMutexIdle.mutex_pend_inheritance_c_owner_valid.
      exact (PendComponent.mutex_pend_inheritance_segment_output _ _ _ _ _ _ _ _ segment).
    + split; [exact Htask|]. split; [intros; apply Hevent|].
      intros _ active_origin Hactive.
      eapply PendComponent.mutex_pend_inherit_preserves_observer_active;
        [exact (proj1 Hsource)|exact (proj2 (proj2 Hsource))|exact Hactive].
  - destruct completion as [[Hread Hstep] Hinput Houtput].
    destruct (TaskSuspendActualC.task_suspend_step_creation_frames _ _ _ _ _ _ _ observer observer Hstep)
      as [Htask Hrest].
    pose proof (proj1 (sem_pend_suspend_step_event_timer_fields _ _ _ _ _ _ _ Hstep)) as Hevents.
    split; [eapply TaskSuspendMaskedC.task_suspend_masked_owner_valid; exact Houtput|].
    split; [exact Htask|]. split.
    + intros invocation Hobserver; unfold event_creation_frame; rewrite Hevents; reflexivity.
    + intros _ active_origin Hactive.
      destruct (TaskSuspendActualC.task_suspend_step_state_cases _ _ _ _ _ _ _ Hstep)
        as [->|[slot [node [Hnode ->]]]]; [exact Hactive|].
      eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hnode|reflexivity|exact Hactive].
  - destruct segment as [Hsource Hcompletion].
    destruct (os_sched_install_client_state_frame _ _ _ _ _ sg _ _ Hsource)
      as [Hnodes [Hlife [Hevents Hrest]]].
    split.
    + eapply kernel_client_preserves_validity;
        [apply os_sched_install_client_certificate|exact Hvalid|exact Hsource].
    + split.
      * unfold task_creation_frame, task_creation_view; rewrite Hlife; reflexivity.
      * split.
        -- intros invocation Hobserver; unfold event_creation_frame; rewrite Hevents; reflexivity.
        -- intros _ active_origin Hactive.
           eapply kernel_client_preserves_continuation;
             [apply os_sched_install_client_certificate|exact Hvalid|exact Hsource|reflexivity|exact Hactive].
  - destruct (sem_pend_delete_call_frames event_observer _ _ _ _ _ _ _ _ _ _ source)
      as [Htask [Hevent Hrest]].
    split.
    + rewrite <- Hsg; eapply sem_pend_delete_capture_body_valid; exact source.
    + split; [exact Htask|]. split; [exact Hevent|].
      intros Hstop active_origin Hactive.
      assert (Horigin : active_origin = stored_origin).
      { pose proof (proj1 Hactive) as Hpast; congruence. }
      subst active_origin.
      eapply sem_pend_delete_capture_body_preserves_active; eassumption.
  - destruct (IHfirst Hvalid) as [Hmiddle [Hframe1 [Hevent1 Hactive1]]].
    destruct (IHlast Hmiddle) as [Hafter [Hframe2 [Hevent2 Hactive2]]].
    split; [exact Hafter|]. split.
    + unfold task_creation_frame in *; congruence.
    + split.
      * intros invocation Hobserver; specialize (Hevent1 invocation Hobserver);
          specialize (Hevent2 invocation Hobserver); unfold event_creation_frame in *; congruence.
      * intro Hstop; apply orb_false_iff in Hstop; destruct Hstop as [Hstop1 Hstop2].
        intros origin Hactive; exact (Hactive2 Hstop2 origin (Hactive1 Hstop1 origin Hactive)).
Qed.

(** Only the fixed observer's priority cache is carried through intermediate
    calls. Global current consistency is recovered at the actual caller's
    return; it is not required at an unrelated task's retirement cut. *)
Lemma sem_pend_observed_client_trace_preserves_observer_cache :
  forall external port clients sg observer event_observer first before stopped last after,
  (forall action, clients action -> KernelClientCertificate action) ->
  sem_pend_observed_client_trace external port clients sg observer event_observer
    first before stopped last after ->
  stopped = false -> forall caller_origin,
  task_invocation_active before.(TskState) observer caller_origin ->
  UCOS2_state_inv sg before ->
  sched_observer_current_cache caller_origin before ->
  sched_observer_current_cache caller_origin after.
Proof.
  intros external port clients sg observer event_observer first before stopped last after Hcert Htrace.
  assert (Hpost_cache : forall eid initial result final origin,
    sem_post_critical sg eid initial result final ->
    sched_observer_current_cache origin initial -> sched_observer_current_cache origin final).
  { intros eid initial result final origin [event [Hevent Hsource]] Hcache.
    lazymatch type of Hsource with
    | context [if ?test then _ else _] => destruct test in Hsource
    end.
    - destruct Hsource as [fields [_ Hsource]].
      lazymatch type of Hsource with
      | context [if ?test then _ else _] => destruct test in Hsource
      end; destruct Hsource as [_ ->]; exact Hcache.
    - destruct Hsource as [_ [priority Hsource]].
      eapply CriticalComponent.mutex_del_wake_preserves_observer_cache; eassumption. }
  assert (Habort_cache : forall eid option initial result final origin,
    event_pend_abort_critical sg eid PendSem option initial result final ->
    sched_observer_current_cache origin initial -> sched_observer_current_cache origin final).
  { intros eid option initial result final origin [event [Hevent Hsource]] Hcache.
    lazymatch type of Hsource with
    | context [if ?test then _ else _] => destruct test in Hsource
    end.
    - destruct Hsource as [_ ->]; exact Hcache.
    - lazymatch type of Hsource with
      | context [if ?test then _ else _] => destruct test in Hsource
      end.
      + destruct Hsource as [priorities [Hsource _]].
        eapply CriticalComponent.mutex_del_broadcast_preserves_observer_cache; eassumption.
      + destruct Hsource as [priority [Hsource _]].
        eapply CriticalComponent.mutex_del_wake_preserves_observer_cache; eassumption. }
  assert (Hscan_cache : forall visited initial origin,
    sched_observer_current_cache origin initial ->
    sched_observer_current_cache origin (time_tick_scan sg initial visited)).
  { induction visited as [|slot rest IH]; intros initial origin Hcache; [exact Hcache|].
    change (sched_observer_current_cache origin
      (time_tick_scan sg (time_tick_visit sg initial slot) rest)).
    apply IH; unfold time_tick_visit.
    destruct (initial.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|exact Hcache].
    eapply WakeComponent.kernel_wake_c_source_preserves_observer_cache;
      [apply WakeComponent.KernelWakeCTickSource; exact Hold|exact Hcache]. }
  assert (Hleaf : forall action initial final origin,
    tmr_task_source_call_receipt external action sg initial final ->
    UCOS2_state_inv sg initial -> task_invocation_active initial.(TskState) observer origin ->
    sched_observer_current_cache origin initial -> sched_observer_current_cache origin final).
  { intros action initial final origin Hcall Hvalid Hactive Hcache.
    pose proof (tmr_task_source_client_preserves_current_consistency external action sg initial final
      Hvalid (tmr_task_source_call_receipt_source _ _ _ _ _ Hcall)
      (tmr_task_source_call_receipt_step _ _ _ _ _ Hcall)) as Hwriter.
    destruct Hcall as [action sg initial final Hnontimer Hstep|cut sg initial final Hstep|
      actor requested priority sg initial final Hstep|actor pointer bits result sg initial final Hstep|
      actor event kind message result sg initial final Hinput Hstep|slot previous sg initial final Hstep|
      context outgoing incoming resumed sg initial final Hstep|action sg initial final Hsem Hstep|
      action sg initial final Hcritical Hstep|actor cut sg initial final Hstep|
      actor cut sg initial final Hstep|actor source_sg cut entry timers sg initial final Hstep|
      actor event option result sg initial final Hstep|
      actor source_sg priority result entry returned sg initial final Hstep].
    - eapply sched_current_frame_preserves_observer_cache;
        [exact Hactive| |exact Hwriter|exact Hcache].
      destruct Hnontimer.
      + symmetry; eapply task_creation_client_current_pointer_eq; exact Hstep.
      + destruct Hstep as [Hsource ->]. symmetry; apply task_create_stack_publication_current_pointer_eq.
      + destruct Hstep as [_ ->]; reflexivity.
      + destruct Hstep as [_ ->]; reflexivity.
      + destruct Hstep as [_ ->]; reflexivity.
      + destruct Hstep as [_ [result Hstep]].
        unfold event_create_allocate_critical in Hstep.
        destruct initial.(EventState).(unUsedEventStates).
        * destruct Hstep as [_ ->]; reflexivity.
        * destruct Hstep as [image [_ [_ ->]]]; reflexivity.
      + destruct Hstep as [_ ->]; reflexivity.
      + destruct Hstep as [_ [_ ->]]; reflexivity.
      + destruct Hstep as [_ [_ [_ [_ [result Hstep]]]]].
        destruct Hstep as [allocation' [_ Hstep]].
        destruct free; destruct Hstep as [_ ->]; reflexivity.
      + destruct Hstep as [_ [_ [_ [_ ->]]]]; reflexivity.
      + destruct Hstep as [_ [result Hsource]].
        eapply StatusComponent.kernel_status_c_source_current_eq.
        eapply StatusComponent.KernelStatusCResumeSource; exact Hsource.
      + eapply StatusComponent.kernel_status_c_source_current_eq.
        eapply StatusComponent.KernelStatusCSemAcceptSource.
        destruct Hstep as [event [_ [_ Hsource]]]; exact Hsource.
    - eapply sched_current_frame_preserves_observer_cache;
        [exact Hactive| |exact Hwriter|exact Hcache].
      destruct Hstep as [_ ->]; destruct cut; reflexivity.
    - destruct Hstep as [error Hsource].
      eapply CriticalComponent.task_change_prio_critical_preserves_observer_cache; eassumption.
    - destruct Hstep as [schedule Hsource].
      eapply WakeComponent.kernel_wake_c_source_preserves_observer_cache;
        [eapply WakeComponent.KernelWakeCFlagSource; exact Hsource|exact Hcache].
    - destruct Hstep as [priority Hsource].
      eapply CriticalComponent.mutex_del_wake_preserves_observer_cache; eassumption.
    - destruct Hstep as [Hprevious ->].
      eapply WakeComponent.kernel_wake_c_source_preserves_observer_cache;
        [apply WakeComponent.KernelWakeCTickSource; exact Hprevious|exact Hcache].
    - exact (proj2 (InstallComponent.os_sched_install_client_preserves_observer_cache
        external context outgoing incoming resumed sg initial final observer origin Hstep Hactive)).
    - destruct Hsem.
      + destruct Hstep as [old [Hold ->]].
        eapply WakeComponent.kernel_wake_c_source_preserves_observer_cache;
          [apply WakeComponent.KernelWakeCTickSource; exact Hold|exact Hcache].
      + destruct Hstep as [result Hsource]; eapply Hpost_cache; eassumption.
      + destruct Hstep as [result Hsource]; eapply Habort_cache; eassumption.
      + eapply sched_current_frame_preserves_observer_cache;
          [exact Hactive| |exact Hwriter|exact Hcache].
        change (final = os_sched_save_current_sp initial selected sp) in Hstep; subst final.
        exact (f_equal curTaskID (os_sched_save_current_sp_scheduler_frame initial selected sp)).
      + eapply sched_current_frame_preserves_observer_cache;
          [exact Hactive| |exact Hwriter|exact Hcache].
        destruct Hstep as [_ [result [_ Hsource]]].
        destruct (initial.(TskState).(prioTbl) priority) as [| |selected].
        * destruct Hsource as [_ ->]; reflexivity.
        * destruct Hsource as [_ ->]; reflexivity.
        * destruct Hsource as [old [Hold Hsource]].
          lazymatch type of Hsource with
          | context [if ?test then _ else _] => destruct test in Hsource
          end; destruct Hsource as [_ ->]; [reflexivity|].
          exact (proj1 (sched_wake_by_status_current_cache_frame sg initial.(TskState) initial.(SchedState)
            selected (encode_task_status (sem_pend_delay_resume_task old).(stat)))).
    - destruct Hcritical.
      + destruct Hstep as [_ [result [code [request [error [scheduled [Hsource Hencoding]]]]]]].
        eapply CriticalComponent.mutex_del_critical_preserves_observer_cache; eassumption.
      + destruct Hstep as [result [code [request Hsource]]].
        destruct Hsource as [result code request checkpoint Hguard [error [scheduled [Hsource Hencoding]]]
          |kind Htype Hnotmutex]; [|exact Hcache].
        eapply CriticalComponent.mutex_del_critical_preserves_observer_cache; eassumption.
      + destruct Hstep as [_ [error Hsource]].
        eapply CriticalComponent.task_change_prio_critical_preserves_observer_cache; eassumption.
    - destruct cut; cbn [kernel_client_step tmr_task_tick_source_client tmr_task_tick_cut_source] in Hstep.
      + subst final; unfold time_tick_clock_step_state; destruct (tick_step_advance _ _); exact Hcache.
      + subst final; unfold time_tick_serialized_after_hook; destruct (time_tick_process_tasks initial).
        * apply Hscan_cache; unfold time_tick_clock_step_state; destruct (tick_step_advance _ _); exact Hcache.
        * unfold time_tick_clock_step_state; destruct (tick_step_advance _ _); exact Hcache.
      + destruct Hstep; try exact Hcache; eapply Hpost_cache; eassumption.
    - destruct Hstep as [timers [_ ->]]; exact Hcache.
    - destruct Hstep as [_ [_ [_ ->]]]; exact Hcache.
    - destruct Hstep as [node [_ [_ Hsource]]]; eapply Habort_cache; eassumption.
    - destruct Hstep as [_ [_ [_ [_ Hsource]]]].
      destruct (task_suspend_idle_guard_original_or_unchanged _ _ _ _ _ Hsource) as [->|Horiginal];
        [exact Hcache|].
      eapply StatusComponent.kernel_status_c_source_preserves_observer_cache;
        [eapply StatusComponent.KernelStatusCSuspendSource; exact Horiginal|exact Hactive|exact Hcache]. }
  assert (Hlegacy : forall first initial stopped last final
    (trace : kernel_client_task_source_trace external port clients sg observer event_observer
      first initial stopped last final),
    sem_pend_client_source_calls external port clients sg observer event_observer
      first initial stopped last final trace -> stopped = false -> forall origin,
    task_invocation_active initial.(TskState) observer origin -> UCOS2_state_inv sg initial ->
    sched_observer_current_cache origin initial -> sched_observer_current_cache origin final).
  { clear Htrace first before stopped last after.
    intros first initial stopped0 last final trace Hcalls.
    induction Hcalls as [origin state|action first initial middle transient last final stopped0
      Hin Hforeign Hevent Hstep Hsource Htail Hreceipt Hcalls IH];
      intros Hstop origin0 Hactive Hvalid Hcache; [exact Hcache|].
    apply orb_false_iff in Hstop; destruct Hstop as [Hstop_step Hstop_tail].
    apply (IH Hstop_tail origin0).
    - eapply kernel_client_preserves_continuation;
        [apply Hcert; exact Hin|exact Hvalid|exact Hstep|exact Hstop_step|exact Hactive].
    - eapply kernel_client_preserves_validity; [apply Hcert; exact Hin|exact Hvalid|exact Hstep].
    - eapply Hleaf; eassumption. }
  induction Htrace as [first initial stopped0 last final trace Hcalls
    |action first initial last final Hmember Htyped Hevent Hstep Hcontrol Hreceipt
    |environment irq_critical first initial before_heap input last final after_heap output Hexternal Hport Hclients Hcompletion
    |entry_environment first initial node handler suspended publication local frame before_heap saved_heap body_heap Hexternal Hport Hentry
    |post_environment post_critical source_env local frame call before_heap after_heap origin segment Hexternal Hport Hclients Hreceipt
    |pend_environment pend_critical local frame call before_heap after_heap origin segment Hexternal Hport Hclients
    |suspend_environment suspend_critical saved_local caller saved call frame before_heap after_heap origin completion Hexternal Hport Hclients
    |install_environment local frame call before_heap after_heap sp Hactual segment Hexternal Hport
    |stored_origin capture body_heap restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
      source Hexternal Hport Hclients Hsg Hregistered
    |first initial stopped1 middle transient stopped2 last final Hfirst IHfirst Hlast IHlast];
    intros Hstop caller_origin Hactive Hvalid Hcache.
  - eapply Hlegacy; eassumption.
  - eapply Hleaf; eassumption.
  - destruct (sem_pend_irq_completion_source_frame _ _ _ _ _ _ _ _ _ _ _ Hcompletion)
      as [Htasks Hlife Hevents Hnames Htimers Hrunning Hcurrent Hpriority].
    destruct caller_origin; [exact I|].
    unfold sched_observer_current_cache in *; rewrite Htasks, Hcurrent, Hpriority; exact Hcache.
  - destruct (sem_pend_irq_entry_frames _ _ _ _ _ _ _ _ _ _ _ _ Hentry)
      as [_ [_ [_ [_ Hsched]]]].
    eapply sched_current_frame_preserves_observer_cache; [exact Hactive|rewrite Hsched; reflexivity| |exact Hcache].
    intro Hcurrent; unfold sched_current_consistency in *; rewrite Hsched.
    destruct initial.(SchedState).(curTaskID) as [slot|] eqn:Hslot; [|exact Hcurrent].
    destruct Hcurrent as [old [Hold Hpriority]].
    destruct (sem_pend_irq_entry_task_at _ _ _ _ _ _ _ _ _ _ _ _ Hentry slot old Hold)
      as [current [Hnode Hfields]].
    pose proof (f_equal curPrio Hfields) as Hprio; change (current.(curPrio) = old.(curPrio)) in Hprio.
    exists current; split; [exact Hnode|rewrite Hprio; exact Hpriority].
  - exact (proj2 (PostComponent.mutex_post_critical_c_segment_preserves_observer
      _ _ _ _ _ _ _ _ _ _ observer caller_origin segment (conj Hactive Hcache))).
  - exact (proj2 (PendComponent.mutex_pend_inheritance_c_segment_preserves_observer
      _ _ _ _ _ _ _ _ observer caller_origin segment (conj Hactive Hcache))).
  - destruct completion as [[Hread Hstep] Hinput Houtput].
    exact (proj2 (TaskSuspendActualC.task_suspend_step_preserves_observer
      _ _ _ _ _ _ _ observer caller_origin Hstep (conj Hactive Hcache))).
  - exact (proj2 (InstallComponent.task_install_c_segment_preserves_observer
      _ _ _ _ observer caller_origin _ _ _ _ _ segment Hactive)).
  - assert (Horigin : caller_origin = stored_origin).
    { pose proof (proj1 Hactive) as Hpast; congruence. }
    subst caller_origin.
    exact (proj2 (sem_pend_delete_call_preserves_observer event_observer _ _ _ _ _ _ _ _ _ _
      source Hstop (conj Hactive Hcache))).
  - apply orb_false_iff in Hstop; destruct Hstop as [Hstop1 Hstop2].
    destruct (sem_pend_observed_client_trace_resources _ _ _ _ _ _ _ _ _ _ _ Hcert Hfirst Hvalid)
      as [Hmiddle [_ [_ Hactive_middle]]].
    apply (IHlast Hstop2 caller_origin (Hactive_middle Hstop1 caller_origin Hactive) Hmiddle).
    apply (IHfirst Hstop1 caller_origin Hactive Hvalid Hcache).
Qed.

Lemma sem_pend_observed_client_trace_preserves : forall external port clients sg observer event_observer
  (property : UCOS2_Verify_State -> Prop) caller_origin,
  (forall action, clients action -> KernelClientCertificate action) ->
  (forall action initial final, clients action -> UCOS2_state_inv sg initial ->
    kernel_client_step action sg initial final ->
    tmr_task_source_call_receipt external action sg initial final ->
    property initial -> property final) ->
  sem_pend_irq_cut_preserves property ->
  sem_pend_irq_entry_preserves property ->
  sem_pend_mutex_post_preserves sg property ->
  sem_pend_mutex_inheritance_preserves sg property ->
  sem_pend_suspend_preserves sg property ->
  sem_pend_install_preserves sg property ->
  sem_pend_delete_body_preserves sg observer event_observer caller_origin property ->
  forall first before stopped last after,
  sem_pend_observed_client_trace external port clients sg observer event_observer first before stopped last after ->
  stopped = false ->
  task_invocation_active before.(TskState) observer caller_origin ->
  UCOS2_state_inv sg before -> property before -> property after.
Proof.
  intros external port clients sg observer event_observer property caller_origin Hcert Hproperty Hirq Hentry_property
    Hpost_property Hinherit_property Hsuspend_property Hinstall_property Hdelete_property.
  assert (Hlegacy : forall first before stopped last after
    (trace : kernel_client_task_source_trace external port clients sg observer event_observer
      first before stopped last after),
    sem_pend_client_source_calls external port clients sg observer event_observer
      first before stopped last after trace -> UCOS2_state_inv sg before -> property before -> property after).
  { intros first before stopped last after trace Hcalls; induction Hcalls;
      intros Hvalid Hbefore; [exact Hbefore|].
    apply IHHcalls.
    - eapply kernel_client_preserves_validity; [apply Hcert; eassumption|exact Hvalid|eassumption].
    - eapply Hproperty; eassumption. }
  intros first before stopped last after Htrace; induction Htrace;
    intros Hstop Hactive Hvalid Hbefore.
  - eapply Hlegacy; eassumption.
  - eapply Hproperty; eassumption.
  - eapply Hirq; [eapply sem_pend_irq_completion_source_frame; eassumption|exact Hbefore].
  - eapply Hentry_property; eassumption.
  - eapply Hpost_property; eassumption.
  - eapply Hinherit_property; eassumption.
  - eapply Hsuspend_property; eassumption.
  - eapply Hinstall_property; eassumption.
  - assert (Horigin : caller_origin = stored_origin).
    { pose proof (proj1 Hactive) as Hregistered; congruence. }
    subst stored_origin.
    eapply Hdelete_property; [exact source|eassumption|exact Hstop|exact Hactive| |exact Hvalid|exact Hbefore].
    eapply sem_pend_delete_capture_body_preserves_active; eassumption.
  - apply orb_false_iff in Hstop; destruct Hstop as [Hstop1 Hstop2].
    destruct (sem_pend_observed_client_trace_resources _ _ _ _ _ _ _ _ _ _ _ Hcert Htrace1 Hvalid)
      as [Hmiddle [Htask [Hevent Hactive_middle]]].
    apply IHHtrace2; [exact Hstop2|exact (Hactive_middle Hstop1 caller_origin Hactive)|exact Hmiddle|].
    apply IHHtrace1; assumption.
Qed.

Lemma sem_pend_observed_client_trace_sem_handle : forall external port critical sg observer event_observer
  first before stopped last after eid previous,
  sem_pend_observed_client_trace external port critical.(critical_region_clients) sg observer event_observer
    first before stopped last after ->
  mutex_query_handle_protocol critical sg observer eid -> UCOS2_state_inv sg before ->
  mutex_query_lookup before eid previous -> previous.(eventType) = OS_EVENT_TYPE_SEM ->
  exists current, mutex_query_lookup after eid current /\
    current.(eventGeneration) = previous.(eventGeneration) /\ current.(eventType) = previous.(eventType).
Proof.
  intros external port critical sg observer event_observer first before stopped last after eid previous Htrace Hprotocol.
  revert previous; induction Htrace as [first before stopped last after trace Hcalls
    |action first before last after Hmember Htyped Hevent Hstep Hcontrol Hreceipt
    |environment irq_critical first before before_heap input last after after_heap output Hexternal Hport Hclients Hcompletion
    |entry_environment first initial node handler suspended publication local frame before_heap saved_heap body_heap Hexternal Hport Hentry
    |post_environment post_critical source_env local frame call before_heap after_heap origin segment Hexternal Hport Hclients Hreceipt
    |pend_environment pend_critical local frame call before_heap after_heap origin segment Hexternal Hport Hclients
    |suspend_environment suspend_critical saved_local caller saved call frame before_heap after_heap origin completion Hexternal Hport Hclients
    |install_environment local frame call before_heap after_heap sp Hactual segment Hexternal Hport
    |stored_origin capture body_heap restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
      source Hexternal Hport Hclients Hsg Hregistered
    |first before stopped1 middle transient stopped2 last after Hfirst IHfirst Hlast IHlast];
    intros previous Hvalid Hlookup Hsem.
  - revert previous Hvalid Hlookup Hsem; induction Hcalls;
      intros previous Hvalid Hlookup Hsem; [exists previous; auto|].
    destruct (Hprotocol action before transient previous member foreign Hvalid step Hlookup)
      as [current [Hcurrent [Hgeneration Htype]]].
    assert (Hvalid' : UCOS2_state_inv sg transient).
    { eapply kernel_client_preserves_validity;
        [exact (critical.(critical_region_client_certificates) action member)|exact Hvalid|exact step]. }
    destruct (IHHcalls current Hvalid' Hcurrent ltac:(congruence)) as [final [Hfinal [Hg Ht]]].
    exists final; split; [exact Hfinal|]; split; congruence.
  - exact (proj2 (sem_pend_framed_critical_observer_frame _ _ _ _ observer Htyped Hstep)
      eid previous Hlookup Hsem).
  - pose proof (sem_pend_irq_cut_events _ _
      (sem_pend_irq_completion_source_frame _ _ _ _ _ _ _ _ _ _ _ Hcompletion)) as Hevents.
    exists previous; split; [unfold mutex_query_lookup in *; rewrite Hevents; exact Hlookup|auto].
  - destruct (sem_pend_irq_entry_frames _ _ _ _ _ _ _ _ _ _ _ _ Hentry)
      as [Hlife [Hevents [Hnames [Htimers Hsched]]]].
    exists previous; split; [unfold mutex_query_lookup in *; rewrite Hevents; exact Hlookup|auto].
  - eapply sem_pend_mutex_post_sem_handle_frame; [|exact Hlookup|exact Hsem].
    exact (proj2 (PostComponent.mutex_post_critical_segment_source _ _ _ _ _ _ _ _ _ _ segment)).
  - eapply sem_pend_mutex_inheritance_sem_handle_frame; [|exact Hlookup|exact Hsem].
    exact (proj2 (proj2 (PendComponent.mutex_pend_inheritance_segment_source _ _ _ _ _ _ _ _ segment))).
  - destruct completion as [[Hread Hstep] Hinput Houtput].
    pose proof (proj1 (sem_pend_suspend_step_event_timer_fields _ _ _ _ _ _ _ Hstep)) as Hevents.
    exists previous; split; [unfold mutex_query_lookup in *; rewrite Hevents; exact Hlookup|auto].
  - destruct segment as [Hsource Hcompletion].
    destruct (os_sched_install_client_state_frame _ _ _ _ _ sg _ _ Hsource)
      as [Hnodes [Hlife [Hevents Hrest]]].
    exists previous; split; [unfold mutex_query_lookup in *; rewrite Hevents; exact Hlookup|auto].
  - destruct (sem_pend_delete_call_frames event_observer _ _ _ _ _ _ _ _ _ _ source)
      as [Htask [Hevent [Hname [Htimer Hsemframe]]]].
    eapply Hsemframe; eassumption.
  - destruct (IHfirst previous Hvalid Hlookup Hsem) as [current [Hcurrent [Hgeneration Htype]]].
    pose proof (proj1 (sem_pend_observed_client_trace_resources _ _ _ _ _ _ _ _ _ _ _
      critical.(critical_region_client_certificates) Hfirst Hvalid)) as Hvalid'.
    destruct (IHlast current Hvalid' Hcurrent ltac:(congruence)) as [final [Hfinal [Hg Ht]]].
    exists final; split; [exact Hfinal|]; split; congruence.
Qed.

Lemma sem_pend_observed_c_sequence_trace : forall segment leaf external port clients sg observer event_observer,
  (forall state before input stopped current after output
    (step : segment state before input stopped current after output) first last,
    leaf state before input stopped current after output step first last ->
    sem_pend_observed_client_trace external port clients sg observer event_observer first state stopped last current) ->
  forall state before input stopped current after output
    (run : kernel_c_sequence segment state before input stopped current after output) first last,
  sem_pend_c_sequence_call_certificate segment leaf state before input stopped current after output run first last ->
  sem_pend_observed_client_trace external port clients sg observer event_observer first state stopped last current.
Proof.
  intros segment leaf external port clients sg observer event_observer Hleaf state before input stopped current after
    output run first last Hcertificate; induction Hcertificate.
  - apply sem_pend_observed_client_trace_refl.
  - eapply Hleaf; eassumption.
  - eapply SemPendObservedThen; eassumption.
  - exact IHHcertificate.
Qed.
