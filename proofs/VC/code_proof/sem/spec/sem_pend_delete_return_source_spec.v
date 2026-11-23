Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.Relations.Relation_Operators.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_retirement.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_delete_call_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_c_segment_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_c_idle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_timeout_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_signal_lifetime_spec.
Import UCOS2_C_Rules TaskStateDef DeleteComponent ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The final Restore is a separate completed C call.  Its prefix,
    selected environment interval and suffix keep their original heaps.
    In particular the recycled body endpoint is not called an API return.
    The receipt is attached to the SAME joint-window proof which computes
    the old Restore history; no endpoint-equal trace is substituted. *)
Section DeleteRestoreCompletion.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  saved_local (sg : StableGlobVars) stored_observer stored_origin (event_observer : option nat)
  (selected : TaskDeleteCProgramSelection environment saved_local sg
    (kernel_program_c_step environment critical sg stored_observer stored_origin))
  requested
  (rely : task_delete_c_environment environment critical saved_local requested sg
    (task_delete_selected_c_environment environment saved_local sg
      (kernel_program_c_step environment critical sg stored_observer stored_origin) selected)).

Inductive sem_pend_delete_restore_completion phase loan original saved acquired released
  returned current before_heap after_heap frame
  (history : task_delete_restore_history environment critical requested phase sg
    original released returned current) stopped : Prop :=
| SemPendDeleteRestoreCompletion : forall prefix_heap environment_heap
    (prefix : task_delete_primitive_c_segment environment critical sg released before_heap
      (task_delete_call_masked environment critical saved_local phase loan sg
        original saved acquired released ** frame)
      false released prefix_heap
      (task_delete_call_closed environment saved_local phase loan sg
        original (armv7a_irq_fiq_mask saved) released ** frame))
    (window : task_delete_joint_c_window environment critical saved_local sg
      (kernel_program_c_step environment critical sg stored_observer stored_origin)
      selected requested rely phase loan original released returned current
      (armv7a_irq_fiq_mask saved) prefix_heap environment_heap frame history stopped),
    sem_pend_delete_joint_window_receipt event_observer environment critical saved_local sg
      stored_observer stored_origin selected requested rely phase loan original released returned current
      (armv7a_irq_fiq_mask saved) prefix_heap environment_heap frame history stopped window ->
    task_delete_primitive_c_segment environment critical sg current environment_heap
      (task_delete_call_closed environment saved_local phase loan sg
        returned (armv7a_irq_fiq_mask saved) current ** frame)
      false current after_heap
      (task_delete_call_closed environment saved_local phase loan sg
        returned (armv7a_irq_fiq_mask saved) current ** frame) ->
    sem_pend_delete_restore_completion phase loan original saved acquired released
      returned current before_heap after_heap frame history stopped.

Lemma sem_pend_delete_restore_completion_sequence :
  forall phase loan original saved acquired released returned current before_heap after_heap frame history stopped,
  sem_pend_delete_restore_completion phase loan original saved acquired released
    returned current before_heap after_heap frame history stopped ->
  kernel_c_sequence (kernel_program_c_step environment critical sg stored_observer stored_origin)
    released before_heap
    (task_delete_call_masked environment critical saved_local phase loan sg original saved acquired released ** frame)
    stopped current after_heap
    (task_delete_call_closed environment saved_local phase loan sg returned (armv7a_irq_fiq_mask saved) current ** frame).
Proof.
  intros * Hcompleted; destruct Hcompleted as [prefix_heap environment_heap Hprefix Hwindow Hreceipt Hsuffix].
  replace stopped with (orb false (orb stopped false)) by (rewrite Bool.orb_false_r; reflexivity).
  eapply KernelCSequenceThen.
  - apply KernelCSequenceAtom, KernelProgramCDeletePrimitive; exact Hprefix.
  - intros heap Howned; exact Howned.
  - eapply KernelCSequenceThen.
    + eapply task_delete_joint_c_window_sequence; exact Hwindow.
    + intros heap Howned; exact Howned.
    + apply KernelCSequenceAtom, KernelProgramCDeletePrimitive; exact Hsuffix.
Qed.

Lemma sem_pend_delete_restore_completion_resources :
  forall phase loan original saved acquired released returned current before_heap after_heap frame history stopped,
  sem_pend_delete_restore_completion phase loan original saved acquired released
    returned current before_heap after_heap frame history stopped ->
  (task_delete_call_masked environment critical saved_local phase loan sg
    original saved acquired released ** frame) before_heap /\
  (task_delete_call_closed environment saved_local phase loan sg
    returned (armv7a_irq_fiq_mask saved) current ** frame) after_heap.
Proof.
  intros * Hcompleted; destruct Hcompleted as [prefix_heap environment_heap Hprefix Hwindow Hreceipt Hsuffix].
  split.
  - exact (proj1 (task_delete_primitive_c_segment_resources _ _ _ _ _ _ _ _ _ _ Hprefix)).
  - exact (proj2 (task_delete_primitive_c_segment_resources _ _ _ _ _ _ _ _ _ _ Hsuffix)).
Qed.

Lemma sem_pend_delete_restore_completion_lifetime :
  forall phase loan original saved acquired released returned current before_heap after_heap frame history stopped,
  sem_pend_delete_restore_completion phase loan original saved acquired released
    returned current before_heap after_heap frame history stopped ->
  forall observer origin,
  task_observer_lifetime_transport observer origin released.(TskState) current.(TskState).
Proof.
  intros * Hcompleted observer origin; eapply sem_pend_delete_interval_lifetime.
  eapply sem_pend_delete_restore_completion_sequence; exact Hcompleted.
Qed.

Lemma sem_pend_delete_restore_completion_multi_pointer :
  forall phase loan original saved acquired released returned current before_heap after_heap frame history stopped,
  sem_pend_delete_restore_completion phase loan original saved acquired released
    returned current before_heap after_heap frame history stopped ->
  forall observer tid old generation,
  task_observer_lifetime released.(TskState) observer (RunningInvocation tid generation) ->
  task_invocation_active current.(TskState) observer (RunningInvocation tid generation) ->
  released.(TskState).(inUsedTaskStates) tid = Some old ->
  exists node, current.(TskState).(inUsedTaskStates) tid = Some node /\
    node.(taskGeneration) = old.(taskGeneration) /\ node.(tcbEventMultiPtr) = old.(tcbEventMultiPtr).
Proof.
  intros * Hcompleted observer tid old generation Hlife Hactive Hold.
  eapply sem_pend_delete_interval_multi_pointer; [|exact Hlife|exact Hactive|exact Hold].
  eapply sem_pend_delete_restore_completion_sequence; exact Hcompleted.
Qed.

Lemma sem_pend_delete_restore_completion_clear_status :
  forall phase loan original saved acquired released returned current before_heap after_heap frame history stopped,
  sem_pend_delete_restore_completion phase loan original saved acquired released
    returned current before_heap after_heap frame history stopped ->
  forall observer tid old generation,
  task_observer_lifetime released.(TskState) observer (RunningInvocation tid generation) ->
  task_invocation_active current.(TskState) observer (RunningInvocation tid generation) ->
  released.(TskState).(inUsedTaskStates) tid = Some old ->
  task_non_suspension_bits old.(stat) = 0 ->
  exists node, current.(TskState).(inUsedTaskStates) tid = Some node /\
    task_non_suspension_bits node.(stat) = 0.
Proof.
  intros * Hcompleted observer tid old generation Hlife Hactive Hold Hclear.
  eapply sem_pend_delete_interval_clear_status; [|exact Hlife|exact Hactive|exact Hold|exact Hclear].
  eapply sem_pend_delete_restore_completion_sequence; exact Hcompleted.
Qed.

Lemma sem_pend_delete_restore_completion_waiter_projection :
  forall phase loan original saved acquired released returned current before_heap after_heap frame history stopped,
  sem_pend_delete_restore_completion phase loan original saved acquired released
    returned current before_heap after_heap frame history stopped ->
  forall observer tid old eid generation,
  task_observer_lifetime released.(TskState) observer (RunningInvocation tid generation) ->
  task_invocation_active current.(TskState) observer (RunningInvocation tid generation) ->
  released.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  sem_pend_task_projection released.(TskState) current.(TskState) tid old.
Proof.
  intros * Hcompleted; destruct Hcompleted as [prefix_heap environment_heap Hprefix Hwindow Hreceipt Hsuffix].
  intros observer tid old eid generation Hlife Hactive Hold Hcont.
  eapply sem_pend_delete_joint_window_waiter_projection; eassumption.
Qed.

Lemma sem_pend_delete_restore_completion_frames :
  forall phase loan original saved acquired released returned current before_heap after_heap frame history stopped,
  sem_pend_delete_restore_completion phase loan original saved acquired released
    returned current before_heap after_heap frame history stopped ->
  task_creation_frame stored_observer released.(TskState) current.(TskState) /\
  (forall invocation, event_observer = Some invocation ->
    event_creation_frame invocation released.(EventState) current.(EventState)) /\
  released.(NameState) = current.(NameState) /\
  timer_public_trace sg released.(TimerState) current.(TimerState) /\
  tmr_task_live_sem_identity released current.
Proof.
  intros * Hcompleted; destruct Hcompleted as [prefix_heap environment_heap Hprefix Hwindow Hreceipt Hsuffix].
  eapply sem_pend_delete_joint_window_frames; exact Hreceipt.
Qed.

(** This immediately consumes the actual final Restore's history and
    suffix owner.  The result-history premise is the pure part of the
    already verified recycled-body post, not a future-state requirement. *)
Lemma sem_pend_delete_restore_completion_final_body :
  forall loan original saved acquired released returned current before_heap after_heap frame history stopped
    name api_original initial,
  sem_pend_delete_restore_completion TaskDeleteStable loan original saved acquired released
    returned current before_heap after_heap frame history stopped ->
  task_delete_result_history sg requested name api_original initial original released ->
  (task_delete_final_body environment critical saved_local sg requested name api_original
    (armv7a_irq_fiq_mask saved) initial returned current released loan ** frame) after_heap.
Proof.
  intros * Hcompleted Hresult.
  pose proof (proj2 (sem_pend_delete_restore_completion_resources _ _ _ _ _ _ _ _ _ _ _ _ _ Hcompleted)) as Howned.
  assert (Hprotocol : task_delete_running_protocol sg returned current).
  { destruct history as [Hsource [Hnormal [Hphase Htransport]]].
    apply (proj1 Htransport); exact (proj2 (proj2 Hresult)). }
  assert (Hpack : task_delete_call_closed environment saved_local TaskDeleteStable loan sg
      returned (armv7a_irq_fiq_mask saved) current ** frame |--
    task_delete_final_body environment critical saved_local sg requested name api_original
      (armv7a_irq_fiq_mask saved) initial returned current released loan ** frame).
  { unfold task_delete_final_body; entailer!; exists original; auto. }
  exact (Hpack after_heap Howned).
Qed.
End DeleteRestoreCompletion.

(** The body and final Restore meet at the SAME recycled heap and call.
    Both stop indices retain their original stored observer/origin.  The
    properties below instead use backward lifetime transport for an
    arbitrary separately observed caller which really survives the end. *)
Record sem_pend_delete_final_restore_source event_observer stored_observer stored_origin capture body_heap
  restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
  final_selected final_rely returned current after_heap history final_stopped : Prop := {
  sem_pend_delete_final_body_source : sem_pend_delete_call_source event_observer stored_observer stored_origin
    capture body_heap restore_selected restore_rely save_selected save_rely restore_stopped save_stopped;
  sem_pend_delete_final_completion :
    sem_pend_delete_restore_completion
      capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_environment)
      capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_critical)
      capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_saved_local)
      capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_globals)
      stored_observer stored_origin event_observer final_selected
      capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_requested) final_rely
      TaskDeleteStable capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_loan)
      capture.(delete_save_returned) capture.(delete_save_saved) capture.(delete_save_resumed)
      (task_delete_capture_cut capture) returned current body_heap after_heap
      capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_frame) history final_stopped
}.

Lemma sem_pend_delete_final_restore_sequence :
  forall event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
    final_selected final_rely returned current after_heap history final_stopped,
  sem_pend_delete_final_restore_source event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
    final_selected final_rely returned current after_heap history final_stopped ->
  let inputs := capture.(delete_save_restore).(delete_restore_inputs) in
  kernel_c_sequence (task_delete_program_segment stored_observer stored_origin capture)
    inputs.(delete_capture_acquired) capture.(delete_save_restore).(delete_restore_before_heap)
    (task_delete_capture_before_owner inputs)
    (orb (task_delete_capture_observer_stopped capture stored_origin restore_stopped save_stopped) final_stopped)
    current after_heap
    (task_delete_call_closed inputs.(delete_capture_environment) inputs.(delete_capture_saved_local)
      TaskDeleteStable inputs.(delete_capture_loan) inputs.(delete_capture_globals)
      returned (armv7a_irq_fiq_mask capture.(delete_save_saved)) current ** inputs.(delete_capture_frame)).
Proof.
  intros * [Hbody Hrestore] inputs.
  eapply KernelCSequenceThen.
  - exact (sem_pend_delete_call_run event_observer _ _ _ _ _ _ _ _ _ _ Hbody).
  - intros heap Howned; exact Howned.
  - eapply sem_pend_delete_restore_completion_sequence; exact Hrestore.
Qed.

Lemma sem_pend_delete_final_restore_lifetime :
  forall event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
    final_selected final_rely returned current after_heap history final_stopped,
  sem_pend_delete_final_restore_source event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
    final_selected final_rely returned current after_heap history final_stopped ->
  forall observer origin,
  task_observer_lifetime_transport observer origin
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState) current.(TskState).
Proof.
  intros * Hsource observer origin; eapply sem_pend_delete_interval_lifetime.
  eapply sem_pend_delete_final_restore_sequence; exact Hsource.
Qed.

Lemma sem_pend_delete_final_restore_multi_pointer :
  forall event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
    final_selected final_rely returned current after_heap history final_stopped,
  sem_pend_delete_final_restore_source event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
    final_selected final_rely returned current after_heap history final_stopped ->
  forall observer tid old generation,
  task_observer_lifetime capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState)
    observer (RunningInvocation tid generation) ->
  task_invocation_active current.(TskState) observer (RunningInvocation tid generation) ->
  capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState).(inUsedTaskStates) tid = Some old ->
  exists node, current.(TskState).(inUsedTaskStates) tid = Some node /\
    node.(taskGeneration) = old.(taskGeneration) /\ node.(tcbEventMultiPtr) = old.(tcbEventMultiPtr).
Proof.
  intros * Hsource observer tid old generation Hlife Hactive Hold.
  eapply sem_pend_delete_interval_multi_pointer; [|exact Hlife|exact Hactive|exact Hold].
  eapply sem_pend_delete_final_restore_sequence; exact Hsource.
Qed.

Lemma sem_pend_delete_final_restore_clear_status :
  forall event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
    final_selected final_rely returned current after_heap history final_stopped,
  sem_pend_delete_final_restore_source event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
    final_selected final_rely returned current after_heap history final_stopped ->
  forall observer tid old generation,
  task_observer_lifetime capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState)
    observer (RunningInvocation tid generation) ->
  task_invocation_active current.(TskState) observer (RunningInvocation tid generation) ->
  capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState).(inUsedTaskStates) tid = Some old ->
  task_non_suspension_bits old.(stat) = 0 ->
  exists node, current.(TskState).(inUsedTaskStates) tid = Some node /\
    task_non_suspension_bits node.(stat) = 0.
Proof.
  intros * Hsource observer tid old generation Hlife Hactive Hold Hclear.
  eapply sem_pend_delete_interval_clear_status; [|exact Hlife|exact Hactive|exact Hold|exact Hclear].
  eapply sem_pend_delete_final_restore_sequence; exact Hsource.
Qed.

Lemma sem_pend_delete_final_restore_waiter_projection :
  forall event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
    final_selected final_rely returned current after_heap history final_stopped,
  sem_pend_delete_final_restore_source event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
    final_selected final_rely returned current after_heap history final_stopped ->
  forall observer tid old eid generation,
  task_observer_lifetime capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState)
    observer (RunningInvocation tid generation) ->
  task_invocation_active current.(TskState) observer (RunningInvocation tid generation) ->
  capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  sem_pend_task_projection capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState)
    current.(TskState) tid old.
Proof.
  intros * [Hbody Hrestore] observer tid old eid generation Hlife Hactive Hold Hcont.
  pose proof (proj1 (sem_pend_delete_call_lifetime event_observer _ _ _ _ _ _ _ _ _ _ Hbody
    observer (RunningInvocation tid generation) Hlife)) as Hcut_life.
  pose proof (proj2 (sem_pend_delete_restore_completion_lifetime _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ Hrestore observer (RunningInvocation tid generation) Hcut_life) Hactive) as Hcut_active.
  destruct (sem_pend_delete_call_waiter_projection event_observer _ _ _ _ _ _ _ _ _ _ Hbody
    observer tid old eid generation Hlife Hcut_active Hold Hcont) as [cut_node [Hcut Hfirst]].
  pose proof (sem_pend_wait_trace_preserves_continuation _ _ _ _ Hfirst Hcont) as Hcut_cont.
  destruct (sem_pend_delete_restore_completion_waiter_projection _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ Hrestore observer tid cut_node eid generation
    Hcut_life Hactive Hcut Hcut_cont) as [node [Hnode Hlast]].
  exists node; split; [exact Hnode|]. eapply rt_trans; eassumption.
Qed.

(** This is the actual C post-to-source factory.  The body result is
    extracted before the original final-body assertion hides [cut_call]. *)
Lemma sem_pend_delete_final_restore_from_recycled_post :
  forall event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
    final_selected final_rely returned current after_heap history final_stopped
    (body : sem_pend_delete_call_source event_observer stored_observer stored_origin capture body_heap
      restore_selected restore_rely save_selected save_rely restore_stopped save_stopped),
  let inputs := capture.(delete_save_restore).(delete_restore_inputs) in
  sem_pend_delete_restore_completion inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_saved_local) inputs.(delete_capture_globals) stored_observer stored_origin event_observer
    final_selected inputs.(delete_capture_requested) final_rely TaskDeleteStable inputs.(delete_capture_loan)
    capture.(delete_save_returned) capture.(delete_save_saved) capture.(delete_save_resumed)
    (task_delete_capture_cut capture) returned current body_heap after_heap inputs.(delete_capture_frame) history final_stopped ->
  (task_delete_recycled_body inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_saved_local) inputs.(delete_capture_globals) inputs.(delete_capture_requested)
    inputs.(delete_capture_original) inputs.(delete_capture_initial) capture.(delete_save_returned)
    capture.(delete_save_saved) capture.(delete_save_resumed) (task_delete_capture_cut capture)
    inputs.(delete_capture_loan) inputs.(delete_capture_name) ** inputs.(delete_capture_frame)) body_heap ->
  sem_pend_delete_final_restore_source event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
    final_selected final_rely returned current after_heap history final_stopped /\
  (task_delete_final_body inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_saved_local) inputs.(delete_capture_globals) inputs.(delete_capture_requested)
    inputs.(delete_capture_name) inputs.(delete_capture_original) (armv7a_irq_fiq_mask capture.(delete_save_saved))
    inputs.(delete_capture_initial) returned current (task_delete_capture_cut capture) inputs.(delete_capture_loan) **
    inputs.(delete_capture_frame)) after_heap.
Proof.
  intros event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
    final_selected final_rely returned current after_heap history final_stopped body inputs Hrestore Hpost.
  assert (Hresult : task_delete_result_history inputs.(delete_capture_globals) inputs.(delete_capture_requested)
    inputs.(delete_capture_name) inputs.(delete_capture_original) inputs.(delete_capture_initial)
    capture.(delete_save_returned) (task_delete_capture_cut capture)).
  { destruct Hpost as [hbody [hframe [Hjoin [Hbody Hframe]]]].
    exact (proj1 Hbody). }
  split; [constructor; assumption|].
  eapply sem_pend_delete_restore_completion_final_body; eassumption.
Qed.

(** The original Scheduler result is preserved at its existential
    production point, before [task_delete_scheduled_api_post] forgets it.
    Keeping this packet does not assert that an arbitrary raw body has a
    typed receipt.  Its Save, body and Restore proofs are the actual three
    components of this one call history. *)
Definition sem_pend_delete_sched_history environment critical sg original mask before
  scheduled entry resumed released saved returned current
  (save : os_sched_continuation_save_effect environment critical sg original mask saved before scheduled entry)
  (body : os_sched_c_return environment.(task_stack_call_external) critical sg entry scheduled resumed released)
  (restore : os_sched_continuation_restore_effect environment critical sg resumed released returned current) :
  os_sched_continuation_call_history environment critical sg original mask before returned current :=
  ex_intro _ scheduled (ex_intro _ entry (ex_intro _ resumed (ex_intro _ released
    (ex_intro _ saved (conj save (conj body restore)))))).

Lemma sem_pend_delete_sched_history_same_call :
  forall environment critical sg original mask before scheduled entry resumed released saved returned current
    (save : os_sched_continuation_save_effect environment critical sg original mask saved before scheduled entry)
    (body : os_sched_c_return environment.(task_stack_call_external) critical sg entry scheduled resumed released)
    (restore : os_sched_continuation_restore_effect environment critical sg resumed released returned current),
  task_tcb_init_stack_same_call returned original.
Proof.
  intros; eapply os_sched_continuation_call_history_same_call.
  exact (sem_pend_delete_sched_history environment critical sg original mask before
    scheduled entry resumed released saved returned current save body restore).
Qed.

(** The following are observations of the completed protected BODY.
    They intentionally do not call its recycled endpoint a normal API
    return.  The current-origin transport follows the two original CPU
    call histories, while observer cache/lifetime continue to use the
    independent stored observer/origin of [sem_pend_delete_call_source]. *)
Local Lemma sem_pend_delete_prepare_running : forall before tid old prepared loan,
  task_delete_prepare_single_wait before tid old = Some (prepared, loan) ->
  prepared.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros before tid old prepared loan Hprepare.
  unfold task_delete_prepare_single_wait in Hprepare.
  destruct old.(eventPtr) as [eid|];
    [destruct (before.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate]|];
    cbn [task_set_event_ptr tcbFlagNode] in Hprepare;
    lazymatch type of Hprepare with
    | context [if ?test then _ else _] => destruct test eqn:Hflag
    end;
    try (lazymatch type of Hprepare with
      | context [match ?lookup with Some _ => _ | None => _ end] =>
          destruct lookup as [[waiter flags]|] eqn:Hunlink; [|discriminate]
      end);
    inversion Hprepare; subst; reflexivity.
Qed.

Local Lemma sem_pend_delete_masked_owner_phase_valid :
  forall environment critical local phase loan sg call saved acquired state heap frame,
  (task_delete_call_masked environment critical local phase loan sg call saved acquired state ** frame) heap ->
  task_delete_phase_valid phase sg state.
Proof.
  intros environment critical local phase loan sg call saved acquired state heap frame Howner.
  unfold task_delete_call_masked, kernel_continuation_call_masked,
    kernel_continuation_inv, task_delete_phase_resources in Howner.
  destruct Howner as [hmasked [hframe [Hjoin [Hmasked Hframe]]]].
  destruct Hmasked as [hcall [hworld [Hjoin' [Hcall [Hcoverage Hworld]]]]].
  destruct Hworld as [hresources [hparked [Hjoin'' [Hresources Hparked]]]].
  exact (proj1 Hresources).
Qed.

Lemma sem_pend_delete_capture_body_valid :
  forall event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped,
  sem_pend_delete_call_source event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped ->
  UCOS2_state_inv capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_globals)
    (task_delete_capture_cut capture).
Proof.
  intros * Hsource.
  pose proof (proj2 (sem_pend_delete_call_resources event_observer _ _ _ _ _ _ _ _ _ _ Hsource)) as Howned.
  eapply (sem_pend_delete_masked_owner_phase_valid _ _ _ TaskDeleteStable).
  exact Howned.
Qed.

Lemma sem_pend_delete_capture_body_running :
  forall event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped,
  sem_pend_delete_call_source event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped ->
  (task_delete_capture_cut capture).(SchedState).(isRunning) =
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(SchedState).(isRunning).
Proof.
  intros * Hsource.
  pose proof capture.(delete_save_restore).(delete_restore_preparation) as [_ [Hprepare Hprotocol]].
  pose proof (sem_pend_delete_prepare_running _ _ _ _ _ Hprepare) as Hfirst.
  pose proof capture.(delete_save_restore).(delete_restore_history) as [_ [_ [Hrestore _]]].
  pose proof capture.(delete_save_observation) as [_ [_ [Hsave _]]].
  pose proof (proj1 (proj2 Hrestore)) as Hmiddle.
  pose proof (proj1 (proj2 Hsave)) as Hlast.
  change ((delete_save_resumed capture).(SchedState).(isRunning) =
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(SchedState).(isRunning)).
  change (capture.(delete_save_restore).(delete_restore_between).(SchedState).(isRunning) =
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_prepared).(SchedState).(isRunning)) in Hmiddle.
  congruence.
Qed.

Lemma sem_pend_delete_capture_body_current :
  forall event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped,
  sem_pend_delete_call_source event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped ->
  task_execution_current
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_first).(os_sched_call_origin)
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired) ->
  task_execution_current capture.(delete_save_returned).(os_sched_call_origin) (task_delete_capture_cut capture).
Proof.
  intros * Hsource Hcurrent.
  pose proof capture.(delete_save_restore).(delete_restore_preparation) as [_ [Hprepare Hprotocol]].
  pose proof (proj2 (proj2 (proj2 (proj2
    (TaskDeleteCompletedMacro.task_delete_prepare_single_wait_metadata_frame _ _ _ _ _ Hprepare))))) as Hprepare_id.
  assert (Hprepared : task_execution_current
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_first).(os_sched_call_origin)
    (task_delete_locked capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_prepared))).
  { unfold task_execution_current in *.
    destruct capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_first).(os_sched_call_origin) as [|slot generation];
      [exact I|]. change (capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_prepared).(SchedState).(curTaskID) = Some slot).
    rewrite Hprepare_id; exact Hcurrent. }
  pose proof (proj1 capture.(delete_save_restore).(delete_restore_history)) as Hrestore.
  assert (Hbetween : task_execution_current capture.(delete_save_restore).(delete_restore_middle).(os_sched_call_origin)
    capture.(delete_save_restore).(delete_restore_between)).
  { eapply task_execution_source_trace_preserves_current;
      [exact (proj2 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Hrestore))|exact Hprepared]. }
  pose proof (proj1 (proj1 capture.(delete_save_observation))) as Hsave.
  change (task_execution_current capture.(delete_save_returned).(os_sched_call_origin) capture.(delete_save_resumed)).
  eapply task_execution_source_trace_preserves_current;
    [exact (proj2 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Hsave))|exact Hbetween].
Qed.

Lemma sem_pend_delete_capture_body_idle :
  forall event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped,
  sem_pend_delete_call_source event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped ->
  capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(SchedState).(isRunning) = true ->
  task_idle_ready capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_globals)
    (task_delete_capture_cut capture).(TskState).
Proof.
  intros * Hsource Hrunning.
  apply SelectedDeleteIdle.task_delete_capture_recycle_idle.
  change ((task_delete_capture_cut capture).(SchedState).(isRunning) = true).
  rewrite (sem_pend_delete_capture_body_running event_observer _ _ _ _ _ _ _ _ _ _ Hsource); exact Hrunning.
Qed.

(** Active identity is a separate consequence of the finite C leaves.
    It does not need an observer-cache hypothesis.  The only retiring leaf
    uses its original stop index; all other leaves use their proved source
    operation, including both creation variants and the actual IRQ transfer. *)
Local Lemma sem_pend_program_c_step_preserves_active :
  forall environment critical sg observer origin state before input stopped returned after output,
  kernel_program_c_step environment critical sg observer origin
    state before input stopped returned after output -> stopped = false ->
  task_invocation_active state.(TskState) observer origin ->
  task_invocation_active returned.(TskState) observer origin.
Proof.
  intros environment critical sg observer origin state before input stopped returned after output
    Hstep Hstop Hactive; destruct Hstep.
  - destruct call as [actual|actual];
      destruct H as [Hcompletion [Hphysical [Hsource Hpacket]]]; cbn in *.
    + destruct Hsource as [code [Hcritical Hresult]].
      eapply CriticalComponent.task_change_prio_critical_preserves_invocation_active; eassumption.
    + eapply CriticalComponent.mutex_del_call_fields_preserve_invocation; [|exact Hactive].
      exact (proj1 (CriticalComponent.mutex_del_critical_call_observation_fields
        _ _ _ _ _ _ _ _ Hsource)).
  - destruct H.
    + destruct operation; exact Hactive.
    + destruct H as [Hpre Hpost].
      assert (Hvalid : UCOS2_state_inv sg state).
      { destruct Hpre as [owned [rest [Hjoin [[Hfacts Howned] Hrest]]]]; exact (proj1 Hfacts). }
      exact (kernel_client_preserves_continuation _ (task_create_stack_publication_certificate publication)
        sg state (task_create_stack_publication_state sg publication state) observer origin
        Hvalid effect eq_refl Hactive).
    + exact (proj1 (BuiltinComponent.kernel_irq_transfer_c_completion_preserves_observer
        _ _ _ _ _ _ _ _ _ _ _ _ H Hactive)).
  - destruct H.
    exact (proj1 (InstallComponent.task_install_c_segment_preserves_observer
      environment local sg frame observer origin call before after sp Hactual H Hactive)).
  - eapply WakeComponent.kernel_wake_c_source_preserves_observer_active;
      [exact (WakeComponent.kernel_wake_c_segment_source _ _ _ _ _ _ _ H)|exact Hactive].
  - destruct H as [Hsource Hpre Hpost].
    eapply StatusComponent.kernel_status_c_source_preserves_observer_active; eassumption.
  - eapply CreationComponent.kernel_task_creation_c_source_preserves_observer_active;
      [exact (CreationComponent.kernel_task_creation_c_segment_source _ _ _ _ _ _ _ H)|exact Hactive].
  - pose proof (EventCreationComponent.kernel_event_creation_c_segment_source _ _ _ _ _ _ _ H) as Hsource.
    rewrite (proj1 (EventCreationComponent.kernel_event_creation_c_source_fields_eq _ _ Hsource)); exact Hactive.
  - pose proof (QueueCreationComponent.kernel_queue_creation_c_segment_source _ _ _ _ _ _ _ H) as Hsource.
    rewrite (proj1 (QueueCreationComponent.kernel_queue_creation_c_source_fields_eq _ _ _ Hsource)); exact Hactive.
  - destruct H as [[Hnode [Hother Hsource]] Hpre Hpost].
    eapply PendComponent.mutex_pend_inherit_preserves_observer_active; eassumption.
  - destruct H as [[Hcaller Hsource] Hpre Hpost].
    eapply PostComponent.mutex_post_critical_preserves_observer_active; eassumption.
  - destruct H; exact Hactive.
  - destruct H; try exact Hactive. destruct H; exact Hactive.
  - destruct H as [inputs before_heap prepared_heap Hcontext Hcompletion|capture after_heap Hcontext Hcompletion].
    + destruct Hcompletion as [Hprepare Hbefore Hafter].
      eapply task_delete_preparation_history_preserves_observer_active; eassumption.
    + eapply task_delete_cut_preserves_observer_active; eassumption.
Qed.

Local Lemma sem_pend_program_c_sequence_preserves_active :
  forall environment critical sg observer origin state before input stopped returned after output,
  kernel_c_sequence (kernel_program_c_step environment critical sg observer origin)
    state before input stopped returned after output -> stopped = false ->
  task_invocation_active state.(TskState) observer origin ->
  task_invocation_active returned.(TskState) observer origin.
Proof.
  intros environment critical sg observer origin state before input stopped returned after output Hrun.
  induction Hrun; intros Hstop Hactive.
  - exact Hactive.
  - eapply sem_pend_program_c_step_preserves_active; eassumption.
  - apply Bool.orb_false_iff in Hstop; destruct Hstop as [Hfirst Hlast].
    apply IHHrun2; [exact Hlast|]. apply IHHrun1; assumption.
  - apply IHHrun; assumption.
Qed.

Lemma sem_pend_delete_capture_body_preserves_active :
  forall event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped,
  sem_pend_delete_call_source event_observer stored_observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped ->
  task_delete_capture_observer_stopped capture stored_origin restore_stopped save_stopped = false ->
  task_invocation_active capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState)
    stored_observer stored_origin ->
  task_invocation_active (task_delete_capture_cut capture).(TskState) stored_observer stored_origin.
Proof.
  intros * Hsource Hstop Hactive.
  eapply sem_pend_program_c_sequence_preserves_active;
    [exact (sem_pend_delete_call_run event_observer _ _ _ _ _ _ _ _ _ _ Hsource)|
      exact Hstop|exact Hactive].
Qed.
