Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Ucos2Verify.lib.timer Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.event Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.VC.code.core.spec.kernel_client_resumption.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_pend_abort_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_stage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_critical_idle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_wake_status_idle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_idle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_idle_guard_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fresh_fields_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_c_idle_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_idle_frames_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_client_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.task_status.
Import TaskStateDef ListNotations.
Local Open Scope Z_scope.

(** Named Timer source cuts. The returned bool/error, cached successor and
    callback request are PARAMETERS of a cut: they are not erased into an
    unconstrained final Timer state. Stop and expire end BEFORE callback
    execution. Raw allocation and publication are kept separately because
    a raw client trace can contain them; only a completed public segment
    has the stronger image-presence frame used by resumption histories. *)
Inductive TmrTaskTimerSourceCut : Type :=
| TmrTaskTimerAllocate (index : TimerID) (private : TimerPrivateAllocation)
| TmrTaskTimerPublish (index : TimerID) (private : TimerPrivateAllocation)
    (delay period : Z) (mode : TimerMode) (callback argument name : Z)
| TmrTaskTimerRelease (index : TimerID) (old : TimerImage) (name : Z)
| TmrTaskTimerLink (index : TimerID) (periodic : bool)
| TmrTaskTimerUnlink (index : TimerID)
| TmrTaskTimerComplete (index : TimerID)
| TmrTaskTimerAdvance
| TmrTaskTimerStart (index : TimerID) (result : bool) (error : OSErrCode)
| TmrTaskTimerStopDispatch (index : TimerID) (opt argument : Z)
    (result : bool) (error : OSErrCode) (request : option (Z * Z * Z))
| TmrTaskTimerDelete (index : TimerID) (name : Z) (result : bool) (error : OSErrCode)
| TmrTaskTimerExpireDispatch (index : TimerID) (cached : Z)
    (request : option (Z * Z * Z)).

Definition tmr_task_timer_cut_source sg cut (before after : GlobTimerState) : Prop :=
  match cut with
  | TmrTaskTimerAllocate index private => timer_allocate before = Some (index, private, after)
  | TmrTaskTimerPublish index private delay period mode callback argument name =>
      after = timer_publish before index private delay period mode callback argument name
  | TmrTaskTimerRelease index old name =>
      before.(timerImages) index = Some old /\ after = timer_release sg before index old name
  | TmrTaskTimerLink index periodic => timer_link sg before index periodic = Some after
  | TmrTaskTimerUnlink index => timer_unlink sg before index = Some after
  | TmrTaskTimerComplete index => timer_complete before index = Some after
  | TmrTaskTimerAdvance => after = timer_service_advance before
  | TmrTaskTimerStart index result error => timer_start_locked sg before index = Some (result, error, after)
  | TmrTaskTimerStopDispatch index opt argument result error request =>
      timer_stop_dispatch sg before index opt argument = Some (result, error, request, after)
  | TmrTaskTimerDelete index name result error =>
      timer_delete_locked sg before index name = Some (result, error, after)
  | TmrTaskTimerExpireDispatch index cached request =>
      timer_expire_dispatch sg before index = Some (cached, request, after)
  end.

Lemma tmr_task_timer_cut_initialization_phase_eq : forall sg cut before after,
  tmr_task_timer_cut_source sg cut before after ->
  after.(timerInitPhase) = before.(timerInitPhase).
Proof.
  intros sg cut before after; destruct cut; cbn [tmr_task_timer_cut_source]; intro Hsource.
  - unfold timer_allocate in Hsource.
    destruct before.(timerFree) as [|slot rest]; [discriminate|].
    destruct (before.(timerImages) slot); [|discriminate].
    inversion Hsource; reflexivity.
  - subst after; reflexivity.
  - destruct Hsource as [_ ->]; reflexivity.
  - eapply timer_link_preserves_initialization_phase; exact Hsource.
  - eapply timer_unlink_preserves_initialization_phase; exact Hsource.
  - eapply timer_complete_preserves_initialization_phase; exact Hsource.
  - subst after; reflexivity.
  - eapply timer_start_locked_preserves_initialization_phase; exact Hsource.
  - eapply timer_stop_dispatch_preserves_initialization_phase; exact Hsource.
  - eapply timer_delete_locked_preserves_initialization_phase; exact Hsource.
  - eapply timer_expire_dispatch_preserves_initialization_phase; exact Hsource.
Qed.

Definition tmr_task_timer_source_client (actor : option nat) cut : KernelClientAction :=
  {| kernel_client_actor := actor;
     kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after => exists timers,
       tmr_task_timer_cut_source sg cut before.(TimerState) timers /\
       after = replace_TimerS timers before |}.

Lemma tmr_task_timer_cut_client_step : forall actor sg cut before timers,
  tmr_task_timer_cut_source sg cut before.(TimerState) timers ->
  kernel_client_step (tmr_task_timer_source_client actor cut) sg before
    (replace_TimerS timers before).
Proof. intros; exists timers; split; [exact H|reflexivity]. Qed.

Lemma tmr_task_timer_client_source : forall actor sg cut before after,
  kernel_client_step (tmr_task_timer_source_client actor cut) sg before after ->
  tmr_task_timer_cut_source sg cut before.(TimerState) after.(TimerState) /\
  after = replace_TimerS after.(TimerState) before.
Proof. intros actor sg cut before after [timers [Hsource ->]]; split; [exact Hsource|reflexivity]. Qed.

Lemma tmr_task_timer_source_client_preserves_initialized : forall actor cut sg,
  tmr_task_fields_action_preserves_initialized sg (tmr_task_timer_source_client actor cut).
Proof.
  intros actor cut sg before after [timers [Hsource ->]] Hinit.
  unfold timer_api_initialized in *; cbn [replace_TimerS TimerState].
  rewrite (tmr_task_timer_cut_initialization_phase_eq sg cut before.(TimerState) timers Hsource).
  exact Hinit.
Qed.

Lemma tmr_task_timer_source_client_name_frame : forall actor cut sg before after,
  kernel_client_step (tmr_task_timer_source_client actor cut) sg before after ->
  before.(NameState) = after.(NameState).
Proof. intros actor cut sg before after [timers [_ ->]]; reflexivity. Qed.

(** A completed source call can also register its actual cut directly.
    Its source relation is retained alongside the actual input/output.
    The C body supplies its closed output resources; no all-input validity
    theorem for an unguarded internal helper is fabricated. In particular
    source evidence is still required even when the output owns UCOS2_inv.
    This mirrors the existing actual-call payloads of KernelCriticalCCall. *)
Definition tmr_task_timer_call_client (actor : option nat) (source_sg : StableGlobVars)
  cut (entry : UCOS2_Verify_State) (timers : GlobTimerState) : KernelClientAction :=
  {| kernel_client_actor := actor; kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       sg = source_sg /\ before = entry /\
       tmr_task_timer_cut_source sg cut before.(TimerState) timers /\
       after = replace_TimerS timers before |}.

Lemma tmr_task_timer_call_client_source : forall actor source_sg cut entry timers sg before after,
  kernel_client_step (tmr_task_timer_call_client actor source_sg cut entry timers) sg before after ->
  kernel_client_step (tmr_task_timer_source_client actor cut) sg before after.
Proof. intros actor source_sg cut entry timers sg before after [_ [_ [Hsource ->]]]; exists timers; auto. Qed.

Lemma tmr_task_timer_call_client_certificate : forall actor sg cut entry timers,
  UCOS2_state_inv sg (replace_TimerS timers entry) ->
  KernelClientCertificate (tmr_task_timer_call_client actor sg cut entry timers).
Proof.
  intros actor sg cut entry timers Hclosed; constructor.
  - intros actual_sg before after Hvalid [-> [-> [Hsource ->]]]; exact Hclosed.
  - intros actual_sg before after observer Hvalid [_ [_ [_ ->]]] Hforeign; reflexivity.
  - intros actual_sg before after observer origin Hvalid [_ [_ [_ ->]]] Hnormal Hactive; exact Hactive.
  - intros actual_sg before after observer Hvalid [_ [_ [_ ->]]] Hforeign; reflexivity.
Qed.

(** The additional Sem family names precisely the existing source actions.
    It does not include SemPendSourceTaskEventRunningFrame: that constructor
    proves a wait-field property and deliberately says nothing about Timer.
    The actual counter cuts are included through SchedTaskSourceProfile. *)
Inductive tmr_task_sem_source_client : KernelClientAction -> Prop :=
| TmrTaskSemTick : forall selected,
    tmr_task_sem_source_client (sem_pend_tick_source_client selected)
| TmrTaskSemPost : forall actor eid,
    tmr_task_sem_source_client (sem_pend_post_source_client actor eid)
| TmrTaskSemAbort : forall actor eid option,
    tmr_task_sem_source_client (sem_pend_abort_source_client actor eid option)
| TmrTaskSemSavedSP : forall actor selected sp,
    tmr_task_sem_source_client (sem_pend_saved_sp_source_client actor selected sp)
| TmrTaskSemDelayResume : forall actor priority,
    tmr_task_sem_source_client (sem_pend_delay_resume_source_client actor priority).

Lemma tmr_task_sem_source_client_wait_projection : forall action,
  tmr_task_sem_source_client action -> sem_pend_projected_source_client action.
Proof. intros action Hsource; destruct Hsource; constructor. Qed.

Lemma tmr_task_sem_post_name_timer_frame : forall sg eid before result after,
  sem_post_critical sg eid before result after ->
  before.(NameState) = after.(NameState) /\ before.(TimerState) = after.(TimerState).
Proof.
  intros sg eid before result after [event [Hevent Hsource]].
  lazymatch type of Hsource with
  | (if ?condition then _ else _) => destruct condition in Hsource
  end.
  - destruct Hsource as [fields [_ Hsource]].
    lazymatch type of Hsource with
    | (if ?condition then _ else _) => destruct condition in Hsource
    end; destruct Hsource as [_ ->]; split; reflexivity.
  - destruct Hsource as [_ [priority Hsource]].
    eapply CriticalComponent.mutex_del_wake_name_timer_frame; exact Hsource.
Qed.

Lemma tmr_task_sem_abort_name_timer_frame : forall sg eid option before result after,
  event_pend_abort_critical sg eid PendSem option before result after ->
  before.(NameState) = after.(NameState) /\ before.(TimerState) = after.(TimerState).
Proof.
  intros sg eid option before result after [event [Hevent Hsource]].
  lazymatch type of Hsource with
  | (if ?condition then _ else _) => destruct condition in Hsource
  end.
  - destruct Hsource as [_ ->]; split; reflexivity.
  - lazymatch type of Hsource with
    | (if ?condition then _ else _) => destruct condition in Hsource
    end.
    + destruct Hsource as [priorities [Hsource _]].
      eapply CriticalComponent.mutex_del_broadcast_name_timer_frame; exact Hsource.
    + destruct Hsource as [priority [Hsource _]].
      eapply CriticalComponent.mutex_del_wake_name_timer_frame; exact Hsource.
Qed.

Lemma tmr_task_change_priority_name_timer_frame : forall sg oldprio newprio before result after,
  task_change_priority_critical sg oldprio newprio before result after ->
  before.(NameState) = after.(NameState) /\ before.(TimerState) = after.(TimerState).
Proof.
  intros sg oldprio newprio before result after [_ Hsource].
  destruct (before.(TskState).(prioTbl) newprio).
  - destruct Hsource as [selected [_ [_ Hsource]]].
    destruct (before.(TskState).(prioTbl) selected) as [| |selected_tid].
    + destruct Hsource as [_ ->]; split; reflexivity.
    + destruct Hsource as [_ ->]; split; reflexivity.
    + destruct Hsource as [old [_ [_ [_ [_ ->]]]]]; split; reflexivity.
  - destruct Hsource as [_ ->]; split; reflexivity.
  - destruct Hsource as [_ ->]; split; reflexivity.
Qed.

Lemma tmr_task_delay_resume_name_timer_frame : forall sg priority before result after,
  time_delay_resume_critical sg priority before result after ->
  before.(NameState) = after.(NameState) /\ before.(TimerState) = after.(TimerState).
Proof.
  intros sg priority before result after [_ Hsource].
  destruct (before.(TskState).(prioTbl) priority).
  - destruct Hsource as [_ ->]; split; reflexivity.
  - destruct Hsource as [_ ->]; split; reflexivity.
  - destruct Hsource as [old [_ Hsource]].
    destruct (Z.eqb old.(dly) 0); destruct Hsource as [_ ->]; split; reflexivity.
Qed.

Lemma tmr_task_sem_source_client_name_timer_frame : forall action sg before after,
  tmr_task_sem_source_client action -> kernel_client_step action sg before after ->
  before.(NameState) = after.(NameState) /\ before.(TimerState) = after.(TimerState).
Proof.
  intros action sg before after Hsource; destruct Hsource; intro Hstep.
  - destruct Hstep as [old [_ ->]].
    pose proof (tick_task_step_non_task_sched_state_eq sg selected old before) as Hframe.
    split; symmetry; [exact (f_equal NameState Hframe)|exact (f_equal TimerState Hframe)].
  - destruct Hstep as [result Hstep]; eapply tmr_task_sem_post_name_timer_frame; exact Hstep.
  - destruct Hstep as [result Hstep]; eapply tmr_task_sem_abort_name_timer_frame; exact Hstep.
  - change (after = os_sched_save_current_sp before selected sp) in Hstep; subst after.
    unfold os_sched_save_current_sp; destruct (before.(TskState).(inUsedTaskStates) selected);
      split; reflexivity.
  - destruct Hstep as [_ [result Hstep]]; eapply tmr_task_delay_resume_name_timer_frame; exact Hstep.
Qed.

Lemma tmr_task_sem_source_client_preserves_initialized : forall action sg,
  tmr_task_sem_source_client action -> tmr_task_fields_action_preserves_initialized sg action.
Proof.
  intros action sg Hsource; apply tmr_task_fields_action_initialized_from_timer_frame.
  intros before after Hstep; symmetry.
  exact (proj2 (tmr_task_sem_source_client_name_timer_frame action sg before after Hsource Hstep)).
Qed.

(** The serialized tick cut begins after the actual port/application hook;
    it is not a model of that hook. The separate post cut retains the
    canonical NULL/type/count/overflow/wake results used by OSTmrSignal.
    Scheduling, if requested, is a subsequent source segment. *)
Inductive TmrTaskTickSourceCut : Type :=
| TmrTaskTickClock
| TmrTaskTickSerialized
| TmrTaskTickPost (pointer : Z) (result : TimeTickPostResult).

Definition tmr_task_tick_cut_source sg cut before after : Prop :=
  match cut with
  | TmrTaskTickClock => after = time_tick_clock_step_state before
  | TmrTaskTickSerialized => after = time_tick_serialized_after_hook sg before
  | TmrTaskTickPost pointer result => time_tick_post_call sg pointer before result after
  end.

Definition tmr_task_tick_source_client (actor : option nat) cut : KernelClientAction :=
  {| kernel_client_actor := actor; kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after => tmr_task_tick_cut_source sg cut before after |}.

Lemma tmr_task_tick_scan_name_timer_frame : forall sg visited before,
  before.(NameState) = (time_tick_scan sg before visited).(NameState) /\
  before.(TimerState) = (time_tick_scan sg before visited).(TimerState).
Proof.
  intros sg visited; induction visited as [|selected rest IH]; intros before.
  - split; reflexivity.
  - change (before.(NameState) = (time_tick_scan sg (time_tick_visit sg before selected) rest).(NameState) /\
      before.(TimerState) = (time_tick_scan sg (time_tick_visit sg before selected) rest).(TimerState)).
    destruct (IH (time_tick_visit sg before selected)) as [Hname Htimer].
    rewrite <- Hname, <- Htimer; unfold time_tick_visit.
    destruct (before.(TskState).(inUsedTaskStates) selected) as [old|]; [|split; reflexivity].
    pose proof (tick_task_step_non_task_sched_state_eq sg selected old before) as Hframe.
    split; symmetry; [exact (f_equal NameState Hframe)|exact (f_equal TimerState Hframe)].
Qed.

Lemma tmr_task_tick_cut_name_timer_frame : forall sg cut before after,
  tmr_task_tick_cut_source sg cut before after ->
  before.(NameState) = after.(NameState) /\ before.(TimerState) = after.(TimerState).
Proof.
  intros sg cut before after; destruct cut; cbn [tmr_task_tick_cut_source]; intro Hsource.
  - subst after; unfold time_tick_clock_step_state; destruct (tick_step_advance _ _); split; reflexivity.
  - subst after; unfold time_tick_serialized_after_hook; destruct (time_tick_process_tasks before).
    + destruct (tmr_task_tick_scan_name_timer_frame sg
        (removelast before.(TskState).(taskLifecycle).(taskActiveOrder))
        (time_tick_clock_step_state before)) as [Hname Htimer].
      rewrite <- Hname, <- Htimer; unfold time_tick_clock_step_state;
        destruct (tick_step_advance _ _); split; reflexivity.
    + unfold time_tick_clock_step_state; destruct (tick_step_advance _ _); split; reflexivity.
  - destruct Hsource; try (split; reflexivity).
    eapply tmr_task_sem_post_name_timer_frame; eassumption.
Qed.

Lemma tmr_task_tick_source_client_preserves_initialized : forall actor cut sg,
  tmr_task_fields_action_preserves_initialized sg (tmr_task_tick_source_client actor cut).
Proof.
  intros actor cut sg; apply tmr_task_fields_action_initialized_from_timer_frame.
  intros before after Hstep; symmetry.
  exact (proj2 (tmr_task_tick_cut_name_timer_frame sg cut before after Hstep)).
Qed.

Lemma tmr_task_event_ready_lifecycle_frame : forall sg before eid kind message result priority after,
  event_task_rdy sg before eid kind message result = Some (priority, after) ->
  after.(TskState).(taskLifecycle) = before.(TskState).(taskLifecycle) /\
  after.(EventState).(eventLifecycle) = before.(EventState).(eventLifecycle).
Proof.
  intros sg before eid kind message result priority after Hsource.
  unfold event_task_rdy in Hsource.
  destruct (before.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
  destruct (before.(TskState).(prioTbl) (event_wait_priority before.(TskState) event))
    as [| |selected]; try discriminate.
  destruct (before.(TskState).(inUsedTaskStates) selected) as [old|]; [|discriminate].
  injection Hsource as Hpriority Hafter; subst after; split; reflexivity.
Qed.

Lemma tmr_task_sem_post_lifecycle_frame : forall sg eid before result after,
  sem_post_critical sg eid before result after ->
  after.(TskState).(taskLifecycle) = before.(TskState).(taskLifecycle) /\
  after.(EventState).(eventLifecycle) = before.(EventState).(eventLifecycle).
Proof.
  intros sg eid before result after [event [_ Hsource]].
  destruct (Z.eqb (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
  - destruct Hsource as [fields [_ Hsource]].
    destruct (Z.ltb fields.(semCount) 65535); destruct Hsource as [_ ->]; split; reflexivity.
  - destruct Hsource as [_ [priority Hsource]].
    eapply tmr_task_event_ready_lifecycle_frame; exact Hsource.
Qed.

(** The actual Signal/Post source already has ordered NULL/type guards.
    Its validity and continuation guarantees come from the existing Sem
    body results. This producer needs no extra certificate premise. *)
Lemma tmr_task_tick_post_client_certificate : forall actor pointer result,
  KernelClientCertificate (tmr_task_tick_source_client actor (TmrTaskTickPost pointer result)).
Proof.
  intros actor pointer result; constructor.
  - intros sg before after Hvalid Hsource.
    exact (time_tick_post_call_preserves_state_inv sg pointer before result after Hsource Hvalid).
  - intros sg before after observer Hvalid Hsource Hforeign.
    change (time_tick_post_call sg pointer before result after) in Hsource.
    destruct Hsource as [state error Herror |
      state eid event error Hargument Hpointer Hlookup Htype |
      state eid event actual current Hargument Hpointer Hlookup Htype Hcritical]; try reflexivity.
    unfold task_creation_frame, task_creation_view.
    rewrite (proj1 (tmr_task_sem_post_lifecycle_frame sg eid state actual current Hcritical)); reflexivity.
  - intros sg before after observer origin Hvalid Hsource Hnormal Hactive.
    change (time_tick_post_call sg pointer before result after) in Hsource.
    eapply time_tick_post_call_preserves_invocation; eassumption.
  - intros sg before after observer Hvalid Hsource Hforeign.
    change (time_tick_post_call sg pointer before result after) in Hsource.
    destruct Hsource as [state error Herror |
      state eid event error Hargument Hpointer Hlookup Htype |
      state eid event actual current Hargument Hpointer Hlookup Htype Hcritical]; try reflexivity.
    unfold event_creation_frame, event_creation_view.
    rewrite (proj2 (tmr_task_sem_post_lifecycle_frame sg eid state actual current Hcritical)); reflexivity.
Qed.

Lemma tmr_task_event_broadcast_lifecycle_frame : forall sg eid kind message result before priorities after,
  event_broadcast sg eid kind message result before priorities after ->
  after.(TskState).(taskLifecycle) = before.(TskState).(taskLifecycle) /\
  after.(EventState).(eventLifecycle) = before.(EventState).(eventLifecycle).
Proof.
  intros sg eid kind message result before priorities after Hsource; induction Hsource.
  - split; reflexivity.
  - destruct (tmr_task_event_ready_lifecycle_frame sg s eid kind message result priority mid H1)
      as [Htask Hevent]. destruct IHHsource as [Htask' Hevent']; split; congruence.
Qed.

Lemma tmr_task_sem_abort_lifecycle_frame : forall sg eid opt before result after,
  event_pend_abort_critical sg eid PendSem opt before result after ->
  after.(TskState).(taskLifecycle) = before.(TskState).(taskLifecycle) /\
  after.(EventState).(eventLifecycle) = before.(EventState).(eventLifecycle).
Proof.
  intros sg eid opt before result after [event [_ Hsource]].
  destruct (Z.eqb (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
  - destruct Hsource as [_ ->]; split; reflexivity.
  - destruct (Z.eqb opt 1).
    + destruct Hsource as [priorities [Hsource _]].
      eapply tmr_task_event_broadcast_lifecycle_frame; exact Hsource.
    + destruct Hsource as [priority [Hsource _]].
      eapply tmr_task_event_ready_lifecycle_frame; exact Hsource.
Qed.

(** The typed Abort critical call is the actual post-type-check cut. Its
    type premise comes from that call's ordered source guard, not from a
    desired final invariant. opt keeps the C default-single-abort branch
    for EVERY value other than 1. No early-error API branch is changed. *)
Definition tmr_task_sem_abort_call_client (actor : option nat) eid opt
  (result : Z * (OSErrCode * bool)) : KernelClientAction :=
  {| kernel_client_actor := actor; kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after => exists event,
       before.(EventState).(inUsedEventStates) eid = Some event /\
       event.(eventType) = OS_EVENT_TYPE_SEM /\
       event_pend_abort_critical sg eid PendSem opt before result after |}.

Lemma tmr_task_sem_abort_call_certificate : forall actor eid opt result,
  KernelClientCertificate (tmr_task_sem_abort_call_client actor eid opt result).
Proof.
  intros actor eid opt result; constructor.
  - intros sg before after Hvalid [event [Hlookup [Htype Hsource]]].
    exact (proj1 (event_pend_abort_critical_preserves_resources sg before eid event PendSem opt result after
      Hvalid Hlookup ltac:(rewrite Htype; reflexivity) Hsource)).
  - intros sg before after observer Hvalid [event [Hlookup [Htype Hsource]]] Hforeign.
    unfold task_creation_frame, task_creation_view.
    rewrite (proj1 (tmr_task_sem_abort_lifecycle_frame sg eid opt before result after Hsource)); reflexivity.
  - intros sg before after observer origin Hvalid [event [Hlookup [Htype Hsource]]] Hnormal Hactive.
    eapply event_pend_abort_critical_preserves_invocation; try eassumption.
    rewrite Htype; reflexivity.
  - intros sg before after observer Hvalid [event [Hlookup [Htype Hsource]]] Hforeign.
    unfold event_creation_frame, event_creation_view.
    rewrite (proj2 (tmr_task_sem_abort_lifecycle_frame sg eid opt before result after Hsource)); reflexivity.
Qed.

Lemma tmr_task_sem_abort_call_preserves_initialized : forall actor eid opt result sg,
  tmr_task_fields_action_preserves_initialized sg (tmr_task_sem_abort_call_client actor eid opt result).
Proof.
  intros actor eid opt result sg; apply tmr_task_fields_action_initialized_from_timer_frame.
  intros before after [event [Hlookup [Htype Hsource]]]; symmetry.
  exact (proj2 (tmr_task_sem_abort_name_timer_frame sg eid opt before result after Hsource)).
Qed.

(** Source cuts already used by the selected C dispatcher but absent from
    the old seven-constructor Scheduler registry. Type errors and all
    actual return codes remain in the existing observation relations. *)
Inductive tmr_task_critical_source_client : KernelClientAction -> Prop :=
| TmrTaskCriticalMutexNoPend : forall actor eid,
    tmr_task_critical_source_client
      (CriticalComponent.mutex_del_no_pend_critical_call_client actor eid)
| TmrTaskCriticalMutexDelete : forall actor eid option,
    tmr_task_critical_source_client
      (CriticalComponent.mutex_del_critical_call_client actor eid option)
| TmrTaskCriticalChangePriority : forall actor requested priority,
    tmr_task_critical_source_client
      (CriticalComponent.task_change_prio_critical_call_client actor requested priority).

Lemma tmr_task_critical_source_client_preserves_initialized : forall action sg,
  tmr_task_critical_source_client action -> tmr_task_fields_action_preserves_initialized sg action.
Proof.
  intros action sg Hsource; apply tmr_task_fields_action_initialized_from_timer_frame.
  intros before after Hstep; destruct Hsource.
  - destruct Hstep as [_ [result [code [request [error [scheduled [Hcritical Hencoding]]]]]]].
    symmetry; exact (proj2 (CriticalComponent.mutex_del_critical_name_timer_frame
      sg eid 0 before (result, (error, scheduled)) after Hcritical)).
  - destruct Hstep as [result [code [request Hsource]]].
    symmetry; exact (proj2 (proj2 (CriticalComponent.mutex_del_critical_call_observation_fields
      sg eid option before result code request after Hsource))).
  - destruct Hstep as [_ [error Hsource]].
    symmetry; exact (proj2 (CriticalComponent.task_change_prio_critical_current_timer_frame
      sg requested priority before error after Hsource)).
Qed.

(** Ready-list preservation is derived from the actual source update and
    its existing resource certificate. It is not an endpoint premise of
    OSTmr_Task. In particular, a wake operation may change priorities or
    status, but it cannot remove an already runnable task. *)
Lemma tmr_task_runnable_preserves_ready : forall sg before after,
  UCOS2_state_inv sg before -> UCOS2_state_inv sg after ->
  mutex_del_preserves_runnable before after ->
  before.(SchedState).(readyList) <> [] -> after.(SchedState).(readyList) <> [].
Proof.
  intros sg before after Hvalid Hafter Hrunnable Hnonempty.
  destruct before.(SchedState).(readyList) as [|tid rest] eqn:Hlist; [contradiction|].
  pose proof (proj1 (proj1 (proj2 (proj2 Hvalid)))) as Hsched.
  destruct (proj1 Hsched tid ltac:(rewrite Hlist; left; reflexivity))
    as [node [Hnode [_ Hready]]].
  destruct (Hrunnable tid node Hnode Hready) as [current [Hcurrent Hready']].
  pose proof (proj1 (proj1 (proj2 (proj2 Hafter)))) as Hsched'.
  pose proof (proj1 (proj2 (proj2 Hsched')) _ _ Hcurrent Hready') as Hin.
  intro Hempty; rewrite Hempty in Hin; contradiction.
Qed.

Lemma tmr_task_client_runnable_preserves_ready : forall action,
  KernelClientCertificate action ->
  (forall sg before after, kernel_client_step action sg before after ->
    mutex_del_preserves_runnable before after) ->
  kernel_client_preserves_resources kernel_sched_ready_inv action.
Proof.
  intros action Hcertificate Hrunnable sg before after [Hvalid Hnonempty] Hstep.
  destruct (kernel_client_certificate_preserves_selected_resources action Hcertificate
    sg before after Hvalid Hstep) as [Hafter Hframes].
  split; [|exact Hframes]. split; [exact Hafter|].
  exact (tmr_task_runnable_preserves_ready sg before after Hvalid Hafter
    (Hrunnable sg before after Hstep) Hnonempty).
Qed.

Lemma tmr_task_updated_task_preserves_runnable : forall before after selected old updated,
  before.(TskState).(inUsedTaskStates) selected = Some old ->
  after.(TskState) = glob_task_set_usedtask before.(TskState) selected updated ->
  (is_effectively_ready old.(stat) old.(dly) = true ->
    is_effectively_ready updated.(stat) updated.(dly) = true) ->
  mutex_del_preserves_runnable before after.
Proof.
  intros before after selected old updated Hold Htasks Hupdate tid node Hnode Hready.
  rewrite Htasks; cbn [glob_task_set_usedtask inUsedTaskStates].
  destruct (Z.eqb tid selected) eqn:Heq.
  - apply Z.eqb_eq in Heq; subst tid. assert (node = old) by congruence; subst node.
    exists updated; split; [reflexivity|apply Hupdate; exact Hready].
  - exists node; split; assumption.
Qed.

Lemma tmr_task_tick_preserves_runnable : forall sg before selected old,
  before.(TskState).(inUsedTaskStates) selected = Some old ->
  mutex_del_preserves_runnable before (tick_task_step sg selected old before).
Proof.
  intros sg before selected old Hold.
  eapply tmr_task_updated_task_preserves_runnable; [exact Hold| |].
  - apply tick_task_step_task_state_eq; exact Hold.
  - apply SelectedIdleWakeStatus.tick_task_update_keeps_ready_task_ready.
Qed.

Lemma tmr_task_sem_post_preserves_runnable : forall sg eid before result after,
  sem_post_critical sg eid before result after -> mutex_del_preserves_runnable before after.
Proof.
  intros sg eid before result after [event [_ Hsource]].
  destruct (Z.eqb (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
  - destruct Hsource as [fields [_ Hsource]].
    destruct (Z.ltb fields.(semCount) 65535); destruct Hsource as [_ ->];
      intros tid old Hold Hready; exists old; split; assumption.
  - destruct Hsource as [_ [priority Hsource]].
    eapply mutex_del_wake_preserves_runnable; exact Hsource.
Qed.

Lemma tmr_task_sem_abort_preserves_runnable : forall sg eid opt before result after,
  event_pend_abort_critical sg eid PendSem opt before result after ->
  mutex_del_preserves_runnable before after.
Proof.
  intros sg eid opt before result after [event [_ Hsource]].
  destruct (Z.eqb (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
  - destruct Hsource as [_ ->]; apply mutex_del_preserves_runnable_refl.
  - destruct (Z.eqb opt 1).
    + destruct Hsource as [priorities [Hsource _]].
      eapply mutex_del_broadcast_preserves_runnable; exact Hsource.
    + destruct Hsource as [priority [Hsource _]].
      eapply mutex_del_wake_preserves_runnable; exact Hsource.
Qed.

Lemma tmr_task_delay_resume_preserves_runnable : forall sg priority before result after,
  time_delay_resume_critical sg priority before result after ->
  mutex_del_preserves_runnable before after.
Proof.
  intros sg priority before result after [_ Hsource].
  destruct (before.(TskState).(prioTbl) priority) as [| |selected].
  - destruct Hsource as [_ ->]; apply mutex_del_preserves_runnable_refl.
  - destruct Hsource as [_ ->]; apply mutex_del_preserves_runnable_refl.
  - destruct Hsource as [old [Hold Hsource]].
    destruct (Z.eqb old.(dly) 0) eqn:Hdelay; destruct Hsource as [_ ->].
    + apply mutex_del_preserves_runnable_refl.
    + eapply tmr_task_updated_task_preserves_runnable; [exact Hold|reflexivity|].
      intro Hready; unfold is_effectively_ready in Hready.
      destruct (Z.eqb (task_non_suspension_bits old.(stat)) 0); [|discriminate].
      rewrite Hdelay, Bool.andb_false_r in Hready; discriminate.
Qed.

Lemma tmr_task_sem_source_client_preserves_runnable : forall action sg before after,
  tmr_task_sem_source_client action -> kernel_client_step action sg before after ->
  mutex_del_preserves_runnable before after.
Proof.
  intros action sg before after Hsource; destruct Hsource; intro Hstep.
  - destruct Hstep as [old [Hold ->]]; apply tmr_task_tick_preserves_runnable; exact Hold.
  - destruct Hstep as [result Hstep]; eapply tmr_task_sem_post_preserves_runnable; exact Hstep.
  - destruct Hstep as [result Hstep]; eapply tmr_task_sem_abort_preserves_runnable; exact Hstep.
  - change (after = os_sched_save_current_sp before selected sp) in Hstep; subst after.
    unfold os_sched_save_current_sp.
    destruct (before.(TskState).(inUsedTaskStates) selected) as [old|] eqn:Hold.
    + eapply tmr_task_updated_task_preserves_runnable; [exact Hold|reflexivity|exact (fun H => H)].
    + intros tid node Hnode Hready; exists node; split; assumption.
  - destruct Hstep as [_ [result Hstep]]; eapply tmr_task_delay_resume_preserves_runnable; exact Hstep.
Qed.

Lemma tmr_task_tick_scan_preserves_runnable : forall sg visited before,
  mutex_del_preserves_runnable before (time_tick_scan sg before visited).
Proof.
  intros sg visited; induction visited as [|selected rest IH]; intros before.
  - apply mutex_del_preserves_runnable_refl.
  - change (mutex_del_preserves_runnable before
      (time_tick_scan sg (time_tick_visit sg before selected) rest)).
    eapply mutex_del_preserves_runnable_trans; [|apply IH].
    unfold time_tick_visit.
    destruct (before.(TskState).(inUsedTaskStates) selected) as [old|] eqn:Hold.
    + apply tmr_task_tick_preserves_runnable; exact Hold.
    + apply mutex_del_preserves_runnable_refl.
Qed.

Lemma tmr_task_tick_cut_preserves_runnable : forall sg cut before after,
  tmr_task_tick_cut_source sg cut before after -> mutex_del_preserves_runnable before after.
Proof.
  intros sg cut before after; destruct cut; cbn [tmr_task_tick_cut_source]; intro Hsource.
  - subst after; unfold time_tick_clock_step_state; destruct (tick_step_advance _ _);
      intros tid old Hold Hready; exists old; split; assumption.
  - subst after; unfold time_tick_serialized_after_hook.
    assert (Hclock : mutex_del_preserves_runnable before (time_tick_clock_step_state before)).
    { unfold time_tick_clock_step_state; destruct (tick_step_advance _ _);
        intros tid old Hold Hready; exists old; split; assumption. }
    destruct (time_tick_process_tasks before); [|exact Hclock].
    eapply mutex_del_preserves_runnable_trans; [exact Hclock|apply tmr_task_tick_scan_preserves_runnable].
  - destruct Hsource; try apply mutex_del_preserves_runnable_refl.
    eapply tmr_task_sem_post_preserves_runnable; eassumption.
Qed.

Lemma tmr_task_critical_source_client_preserves_runnable : forall action sg before after,
  tmr_task_critical_source_client action -> kernel_client_step action sg before after ->
  mutex_del_preserves_runnable before after.
Proof.
  intros action sg before after Hsource; destruct Hsource; intro Hstep.
  - destruct Hstep as [_ [result [code [request [error [scheduled [Hcritical Hencoding]]]]]]].
    eapply mutex_del_critical_preserves_runnable; exact Hcritical.
  - destruct Hstep as [result [code [request Hsource]]].
    destruct Hsource as [result code request checkpoint Hguard Hobservation|kind Htype Hnotmutex].
    + destruct Hobservation as [error [scheduled [Hcritical Hencoding]]].
      eapply mutex_del_critical_preserves_runnable; exact Hcritical.
    + apply mutex_del_preserves_runnable_refl.
  - destruct Hstep as [_ [error Hsource]].
    destruct (SelectedIdleCritical.task_change_prio_critical_idle_fields
      sg requested priority before error after Hsource) as [_ Hfields].
    intros tid old Hold Hready.
    destruct (Hfields tid old Hold) as [current [Hcurrent [_ [Hs Hd]]]].
    exists current; split; [exact Hcurrent|rewrite Hs, Hd; exact Hready].
Qed.

Lemma tmr_task_event_broadcast_preserves_current_consistency :
  forall sg eid kind message result before priorities after,
  event_broadcast sg eid kind message result before priorities after ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros sg eid kind message result before priorities after Hsource; induction Hsource; intro Hcurrent.
  - exact Hcurrent.
  - apply IHHsource; eapply event_task_rdy_preserves_current_consistency; eassumption.
Qed.

Lemma tmr_task_sem_post_preserves_current_consistency : forall sg eid before result after,
  sem_post_critical sg eid before result after ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros sg eid before result after [event [_ Hsource]] Hcurrent.
  destruct (Z.eqb (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
  - destruct Hsource as [fields [_ Hsource]].
    destruct (Z.ltb fields.(semCount) 65535); destruct Hsource as [_ ->]; exact Hcurrent.
  - destruct Hsource as [_ [priority Hsource]].
    eapply event_task_rdy_preserves_current_consistency; eassumption.
Qed.

Lemma tmr_task_sem_abort_preserves_current_consistency : forall sg eid opt before result after,
  event_pend_abort_critical sg eid PendSem opt before result after ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros sg eid opt before result after [event [_ Hsource]] Hcurrent.
  destruct (Z.eqb (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
  - destruct Hsource as [_ ->]; exact Hcurrent.
  - destruct (Z.eqb opt 1).
    + destruct Hsource as [priorities [Hsource _]].
      eapply tmr_task_event_broadcast_preserves_current_consistency; eassumption.
    + destruct Hsource as [priority [Hsource _]].
      eapply event_task_rdy_preserves_current_consistency; eassumption.
Qed.

Lemma tmr_task_sem_source_client_preserves_current_consistency : forall action sg before after,
  tmr_task_sem_source_client action -> kernel_client_step action sg before after ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros action sg before after Hsource; destruct Hsource; intros Hstep Hcurrent.
  - destruct Hstep as [old [Hold ->]]; eapply tick_task_step_preserves_current_consistency; eassumption.
  - destruct Hstep as [result Hstep]; eapply tmr_task_sem_post_preserves_current_consistency; eassumption.
  - destruct Hstep as [result Hstep]; eapply tmr_task_sem_abort_preserves_current_consistency; eassumption.
  - change (after = os_sched_save_current_sp before selected sp) in Hstep; subst after.
    unfold os_sched_save_current_sp.
    destruct (before.(TskState).(inUsedTaskStates) selected) as [old|] eqn:Hold.
    + eapply sched_current_consistency_update_task with (old := old)
        (updated := task_set_saved_sp old sp);
        [exact Hold|reflexivity|reflexivity|reflexivity|reflexivity|exact Hcurrent].
    + exact Hcurrent.
  - destruct Hstep as [_ [result [_ Hstep]]].
    destruct (before.(TskState).(prioTbl) priority) as [| |selected].
    + destruct Hstep as [_ ->]; exact Hcurrent.
    + destruct Hstep as [_ ->]; exact Hcurrent.
    + destruct Hstep as [old [Hold Hstep]].
      destruct (Z.eqb old.(dly) 0); destruct Hstep as [_ ->]; [exact Hcurrent|].
      destruct (sched_wake_by_status_current_cache_frame sg before.(TskState) before.(SchedState)
        selected (encode_task_status (sem_pend_delay_resume_task old).(stat))) as [Hid Hprio].
      eapply sched_current_consistency_update_task with (old := old)
        (updated := sem_pend_delay_resume_task old);
        [exact Hold|reflexivity|reflexivity|exact Hid|exact Hprio|exact Hcurrent].
Qed.

Lemma tmr_task_tick_cut_preserves_current_consistency : forall sg cut before after,
  tmr_task_tick_cut_source sg cut before after ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros sg cut before after; destruct cut; cbn [tmr_task_tick_cut_source]; intros Hsource Hcurrent.
  - subst after; unfold time_tick_clock_step_state; destruct (tick_step_advance _ _); exact Hcurrent.
  - subst after; apply time_tick_serialized_after_hook_preserves_current_consistency; exact Hcurrent.
  - destruct Hsource; try exact Hcurrent.
    eapply tmr_task_sem_post_preserves_current_consistency; eassumption.
Qed.

Lemma tmr_task_mutex_prepare_preserves_current_consistency : forall sg mutex before after,
  mutex_del_prepare sg mutex before after ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros sg mutex before after Hprepare Hcurrent; unfold mutex_del_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)); [subst; exact Hcurrent|].
  destruct mutex.(mfOwner) as [owner|].
  - destruct Hprepare as [node [priority [Hnode [_ ->]]]].
    unfold mutex_del_owner_priority_state; destruct Z.eq_dec; [exact Hcurrent|].
    apply mutex_del_relocated_preserves_current_consistency; exact Hcurrent.
  - subst; exact Hcurrent.
Qed.

Lemma tmr_task_mutex_delete_preserves_current_consistency : forall sg eid opt before result after,
  mutex_del_critical sg eid opt before result after ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros sg eid opt before result after [event [mutex [_ [_ [_ Hsource]]]]] Hcurrent.
  destruct (Z.eq_dec opt 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
    + destruct Hsource as [prepared [Hprepare [-> Hresult]]].
      change (sched_current_consistency prepared.(TskState) prepared.(SchedState)).
      eapply tmr_task_mutex_prepare_preserves_current_consistency; eassumption.
    + destruct Hsource as [-> Hresult]; exact Hcurrent.
  - destruct (Z.eq_dec opt 1).
    + destruct Hsource as [prepared [priorities [drained [Hprepare [Hbroadcast [-> Hresult]]]]]].
      change (sched_current_consistency drained.(TskState) drained.(SchedState)).
      eapply tmr_task_event_broadcast_preserves_current_consistency; [exact Hbroadcast|].
      eapply tmr_task_mutex_prepare_preserves_current_consistency; eassumption.
    + destruct Hsource as [-> Hresult]; exact Hcurrent.
Qed.

Lemma tmr_task_critical_source_client_preserves_current_consistency : forall action sg before after,
  tmr_task_critical_source_client action -> kernel_client_step action sg before after ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros action sg before after Hsource; destruct Hsource; intros Hstep Hcurrent.
  - destruct Hstep as [_ [result [code [request [error [scheduled [Hcritical Hencoding]]]]]]].
    eapply tmr_task_mutex_delete_preserves_current_consistency; eassumption.
  - destruct Hstep as [result [code [request Hsource]]].
    destruct Hsource as [result code request checkpoint Hguard Hobservation|kind Htype Hnotmutex].
    + destruct Hobservation as [error [scheduled [Hcritical Hencoding]]].
      eapply tmr_task_mutex_delete_preserves_current_consistency; eassumption.
    + exact Hcurrent.
  - destruct Hstep as [_ [error Hsource]].
    eapply task_change_prio_critical_preserves_current_consistency; eassumption.
Qed.

(** The actual selected Suspend body performs its Idle check after SELF
    resolution. It therefore uses the guarded source below, not the older
    KernelSourceTaskSuspend relation. Other existing Scheduler clients keep
    their original registration certificates. ChangePrio uses the actual
    API relation through TmrTaskCriticalChangePriority or the Scheduler
    ChangePrio constructor, not the older Sem projection relation. *)
Inductive tmr_task_nontimer_source_client : KernelClientAction -> Prop :=
| TmrTaskSourceTaskLifecycle : forall action,
    tmr_task_nontimer_source_client (task_creation_client action)
| TmrTaskSourceTaskStackPublication : forall publication,
    tmr_task_nontimer_source_client (task_create_stack_publication_client publication)
| TmrTaskSourceTaskBegin : forall origin,
    tmr_task_nontimer_source_client (task_create_begin_client origin)
| TmrTaskSourceTaskReserve : forall prio invocation origin,
    tmr_task_nontimer_source_client (task_create_reserve_client prio invocation origin)
| TmrTaskSourceTaskRollback : forall prio invocation,
    tmr_task_nontimer_source_client (task_create_rollback_client prio invocation)
| TmrTaskSourceEventAllocate : forall actor invocation,
    tmr_task_nontimer_source_client (event_create_allocate_client actor invocation)
| TmrTaskSourceEventStore : forall actor eid allocation field value,
    tmr_task_nontimer_source_client (event_create_private_store_client actor eid allocation field value)
| TmrTaskSourceEventPublish : forall actor eid allocation node,
    tmr_task_nontimer_source_client (event_create_publication_client actor eid allocation node)
| TmrTaskSourceQueueReserve : forall actor eid allocation free,
    tmr_task_nontimer_source_client (q_create_reserve_client actor eid allocation free)
| TmrTaskSourceQueuePublish : forall actor eid allocation qid start size slots name,
    tmr_task_nontimer_source_client (q_create_publication_client actor eid allocation qid start size slots name)
| TmrTaskSourceTaskResume : forall actor prio,
    tmr_task_nontimer_source_client (task_resume_critical_client actor prio)
| TmrTaskSourceSemAccept : forall invocation eid count,
    tmr_task_nontimer_source_client (sem_accept_critical_client invocation eid count).

Lemma tmr_task_nontimer_source_client_original : forall action,
  tmr_task_nontimer_source_client action -> kernel_nontimer_source_client action.
Proof. intros action Hsource; destruct Hsource; constructor. Qed.

Inductive tmr_task_scheduler_source_client external : KernelClientAction -> Prop :=
| TmrTaskSchedulerNontimer : forall action,
    tmr_task_nontimer_source_client action -> tmr_task_scheduler_source_client external action
| TmrTaskSchedulerProfile : forall cut,
    tmr_task_scheduler_source_client external (kernel_full_profile_cut_client cut)
| TmrTaskSchedulerChangePrio : forall actor requested priority,
    tmr_task_scheduler_source_client external (task_change_prio_critical_client actor requested priority)
| TmrTaskSchedulerFlagReady : forall actor pointer bits result,
    tmr_task_scheduler_source_client external (flag_task_rdy_source_client actor pointer bits result)
| TmrTaskSchedulerEventReady : forall actor eid kind message result,
    tmr_task_scheduler_source_client external (event_task_rdy_source_client actor eid kind message result)
| TmrTaskSchedulerTickTask : forall slot old,
    tmr_task_scheduler_source_client external (time_tick_task_source_client slot old)
| TmrTaskSchedulerTaskInstall : forall context outgoing incoming resumed,
    tmr_task_scheduler_source_client external (os_sched_install_client external context outgoing incoming resumed).

Lemma tmr_task_scheduler_source_client_original : forall external action,
  tmr_task_scheduler_source_client external action -> sched_task_source_client external action.
Proof.
  intros external action Hsource; destruct Hsource.
  - apply SchedTaskSourceNontimer; apply tmr_task_nontimer_source_client_original; exact H.
  - apply SchedTaskSourceProfile.
  - apply SchedTaskSourceChangePrio.
  - apply SchedTaskSourceFlagReady.
  - apply SchedTaskSourceEventReady.
  - apply SchedTaskSourceTickTask.
  - apply SchedTaskSourceTaskInstall.
Qed.

Lemma tmr_task_update_preserves_idle_non_idle : forall sg call before after selected old updated,
  before.(TskState).(inUsedTaskStates) selected = Some old ->
  after.(TskState) = glob_task_set_usedtask before.(TskState) selected updated ->
  updated.(taskGeneration) = old.(taskGeneration) -> updated.(curPrio) = old.(curPrio) ->
  (is_effectively_ready old.(stat) old.(dly) = true ->
    is_effectively_ready updated.(stat) updated.(dly) = true) ->
  (task_idle_ready sg before.(TskState) -> task_idle_ready sg after.(TskState)) /\
  (flag_pend_non_idle_at sg call before -> flag_pend_non_idle_at sg call after).
Proof.
  intros sg call before after selected old updated Hold Htasks Hg Hp Hready; split.
  - rewrite Htasks; eapply SelectedIdleFrames.task_update_ready_preserves_idle_ready; eassumption.
  - apply SelectedIdleFrames.task_used_priority_transport_non_idle; rewrite Htasks.
    eapply SelectedIdleFrames.task_update_used_priority_transport; eassumption.
Qed.

Lemma tmr_task_event_ready_preserves_idle_non_idle :
  forall sg call eid kind message result before priority after,
  event_task_rdy sg before eid kind message result = Some (priority, after) ->
  (task_idle_ready sg before.(TskState) -> task_idle_ready sg after.(TskState)) /\
  (flag_pend_non_idle_at sg call before -> flag_pend_non_idle_at sg call after).
Proof.
  intros sg call eid kind message result before priority after Hsource.
  unfold event_task_rdy in Hsource.
  destruct (before.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
  destruct (before.(TskState).(prioTbl) (event_wait_priority before.(TskState) event))
    as [| |selected]; try discriminate.
  destruct (before.(TskState).(inUsedTaskStates) selected) as [old|] eqn:Hold; [|discriminate].
  injection Hsource as Hpriority Hafter; subst after.
  eapply tmr_task_update_preserves_idle_non_idle;
    [exact Hold|reflexivity|reflexivity|reflexivity|].
  apply task_event_wake_single_keeps_ready_task_ready.
Qed.

Lemma tmr_task_event_broadcast_preserves_idle_non_idle :
  forall sg call eid kind message result before priorities after,
  event_broadcast sg eid kind message result before priorities after ->
  (task_idle_ready sg before.(TskState) -> task_idle_ready sg after.(TskState)) /\
  (flag_pend_non_idle_at sg call before -> flag_pend_non_idle_at sg call after).
Proof.
  intros sg call eid kind message result before priorities after Hsource; induction Hsource.
  - split; exact (fun H => H).
  - destruct (tmr_task_event_ready_preserves_idle_non_idle sg call eid kind message result s priority mid H1)
      as [Hidle Hnonidle]. destruct IHHsource as [Hidle' Hnonidle']; split; auto.
Qed.

Lemma tmr_task_tick_preserves_idle_non_idle : forall sg call before selected old,
  before.(TskState).(inUsedTaskStates) selected = Some old ->
  (task_idle_ready sg before.(TskState) ->
    task_idle_ready sg (tick_task_step sg selected old before).(TskState)) /\
  (flag_pend_non_idle_at sg call before ->
    flag_pend_non_idle_at sg call (tick_task_step sg selected old before)).
Proof.
  intros sg call before selected old Hold.
  eapply tmr_task_update_preserves_idle_non_idle; [exact Hold| | | |].
  - apply tick_task_step_task_state_eq; exact Hold.
  - unfold tick_task_update; destruct (Z.eqb old.(dly) 0); reflexivity.
  - unfold tick_task_update; destruct (Z.eqb old.(dly) 0); reflexivity.
  - apply SelectedIdleWakeStatus.tick_task_update_keeps_ready_task_ready.
Qed.

Lemma tmr_task_nontimer_source_preserves_idle_non_idle : forall action sg call before after,
  tmr_task_nontimer_source_client action -> UCOS2_state_inv sg before ->
  kernel_client_step action sg before after ->
  (task_idle_ready sg before.(TskState) -> task_idle_ready sg after.(TskState)) /\
  (flag_pend_non_idle_at sg call before -> flag_pend_non_idle_at sg call after).
Proof.
  intros action sg call before after Hsource Hvalid; destruct Hsource; intro Hstep.
  - destruct Hstep as [Hguard [_ ->]].
    destruct action as [priority entry slot rest image|priority entry allocation image|
      priority invocation node|invocation].
    + apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity.
    + apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity.
    + pose proof (task_commit_identity_private before.(TskState) priority invocation node
        (proj1 Hguard)) as Hprivate.
      pose proof (proj1 (task_private_excludes_public sg before.(TskState) node.(taskID)
        (proj1 (proj1 (proj2 Hvalid))) Hprivate)) as Hfresh.
      split.
      * apply task_commit_preserves_idle_ready; exact Hfresh.
      * apply SelectedIdleFrames.task_used_priority_transport_non_idle.
        apply SelectedIdleBuiltin.task_commit_used_priority_transport; exact Hfresh.
    + apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity.
  - eapply SelectedIdleBuiltin.task_create_stack_publication_idle_non_idle; eassumption.
  - destruct Hstep as [_ ->]; apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity.
  - destruct Hstep as [_ ->]; apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity.
  - destruct Hstep as [_ ->]; apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity.
  - destruct Hstep as [_ [result Hstep]]. unfold event_create_allocate_critical in Hstep.
    destruct before.(EventState).(unUsedEventStates).
    + destruct Hstep as [_ ->]; apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity.
    + destruct Hstep as [image [_ [_ ->]]]; apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity.
  - destruct Hstep as [_ ->]; apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity.
  - destruct Hstep as [_ [_ ->]]; apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity.
  - destruct Hstep as [_ [_ [_ [_ [result [a [Ha Hstep]]]]]]].
    destruct free; destruct Hstep as [_ ->]; apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity.
  - destruct Hstep as [_ [_ [_ [_ ->]]]]; apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity.
  - destruct Hstep as [_ [result [_ Hstep]]].
    destruct (before.(TskState).(prioTbl) prio) as [| |selected].
    + destruct Hstep as [_ ->]; split; exact (fun H => H).
    + destruct Hstep as [_ ->]; split; exact (fun H => H).
    + destruct Hstep as [old [Hold Hstep]].
      destruct (task_is_suspended old.(stat)) eqn:Hsusp; destruct Hstep as [_ ->].
      * eapply tmr_task_update_preserves_idle_non_idle;
          [exact Hold|reflexivity|reflexivity|reflexivity|].
        intro Hready; unfold is_effectively_ready in Hready.
        destruct (Z.eqb (task_non_suspension_bits old.(stat)) 0); [|discriminate].
        rewrite Hsusp in Hready; discriminate.
      * split; exact (fun H => H).
  - destruct Hstep as [event [_ [_ [node [fields [_ [_ [_ ->]]]]]]]].
    destruct (Z.ltb 0 fields.(semCount)); apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity.
Qed.

Lemma tmr_task_change_prio_preserves_idle_non_idle : forall sg call requested priority before code after,
  UCOS2_state_inv sg before -> UCOS2_state_inv sg after -> before.(SchedState).(isRunning) = true ->
  task_change_prio_critical sg requested priority before code after ->
  (task_idle_ready sg before.(TskState) -> task_idle_ready sg after.(TskState)) /\
  (flag_pend_non_idle_at sg call before -> flag_pend_non_idle_at sg call after).
Proof.
  intros sg call requested priority before code after Hvalid Hafter Hrunning Hsource.
  destruct (SelectedIdleCritical.task_change_prio_critical_idle_fields
    sg requested priority before code after Hsource) as [Hlife Hfields].
  eapply SelectedMutexIdle.running_active_order_preserves_idle_non_idle;
    [exact Hvalid|exact Hafter|exact Hrunning| |rewrite Hlife; reflexivity| |].
  - eapply task_change_prio_critical_running_eq; exact Hsource.
  - intros slot old Hold; destruct (Hfields slot old Hold) as [current [Hcurrent [Hg Hrest]]].
    exists current; split; assumption.
  - intros slot old Hold Hready.
    destruct (Hfields slot old Hold) as [current [Hcurrent [_ [Hs Hd]]]].
    exists current; split; [exact Hcurrent|rewrite Hs, Hd; exact Hready].
Qed.

Lemma tmr_task_scheduler_source_preserves_idle_non_idle : forall external action sg call before after,
  tmr_task_scheduler_source_client external action ->
  UCOS2_state_inv sg before -> UCOS2_state_inv sg after -> before.(SchedState).(isRunning) = true ->
  kernel_client_step action sg before after ->
  (task_idle_ready sg before.(TskState) -> task_idle_ready sg after.(TskState)) /\
  (flag_pend_non_idle_at sg call before -> flag_pend_non_idle_at sg call after).
Proof.
  intros external action sg call before after Hsource Hvalid Hafter Hrunning; destruct Hsource; intro Hstep.
  - eapply tmr_task_nontimer_source_preserves_idle_non_idle; eassumption.
  - destruct Hstep as [Hinput ->]; destruct cut as [|observed|slot node].
    + apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity.
    + apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity.
    + destruct Hinput as [_ Hnode].
      eapply tmr_task_update_preserves_idle_non_idle;
        [exact Hnode|reflexivity|reflexivity|reflexivity|exact (fun H => H)].
  - destruct Hstep as [code Hstep]; eapply tmr_task_change_prio_preserves_idle_non_idle; eassumption.
  - destruct Hstep as [schedule Hstep].
    destruct (flag_task_rdy_result _ _ _ _ _ _ _ Hstep)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]].
    eapply tmr_task_update_preserves_idle_non_idle;
      [exact Hold|reflexivity|reflexivity|reflexivity|].
    apply task_flag_wake_keeps_ready_task_ready.
  - destruct Hstep as [priority Hstep]. eapply tmr_task_event_ready_preserves_idle_non_idle; exact Hstep.
  - destruct Hstep as [Hnode ->]; apply tmr_task_tick_preserves_idle_non_idle; exact Hnode.
  - apply SelectedIdleFrames.task_used_map_eq_idle_non_idle.
    exact (proj1 (os_sched_install_client_state_frame external context outgoing incoming resumed sg before after Hstep)).
Qed.

Lemma tmr_task_sem_source_preserves_idle_non_idle : forall action sg call before after,
  tmr_task_sem_source_client action -> kernel_client_step action sg before after ->
  (task_idle_ready sg before.(TskState) -> task_idle_ready sg after.(TskState)) /\
  (flag_pend_non_idle_at sg call before -> flag_pend_non_idle_at sg call after).
Proof.
  intros action sg call before after Hsource; destruct Hsource; intro Hstep.
  - destruct Hstep as [old [Hold ->]]; apply tmr_task_tick_preserves_idle_non_idle; exact Hold.
  - destruct Hstep as [result [event [_ Hstep]]].
    destruct (Z.eqb (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
    + destruct Hstep as [fields [_ Hstep]]; destruct (Z.ltb fields.(semCount) 65535);
        destruct Hstep as [_ ->]; apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity.
    + destruct Hstep as [_ [priority Hstep]]; eapply tmr_task_event_ready_preserves_idle_non_idle; exact Hstep.
  - destruct Hstep as [result [event [_ Hstep]]].
    destruct (Z.eqb (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
    + destruct Hstep as [_ ->]; split; exact (fun H => H).
    + destruct (Z.eqb option 1).
      * destruct Hstep as [priorities [Hstep _]]. eapply tmr_task_event_broadcast_preserves_idle_non_idle; exact Hstep.
      * destruct Hstep as [priority [Hstep _]]. eapply tmr_task_event_ready_preserves_idle_non_idle; exact Hstep.
  - change (after = os_sched_save_current_sp before selected sp) in Hstep; subst after.
    unfold os_sched_save_current_sp; destruct (before.(TskState).(inUsedTaskStates) selected) as [old|] eqn:Hold.
    + eapply tmr_task_update_preserves_idle_non_idle;
        [exact Hold|reflexivity|reflexivity|reflexivity|exact (fun H => H)].
    + apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity.
  - destruct Hstep as [_ [result [_ Hstep]]]. destruct (before.(TskState).(prioTbl) priority) as [| |selected].
    + destruct Hstep as [_ ->]; split; exact (fun H => H).
    + destruct Hstep as [_ ->]; split; exact (fun H => H).
    + destruct Hstep as [old [Hold Hstep]]; destruct (Z.eqb old.(dly) 0) eqn:Hdelay;
        destruct Hstep as [_ ->]; [split; exact (fun H => H)|].
      eapply tmr_task_update_preserves_idle_non_idle;
        [exact Hold|reflexivity|reflexivity|reflexivity|].
      intro Hready; unfold is_effectively_ready in Hready.
      destruct (Z.eqb (task_non_suspension_bits old.(stat)) 0); [|discriminate].
      rewrite Hdelay, Bool.andb_false_r in Hready; discriminate.
Qed.

Lemma tmr_task_tick_scan_preserves_idle_non_idle : forall sg call visited before,
  (task_idle_ready sg before.(TskState) -> task_idle_ready sg (time_tick_scan sg before visited).(TskState)) /\
  (flag_pend_non_idle_at sg call before -> flag_pend_non_idle_at sg call (time_tick_scan sg before visited)).
Proof.
  intros sg call visited; induction visited as [|selected rest IH]; intros before.
  - split; exact (fun H => H).
  - change ((task_idle_ready sg before.(TskState) ->
      task_idle_ready sg (time_tick_scan sg (time_tick_visit sg before selected) rest).(TskState)) /\
      (flag_pend_non_idle_at sg call before ->
        flag_pend_non_idle_at sg call (time_tick_scan sg (time_tick_visit sg before selected) rest))).
    destruct (IH (time_tick_visit sg before selected)) as [Hidle Hnonidle].
    unfold time_tick_visit in *.
    destruct (before.(TskState).(inUsedTaskStates) selected) as [old|] eqn:Hold; [|split; assumption].
    destruct (tmr_task_tick_preserves_idle_non_idle sg call before selected old Hold) as [Hfirst Hfirst'];
      split; auto.
Qed.

Lemma tmr_task_tick_cut_preserves_idle_non_idle : forall sg call cut before after,
  tmr_task_tick_cut_source sg cut before after ->
  (task_idle_ready sg before.(TskState) -> task_idle_ready sg after.(TskState)) /\
  (flag_pend_non_idle_at sg call before -> flag_pend_non_idle_at sg call after).
Proof.
  intros sg call cut before after; destruct cut; cbn [tmr_task_tick_cut_source]; intro Hsource.
  - subst after; unfold time_tick_clock_step_state; destruct (tick_step_advance _ _);
      apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity.
  - subst after; unfold time_tick_serialized_after_hook.
    assert (Hclock : (task_idle_ready sg before.(TskState) ->
      task_idle_ready sg (time_tick_clock_step_state before).(TskState)) /\
      (flag_pend_non_idle_at sg call before ->
        flag_pend_non_idle_at sg call (time_tick_clock_step_state before))).
    { unfold time_tick_clock_step_state; destruct (tick_step_advance _ _);
        apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity. }
    destruct (time_tick_process_tasks before); [|exact Hclock].
    destruct (tmr_task_tick_scan_preserves_idle_non_idle sg call
      (removelast before.(TskState).(taskLifecycle).(taskActiveOrder))
      (time_tick_clock_step_state before)) as [Hidle Hnonidle].
    destruct Hclock; split; auto.
  - destruct Hsource as [state error Herror|state eid event error Hargument Hpointer Hlookup Htype|
      state eid event actual current Hargument Hpointer Hlookup Htype Hcritical];
      try (split; exact (fun H => H)).
    destruct Hcritical as [node [_ Hstep]].
    lazymatch type of Hstep with
    | (if ?condition then _ else _) => destruct condition in Hstep
    end.
    + destruct Hstep as [fields [_ Hstep]].
      lazymatch type of Hstep with
      | (if ?condition then _ else _) => destruct condition in Hstep
      end; destruct Hstep as [_ ->];
        apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity.
    + destruct Hstep as [_ [priority Hstep]].
      eapply tmr_task_event_ready_preserves_idle_non_idle; exact Hstep.
Qed.

Lemma tmr_task_event_broadcast_running_eq : forall sg eid kind message result before priorities after,
  event_broadcast sg eid kind message result before priorities after ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros sg eid kind message result before priorities after Hsource; induction Hsource; [reflexivity|].
  rewrite IHHsource; eapply event_task_rdy_running_eq; exact H1.
Qed.

Lemma tmr_task_mutex_delete_running_eq : forall sg eid opt before result after,
  mutex_del_critical sg eid opt before result after ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros sg eid opt before result after [event [mutex [_ [_ [_ Hsource]]]]].
  destruct (Z.eq_dec opt 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
    + destruct Hsource as [prepared [Hprepare [-> Hresult]]].
      change (prepared.(SchedState).(isRunning) = before.(SchedState).(isRunning)).
      eapply mutex_del_prepare_running_eq; exact Hprepare.
    + destruct Hsource as [-> Hresult]; reflexivity.
  - destruct (Z.eq_dec opt 1).
    + destruct Hsource as [prepared [priorities [drained [Hprepare [Hbroadcast [-> Hresult]]]]]].
      change (drained.(SchedState).(isRunning) = before.(SchedState).(isRunning)).
      rewrite (tmr_task_event_broadcast_running_eq _ _ _ _ _ _ _ _ Hbroadcast).
      eapply mutex_del_prepare_running_eq; exact Hprepare.
    + destruct Hsource as [-> Hresult]; reflexivity.
Qed.

Lemma tmr_task_mutex_delete_preserves_idle_non_idle : forall sg call eid opt before result after,
  UCOS2_state_inv sg before -> UCOS2_state_inv sg after -> before.(SchedState).(isRunning) = true ->
  mutex_del_critical sg eid opt before result after ->
  (task_idle_ready sg before.(TskState) -> task_idle_ready sg after.(TskState)) /\
  (flag_pend_non_idle_at sg call before -> flag_pend_non_idle_at sg call after).
Proof.
  intros sg call eid opt before result after Hvalid Hafter Hrunning Hsource.
  destruct (mutex_del_critical_call_fields_eq sg eid opt before result after Hsource)
    as [Hnodes [Hstacks [Hlife Hrest]]].
  eapply SelectedMutexIdle.running_active_order_preserves_idle_non_idle;
    [exact Hvalid|exact Hafter|exact Hrunning| |rewrite Hlife; reflexivity| |].
  - eapply tmr_task_mutex_delete_running_eq; exact Hsource.
  - intros slot old Hold; pose proof (Hnodes slot) as Hnode; rewrite Hold in Hnode.
    destruct (after.(TskState).(inUsedTaskStates) slot) as [current|] eqn:Hcurrent;
      cbn in Hnode; [|discriminate].
    exists current; split; [reflexivity|congruence].
  - eapply mutex_del_critical_preserves_runnable; exact Hsource.
Qed.

Lemma tmr_task_critical_source_preserves_idle_non_idle : forall action sg call before after,
  tmr_task_critical_source_client action ->
  UCOS2_state_inv sg before -> UCOS2_state_inv sg after -> before.(SchedState).(isRunning) = true ->
  kernel_client_step action sg before after ->
  (task_idle_ready sg before.(TskState) -> task_idle_ready sg after.(TskState)) /\
  (flag_pend_non_idle_at sg call before -> flag_pend_non_idle_at sg call after).
Proof.
  intros action sg call before after Hsource Hvalid Hafter Hrunning; destruct Hsource; intro Hstep.
  - destruct Hstep as [_ [result [code [request [error [scheduled [Hcritical Hencoding]]]]]]].
    eapply tmr_task_mutex_delete_preserves_idle_non_idle; eassumption.
  - destruct Hstep as [result [code [request Hsource]]].
    destruct Hsource as [result code request checkpoint Hguard Hobservation|kind Htype Hnotmutex].
    + destruct Hobservation as [error [scheduled [Hcritical Hencoding]]].
      eapply tmr_task_mutex_delete_preserves_idle_non_idle; eassumption.
    + split; exact (fun H => H).
  - destruct Hstep as [_ [error Hsource]]; eapply tmr_task_change_prio_preserves_idle_non_idle; eassumption.
Qed.

(** Pointwise transport of the four actual wait-registration fields.
    This retains the disabled Multi pointer, which the older Sem wait
    projection intentionally omitted. It is proved from each source body. *)
Definition tmr_task_clear_fields_transport before after : Prop :=
  forall slot old, before.(TskState).(inUsedTaskStates) slot = Some old ->
  flag_active_event_clear old -> old.(tcbFlagNode) = 0 ->
  exists current, after.(TskState).(inUsedTaskStates) slot = Some current /\
    flag_active_event_clear current /\ current.(tcbFlagNode) = 0.

Lemma tmr_task_clear_fields_transport_map_eq : forall before after,
  after.(TskState).(inUsedTaskStates) = before.(TskState).(inUsedTaskStates) ->
  tmr_task_clear_fields_transport before after.
Proof. intros before after Hmap slot old Hold Hclear Hflag; exists old; rewrite Hmap; auto. Qed.

Lemma tmr_task_clear_fields_transport_trans : forall before middle after,
  tmr_task_clear_fields_transport before middle -> tmr_task_clear_fields_transport middle after ->
  tmr_task_clear_fields_transport before after.
Proof.
  intros before middle after Hfirst Hsecond slot old Hold Hclear Hflag.
  destruct (Hfirst slot old Hold Hclear Hflag) as [node [Hnode [Hclear' Hflag']]].
  exact (Hsecond slot node Hnode Hclear' Hflag').
Qed.

Lemma tmr_task_update_preserves_clear : forall before after selected old updated,
  before.(TskState).(inUsedTaskStates) selected = Some old ->
  after.(TskState).(inUsedTaskStates) =
    (glob_task_set_usedtask before.(TskState) selected updated).(inUsedTaskStates) ->
  (flag_active_event_clear old -> old.(tcbFlagNode) = 0 ->
    flag_active_event_clear updated /\ updated.(tcbFlagNode) = 0) ->
  tmr_task_clear_fields_transport before after.
Proof.
  intros before after selected old updated Hold Htasks Hupdate slot node Hnode Hclear Hflag.
  rewrite Htasks; cbn [glob_task_set_usedtask inUsedTaskStates].
  destruct (Z.eqb slot selected) eqn:Heq.
  - apply Z.eqb_eq in Heq; subst slot. assert (node = old) by congruence; subst node.
    exists updated; split; [reflexivity|apply Hupdate; assumption].
  - exists node; auto.
Qed.

Lemma tmr_task_projected_source_preserves_clear : forall action sg before after,
  sem_pend_projected_source_client action -> kernel_client_step action sg before after ->
  tmr_task_clear_fields_transport before after.
Proof.
  intros action sg before after Hsource Hstep slot old Hold [Hevent [Hmulti Hpointer]] Hflag.
  destruct (sem_pend_source_client_projection action sg before after slot old Hsource Hstep Hold)
    as [current [Hcurrent Htrace]].
  assert (Hnone : sem_pend_task_unregistered old) by (repeat split; assumption).
  pose proof (sem_pend_wait_trace_preserves_unregistered old current Htrace Hnone)
    as [Hevent' [Hmulti' Hflag']].
  pose proof (tmr_task_source_client_multi_pointer action sg before after Hsource Hstep slot) as Hptr.
  rewrite Hcurrent, Hold in Hptr; cbn in Hptr.
  exists current; split; [exact Hcurrent|]. split; [|exact Hflag'].
  repeat split; congruence.
Qed.

Lemma tmr_task_creation_client_preserves_clear : forall action sg before after,
  UCOS2_state_inv sg before -> kernel_client_step (task_creation_client action) sg before after ->
  tmr_task_clear_fields_transport before after.
Proof.
  intros action sg before after Hvalid [Hguard [_ ->]].
  destruct action as [priority entry slot rest image|priority entry allocation image|
    priority invocation node|invocation].
  - apply tmr_task_clear_fields_transport_map_eq; reflexivity.
  - apply tmr_task_clear_fields_transport_map_eq; reflexivity.
  - pose proof (task_commit_identity_private before.(TskState) priority invocation node (proj1 Hguard)) as Hprivate.
    pose proof (proj1 (task_private_excludes_public sg before.(TskState) node.(taskID)
      (proj1 (proj1 (proj2 Hvalid))) Hprivate)) as Hfresh.
    intros slot old Hold [Hevent [Hmulti Hpointer]] Hflag.
    destruct (task_commit_transports_old_fields before.(TskState) priority invocation node slot old Hfresh Hold)
      as [current [Hcurrent Hfields]].
    exists current; split; [exact Hcurrent|].
    pose proof (f_equal eventPtr Hfields) as He.
    pose proof (f_equal eventMultiWaitEvents Hfields) as Hm.
    pose proof (f_equal tcbEventMultiPtr Hfields) as Hp.
    pose proof (f_equal tcbFlagNode Hfields) as Hf.
    cbn [task_set_links eventPtr eventMultiWaitEvents tcbEventMultiPtr tcbFlagNode] in He, Hm, Hp, Hf.
    unfold flag_active_event_clear; repeat split; congruence.
  - apply tmr_task_clear_fields_transport_map_eq; reflexivity.
Qed.

Lemma tmr_task_nontimer_source_preserves_clear : forall action sg before after,
  tmr_task_nontimer_source_client action -> UCOS2_state_inv sg before ->
  kernel_client_step action sg before after -> tmr_task_clear_fields_transport before after.
Proof.
  intros action sg before after Hsource Hvalid; destruct Hsource; intro Hstep.
  - eapply tmr_task_creation_client_preserves_clear; eassumption.
  - destruct (task_create_stack_publication_raw_projection sg publication before after Hstep) as [Hraw ->].
    change (tmr_task_clear_fields_transport before
      (task_create_stack_publication_raw_state sg publication before)).
    eapply tmr_task_creation_client_preserves_clear; eassumption.
  - destruct Hstep as [_ ->]; apply tmr_task_clear_fields_transport_map_eq; reflexivity.
  - destruct Hstep as [_ ->]; apply tmr_task_clear_fields_transport_map_eq; reflexivity.
  - destruct Hstep as [_ ->]; apply tmr_task_clear_fields_transport_map_eq; reflexivity.
  - destruct Hstep as [_ [result Hstep]]. unfold event_create_allocate_critical in Hstep.
    destruct before.(EventState).(unUsedEventStates).
    + destruct Hstep as [_ ->]; apply tmr_task_clear_fields_transport_map_eq; reflexivity.
    + destruct Hstep as [image [_ [_ ->]]]; apply tmr_task_clear_fields_transport_map_eq; reflexivity.
  - destruct Hstep as [_ ->]; apply tmr_task_clear_fields_transport_map_eq; reflexivity.
  - destruct Hstep as [_ [_ ->]]; apply tmr_task_clear_fields_transport_map_eq; reflexivity.
  - destruct Hstep as [_ [_ [_ [_ [result [a [Ha Hstep]]]]]]].
    destruct free; destruct Hstep as [_ ->]; apply tmr_task_clear_fields_transport_map_eq; reflexivity.
  - destruct Hstep as [_ [_ [_ [_ ->]]]]; apply tmr_task_clear_fields_transport_map_eq; reflexivity.
  - eapply tmr_task_projected_source_preserves_clear; [apply SemPendSourceResume|exact Hstep].
  - destruct Hstep as [event [_ [_ [node [fields [_ [_ [_ ->]]]]]]]].
    destruct (Z.ltb 0 fields.(semCount)); apply tmr_task_clear_fields_transport_map_eq; reflexivity.
Qed.

Lemma tmr_task_event_ready_preserves_clear : forall sg before eid kind message result priority after,
  event_task_rdy sg before eid kind message result = Some (priority, after) ->
  tmr_task_clear_fields_transport before after.
Proof.
  intros sg before eid kind message result priority after Hsource.
  unfold event_task_rdy in Hsource.
  destruct (before.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
  destruct (before.(TskState).(prioTbl) (event_wait_priority before.(TskState) event)) as [| |selected]; try discriminate.
  destruct (before.(TskState).(inUsedTaskStates) selected) as [old|] eqn:Hold; [|discriminate].
  injection Hsource as Hpriority Hafter; subst after.
  eapply tmr_task_update_preserves_clear; [exact Hold|reflexivity|].
  intros [Hevent [Hmulti Hpointer]] Hflag; unfold flag_active_event_clear; repeat split; assumption || reflexivity.
Qed.

Lemma tmr_task_event_broadcast_preserves_clear : forall sg eid kind message result before priorities after,
  event_broadcast sg eid kind message result before priorities after -> tmr_task_clear_fields_transport before after.
Proof.
  intros sg eid kind message result before priorities after Hsource; induction Hsource.
  - apply tmr_task_clear_fields_transport_map_eq; reflexivity.
  - eapply tmr_task_clear_fields_transport_trans; [|exact IHHsource].
    eapply tmr_task_event_ready_preserves_clear; eassumption.
Qed.

Lemma tmr_task_change_prio_preserves_clear : forall sg requested priority before code after,
  task_change_prio_critical sg requested priority before code after -> tmr_task_clear_fields_transport before after.
Proof.
  intros sg requested priority before code after Hsource; unfold task_change_prio_critical in Hsource.
  destruct (before.(TskState).(prioTbl) priority).
  - destruct Hsource as [selected [Hselection Hsource]]. unfold task_change_prio_selected_effect in Hsource.
    destruct (Z.eqb selected sg.(osLowestPrio)).
    + destruct Hsource as [_ ->]; apply tmr_task_clear_fields_transport_map_eq; reflexivity.
    + destruct (before.(TskState).(prioTbl) selected) as [| |slot].
      * destruct Hsource as [_ ->]; apply tmr_task_clear_fields_transport_map_eq; reflexivity.
      * destruct Hsource as [_ ->]; apply tmr_task_clear_fields_transport_map_eq; reflexivity.
      * destruct Hsource as [old [Hold [_ ->]]].
        eapply tmr_task_update_preserves_clear; [exact Hold|reflexivity|].
        intros Hclear Hflag; split; assumption.
  - destruct Hsource as [_ ->]; apply tmr_task_clear_fields_transport_map_eq; reflexivity.
  - destruct Hsource as [_ ->]; apply tmr_task_clear_fields_transport_map_eq; reflexivity.
Qed.

Lemma tmr_task_scheduler_source_preserves_clear : forall external action sg before after,
  tmr_task_scheduler_source_client external action -> UCOS2_state_inv sg before ->
  kernel_client_step action sg before after -> tmr_task_clear_fields_transport before after.
Proof.
  intros external action sg before after Hsource Hvalid; destruct Hsource; intro Hstep.
  - eapply tmr_task_nontimer_source_preserves_clear; eassumption.
  - destruct Hstep as [Hinput ->]; destruct cut as [|observed|slot node].
    + apply tmr_task_clear_fields_transport_map_eq; reflexivity.
    + apply tmr_task_clear_fields_transport_map_eq; reflexivity.
    + destruct Hinput as [_ Hnode]. eapply tmr_task_update_preserves_clear; [exact Hnode|reflexivity|].
      intros Hclear Hflag; split; assumption.
  - destruct Hstep as [code Hstep]; eapply tmr_task_change_prio_preserves_clear; exact Hstep.
  - destruct Hstep as [schedule Hstep].
    destruct (flag_task_rdy_result _ _ _ _ _ _ _ Hstep)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]].
    eapply tmr_task_update_preserves_clear; [exact Hold|reflexivity|].
    intros Hclear Hflag; split; [exact Hclear|reflexivity].
  - destruct Hstep as [priority Hstep]; eapply tmr_task_event_ready_preserves_clear; exact Hstep.
  - destruct Hstep as [Hold ->].
    eapply (tmr_task_projected_source_preserves_clear (sem_pend_tick_source_client slot) sg);
      [constructor|exists old; split; [exact Hold|reflexivity]].
  - eapply tmr_task_projected_source_preserves_clear; [apply SemPendSourceSchedulerInstall|exact Hstep].
Qed.

Lemma tmr_task_tick_scan_preserves_clear : forall sg visited before,
  tmr_task_clear_fields_transport before (time_tick_scan sg before visited).
Proof.
  intros sg visited; induction visited as [|selected rest IH]; intros before.
  - apply tmr_task_clear_fields_transport_map_eq; reflexivity.
  - change (tmr_task_clear_fields_transport before
      (time_tick_scan sg (time_tick_visit sg before selected) rest)).
    eapply tmr_task_clear_fields_transport_trans; [|apply IH].
    unfold time_tick_visit; destruct (before.(TskState).(inUsedTaskStates) selected) as [old|] eqn:Hold.
    + eapply (tmr_task_projected_source_preserves_clear (sem_pend_tick_source_client selected) sg);
        [constructor|exists old; split; [exact Hold|reflexivity]].
    + apply tmr_task_clear_fields_transport_map_eq; reflexivity.
Qed.

Lemma tmr_task_tick_cut_preserves_clear : forall sg cut before after,
  tmr_task_tick_cut_source sg cut before after -> tmr_task_clear_fields_transport before after.
Proof.
  intros sg cut before after; destruct cut; cbn [tmr_task_tick_cut_source]; intro Hsource.
  - subst after; unfold time_tick_clock_step_state; destruct (tick_step_advance _ _);
      apply tmr_task_clear_fields_transport_map_eq; reflexivity.
  - subst after; unfold time_tick_serialized_after_hook.
    assert (Hclock : tmr_task_clear_fields_transport before (time_tick_clock_step_state before)).
    { unfold time_tick_clock_step_state; destruct (tick_step_advance _ _);
        apply tmr_task_clear_fields_transport_map_eq; reflexivity. }
    destruct (time_tick_process_tasks before); [|exact Hclock].
    eapply tmr_task_clear_fields_transport_trans; [exact Hclock|apply tmr_task_tick_scan_preserves_clear].
  - destruct Hsource as [state error Herror|state eid event error Hargument Hpointer Hlookup Htype|
      state eid event actual current Hargument Hpointer Hlookup Htype Hcritical];
      try (apply tmr_task_clear_fields_transport_map_eq; reflexivity).
    destruct Hcritical as [node [_ Hstep]].
    lazymatch type of Hstep with
    | (if ?condition then _ else _) => destruct condition in Hstep
    end.
    + destruct Hstep as [fields [_ Hstep]].
      lazymatch type of Hstep with
      | (if ?condition then _ else _) => destruct condition in Hstep
      end; destruct Hstep as [_ ->];
        apply tmr_task_clear_fields_transport_map_eq; reflexivity.
    + destruct Hstep as [_ [priority Hstep]].
      eapply tmr_task_event_ready_preserves_clear; exact Hstep.
Qed.

Lemma tmr_task_mutex_prepare_preserves_clear : forall sg mutex before after,
  mutex_del_prepare sg mutex before after -> tmr_task_clear_fields_transport before after.
Proof.
  intros sg mutex before after Hprepare; unfold mutex_del_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis));
    [subst; apply tmr_task_clear_fields_transport_map_eq; reflexivity|].
  destruct mutex.(mfOwner) as [owner|].
  - destruct Hprepare as [node [priority [Hnode [_ ->]]]].
    unfold mutex_del_owner_priority_state; destruct Z.eq_dec.
    + apply tmr_task_clear_fields_transport_map_eq; reflexivity.
    + eapply tmr_task_update_preserves_clear; [exact Hnode|reflexivity|].
      intros Hclear Hflag; split; assumption.
  - subst; apply tmr_task_clear_fields_transport_map_eq; reflexivity.
Qed.

Lemma tmr_task_mutex_delete_preserves_clear : forall sg eid opt before result after,
  mutex_del_critical sg eid opt before result after -> tmr_task_clear_fields_transport before after.
Proof.
  intros sg eid opt before result after [event [mutex [_ [_ [_ Hsource]]]]].
  destruct (Z.eq_dec opt 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
    + destruct Hsource as [prepared [Hprepare [-> Hresult]]].
      change (tmr_task_clear_fields_transport before prepared).
      eapply tmr_task_mutex_prepare_preserves_clear; exact Hprepare.
    + destruct Hsource as [-> Hresult]; apply tmr_task_clear_fields_transport_map_eq; reflexivity.
  - destruct (Z.eq_dec opt 1).
    + destruct Hsource as [prepared [priorities [drained [Hprepare [Hbroadcast [-> Hresult]]]]]].
      change (tmr_task_clear_fields_transport before drained).
      eapply tmr_task_clear_fields_transport_trans.
      * eapply tmr_task_mutex_prepare_preserves_clear; exact Hprepare.
      * eapply tmr_task_event_broadcast_preserves_clear; exact Hbroadcast.
    + destruct Hsource as [-> Hresult]; apply tmr_task_clear_fields_transport_map_eq; reflexivity.
Qed.

Lemma tmr_task_critical_source_preserves_clear : forall action sg before after,
  tmr_task_critical_source_client action -> kernel_client_step action sg before after ->
  tmr_task_clear_fields_transport before after.
Proof.
  intros action sg before after Hsource; destruct Hsource; intro Hstep.
  - destruct Hstep as [_ [result [code [request [error [scheduled [Hcritical Hencoding]]]]]]].
    eapply tmr_task_mutex_delete_preserves_clear; exact Hcritical.
  - destruct Hstep as [result [code [request Hsource]]].
    destruct Hsource as [result code request checkpoint Hguard Hobservation|kind Htype Hnotmutex].
    + destruct Hobservation as [error [scheduled [Hcritical Hencoding]]].
      eapply tmr_task_mutex_delete_preserves_clear; exact Hcritical.
    + apply tmr_task_clear_fields_transport_map_eq; reflexivity.
  - destruct Hstep as [_ [error Hsource]]; eapply tmr_task_change_prio_preserves_clear; exact Hsource.
Qed.

(** Like TimerCall, this registers one completed actual critical call.
    Its Idle fact is supplied by the current source endpoint when the
    body is registered; it is not an all-future-entry assumption. *)
Definition tmr_task_suspend_call_client (actor : option nat) source_sg priority result
  (entry returned : UCOS2_Verify_State) : KernelClientAction :=
  {| kernel_client_actor := actor; kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       sg = source_sg /\ before = entry /\ after = returned /\
       task_suspend_argument_error sg priority = None /\
       task_suspend_idle_guard_critical sg priority before result after |}.

Lemma tmr_task_suspend_call_client_guarded : forall actor source_sg priority result entry returned sg before after,
  kernel_client_step (tmr_task_suspend_call_client actor source_sg priority result entry returned)
    sg before after ->
  kernel_client_step (task_suspend_idle_guard_client actor priority) sg before after.
Proof. intros * [_ [_ [_ [Hargument Hsource]]]]; split; [exact Hargument|exists result; exact Hsource]. Qed.

Lemma tmr_task_suspend_call_client_certificate : forall actor source_sg priority result entry returned,
  KernelClientCertificate (tmr_task_suspend_call_client actor source_sg priority result entry returned).
Proof.
  intros actor source_sg priority result entry returned.
  pose proof (task_suspend_idle_guard_client_certificate actor priority) as Hcertificate.
  constructor.
  - intros sg before after Hvalid Hstep.
    eapply kernel_client_preserves_validity; [exact Hcertificate|exact Hvalid|].
    eapply tmr_task_suspend_call_client_guarded; exact Hstep.
  - intros sg before after observer Hvalid Hstep Hforeign.
    eapply kernel_client_frames_creation; [exact Hcertificate|exact Hvalid| |exact Hforeign].
    eapply tmr_task_suspend_call_client_guarded; exact Hstep.
  - intros sg before after observer origin Hvalid Hstep Hnormal Hactive.
    eapply kernel_client_preserves_continuation; [exact Hcertificate|exact Hvalid| |exact Hnormal|exact Hactive].
    eapply tmr_task_suspend_call_client_guarded; exact Hstep.
  - intros sg before after observer Hvalid Hstep Hforeign.
    eapply kernel_client_frames_event_creation; [exact Hcertificate|exact Hvalid| |exact Hforeign].
    eapply tmr_task_suspend_call_client_guarded; exact Hstep.
Qed.

Lemma tmr_task_suspend_call_name_timer_frame : forall actor source_sg priority result entry returned sg before after,
  kernel_client_step (tmr_task_suspend_call_client actor source_sg priority result entry returned)
    sg before after ->
  before.(NameState) = after.(NameState) /\ before.(TimerState) = after.(TimerState).
Proof.
  intros * [_ [_ [_ [Hargument Hsource]]]].
  destruct (task_suspend_idle_guard_original_or_unchanged _ _ _ _ _ Hsource) as [->|Horiginal];
    [split; reflexivity|].
  assert (Hstep : kernel_client_step (task_suspend_critical_client actor priority) sg before after)
    by (split; [exact Hargument|exists result; exact Horiginal]).
  split.
  - unfold task_suspend_critical in Horiginal.
    destruct Horiginal as [cid [current [_ [_ [_ Hsource']]]]].
    destruct (before.(TskState).(prioTbl) (fst (task_suspend_selection sg priority current))).
    + destruct Hsource' as [_ ->]; reflexivity.
    + destruct Hsource' as [_ ->]; reflexivity.
    + destruct Hsource' as [node [_ [_ ->]]]; reflexivity.
  - symmetry; eapply kernel_nontimer_source_client_timer_state_eq; [constructor|exact Hstep].
Qed.

(** A new source-bound registry, selected at the new Task entry. Registered
    bodies retain the existing resource/name/ready certificates. The ready
    certificate was already part of Scheduler registration; the additional
    source families discharge it from their actual updates below. *)
Inductive tmr_task_source_client external : KernelClientAction -> Prop :=
| TmrTaskSourceScheduler : forall action,
    tmr_task_scheduler_source_client external action -> tmr_task_source_client external action
| TmrTaskSourceSem : forall action,
    tmr_task_sem_source_client action -> tmr_task_source_client external action
| TmrTaskSourceCritical : forall action,
    tmr_task_critical_source_client action -> tmr_task_source_client external action
| TmrTaskSourceTick : forall actor cut,
    tmr_task_source_client external (tmr_task_tick_source_client actor cut)
| TmrTaskSourceTimer : forall actor cut,
    tmr_task_source_client external (tmr_task_timer_source_client actor cut)
| TmrTaskSourceTimerCall : forall actor source_sg cut entry timers,
    tmr_task_source_client external (tmr_task_timer_call_client actor source_sg cut entry timers)
| TmrTaskSourceSemAbortCall : forall actor eid opt result,
    tmr_task_source_client external (tmr_task_sem_abort_call_client actor eid opt result)
| TmrTaskSourceSuspendCall : forall actor source_sg priority result entry returned,
    tmr_task_source_client external (tmr_task_suspend_call_client actor source_sg priority result entry returned).

Lemma tmr_task_source_client_preserves_initialized : forall external action sg,
  tmr_task_source_client external action -> tmr_task_fields_action_preserves_initialized sg action.
Proof.
  intros external action sg Hsource; destruct Hsource.
  - eapply tmr_task_fields_sched_source_preserves_initialized.
    apply tmr_task_scheduler_source_client_original; exact H.
  - apply tmr_task_sem_source_client_preserves_initialized; exact H.
  - apply tmr_task_critical_source_client_preserves_initialized; exact H.
  - apply tmr_task_tick_source_client_preserves_initialized.
  - apply tmr_task_timer_source_client_preserves_initialized.
  - intros before after Hstep Hinit.
    eapply tmr_task_timer_source_client_preserves_initialized.
    + eapply tmr_task_timer_call_client_source; exact Hstep.
    + exact Hinit.
  - apply tmr_task_sem_abort_call_preserves_initialized.
  - apply tmr_task_fields_action_initialized_from_timer_frame.
    intros before after Hstep; symmetry.
    exact (proj2 (tmr_task_suspend_call_name_timer_frame actor source_sg priority result entry returned
      sg before after Hstep)).
Qed.

Lemma tmr_task_source_client_preserves_current_consistency : forall external action sg before after,
  UCOS2_state_inv sg before ->
  tmr_task_source_client external action -> kernel_client_step action sg before after ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros external action sg before after Hvalid Hsource; destruct Hsource; intros Hstep Hcurrent.
  - eapply sched_task_source_client_preserves_current_consistency;
      [exact Hvalid|exact Hcurrent| |exact Hstep].
    apply tmr_task_scheduler_source_client_original; exact H.
  - eapply tmr_task_sem_source_client_preserves_current_consistency; eassumption.
  - eapply tmr_task_critical_source_client_preserves_current_consistency; eassumption.
  - exact (tmr_task_tick_cut_preserves_current_consistency sg cut before after Hstep Hcurrent).
  - destruct Hstep as [timers [_ ->]]; exact Hcurrent.
  - destruct Hstep as [_ [_ [_ ->]]]; exact Hcurrent.
  - destruct Hstep as [event [_ [_ Hcritical]]].
    eapply tmr_task_sem_abort_preserves_current_consistency; eassumption.
  - destruct Hstep as [_ [_ [_ [_ Hcritical]]]].
    destruct (task_suspend_idle_guard_original_or_unchanged _ _ _ _ _ Hcritical) as [->|Horiginal];
      [exact Hcurrent|].
    eapply task_suspend_critical_preserves_current_consistency; eassumption.
Qed.

Lemma tmr_task_source_client_running_eq : forall external action sg before after,
  UCOS2_state_inv sg before -> tmr_task_source_client external action ->
  kernel_client_step action sg before after ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros external action sg before after Hvalid Hsource; destruct Hsource; intro Hstep.
  - eapply sched_task_running_source_step_running_eq.
    eapply sched_task_source_client_running_step; [apply tmr_task_scheduler_source_client_original; exact H|exact Hstep].
  - exact (proj2 (sem_pend_source_client_call_frame action sg before after
      (tmr_task_sem_source_client_wait_projection action H) Hstep)).
  - destruct H; cbn in Hstep.
    + destruct Hstep as [_ [result [code [request [error [scheduled [Hcritical Hencoding]]]]]]].
      eapply tmr_task_mutex_delete_running_eq; exact Hcritical.
    + destruct Hstep as [result [code [request Hsource]]].
      destruct Hsource as [result code request checkpoint Hguard Hobservation|kind Htype Hnotmutex].
      * destruct Hobservation as [error [scheduled [Hcritical Hencoding]]].
        eapply tmr_task_mutex_delete_running_eq; exact Hcritical.
      * reflexivity.
    + destruct Hstep as [_ [error Hsource]]; eapply task_change_prio_critical_running_eq; exact Hsource.
  - change (tmr_task_tick_cut_source sg cut before after) in Hstep.
    destruct cut; cbn [tmr_task_tick_cut_source] in Hstep.
    + subst after; unfold time_tick_clock_step_state; destruct (tick_step_advance _ _); reflexivity.
    + subst after; apply time_tick_serialized_after_hook_running_eq.
    + exact (proj2 (proj2 (time_tick_post_call_state_frame sg pointer before result after Hstep Hvalid))).
  - destruct Hstep as [timers [_ ->]]; reflexivity.
  - destruct Hstep as [_ [_ [_ ->]]]; reflexivity.
  - destruct Hstep as [event [_ [_ Hcritical]]].
    destruct Hcritical as [node [_ Hsource]].
    lazymatch type of Hsource with
    | (if ?condition then _ else _) => destruct condition in Hsource
    end.
    + destruct Hsource as [_ ->]; reflexivity.
    + lazymatch type of Hsource with
      | (if ?condition then _ else _) => destruct condition in Hsource
      end.
      * destruct Hsource as [priorities [Hsource _]].
        eapply tmr_task_event_broadcast_running_eq; exact Hsource.
      * destruct Hsource as [priority [Hsource _]].
        eapply event_task_rdy_running_eq; exact Hsource.
  - destruct Hstep as [_ [_ [_ [_ Hcritical]]]].
    destruct (task_suspend_idle_guard_original_or_unchanged _ _ _ _ _ Hcritical) as [->|Horiginal];
      [reflexivity|]. eapply task_suspend_critical_running_eq; exact Horiginal.
Qed.

Lemma tmr_task_source_client_preserves_idle_non_idle : forall external action sg call before after,
  UCOS2_state_inv sg before -> UCOS2_state_inv sg after -> before.(SchedState).(isRunning) = true ->
  tmr_task_source_client external action -> kernel_client_step action sg before after ->
  (task_idle_ready sg before.(TskState) -> task_idle_ready sg after.(TskState)) /\
  (flag_pend_non_idle_at sg call before -> flag_pend_non_idle_at sg call after).
Proof.
  intros external action sg call before after Hvalid Hafter Hrunning Hsource; destruct Hsource; intro Hstep.
  - eapply tmr_task_scheduler_source_preserves_idle_non_idle; eassumption.
  - eapply tmr_task_sem_source_preserves_idle_non_idle; eassumption.
  - eapply tmr_task_critical_source_preserves_idle_non_idle; eassumption.
  - exact (tmr_task_tick_cut_preserves_idle_non_idle sg call cut before after Hstep).
  - destruct Hstep as [timers [_ ->]]; apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity.
  - destruct Hstep as [_ [_ [_ ->]]]; apply SelectedIdleFrames.task_used_map_eq_idle_non_idle; reflexivity.
  - destruct Hstep as [event [_ [_ Hcritical]]].
    destruct Hcritical as [node [_ Hsource]].
    lazymatch type of Hsource with
    | (if ?condition then _ else _) => destruct condition in Hsource
    end.
    + destruct Hsource as [_ ->]; split; exact (fun H => H).
    + lazymatch type of Hsource with
      | (if ?condition then _ else _) => destruct condition in Hsource
      end.
      * destruct Hsource as [priorities [Hsource _]].
        eapply tmr_task_event_broadcast_preserves_idle_non_idle; exact Hsource.
      * destruct Hsource as [priority [Hsource _]].
        eapply tmr_task_event_ready_preserves_idle_non_idle; exact Hsource.
  - destruct Hstep as [_ [_ [_ [_ Hcritical]]]]; split.
    + intros Hidle.
      exact (task_suspend_idle_guard_preserves_idle_ready sg priority before result after Hvalid Hidle Hcritical).
    + destruct (task_suspend_idle_guard_original_or_unchanged _ _ _ _ _ Hcritical) as [->|Horiginal];
        [exact (fun H => H)|].
      apply SelectedIdleFrames.task_used_priority_transport_non_idle.
      eapply SelectedIdleWakeStatus.kernel_status_c_source_used_priority_transport.
      econstructor; exact Horiginal.
Qed.

Lemma tmr_task_source_client_preserves_clear : forall external action sg before after,
  UCOS2_state_inv sg before -> tmr_task_source_client external action ->
  kernel_client_step action sg before after -> tmr_task_clear_fields_transport before after.
Proof.
  intros external action sg before after Hvalid Hsource; destruct Hsource; intro Hstep.
  - eapply tmr_task_scheduler_source_preserves_clear; eassumption.
  - eapply tmr_task_projected_source_preserves_clear;
      [apply tmr_task_sem_source_client_wait_projection; exact H|exact Hstep].
  - eapply tmr_task_critical_source_preserves_clear; eassumption.
  - exact (tmr_task_tick_cut_preserves_clear sg cut before after Hstep).
  - destruct Hstep as [timers [_ ->]]; apply tmr_task_clear_fields_transport_map_eq; reflexivity.
  - destruct Hstep as [_ [_ [_ ->]]]; apply tmr_task_clear_fields_transport_map_eq; reflexivity.
  - destruct Hstep as [event [_ [_ Hcritical]]].
    destruct Hcritical as [node [_ Hsource]].
    lazymatch type of Hsource with
    | (if ?condition then _ else _) => destruct condition in Hsource
    end.
    + destruct Hsource as [_ ->]; apply tmr_task_clear_fields_transport_map_eq; reflexivity.
    + lazymatch type of Hsource with
      | (if ?condition then _ else _) => destruct condition in Hsource
      end.
      * destruct Hsource as [priorities [Hsource _]].
        eapply tmr_task_event_broadcast_preserves_clear; exact Hsource.
      * destruct Hsource as [priority [Hsource _]].
        eapply tmr_task_event_ready_preserves_clear; exact Hsource.
  - destruct Hstep as [_ [_ [_ [Hargument Hcritical]]]].
    destruct (task_suspend_idle_guard_original_or_unchanged _ _ _ _ _ Hcritical) as [->|Horiginal];
      [apply tmr_task_clear_fields_transport_map_eq; reflexivity|].
    eapply (tmr_task_projected_source_preserves_clear (task_suspend_critical_client actor priority) sg);
      [constructor|split; [exact Hargument|exists result; exact Horiginal]].
Qed.

Definition tmr_task_registered_source_client external action : Prop :=
  tmr_task_source_client external action /\ KernelClientCertificate action /\
  (forall sg before after, kernel_client_step action sg before after ->
    before.(NameState) = after.(NameState)) /\
  kernel_client_preserves_resources kernel_sched_ready_inv action.

Definition tmr_task_source_region (external : OsSchedExternalResources) (resources : CriticalRegionResources)
  : CriticalRegionResources.
Proof.
  refine {| critical_region_outside_without_running := resources.(critical_region_outside_without_running);
            critical_region_outside_without_running_rep := resources.(critical_region_outside_without_running_rep);
            critical_region_inside := resources.(critical_region_inside);
            critical_region_clients := tmr_task_registered_source_client external |}.
  - intros action [_ [Hcertificate _]]; exact Hcertificate.
  - intros action [_ [_ [Hname _]]]; exact Hname.
Defined.

Lemma tmr_task_source_region_ready_clients : forall external resources,
  kernel_sched_ready_clients (tmr_task_source_region external resources).
Proof. intros external resources action [_ [_ [_ Hready]]]; exact Hready. Qed.

Lemma tmr_task_source_region_current_clients : forall external resources action,
  (tmr_task_source_region external resources).(critical_region_clients) action ->
  kernel_client_preserves_resources
    (fun sg state => UCOS2_state_inv sg state /\
      sched_current_consistency state.(TskState) state.(SchedState)) action.
Proof.
  intros external resources action [Hsource [Hcertificate Hrest]] sg before after [Hvalid Hcurrent] Hstep.
  destruct (kernel_client_certificate_preserves_selected_resources action Hcertificate
    sg before after Hvalid Hstep) as [Hafter Hframes].
  split; [|exact Hframes]. split; [exact Hafter|].
  exact (tmr_task_source_client_preserves_current_consistency external action sg before after
    Hvalid Hsource Hstep Hcurrent).
Qed.

Lemma tmr_task_source_region_idle_non_idle_clients : forall external resources call action,
  (tmr_task_source_region external resources).(critical_region_clients) action ->
  kernel_client_preserves_resources
    (fun sg state => UCOS2_state_inv sg state /\ state.(SchedState).(isRunning) = true /\
      task_idle_ready sg state.(TskState) /\ flag_pend_non_idle_at sg call state) action.
Proof.
  intros external resources call action [Hsource [Hcertificate Hrest]] sg before after
    [Hvalid [Hrunning [Hidle Hnonidle]]] Hstep.
  destruct (kernel_client_certificate_preserves_selected_resources action Hcertificate
    sg before after Hvalid Hstep) as [Hafter Hframes].
  destruct (tmr_task_source_client_preserves_idle_non_idle external action sg call before after
    Hvalid Hafter Hrunning Hsource Hstep) as [Hidle' Hnonidle'].
  split; [|exact Hframes]. split; [exact Hafter|]. split.
  - rewrite (tmr_task_source_client_running_eq external action sg before after Hvalid Hsource Hstep); exact Hrunning.
  - split; [apply Hidle'; exact Hidle|apply Hnonidle'; exact Hnonidle].
Qed.

Lemma tmr_task_source_region_clear_clients : forall external resources call action,
  (tmr_task_source_region external resources).(critical_region_clients) action ->
  kernel_client_preserves_resources
    (fun sg state => UCOS2_state_inv sg state /\
      exists node, state.(TskState).(inUsedTaskStates)
        call.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
        flag_active_event_clear node /\ node.(tcbFlagNode) = 0) action.
Proof.
  intros external resources call action [Hsource [Hcertificate Hrest]] sg before after
    [Hvalid [node [Hnode [Hclear Hflag]]]] Hstep.
  destruct (kernel_client_certificate_preserves_selected_resources action Hcertificate
    sg before after Hvalid Hstep) as [Hafter Hframes].
  split; [|exact Hframes]. split; [exact Hafter|].
  exact (tmr_task_source_client_preserves_clear external action sg before after
    Hvalid Hsource Hstep call.(os_sched_call_stack).(stackLeaseSlot) node Hnode Hclear Hflag).
Qed.

Lemma tmr_task_source_region_client_preserves_initialized : forall external resources sg action,
  (tmr_task_source_region external resources).(critical_region_clients) action ->
  tmr_task_fields_action_preserves_initialized sg action.
Proof.
  intros external resources sg action [Hsource Hresource].
  eapply tmr_task_source_client_preserves_initialized; exact Hsource.
Qed.

Lemma tmr_task_source_region_scheduler_registration : forall external resources action,
  tmr_task_scheduler_source_client external action ->
  sched_task_registered_client external action ->
  (tmr_task_source_region external resources).(critical_region_clients) action.
Proof.
  intros external resources action Hsource [_ [Hcertificate [Hname Hready]]].
  split; [apply TmrTaskSourceScheduler; exact Hsource|].
  split; [exact Hcertificate|]. split; assumption.
Qed.

Lemma tmr_task_source_region_sem_registration : forall external resources action,
  tmr_task_sem_source_client action -> KernelClientCertificate action ->
  (tmr_task_source_region external resources).(critical_region_clients) action.
Proof.
  intros external resources action Hsource Hcertificate.
  split; [apply TmrTaskSourceSem; exact Hsource|]. split; [exact Hcertificate|].
  split.
  - intros sg before after Hstep.
    exact (proj1 (tmr_task_sem_source_client_name_timer_frame action sg before after Hsource Hstep)).
  - apply tmr_task_client_runnable_preserves_ready; [exact Hcertificate|].
    intros; eapply tmr_task_sem_source_client_preserves_runnable; eassumption.
Qed.

Lemma tmr_task_source_region_timer_registration : forall external resources actor cut,
  KernelClientCertificate (tmr_task_timer_source_client actor cut) ->
  (tmr_task_source_region external resources).(critical_region_clients)
    (tmr_task_timer_source_client actor cut).
Proof.
  intros external resources actor cut Hcertificate.
  split; [apply TmrTaskSourceTimer|]. split; [exact Hcertificate|].
  split.
  - intros; eapply tmr_task_timer_source_client_name_frame; eassumption.
  - apply tmr_task_client_runnable_preserves_ready; [exact Hcertificate|].
    intros sg before after [timers [Hsource ->]] tid old Hold Hready.
    exists old; split; assumption.
Qed.

Lemma tmr_task_source_region_tick_registration : forall external resources actor cut,
  KernelClientCertificate (tmr_task_tick_source_client actor cut) ->
  (tmr_task_source_region external resources).(critical_region_clients)
    (tmr_task_tick_source_client actor cut).
Proof.
  intros external resources actor cut Hcertificate.
  split; [apply TmrTaskSourceTick|]. split; [exact Hcertificate|].
  split.
  - intros sg before after Hstep.
    exact (proj1 (tmr_task_tick_cut_name_timer_frame sg cut before after Hstep)).
  - apply tmr_task_client_runnable_preserves_ready; [exact Hcertificate|].
    intros sg before after Hstep.
    exact (tmr_task_tick_cut_preserves_runnable sg cut before after Hstep).
Qed.

Lemma tmr_task_source_region_critical_registration : forall external resources action,
  tmr_task_critical_source_client action ->
  (tmr_task_source_region external resources).(critical_region_clients) action.
Proof.
  intros external resources action Hsource.
  split; [apply TmrTaskSourceCritical; exact Hsource|].
  assert (Hcertificate : KernelClientCertificate action).
  { destruct Hsource.
    - apply CriticalComponent.mutex_del_no_pend_critical_call_client_certificate.
    - apply CriticalComponent.mutex_del_critical_call_client_certificate.
    - apply CriticalComponent.task_change_prio_critical_call_client_certificate. }
  split; [exact Hcertificate|]. split.
  - destruct Hsource.
    + apply CriticalComponent.mutex_del_no_pend_critical_call_client_name_frame.
    + apply CriticalComponent.mutex_del_critical_call_client_name_frame.
    + apply CriticalComponent.task_change_prio_critical_call_client_name_frame.
  - apply tmr_task_client_runnable_preserves_ready; [exact Hcertificate|].
    intros; eapply tmr_task_critical_source_client_preserves_runnable; eassumption.
Qed.

(** Actual closed C source endpoints construct registry membership AND
    their exact step. They are usable by a dispatcher from the beginning
    of this new route; neither theorem claims an old trace used this family. *)
Lemma tmr_task_source_region_timer_call : forall external resources actor sg cut entry timers,
  tmr_task_timer_cut_source sg cut entry.(TimerState) timers ->
  UCOS2_state_inv sg (replace_TimerS timers entry) ->
  (tmr_task_source_region external resources).(critical_region_clients)
    (tmr_task_timer_call_client actor sg cut entry timers) /\
  kernel_client_step (tmr_task_timer_call_client actor sg cut entry timers)
    sg entry (replace_TimerS timers entry).
Proof.
  intros external resources actor sg cut entry timers Hsource Hclosed; split.
  - split; [apply TmrTaskSourceTimerCall|]. split.
    + apply tmr_task_timer_call_client_certificate; exact Hclosed.
    + split.
      * intros actual_sg before after [_ [_ [_ ->]]]; reflexivity.
      * apply tmr_task_client_runnable_preserves_ready.
        -- apply tmr_task_timer_call_client_certificate; exact Hclosed.
        -- intros actual_sg before after [_ [_ [_ ->]]] tid old Hold Hready.
           exists old; split; assumption.
  - split; [reflexivity|]. split; [reflexivity|]. split; [exact Hsource|reflexivity].
Qed.

Lemma tmr_task_source_region_signal_post : forall external resources actor sg pointer result before after,
  time_tick_post_call sg pointer before result after ->
  (tmr_task_source_region external resources).(critical_region_clients)
    (tmr_task_tick_source_client actor (TmrTaskTickPost pointer result)) /\
  kernel_client_step (tmr_task_tick_source_client actor (TmrTaskTickPost pointer result))
    sg before after.
Proof.
  intros external resources actor sg pointer result before after Hsource; split.
  - apply tmr_task_source_region_tick_registration; apply tmr_task_tick_post_client_certificate.
  - exact Hsource.
Qed.

Lemma tmr_task_source_region_sem_abort_call : forall external resources actor sg eid opt result event before after,
  before.(EventState).(inUsedEventStates) eid = Some event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
  event_pend_abort_critical sg eid PendSem opt before result after ->
  (tmr_task_source_region external resources).(critical_region_clients)
    (tmr_task_sem_abort_call_client actor eid opt result) /\
  kernel_client_step (tmr_task_sem_abort_call_client actor eid opt result) sg before after.
Proof.
  intros external resources actor sg eid opt result event before after Hlookup Htype Hsource; split.
  - split; [apply TmrTaskSourceSemAbortCall|]. split; [apply tmr_task_sem_abort_call_certificate|].
    split.
    + intros actual_sg initial final [node [_ [_ Hcritical]]].
      exact (proj1 (tmr_task_sem_abort_name_timer_frame actual_sg eid opt initial result final Hcritical)).
    + apply tmr_task_client_runnable_preserves_ready; [apply tmr_task_sem_abort_call_certificate|].
      intros actual_sg initial final [node [_ [_ Hcritical]]].
      eapply tmr_task_sem_abort_preserves_runnable; exact Hcritical.
  - exists event; auto.
Qed.

Lemma tmr_task_source_region_suspend_call : forall external resources actor sg priority result before after,
  task_suspend_argument_error sg priority = None ->
  task_suspend_idle_guard_critical sg priority before result after ->
  task_idle_ready sg before.(TskState) ->
  (tmr_task_source_region external resources).(critical_region_clients)
    (tmr_task_suspend_call_client actor sg priority result before after) /\
  kernel_client_step (tmr_task_suspend_call_client actor sg priority result before after) sg before after.
Proof.
  intros external resources actor sg priority result before after Hargument Hsource Hidle; split.
  - split; [apply TmrTaskSourceSuspendCall|]. split; [apply tmr_task_suspend_call_client_certificate|]. split.
    + intros actual_sg initial final Hstep.
      exact (proj1 (tmr_task_suspend_call_name_timer_frame actor sg priority result before after
        actual_sg initial final Hstep)).
    + intros actual_sg initial final [Hvalid Hnonempty] Hstep.
      pose proof (kernel_client_certificate_preserves_selected_resources _
        (tmr_task_suspend_call_client_certificate actor sg priority result before after)
        actual_sg initial final Hvalid Hstep) as [Hafter Hframes].
      destruct Hstep as [-> [-> [-> [Hargument' Hsource']]]].
      split; [|exact Hframes]. split; [exact Hafter|].
      eapply sched_idle_ready_nonempty.
      * exact (proj1 (proj1 (proj2 (proj2 Hafter)))).
      * exact (task_suspend_idle_guard_preserves_idle_ready sg priority before result after
          Hvalid Hidle Hsource').
  - split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; assumption.
Qed.

Lemma tmr_task_suspend_call_preserves_idle : forall actor source_sg priority result entry returned sg before after,
  UCOS2_state_inv sg before -> task_idle_ready sg before.(TskState) ->
  kernel_client_step (tmr_task_suspend_call_client actor source_sg priority result entry returned)
    sg before after -> task_idle_ready sg after.(TskState).
Proof.
  intros * Hvalid Hidle [_ [_ [_ [_ Hsource]]]].
  eapply task_suspend_idle_guard_preserves_idle_ready; eassumption.
Qed.

Lemma tmr_task_source_region_trace_preserves_initialized :
  forall external resources sg observer event_observer before stopped after,
  kernel_client_resource_trace (tmr_task_source_region external resources).(critical_region_clients)
    sg observer event_observer before stopped after ->
  timer_api_initialized before.(TimerState) -> timer_api_initialized after.(TimerState).
Proof.
  intros external resources sg observer event_observer before stopped after Htrace Hinit.
  eapply tmr_task_fields_client_trace_preserves_initialized; [|exact Htrace|exact Hinit].
  intros action Hin; eapply tmr_task_source_region_client_preserves_initialized; exact Hin.
Qed.
