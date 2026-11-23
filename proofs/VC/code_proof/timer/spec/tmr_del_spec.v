Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.ucos2_timer_region.
Require Import Ucos2Verify.lib.kernel_execution.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Coq.micromega.Lia.
Require Export Ucos2Verify.VC.code.sched.spec.sched_lock_call_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_unlock_call_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_unlink_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_free_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_complement_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_no_schedule_spec.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_spec.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** These are source-derived facts for the already specified OSTimeTick
    client, including its supported hook/post sequence.  They are NOT a
    complete ISR/Timer environment or a permission to open a region. *)
Lemma tmr_del_tick_scan_intr_timer_eq : forall sg visited initial,
  (time_tick_scan sg initial visited).(IntrState) = initial.(IntrState) /\
  (time_tick_scan sg initial visited).(TimerState) = initial.(TimerState).
Proof.
  intros sg visited; induction visited as [|tid rest IH]; intro initial.
  - split; reflexivity.
  - change ((time_tick_scan sg (time_tick_visit sg initial tid) rest).(IntrState) =
      initial.(IntrState) /\
      (time_tick_scan sg (time_tick_visit sg initial tid) rest).(TimerState) =
      initial.(TimerState)).
    destruct (IH (time_tick_visit sg initial tid)) as [Hintr Htimer].
    rewrite Hintr, Htimer; unfold time_tick_visit.
    destruct (initial.(TskState).(inUsedTaskStates) tid) as [node|];
      [|split; reflexivity].
    pose proof (tick_task_step_non_task_sched_state_eq sg tid node initial) as Hframe.
    split; [exact (f_equal IntrState Hframe)|exact (f_equal TimerState Hframe)].
Qed.

Lemma tmr_del_tick_serialized_intr_timer_eq : forall sg initial,
  (time_tick_serialized_after_hook sg initial).(IntrState) = initial.(IntrState) /\
  (time_tick_serialized_after_hook sg initial).(TimerState) = initial.(TimerState).
Proof.
  intros sg initial; unfold time_tick_serialized_after_hook.
  destruct (time_tick_process_tasks initial).
  - destruct (tmr_del_tick_scan_intr_timer_eq sg
      (removelast initial.(TskState).(taskLifecycle).(taskActiveOrder))
      (time_tick_clock_step_state initial)) as [Hintr Htimer].
    rewrite Hintr, Htimer; split; reflexivity.
  - split; reflexivity.
Qed.

Lemma tmr_del_tick_call_intr_timer_eq : forall app sg value counter initial result final,
  time_tick_sem app sg value counter initial result final ->
  UCOS2_state_inv sg initial ->
  final.(IntrState) = initial.(IntrState) /\ final.(TimerState) = initial.(TimerState).
Proof.
  intros app sg value counter initial result final
    [_ [value_after [counter_after [hook [Hhook ->]]]]] Hvalid.
  destruct (tmr_del_tick_serialized_intr_timer_eq sg hook) as [Hintr Htimer].
  rewrite Hintr, Htimer.
  eapply time_tick_hook_result_intr_timer_eq; eassumption.
Qed.

Lemma tmr_del_tick_scan_preserves_invocation : forall sg visited initial invocation origin,
  task_invocation_active initial.(TskState) invocation origin ->
  task_invocation_active (time_tick_scan sg initial visited).(TskState) invocation origin.
Proof.
  intros sg visited; induction visited as [|tid rest IH];
    intros initial invocation origin Hactive; [exact Hactive|].
  change (task_invocation_active
    (time_tick_scan sg (time_tick_visit sg initial tid) rest).(TskState) invocation origin).
  apply IH; unfold time_tick_visit.
  destruct (initial.(TskState).(inUsedTaskStates) tid) as [node|] eqn:Hnode;
    [|exact Hactive].
  rewrite tick_task_step_task_state_eq by exact Hnode.
  eapply glob_task_set_usedtask_preserves_invocation_active;
    [exact Hnode| |exact Hactive].
  unfold tick_task_update; destruct (Z.eqb node.(dly) 0); reflexivity.
Qed.

Lemma tmr_del_tick_posts_running_eq : forall sg initial log final,
  time_tick_application_posts sg initial log final -> UCOS2_state_inv sg initial ->
  final.(SchedState).(isRunning) = initial.(SchedState).(isRunning).
Proof.
  intros sg initial log final Hposts; induction Hposts; intro Hvalid; [reflexivity|].
  rewrite (IHHposts (time_tick_post_call_preserves_state_inv sg pointer s result middle H Hvalid)).
  exact (proj2 (proj2 (time_tick_post_call_state_frame sg pointer s result middle H Hvalid))).
Qed.

Lemma tmr_del_tick_hook_running_eq : forall app sg value counter initial
  value_after counter_after final,
  time_tick_hook_result app sg value counter initial value_after counter_after final ->
  UCOS2_state_inv sg initial ->
  final.(SchedState).(isRunning) = initial.(SchedState).(isRunning).
Proof.
  intros app sg value counter initial value_after counter_after final
    [log [middle [_ [Hposts [_ Hsignal]]]]] Hvalid.
  pose proof (tmr_del_tick_posts_running_eq sg initial log middle Hposts Hvalid) as Hrunning.
  destruct (snd (time_tick_hook_counter_step counter)); [|subst final; exact Hrunning].
  destruct Hsignal as [result Hcall].
  pose proof (time_tick_application_posts_preserves_state_inv sg initial log middle Hposts Hvalid)
    as Hmiddle.
  rewrite (proj2 (proj2 (time_tick_post_call_state_frame sg middle.(TimerState).(timerSignalSem)
    middle result final Hcall Hmiddle))); exact Hrunning.
Qed.

Lemma tmr_del_tick_call_running_eq : forall app sg value counter initial result final,
  time_tick_sem app sg value counter initial result final -> UCOS2_state_inv sg initial ->
  final.(SchedState).(isRunning) = initial.(SchedState).(isRunning).
Proof.
  intros app sg value counter initial result final
    [_ [value_after [counter_after [hook [Hhook ->]]]]] Hvalid.
  unfold time_tick_serialized_after_hook.
  destruct (time_tick_process_tasks hook).
  - rewrite time_tick_scan_running_eq.
    change (hook.(SchedState).(isRunning) = initial.(SchedState).(isRunning)).
    eapply tmr_del_tick_hook_running_eq; eassumption.
  - change (hook.(SchedState).(isRunning) = initial.(SchedState).(isRunning)).
    eapply tmr_del_tick_hook_running_eq; eassumption.
Qed.

Lemma tmr_del_tick_serialized_preserves_invocation : forall sg initial invocation origin,
  task_invocation_active initial.(TskState) invocation origin ->
  task_invocation_active (time_tick_serialized_after_hook sg initial).(TskState)
    invocation origin.
Proof.
  intros sg initial invocation origin Hactive; unfold time_tick_serialized_after_hook.
  destruct (time_tick_process_tasks initial);
    [apply tmr_del_tick_scan_preserves_invocation|]; exact Hactive.
Qed.

Lemma tmr_del_tick_call_preserves_invocation : forall app sg value counter initial result final
  invocation origin,
  time_tick_sem app sg value counter initial result final -> UCOS2_state_inv sg initial ->
  task_invocation_active initial.(TskState) invocation origin ->
  task_invocation_active final.(TskState) invocation origin.
Proof.
  intros app sg value counter initial result final invocation origin
    [_ [value_after [counter_after [hook [Hhook ->]]]]] Hvalid Hactive.
  apply tmr_del_tick_serialized_preserves_invocation.
  eapply time_tick_hook_result_preserves_invocation; eassumption.
Qed.

Lemma tmr_del_tick_post_event_lifecycle_eq : forall sg pointer initial result final,
  time_tick_post_call sg pointer initial result final -> UCOS2_state_inv sg initial ->
  final.(EventState).(eventLifecycle) = initial.(EventState).(eventLifecycle).
Proof.
  intros sg pointer initial result final Hcall Hvalid; destruct Hcall;
    try reflexivity.
  assert (Hkind := time_tick_post_type_none e H2).
  destruct H3 as [node [Hnode Hstep]].
  assert (node = e) by congruence; subst node.
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0) eqn:Hempty.
  - destruct Hstep as [fields [Hfields Hstep]].
    destruct (Z.ltb fields.(semCount) 65535); destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [_ [priority Hstep]]; apply Z.eqb_neq in Hempty.
    assert (Hpend : event_type_to_pend_type e.(eventType) = Some PendSem)
      by (rewrite Hkind; reflexivity).
    destruct (event_wake_decompose sg s eid e PendSem 0 PendOK priority after
      Hvalid H1 Hpend Hempty Hstep)
      as [head [tail [old [_ [_ [_ [-> _]]]]]]].
    reflexivity.
Qed.

Lemma tmr_del_tick_posts_lifecycle_eq : forall sg initial log final,
  time_tick_application_posts sg initial log final -> UCOS2_state_inv sg initial ->
  final.(TskState).(taskLifecycle) = initial.(TskState).(taskLifecycle) /\
  final.(EventState).(eventLifecycle) = initial.(EventState).(eventLifecycle).
Proof.
  intros sg initial log final Hposts; induction Hposts; intro Hvalid;
    [split; reflexivity|].
  pose proof (time_tick_post_call_preserves_state_inv sg pointer s result middle H Hvalid)
    as Hmiddle.
  destruct (IHHposts Hmiddle) as [Htask Hevent].
  rewrite Htask, Hevent; split.
  - exact (proj1 (proj2 (time_tick_post_call_state_frame sg pointer s result middle H Hvalid))).
  - eapply tmr_del_tick_post_event_lifecycle_eq; eassumption.
Qed.

Lemma tmr_del_tick_hook_lifecycle_eq : forall app sg value counter initial
  value_after counter_after final,
  time_tick_hook_result app sg value counter initial value_after counter_after final ->
  UCOS2_state_inv sg initial ->
  final.(TskState).(taskLifecycle) = initial.(TskState).(taskLifecycle) /\
  final.(EventState).(eventLifecycle) = initial.(EventState).(eventLifecycle).
Proof.
  intros app sg value counter initial value_after counter_after final
    [log [middle [_ [Hposts [_ Hsignal]]]]] Hvalid.
  destruct (tmr_del_tick_posts_lifecycle_eq sg initial log middle Hposts Hvalid)
    as [Htask Hevent].
  destruct (snd (time_tick_hook_counter_step counter));
    [|subst final; split; assumption].
  destruct Hsignal as [result Hcall].
  pose proof (time_tick_application_posts_preserves_state_inv sg initial log middle Hposts Hvalid)
    as Hmiddle.
  destruct (proj2 (time_tick_post_call_state_frame sg middle.(TimerState).(timerSignalSem)
    middle result final Hcall Hmiddle)) as [Htask_final Hrunning].
  pose proof (tmr_del_tick_post_event_lifecycle_eq sg middle.(TimerState).(timerSignalSem)
    middle result final Hcall Hmiddle) as Hevent_final.
  split; congruence.
Qed.

Lemma tmr_del_tick_scan_event_state_eq : forall sg visited initial,
  (time_tick_scan sg initial visited).(EventState) = initial.(EventState).
Proof.
  intros sg visited; induction visited as [|tid rest IH]; intro initial;
    [reflexivity|].
  change ((time_tick_scan sg (time_tick_visit sg initial tid) rest).(EventState) =
    initial.(EventState)).
  rewrite IH; unfold time_tick_visit.
  destruct (initial.(TskState).(inUsedTaskStates) tid) as [node|]; [|reflexivity].
  exact (f_equal EventState (tick_task_step_non_task_sched_state_eq sg tid node initial)).
Qed.

Lemma tmr_del_tick_serialized_lifecycle_eq : forall sg initial,
  (time_tick_serialized_after_hook sg initial).(TskState).(taskLifecycle) =
    initial.(TskState).(taskLifecycle) /\
  (time_tick_serialized_after_hook sg initial).(EventState).(eventLifecycle) =
    initial.(EventState).(eventLifecycle).
Proof.
  intros sg initial; unfold time_tick_serialized_after_hook.
  destruct (time_tick_process_tasks initial).
  - rewrite time_tick_scan_task_lifecycle_eq, tmr_del_tick_scan_event_state_eq;
      split; reflexivity.
  - split; reflexivity.
Qed.

Lemma tmr_del_tick_call_lifecycle_eq : forall app sg value counter initial result final,
  time_tick_sem app sg value counter initial result final -> UCOS2_state_inv sg initial ->
  final.(TskState).(taskLifecycle) = initial.(TskState).(taskLifecycle) /\
  final.(EventState).(eventLifecycle) = initial.(EventState).(eventLifecycle).
Proof.
  intros app sg value counter initial result final
    [_ [value_after [counter_after [hook [Hhook ->]]]]] Hvalid.
  destruct (tmr_del_tick_serialized_lifecycle_eq sg hook) as [Htask Hevent].
  rewrite Htask, Hevent; eapply tmr_del_tick_hook_lifecycle_eq; eassumption.
Qed.

(** Embed the already specified, ordinary-return OSTimeTick call in the
    region client interface.  Eligibility is its actual ISR entry predicate,
    not a post-state Timer-equality filter.  The certificate below discharges
    the shared obligations from the source relation.  This one client is
    not the complete Timer environment and grants no heap-opening rule. *)
Definition tmr_del_tick_client (app : TimeTickApplicationResources)
  (value counter : Z) (invocation : nat) (origin : TaskInvocationOrigin) : KernelClientAction :=
  {| kernel_client_actor := None;
     kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg initial final =>
       time_tick_entry sg invocation origin initial /\
       time_tick_sem app sg value counter initial tt final |}.

Lemma tmr_del_tick_client_certificate : forall app value counter invocation origin,
  KernelClientCertificate (tmr_del_tick_client app value counter invocation origin).
Proof.
  intros app value counter invocation origin; constructor.
  - intros sg initial final Hvalid [Hentry Hcall].
    eapply time_tick_sem_preserves_state_inv; [|exact Hvalid|exact Hcall].
    destruct Hentry as [Hprofile _]; rewrite Hprofile; reflexivity.
  - intros sg initial final observer Hvalid [Hentry Hcall] Hforeign.
    destruct (tmr_del_tick_call_lifecycle_eq app sg value counter initial tt final Hcall Hvalid)
      as [Htask Hevent].
    unfold task_creation_frame, task_creation_view; rewrite Htask; reflexivity.
  - intros sg initial final observer observer_origin Hvalid [Hentry Hcall] Hnormal Hactive.
    eapply tmr_del_tick_call_preserves_invocation; eassumption.
  - intros sg initial final observer Hvalid [Hentry Hcall] Hforeign.
    destruct (tmr_del_tick_call_lifecycle_eq app sg value counter initial tt final Hcall Hvalid)
      as [Htask Hevent].
    unfold event_creation_frame, event_creation_view; rewrite Hevent; reflexivity.
Qed.

(** OSIntEnter is a second concrete client of the unlocked interval.  Its
    source body only observes OSRunning and updates IntrState; it does not
    touch TimerState, task lifecycle, or EventState.  The observation is
    retained in the action guard instead of being replaced by an implicit
    task-context assumption. *)
Definition tmr_del_int_enter_state (entry : UCOS2_Verify_State) : UCOS2_Verify_State :=
  replace_IntrS
    (interrupt_enter_state entry.(SchedState).(isRunning) entry.(IntrState))
    entry.

Lemma tmr_del_int_enter_preserves_validity : forall sg entry,
  UCOS2_state_inv sg entry ->
  UCOS2_state_inv sg (tmr_del_int_enter_state entry).
Proof. intros sg entry Hvalid; exact Hvalid. Qed.

Definition tmr_del_int_enter_client (observed : bool) : KernelClientAction :=
  {| kernel_client_actor := None;
     kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       before.(SchedState).(isRunning) = observed /\
       after = tmr_del_int_enter_state before |}.

Lemma tmr_del_int_enter_client_certificate : forall observed,
  KernelClientCertificate (tmr_del_int_enter_client observed).
Proof.
  intros observed; constructor.
  - intros sg before after Hvalid [Hobserved ->].
    apply tmr_del_int_enter_preserves_validity; exact Hvalid.
  - intros sg before after observer Hvalid [_ ->] Hforeign.
    unfold task_creation_frame, task_creation_view; reflexivity.
  - intros sg before after observer origin Hvalid [_ ->] Hnormal Hactive.
    exact Hactive.
  - intros sg before after observer Hvalid [_ ->] Hforeign.
    unfold event_creation_frame, event_creation_view; reflexivity.
Qed.

Lemma tmr_del_int_enter_client_timer_state_eq : forall observed sg before after,
  kernel_client_step (tmr_del_int_enter_client observed) sg before after ->
  after.(TimerState) = before.(TimerState).
Proof.
  intros observed sg before after [_ Hafter].
  rewrite Hafter; reflexivity.
Qed.

(** The supported client family is deliberately explicit and extensible.
    It contains only source bindings whose complete client certificate and
    Timer-state frame are proved here; adding another interrupt, callback or
    task API requires a new constructor-level certificate rather than
    silently widening the rely relation. *)
Definition tmr_del_supported_client_family (action : KernelClientAction) : Prop :=
  (exists observed, action = tmr_del_int_enter_client observed) \/
  (exists app value counter invocation origin,
     action = tmr_del_tick_client app value counter invocation origin).

Lemma tmr_del_supported_client_certificate : forall action,
  tmr_del_supported_client_family action -> KernelClientCertificate action.
Proof.
  intros action [ [observed Haction] | [app [value [counter [invocation [origin Haction]]]]]];
    subst action.
  - apply tmr_del_int_enter_client_certificate.
  - apply tmr_del_tick_client_certificate.
Qed.

Lemma tmr_del_tick_client_intr_timer_eq : forall app value counter invocation origin sg initial final,
  kernel_client_step (tmr_del_tick_client app value counter invocation origin) sg initial final ->
  UCOS2_state_inv sg initial ->
  final.(IntrState) = initial.(IntrState) /\ final.(TimerState) = initial.(TimerState).
Proof.
  intros app value counter invocation origin sg initial final [Hentry Hcall] Hvalid.
  eapply tmr_del_tick_call_intr_timer_eq; eassumption.
Qed.

Lemma tmr_del_supported_client_timer_state_eq : forall action,
  tmr_del_supported_client_family action ->
  forall sg before after,
    UCOS2_state_inv sg before ->
    kernel_client_step action sg before after ->
    after.(TimerState) = before.(TimerState).
Proof.
  intros action [ [observed Haction] | [app [value [counter [invocation [origin Haction]]]]]];
    subst action; intros sg before after Hvalid Hstep.
  - eapply tmr_del_int_enter_client_timer_state_eq; eassumption.
  - eapply tmr_del_tick_client_intr_timer_eq; eassumption.
Qed.

(** Bind the paired control envelope to the already specified Tick body.
    Its counter/Timer frame is DERIVED from time_tick_sem, not inserted as
    a filter on arbitrary client actions. The observed flag at each end
    is explicit in the envelope: a concrete wrapper must bind both actual
    observations to this value. This single body is not the complete ISR
    family, and its existing C contract still requires the full invariant. *)
Lemma tmr_del_tick_interrupt_control :
  forall app value counter invocation origin handler observed sg before after,
  UCOS2_state_inv sg before ->
  kernel_interrupt_nesting_agrees observed (KernelCaller invocation origin) before.(IntrState) ->
  (observed = true -> before.(IntrState).(lockNesting) <> 0) ->
  kernel_client_step (tmr_del_tick_client app value counter invocation origin) sg
    (replace_IntrS (interrupt_enter_state observed before.(IntrState)) before) after ->
  UCOS2_state_inv sg after /\ after.(TimerState) = before.(TimerState) /\
  kernel_control_step (KernelExitInterrupt observed)
    (KernelInterrupt handler (KernelCaller invocation origin)) after.(IntrState)
    (KernelCaller invocation origin) before.(IntrState) false.
Proof.
  intros app value counter invocation origin handler observed sg before after
    Hvalid Hagrees Hlocked Hbody.
  assert (Hentered : UCOS2_state_inv sg
    (replace_IntrS (interrupt_enter_state observed before.(IntrState)) before)).
  { rewrite UCOS2_validity_replace_interrupt_eq; exact Hvalid. }
  pose proof (kernel_client_preserves_validity
    (tmr_del_tick_client app value counter invocation origin)
    (tmr_del_tick_client_certificate app value counter invocation origin) sg
    (replace_IntrS (interrupt_enter_state observed before.(IntrState)) before) after
    Hentered Hbody) as Hafter.
  destruct (tmr_del_tick_client_intr_timer_eq app value counter invocation origin sg
    (replace_IntrS (interrupt_enter_state observed before.(IntrState)) before) after
    Hbody Hentered) as [Hintr Htimer].
  split; [exact Hafter|]. split; [exact Htimer|].
  rewrite Hintr.
  exact (proj2 (kernel_borrowed_interrupt_counter_envelope observed invocation origin handler
    before.(IntrState) Hagrees Hlocked)).
Qed.

(** Bind OSIntExit's actual OSRunning read to the supported Tick body's
    endpoint. This equality is derived from the post/scan operations,
    not stipulated as an extra filter on the client relation. *)
Lemma tmr_del_tick_interrupt_exit_guard :
  forall app value counter invocation origin observed sg before after,
  UCOS2_state_inv sg before -> observed = before.(SchedState).(isRunning) ->
  (observed = true -> before.(IntrState).(lockNesting) <> 0) ->
  kernel_client_step (tmr_del_tick_client app value counter invocation origin) sg
    (replace_IntrS (interrupt_enter_state observed before.(IntrState)) before) after ->
  after.(SchedState).(isRunning) = observed /\
  interrupt_exit_requests_schedule after.(SchedState).(isRunning) after.(IntrState) = false.
Proof.
  intros app value counter invocation origin observed sg before after
    Hvalid Hobserved Hlocked Hbody.
  assert (Hentered : UCOS2_state_inv sg
    (replace_IntrS (interrupt_enter_state observed before.(IntrState)) before)).
  { rewrite UCOS2_validity_replace_interrupt_eq; exact Hvalid. }
  destruct (tmr_del_tick_client_intr_timer_eq app value counter invocation origin sg
    (replace_IntrS (interrupt_enter_state observed before.(IntrState)) before) after
    Hbody Hentered) as [Hintr _].
  pose proof Hbody as [_ Hcall].
  pose proof (tmr_del_tick_call_running_eq app sg value counter
    (replace_IntrS (interrupt_enter_state observed before.(IntrState)) before) tt after
    Hcall Hentered) as Hrunning.
  change (after.(SchedState).(isRunning) = before.(SchedState).(isRunning)) in Hrunning.
  rewrite <- Hobserved in Hrunning; split; [exact Hrunning|].
  rewrite Hrunning, Hintr; cbn [replace_IntrS IntrState].
  destruct observed; [|reflexivity].
  apply os_int_exit_no_schedule_positive_lock.
  unfold interrupt_enter_state; destruct (Z.ltb before.(IntrState).(intNesting) 255);
    cbn; apply Hlocked; reflexivity.
Qed.

(** The selected public prefix checks NULL, type, then ISR nesting. These
    are observations at the actual reads, not permission to dereference
    an arbitrary pointer or identify states separated by interference.
    Reused proof text from annotation r2 is rechecked in this candidate. *)
Definition tmr_del_early_result (pointer type_byte nesting : Z)
  : option (bool * OSErrCode) :=
  if Z.eqb pointer 0 then Some (false, OS_ERR_TMR_INVALID)
  else if Z.eqb type_byte 100 then
    if Z.ltb 0 nesting then Some (false, OS_ERR_TMR_ISR) else None
  else Some (false, OS_ERR_TMR_INVALID_TYPE).

Lemma tmr_del_early_result_null : forall type_byte nesting,
  tmr_del_early_result 0 type_byte nesting = Some (false, OS_ERR_TMR_INVALID).
Proof. reflexivity. Qed.

Lemma tmr_del_early_result_type : forall pointer type_byte nesting,
  pointer <> 0 -> type_byte <> 100 ->
  tmr_del_early_result pointer type_byte nesting = Some (false, OS_ERR_TMR_INVALID_TYPE).
Proof.
  intros pointer type_byte nesting Hp Htype; unfold tmr_del_early_result.
  apply Z.eqb_neq in Hp; apply Z.eqb_neq in Htype; rewrite Hp, Htype; reflexivity.
Qed.

Lemma tmr_del_early_result_isr : forall pointer nesting,
  pointer <> 0 -> 0 < nesting ->
  tmr_del_early_result pointer 100 nesting = Some (false, OS_ERR_TMR_ISR).
Proof.
  intros pointer nesting Hp Hints; unfold tmr_del_early_result.
  apply Z.eqb_neq in Hp; apply Z.ltb_lt in Hints; rewrite Hp, Hints; reflexivity.
Qed.

Lemma tmr_del_early_result_continue_iff : forall pointer type_byte nesting,
  tmr_del_early_result pointer type_byte nesting = None <->
  pointer <> 0 /\ type_byte = 100 /\ nesting <= 0.
Proof.
  intros; unfold tmr_del_early_result.
  destruct (Z.eqb pointer 0) eqn:Hp; [apply Z.eqb_eq in Hp|apply Z.eqb_neq in Hp].
  - split; [discriminate|tauto].
  - destruct (Z.eqb type_byte 100) eqn:Htype;
      [apply Z.eqb_eq in Htype|apply Z.eqb_neq in Htype].
    + destruct (Z.ltb 0 nesting) eqn:Hn;
        [apply Z.ltb_lt in Hn|apply Z.ltb_ge in Hn].
      * split; [discriminate|intros [_ [_ Hle]]; lia].
      * split; [intro; repeat split; assumption|intro; reflexivity].
    + split; [discriminate|tauto].
Qed.

(** Context agreement is an explicit source-binding premise. These facts
    do not assume a task-only precondition that erases the ISR error arm.
    They intentionally do NOT infer a caller in the OSRunning=false case. *)
Lemma tmr_del_running_interrupt_guard : forall pointer handler context counters,
  pointer <> 0 ->
  kernel_interrupt_nesting_agrees true (KernelInterrupt handler context) counters ->
  tmr_del_early_result pointer 100 counters.(intNesting) = Some (false, OS_ERR_TMR_ISR).
Proof.
  intros pointer handler context counters Hp Hagrees.
  apply tmr_del_early_result_isr; [exact Hp|].
  eapply kernel_running_interrupt_nesting_positive; exact Hagrees.
Qed.

Lemma tmr_del_running_continue_is_caller : forall pointer type_byte context counters,
  kernel_interrupt_nesting_agrees true context counters ->
  tmr_del_early_result pointer type_byte counters.(intNesting) = None ->
  exists invocation origin, kernel_caller_executing invocation origin context.
Proof.
  intros pointer type_byte context counters Hagrees Hcontinue.
  apply tmr_del_early_result_continue_iff in Hcontinue.
  destruct Hcontinue as [Hp [Htype Hnonpositive]].
  apply (kernel_running_zero_nesting_is_caller context counters Hagrees).
  pose proof (Hagrees eq_refl); lia.
Qed.

(** The lock-held switch is exposed as an inductive source relation.  This
    keeps the four concrete branches visible to the caller proof while
    reusing the executable [timer_delete_locked] transformer.  The relation
    does not grant any heap ownership; it only records which already
    protected Unlink/Free composition the C switch selected. *)
Inductive tmr_del_locked_calls (sg : StableGlobVars) (before : GlobTimerState)
  (i : TimerID) (name : addr) : bool -> OSErrCode -> GlobTimerState -> Prop :=
| TmrDelRunning : forall image stopped after_unlink,
    before.(timerImages) i = Some image -> image.(timerImageState) = 3 ->
    timer_unlink sg before i = Some stopped ->
    stopped.(timerImages) i = Some after_unlink ->
    tmr_del_locked_calls sg before i name true OS_ERR_NONE
      (timer_release sg stopped i after_unlink name)
| TmrDelStopped : forall image,
    before.(timerImages) i = Some image ->
    (image.(timerImageState) = 1 \/ image.(timerImageState) = 2) ->
    tmr_del_locked_calls sg before i name true OS_ERR_NONE
      (timer_release sg before i image name)
| TmrDelUnused : forall image,
    before.(timerImages) i = Some image -> image.(timerImageState) = 0 ->
    tmr_del_locked_calls sg before i name false OS_ERR_TMR_INACTIVE before
| TmrDelInvalidState : forall image,
    before.(timerImages) i = Some image -> image.(timerImageState) <> 0 ->
    image.(timerImageState) <> 1 -> image.(timerImageState) <> 2 ->
    image.(timerImageState) <> 3 ->
    tmr_del_locked_calls sg before i name false OS_ERR_TMR_INVALID_STATE before.

Lemma tmr_del_locked_calls_iff : forall sg before i name ret err completion,
  tmr_del_locked_calls sg before i name ret err completion <->
  timer_delete_locked sg before i name = Some (ret, err, completion).
Proof.
  intros sg before i name ret err completion; split.
  - intro Hcalls; destruct Hcalls; unfold timer_delete_locked; rewrite H.
    + rewrite H0; simpl; rewrite H1, H2; reflexivity.
    + destruct H0 as [Hstate|Hstate]; rewrite Hstate; reflexivity.
    + rewrite H0; reflexivity.
    + apply Z.eqb_neq in H0; apply Z.eqb_neq in H1;
        apply Z.eqb_neq in H2; apply Z.eqb_neq in H3.
      rewrite H3, H1, H2, H0; reflexivity.
  - unfold timer_delete_locked.
    destruct (timerImages before i) as [image|] eqn:Himage; [|discriminate].
    destruct (Z.eqb (timerImageState image) 3) eqn:Hrun.
    + destruct (timer_unlink sg before i) as [stopped|] eqn:Hunlink; [|discriminate].
      destruct (timerImages stopped i) as [after_unlink|] eqn:Hafter; [|discriminate].
      intro Hresult; inversion Hresult; subst.
      eapply TmrDelRunning; eauto; apply Z.eqb_eq; exact Hrun.
    + apply Z.eqb_neq in Hrun.
      destruct (orb (Z.eqb (timerImageState image) 1)
        (Z.eqb (timerImageState image) 2)) eqn:Hstopped.
      * intro Hresult; inversion Hresult; subst.
        eapply TmrDelStopped; [exact Himage|].
        apply Bool.orb_true_iff in Hstopped.
        destruct Hstopped as [Hs|Hs]; apply Z.eqb_eq in Hs; auto.
      * apply Bool.orb_false_iff in Hstopped; destruct Hstopped as [Hone Htwo].
        apply Z.eqb_neq in Hone; apply Z.eqb_neq in Htwo.
        destruct (Z.eqb (timerImageState image) 0) eqn:Hzero;
          intro Hresult; inversion Hresult; subst.
        -- eapply TmrDelUnused; [exact Himage|apply Z.eqb_eq; exact Hzero].
        -- eapply TmrDelInvalidState; eauto; apply Z.eqb_neq; exact Hzero.
Qed.

Lemma tmr_del_locked_failure_unchanged : forall sg before i name err completion,
  tmr_del_locked_calls sg before i name false err completion ->
  completion = before /\
    (err = OS_ERR_TMR_INACTIVE \/ err = OS_ERR_TMR_INVALID_STATE).
Proof. intros; inversion H; subst; auto. Qed.

Lemma tmr_del_locked_calls_total : forall sg before i name image,
  valid_timer_state sg before -> before.(timerImages) i = Some image ->
  exists ret err completion, tmr_del_locked_calls sg before i name ret err completion.
Proof.
  intros sg before i name image Hvalid Himage.
  destruct (Z.eq_dec image.(timerImageState) 3) as [Hrun|Hrun].
  - destruct (valid_timer_state_nonunused_image sg before i image Hvalid Himage
      ltac:(lia)) as [node [Hnode Hencode]].
    destruct (timer_unlink_result_exists sg before i node image Hnode Himage)
      as [stopped Hunlink].
    destruct (timer_unlink_clears_links_and_stops sg before i stopped Hunlink)
      as [after_node [after_image [Hafter_node [Hafter_image Hafter_state]]]].
    do 3 eexists; eapply TmrDelRunning; eassumption.
  - destruct (Z.eq_dec image.(timerImageState) 1) as [Hone|Hone].
    + do 3 eexists; eapply TmrDelStopped; eauto.
    + destruct (Z.eq_dec image.(timerImageState) 2) as [Htwo|Htwo].
      * do 3 eexists; eapply TmrDelStopped; eauto.
      * destruct (Z.eq_dec image.(timerImageState) 0) as [Hzero|Hzero].
        -- do 3 eexists; eapply TmrDelUnused; eassumption.
        -- do 3 eexists; eapply TmrDelInvalidState; eassumption.
Qed.

Lemma tmr_del_locked_success_removes_live_object : forall sg before i name err completion,
  tmr_del_locked_calls sg before i name true err completion ->
  err = OS_ERR_NONE /\ completion.(timerUsed) i = None.
Proof.
  intros; split; [inversion H; reflexivity|].
  eapply timer_delete_locked_removes_live_object.
  apply (proj1 (tmr_del_locked_calls_iff sg before i name true err completion)); exact H.
Qed.

(** The configured Unlink result carries the stopped object image that the
    source immediately passes to Free.  This bridge is deliberately stated
    at Free's existing valid-input layer: it does not add a second Timer
    representation or silently discard the type/delay/padding frame. *)
Lemma tmr_del_unlink_produces_free_input : forall sg before i pointer stopped,
  tmr_free_bindings sg pointer -> pointer = timer_pool_addr sg i ->
  timer_api_initialized before -> timer_unlink sg before i = Some stopped ->
  exists node image, tmr_free_valid_input sg stopped i node image pointer.
Proof.
  intros sg before i pointer stopped Hbindings Hp Hinit Hunlink.
  destruct (timer_unlink_clears_links_and_stops sg before i stopped Hunlink)
    as [node [image [Hnode [Himage [Hstate _]]]]].
  exists node, image; unfold tmr_free_valid_input.
  split; [exact Hbindings|]. split; [exact Hp|]. split.
  - unfold timer_api_initialized in *.
    rewrite (timer_unlink_preserves_initialization_phase sg before i stopped Hunlink).
    exact Hinit.
  - split; [exact Hnode|]. split; [exact Himage|].
    rewrite Hstate; discriminate.
Qed.

(** The direct-Free branch obtains its object from the valid Timer
    representation and the source state-byte guard. *)
Lemma tmr_del_stopped_produces_free_input : forall sg before i pointer image,
  tmr_free_bindings sg pointer -> pointer = timer_pool_addr sg i ->
  valid_timer_state sg before -> timer_api_initialized before ->
  before.(timerImages) i = Some image ->
  (image.(timerImageState) = 1 \/ image.(timerImageState) = 2) ->
  exists node, tmr_free_valid_input sg before i node image pointer.
Proof.
  intros sg before i pointer image Hbindings Hp Hvalid Hinit Himage Hstate.
  destruct (valid_timer_state_nonunused_image sg before i image Hvalid Himage
    ltac:(destruct Hstate; lia)) as [node [Hnode Hencode]].
  exists node; unfold tmr_free_valid_input.
  split; [exact Hbindings|]. split; [exact Hp|]. split; [exact Hinit|].
  split; [exact Hnode|]. split; [exact Himage|].
  intro Hrunning; rewrite Hrunning in Hencode; simpl in Hencode;
    destruct Hstate; lia.
Qed.

(** A successful locked deletion yields the post-Timer validity needed by
    the caller's completion checkpoint.  The theorem is pure state
    transport; it does not claim that Unlock preserves the released slot. *)
Lemma tmr_del_completion_preserves_validity : forall sg before i name ret err timers,
  tmr_unlink_profile sg -> UCOS2_state_inv sg before ->
  timer_api_initialized before.(TimerState) ->
  tmr_del_locked_calls sg before.(TimerState) i name ret err timers ->
  UCOS2_state_inv sg (replace_TimerS timers before) /\ timer_api_initialized timers.
Proof.
  intros sg before i name ret err timers Hprofile Hvalid Hinit Hcalls.
  pose proof Hprofile as [Hen [_ [Hcap _]]].
  assert (Htimer : valid_timer_configuration sg before.(TimerState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  pose proof (proj1 (tmr_del_locked_calls_iff sg before.(TimerState) i name ret err timers)
    Hcalls) as Hstep.
  destruct (timer_delete_locked_preserves_configuration sg before.(TimerState) i name
    ret err timers Hen ltac:(lia) (tmr_unlink_profile_pool_region sg Hprofile)
    Htimer Hinit Hstep) as [Hafter Hphase].
  split; [|exact Hphase].
  apply UCOS2_replace_timer_preserves_validity; [exact Hvalid|exact Hafter| |].
  - intros _ _; exact Hphase.
  - eapply timer_delete_locked_name_references; exact Hstep.
Qed.

(** The corresponding spatial completion bridge reconnects the changed
    Timer pool with all non-Timer resources.  It is the endpoint consumed
    before the canonical scheduler Unlock contract. *)
Lemma tmr_del_completion_merge_timer : forall sg before i name ret err timers,
  tmr_unlink_profile sg -> UCOS2_state_inv sg before ->
  timer_api_initialized before.(TimerState) ->
  tmr_del_locked_calls sg before.(TimerState) i name ret err timers ->
  timer_configured_rep sg timers ** UCOS2_raw_rep_missing_timer sg before |--
    UCOS2_inv sg (replace_TimerS timers before).
Proof.
  intros sg before i name ret err timers Hprofile Hvalid Hinit Hcalls.
  apply (UCOS2_inv_merge_updated_timer sg before (replace_TimerS timers before)).
  - exact (proj1 (tmr_del_completion_preserves_validity sg before i name ret err timers
      Hprofile Hvalid Hinit Hcalls)).
  - symmetry; apply UCOS2_raw_rep_missing_timer_replace_eq.
Qed.

(** Lift the locked Timer transition to the complete kernel state.  The
    callee relation changes only [TimerState]; every other top-level state
    component remains the caller's actual checkpoint.  This is the reusable
    endpoint for an OSTmrDel annotation, before the scheduler Unlock may
    perform its own continuation or scheduling step. *)
Definition tmr_del_locked_state_step
  (sg : StableGlobVars) (before : UCOS2_Verify_State)
  (i : TimerID) (name : addr) (ret : bool) (err : OSErrCode)
  (after : UCOS2_Verify_State) : Prop :=
  exists timers,
    tmr_del_locked_calls sg before.(TimerState) i name ret err timers /\
    after = replace_TimerS timers before.

Lemma tmr_del_locked_state_step_preserves_validity : forall sg before i name ret err after,
  tmr_unlink_profile sg -> UCOS2_state_inv sg before ->
  timer_api_initialized before.(TimerState) ->
  tmr_del_locked_state_step sg before i name ret err after ->
  UCOS2_state_inv sg after /\ timer_api_initialized after.(TimerState).
Proof.
  intros sg before i name ret err after Hprofile Hvalid Hinit
    [timers [Hcalls Hafter]].
  subst after.
  exact (tmr_del_completion_preserves_validity sg before i name ret err timers
    Hprofile Hvalid Hinit Hcalls).
Qed.

Lemma tmr_del_locked_state_step_failure_unchanged : forall sg before i name err after,
  tmr_del_locked_state_step sg before i name false err after ->
  after = before /\
  (err = OS_ERR_TMR_INACTIVE \/ err = OS_ERR_TMR_INVALID_STATE).
Proof.
  intros sg before i name err after [timers [Hcalls Hafter]].
  pose proof (tmr_del_locked_failure_unchanged sg before.(TimerState) i name err timers
    Hcalls) as [Htimer Herr].
  subst timers; subst after.
  rewrite replace_TimerS_put_back.
  split; [reflexivity|exact Herr].
Qed.

Lemma tmr_del_locked_state_step_success_removes_live_object : forall sg before i name err after,
  tmr_del_locked_state_step sg before i name true err after ->
  err = OS_ERR_NONE /\ after.(TimerState).(timerUsed) i = None.
Proof.
  intros sg before i name err after [timers [Hcalls Hafter]].
  pose proof (tmr_del_locked_success_removes_live_object sg before.(TimerState)
    i name err timers Hcalls) as [Herr Hremoved].
  subst after; split; [exact Herr|rewrite replace_TimerS_TimerState; exact Hremoved].
Qed.

Lemma tmr_del_locked_state_step_total : forall sg before i name image,
  valid_timer_state sg before.(TimerState) ->
  before.(TimerState).(timerImages) i = Some image ->
  exists ret err after, tmr_del_locked_state_step sg before i name ret err after.
Proof.
  intros sg before i name image Hvalid Himage.
  destruct (tmr_del_locked_calls_total sg before.(TimerState) i name image Hvalid Himage)
    as [ret [err [timers Hcalls]]].
  exists ret, err, (replace_TimerS timers before).
  exists timers; split; [exact Hcalls|reflexivity].
Qed.

(** The ordinary return keeps the exact Unlock postcondition and only then
    writes [perr].  A released Timer slot is intentionally not framed as a
    caller-owned cell after a possible scheduler continuation. *)
Definition tmr_del_after_unlock (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask : Z)
  (completion : UCOS2_Verify_State) (perr : Z) (err : OSErrCode) : Assertion :=
  os_sched_unlock_post external platform critical sg context mask completion **
  perr # UChar |-> encode_os_err_code err.

(** The public result is deliberately separate from the concrete boolean and
    error byte.  The constructor records both values so an observer cannot
    forget the source's exact error branch. *)
Inductive TmrDelResult : Type :=
| TmrDelResultValue (ret : bool) (err : OSErrCode).

Definition tmr_del_result_ret (result : TmrDelResult) : bool :=
  match result with TmrDelResultValue ret _ => ret end.

Definition tmr_del_result_err (result : TmrDelResult) : OSErrCode :=
  match result with TmrDelResultValue _ err => err end.

Definition tmr_del_return (result : TmrDelResult) : Z :=
  if tmr_del_result_ret result then 1 else 0.

Definition tmr_del_observe_result (result : TmrDelResult)
  : program (UCOS2_Verify_State -> Prop) Z :=
  fun before observed after =>
    observed = tmr_del_return result /\ after = before.

(** Source-ordered abstract result classification.  The early arms retain the
    complete abstract state.  The locked arm exposes the exact pre-Unlock
    Timer transition; Restore/scheduling is represented by the caller's
    [os_sched_unlock_post] contract, not hidden in this relation. *)
Definition tmr_del_result_prop (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pointer name : addr)
  (before after : UCOS2_Verify_State) (result : TmrDelResult) : Prop :=
  (pointer = 0 /\ result = TmrDelResultValue false OS_ERR_TMR_INVALID /\ after = before) \/
  (pointer <> 0 /\
   exists i image,
     pointer = timer_pool_addr sg i /\
     before.(TimerState).(timerImages) i = Some image /\
     image.(timerImageType) <> 100 /\
     result = TmrDelResultValue false OS_ERR_TMR_INVALID_TYPE /\ after = before) \/
  (pointer <> 0 /\
   exists i image,
     pointer = timer_pool_addr sg i /\
     before.(TimerState).(timerImages) i = Some image /\
     image.(timerImageType) = 100 /\
     before.(IntrState).(intNesting) > 0 /\
     result = TmrDelResultValue false OS_ERR_TMR_ISR /\ after = before) \/
  (pointer <> 0 /\ exists i image acquired locked,
     pointer = timer_pool_addr sg i /\
     before.(TimerState).(timerImages) i = Some image /\
     image.(timerImageType) = 100 /\
     before.(IntrState).(intNesting) <= 0 /\
     os_sched_lock_call_relation critical sg invocation before acquired locked /\
     tmr_del_locked_state_step sg locked i name
       (tmr_del_result_ret result) (tmr_del_result_err result) after).

(** The endpoint labels the Timer completion before Unlock.  The spatial
    caller post below retains Unlock's separate acquisition/resumption
    contract; this token must not be interpreted as its returned state. *)
Definition tmr_del_completion_token (completion : UCOS2_Verify_State)
  : UCOS2_Verify_State -> Prop := fun observed => observed = completion.

Definition tmr_del_completion_observation (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pointer name : addr)
  (before after : UCOS2_Verify_State) (result : TmrDelResult)
  : (UCOS2_Verify_State -> Prop) -> Prop :=
  fun observed => tmr_del_result_prop critical sg invocation pointer name
    before after result /\ observed = tmr_del_completion_token after.

Definition tmr_del_atomic_cmd (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat)
  (before : UCOS2_Verify_State) (pointer : addr) (name : addr)
  : program (UCOS2_Verify_State -> Prop) TmrDelResult :=
  fun initial result final =>
    LastSeen before initial /\ exists completion,
      tmr_del_completion_observation critical sg invocation pointer name
        before completion result final.

Lemma tmr_del_safe_return : forall critical sg invocation pointer name before after result
  (X : Z -> (UCOS2_Verify_State -> Prop) -> Prop),
  tmr_del_result_prop critical sg invocation pointer name before after result ->
  safeExec (LastSeen before)
    (bind (tmr_del_atomic_cmd critical sg invocation before pointer name)
      tmr_del_observe_result) X ->
  safeExec (tmr_del_completion_observation critical sg invocation pointer name
    before after result) (StateRelMonad.ret (tmr_del_return result)) X.
Proof.
  intros critical sg invocation pointer name before after result X Hsem Hexec.
  assert (Hstep : hs_eval (tmr_del_atomic_cmd critical sg invocation before pointer name)
    (LastSeen before)
    (tmr_del_completion_observation critical sg invocation pointer name before after result)
    result).
  { unfold hs_eval, tmr_del_atomic_cmd; intros initial Hinitial.
    exists (tmr_del_completion_token after); split.
    - split; [exact Hinitial|]. exists after.
      unfold tmr_del_completion_observation; split; [exact Hsem|reflexivity].
    - unfold tmr_del_completion_observation; split; [exact Hsem|reflexivity]. }
  pose proof (highstepbind_derive
    (tmr_del_atomic_cmd critical sg invocation before pointer name)
    tmr_del_observe_result (LastSeen before) result
    (tmr_del_completion_observation critical sg invocation pointer name before after result)
    Hstep X Hexec) as Hobserve.
  eapply (highstependret_derive (tmr_del_observe_result result)
    (tmr_del_completion_observation critical sg invocation pointer name before after result)
    (tmr_del_return result)
    (fun _ => tmr_del_completion_observation critical sg invocation pointer name
      before after result)).
  2: exact Hobserve.
  unfold hs_eval, tmr_del_observe_result; intros initial Hinitial.
  exists initial; split; [split; reflexivity|exact Hinitial].
Qed.

Lemma tmr_del_return_in_range : forall result,
  tmr_del_return result = 0 \/ tmr_del_return result = 1.
Proof. intros [ret err]; destruct ret; simpl; auto. Qed.

Definition tmr_del_caller_post
  (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (mask : Z)
  (before after : UCOS2_Verify_State) (pointer name perr : addr)
  (result : TmrDelResult) : Assertion :=
  coq_prop (tmr_del_result_prop critical sg context.(os_sched_call_invocation)
    pointer name before after result) &&
  tmr_del_after_unlock external platform critical sg context mask after perr
    (tmr_del_result_err result).

Definition tmr_del_pointer_binding (sg : StableGlobVars)
  (before : UCOS2_Verify_State) (pointer : addr) : Prop :=
  pointer = 0 \/
  exists i image,
    sg.(osKernelConfig).(cfgTimerEnabled) = true /\
    timer_api_initialized before.(TimerState) /\
    pointer = timer_pool_addr sg i /\
    before.(TimerState).(timerImages) i = Some image.

Definition tmr_del_observation_binding (sg : StableGlobVars)
  (before : UCOS2_Verify_State) (pointer : addr) (i : TimerID)
  (image : TimerImage) : Prop :=
  sg.(osKernelConfig).(cfgTimerEnabled) = true /\
  timer_api_initialized before.(TimerState) /\
  pointer = timer_pool_addr sg i /\
  before.(TimerState).(timerImages) i = Some image.

Definition tmr_del_observation_case (sg : StableGlobVars)
  (before : UCOS2_Verify_State) (pointer : addr) (i : TimerID)
  (image : TimerImage) : Prop :=
  pointer = 0 \/ tmr_del_observation_binding sg before pointer i image.

Definition tmr_del_image_type (image : TimerImage) : Z := image.(timerImageType).

Definition tmr_del_image_state (image : TimerImage) : Z := image.(timerImageState).

Definition tmr_del_locked_image (state : UCOS2_Verify_State)
  (i : TimerID) (image : TimerImage) : Prop :=
  state.(TimerState).(timerImages) i = Some image.

Definition tmr_del_timer_state (state : UCOS2_Verify_State) : GlobTimerState :=
  state.(TimerState).

Definition tmr_del_int_nesting (state : UCOS2_Verify_State) : Z :=
  state.(IntrState).(intNesting).

(** The Free helper's object witness is an internal representation detail.
    Keep it existential at the Del call boundary so a preceding Unlink
    step can expose the stopped state without leaking an unbound Coq
    witness into the C annotation.  This wrapper is equivalent to the
    existing [tmr_free_valid_input] family and does not weaken the helper
    contract. *)
Definition tmr_del_free_input (sg : StableGlobVars) (s : GlobTimerState)
  (i : TimerID) (old : TimerImage) (p : addr) : Prop :=
  exists t, tmr_free_valid_input sg s i t old p.

(** Bind the same selected C/ABI interpretation already required by the
    Unlink, Free and Unlock callees.  These are configuration and frontend
    address facts, not restrictions on the runtime Timer branches.  QCP's
    abstract address evaluator does not derive them from pure state validity. *)
Definition tmr_del_c_bindings (sg : StableGlobVars) (pointer : addr) : Prop :=
  tmr_unlink_layout /\ tmr_free_bindings sg pointer /\
  os_sched_unlock_global_addresses sg &("OSRunning") &("OSIntNesting")
    &("OSLockNesting") &("OSPrioHighRdy") &("OSPrioCur") &("OSTCBHighRdy")
    &("OSTCBPrioTbl") &("OSCtxSwCtr") &("OSUnMapTbl") &("OSRdyGrp") &("OSRdyTbl") /\
  &("OSTmrWheelTbl") = sg.(g_OSTmrWheelTbl).

Definition tmr_del_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (before : UCOS2_Verify_State) (pointer perr : addr) (perr_in : Z) : Assertion :=
  coq_prop (valid_stable_glob_vars sg /\
    tmr_del_c_bindings sg pointer /\
    tmr_del_pointer_binding sg before pointer /\
    os_sched_lock_global_addresses sg &("OSRunning")
      &("OSIntNesting") &("OSLockNesting")) &&
  interrupt_platform_running platform invocation origin mask **
  UCOS2_inv sg before.

(** OSTmrDel may return through the scheduler Unlock path after either a
    Timer-only update or an unchanged Timer state.  The scheduler's possible
    Save/Restore continuation is therefore an explicit platform/client
    obligation of this caller, just as it is for OSIntExit and OS_Sched; it is
    not inferred from Timer validity.  Only source-reachable completion
    states are quantified; unrelated callers/states impose no obligation. *)
Definition tmr_del_scheduler_acquire_safety
  (external : OsSchedExternalResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext)
  (before : UCOS2_Verify_State) (pointer name : addr) : Prop :=
  forall i image acquired locked result completion,
    pointer <> 0 -> pointer = timer_pool_addr sg i ->
    before.(TimerState).(timerImages) i = Some image ->
    tmr_del_early_result pointer image.(timerImageType) before.(IntrState).(intNesting) = None ->
    os_sched_lock_call_relation critical sg context.(os_sched_call_invocation)
      before acquired locked ->
    tmr_del_locked_state_step sg locked i name (tmr_del_result_ret result)
      (tmr_del_result_err result) completion ->
    os_sched_unlock_acquire_safety external critical sg context completion.

Definition tmr_del_early_post (sg : StableGlobVars)
  (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (context : OsSchedCallContext) (mask : Z)
  (before : UCOS2_Verify_State) (perr : addr) (err : OSErrCode) : Assertion :=
  perr # UChar |-> encode_os_err_code err **
  interrupt_platform_running platform context.(os_sched_call_invocation)
    context.(os_sched_call_origin) mask **
  UCOS2_inv sg before **
  os_sched_context_resources external context ** unmap_table_rep sg.

Definition tmr_del_post (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask : Z)
  (before : UCOS2_Verify_State) (pointer name perr : addr) (ret : Z) : Assertion :=
  (coq_prop (ret = 0 /\ tmr_del_result_prop critical sg context.(os_sched_call_invocation)
      pointer name before before (TmrDelResultValue false OS_ERR_TMR_INVALID)) &&
    tmr_del_early_post sg external platform critical context mask
      before perr OS_ERR_TMR_INVALID) ||
  (coq_prop (ret = 0 /\ tmr_del_result_prop critical sg context.(os_sched_call_invocation)
      pointer name before before (TmrDelResultValue false OS_ERR_TMR_INVALID_TYPE)) &&
    tmr_del_early_post sg external platform critical context mask
      before perr OS_ERR_TMR_INVALID_TYPE) ||
  (coq_prop (ret = 0 /\ tmr_del_result_prop critical sg context.(os_sched_call_invocation)
      pointer name before before (TmrDelResultValue false OS_ERR_TMR_ISR)) &&
    tmr_del_early_post sg external platform critical context mask
      before perr OS_ERR_TMR_ISR) ||
  (EX result post,
    coq_prop (ret = tmr_del_return result /\
      tmr_del_result_prop critical sg context.(os_sched_call_invocation)
        pointer name before post result) &&
    tmr_del_caller_post external platform critical sg context mask before post
      pointer name perr result).

(** OSTmrDel caller-composition seed.  The locked Timer transformer does
    not itself account for the ordered pointer/type/ISR checks, scheduler
    calls or the caller's error-output cell.  The annotation owner supplies
    that full contract after the scheduler C-call dependencies are ready. *)

(** [OSTmrDel] reads the timer type and interrupt nesting before acquiring
    the scheduler lock.  This residual names exactly the ownership left
    after those two observations: the timer object with its type byte
    removed, the interrupt range plus lock-nesting cell, and all other
    module owners.  It is a structural split of [UCOS2_inv], not a rule for
    opening a shared invariant or for permitting an ISR to interfere. *)
Definition tmr_del_observation_residual (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (i : TimerID) (v : TimerImage) : Assertion :=
  timer_raw_rep_without_type sg s.(TimerState) i v **
  interrupt_inv_no_int_nesting sg s.(IntrState) **
  UCOS2_raw_rep_missing_two sg s TimerModule InterruptModule.

(** After the scheduler call the Timer owner is reopened at the lock's
    current state, so the state byte is split from that fresh image rather
    than carried from the pre-lock snapshot. *)
Definition tmr_del_locked_observation_residual (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (i : TimerID) (v : TimerImage) : Assertion :=
  timer_raw_rep_without_type_state sg s.(TimerState) i v **
  UCOS2_raw_rep_missing_timer sg s.

Lemma tmr_del_split_locked_state : forall sg s i v,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  timer_api_initialized s.(TimerState) ->
  s.(TimerState).(timerImages) i = Some v ->
  UCOS2_inv sg s |--
    coq_prop (UCOS2_state_inv sg s) &&
    (timer_pool_addr sg i # UChar |-> v.(timerImageType) **
     (timer_pool_addr sg i + timer_option_offset sg.(osKernelConfig) + 1) # UChar |->
       v.(timerImageState) **
     tmr_del_locked_observation_residual sg s i v).
Proof.
  intros sg s i v Henabled Hinitialized Himage.
  rewrite (UCOS2_inv_split_module sg s TimerModule).
  cbn [UCOS2_module_rep]. pureIntros.
  rewrite (timer_initialized_configured_rep_eq sg s.(TimerState) Henabled Hinitialized).
  sep_apply_l_atomic (timer_raw_rep_split_type_state sg s.(TimerState) i v Himage).
  unfold tmr_del_locked_observation_residual.
  entailer!.
Qed.

Lemma tmr_del_split_observations : forall sg s i v,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  timer_api_initialized s.(TimerState) ->
  s.(TimerState).(timerImages) i = Some v ->
  UCOS2_inv sg s |--
    coq_prop (UCOS2_state_inv sg s) &&
    (timer_pool_addr sg i # UChar |-> v.(timerImageType) **
     sg.(g_OSIntNesting) # UChar |-> s.(IntrState).(intNesting) **
     tmr_del_observation_residual sg s i v).
Proof.
  intros sg s i v Henabled Hinitialized Himage.
  rewrite (UCOS2_inv_split_two sg s TimerModule InterruptModule ltac:(discriminate)).
  cbn [UCOS2_module_rep].
  pureIntros.
  rewrite (timer_initialized_configured_rep_eq sg s.(TimerState) Henabled Hinitialized).
  sep_apply_l_atomic (timer_raw_rep_split_type sg s.(TimerState) i v Himage).
  unfold tmr_del_observation_residual, interrupt_inv,
    interrupt_inv_no_int_nesting, store_int_state.
  entailer!.
Qed.

Lemma tmr_del_merge_observations : forall sg s i v,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  timer_api_initialized s.(TimerState) ->
  s.(TimerState).(timerImages) i = Some v ->
  coq_prop (UCOS2_state_inv sg s) &&
    (timer_pool_addr sg i # UChar |-> v.(timerImageType) **
     sg.(g_OSIntNesting) # UChar |-> s.(IntrState).(intNesting) **
     tmr_del_observation_residual sg s i v) |-- UCOS2_inv sg s.
Proof.
  intros sg s i v Henabled Hinitialized Himage.
  rewrite (UCOS2_inv_split_two sg s TimerModule InterruptModule ltac:(discriminate)).
  cbn [UCOS2_module_rep].
  unfold tmr_del_observation_residual.
  unfold interrupt_inv, interrupt_inv_no_int_nesting, store_int_state.
  pureIntros.
  rewrite (timer_initialized_configured_rep_eq sg s.(TimerState) Henabled Hinitialized).
  sep_apply_l_atomic (timer_raw_rep_merge_type sg s.(TimerState) i v Himage).
  entailer!.
Qed.

(** A Timer loan may cross the scheduler-lock interval only when every
    admitted environment client preserves the abstract Timer state.  This
    is a separate obligation from validity and task/event framing: the
    generic kernel-client certificate intentionally does not claim it. *)
Definition tmr_del_timer_state_stable
  (clients : KernelClientAction -> Prop) : Prop :=
  forall action, clients action ->
  forall sg before after,
    UCOS2_state_inv sg before ->
    kernel_client_step action sg before after ->
    after.(TimerState) = before.(TimerState).

Lemma tmr_del_tick_client_timer_state_stable : forall app value counter invocation origin,
  tmr_del_timer_state_stable
    (fun action => action = tmr_del_tick_client app value counter invocation origin).
Proof.
  intros app value counter invocation origin.
  unfold tmr_del_timer_state_stable; intros action Haction sg before after Hvalid Hstep.
  subst action.
  exact (proj2 (tmr_del_tick_client_intr_timer_eq app value counter invocation origin
    sg before after Hstep Hvalid)).
Qed.

Lemma tmr_del_trace_preserves_timer_state : forall clients sg observer before stopped after,
  (forall action, clients action -> KernelClientCertificate action) ->
  tmr_del_timer_state_stable clients ->
  kernel_client_trace clients sg observer before stopped after ->
  UCOS2_state_inv sg before ->
  after.(TimerState) = before.(TimerState).
Proof.
  intros clients sg observer before stopped after Hcert Hstable Htrace.
  induction Htrace as
    [s
    | action before middle after stopped Hclient Hforeign Hevent Hstep Htail IH];
    intro Hvalid.
  - reflexivity.
  - pose proof (Hcert action Hclient) as Hcertificate.
    pose proof (kernel_client_preserves_validity action Hcertificate
      sg before middle Hvalid Hstep) as Hmiddle.
    pose proof (Hstable action Hclient sg before middle Hvalid Hstep) as Htimer.
    specialize (IH Hmiddle).
    transitivity middle.(TimerState); [exact IH|exact Htimer].
Qed.

Lemma tmr_del_supported_trace_preserves_timer_state : forall sg observer before stopped after,
  kernel_client_trace tmr_del_supported_client_family sg observer before stopped after ->
  UCOS2_state_inv sg before ->
  after.(TimerState) = before.(TimerState).
Proof.
  intros sg observer before stopped after Htrace Hvalid.
  apply tmr_del_trace_preserves_timer_state with
    (clients := tmr_del_supported_client_family)
    (sg := sg) (observer := observer) (before := before)
    (stopped := stopped) (after := after).
    
  - intros action Haction.
    apply tmr_del_supported_client_certificate; exact Haction.
  - unfold tmr_del_timer_state_stable; intros action Haction.
    apply tmr_del_supported_client_timer_state_eq; exact Haction.
  - exact Htrace.
  - exact Hvalid.
Qed.

Definition tmr_del_critical_timer_state_stable
  (critical : CriticalRegionResources) : Prop :=
  tmr_del_timer_state_stable critical.(critical_region_clients).

Lemma tmr_del_timer_residual_stable : forall critical sg observer before after i v,
  critical_region_interval critical sg observer before after ->
  tmr_del_critical_timer_state_stable critical ->
  UCOS2_state_inv sg before ->
  timer_raw_rep_without_type sg before.(TimerState) i v =
    timer_raw_rep_without_type sg after.(TimerState) i v.
Proof.
  intros critical sg observer before after i v Hinterval Hstable Hvalid.
  pose proof (tmr_del_trace_preserves_timer_state
    critical.(critical_region_clients) sg observer before false after
    critical.(critical_region_client_certificates) Hstable
    (critical_region_interval_raw_trace _ _ _ _ _ Hinterval) Hvalid) as Htimer.
  rewrite Htimer; reflexivity.
Qed.

(** The first caller-level checkpoint for [OSTmrDel].  The relation keeps
    the source order visible: the pointer/type/ISR observations are made at
    [before], the scheduler-lock interval reaches [entry], and only then is
    the locked Timer transformer applied.  It is intentionally a
    pre-Unlock endpoint; it does not claim that [perr] has been written or
    that the caller has resumed after a possible scheduler continuation. *)
Definition tmr_del_locked_checkpoint
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (before entry : UCOS2_Verify_State)
  (pointer type_byte nesting : Z) (i : TimerID) (name : addr)
  (image : TimerImage) (ret : bool) (err : OSErrCode)
  (after : UCOS2_Verify_State) : Prop :=
  tmr_del_early_result pointer type_byte nesting = None /\
  critical_region_interval critical sg invocation before entry /\
  UCOS2_state_inv sg before /\
  UCOS2_state_inv sg entry /\
  pointer = timer_pool_addr sg i /\
  type_byte = image.(timerImageType) /\
  nesting = before.(IntrState).(intNesting) /\
  before.(TimerState).(timerImages) i = Some image /\
  entry.(TimerState).(timerImages) i = Some image /\
  tmr_del_locked_state_step sg entry i name ret err after.

Lemma tmr_del_locked_checkpoint_timer_state_eq : forall critical sg invocation
  before entry pointer type_byte nesting i name image ret err after,
  tmr_del_critical_timer_state_stable critical ->
  tmr_del_locked_checkpoint critical sg invocation before entry pointer type_byte
    nesting i name image ret err after ->
  entry.(TimerState) = before.(TimerState).
Proof.
  intros critical sg invocation before entry pointer type_byte nesting i name image ret err after
    Hstable Hcheckpoint.
  destruct Hcheckpoint as [Hearly [Hinterval [Hbefore [Hentry [Hpointer [Htype
    [Hnest [Hbefore_image [Hentry_image Hstep]]]]]]]]].
  eapply tmr_del_trace_preserves_timer_state
    with (clients := critical.(critical_region_clients))
         (observer := invocation) (stopped := false).
  - exact critical.(critical_region_client_certificates).
  - exact Hstable.
  - apply critical_region_interval_raw_trace; exact Hinterval.
  - exact Hbefore.
Qed.

Lemma tmr_del_locked_checkpoint_preserves_validity : forall critical sg invocation
  before entry pointer type_byte nesting i name image ret err after,
  tmr_unlink_profile sg ->
  timer_api_initialized before.(TimerState) ->
  tmr_del_critical_timer_state_stable critical ->
  tmr_del_locked_checkpoint critical sg invocation before entry pointer type_byte
    nesting i name image ret err after ->
  UCOS2_state_inv sg after /\ timer_api_initialized after.(TimerState).
Proof.
  intros critical sg invocation before entry pointer type_byte nesting i name image ret err after
    Hprofile Hinit Hstable Hcheckpoint.
  destruct Hcheckpoint as [Hearly [Hinterval [Hbefore [Hentry [Hpointer [Htype
    [Hnest [Hbefore_image [Hentry_image Hstep]]]]]]]]].
  assert (Htimer_eq : entry.(TimerState) = before.(TimerState)).
  { eapply tmr_del_trace_preserves_timer_state
      with (clients := critical.(critical_region_clients))
           (observer := invocation) (stopped := false).
    - exact critical.(critical_region_client_certificates).
    - exact Hstable.
    - apply critical_region_interval_raw_trace; exact Hinterval.
    - exact Hbefore. }
  assert (Hentry_init : timer_api_initialized entry.(TimerState)).
  { rewrite Htimer_eq; exact Hinit. }
  pose proof (tmr_del_locked_state_step_preserves_validity sg entry i name ret err after
    Hprofile Hentry Hentry_init Hstep) as Hpost.
  exact Hpost.
Qed.

Lemma tmr_del_locked_checkpoint_total : forall critical sg invocation
  before entry pointer type_byte nesting i name image,
  tmr_unlink_profile sg ->
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  timer_api_initialized before.(TimerState) ->
  UCOS2_state_inv sg before ->
  tmr_del_critical_timer_state_stable critical ->
  critical_region_interval critical sg invocation before entry ->
  pointer = timer_pool_addr sg i ->
  type_byte = image.(timerImageType) ->
  nesting = before.(IntrState).(intNesting) ->
  before.(TimerState).(timerImages) i = Some image ->
  tmr_del_early_result pointer type_byte nesting = None ->
  exists ret err after,
    tmr_del_locked_checkpoint critical sg invocation before entry pointer type_byte
      nesting i name image ret err after.
Proof.
  intros critical sg invocation before entry pointer type_byte nesting i name image
    Hprofile Henabled Hinit Hbefore Hstable Hinterval Hpointer Htype Hnest Himage Hearly.
  pose proof (tmr_del_trace_preserves_timer_state
    critical.(critical_region_clients) sg invocation before false entry
    critical.(critical_region_client_certificates) Hstable
    (critical_region_interval_raw_trace _ _ _ _ _ Hinterval) Hbefore) as Htimer_eq.
  pose proof (critical_region_interval_transports_resources critical sg invocation
    before entry Hinterval Hbefore) as Hentry.
  assert (Hentry_init : timer_api_initialized entry.(TimerState)).
  { rewrite Htimer_eq; exact Hinit. }
  assert (Hentry_image : entry.(TimerState).(timerImages) i = Some image).
  { rewrite Htimer_eq; exact Himage. }
  assert (Hentry_timer_config : valid_timer_configuration sg entry.(TimerState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hentry; tauto. }
  assert (Hentry_timer_state : valid_timer_state sg entry.(TimerState)).
  { apply (proj1 (timer_initialized_configuration_iff sg entry.(TimerState)
      Henabled Hentry_init)); exact Hentry_timer_config. }
  destruct (tmr_del_locked_state_step_total sg entry i name image
    Hentry_timer_state Hentry_image) as [ret [err [after Hstep]]].
  pose proof (proj1 Hentry) as Hentry_valid.
  exists ret, err, after.
  exact (conj Hearly (conj Hinterval (conj Hbefore (conj Hentry_valid
    (conj Hpointer (conj Htype (conj Hnest (conj Himage
      (conj Hentry_image Hstep))))))))).
Qed.

(** Unlink and Free consume only the mutable pool body. Type and service
    views remain outside this call footprint; actual loan acquisition and
    return still require the shared-region protocol. *)
Definition tmr_del_unlink_pool_body_post (sg : StableGlobVars)
  (s : GlobTimerState) (i : TimerID) : Assertion :=
  EX post, coq_prop (timer_unlink sg s i = Some post /\
    valid_timer_configuration sg post /\ timer_api_initialized post) &&
    timer_pool_rep_without_types sg post.

Lemma tmr_del_unlink_pool_body_spec_consequence : forall sg s i (R : Assertion),
  tmr_unlink_layout -> tmr_unlink_profile sg -> valid_timer_configuration sg s ->
  timer_api_initialized s -> tmr_unlink_running s i ->
  timer_pool_rep_without_types sg s ** R |--
  EX match_time, EX next, EX prev, EX first, EX entries, EX F,
    tmr_unlink_raw_pre (timer_pool_addr sg i) sg.(g_OSTmrWheelTbl)
      match_time next prev first entries F **
    (tmr_unlink_raw_post (timer_pool_addr sg i) sg.(g_OSTmrWheelTbl)
       match_time next prev first entries F -*
      (tmr_del_unlink_pool_body_post sg s i ** R)).
Proof.
  intros sg s i R Hlayout Hprofile Hvalid Hinit [t [Ht Hrunning]].
  pose proof Hprofile as [Henabled [Hnames [Hcapacity [Hwheel_size [Hpool Hwheel_region]]]]].
  pose proof Hlayout as [_ [_ [_ [_ [Hfirst_addr [Hentries_addr Hsizeof]]]]]].
  pose proof (proj1 (timer_initialized_configuration_iff sg s Henabled Hinit) Hvalid) as Hstate.
  destruct (valid_timer_state_running_position sg s i t Hstate Ht Hrunning)
    as [n [row [old [Hi [Hrow [Hin Hn]]]]]].
  pose proof Hstate as [_ [Hwheel [_ [_ [_ [_ [_ [Hused _]]]]]]]].
  pose proof Hwheel as [_ [Hnd _]].
  pose proof (timer_wheel_row_nodup _ _ _ Hnd Hrow) as Hrownd.
  pose proof (tmr_unlink_profile_pool_region sg Hprofile) as Hpool_region.
  pose proof (tmr_unlink_profile_object_size sg Hprofile) as Hobject_size.
  assert (Haddress_bounds : forall j, In j row ->
    0 < timer_pool_addr sg j /\ timer_pool_addr sg j + 40 <= 4294967296).
  { intros j Hj.
    pose proof (timer_pool_addr_in_range sg j Hpool_region
      (timer_wheel_row_ids_in_range sg s n row j Hstate Hrow Hj)) as Hbounds.
    rewrite Hobject_size in Hbounds; exact Hbounds. }
  pose proof (Haddress_bounds i Hin) as Htarget_bounds.
  assert (Hnonnull : forall j, In j row -> timer_pool_addr sg j <> 0)
    by (intros j Hj; pose proof (Haddress_bounds j Hj); lia).
  destruct (Hused i t Ht) as [Hobject_valid _].
  pose proof (timer_used_image_eq sg s i t old Hstate Ht Hi) as Himage.
  assert (Hmatch_range : 0 <= timerImageMatch old < 4294967296).
  { rewrite Himage; cbn [timer_object_image].
    destruct Hobject_valid as [_ [_ [Hmatch _]]]; exact Hmatch. }
  assert (Hspoke : timer_spoke (osKernelConfig sg) (timerImageMatch old) = timerImageMatch old mod 7).
  { unfold timer_spoke, Ucos2Verify.lib.kernel_resources.kernel_u16; rewrite Hwheel_size.
    rewrite Z.mod_small; [reflexivity|pose proof (tmr_unlink_spoke_in_range (timerImageMatch old)); lia]. }
  assert (Hindex : Z.of_nat n = timerImageMatch old mod 7).
  { rewrite Hn, Hspoke, Z2Nat.id; [reflexivity|pose proof (tmr_unlink_spoke_in_range (timerImageMatch old)); lia]. }
  destruct (tmr_unlink_row_entries_decrease sg s n row i Hprofile Hstate Hrow Hin)
    as [Hentries_bounds Hentries].
  destruct (tmr_unlink_row_neighbor_facts__configured_refinement sg s n row i old Hprofile Hstate Hrow Hin Hi)
    as [Hneighbor_bounds [Hprev [Hnext Hdistinct]]].
  destruct (tmr_unlink_images_fields_split_merge__configured_refinement false sg (timerImages s) i old row
    Hlayout Hnames Hi Hprev Hnext Hdistinct) as [Fimages [Himages_pre Himages_post]].
  cbn [tmr_unlink_object_view] in Himages_pre, Himages_post.
  destruct (tmr_unlink_configured_successor sg s i Hprofile Hvalid Hinit
    (ex_intro _ t (conj Ht Hrunning))) as [post [Hstep [Hpost_valid Hpost_init]]].
  assert (Hnth : nth n (timerWheel s) nil = row) by (eapply nth_error_nth; exact Hrow).
  pose proof Hstep as Hstep_fields.
  unfold timer_unlink in Hstep_fields; rewrite Ht, Hi, <- Hn, Hnth in Hstep_fields.
  injection Hstep_fields as Hpost_eq.
  assert (Hpost_rep : timer_pool_rep_without_types sg post =
    store_map (fun j v => timer_object_rep_without_type (osKernelConfig sg) (timer_pool_addr sg j) v)
      (timer_wheel_unlink_images sg (timerImages s) i old row) **
    timer_wheel_rep_from sg (g_OSTmrWheelTbl sg)
      (timer_wheel_update (timerWheel s) n (remove Z.eq_dec i row)) **
    sg.(g_OSTmrFreeList) # Ptr |-> timer_id_pointer sg s.(timerFree) **
    sg.(g_OSTmrFree) # UShort |-> s.(timerFreeCount) **
    sg.(g_OSTmrUsed) # UShort |-> s.(timerUsedCount)).
  { rewrite <- Hpost_eq; reflexivity. }
  assert (Hfirst : timer_id_pointer sg (remove Z.eq_dec i row) =
    if Z.eq_dec (timer_id_pointer sg row) (timer_pool_addr sg i)
      then timerImageNext old else timer_id_pointer sg row).
  { apply tmr_unlink_row_first_after_remove__configured_refinement; try assumption.
    exact (proj1 (timer_wheel_row_node_pointers sg s n row i old Hwheel Hrow Hin Hi)). }
  assert (Hraw_bounds : tmr_unlink_wheel_size /\
    0 < timer_pool_addr sg i /\ timer_pool_addr sg i + 40 <= 4294967296 /\
    0 < g_OSTmrWheelTbl sg /\ g_OSTmrWheelTbl sg + 56 <= 4294967296 /\
    0 <= timerImageMatch old < 4294967296 /\ 0 <= Z.of_nat (List.length row) < 65536 /\
    tmr_unlink_neighbor_bounds (timer_pool_addr sg i) (timerImageNext old) (timerImagePrev old)
      (timer_id_pointer sg row)).
  { unfold kernel_region_valid in Hwheel_region; cbn in Hwheel_region; intuition lia. }
  set (Fraw := Fimages ** tmr_unlink_wheel_without_spoke sg (g_OSTmrWheelTbl sg) (timerWheel s) n **
    sg.(g_OSTmrFreeList) # Ptr |-> timer_id_pointer sg s.(timerFree) **
    sg.(g_OSTmrFree) # UShort |-> s.(timerFreeCount) **
    sg.(g_OSTmrUsed) # UShort |-> s.(timerUsedCount) ** R).
  Exists (timerImageMatch old) (timerImageNext old) (timerImagePrev old)
    (timer_id_pointer sg row) (Z.of_nat (List.length row)) Fraw.
  assert (Hwand : emp |--
    tmr_unlink_raw_post (timer_pool_addr sg i) (g_OSTmrWheelTbl sg) (timerImageMatch old)
      (timerImageNext old) (timerImagePrev old) (timer_id_pointer sg row) (Z.of_nat (List.length row)) Fraw
      -* (tmr_del_unlink_pool_body_post sg s i ** R)).
  { apply_sepcon_adjoint.
    unfold tmr_unlink_raw_post, tmr_del_unlink_pool_body_post, Fraw.
    Exists post; rewrite Hpost_rep.
    entailer!.
    sepcon_right_assoc.
    sep_apply_r_atomic Himages_post; sepcon_right_assoc.
    sep_apply_r_atomic (tmr_unlink_wheel_merge_updated_spoke sg (timerWheel s) n row
      (remove Z.eq_dec i row) (g_OSTmrWheelTbl sg) Hrow).
    rewrite Hfirst_addr, Hentries_addr; unfold tmr_unlink_spoke_addr; rewrite <- Hindex, Hfirst.
    entailer!.
    rewrite Hentries; entailer!. }
  assert (Hpre : timer_pool_rep_without_types sg s ** R |--
    tmr_unlink_raw_pre (timer_pool_addr sg i) (g_OSTmrWheelTbl sg) (timerImageMatch old)
      (timerImageNext old) (timerImagePrev old) (timer_id_pointer sg row) (Z.of_nat (List.length row)) Fraw).
  { unfold timer_pool_rep_without_types, timer_images_rep_without_types, tmr_unlink_raw_pre, Fraw.
    sep_apply_l_atomic Himages_pre.
    sep_apply_l_atomic (tmr_unlink_wheel_split_spoke sg (timerWheel s) n row (g_OSTmrWheelTbl sg) Hrow).
    rewrite Hfirst_addr, Hentries_addr; unfold tmr_unlink_spoke_addr; rewrite <- Hindex.
    entailer!. }
  sep_apply_l_atomic Hpre; entailer!.
Qed.

(** Rejoin the body with the region's unchanged type and service views.
    Their equality comes from the actual delete transition, not a stability
    premise or an independently reusable full-heap handle. *)
Lemma tmr_del_pool_body_merge_completion : forall sg before i name ret err timers,
  tmr_unlink_profile sg -> UCOS2_state_inv sg before ->
  timer_api_initialized before.(TimerState) ->
  timer_delete_locked sg before.(TimerState) i name = Some (ret, err, timers) ->
  timer_pool_rep_without_types sg timers ** UCOS2_raw_rep_missing_timer_pool_body sg before |--
  UCOS2_inv sg (replace_TimerS timers before).
Proof.
  intros sg before i name ret err timers Hprofile Hvalid Hinit Hstep.
  pose proof Hprofile as [He [_ [Hcap _]]].
  assert (Htimer : valid_timer_configuration sg before.(TimerState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  destruct (timer_delete_locked_preserves_configuration sg before.(TimerState) i
    name ret err timers He ltac:(lia) (tmr_unlink_profile_pool_region sg Hprofile)
    Htimer Hinit Hstep) as [Htimers Hinitialized].
  assert (Hpost : UCOS2_state_inv sg (replace_TimerS timers before)).
  { apply UCOS2_replace_timer_preserves_validity; [exact Hvalid|exact Htimers| |].
    - intros _ _; exact Hinitialized.
    - eapply timer_delete_locked_name_references; exact Hstep. }
  apply UCOS2_inv_merge_updated_timer_pool_body; try assumption.
  - eapply timer_delete_locked_image_types_eq; exact Hstep.
  - eapply timer_delete_locked_service_globals_eq; exact Hstep.
Qed.

(** These are the physical endpoints of BorrowableRegion's Borrow/Return
    protocol, not additional contracts for CPU primitives.  Borrow starts
    with an already-owned full invariant.  Return uses the actual delete
    transformer, and so cannot return stale pool bytes or obtain the pool
    from the ISR complement alone.  Source-continuation/mask binding is
    still required at the actual Save/Restore call sites. *)
Lemma tmr_del_pool_body_borrow_share : forall sg s,
  tmr_unlink_profile sg -> timer_api_initialized s.(TimerState) ->
  UCOS2_inv sg s |--
    timer_region_share_rep sg s false true ** timer_region_share_rep sg s true false.
Proof.
  intros sg s Hprofile Hinit.
  rewrite (UCOS2_inv_split_timer_pool_body sg s (proj1 Hprofile) Hinit).
  unfold timer_region_share_rep; simpl; entailer!.
Qed.

Lemma tmr_del_pool_body_return_share : forall sg before i name ret err timers,
  tmr_unlink_profile sg -> UCOS2_state_inv sg before ->
  timer_api_initialized before.(TimerState) ->
  timer_delete_locked sg before.(TimerState) i name = Some (ret, err, timers) ->
  timer_pool_rep_without_types sg timers ** UCOS2_raw_rep_missing_timer_pool_body sg before |--
    timer_region_share_rep sg (replace_TimerS timers before) true true.
Proof.
  intros sg before i name ret err timers Hprofile Hvalid Hinit Hdelete.
  pose proof Hprofile as [He [_ [Hcap _]]].
  assert (Htimer : valid_timer_configuration sg before.(TimerState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  destruct (timer_delete_locked_preserves_configuration sg before.(TimerState) i
    name ret err timers He ltac:(lia) (tmr_unlink_profile_pool_region sg Hprofile)
    Htimer Hinit Hdelete) as [_ Hinitialized].
  rewrite (timer_region_full_share sg (replace_TimerS timers before) He Hinitialized).
  eapply tmr_del_pool_body_merge_completion; eassumption.
Qed.

(** A reusable Timer-specific ownership boundary for callers that borrow the
    mutable pool body.  The two fields below are the actual spatial endpoints
    proved above; they deliberately do not mention CPU save words, IRQ masks,
    or an observation token.  Those caller/platform obligations remain an
    outer contract and cannot be manufactured from this pool interface. *)
Record TmrDelPoolBodyLoanInterface (sg : StableGlobVars) : Type := {
  tmr_del_loan_profile : tmr_unlink_profile sg;
  tmr_del_loan_open : forall s,
    timer_api_initialized s.(TimerState) ->
    UCOS2_inv sg s |--
      timer_region_share_rep sg s false true **
      timer_region_share_rep sg s true false;
  tmr_del_loan_complete : forall before i name ret err timers,
    UCOS2_state_inv sg before ->
    timer_api_initialized before.(TimerState) ->
    timer_delete_locked sg before.(TimerState) i name = Some (ret, err, timers) ->
    timer_pool_rep_without_types sg timers **
      UCOS2_raw_rep_missing_timer_pool_body sg before |--
      timer_region_share_rep sg (replace_TimerS timers before) true true
}.

Definition tmr_del_pool_body_loan_interface
  (sg : StableGlobVars) (Hprofile : tmr_unlink_profile sg) :
  TmrDelPoolBodyLoanInterface sg.
Proof.
  refine {| tmr_del_loan_profile := Hprofile;
            tmr_del_loan_open := _;
            tmr_del_loan_complete := _ |}.
  - intros s Hinit.
    exact (tmr_del_pool_body_borrow_share sg s Hprofile Hinit).
  - intros before i name ret err timers Hvalid Hinit Hdelete.
    exact (tmr_del_pool_body_return_share sg before i name ret err timers
      Hprofile Hvalid Hinit Hdelete).
Defined.

(** Resource composition at a real interference point: OSIntExit's locked
    preparation returns the updated interrupt counters, while Del returns
    its completed pool body.  The two disjoint pieces reconstruct the
    combined state, not the pre-interrupt state.  This does not yet supply
    the platform/region transfer at interrupt entry and return. *)
Lemma tmr_del_pool_body_merge_after_locked_interrupt :
  forall sg before observed i name ret err timers,
  tmr_unlink_profile sg -> UCOS2_state_inv sg before ->
  timer_api_initialized before.(TimerState) -> before.(IntrState).(lockNesting) <> 0 ->
  timer_delete_locked sg before.(TimerState) i name = Some (ret, err, timers) ->
  timer_pool_rep_without_types sg timers **
    store_int_state sg (interrupt_exit_state observed before.(IntrState)) **
    UCOS2_raw_rep_missing_timer_pool_body_interrupt sg before |--
  UCOS2_inv sg (replace_TimerS timers (os_int_exit_ready_checkpoint observed before)).
Proof.
  intros sg before observed i name ret err timers Hprofile Hvalid Hinit Hlocked Hstep.
  assert (Htimer : (os_int_exit_ready_checkpoint observed before).(TimerState) = before.(TimerState)).
  { rewrite (os_int_exit_locked_checkpoint_eq observed before Hlocked); reflexivity. }
  assert (Hcurrent : UCOS2_state_inv sg (os_int_exit_ready_checkpoint observed before))
    by (apply os_int_exit_ready_checkpoint_preserves_validity; exact Hvalid).
  assert (Hinitialized : timer_api_initialized
    (os_int_exit_ready_checkpoint observed before).(TimerState)) by (rewrite Htimer; exact Hinit).
  assert (Hdelete : timer_delete_locked sg
    (os_int_exit_ready_checkpoint observed before).(TimerState) i name = Some (ret, err, timers))
    by (rewrite Htimer; exact Hstep).
  sep_apply_l_atomic (os_int_exit_locked_merge_timer_region sg observed before Hvalid Hlocked).
  unfold UCOS2_inv_missing_timer_pool_body; Intros.
  sep_apply_l_atomic (tmr_del_pool_body_merge_completion sg (os_int_exit_ready_checkpoint observed before)
    i name ret err timers Hprofile Hcurrent Hinitialized Hdelete).
  entailer!.
Qed.

(** Joint control/resource endpoint. The control step comes from the actual
    paired ISR envelope; its descriptor alone lends no bytes. The spatial
    premise separately consumes Del's completed body and the ISR's current
    complement. 'continuation' is the saved caller to resume after the port
    return, not an assertion that the ARM exception return is proved here.

    Unlike the positive-lock specialization above, the source no-selection
    branch also covers OSRunning=false. Every non-interrupt field is taken
    from the real ISR endpoint [entry], never rolled back to a pre-ISR state. *)
Lemma tmr_del_pool_body_merge_at_interrupt_exit :
  forall sg entry observed invocation origin handler continuation counters i name ret err timers,
  tmr_unlink_profile sg -> UCOS2_state_inv sg entry ->
  timer_api_initialized entry.(TimerState) ->
  kernel_control_step (KernelExitInterrupt observed)
    (KernelInterrupt handler (KernelCaller invocation origin)) entry.(IntrState)
    continuation counters false ->
  timer_delete_locked sg entry.(TimerState) i name = Some (ret, err, timers) ->
  timer_pool_rep_without_types sg timers ** store_int_state sg counters **
    UCOS2_raw_rep_missing_timer_pool_body_interrupt sg entry |--
  coq_prop (continuation = KernelCaller invocation origin /\
    os_int_exit_requests_switch observed entry = false) &&
  UCOS2_inv sg (replace_TimerS timers (os_int_exit_ready_checkpoint observed entry)).
Proof.
  intros sg entry observed invocation origin handler continuation counters i name ret err timers
    Hprofile Hvalid Hinit Hcontrol Hdelete.
  destruct (kernel_control_step_deterministic (KernelExitInterrupt observed)
    (KernelInterrupt handler (KernelCaller invocation origin)) entry.(IntrState)
    continuation counters false (KernelCaller invocation origin)
    (interrupt_exit_state observed entry.(IntrState))
    (interrupt_exit_requests_schedule observed entry.(IntrState)) Hcontrol
    (KernelControlExit handler observed (KernelCaller invocation origin) entry.(IntrState)))
    as [Hcontinuation [Hcounters Hschedule]].
  subst continuation counters; symmetry in Hschedule.
  assert (Hnoswitch : os_int_exit_requests_switch observed entry = false)
    by (apply os_int_exit_no_schedule_no_switch; exact Hschedule).
  assert (Htimer : (os_int_exit_ready_checkpoint observed entry).(TimerState) = entry.(TimerState)).
  { rewrite (os_int_exit_no_schedule_checkpoint_eq observed entry Hschedule); reflexivity. }
  assert (Hcurrent : UCOS2_state_inv sg (os_int_exit_ready_checkpoint observed entry))
    by (apply os_int_exit_ready_checkpoint_preserves_validity; exact Hvalid).
  assert (Hinitialized : timer_api_initialized
    (os_int_exit_ready_checkpoint observed entry).(TimerState)) by (rewrite Htimer; exact Hinit).
  assert (Hstep : timer_delete_locked sg
    (os_int_exit_ready_checkpoint observed entry).(TimerState) i name = Some (ret, err, timers))
    by (rewrite Htimer; exact Hdelete).
  sep_apply_l_atomic (os_int_exit_no_schedule_merge_timer_region sg observed entry Hvalid Hschedule).
  unfold UCOS2_inv_missing_timer_pool_body; Intros.
  sep_apply_l_atomic (tmr_del_pool_body_merge_completion sg (os_int_exit_ready_checkpoint observed entry)
    i name ret err timers Hprofile Hcurrent Hinitialized Hstep).
  entailer!.
Qed.

(** Consume the concrete Tick proof above at the same resource endpoint.
    The complement is indexed by [after], so actual Task/Event/Tick writes
    remain visible. No proof here frames a borrowed body through Tick's
    old full-heap Save declaration or derives an outside-to-heap rule. *)
Lemma tmr_del_pool_body_merge_after_tick_interrupt :
  forall app value counter invocation origin handler observed sg before after i name ret err timers,
  tmr_unlink_profile sg -> UCOS2_state_inv sg before ->
  timer_api_initialized before.(TimerState) ->
  kernel_interrupt_nesting_agrees observed (KernelCaller invocation origin) before.(IntrState) ->
  (observed = true -> before.(IntrState).(lockNesting) <> 0) ->
  kernel_client_step (tmr_del_tick_client app value counter invocation origin) sg
    (replace_IntrS (interrupt_enter_state observed before.(IntrState)) before) after ->
  timer_delete_locked sg before.(TimerState) i name = Some (ret, err, timers) ->
  timer_pool_rep_without_types sg timers ** store_int_state sg before.(IntrState) **
    UCOS2_raw_rep_missing_timer_pool_body_interrupt sg after |--
  coq_prop (kernel_control_step (KernelExitInterrupt observed)
    (KernelInterrupt handler (KernelCaller invocation origin)) after.(IntrState)
    (KernelCaller invocation origin) before.(IntrState) false) &&
  UCOS2_inv sg (replace_TimerS timers (os_int_exit_ready_checkpoint observed after)).
Proof.
  intros app value counter invocation origin handler observed sg before after i name ret err timers
    Hprofile Hvalid Hinit Hagrees Hlocked Hbody Hdelete.
  destruct (tmr_del_tick_interrupt_control app value counter invocation origin handler observed
    sg before after Hvalid Hagrees Hlocked Hbody) as [Hafter [Htimer Hcontrol]].
  assert (Hinitialized : timer_api_initialized after.(TimerState))
    by (rewrite Htimer; exact Hinit).
  assert (Hstep : timer_delete_locked sg after.(TimerState) i name = Some (ret, err, timers))
    by (rewrite Htimer; exact Hdelete).
  sep_apply_l_atomic (tmr_del_pool_body_merge_at_interrupt_exit sg after observed invocation origin
    handler (KernelCaller invocation origin) before.(IntrState) i name ret err timers
    Hprofile Hafter Hinitialized Hcontrol Hstep).
  entailer!.
Qed.

Lemma tmr_del_stopped_free_body_spec_consequence : forall sg s i old p (LitMap : string -> Z),
  tmr_free_bindings sg p -> p = timer_pool_addr sg i ->
  valid_timer_configuration sg s -> timer_api_initialized s ->
  s.(timerImages) i = Some old ->
  (old.(timerImageState) = 1 \/ old.(timerImageState) = 2) ->
  timer_pool_rep_without_types sg s ** GlobalStrings LitMap |--
  coq_prop (timer_delete_locked sg s i (LitMap "?") =
    Some (true, OS_ERR_NONE, timer_release sg s i old (LitMap "?"))) &&
  ((tmr_free_write_pre p (timer_id_pointer sg s.(timerFree))
      s.(timerUsedCount) s.(timerFreeCount) ** GlobalStrings LitMap) **
   ((tmr_free_write_post p (timer_id_pointer sg s.(timerFree)) s.(timerUsedCount)
       s.(timerFreeCount) (LitMap "?") ** GlobalStrings LitMap) -*
    (tmr_free_body_post sg s i old (LitMap "?") ** GlobalStrings LitMap))).
Proof.
  intros sg s i old p LitMap Hbindings Hp Hvalid Hinit Hlookup Hstopped.
  pose proof Hbindings as [Hcfg _].
  assert (He : cfgTimerEnabled (osKernelConfig sg) = true) by (rewrite Hcfg; reflexivity).
  pose proof (proj1 (timer_initialized_configuration_iff sg s He Hinit) Hvalid) as Hstate.
  destruct (valid_timer_state_nonunused_image sg s i old Hstate Hlookup ltac:(lia))
    as [t [Ht Hencode]].
  assert (Hnotrun : timerState t <> TimerRunning).
  { intro E; rewrite E in Hencode; simpl in Hencode; lia. }
  assert (Hinput : tmr_free_valid_input sg s i t old p).
  { exact (conj Hbindings (conj Hp (conj Hinit (conj Ht (conj Hlookup Hnotrun))))). }
  assert (Hdelete : timer_delete_locked sg s i (LitMap "?") =
    Some (true, OS_ERR_NONE, timer_release sg s i old (LitMap "?"))).
  { unfold timer_delete_locked; rewrite Hlookup.
    destruct Hstopped as [Hstopped|Hstopped]; rewrite Hstopped; reflexivity. }
  sep_apply_l_atomic (tmr_free_body_spec_consequence sg s i t old p LitMap Hinput Hvalid).
  entailer!.
Qed.

Lemma tmr_del_unlink_free_pool_body_spec_consequence : forall sg before i image p
  (LitMap : string -> Z),
  tmr_free_bindings sg p -> p = timer_pool_addr sg i ->
  before.(timerImages) i = Some image -> image.(timerImageState) = 3 ->
  tmr_del_unlink_pool_body_post sg before i ** GlobalStrings LitMap |--
  EX stopped, EX old,
    coq_prop (timer_unlink sg before i = Some stopped /\
      timer_delete_locked sg before i (LitMap "?") =
        Some (true, OS_ERR_NONE, timer_release sg stopped i old (LitMap "?"))) &&
    ((tmr_free_write_pre p (timer_id_pointer sg stopped.(timerFree))
        stopped.(timerUsedCount) stopped.(timerFreeCount) ** GlobalStrings LitMap) **
     ((tmr_free_write_post p (timer_id_pointer sg stopped.(timerFree))
         stopped.(timerUsedCount) stopped.(timerFreeCount) (LitMap "?") **
       GlobalStrings LitMap) -*
      (tmr_free_body_post sg stopped i old (LitMap "?") ** GlobalStrings LitMap))).
Proof.
  intros sg before i image p LitMap Hbindings Hp Himage Hrunning.
  unfold tmr_del_unlink_pool_body_post; Intros stopped.
  match goal with H : timer_unlink sg before i = Some stopped /\ _ |- _ =>
    destruct H as [Hstep [Hvalid Hinit]] end.
  destruct (timer_unlink_clears_links_and_stops sg before i stopped Hstep)
    as [t [old [Ht [Hold [Hstopped Hrest]]]]].
  assert (Hinput : tmr_free_valid_input sg stopped i t old p).
  { unfold tmr_free_valid_input.
    refine (conj Hbindings (conj Hp (conj Hinit (conj Ht (conj Hold _))))).
    rewrite Hstopped; discriminate. }
  assert (Hdelete : timer_delete_locked sg before i (LitMap "?") =
    Some (true, OS_ERR_NONE, timer_release sg stopped i old (LitMap "?"))).
  { unfold timer_delete_locked; rewrite Himage, Hrunning; cbn [Z.eqb].
    rewrite Hstep, Hold; reflexivity. }
  Exists stopped old.
  sep_apply_l_atomic (tmr_free_body_spec_consequence sg stopped i t old p
    LitMap Hinput Hvalid).
  entailer!.
Qed.

(** Instantiate the proved three-cell OSIntExit contract, keeping the
    caller's completed Timer body in its continuation rather than giving
    it to the ISR. The postcondition consumes the actual C result and
    restores the current complement; all non-Timer writes are retained.
    This is a call-site consequence, not an interrupt acquisition rule. *)
Lemma tmr_del_interrupt_exit_spec_consequence :
  forall platform sg invocation origin entry i name ret err timers,
  tmr_unlink_profile sg -> UCOS2_state_inv sg entry ->
  timer_api_initialized entry.(TimerState) ->
  os_int_exit_no_schedule_addresses sg (&("OSRunning")) (&("OSIntNesting")) (&("OSLockNesting")) ->
  interrupt_exit_requests_schedule entry.(SchedState).(isRunning) entry.(IntrState) = false ->
  timer_delete_locked sg entry.(TimerState) i name = Some (ret, err, timers) ->
  interrupt_platform_running platform invocation origin 192 **
    UCOS2_inv_missing_timer_pool_body sg entry ** timer_pool_rep_without_types sg timers |--
  (coq_prop (os_int_exit_no_schedule_addresses sg
      (&("OSRunning")) (&("OSIntNesting")) (&("OSLockNesting"))) &&
   os_int_exit_no_schedule_pre platform sg invocation origin
      entry.(SchedState).(isRunning) entry.(IntrState)) **
  (os_int_exit_no_schedule_post platform sg invocation origin
      entry.(SchedState).(isRunning) entry.(IntrState) -*
   (interrupt_platform_running platform invocation origin 192 **
    UCOS2_inv sg (replace_TimerS timers
      (os_int_exit_ready_checkpoint entry.(SchedState).(isRunning) entry)))).
Proof.
  intros platform sg invocation origin entry i name ret err timers
    Hprofile Hvalid Hinit Haddresses Hdisabled Hdelete.
  assert (Htimer : (os_int_exit_ready_checkpoint entry.(SchedState).(isRunning) entry).(TimerState) =
    entry.(TimerState)).
  { rewrite (os_int_exit_no_schedule_checkpoint_eq _ _ Hdisabled); reflexivity. }
  assert (Hcurrent : UCOS2_state_inv sg
    (os_int_exit_ready_checkpoint entry.(SchedState).(isRunning) entry))
    by (apply os_int_exit_ready_checkpoint_preserves_validity; exact Hvalid).
  assert (Hinitialized : timer_api_initialized
    (os_int_exit_ready_checkpoint entry.(SchedState).(isRunning) entry).(TimerState))
    by (rewrite Htimer; exact Hinit).
  assert (Hstep : timer_delete_locked sg
    (os_int_exit_ready_checkpoint entry.(SchedState).(isRunning) entry).(TimerState) i name =
    Some (ret, err, timers)) by (rewrite Htimer; exact Hdelete).
  assert (Hreturn : os_int_exit_timer_residual sg entry ** timer_pool_rep_without_types sg timers |--
    os_int_exit_no_schedule_post platform sg invocation origin
        entry.(SchedState).(isRunning) entry.(IntrState) -*
    (interrupt_platform_running platform invocation origin 192 **
     UCOS2_inv sg (replace_TimerS timers
       (os_int_exit_ready_checkpoint entry.(SchedState).(isRunning) entry)))).
  { apply_sepcon_adjoint.
    sep_apply_l_atomic (os_int_exit_timer_region_call_post platform sg invocation origin entry
      Hvalid Hdisabled).
    unfold UCOS2_inv_missing_timer_pool_body; Intros.
    sep_apply_l_atomic (tmr_del_pool_body_merge_completion sg
      (os_int_exit_ready_checkpoint entry.(SchedState).(isRunning) entry) i name ret err timers
      Hprofile Hcurrent Hinitialized Hstep).
    entailer!. }
  sep_apply_l_atomic (os_int_exit_timer_region_call_pre platform sg invocation origin entry Hdisabled).
  Intros; sep_apply_l_atomic Hreturn; entailer!.
Qed.

Lemma tmr_del_tick_interrupt_exit_spec_consequence :
  forall app value counter invocation origin observed platform sg before after i name ret err timers,
  tmr_unlink_profile sg -> UCOS2_state_inv sg before ->
  timer_api_initialized before.(TimerState) -> observed = before.(SchedState).(isRunning) ->
  os_int_exit_no_schedule_addresses sg (&("OSRunning")) (&("OSIntNesting")) (&("OSLockNesting")) ->
  (observed = true -> before.(IntrState).(lockNesting) <> 0) ->
  kernel_client_step (tmr_del_tick_client app value counter invocation origin) sg
    (replace_IntrS (interrupt_enter_state observed before.(IntrState)) before) after ->
  timer_delete_locked sg before.(TimerState) i name = Some (ret, err, timers) ->
  interrupt_platform_running platform invocation origin 192 **
    UCOS2_inv_missing_timer_pool_body sg after ** timer_pool_rep_without_types sg timers |--
  (coq_prop (os_int_exit_no_schedule_addresses sg
      (&("OSRunning")) (&("OSIntNesting")) (&("OSLockNesting"))) &&
   os_int_exit_no_schedule_pre platform sg invocation origin
      after.(SchedState).(isRunning) after.(IntrState)) **
  (os_int_exit_no_schedule_post platform sg invocation origin
      after.(SchedState).(isRunning) after.(IntrState) -*
   (interrupt_platform_running platform invocation origin 192 **
    UCOS2_inv sg (replace_TimerS timers
      (os_int_exit_ready_checkpoint after.(SchedState).(isRunning) after)))).
Proof.
  intros app value counter invocation origin observed platform sg before after i name ret err timers
    Hprofile Hvalid Hinit Hobserved Haddresses Hlocked Hbody Hdelete.
  assert (Hentered : UCOS2_state_inv sg
    (replace_IntrS (interrupt_enter_state observed before.(IntrState)) before)).
  { rewrite UCOS2_validity_replace_interrupt_eq; exact Hvalid. }
  pose proof (kernel_client_preserves_validity
    (tmr_del_tick_client app value counter invocation origin)
    (tmr_del_tick_client_certificate app value counter invocation origin) sg
    (replace_IntrS (interrupt_enter_state observed before.(IntrState)) before) after
    Hentered Hbody) as Hafter.
  destruct (tmr_del_tick_client_intr_timer_eq app value counter invocation origin sg
    (replace_IntrS (interrupt_enter_state observed before.(IntrState)) before) after Hbody Hentered)
    as [_ Htimer].
  change (after.(TimerState) = before.(TimerState)) in Htimer.
  destruct (tmr_del_tick_interrupt_exit_guard app value counter invocation origin observed sg
    before after Hvalid Hobserved Hlocked Hbody) as [_ Hdisabled].
  apply (tmr_del_interrupt_exit_spec_consequence platform sg invocation origin after i name ret err timers);
    try assumption; rewrite Htimer; assumption.
Qed.

(** Connect the actual smaller Tick postcondition to the actual smaller
    OSIntExit precondition. The Hook's smaller C contract is still an
    explicit dependency of Tick; this theorem does not validate that
    external implementation, region acquisition or the port return. *)
Lemma tmr_del_tick_post_interrupt_exit_spec_consequence :
  forall app value counter counter_address invocation origin region_entry observed platform
    critical sg before i name ret err timers X,
  tmr_unlink_profile sg -> UCOS2_state_inv sg before ->
  timer_api_initialized before.(TimerState) -> observed = before.(SchedState).(isRunning) ->
  time_tick_entry sg invocation origin
    (replace_IntrS (interrupt_enter_state observed before.(IntrState)) before) ->
  os_int_exit_no_schedule_addresses sg (&("OSRunning")) (&("OSIntNesting")) (&("OSLockNesting")) ->
  (observed = true -> before.(IntrState).(lockNesting) <> 0) ->
  timer_delete_locked sg before.(TimerState) i name = Some (ret, err, timers) ->
  time_tick_complement_post platform critical app sg invocation origin region_entry
    (replace_IntrS (interrupt_enter_state observed before.(IntrState)) before)
    value counter_address counter X ** timer_pool_rep_without_types sg timers |--
  EX app_after counter_after hook_state,
    coq_prop (X (time_tick_serialized_after_hook sg hook_state)) &&
    (time_tick_complement_client_frame critical app sg invocation region_entry app_after counter_address counter_after **
     (coq_prop (os_int_exit_no_schedule_addresses sg
        (&("OSRunning")) (&("OSIntNesting")) (&("OSLockNesting"))) &&
      os_int_exit_no_schedule_pre platform sg invocation origin
        (time_tick_serialized_after_hook sg hook_state).(SchedState).(isRunning)
        (time_tick_serialized_after_hook sg hook_state).(IntrState)) **
     (os_int_exit_no_schedule_post platform sg invocation origin
        (time_tick_serialized_after_hook sg hook_state).(SchedState).(isRunning)
        (time_tick_serialized_after_hook sg hook_state).(IntrState) -*
      (interrupt_platform_running platform invocation origin 192 **
       UCOS2_inv sg (replace_TimerS timers
         (os_int_exit_ready_checkpoint
           (time_tick_serialized_after_hook sg hook_state).(SchedState).(isRunning)
           (time_tick_serialized_after_hook sg hook_state)))))).
Proof.
  intros app value counter counter_address invocation origin region_entry observed platform
    critical sg before i name ret err timers X Hprofile Hvalid Hinit Hobserved Hentry
    Haddresses Hlocked Hdelete.
  unfold time_tick_complement_post; Intros app_after counter_after hook_state.
  match goal with H : time_tick_hook_result _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hhook HX] end.
  assert (Hbody : kernel_client_step (tmr_del_tick_client app value counter invocation origin) sg
    (replace_IntrS (interrupt_enter_state observed before.(IntrState)) before)
    (time_tick_serialized_after_hook sg hook_state)).
  { split; [exact Hentry|]. split; [reflexivity|].
    exists app_after, counter_after, hook_state; split; [exact Hhook|reflexivity]. }
  unfold time_tick_complement_owned.
  Exists app_after counter_after hook_state.
  apply _derivable1_andp_intros; [entailer!|].
  cancel (time_tick_complement_client_frame critical app sg invocation region_entry
    app_after counter_address counter_after).
  sep_apply (tmr_del_tick_interrupt_exit_spec_consequence app value counter invocation origin
    observed platform sg before (time_tick_serialized_after_hook sg hook_state) i name ret err timers
    Hprofile Hvalid Hinit Hobserved Haddresses Hlocked Hbody Hdelete).
  entailer!.
Qed.

(** Del calls the full scheduler contract only after returning its actual
    observation cells. The post bridge exposes the newly acquired state;
    no Timer or Interrupt fragment is framed beside a second full heap.
    These are consequences of the existing region representation contract,
    not additional CPU/BSP assumptions or interval-stability theorems. *)
Lemma tmr_del_lock_pre_from_inv : forall platform critical sg invocation origin mask before,
  interrupt_platform_running platform invocation origin mask ** UCOS2_inv sg before |--
  os_sched_lock_pre platform critical sg invocation origin mask before.
Proof.
  intros; unfold os_sched_lock_pre, os_sched_lock_outside_frame, os_sched_lock_running.
  rewrite critical_region_outside_without_running_rep, UCOS2_inv_split_running.
  entailer!.
Qed.

(** The two bytes read before [OSSchedLock] are a temporary view of the
    existing invariant.  Reassemble that view before opening the scheduler
    contract; carrying it beside [outside_frame] would duplicate the Timer
    and Interrupt owners. *)
Lemma tmr_del_lock_pre_from_observations : forall platform critical sg invocation origin mask
  before i image,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  timer_api_initialized before.(TimerState) ->
  before.(TimerState).(timerImages) i = Some image ->
  interrupt_platform_running platform invocation origin mask **
    (coq_prop (UCOS2_state_inv sg before) &&
      (timer_pool_addr sg i # UChar |-> image.(timerImageType) **
       sg.(g_OSIntNesting) # UChar |-> before.(IntrState).(intNesting) **
       tmr_del_observation_residual sg before i image)) |--
  os_sched_lock_pre platform critical sg invocation origin mask before.
Proof.
  intros platform critical sg invocation origin mask before i image Henabled Hinit Himage.
  rewrite (tmr_del_merge_observations sg before i image Henabled Hinit Himage).
  apply tmr_del_lock_pre_from_inv.
Qed.

Lemma tmr_del_lock_post_to_inv : forall platform critical sg invocation origin mask before,
  os_sched_lock_post platform critical sg invocation origin mask before |--
  EX acquired locked,
    coq_prop (os_sched_lock_call_relation critical sg invocation before acquired locked) &&
    (interrupt_platform_running platform invocation origin mask ** UCOS2_inv sg locked).
Proof.
  intros; unfold os_sched_lock_post, os_sched_lock_outside_frame, os_sched_lock_running.
  Intros acquired locked; Exists acquired locked.
  rewrite critical_region_outside_without_running_rep, UCOS2_inv_split_running.
  entailer!.
Qed.

Lemma tmr_del_unlock_pre_from_inv : forall external platform critical sg context mask completion,
  os_sched_unlock_acquire_safety external critical sg context completion ->
  interrupt_platform_running platform (os_sched_call_invocation context)
    (os_sched_call_origin context) mask ** UCOS2_inv sg completion **
    os_sched_context_resources external context ** unmap_table_rep sg |--
  os_sched_unlock_pre external platform critical sg context mask completion.
Proof.
  intros; unfold os_sched_unlock_pre, os_sched_unlock_observation_frame,
    os_sched_unlock_running.
  rewrite critical_region_outside_without_running_rep, UCOS2_inv_split_running.
  entailer!.
Qed.

Lemma tmr_del_locked_step_result : forall critical sg invocation pointer name before
  i image acquired locked completion result,
  tmr_del_observation_binding sg before pointer i image ->
  tmr_del_early_result pointer (tmr_del_image_type image) (tmr_del_int_nesting before) = None ->
  os_sched_lock_call_relation critical sg invocation before acquired locked ->
  tmr_del_locked_state_step sg locked i name (tmr_del_result_ret result)
    (tmr_del_result_err result) completion ->
  tmr_del_result_prop critical sg invocation pointer name before completion result.
Proof.
  intros critical sg invocation pointer name before i image acquired locked completion result
    [Henabled [Hinitialized [Hpointer Himage]]] Hearly Hlock Hstep.
  apply tmr_del_early_result_continue_iff in Hearly.
  destruct Hearly as [Hnonnull [Htype Hnest]].
  unfold tmr_del_result_prop; right; right; right.
  split; [exact Hnonnull|].
  exists i, image, acquired, locked.
  split; [exact Hpointer|].
  split; [exact Himage|].
  split; [exact Htype|].
  split; [exact Hnest|].
  split; [exact Hlock|].
  exact Hstep.
Qed.

Lemma tmr_del_locked_step_unlock_safety : forall external critical sg context before pointer
  name i image acquired locked completion result,
  tmr_del_scheduler_acquire_safety external critical sg context before pointer name ->
  tmr_del_observation_binding sg before pointer i image ->
  tmr_del_early_result pointer (tmr_del_image_type image) (tmr_del_int_nesting before) = None ->
  os_sched_lock_call_relation critical sg (os_sched_call_invocation context) before acquired locked ->
  tmr_del_locked_state_step sg locked i name (tmr_del_result_ret result)
    (tmr_del_result_err result) completion ->
  os_sched_unlock_acquire_safety external critical sg context completion.
Proof.
  intros external critical sg context before pointer name i image acquired locked completion result
    Hsafe [Henabled [Hinitialized [Hpointer Himage]]] Hearly Hlock Hstep.
  pose proof (proj1 (tmr_del_early_result_continue_iff _ _ _) Hearly) as Hguards.
  destruct Hguards as [Hnonnull _].
  exact (Hsafe i image acquired locked result completion
    Hnonnull Hpointer Himage Hearly Hlock Hstep).
Qed.

Lemma tmr_del_merge_observed_cells : forall sg before pointer i image,
  tmr_del_c_bindings sg pointer ->
  tmr_del_observation_binding sg before pointer i image ->
  UCOS2_state_inv sg before ->
  &(pointer # "os_tmr" ->ₛ "OSTmrType") # UChar |-> tmr_del_image_type image **
  &("OSIntNesting") # UChar |-> tmr_del_int_nesting before **
  tmr_del_observation_residual sg before i image |-- UCOS2_inv sg before.
Proof.
  intros sg before pointer i image Hbindings Hobservation Hvalid.
  destruct Hobservation as [Henabled [Hinitialized [Hpointer Himage]]].
  assert (Htype : &(pointer # "os_tmr" ->ₛ "OSTmrType") = pointer).
  { unfold tmr_del_c_bindings, tmr_free_bindings, tmr_free_layout in Hbindings; tauto. }
  assert (Hints : &("OSIntNesting") = sg.(g_OSIntNesting)).
  { unfold tmr_del_c_bindings, os_sched_unlock_global_addresses,
      os_sched_global_addresses in Hbindings; tauto. }
  unfold tmr_del_image_type, tmr_del_int_nesting.
  rewrite Htype, Hpointer, Hints.
  rewrite <- (tmr_del_merge_observations sg before i image Henabled Hinitialized Himage).
  entailer!.
Qed.

(** Facts established by the ordered pointer, type and ISR tests before Lock. *)
Definition tmr_del_checks_passed (pointer : addr) (image : TimerImage)
  (before : UCOS2_Verify_State) : Prop :=
  tmr_del_early_result pointer (tmr_del_image_type image)
    (tmr_del_int_nesting before) = None.

Definition tmr_del_image_stopped (image : TimerImage) : Prop :=
  tmr_del_image_state image = 1 \/ tmr_del_image_state image = 2.

Definition tmr_del_call_history (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (before : UCOS2_Verify_State)
  (pointer : addr) (i : TimerID) (image : TimerImage)
  (locked : UCOS2_Verify_State) : Prop :=
  tmr_del_observation_binding sg before pointer i image /\
  tmr_del_checks_passed pointer image before /\
  exists acquired, os_sched_lock_call_relation critical sg invocation before acquired locked.

Definition tmr_del_success_result : TmrDelResult :=
  TmrDelResultValue true OS_ERR_NONE.
Definition tmr_del_inactive_result : TmrDelResult :=
  TmrDelResultValue false OS_ERR_TMR_INACTIVE.
Definition tmr_del_invalid_state_result : TmrDelResult :=
  TmrDelResultValue false OS_ERR_TMR_INVALID_STATE.

Definition tmr_del_release_state (sg : StableGlobVars)
  (locked : UCOS2_Verify_State) (s : GlobTimerState)
  (i : TimerID) (old : TimerImage) (name : addr) : UCOS2_Verify_State :=
  replace_TimerS (timer_release sg s i old name) locked.

(** A pure relation for the expected Free endpoint, retained with its
    exact input snapshot. The callee's spatial post still has to establish
    the corresponding bytes; this relation does not provide those bytes. *)
Definition tmr_del_release_step (sg : StableGlobVars)
  (locked : UCOS2_Verify_State) (s : GlobTimerState)
  (i : TimerID) (old : TimerImage) (name : addr) : Prop :=
  tmr_del_locked_state_step sg locked i name true OS_ERR_NONE
    (tmr_del_release_state sg locked s i old name).


Lemma tmr_del_bindings_unlink_profile : forall sg pointer state,
  tmr_del_c_bindings sg pointer -> UCOS2_state_inv sg state ->
  tmr_unlink_profile sg.
Proof.
  intros sg pointer state Hbindings Hvalid.
  assert (Hcfg : osKernelConfig sg = selected_kernel_configuration).
  { unfold tmr_del_c_bindings, tmr_free_bindings in Hbindings; tauto. }
  assert (Hprofile : selected_kernel_profile sg).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  assert (Henabled : cfgTimerEnabled (osKernelConfig sg) = true).
  { rewrite Hcfg; reflexivity. }
  pose proof (selected_kernel_profile_timer_pool_region_valid sg Hprofile Henabled) as Hpool.
  rewrite Hcfg in Hpool.
  change (kernel_region_valid (g_OSTmrTbl sg, 640)) in Hpool.
  assert (Hwheel : kernel_region_valid (g_OSTmrWheelTbl sg, 56)).
  { apply (valid_selected_kernel_global_layout_region sg).
    - unfold selected_kernel_profile in Hprofile; tauto.
    - unfold selected_kernel_global_regions.
      apply in_or_app; right. apply in_or_app; right.
      apply in_or_app; right. apply in_or_app; left.
      unfold kernel_independent_regions.
      apply in_or_app; right. apply in_or_app; right.
      apply in_or_app; left. rewrite Hcfg; simpl; auto. }
  unfold tmr_unlink_profile; rewrite Hcfg.
  change (true = true /\ true = true /\ 16 = 16 /\ 7 = 7 /\
    kernel_region_valid (g_OSTmrTbl sg, 640) /\ kernel_region_valid (g_OSTmrWheelTbl sg, 56)).
  tauto.
Qed.

Lemma tmr_del_merge_locked_cells : forall sg locked pointer i image,
  tmr_del_c_bindings sg pointer -> pointer = timer_pool_addr sg i ->
  UCOS2_state_inv sg locked -> timer_api_initialized (TimerState locked) ->
  timerImages (TimerState locked) i = Some image ->
  &(pointer # "os_tmr" ->ₛ "OSTmrType") # UChar |-> tmr_del_image_type image **
  &(pointer # "os_tmr" ->ₛ "OSTmrState") # UChar |-> tmr_del_image_state image **
  tmr_del_locked_observation_residual sg locked i image |-- UCOS2_inv sg locked.
Proof.
  intros sg locked pointer i image Hbindings Hpointer Hvalid Hinit Himage.
  assert (Hcfg : osKernelConfig sg = selected_kernel_configuration).
  { unfold tmr_del_c_bindings, tmr_free_bindings in Hbindings; tauto. }
  assert (Htype : &(pointer # "os_tmr" ->ₛ "OSTmrType") = pointer).
  { unfold tmr_del_c_bindings, tmr_free_bindings, tmr_free_layout in Hbindings; tauto. }
  assert (Hstate : &(pointer # "os_tmr" ->ₛ "OSTmrState") = pointer + 37).
  { unfold tmr_del_c_bindings, tmr_free_bindings, tmr_free_layout in Hbindings; tauto. }
  assert (Henabled : cfgTimerEnabled (osKernelConfig sg) = true).
  { rewrite Hcfg; reflexivity. }
  assert (Hoffset : timer_option_offset (osKernelConfig sg) = 36).
  { rewrite Hcfg; reflexivity. }
  unfold tmr_del_image_type, tmr_del_image_state, tmr_del_locked_observation_residual.
  rewrite Htype, Hstate, Hpointer.
  pose proof (timer_raw_rep_merge_type_state sg (TimerState locked) i image Himage) as Hmerge.
  rewrite Hoffset in Hmerge.
  replace (timer_pool_addr sg i + 36 + 1) with (timer_pool_addr sg i + 37) in Hmerge by lia.
  rewrite (UCOS2_inv_split_module sg locked TimerModule).
  cbn [UCOS2_module_rep].
  rewrite (timer_initialized_configured_rep_eq sg (TimerState locked) Henabled Hinit).
  rewrite <- Hmerge.
  entailer!.
Qed.

Lemma tmr_del_unchanged_unlock_pre : forall external platform critical sg context mask
  before pointer i original locked current name result,
  tmr_del_c_bindings sg pointer ->
  tmr_del_call_history critical sg (os_sched_call_invocation context)
    before pointer i original locked ->
  UCOS2_state_inv sg locked -> timer_api_initialized (TimerState locked) ->
  timerImages (TimerState locked) i = Some current ->
  tmr_del_locked_state_step sg locked i name (tmr_del_result_ret result)
    (tmr_del_result_err result) locked ->
  tmr_del_scheduler_acquire_safety external critical sg context before pointer name ->
  &(pointer # "os_tmr" ->ₛ "OSTmrType") # UChar |-> tmr_del_image_type current **
  &(pointer # "os_tmr" ->ₛ "OSTmrState") # UChar |-> tmr_del_image_state current **
  tmr_del_locked_observation_residual sg locked i current **
  interrupt_platform_running platform (os_sched_call_invocation context)
    (os_sched_call_origin context) mask **
  os_sched_context_resources external context ** unmap_table_rep sg |--
  coq_prop (tmr_del_result_prop critical sg (os_sched_call_invocation context)
    pointer name before locked result /\
    os_sched_unlock_global_addresses sg &("OSRunning") &("OSIntNesting")
      &("OSLockNesting") &("OSPrioHighRdy") &("OSPrioCur") &("OSTCBHighRdy")
      &("OSTCBPrioTbl") &("OSCtxSwCtr") &("OSUnMapTbl") &("OSRdyGrp") &("OSRdyTbl")) &&
  os_sched_unlock_pre external platform critical sg context mask locked.
Proof.
  intros external platform critical sg context mask before pointer i original locked
    current name result Hbindings [Hobs [Hchecks [acquired Hlock]]] Hvalid Hinit
    Himage Hstep Hsafe.
  pose proof Hobs as [_ [_ [Hpointer _]]].
  pose proof (tmr_del_locked_step_result critical sg (os_sched_call_invocation context)
    pointer name before i original acquired locked locked result
    Hobs Hchecks Hlock Hstep) as Hresult.
  pose proof (tmr_del_locked_step_unlock_safety external critical sg context before
    pointer name i original acquired locked locked result
    Hsafe Hobs Hchecks Hlock Hstep) as Hunlock.
  assert (Haddresses : os_sched_unlock_global_addresses sg &("OSRunning") &("OSIntNesting")
      &("OSLockNesting") &("OSPrioHighRdy") &("OSPrioCur") &("OSTCBHighRdy")
      &("OSTCBPrioTbl") &("OSCtxSwCtr") &("OSUnMapTbl") &("OSRdyGrp") &("OSRdyTbl")).
  { unfold tmr_del_c_bindings in Hbindings; tauto. }
  apply _derivable1_andp_intros; [entailer!|].
  sep_apply_l_atomic (tmr_del_merge_locked_cells sg locked pointer i current
    Hbindings Hpointer Hvalid Hinit Himage).
  rewrite <- (tmr_del_unlock_pre_from_inv external platform critical sg context mask locked Hunlock).
  entailer!.
Qed.

Lemma tmr_del_released_unlock_pre : forall external platform critical sg context mask
  before pointer i original locked s old name,
  tmr_del_c_bindings sg pointer ->
  tmr_del_call_history critical sg (os_sched_call_invocation context)
    before pointer i original locked ->
  UCOS2_state_inv sg locked -> timer_api_initialized (TimerState locked) ->
  tmr_del_release_step sg locked s i old name ->
  tmr_del_scheduler_acquire_safety external critical sg context before pointer name ->
  tmr_free_valid_post sg s i old name ** UCOS2_raw_rep_missing_timer sg locked **
  interrupt_platform_running platform (os_sched_call_invocation context)
    (os_sched_call_origin context) mask **
  os_sched_context_resources external context ** unmap_table_rep sg |--
  coq_prop (tmr_del_result_prop critical sg (os_sched_call_invocation context)
    pointer name before (tmr_del_release_state sg locked s i old name) tmr_del_success_result /\
    os_sched_unlock_global_addresses sg &("OSRunning") &("OSIntNesting")
      &("OSLockNesting") &("OSPrioHighRdy") &("OSPrioCur") &("OSTCBHighRdy")
      &("OSTCBPrioTbl") &("OSCtxSwCtr") &("OSUnMapTbl") &("OSRdyGrp") &("OSRdyTbl")) &&
  os_sched_unlock_pre external platform critical sg context mask
    (tmr_del_release_state sg locked s i old name).
Proof.
  intros external platform critical sg context mask before pointer i original locked
    s old name Hbindings [Hobs [Hchecks [acquired Hlock]]] Hvalid Hinit Hstep Hsafe.
  pose proof (tmr_del_bindings_unlink_profile sg pointer locked Hbindings Hvalid) as Hprofile.
  pose proof (tmr_del_locked_step_result critical sg (os_sched_call_invocation context)
    pointer name before i original acquired locked (tmr_del_release_state sg locked s i old name)
    tmr_del_success_result Hobs Hchecks Hlock Hstep) as Hresult.
  pose proof (tmr_del_locked_step_unlock_safety external critical sg context before
    pointer name i original acquired locked (tmr_del_release_state sg locked s i old name)
    tmr_del_success_result Hsafe Hobs Hchecks Hlock Hstep) as Hunlock.
  pose proof (tmr_del_locked_state_step_preserves_validity sg locked i name true OS_ERR_NONE
    (tmr_del_release_state sg locked s i old name) Hprofile Hvalid Hinit Hstep) as [Hpost _].
  assert (Hmerge : timer_configured_rep sg (timer_release sg s i old name) **
    UCOS2_raw_rep_missing_timer sg locked |--
    UCOS2_inv sg (tmr_del_release_state sg locked s i old name)).
  { unfold tmr_del_release_state.
    apply (UCOS2_inv_merge_updated_timer sg locked
      (replace_TimerS (timer_release sg s i old name) locked)); [exact Hpost|].
    symmetry; apply UCOS2_raw_rep_missing_timer_replace_eq. }
  assert (Haddresses : os_sched_unlock_global_addresses sg &("OSRunning") &("OSIntNesting")
      &("OSLockNesting") &("OSPrioHighRdy") &("OSPrioCur") &("OSTCBHighRdy")
      &("OSTCBPrioTbl") &("OSCtxSwCtr") &("OSUnMapTbl") &("OSRdyGrp") &("OSRdyTbl")).
  { unfold tmr_del_c_bindings in Hbindings; tauto. }
  apply _derivable1_andp_intros; [entailer!|].
  unfold tmr_free_valid_post, timer_inv; Intros.
  sep_apply_l_atomic Hmerge.
  rewrite <- (tmr_del_unlock_pre_from_inv external platform critical sg context mask
    (tmr_del_release_state sg locked s i old name) Hunlock).
  entailer!.
Qed.

Lemma tmr_del_initialized_timer_valid : forall sg pointer state,
  tmr_del_c_bindings sg pointer -> UCOS2_state_inv sg state ->
  timer_api_initialized (TimerState state) ->
  valid_timer_state sg (TimerState state).
Proof.
  intros sg pointer state Hbindings Hvalid Hinit.
  pose proof (tmr_del_bindings_unlink_profile sg pointer state Hbindings Hvalid) as [Hen _].
  apply (proj1 (timer_initialized_configuration_iff sg (TimerState state) Hen Hinit)).
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto.
Qed.

(** The API continuation observes both bytes and the actual normal-return
    kernel state.  The earlier completion token is retained only for the
    historical protected-prefix interface. *)
Definition TmrDelOutput : Type := (Z * Z)%type.

Definition tmr_del_output (result : TmrDelResult) : TmrDelOutput :=
  (tmr_del_return result, encode_os_err_code (tmr_del_result_err result)).

Definition tmr_del_at_state (state : UCOS2_Verify_State)
  : UCOS2_Verify_State -> Prop := fun current => current = state.

(** These are precisely the three errors returned before OSSchedLock. *)
Definition tmr_del_needs_unlock (result : TmrDelResult) : bool :=
  match tmr_del_result_err result with
  | OS_ERR_TMR_INVALID | OS_ERR_TMR_INVALID_TYPE | OS_ERR_TMR_ISR => false
  | _ => true
  end.

(** Ordinary-return consequence of the existing callee post.  The second
    acquisition belongs to OS_Sched and is deliberately distinct from the
    unlock checkpoint.  A retired invocation has no ordinary-return arm. *)
Definition tmr_del_unlock_return (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (before : UCOS2_Verify_State)
  (returned : OsSchedCallContext) (final : UCOS2_Verify_State) : Prop :=
  (before.(SchedState).(isRunning) = false /\ UCOS2_state_inv sg before /\
    returned = context /\ final = before) \/
  (exists entry,
    before.(SchedState).(isRunning) = true /\
    critical_region_interval critical sg context.(os_sched_call_invocation) before entry /\
    UCOS2_state_inv sg (os_sched_unlock_checkpoint true entry) /\
    ((os_sched_unlock_requests entry = true /\ exists sched_entry,
       critical_region_interval critical sg context.(os_sched_call_invocation)
         (os_sched_unlock_checkpoint true entry) sched_entry /\
       os_sched_c_return external critical sg sched_entry context returned final) \/
     (os_sched_unlock_requests entry = false /\ returned = context /\
       final = os_sched_unlock_checkpoint true entry))).

Definition tmr_del_return_frame (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context returned : OsSchedCallContext) (mask : Z)
  (final : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running platform context.(os_sched_call_invocation)
    context.(os_sched_call_origin) mask **
  critical_region_outside critical sg context.(os_sched_call_invocation) final **
  os_sched_context_resources external returned ** unmap_table_rep sg.

Lemma tmr_del_unlock_post_return : forall external platform critical sg context mask before,
  os_sched_unlock_post external platform critical sg context mask before |--
  EX returned final,
    coq_prop (tmr_del_unlock_return external critical sg context before returned final) &&
    tmr_del_return_frame external platform critical sg context returned mask final.
Proof.
  intros; unfold os_sched_unlock_post; apply derivable1_orp_elim.
  - Intros. Exists context before.
    assert (Hreturn : tmr_del_unlock_return external critical sg context before context before).
    { unfold tmr_del_unlock_return; left; tauto. }
    unfold tmr_del_return_frame.
    unfold os_sched_unlock_observation_frame, critical_region_outside,
      os_sched_unlock_running in *.
    entailer!.
  - Intros entry.
    destruct (os_sched_unlock_requests entry) eqn:Hrequests.
    + unfold os_sched_post; Intros sched_entry final returned.
      Exists returned final.
      assert (Hreturn : tmr_del_unlock_return external critical sg context before returned final).
      { unfold tmr_del_unlock_return; right; exists entry.
        split; [tauto|]. split; [tauto|]. split; [tauto|].
        left; split; [exact Hrequests|]. exists sched_entry; tauto. }
      unfold tmr_del_return_frame; entailer!.
    + Exists context (os_sched_unlock_checkpoint true entry).
      assert (Hreturn : tmr_del_unlock_return external critical sg context before context
        (os_sched_unlock_checkpoint true entry)).
      { unfold tmr_del_unlock_return; right; exists entry.
        split; [tauto|]. split; [tauto|]. split; [tauto|]. right; auto. }
      unfold tmr_del_return_frame, os_sched_unlock_outside_frame; entailer!.
Qed.

(** The first program is the existing ordered NULL/type/ISR classification,
    actual Lock relation and Unlink/Free composition.  The second program
    consumes Unlock's actual normal-return relation, before observing perr
    and the Boolean.  No Timer equality across scheduling is assumed. *)
Definition tmr_del_prefix_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pointer name : addr)
  : program UCOS2_Verify_State TmrDelResult :=
  fun before result completion =>
    tmr_del_result_prop critical sg invocation pointer name before completion result.

Definition tmr_del_return_program (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (result : TmrDelResult)
  : program UCOS2_Verify_State OsSchedCallContext :=
  if tmr_del_needs_unlock result then tmr_del_unlock_return external critical sg context
  else StateRelMonad.ret context.

Definition tmr_del_call_program (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (pointer name : addr)
  : program UCOS2_Verify_State TmrDelOutput :=
  bind (tmr_del_prefix_program critical sg context.(os_sched_call_invocation) pointer name)
    (fun result => bind (tmr_del_return_program external critical sg context result)
      (fun _ => StateRelMonad.ret (tmr_del_output result))).

Lemma tmr_del_call_program_result_iff : forall external critical sg context pointer name
  before output final,
  tmr_del_call_program external critical sg context pointer name before output final <->
  exists completion result returned,
    tmr_del_result_prop critical sg context.(os_sched_call_invocation)
      pointer name before completion result /\
    tmr_del_return_program external critical sg context result completion returned final /\
    output = tmr_del_output result.
Proof.
  intros; unfold tmr_del_call_program, tmr_del_prefix_program.
  change ((exists result completion,
    tmr_del_result_prop critical sg (os_sched_call_invocation context)
      pointer name before completion result /\
    exists returned endpoint,
      tmr_del_return_program external critical sg context result completion returned endpoint /\
      output = tmr_del_output result /\ endpoint = final) <->
    exists completion result returned,
      tmr_del_result_prop critical sg (os_sched_call_invocation context)
        pointer name before completion result /\
      tmr_del_return_program external critical sg context result completion returned final /\
      output = tmr_del_output result).
  split.
  - intros [result [completion [Hprefix [returned [endpoint [Hreturn [Houtput ->]]]]]]].
    exists completion, result, returned; auto.
  - intros [completion [result [returned [Hprefix [Hreturn Houtput]]]]].
    exists result, completion; split; [exact Hprefix|].
    exists returned, final; auto.
Qed.

Lemma tmr_del_call_safe_return : forall external critical sg context pointer name
  before completion result returned final (X : TmrDelOutput -> UCOS2_Verify_State -> Prop),
  tmr_del_result_prop critical sg context.(os_sched_call_invocation)
    pointer name before completion result ->
  tmr_del_return_program external critical sg context result completion returned final ->
  safeExec (tmr_del_at_state before)
    (tmr_del_call_program external critical sg context pointer name) X ->
  safeExec (tmr_del_at_state final) (StateRelMonad.ret (tmr_del_output result)) X.
Proof.
  intros external critical sg context pointer name before completion result returned final
    X Hprefix Hreturn Hsafe.
  eapply (highstependret_derive
    (tmr_del_call_program external critical sg context pointer name)
    (tmr_del_at_state before) (tmr_del_output result)
    (fun _ => tmr_del_at_state final)); [|exact Hsafe].
  unfold hs_eval, tmr_del_at_state; intros initial ->.
  exists final; split; [|reflexivity].
  apply tmr_del_call_program_result_iff.
  exists completion, result, returned; auto.
Qed.

Definition tmr_del_api_return_resources (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context returned : OsSchedCallContext) (mask : Z)
  (result : TmrDelResult) (final : UCOS2_Verify_State) : Assertion :=
  if tmr_del_needs_unlock result then
    tmr_del_return_frame external platform critical sg context returned mask final
  else interrupt_platform_running platform context.(os_sched_call_invocation)
    context.(os_sched_call_origin) mask ** UCOS2_inv sg final **
    os_sched_context_resources external returned ** unmap_table_rep sg.

(** One existential group binds the protected effect, actual returned
    context, final kernel state, exact output pair, arbitrary same X and
    the spatial return resources.  perr remains a caller-owned byte. *)
Definition tmr_del_api_post (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask : Z)
  (before : UCOS2_Verify_State) (pointer name perr : addr) (ret : Z)
  (X : TmrDelOutput -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX completion result returned final,
    coq_prop (tmr_del_result_prop critical sg context.(os_sched_call_invocation)
        pointer name before completion result /\
      tmr_del_return_program external critical sg context result completion returned final /\
      ret = tmr_del_return result /\
      safeExec (tmr_del_at_state final) (StateRelMonad.ret (tmr_del_output result)) X) &&
    (tmr_del_api_return_resources external platform critical sg context returned mask result final **
     perr # UChar |-> encode_os_err_code (tmr_del_result_err result)).

Lemma tmr_del_api_post_after_unlock : forall external platform critical sg context mask
  before pointer name perr completion result X,
  tmr_del_result_prop critical sg context.(os_sched_call_invocation)
    pointer name before completion result ->
  tmr_del_needs_unlock result = true ->
  safeExec (tmr_del_at_state before)
    (tmr_del_call_program external critical sg context pointer name) X ->
  os_sched_unlock_post external platform critical sg context mask completion **
    perr # UChar |-> encode_os_err_code (tmr_del_result_err result) |--
  tmr_del_api_post external platform critical sg context mask before pointer name perr
    (tmr_del_return result) X.
Proof.
  intros external platform critical sg context mask before pointer name perr completion result
    X Hprefix Hunlock Hsafe.
  sep_apply_l_atomic (tmr_del_unlock_post_return external platform critical sg context mask completion).
  Intros returned final.
  assert (Hreturn : tmr_del_return_program external critical sg context result completion returned final).
  { unfold tmr_del_return_program; rewrite Hunlock; assumption. }
  pose proof (tmr_del_call_safe_return external critical sg context pointer name before completion
    result returned final X Hprefix Hreturn Hsafe) as Hexec.
  unfold tmr_del_api_post; Exists completion result returned final.
  unfold tmr_del_api_return_resources; rewrite Hunlock; entailer!.
Qed.

Lemma tmr_del_api_post_early : forall external platform critical sg context mask
  before pointer name perr result X,
  tmr_del_result_prop critical sg context.(os_sched_call_invocation)
    pointer name before before result ->
  tmr_del_needs_unlock result = false ->
  safeExec (tmr_del_at_state before)
    (tmr_del_call_program external critical sg context pointer name) X ->
  tmr_del_early_post sg external platform critical context mask before perr
    (tmr_del_result_err result) |--
  tmr_del_api_post external platform critical sg context mask before pointer name perr
    (tmr_del_return result) X.
Proof.
  intros external platform critical sg context mask before pointer name perr result X
    Hprefix Hearly Hsafe.
  assert (Hreturn : tmr_del_return_program external critical sg context result before context before).
  { unfold tmr_del_return_program; rewrite Hearly; split; reflexivity. }
  pose proof (tmr_del_call_safe_return external critical sg context pointer name before before
    result context before X Hprefix Hreturn Hsafe) as Hexec.
  unfold tmr_del_api_post; Exists before result context before.
  unfold tmr_del_api_return_resources; rewrite Hearly.
  unfold tmr_del_early_post; entailer!.
Qed.
