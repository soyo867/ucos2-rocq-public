Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_clear_status_pend_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_status_call_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_status_callback_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_status_unlock_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_iteration_entry_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_scan_unlock_entry_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_registered_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_unlock_fields_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_callback_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_return_facts_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_lock_fields_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_fields_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_status Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.event.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Current loop observations. A caller may be suspended, while its
    event-pend status is clear and the signal input covers all old errors. *)
Definition tmr_task_client_status_iteration_entry critical sg call state : Prop :=
  tmr_task_client_clear_status_pend_entry sg call state /\
  exists eid observed,
    sem_pend_call_input critical sg call.(os_sched_call_invocation)
      state.(TimerState).(timerSignalSem) state eid observed.

Lemma tmr_task_client_status_iteration_from_ready : forall critical sg call state,
  tmr_task_fields_iteration_entry critical sg call state ->
  tmr_task_client_status_iteration_entry critical sg call state.
Proof.
  intros critical sg call state [Hentry [Hready Hinput]].
  split; [eapply tmr_task_client_clear_status_pend_entry_from_ready; eassumption|exact Hinput].
Qed.

Lemma tmr_task_client_status_iteration_from_lifetime : forall critical sg call state
  (fallback : OSEventAbstractState),
  tmr_task_client_clear_status_pend_entry sg call state ->
  tmr_task_signal_lifetime critical sg call.(os_sched_call_invocation) state ->
  tmr_task_client_status_iteration_entry critical sg call state.
Proof.
  intros critical sg call state fallback Hentry Hlife; split; [exact Hentry|].
  exact (tmr_task_signal_lifetime_call_input critical sg call.(os_sched_call_invocation)
    state fallback Hlife).
Qed.

Lemma tmr_task_client_status_iteration_pend_domain : forall critical sg call state,
  sem_pend_profile sg -> kernel_tcb_stack_field_layout sg ->
  tmr_task_client_status_iteration_entry critical sg call state ->
  exists eid observed,
    tmr_task_client_clear_status_pend_domain critical sg call
      state.(TimerState).(timerSignalSem) state eid observed /\
    tmr_task_client_clear_status_pend_entry sg call state.
Proof.
  intros critical sg call state Hprofile Hlayout [Hentry [eid [observed Hinput]]].
  exists eid, observed; split; [exact (conj Hprofile (conj Hlayout Hinput))|exact Hentry].
Qed.

Lemma tmr_task_client_status_entry_same_call : forall sg original returned state,
  kernel_stack_call_same_call returned original ->
  tmr_task_client_clear_status_pend_entry sg original state ->
  tmr_task_client_clear_status_pend_entry sg returned state.
Proof.
  intros sg original returned state Hsame [Hentry Hstatus]; split.
  - eapply tmr_task_unlock_entry_same_call; eassumption.
  - eapply tmr_task_caller_wait_status_clear_same_call; eassumption.
Qed.

Lemma tmr_task_client_status_entry_replace_timers : forall sg call state timers,
  tmr_task_client_clear_status_pend_entry sg call state ->
  tmr_task_client_clear_status_pend_entry sg call (replace_TimerS timers state).
Proof. intros sg call state timers Hentry; exact Hentry. Qed.

Lemma tmr_task_client_status_lock_return_entry : forall external environment critical sg original mask
  before returned current,
  tmr_task_registered_source_coverage external critical -> UCOS2_state_inv sg before ->
  tmr_task_client_clear_status_pend_entry sg original before ->
  kernel_call_normal_return original before returned current ->
  (kernel_call_task_source original before -> kernel_call_task_source returned current) ->
  os_sched_lock_continuation_control before current ->
  os_sched_lock_fields_return_sources environment critical sg original mask before returned current ->
  tmr_task_client_clear_status_pend_entry sg returned current.
Proof.
  intros external environment critical sg original mask before returned current
    Hcoverage Hvalid [Hentry Hstatus] Hnormal Hsource Hcontrol Hsources; split.
  - eapply tmr_task_lock_return_unlock_entry; eassumption.
  - eapply tmr_task_lock_return_wait_status; try eassumption; exact (proj1 Hentry).
Qed.

Lemma tmr_task_client_status_lock_post_entry : forall external environment critical local sg
  original mask before X,
  tmr_task_registered_source_coverage external critical -> UCOS2_state_inv sg before ->
  tmr_task_client_clear_status_pend_entry sg original before ->
  os_sched_lock_fields_post environment critical local sg original mask before X |--
  EX returned current,
    coq_prop (tmr_task_client_clear_status_pend_entry sg returned current /\
      os_sched_lock_continuation_history environment critical sg original mask before returned current /\
      kernel_call_normal_return original before returned current /\
      (kernel_call_task_source original before -> kernel_call_task_source returned current) /\
      os_sched_lock_continuation_control before current /\
      os_sched_lock_fields_return_sources environment critical sg original mask before returned current /\
      safeExec (fun observed => observed = current) (StateRelMonad.ret returned) X) &&
    os_sched_fields_closed environment local sg returned mask current.
Proof.
  intros external environment critical local sg original mask before X Hcoverage Hvalid Hentry
    heap [returned [current [[Hhistory [Hnormal [Hsource [Hcontrol [Hsources Hsafe]]]]] Howned]]].
  exists returned, current; split; [|exact Howned].
  split; [eapply tmr_task_client_status_lock_return_entry; eassumption|].
  exact (conj Hhistory (conj Hnormal (conj Hsource (conj Hcontrol (conj Hsources Hsafe))))).
Qed.

Lemma tmr_task_client_status_callback_return_entry : forall Application sg callback fn self argument
  context (before : tmr_task_scan_world Application) returned after,
  tmr_task_client_status_callback_return_facts sg callback fn self argument context before returned after ->
  tmr_task_client_clear_status_pend_entry sg context (fst before) ->
  tmr_task_client_clear_status_pend_entry sg returned (fst after).
Proof.
  intros Application sg callback fn self argument context before returned after
    [Hfacts Hstatus_return] [Hentry Hstatus]; split.
  - eapply tmr_task_callback_return_unlock_entry; eassumption.
  - apply Hstatus_return; exact Hstatus.
Qed.

Lemma tmr_task_client_status_callback_post_entry : forall Application AppRep environment sg callback mask perr
  fn self argument context (before : tmr_task_scan_world Application) arguments result,
  tmr_task_client_clear_status_pend_entry sg context (fst before) ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_client_status_callback_post AppRep environment sg callback mask perr
      fn self argument context before arguments result)
    (fun heap => exists returned after,
      arguments = (self, argument) /\
      tmr_task_client_status_callback_return_facts sg callback fn self argument context before returned after /\
      tmr_task_client_clear_status_pend_entry sg returned (fst after) /\
      tmr_task_current_fields_owned AppRep environment sg mask perr returned after heap).
Proof.
  intros Application AppRep environment sg callback mask perr fn self argument context before
    arguments result Hentry heap [returned [after [Harguments [Hfacts Howned]]]].
  exists returned, after; split; [exact Harguments|]. split; [exact Hfacts|].
  split; [eapply tmr_task_client_status_callback_return_entry; eassumption|exact Howned].
Qed.

(** Idle and non-Idle below are consumed as observations of this actual
    Scheduler return. Their production from the real source remains a
    separate obligation; current readiness does not establish them. *)
Lemma tmr_task_client_status_scheduled_return_entry : forall sg original before returned current reference,
  tmr_task_unlock_entry sg original before ->
  kernel_call_normal_return original before returned current ->
  (kernel_call_task_source original before -> kernel_call_task_source returned current) ->
  os_sched_unlock_continuation_control before current ->
  os_sched_task_current_ready returned current ->
  flag_active_fresh_registration reference returned current ->
  task_idle_ready sg current.(TskState) -> flag_pend_non_idle_at sg returned current ->
  tmr_task_client_clear_status_pend_entry sg returned current.
Proof.
  intros sg original before returned current reference
    [Hsource [Havailable [Hrunning Hrest]]] Hnormal Hsource_return Hcontrol Hready Hfresh Hidle Hnonidle.
  split; [|apply tmr_task_caller_wait_status_clear_from_ready; exact Hready].
  split; [apply Hsource_return; exact Hsource|].
  split; [exact (proj2 Hnormal Havailable)|].
  split; [rewrite (proj1 Hcontrol); exact Hrunning|].
  split; [exact (SchedulerReturnFacts.os_sched_task_current_ready_current_consistency
    returned current Hready)|]. split; [exact Hidle|].
  destruct Hfresh as [node [[Hsame [Horigin [Hnode [Hgeneration [Hactive Hclear]]]]] Hflag]].
  pose proof Hsame as [_ [_ Hstack]].
  destruct Hnonidle as [actual [Hactual [Hactual_generation Hpriority]]].
  rewrite Hstack in Hactual.
  assert (actual = node) by congruence; subst actual.
  intros observed Hobserved; rewrite Hstack in Hobserved.
  assert (observed = node) by congruence; subst observed.
  exact (conj Hpriority (conj Hclear Hflag)).
Qed.
