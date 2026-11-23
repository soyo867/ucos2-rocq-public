Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_status_callback_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_registered_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_sem_source_projection_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_clear_status_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_lock_fields_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_fields_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_status Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.kernel_client_invariants Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.sched.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Existing source actions preserve clear event-pend bits even when the
    caller is suspended. This is a derivation from their real updates, not
    an extra registration promise or a readiness restriction. *)
Lemma tmr_task_scheduler_source_preserves_wait_status : forall external action sg before after,
  tmr_task_scheduler_source_client external action -> UCOS2_state_inv sg before ->
  kernel_client_step action sg before after -> sem_pend_status_clear_transport before after.
Proof.
  intros external action sg before after Hsource Hvalid.
  destruct Hsource as [action Hnontimer|cut|actor requested priority|
    actor pointer bits result|actor event kind message result|slot previous|
    context outgoing incoming resumed]; intro Hstep.
  - apply sem_pend_source_projection_preserves_clear_status; intros slot old Hold.
    eapply tmr_task_sem_nontimer_projection; eassumption.
  - apply sem_pend_source_projection_preserves_clear_status; intros slot old Hold.
    eapply tmr_task_sem_profile_projection; eassumption.
  - destruct Hstep as [code Hchange].
    apply sem_pend_source_projection_preserves_clear_status; intros slot old Hold.
    eapply tmr_task_sem_change_prio_projection; eassumption.
  - destruct Hstep as [schedule Hready].
    destruct (flag_task_rdy_result _ _ _ _ _ _ _ Hready)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]].
    eapply sem_pend_source_update_preserves_clear_status; [exact Hold|reflexivity|].
    intro Hclear.
    change (task_non_suspension_bits (task_clear_pending_status old.(stat) PendFlag) = 0).
    rewrite task_clear_pending_status_none by exact Hclear; exact Hclear.
  - destruct Hstep as [priority Hready].
    eapply sem_pend_source_event_ready_preserves_clear_status; exact Hready.
  - destruct Hstep as [Hold ->].
    apply sem_pend_source_projection_preserves_clear_status; intros tid node Hnode.
    eapply sem_pend_tick_task_projection; eassumption.
  - apply sem_pend_source_projection_preserves_clear_status; intros slot old Hold.
    eapply sem_pend_source_client_projection;
      [apply SemPendSourceSchedulerInstall|exact Hstep|exact Hold].
Qed.

Lemma tmr_task_source_client_preserves_wait_status : forall external action sg before after,
  tmr_task_source_client external action -> UCOS2_state_inv sg before ->
  kernel_client_step action sg before after -> sem_pend_status_clear_transport before after.
Proof.
  intros external action sg before after Hsource Hvalid.
  destruct Hsource as [action Hscheduler|action Hsem|action Hcritical|actor cut|
    actor cut|actor source_sg cut entry timers|actor event option result|
    actor source_sg priority result entry returned]; intro Hstep.
  - eapply tmr_task_scheduler_source_preserves_wait_status; eassumption.
  - apply sem_pend_source_projection_preserves_clear_status; intros slot old Hold.
    eapply sem_pend_source_client_projection;
      [apply tmr_task_sem_source_client_wait_projection; exact Hsem|exact Hstep|exact Hold].
  - eapply sem_pend_source_critical_preserves_clear_status; eassumption.
  - apply sem_pend_source_projection_preserves_clear_status; intros slot old Hold.
    exact (tmr_task_sem_tick_projection _ cut _ _ _ _ Hstep Hold).
  - destruct Hstep as [timers [_ ->]]; apply sem_pend_status_clear_transport_map_eq; reflexivity.
  - destruct Hstep as [_ [_ [_ ->]]]; apply sem_pend_status_clear_transport_map_eq; reflexivity.
  - destruct Hstep as [node [_ [_ Habort]]].
    apply sem_pend_source_projection_preserves_clear_status; intros slot old Hold.
    eapply sem_pend_abort_critical_projection; eassumption.
  - apply sem_pend_source_projection_preserves_clear_status; intros slot old Hold.
    eapply tmr_task_sem_suspend_projection; eassumption.
Qed.

Definition tmr_task_call_wait_status_inv (call : OsSchedCallContext) sg state : Prop :=
  UCOS2_state_inv sg state /\
  exists node, state.(TskState).(inUsedTaskStates)
    call.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
    task_non_suspension_bits node.(stat) = 0.

Lemma tmr_task_call_wait_status_inv_from_source : forall sg call state,
  UCOS2_state_inv sg state -> kernel_call_task_source call state ->
  tmr_task_caller_wait_status_clear call state -> tmr_task_call_wait_status_inv call sg state.
Proof.
  intros sg call state Hvalid Hsource Hclear; split; [exact Hvalid|].
  destruct (kernel_call_task_source_current_at call state Hsource) as [Hcurrent [node [Hnode Hg]]].
  exists node; split; [exact Hnode|apply Hclear; exact Hnode].
Qed.

Lemma tmr_task_registered_source_wait_status_clients : forall external critical call action,
  tmr_task_registered_source_coverage external critical -> critical.(critical_region_clients) action ->
  kernel_client_preserves_resources (tmr_task_call_wait_status_inv call) action.
Proof.
  intros external critical call action Hcoverage Hin sg before after
    [Hvalid [node [Hnode Hclear]]] Hstep.
  destruct (kernel_client_certificate_preserves_selected_resources action
    (critical_region_client_certificates critical action Hin) sg before after Hvalid Hstep)
    as [Hafter Hframes].
  split; [|exact Hframes]. split; [exact Hafter|].
  exact (tmr_task_source_client_preserves_wait_status external action sg before after
    (proj1 (Hcoverage action Hin)) Hvalid Hstep _ node Hnode Hclear).
Qed.

(** Both intervals are the actual Save/Restore source traces. The state
    and returned descriptor below are the ones in the existing receipt. *)
Lemma tmr_task_fields_checkpoint_wait_status :
  forall checkpoint external environment critical sg original mask before acquired returned current,
  tmr_task_registered_source_coverage external critical ->
  os_sched_fields_checkpoint_sources checkpoint environment critical sg original mask before acquired returned current ->
  (UCOS2_state_inv sg acquired -> UCOS2_state_inv sg (checkpoint acquired)) ->
  (checkpoint acquired).(TskState) = acquired.(TskState) ->
  tmr_task_call_wait_status_inv original sg before ->
  tmr_task_caller_wait_status_clear returned current.
Proof.
  intros checkpoint external environment critical sg original mask before acquired returned current
    Hcoverage Hsources Hcheckpoint Htasks Hbefore.
  assert (Hafter : tmr_task_call_wait_status_inv original sg current).
  { eapply (os_sched_fields_checkpoint_registered_invariant checkpoint environment critical
      (tmr_task_call_wait_status_inv original) sg original mask before acquired returned current).
    - intros action Hin; eapply tmr_task_registered_source_wait_status_clients; eassumption.
    - exact Hsources.
    - intros [Hvalid [node [Hnode Hclear]]]; split; [apply Hcheckpoint; exact Hvalid|].
      exists node; rewrite Htasks; auto.
    - exact Hbefore. }
  destruct (proj2 Hafter) as [node [Hnode Hclear]].
  pose proof (os_sched_fields_checkpoint_same_call checkpoint environment critical sg original
    mask before acquired returned current Hsources) as [_ [_ Hstack]].
  intros actual Hactual; rewrite Hstack in Hactual.
  assert (actual = node) by congruence; subst actual; exact Hclear.
Qed.

Lemma tmr_task_lock_return_wait_status : forall external environment critical sg original mask before returned current,
  tmr_task_registered_source_coverage external critical -> UCOS2_state_inv sg before ->
  kernel_call_task_source original before -> tmr_task_caller_wait_status_clear original before ->
  os_sched_lock_fields_return_sources environment critical sg original mask before returned current ->
  tmr_task_caller_wait_status_clear returned current.
Proof.
  intros external environment critical sg original mask before returned current
    Hcoverage Hvalid Hsource Hclear Hsources.
  unfold os_sched_lock_fields_return_sources in Hsources.
  destruct before.(SchedState).(isRunning) eqn:Hrunning.
  - destruct Hsources as [acquired Hsources].
    eapply (tmr_task_fields_checkpoint_wait_status (os_sched_lock_checkpoint true)
      external environment critical sg original mask before acquired returned current);
      [exact Hcoverage|exact Hsources| |reflexivity|].
    + apply os_sched_lock_checkpoint_preserves_validity.
    + eapply tmr_task_call_wait_status_inv_from_source; eassumption.
  - destruct Hsources as [-> ->]; exact Hclear.
Qed.

Lemma tmr_task_unlock_prefix_wait_status : forall external environment critical sg original mask
  before acquired restored unlocked,
  tmr_task_registered_source_coverage external critical -> UCOS2_state_inv sg before ->
  kernel_call_task_source original before -> tmr_task_caller_wait_status_clear original before ->
  os_sched_fields_checkpoint_sources (os_sched_unlock_checkpoint true)
    environment critical sg original mask before acquired restored unlocked ->
  tmr_task_caller_wait_status_clear restored unlocked.
Proof.
  intros external environment critical sg original mask before acquired restored unlocked
    Hcoverage Hvalid Hsource Hclear Hsources.
  eapply (tmr_task_fields_checkpoint_wait_status (os_sched_unlock_checkpoint true)
    external environment critical sg original mask before acquired restored unlocked);
    [exact Hcoverage|exact Hsources| |reflexivity|].
  - apply os_sched_unlock_checkpoint_preserves_validity.
  - eapply tmr_task_call_wait_status_inv_from_source; eassumption.
Qed.

(** The no-schedule fact is the protected C decision, not an inference
    from the left disjunct of the old spatial return-world assertion. *)
Lemma tmr_task_unlock_no_schedule_wait_status : forall external environment critical sg original mask
  before acquired restored unlocked returned current,
  tmr_task_registered_source_coverage external critical -> UCOS2_state_inv sg before ->
  kernel_call_task_source original before -> tmr_task_caller_wait_status_clear original before ->
  os_sched_fields_checkpoint_sources (os_sched_unlock_checkpoint true)
    environment critical sg original mask before acquired restored unlocked ->
  os_sched_unlock_requests acquired = false ->
  os_sched_unlock_tail_program environment critical sg mask (os_sched_unlock_requests acquired)
    restored unlocked returned current -> tmr_task_caller_wait_status_clear returned current.
Proof.
  intros external environment critical sg original mask before acquired restored unlocked returned current
    Hcoverage Hvalid Hsource Hclear Hsources Hrequest Htail.
  unfold os_sched_unlock_tail_program in Htail; rewrite Hrequest in Htail.
  destruct Htail as [Hreturned Hcurrent]; subst returned current.
  eapply tmr_task_unlock_prefix_wait_status; eassumption.
Qed.

(** This consumes the old Lock post once and retains exactly its output
    pair, heap owner and continuation X. *)
Lemma tmr_task_lock_post_wait_status : forall external environment critical local sg original mask before X,
  tmr_task_registered_source_coverage external critical -> UCOS2_state_inv sg before ->
  kernel_call_task_source original before -> tmr_task_caller_wait_status_clear original before ->
  os_sched_lock_fields_post environment critical local sg original mask before X |--
  EX returned current,
    coq_prop (tmr_task_caller_wait_status_clear returned current /\
      os_sched_lock_continuation_history environment critical sg original mask before returned current /\
      kernel_call_normal_return original before returned current /\
      (kernel_call_task_source original before -> kernel_call_task_source returned current) /\
      os_sched_lock_continuation_control before current /\
      os_sched_lock_fields_return_sources environment critical sg original mask before returned current /\
      safeExec (fun observed => observed = current) (StateRelMonad.ret returned) X) &&
    os_sched_fields_closed environment local sg returned mask current.
Proof.
  intros external environment critical local sg original mask before X Hcoverage Hvalid Hsource Hclear
    heap [returned [current [[Hhistory [Hnormal [Hsource' [Hcontrol [Hsources Hsafe]]]]] Howned]]].
  exists returned, current; split; [|exact Howned].
  split; [eapply tmr_task_lock_return_wait_status; eassumption|].
  exact (conj Hhistory (conj Hnormal (conj Hsource' (conj Hcontrol (conj Hsources Hsafe))))).
Qed.

Lemma tmr_task_caller_wait_status_replace_timers : forall call state timers,
  tmr_task_caller_wait_status_clear call state ->
  tmr_task_caller_wait_status_clear call (replace_TimerS timers state).
Proof. intros call state timers Hclear; exact Hclear. Qed.
