Require Import Coq.ZArith.ZArith.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.timer.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_acquire_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_program_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_continuation_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_loop_spec.
Import TaskStateDef.
Local Open Scope Z_scope.

(** The actual Task needs the initialization phase to stay finished.
    Allocation's private image change is allowed. Each path below uses
    its real source, including the unchanged four-case Scheduler body. *)
Lemma tmr_task_client_wait_source_preserves_initialized :
  forall environment critical sg original eid generation before after,
  (forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action) ->
  tmr_task_fields_action_preserves_initialized sg
    environment.(task_stack_call_external).(os_sched_hook_action) ->
  sem_pend_client_wait_source environment critical sg original eid generation before after ->
  timer_api_initialized before.(TimerState) -> timer_api_initialized after.(TimerState).
Proof.
  intros environment critical sg original eid generation before after Hclients Hhook Hsource.
  induction Hsource as [before after Hlegacy|before call returned after Hsame Hreturn|
    before call returned after Hsame Hbody|before middle after Hfirst IHfirst Hlast IHlast]; intro Hinit.
  - eapply tmr_task_fields_pend_source_history_preserves_initialized; eassumption.
  - eapply sem_pend_client_return_source_preserves_timer_initialized; eassumption.
  - eapply tmr_task_fields_sched_body_preserves_initialized; eassumption.
  - apply IHlast, IHfirst; exact Hinit.
Qed.

Lemma tmr_task_client_checkpoint_preserves_initialized :
  forall environment critical sg call pevent timeout before error checkpoint,
  (forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action) ->
  tmr_task_fields_action_preserves_initialized sg
    environment.(task_stack_call_external).(os_sched_hook_action) ->
  sem_pend_client_checkpoint_result environment critical sg call pevent timeout before error checkpoint ->
  timer_api_initialized before.(TimerState) -> timer_api_initialized checkpoint.(TimerState).
Proof.
  intros environment critical sg call pevent timeout before error checkpoint Hclients Hhook
    (eid & observed & returned & mask & saved & entry & current & start & waiting &
      Hnonnull & Haddress & Hid & Hslot & Hcontext & Hacquire & Hfirst & Hresult) Hinit.
  assert (Hentry : timer_api_initialized entry.(TimerState)).
  { eapply sem_pend_client_return_source_preserves_timer_initialized;
      [exact (proj1 Hacquire)|exact Hinit]. }
  assert (Hwaiting : timer_api_initialized waiting.(TimerState)).
  { rewrite (tmr_task_fields_pend_first_timer_state_eq sg eid timeout entry start waiting Hfirst).
    exact Hentry. }
  destruct start as [|tid generation].
  - destruct Hresult as [_ ->]; exact Hwaiting.
  - destruct Hresult as [_ [resumed [node [code [Hwait [_ [_ [_ Hcleanup]]]]]]]].
    rewrite (tmr_task_fields_pend_cleanup_timer_state_eq sg eid resumed code checkpoint Hcleanup).
    eapply tmr_task_client_wait_source_preserves_initialized; eassumption.
Qed.

Lemma tmr_task_client_runtime_preserves_initialized :
  forall environment critical sg call pevent timeout before error current,
  (forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action) ->
  tmr_task_fields_action_preserves_initialized sg
    environment.(task_stack_call_external).(os_sched_hook_action) ->
  sem_pend_client_runtime_program environment critical sg call pevent timeout before error current ->
  timer_api_initialized before.(TimerState) -> timer_api_initialized current.(TimerState).
Proof.
  intros environment critical sg call pevent timeout before error current Hclients Hhook
    [Hlegacy|[checkpoint [entered [returned [Hcheckpoint [Hsame Hrestore]]]]]] Hinit.
  - eapply tmr_task_fields_pend_source_runtime_preserves_initialized; eassumption.
  - eapply sem_pend_client_return_source_preserves_timer_initialized; [exact Hrestore|].
    eapply tmr_task_client_checkpoint_preserves_initialized; eassumption.
Qed.

Lemma tmr_task_client_pend_preserves_initialized : forall Application environment critical sg
  (effects : TmrTaskEffects Application) call signal before output after,
  (forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action) ->
  tmr_task_fields_action_preserves_initialized sg
    environment.(task_stack_call_external).(os_sched_hook_action) ->
  tmr_task_client_pend_program environment critical sg effects call signal before output after ->
  timer_api_initialized (tmr_task_timers before) -> timer_api_initialized (tmr_task_timers after).
Proof.
  intros Application environment critical sg effects call signal before output after Hclients Hhook
    [Hpend Hrest] Hinit.
  eapply tmr_task_client_runtime_preserves_initialized; eassumption.
Qed.
