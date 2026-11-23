Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Ucos2Verify.lib.timer Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.task Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.tick.
Require Import Ucos2Verify.VC.code.core.spec.kernel_client_resumption.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_lock_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_effect_properties_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_phase_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_legacy_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_lock_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_continuation_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_sw_hook_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_acquire_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_checkpoint_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_continuation_loop_spec.
Import TaskStateDef.
Local Open Scope Z_scope.

Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_program_spec.

(** Source-history consumers belong above the primitive action proofs.
    Each branch below uses its own actual source: old history, a timer
    trace, or the same completed C Scheduler call. *)
Lemma tmr_task_fields_pend_source_history_preserves_initialized :
  forall environment critical sg original eid generation before after,
  (forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action) ->
  tmr_task_fields_action_preserves_initialized sg
    environment.(task_stack_call_external).(os_sched_hook_action) ->
  sem_pend_source_history environment critical sg original eid generation before after ->
  timer_api_initialized before.(TimerState) -> timer_api_initialized after.(TimerState).
Proof.
  intros environment critical sg original eid generation before after Hclients Hhook Hhistory Hinit.
  eapply sem_pend_source_history_preserves_property
    with (property := fun state => timer_api_initialized state.(TimerState)).
  - intros entry current Hlegacy Hentry.
    eapply tmr_task_fields_pend_wait_preserves_initialized; eassumption.
  - intros entry current Htimer Hentry.
    eapply timer_public_storage_frame_initialized; [|exact Hentry].
    eapply timer_public_trace_public_storage_frame; exact Htimer.
  - intros entry entered returned current Hsame Hreturn Hentry.
    eapply tmr_task_fields_sched_c_return_preserves_initialized; eassumption.
  - exact Hhistory.
  - exact Hinit.
Qed.

Lemma tmr_task_fields_pend_source_checkpoint_preserves_initialized :
  forall environment critical sg call pevent timeout before error checkpoint,
  (forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action) ->
  tmr_task_fields_action_preserves_initialized sg
    environment.(task_stack_call_external).(os_sched_hook_action) ->
  sem_pend_source_checkpoint_result (Some environment) critical sg call pevent timeout
    before error checkpoint ->
  timer_api_initialized before.(TimerState) -> timer_api_initialized checkpoint.(TimerState).
Proof.
  intros environment critical sg call pevent timeout before error checkpoint Hclients Hhook
    (eid & observed & returned & mask & saved & entry & current & start & waiting &
      Hnonnull & Haddress & Hid & Hslot & Hcontext & Hacquire & Hfirst & Hresult) Hinit.
  change (sem_pend_acquire_observation environment critical sg call returned mask saved
    before entry eid observed current) in Hacquire.
  assert (Hentry : timer_api_initialized entry.(TimerState)).
  { eapply timer_public_storage_frame_initialized; [|exact Hinit].
    eapply timer_public_trace_public_storage_frame.
    eapply tmr_task_fields_pend_save_timer_trace; exact (proj1 Hacquire). }
  assert (Hwaiting : timer_api_initialized waiting.(TimerState)).
  { rewrite (tmr_task_fields_pend_first_timer_state_eq sg eid timeout entry start waiting Hfirst).
    exact Hentry. }
  destruct start as [|tid generation].
  - destruct Hresult as [_ ->]; exact Hwaiting.
  - destruct Hresult as [_ [owned [resumed [node [code
      [Howned [Hwait [_ [_ [_ Hcleanup]]]]]]]]]].
    injection Howned as Howned; subst owned.
    rewrite (tmr_task_fields_pend_cleanup_timer_state_eq sg eid resumed code checkpoint Hcleanup).
    eapply tmr_task_fields_pend_source_history_preserves_initialized; eassumption.
Qed.

Lemma tmr_task_fields_pend_source_runtime_preserves_initialized :
  forall external platform environment critical sg call pevent timeout before error current,
  (forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action) ->
  tmr_task_fields_action_preserves_initialized sg
    environment.(task_stack_call_external).(os_sched_hook_action) ->
  sem_pend_source_runtime_program external platform (Some environment) critical sg call
    pevent timeout before error current ->
  timer_api_initialized before.(TimerState) -> timer_api_initialized current.(TimerState).
Proof.
  intros external platform environment critical sg call pevent timeout before error current
    Hclients Hhook Hrun Hinit.
  destruct Hrun as [[Hearly [Hguard ->]]|
    [checkpoint [entered [returned [eid [Hcheckpoint [_ [_ [_ [_ Hrestore]]]]]]]]]].
  - exact Hinit.
  - eapply timer_public_storage_frame_initialized.
    + eapply timer_public_trace_public_storage_frame.
      eapply tmr_task_fields_pend_restore_timer_trace; exact Hrestore.
    + eapply tmr_task_fields_pend_source_checkpoint_preserves_initialized; eassumption.
Qed.

(** The existing loop-level statements retain the same arbitrary caller
    and application state; Pend now consumes the expanded actual source. *)
Lemma tmr_task_fields_task_pend_preserves_initialized : forall Application environment critical sg
  (effects : TmrTaskEffects Application) call signal before output after,
  (forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action) ->
  tmr_task_fields_action_preserves_initialized sg
    environment.(task_stack_call_external).(os_sched_hook_action) ->
  tmr_task_continuation_pend_program environment critical sg effects call signal before output after ->
  timer_api_initialized (tmr_task_timers before) -> timer_api_initialized (tmr_task_timers after).
Proof.
  intros Application environment critical sg effects call signal before output after Hclients Hhook
    [Hpend Happlication] Hinit.
  eapply tmr_task_fields_pend_source_runtime_preserves_initialized; eassumption.
Qed.

Lemma tmr_task_fields_task_lock_preserves_initialized : forall Application environment critical sg mask
  (effects : TmrTaskEffects Application) call before returned after,
  tmr_task_continuation_lock_program environment critical sg mask effects call before returned after ->
  timer_api_initialized (tmr_task_timers before) -> timer_api_initialized (tmr_task_timers after).
Proof.
  intros Application environment critical sg mask effects call before returned after [Hlock Happlication] Hinit.
  eapply tmr_task_fields_lock_program_preserves_initialized; eassumption.
Qed.

Lemma tmr_task_fields_task_unlock_preserves_initialized : forall Application environment critical sg mask
  (effects : TmrTaskEffects Application) call before returned after,
  (forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action) ->
  tmr_task_continuation_unlock_program environment critical sg mask effects call before returned after ->
  timer_api_initialized (tmr_task_timers before) -> timer_api_initialized (tmr_task_timers after).
Proof.
  intros Application environment critical sg mask effects call before returned after Hclients
    [Hunlock Happlication] Hinit.
  eapply tmr_task_fields_unlock_program_preserves_initialized; eassumption.
Qed.

Lemma tmr_task_fields_task_pend_named_source_preserves_initialized :
  forall Application external environment critical sg (effects : TmrTaskEffects Application)
    call signal before output after,
  (forall action, critical.(critical_region_clients) action -> sched_task_source_client external action) ->
  task_sw_hook_source_binding environment.(task_stack_call_external) ->
  tmr_task_continuation_pend_program environment critical sg effects call signal before output after ->
  timer_api_initialized (tmr_task_timers before) -> timer_api_initialized (tmr_task_timers after).
Proof.
  intros Application external environment critical sg effects call signal before output after
    Hsource Hbinding Hrun Hinit.
  eapply tmr_task_fields_task_pend_preserves_initialized.
  - eapply tmr_task_fields_named_clients_preserve_initialized; exact Hsource.
  - apply tmr_task_fields_bound_hook_preserves_initialized; exact Hbinding.
  - exact Hrun.
  - exact Hinit.
Qed.

Lemma tmr_task_fields_task_unlock_named_source_preserves_initialized :
  forall Application external environment critical sg mask (effects : TmrTaskEffects Application)
    call before returned after,
  (forall action, critical.(critical_region_clients) action -> sched_task_source_client external action) ->
  tmr_task_continuation_unlock_program environment critical sg mask effects call before returned after ->
  timer_api_initialized (tmr_task_timers before) -> timer_api_initialized (tmr_task_timers after).
Proof.
  intros Application external environment critical sg mask effects call before returned after Hsource Hrun Hinit.
  eapply tmr_task_fields_task_unlock_preserves_initialized.
  - eapply tmr_task_fields_named_clients_preserve_initialized; exact Hsource.
  - exact Hrun.
  - exact Hinit.
Qed.
