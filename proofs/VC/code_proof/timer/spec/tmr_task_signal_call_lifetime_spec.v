Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_lock_fields_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_fields_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_lock_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.mutex_query_spec Ucos2Verify.lib.timer.

(** This transports the current object over the actual registered interval.
    The existing handle protocol and the interval's certified steps supply
    the live object; no future Pend-admission fact is assumed. *)
Lemma tmr_task_signal_lifetime_interval : forall critical sg invocation before after,
  UCOS2_state_inv sg before ->
  tmr_task_signal_lifetime critical sg invocation before ->
  critical_region_interval critical sg invocation before after ->
  tmr_task_signal_lifetime critical sg invocation after.
Proof.
  intros critical sg invocation before after Hvalid Hlife Hinterval.
  pose proof (tmr_task_signal_interval_value critical sg invocation before after Hinterval)
    as Hsignal.
  destruct Hlife as [Hnull|[eid [previous
    [Hnonnull [Haddress [Hid [Hlookup [Htype Hprotocol]]]]]]]].
  - left; rewrite Hsignal; exact Hnull.
  - destruct (mutex_query_handle_interval_preserves_identity critical sg invocation eid
      before after previous Hprotocol Hinterval Hvalid Hlookup)
      as [current [Hcurrent [Hgeneration Hcurrent_type]]].
    right; exists eid, current.
    split; [rewrite Hsignal; exact Hnonnull|].
    split; [rewrite Hsignal; exact Haddress|]. split; [exact Hid|].
    split; [exact Hcurrent|]. split; [congruence|exact Hprotocol].
Qed.

(** The two intervals and the returned invocation come from the SAME
    fields-call source receipt. Lock and the Unlock prefix change only
    interrupt counters at their local checkpoint. *)
Lemma tmr_task_fields_checkpoint_preserves_signal_lifetime :
  forall (checkpoint : UCOS2_Verify_State -> UCOS2_Verify_State)
    environment critical sg original mask before acquired returned current,
  (forall state, UCOS2_state_inv sg state -> UCOS2_state_inv sg (checkpoint state)) ->
  (forall state, (checkpoint state).(TimerState) = state.(TimerState)) ->
  (forall state, (checkpoint state).(EventState) = state.(EventState)) ->
  UCOS2_state_inv sg before ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) before ->
  os_sched_fields_checkpoint_sources checkpoint environment critical sg original mask
    before acquired returned current ->
  tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current.
Proof.
  intros checkpoint environment critical sg original mask before acquired returned current
    Hcheckpoint Htimers Hevents Hvalid Hlife [entered [saved [Hsave [Hrestore Hsame]]]].
  pose proof (kernel_call_save_source_region_interval environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original entered mask saved before acquired Hsave)
    as Hsave_interval.
  pose proof (proj1 (critical_region_interval_transports_resources critical sg
    original.(os_sched_call_invocation) before acquired Hsave_interval Hvalid)) as Hacquired.
  pose proof (tmr_task_signal_lifetime_interval critical sg original.(os_sched_call_invocation)
    before acquired Hvalid Hlife Hsave_interval) as Hsaved_life.
  assert (Hentered_same : kernel_stack_call_same_call entered original).
  { destruct Hsave as [_ [Hinv [Horigin [Hstack Hmask]]]].
    split; [exact Hinv|]. split; assumption. }
  pose proof (tmr_task_signal_lifetime_same_call critical sg original entered acquired
    Hentered_same Hsaved_life) as Hentered_life.
  assert (Hcheckpoint_identity : tmr_task_signal_identity_preserved sg acquired (checkpoint acquired)).
  { split; [rewrite Htimers; reflexivity|].
    intros eid previous Hnonnull Haddress Hlookup.
    exists previous; split.
    - unfold mutex_query_lookup in *; rewrite Hevents; exact Hlookup.
    - split; reflexivity. }
  pose proof (tmr_task_signal_lifetime_preserved critical sg entered.(os_sched_call_invocation)
    acquired (checkpoint acquired) Hentered_life Hcheckpoint_identity) as Hreleased_life.
  pose proof (proj1 (kernel_resumption_task_source_trace_erases
    environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg entered.(os_sched_call_invocation) None
    entered.(os_sched_call_origin) (checkpoint acquired) false returned.(os_sched_call_origin)
    current Hrestore)) as Hrestore_interval.
  change (critical_region_interval critical sg entered.(os_sched_call_invocation)
    (checkpoint acquired) current) in Hrestore_interval.
  eapply tmr_task_signal_lifetime_same_call; [exact Hsame|].
  eapply tmr_task_signal_lifetime_interval;
    [apply Hcheckpoint; exact Hacquired|exact Hreleased_life|exact Hrestore_interval].
Qed.

(** For the Task assertion immediately after its literal Lock
    call. The source receipt is already present in that call's actual
    post; this does not add a new guarantee to the callee contract. *)
Lemma tmr_task_lock_fields_return_preserves_signal_lifetime :
  forall environment critical sg original mask before returned current,
  UCOS2_state_inv sg before ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) before ->
  os_sched_lock_fields_return_sources environment critical sg original mask before returned current ->
  tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current.
Proof.
  intros environment critical sg original mask before returned current Hvalid Hlife Hsource.
  unfold os_sched_lock_fields_return_sources in Hsource.
  destruct before.(SchedState).(isRunning).
  - destruct Hsource as [acquired Hsource].
    eapply tmr_task_fields_checkpoint_preserves_signal_lifetime
      with (checkpoint := os_sched_lock_checkpoint true) (acquired := acquired);
      [intros state Hstate; apply os_sched_lock_checkpoint_preserves_validity; exact Hstate|
       intros; reflexivity|
       intros; reflexivity|exact Hvalid|exact Hlife|exact Hsource].
  - destruct Hsource as [-> ->]; exact Hlife.
Qed.

Lemma tmr_task_unlock_fields_prefix_preserves_signal_lifetime :
  forall environment critical sg original mask before acquired restored unlocked,
  UCOS2_state_inv sg before ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) before ->
  os_sched_fields_checkpoint_sources (os_sched_unlock_checkpoint true)
    environment critical sg original mask before acquired restored unlocked ->
  tmr_task_signal_lifetime critical sg restored.(os_sched_call_invocation) unlocked.
Proof.
  intros environment critical sg original mask before acquired restored unlocked Hvalid Hlife Hsource.
  eapply tmr_task_fields_checkpoint_preserves_signal_lifetime
    with (checkpoint := os_sched_unlock_checkpoint true) (acquired := acquired);
    [intros state Hstate; apply os_sched_unlock_checkpoint_preserves_validity; exact Hstate|
     intros; reflexivity|intros; reflexivity|exact Hvalid|exact Hlife|exact Hsource].
Qed.

(** This is the real false scheduling branch of the retained source
    packet. The true branch still needs its actual Scheduler execution;
    no conclusion about it is included in this theorem. *)
Lemma tmr_task_unlock_fields_no_schedule_preserves_signal_lifetime :
  forall environment critical sg original mask before acquired restored unlocked returned current,
  UCOS2_state_inv sg before ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) before ->
  os_sched_fields_checkpoint_sources (os_sched_unlock_checkpoint true)
    environment critical sg original mask before acquired restored unlocked ->
  os_sched_unlock_requests acquired = false ->
  os_sched_unlock_tail_program environment critical sg mask (os_sched_unlock_requests acquired)
    restored unlocked returned current ->
  tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current.
Proof.
  intros environment critical sg original mask before acquired restored unlocked returned current
    Hvalid Hlife Hsource Hrequest Htail.
  unfold os_sched_unlock_tail_program in Htail; rewrite Hrequest in Htail.
  destruct Htail as [Hreturned Hcurrent]; subst returned current.
  eapply tmr_task_unlock_fields_prefix_preserves_signal_lifetime; eassumption.
Qed.
