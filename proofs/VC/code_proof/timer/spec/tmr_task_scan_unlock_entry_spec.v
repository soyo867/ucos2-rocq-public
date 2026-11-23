Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_unlock_fields_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_registered_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_callback_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_repaired_scan_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_lock_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_return_facts_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.kernel_runtime_inv.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Coq.Lists.List Coq.ZArith.ZArith.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The current iteration input already contains these six observations.
    For a completed Pend, this producer uses its actual task stage, normal
    return, Idle observation and cleared multi pointer. In particular the
    configured absence of multi-event C fields is not a pointer proof. *)
Lemma tmr_task_pend_return_unlock_entry : forall sg original before returned current,
  kernel_call_stack_available original before ->
  kernel_call_normal_return original before returned current ->
  sem_pend_task_call_stage sg returned current ->
  kernel_running_idle_ready sg current ->
  (forall node, current.(TskState).(inUsedTaskStates)
    returned.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
    node.(tcbEventMultiPtr) = 0) ->
  tmr_task_unlock_entry sg returned current.
Proof.
  intros sg original before returned current Havailable Hnormal Hstage Hidle Hpointer.
  pose proof (tmr_task_fields_caller_clear_from_pend sg returned current Hstage Hpointer)
    as Hclear.
  destruct Hstage as [Hsource [Hrunning [node [Hready [Hgeneration Hrest]]]]].
  assert (Hcurrent : os_sched_task_current_ready returned current).
  { exists node; exact (conj Hready Hgeneration). }
  split; [exact Hsource|]. split; [exact (proj2 Hnormal Havailable)|].
  split; [exact Hrunning|]. split.
  - exact (SchedulerReturnFacts.os_sched_task_current_ready_current_consistency
      returned current Hcurrent).
  - split; [apply Hidle; exact Hrunning|exact Hclear].
Qed.

(** This handles an unchanged early-error state with its actual descriptor.
    The descriptor may contain new stack fragments; its invocation, origin
    and lease are the same. No post-error task stage is assumed. *)
Lemma tmr_task_unlock_entry_same_call : forall sg original returned state,
  kernel_stack_call_same_call returned original ->
  tmr_task_unlock_entry sg original state -> tmr_task_unlock_entry sg returned state.
Proof.
  intros sg original returned state [Hi [Ho Hstack]] Hentry.
  unfold tmr_task_unlock_entry, kernel_call_task_source,
    kernel_call_stack_available, tmr_task_fields_caller_clear in *.
  rewrite Hi, Ho, Hstack; exact Hentry.
Qed.

(** All Timer-only C writes use this literal state constructor. It leaves
    the executing invocation, parked stack map, scheduler and task fields
    unchanged; Timer validity is a separate existing scan obligation. *)
Lemma tmr_task_unlock_entry_replace_timers : forall sg call state timers,
  tmr_task_unlock_entry sg call state ->
  tmr_task_unlock_entry sg call (replace_TimerS timers state).
Proof. intros sg call state timers Hentry; exact Hentry. Qed.

(** Each source interval below is the one saved in the actual Lock post.
    Registry coverage supplies the three existing preservation instances;
    no selected-source restriction is introduced. *)
Lemma tmr_task_lock_return_unlock_entry : forall external environment critical sg
  original mask before returned current,
  tmr_task_registered_source_coverage external critical ->
  UCOS2_state_inv sg before -> tmr_task_unlock_entry sg original before ->
  kernel_call_normal_return original before returned current ->
  (kernel_call_task_source original before -> kernel_call_task_source returned current) ->
  os_sched_lock_continuation_control before current ->
  os_sched_lock_fields_return_sources environment critical sg original mask before returned current ->
  tmr_task_unlock_entry sg returned current.
Proof.
  intros external environment critical sg original mask before returned current
    Hcoverage Hvalid Hentry Hnormal Hsource_return Hcontrol Hsources.
  destruct (tmr_task_unlock_entry_invariants sg original before Hvalid Hentry)
    as [Hcurrent_inv [Hidle_inv [Hclear_inv Hready]]].
  destruct (tmr_task_registered_source_unlock_clients external critical original Hcoverage)
    as [Hcurrent_clients [Hidle_clients Hclear_clients]].
  pose proof (os_sched_lock_fields_return_registered_current environment critical sg original mask
    before returned current Hcurrent_clients Hsources Hvalid (proj2 Hcurrent_inv)) as Hcurrent.
  destruct (os_sched_lock_fields_return_idle_non_idle environment critical sg original mask
    before returned current Hidle_clients Hsources Hidle_inv) as [Hidle Hnonidle].
  destruct (os_sched_lock_fields_return_registered_clear environment critical sg original mask
    before returned current Hclear_clients Hsources Hclear_inv)
    as [node [Hnode [Hclear Hflag]]].
  destruct Hnonidle as [actual [Hactual [Hgeneration Hpriority]]].
  assert (actual = node) by congruence; subst actual.
  destruct Hentry as [Hsource [Havailable [Hrunning Hrest]]].
  split; [apply Hsource_return; exact Hsource|].
  split; [exact (proj2 Hnormal Havailable)|].
  split; [rewrite (proj1 Hcontrol); exact Hrunning|].
  split; [exact Hcurrent|]. split; [exact Hidle|].
  intros observed Hobserved.
  assert (observed = node) by congruence; subst observed.
  exact (conj Hpriority (conj Hclear Hflag)).
Qed.

(** Open the real post once. The strengthened observation is attached to
    that very returned/current pair and the same closed owner and X. *)
Lemma tmr_task_lock_post_unlock_entry : forall external environment critical local sg
  original mask before X,
  tmr_task_registered_source_coverage external critical ->
  UCOS2_state_inv sg before -> tmr_task_unlock_entry sg original before ->
  os_sched_lock_fields_post environment critical local sg original mask before X |--
  EX returned current,
    coq_prop (tmr_task_unlock_entry sg returned current /\
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
  split.
  - eapply tmr_task_lock_return_unlock_entry; eassumption.
  - exact (conj Hhistory (conj Hnormal (conj Hsource (conj Hcontrol (conj Hsources Hsafe))))).
Qed.

(** The callback's already selected body contract preserves every entry
    observation conditionally. It does not promise current readiness or a
    later successful Pend, and its arbitrary returned state is retained. *)
Lemma tmr_task_callback_return_unlock_entry : forall Application sg callback fn self argument
  context (before : tmr_task_scan_world Application) returned after,
  tmr_task_fields_callback_return_facts sg callback fn self argument context before returned after ->
  tmr_task_unlock_entry sg context (fst before) ->
  tmr_task_unlock_entry sg returned (fst after).
Proof.
  intros Application sg callback fn self argument context before returned after
    [Hcall [Hready [Hservice [Hsame Hpreserves]]]]
    [Hsource [Havailable [Hrunning [Hcurrent [Hidle Hclear]]]]].
  destruct Hpreserves as [Hsource' Havailable' Hrunning' Hclear' Hidle' Hpublic Hcurrent'].
  split; [apply Hsource'; exact Hsource|]. split; [apply Havailable'; exact Havailable|].
  split; [apply Hrunning'; exact Hrunning|]. split; [apply Hcurrent'; exact Hcurrent|].
  split; [apply Hidle'; exact Hidle|apply Hclear'; exact Hclear].
Qed.

Lemma tmr_task_callback_post_unlock_entry : forall Application AppRep environment sg callback mask perr
  fn self argument context (before : tmr_task_scan_world Application) arguments result,
  tmr_task_unlock_entry sg context (fst before) ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_fields_callback_post AppRep environment sg callback mask perr
      fn self argument context before arguments result)
    (fun heap => exists returned after,
      arguments = (self, argument) /\
      tmr_task_fields_callback_return_facts sg callback fn self argument context before returned after /\
      tmr_task_unlock_entry sg returned (fst after) /\
      tmr_task_current_fields_owned AppRep environment sg mask perr returned after heap).
Proof.
  intros Application AppRep environment sg callback mask perr fn self argument context before
    arguments result Hentry heap [returned [after [Harguments [Hfacts Howned]]]].
  exists returned, after; split; [exact Harguments|]. split; [exact Hfacts|].
  split; [eapply tmr_task_callback_return_unlock_entry; eassumption|exact Howned].
Qed.

(** These are the two actual scan constructors. Their callback premise is
    the already observed return packet, not a universal restriction of the
    raw callback program. The empty scan and pointer reads keep the current
    entry unchanged. *)
Lemma tmr_task_scan_cached_unlock_entry : forall Application sg callback spoke
  (before : tmr_task_scan_world Application) context scan index rest future next dispatched,
  tmr_task_unlock_entry sg context (fst before) ->
  scan.(timerScanRemaining) = index :: rest ->
  timer_scan_advance (tmr_task_timers before) scan = Some future ->
  timer_expire_dispatch sg (tmr_task_timers before) index = Some (next, None, dispatched) ->
  tmr_task_scan_step sg callback spoke before context scan (index, None)
    (tmr_task_set_timers dispatched before) context future /\
  tmr_task_unlock_entry sg context (fst (tmr_task_set_timers dispatched before)).
Proof.
  intros Application sg callback spoke before context scan index rest future next dispatched
    Hentry Hremaining Hadvance Hdispatch.
  split; [eapply TmrTaskScanCachedNext; eassumption|].
  apply tmr_task_unlock_entry_replace_timers; exact Hentry.
Qed.

Lemma tmr_task_scan_callback_unlock_entry : forall Application sg callback spoke
  (before : tmr_task_scan_world Application) context scan index rest future next dispatched
  fn self argument returned after,
  tmr_task_unlock_entry sg context (fst before) ->
  scan.(timerScanRemaining) = index :: rest ->
  timer_scan_advance (tmr_task_timers before) scan = Some future ->
  timer_expire_dispatch sg (tmr_task_timers before) index =
    Some (next, Some (fn, self, argument), dispatched) ->
  tmr_task_fields_callback_return_facts sg callback fn self argument context
    (tmr_task_set_timers dispatched before) returned after ->
  tmr_task_scan_step sg callback spoke before context scan (index, Some (fn, self, argument))
    after returned (tmr_task_scan_at_spoke spoke (tmr_task_timers after)) /\
  tmr_task_unlock_entry sg returned (fst after).
Proof.
  intros Application sg callback spoke before context scan index rest future next dispatched
    fn self argument returned after Hentry Hremaining Hadvance Hdispatch Hreturn.
  split.
  - eapply TmrTaskScanReloadHead; [exact Hremaining|exact Hadvance|exact Hdispatch|].
    exact (proj1 Hreturn).
  - eapply tmr_task_callback_return_unlock_entry; [exact Hreturn|].
    apply tmr_task_unlock_entry_replace_timers; exact Hentry.
Qed.
