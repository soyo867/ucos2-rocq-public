Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_client_loop_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_continuation_annotation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Coq.Lists.List.
Import ListNotations Monad MonadNotation.

(** Reuse the existing history record and its Timer-only projections.
    The relation stored in that record is the actual client-level Pend,
    with the original Lock, scan, callback and Unlock programs. *)
Section TaskClientAnnotations.
Context {Application : Type}.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (mask : Z) (effects : TmrTaskEffects Application).

Definition tmr_task_client_history original_context original
  (history : TmrTaskContinuationHistory Application) : Prop :=
  tmr_task_client_prefix environment critical sg mask effects original original_context
    history.(tmr_task_continuation_completed) history.(tmr_task_continuation_before)
    history.(tmr_task_continuation_context) /\
  tmr_task_client_pend_program environment critical sg effects
    history.(tmr_task_continuation_context)
    (tmr_task_timers history.(tmr_task_continuation_before)).(timerSignalSem)
    history.(tmr_task_continuation_before)
    (history.(tmr_task_continuation_error), history.(tmr_task_continuation_wait_context))
    history.(tmr_task_continuation_waited) /\
  tmr_task_continuation_lock_program environment critical sg mask effects
    history.(tmr_task_continuation_wait_context) history.(tmr_task_continuation_waited)
    history.(tmr_task_continuation_lock_context) history.(tmr_task_continuation_locked).

(** count denotes an arbitrary finite observation of the infinite loop.
    It is never an executable loop bound, and the same X is retained. *)
Definition tmr_task_client_scan_safe context completed error visited spoke scan
  (world : tmr_task_scan_world Application)
  (X : (list TmrTaskIterationObservation * OsSchedCallContext) ->
    tmr_task_scan_world Application -> Prop) : Prop :=
  forall count, safeExec (eq world)
    (bind (tmr_task_scan_program sg (tmr_task_callback_program effects) spoke context scan)
      (fun tail =>
    bind (tmr_task_continuation_unlock_program environment critical sg mask effects (snd tail))
      (fun returned =>
    bind (tmr_task_client_prefix_program environment critical sg mask effects count returned)
      (fun later => ret
        (completed ++ {| tmr_task_wait_error := error;
                         tmr_task_iteration_events := visited ++ fst tail;
                         tmr_task_iteration_context := returned |} :: fst later,
         snd later))))) X.

Definition tmr_task_client_scan_facts original_context original history visited
  context world scan X : Prop :=
  tmr_task_client_history original_context original history /\
  tmr_task_scan_prefix sg (tmr_task_callback_program effects)
    (tmr_task_continuation_spoke sg history)
    (tmr_task_continuation_start history) history.(tmr_task_continuation_lock_context)
    (tmr_task_continuation_scan sg history) visited world context scan /\
  timer_scan_continuation_valid sg (tmr_task_timers world) scan /\
  tmr_task_spoke_in_range sg (tmr_task_continuation_spoke sg history) /\
  valid_timer_state sg (tmr_task_timers world) /\
  timer_api_initialized (tmr_task_timers world) /\
  tmr_task_service_frame (tmr_task_timers (tmr_task_continuation_start history))
    (tmr_task_timers world) /\
  tmr_task_client_scan_safe context history.(tmr_task_continuation_completed)
    history.(tmr_task_continuation_error) visited (tmr_task_continuation_spoke sg history)
    scan world X.

Lemma tmr_task_client_history_from_calls : forall original_context original context
  completed before error wait_context waited lock_context locked,
  tmr_task_client_prefix environment critical sg mask effects
    original original_context completed before context ->
  tmr_task_client_pend_program environment critical sg effects context
    (tmr_task_timers before).(timerSignalSem) before (error, wait_context) waited ->
  tmr_task_continuation_lock_program environment critical sg mask effects
    wait_context waited lock_context locked ->
  tmr_task_client_history original_context original
    {| tmr_task_continuation_before := before;
       tmr_task_continuation_context := context;
       tmr_task_continuation_completed := completed;
       tmr_task_continuation_error := error;
       tmr_task_continuation_waited := waited;
       tmr_task_continuation_wait_context := wait_context;
       tmr_task_continuation_locked := locked;
       tmr_task_continuation_lock_context := lock_context |}.
Proof.
  intros original_context original context completed before error wait_context waited
    lock_context locked Hprefix Hpend Hlock.
  unfold tmr_task_client_history; cbn.
  split; [exact Hprefix|split; assumption].
Qed.

Lemma tmr_task_client_history_from_pend_source : forall original_context original context
  completed before error wait_context waited lock_context locked,
  tmr_task_client_prefix environment critical sg mask effects
    original original_context completed before context ->
  sem_pend_client_runtime_program environment critical sg context
    (tmr_task_timers before).(timerSignalSem) 0 (fst before) error (fst waited) ->
  kernel_stack_call_same_call wait_context context ->
  tmr_task_pend_application effects context before error wait_context waited ->
  tmr_task_continuation_lock_program environment critical sg mask effects
    wait_context waited lock_context locked ->
  tmr_task_client_history original_context original
    {| tmr_task_continuation_before := before;
       tmr_task_continuation_context := context;
       tmr_task_continuation_completed := completed;
       tmr_task_continuation_error := error;
       tmr_task_continuation_waited := waited;
       tmr_task_continuation_wait_context := wait_context;
       tmr_task_continuation_locked := locked;
       tmr_task_continuation_lock_context := lock_context |}.
Proof.
  intros original_context original context completed before error wait_context waited
    lock_context locked Hprefix Hsource Hsame Happ Hlock.
  apply tmr_task_client_history_from_calls; [exact Hprefix| |exact Hlock].
  split; [exact Hsource|split; assumption].
Qed.

End TaskClientAnnotations.
