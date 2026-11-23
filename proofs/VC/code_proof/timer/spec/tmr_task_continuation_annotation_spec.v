Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_continuation_loop_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_annotation_spec.
Require Import Coq.Lists.List.
Import ListNotations Monad MonadNotation.

(** Lock can return a new ghost call descriptor. The C function is still
    void. Recording that actual descriptor prevents the following scan from
    silently reusing the descriptor observed before Lock. *)
Record TmrTaskContinuationHistory (Application : Type) : Type := {
  tmr_task_continuation_before : tmr_task_scan_world Application;
  tmr_task_continuation_context : OsSchedCallContext;
  tmr_task_continuation_completed : list TmrTaskIterationObservation;
  tmr_task_continuation_error : Z;
  tmr_task_continuation_waited : tmr_task_scan_world Application;
  tmr_task_continuation_wait_context : OsSchedCallContext;
  tmr_task_continuation_locked : tmr_task_scan_world Application;
  tmr_task_continuation_lock_context : OsSchedCallContext
}.
Arguments tmr_task_continuation_before {Application} _.
Arguments tmr_task_continuation_context {Application} _.
Arguments tmr_task_continuation_completed {Application} _.
Arguments tmr_task_continuation_error {Application} _.
Arguments tmr_task_continuation_waited {Application} _.
Arguments tmr_task_continuation_wait_context {Application} _.
Arguments tmr_task_continuation_locked {Application} _.
Arguments tmr_task_continuation_lock_context {Application} _.

Definition tmr_task_continuation_start {Application}
  (history : TmrTaskContinuationHistory Application) :=
  tmr_task_set_timers
    (timer_service_advance (tmr_task_timers history.(tmr_task_continuation_locked)))
    history.(tmr_task_continuation_locked).
Definition tmr_task_continuation_spoke {Application} sg
  (history : TmrTaskContinuationHistory Application) :=
  tmr_task_spoke_index sg (tmr_task_timers (tmr_task_continuation_start history)).
Definition tmr_task_continuation_scan {Application} sg
  (history : TmrTaskContinuationHistory Application) :=
  timer_scan_begin sg (tmr_task_timers (tmr_task_continuation_start history)).

Section TaskContinuationAnnotations.
Context {Application : Type}.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (mask : Z) (effects : TmrTaskEffects Application).

(** This is the same arbitrary postcondition at every observed finite
    prefix of the source loop. count is not a bound added to the C loop. *)
Definition tmr_task_continuation_loop_safe context completed
  (world : tmr_task_scan_world Application)
  (X : (list TmrTaskIterationObservation * OsSchedCallContext) ->
    tmr_task_scan_world Application -> Prop) : Prop :=
  forall count, safeExec (eq world)
    (bind (tmr_task_continuation_prefix_program environment critical sg mask effects count context)
      (fun tail => ret (completed ++ fst tail, snd tail))) X.

Definition tmr_task_continuation_outer_facts original_context original context completed world X : Prop :=
  tmr_task_continuation_prefix environment critical sg mask effects original original_context
    completed world context /\
  tmr_task_continuation_loop_safe context completed world X.

Definition tmr_task_continuation_history original_context original
  (history : TmrTaskContinuationHistory Application) : Prop :=
  tmr_task_continuation_prefix environment critical sg mask effects original original_context
    history.(tmr_task_continuation_completed) history.(tmr_task_continuation_before)
    history.(tmr_task_continuation_context) /\
  tmr_task_continuation_pend_program environment critical sg effects
    history.(tmr_task_continuation_context)
    (tmr_task_timers history.(tmr_task_continuation_before)).(timerSignalSem)
    history.(tmr_task_continuation_before)
    (history.(tmr_task_continuation_error), history.(tmr_task_continuation_wait_context))
    history.(tmr_task_continuation_waited) /\
  tmr_task_continuation_lock_program environment critical sg mask effects
    history.(tmr_task_continuation_wait_context) history.(tmr_task_continuation_waited)
    history.(tmr_task_continuation_lock_context) history.(tmr_task_continuation_locked).

Definition tmr_task_continuation_scan_safe context completed error visited spoke scan
  (world : tmr_task_scan_world Application)
  (X : (list TmrTaskIterationObservation * OsSchedCallContext) ->
    tmr_task_scan_world Application -> Prop) : Prop :=
  forall count, safeExec (eq world)
    (bind (tmr_task_scan_program sg (tmr_task_callback_program effects) spoke context scan)
      (fun tail =>
    bind (tmr_task_continuation_unlock_program environment critical sg mask effects (snd tail))
      (fun returned =>
    bind (tmr_task_continuation_prefix_program environment critical sg mask effects count returned)
      (fun later => ret
        (completed ++ {| tmr_task_wait_error := error;
                         tmr_task_iteration_events := visited ++ fst tail;
                         tmr_task_iteration_context := returned |} :: fst later,
         snd later))))) X.

(** Geometry and source history of the real scan. Scheduler admission and
    call-source observations are carried separately by their actual callee
    interfaces; this predicate does not assume a future ready task. *)
Definition tmr_task_continuation_scan_facts original_context original history visited
  context world scan X : Prop :=
  tmr_task_continuation_history original_context original history /\
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
  tmr_task_continuation_scan_safe context history.(tmr_task_continuation_completed)
    history.(tmr_task_continuation_error) visited (tmr_task_continuation_spoke sg history)
    scan world X.

Lemma tmr_task_continuation_outer_initial : forall context world X,
  tmr_task_continuation_loop_safe context [] world X ->
  tmr_task_continuation_outer_facts context world context [] world X.
Proof. intros; split; [constructor|assumption]. Qed.

Lemma tmr_task_continuation_loop_safe_prefix : forall before context completed observations
  after returned X,
  tmr_task_continuation_prefix environment critical sg mask effects
    before context observations after returned ->
  tmr_task_continuation_loop_safe context completed before X ->
  tmr_task_continuation_loop_safe returned (completed ++ observations) after X.
Proof.
  intros before context completed observations after returned X Hprefix Hsafe count.
  specialize (Hsafe (List.length observations + count)%nat).
  unfold safeExec, safe, StateRelHoare.weakestpre in *.
  destruct Hsafe as [seen [Hseen Hsafe]]; subst seen.
  exists after; split; [reflexivity|].
  intros result final [tail [middle [Htail Hreturn]]].
  destruct (tmr_task_continuation_prefix_to_source environment critical sg mask effects
    count returned after tail middle Htail) as [Hsource Hlength].
  pose proof (tmr_task_continuation_prefix_app environment critical sg mask effects
    before context observations after returned (fst tail) middle (snd tail)
    Hprefix Hsource) as Hwhole.
  pose proof (tmr_task_continuation_prefix_from_source environment critical sg mask effects
    before context (observations ++ fst tail) middle (snd tail) Hwhole) as Hprogram.
  rewrite app_length, Hlength in Hprogram.
  apply (Hsafe result final).
  exists (observations ++ fst tail, snd tail), middle; split; [exact Hprogram|].
  cbn in *; rewrite app_assoc; exact Hreturn.
Qed.

Lemma tmr_task_continuation_outer_extend : forall original_context original context completed
  before observations returned after X,
  tmr_task_continuation_outer_facts original_context original context completed before X ->
  tmr_task_continuation_prefix environment critical sg mask effects
    before context observations after returned ->
  tmr_task_continuation_outer_facts original_context original returned
    (completed ++ observations) after X.
Proof.
  intros original_context original context completed before observations returned after X
    [Hprior Hsafe] Hprefix; split.
  - eapply tmr_task_continuation_prefix_app; eassumption.
  - eapply tmr_task_continuation_loop_safe_prefix; eassumption.
Qed.

Lemma tmr_task_continuation_history_from_calls : forall original_context original context
  completed before error wait_context waited lock_context locked,
  tmr_task_continuation_prefix environment critical sg mask effects
    original original_context completed before context ->
  tmr_task_continuation_pend_program environment critical sg effects context
    (tmr_task_timers before).(timerSignalSem) before (error, wait_context) waited ->
  tmr_task_continuation_lock_program environment critical sg mask effects
    wait_context waited lock_context locked ->
  tmr_task_continuation_history original_context original
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
  unfold tmr_task_continuation_history; cbn.
  split; [exact Hprefix|split; assumption].
Qed.

End TaskContinuationAnnotations.
