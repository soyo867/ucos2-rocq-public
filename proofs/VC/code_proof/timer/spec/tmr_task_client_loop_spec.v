Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_continuation_loop_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_lock_continuation_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_unlock_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_program_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Coq.Lists.List.
Import ListNotations Monad MonadNotation.
Local Open Scope Z_scope.

(** The full Timer loop with the current client-level Pend relation.
    Lock, scan, arbitrary callback and Unlock use their original programs.
    The observed finite prefixes do not bound the executable infinite loop.
    Old sources embed in the new Pend relation in one direction only. *)
Section TaskClientLoop.
Context {Application : Type}.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (mask : Z) (effects : TmrTaskEffects Application).

Definition tmr_task_client_pend_program (call : OsSchedCallContext) (signal : addr)
  : program (tmr_task_scan_world Application) (Z * OsSchedCallContext) :=
  fun before output after =>
    sem_pend_client_runtime_program environment critical sg
      call signal 0 (fst before) (fst output) (fst after) /\
    kernel_stack_call_same_call (snd output) call /\
    tmr_task_pend_application effects call before (fst output) (snd output) after.

Lemma tmr_task_client_pend_includes_previous : forall call signal before output after,
  tmr_task_continuation_pend_program environment critical sg effects call signal before output after ->
  tmr_task_client_pend_program call signal before output after.
Proof.
  intros call signal before output after [Hsource Hrest].
  split; [left; exact Hsource|exact Hrest].
Qed.

Lemma tmr_task_client_pend_source_continue : forall Result call signal before error returned after
  (next : (Z * OsSchedCallContext) -> program (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop),
  sem_pend_client_runtime_program environment critical sg call signal 0
    (fst before) error (fst after) ->
  kernel_stack_call_same_call returned call ->
  tmr_task_pend_application effects call before error returned after ->
  safeExec (eq before) (bind (tmr_task_client_pend_program call signal) next) X ->
  safeExec (eq after) (next (error, returned)) X.
Proof.
  intros Result call signal before error returned after next X Hsource Hsame Happ Hsafe.
  eapply tmr_task_stage_continue; [|exact Hsafe].
  split; [exact Hsource|split; assumption].
Qed.

Definition tmr_task_client_iteration_program (call : OsSchedCallContext)
  : program (tmr_task_scan_world Application) TmrTaskIterationObservation :=
  bind (get' (fun world => (tmr_task_timers world).(timerSignalSem))) (fun signal =>
  bind (tmr_task_client_pend_program call signal) (fun waited =>
  bind (tmr_task_continuation_lock_program environment critical sg mask effects (snd waited)) (fun locked =>
  bind (tmr_task_tick_program sg (tmr_task_callback_program effects) locked) (fun scanned =>
  bind (tmr_task_continuation_unlock_program environment critical sg mask effects (snd scanned)) (fun returned =>
    ret {| tmr_task_wait_error := fst waited;
           tmr_task_iteration_events := fst scanned;
           tmr_task_iteration_context := returned |}))))).

(** count measures observed completed iterations. It is not a new C loop
    bound; the actual infinite loop below uses repeat_break/continue. *)
Fixpoint tmr_task_client_prefix_program count (call : OsSchedCallContext)
  : program (tmr_task_scan_world Application)
      (list TmrTaskIterationObservation * OsSchedCallContext) :=
  match count with
  | O => ret ([], call)
  | S remaining => bind (tmr_task_client_iteration_program call) (fun observation =>
      bind (tmr_task_client_prefix_program remaining observation.(tmr_task_iteration_context))
        (fun tail => ret (observation :: fst tail, snd tail)))
  end.

Definition tmr_task_client_loop_program (call : OsSchedCallContext)
  : program (tmr_task_scan_world Application) unit :=
  @repeat_break (tmr_task_scan_world Application) OsSchedCallContext unit
    (fun current => bind (tmr_task_client_iteration_program current)
      (fun observation => ret (by_continue observation.(tmr_task_iteration_context)))) call.

Inductive tmr_task_client_prefix : tmr_task_scan_world Application ->
  OsSchedCallContext -> list TmrTaskIterationObservation ->
  tmr_task_scan_world Application -> OsSchedCallContext -> Prop :=
| TmrTaskClientPrefixEmpty : forall before call,
    tmr_task_client_prefix before call [] before call
| TmrTaskClientPrefixIteration : forall before call observation middle tail after returned,
    tmr_task_client_iteration_program call before observation middle ->
    tmr_task_client_prefix middle observation.(tmr_task_iteration_context) tail after returned ->
    tmr_task_client_prefix before call (observation :: tail) after returned.

Lemma tmr_task_client_iteration_source_steps : forall call before signal waited after_wait
  locked after_lock scanned after_scan returned after,
  signal = (tmr_task_timers before).(timerSignalSem) ->
  tmr_task_client_pend_program call signal before waited after_wait ->
  tmr_task_continuation_lock_program environment critical sg mask effects (snd waited) after_wait locked after_lock ->
  tmr_task_tick_program sg (tmr_task_callback_program effects) locked after_lock scanned after_scan ->
  tmr_task_continuation_unlock_program environment critical sg mask effects (snd scanned) after_scan returned after ->
  tmr_task_client_iteration_program call before
    {| tmr_task_wait_error := fst waited;
       tmr_task_iteration_events := fst scanned;
       tmr_task_iteration_context := returned |} after.
Proof.
  intros call before signal waited after_wait locked after_lock scanned after_scan returned after
    Hsignal Hpend Hlock Hscan Hunlock.
  unfold tmr_task_client_iteration_program.
  exists signal, before; split; [split; [exact Hsignal|reflexivity]|].
  exists waited, after_wait; split; [exact Hpend|].
  exists locked, after_lock; split; [exact Hlock|].
  exists scanned, after_scan; split; [exact Hscan|].
  exists returned, after; split; [exact Hunlock|split; reflexivity].
Qed.

Lemma tmr_task_client_prefix_from_source : forall before call observations after returned,
  tmr_task_client_prefix before call observations after returned ->
  tmr_task_client_prefix_program (List.length observations) call
    before (observations, returned) after.
Proof.
  intros before call observations after returned Hprefix; induction Hprefix.
  - split; reflexivity.
  - simpl; exists observation, middle; split; [exact H|].
    exists (tail, returned), after; split; [exact IHHprefix|split; reflexivity].
Qed.

Lemma tmr_task_client_prefix_to_source : forall count call before output after,
  tmr_task_client_prefix_program count call before output after ->
  tmr_task_client_prefix before call (fst output) after (snd output) /\
  List.length (fst output) = count.
Proof.
  induction count as [|count IH]; intros call before output after Hprogram.
  - destruct Hprogram as [Houtput Hstate]; subst output; subst after.
    split; [constructor|reflexivity].
  - destruct Hprogram as [observation [middle [Hiteration
      [tail [final [Htail [Houtput Hstate]]]]]]].
    subst output; subst final.
    destruct (IH _ _ _ _ Htail) as [Hprefix Hlength].
    simpl; split.
    + eapply TmrTaskClientPrefixIteration with (middle := middle);
        [exact Hiteration|exact Hprefix].
    + f_equal; exact Hlength.
Qed.

Lemma tmr_task_client_prefix_app : forall before call observations middle continued
  tail after returned,
  tmr_task_client_prefix before call observations middle continued ->
  tmr_task_client_prefix middle continued tail after returned ->
  tmr_task_client_prefix before call (observations ++ tail) after returned.
Proof.
  intros before call observations middle continued tail after returned Hprefix Htail.
  induction Hprefix; [exact Htail|simpl; econstructor; eauto].
Qed.

Lemma tmr_task_client_prefix_continue : forall Result before call observations
  after returned count
  (next : (list TmrTaskIterationObservation * OsSchedCallContext) ->
    program (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop),
  tmr_task_client_prefix before call observations after returned ->
  safeExec (eq before)
    (bind (tmr_task_client_prefix_program (List.length observations + count) call) next) X ->
  safeExec (eq after)
    (bind (tmr_task_client_prefix_program count returned)
      (fun output => next (observations ++ fst output, snd output))) X.
Proof.
  intros Result before call observations after returned count next X Hprefix Hsafe.
  unfold safeExec, safe, StateRelHoare.weakestpre in *.
  destruct Hsafe as [seen [Hseen Hsafe]]; subst seen.
  exists after; split; [reflexivity|].
  intros result final [output [middle [Hprogram Hnext]]].
  destruct (tmr_task_client_prefix_to_source _ _ _ _ _ Hprogram)
    as [Htail Hlength].
  pose proof (tmr_task_client_prefix_app _ _ _ _ _ _ _ _ Hprefix Htail) as Hwhole.
  pose proof (tmr_task_client_prefix_from_source _ _ _ _ _ Hwhole) as Hsource.
  rewrite app_length, Hlength in Hsource.
  apply (Hsafe result final).
  exists (observations ++ fst output, snd output), middle; split; assumption.
Qed.

Definition tmr_task_client_loop_safe context completed
  (world : tmr_task_scan_world Application)
  (X : (list TmrTaskIterationObservation * OsSchedCallContext) ->
    tmr_task_scan_world Application -> Prop) : Prop :=
  forall count, safeExec (eq world)
    (bind (tmr_task_client_prefix_program count context)
      (fun tail => ret (completed ++ fst tail, snd tail))) X.

Definition tmr_task_client_outer_facts original_context original context completed world X : Prop :=
  tmr_task_client_prefix original original_context completed world context /\
  tmr_task_client_loop_safe context completed world X.

Lemma tmr_task_client_outer_initial : forall context world X,
  tmr_task_client_loop_safe context [] world X ->
  tmr_task_client_outer_facts context world context [] world X.
Proof. intros; split; [constructor|assumption]. Qed.

Lemma tmr_task_client_loop_safe_prefix : forall before context completed observations after returned X,
  tmr_task_client_prefix before context observations after returned ->
  tmr_task_client_loop_safe context completed before X ->
  tmr_task_client_loop_safe returned (completed ++ observations) after X.
Proof.
  intros before context completed observations after returned X Hprefix Hsafe count.
  specialize (Hsafe (List.length observations + count)%nat).
  unfold safeExec, safe, StateRelHoare.weakestpre in *.
  destruct Hsafe as [seen [Hseen Hsafe]]; subst seen.
  exists after; split; [reflexivity|].
  intros result final [tail [middle [Htail Hreturn]]].
  destruct (tmr_task_client_prefix_to_source count returned after tail middle Htail)
    as [Hsource Hlength].
  pose proof (tmr_task_client_prefix_app before context observations after returned
    (fst tail) middle (snd tail) Hprefix Hsource) as Hwhole.
  pose proof (tmr_task_client_prefix_from_source before context (observations ++ fst tail)
    middle (snd tail) Hwhole) as Hprogram.
  rewrite app_length, Hlength in Hprogram.
  apply (Hsafe result final).
  exists (observations ++ fst tail, snd tail), middle; split; [exact Hprogram|].
  cbn in *; rewrite app_assoc; exact Hreturn.
Qed.

Lemma tmr_task_client_outer_extend : forall original_context original context completed
  before observations returned after X,
  tmr_task_client_outer_facts original_context original context completed before X ->
  tmr_task_client_prefix before context observations after returned ->
  tmr_task_client_outer_facts original_context original returned (completed ++ observations) after X.
Proof.
  intros original_context original context completed before observations returned after X
    [Hprior Hsafe] Hprefix; split.
  - eapply tmr_task_client_prefix_app; eassumption.
  - eapply tmr_task_client_loop_safe_prefix; eassumption.
Qed.

End TaskClientLoop.
