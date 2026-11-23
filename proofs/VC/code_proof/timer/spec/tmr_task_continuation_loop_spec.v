Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_loop_program_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_lock_continuation_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_unlock_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_program_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Coq.Lists.List.
Import ListNotations Monad MonadNotation.
Local Open Scope Z_scope.

(** Source composition for the current continuation interfaces. The Lock
    result is its returned ghost call context, not a changed C signature.
    Every subsequent scan/callback consumes that actual context. The
    source-backed SemPend relation retains NULL, type, ISR, lock and blocking
    outcomes, including actual registered scheduler sources. The repaired
    scan retains arbitrary callback bodies. *)
Section TaskContinuationLoop.
Context {Application : Type}.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (mask : Z) (effects : TmrTaskEffects Application).

Definition tmr_task_continuation_pend_program (call : OsSchedCallContext) (signal : addr)
  : program (tmr_task_scan_world Application) (Z * OsSchedCallContext) :=
  fun before output after =>
    sem_pend_source_runtime_program environment.(task_stack_call_external)
      environment.(task_stack_call_platform) (Some environment) critical sg
      call signal 0 (fst before) (fst output) (fst after) /\
    kernel_stack_call_same_call (snd output) call /\
    tmr_task_pend_application effects call before (fst output) (snd output) after.

Definition tmr_task_continuation_lock_program (call : OsSchedCallContext)
  : program (tmr_task_scan_world Application) OsSchedCallContext :=
  fun before returned after =>
    os_sched_lock_continuation_program environment critical sg call mask
      (fst before) returned (fst after) /\
    tmr_task_lock_application effects call before after.

Definition tmr_task_continuation_unlock_program (call : OsSchedCallContext)
  : program (tmr_task_scan_world Application) OsSchedCallContext :=
  fun before returned after =>
    os_sched_unlock_continuation_program environment critical sg call mask
      (fst before) returned (fst after) /\
    tmr_task_unlock_application effects call before returned after.

Definition tmr_task_continuation_iteration_program (call : OsSchedCallContext)
  : program (tmr_task_scan_world Application) TmrTaskIterationObservation :=
  bind (get' (fun world => (tmr_task_timers world).(timerSignalSem))) (fun signal =>
  bind (tmr_task_continuation_pend_program call signal) (fun waited =>
  bind (tmr_task_continuation_lock_program (snd waited)) (fun locked =>
  bind (tmr_task_tick_program sg (tmr_task_callback_program effects) locked) (fun scanned =>
  bind (tmr_task_continuation_unlock_program (snd scanned)) (fun returned =>
    ret {| tmr_task_wait_error := fst waited;
           tmr_task_iteration_events := fst scanned;
           tmr_task_iteration_context := returned |}))))).

(** count measures observed completed iterations. It is not a new C loop
    bound; the actual infinite loop below uses repeat_break/continue. *)
Fixpoint tmr_task_continuation_prefix_program count (call : OsSchedCallContext)
  : program (tmr_task_scan_world Application)
      (list TmrTaskIterationObservation * OsSchedCallContext) :=
  match count with
  | O => ret ([], call)
  | S remaining => bind (tmr_task_continuation_iteration_program call) (fun observation =>
      bind (tmr_task_continuation_prefix_program remaining observation.(tmr_task_iteration_context))
        (fun tail => ret (observation :: fst tail, snd tail)))
  end.

Definition tmr_task_continuation_loop_program (call : OsSchedCallContext)
  : program (tmr_task_scan_world Application) unit :=
  @repeat_break (tmr_task_scan_world Application) OsSchedCallContext unit
    (fun current => bind (tmr_task_continuation_iteration_program current)
      (fun observation => ret (by_continue observation.(tmr_task_iteration_context)))) call.

Inductive tmr_task_continuation_prefix : tmr_task_scan_world Application ->
  OsSchedCallContext -> list TmrTaskIterationObservation ->
  tmr_task_scan_world Application -> OsSchedCallContext -> Prop :=
| TmrTaskContinuationPrefixEmpty : forall before call,
    tmr_task_continuation_prefix before call [] before call
| TmrTaskContinuationPrefixIteration : forall before call observation middle tail after returned,
    tmr_task_continuation_iteration_program call before observation middle ->
    tmr_task_continuation_prefix middle observation.(tmr_task_iteration_context) tail after returned ->
    tmr_task_continuation_prefix before call (observation :: tail) after returned.

Lemma tmr_task_continuation_iteration_source_steps : forall call before signal waited after_wait
  locked after_lock scanned after_scan returned after,
  signal = (tmr_task_timers before).(timerSignalSem) ->
  tmr_task_continuation_pend_program call signal before waited after_wait ->
  tmr_task_continuation_lock_program (snd waited) after_wait locked after_lock ->
  tmr_task_tick_program sg (tmr_task_callback_program effects) locked after_lock scanned after_scan ->
  tmr_task_continuation_unlock_program (snd scanned) after_scan returned after ->
  tmr_task_continuation_iteration_program call before
    {| tmr_task_wait_error := fst waited;
       tmr_task_iteration_events := fst scanned;
       tmr_task_iteration_context := returned |} after.
Proof.
  intros call before signal waited after_wait locked after_lock scanned after_scan returned after
    Hsignal Hpend Hlock Hscan Hunlock.
  unfold tmr_task_continuation_iteration_program.
  exists signal, before; split; [split; [exact Hsignal|reflexivity]|].
  exists waited, after_wait; split; [exact Hpend|].
  exists locked, after_lock; split; [exact Hlock|].
  exists scanned, after_scan; split; [exact Hscan|].
  exists returned, after; split; [exact Hunlock|split; reflexivity].
Qed.

Lemma tmr_task_continuation_prefix_from_source : forall before call observations after returned,
  tmr_task_continuation_prefix before call observations after returned ->
  tmr_task_continuation_prefix_program (List.length observations) call
    before (observations, returned) after.
Proof.
  intros before call observations after returned Hprefix; induction Hprefix.
  - split; reflexivity.
  - simpl; exists observation, middle; split; [exact H|].
    exists (tail, returned), after; split; [exact IHHprefix|split; reflexivity].
Qed.

Lemma tmr_task_continuation_prefix_to_source : forall count call before output after,
  tmr_task_continuation_prefix_program count call before output after ->
  tmr_task_continuation_prefix before call (fst output) after (snd output) /\
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
    + eapply TmrTaskContinuationPrefixIteration with (middle := middle);
        [exact Hiteration|exact Hprefix].
    + f_equal; exact Hlength.
Qed.

Lemma tmr_task_continuation_prefix_app : forall before call observations middle continued
  tail after returned,
  tmr_task_continuation_prefix before call observations middle continued ->
  tmr_task_continuation_prefix middle continued tail after returned ->
  tmr_task_continuation_prefix before call (observations ++ tail) after returned.
Proof.
  intros before call observations middle continued tail after returned Hprefix Htail.
  induction Hprefix; [exact Htail|simpl; econstructor; eauto].
Qed.

Lemma tmr_task_continuation_prefix_continue : forall Result before call observations
  after returned count
  (next : (list TmrTaskIterationObservation * OsSchedCallContext) ->
    program (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop),
  tmr_task_continuation_prefix before call observations after returned ->
  safeExec (eq before)
    (bind (tmr_task_continuation_prefix_program (List.length observations + count) call) next) X ->
  safeExec (eq after)
    (bind (tmr_task_continuation_prefix_program count returned)
      (fun output => next (observations ++ fst output, snd output))) X.
Proof.
  intros Result before call observations after returned count next X Hprefix Hsafe.
  unfold safeExec, safe, StateRelHoare.weakestpre in *.
  destruct Hsafe as [seen [Hseen Hsafe]]; subst seen.
  exists after; split; [reflexivity|].
  intros result final [output [middle [Hprogram Hnext]]].
  destruct (tmr_task_continuation_prefix_to_source _ _ _ _ _ Hprogram)
    as [Htail Hlength].
  pose proof (tmr_task_continuation_prefix_app _ _ _ _ _ _ _ _ Hprefix Htail) as Hwhole.
  pose proof (tmr_task_continuation_prefix_from_source _ _ _ _ _ Hwhole) as Hsource.
  rewrite app_length, Hlength in Hsource.
  apply (Hsafe result final).
  exists (observations ++ fst output, snd output), middle; split; assumption.
Qed.

Lemma tmr_task_continuation_lock_source_continue : forall Result call before returned after
  (next : OsSchedCallContext -> program (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop),
  os_sched_lock_continuation_history environment critical sg call mask
    (fst before) returned (fst after) ->
  tmr_task_lock_application effects call before after ->
  safeExec (eq before) (bind (tmr_task_continuation_lock_program call) next) X ->
  safeExec (eq after) (next returned) X.
Proof.
  intros Result call before returned after next X Hsource Happ Hsafe.
  eapply tmr_task_stage_continue; [|exact Hsafe].
  split; [apply os_sched_lock_continuation_program_iff; exact Hsource|exact Happ].
Qed.

Lemma tmr_task_continuation_unlock_source_continue : forall Result call before returned after
  (next : OsSchedCallContext -> program (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop),
  os_sched_unlock_continuation_history environment critical sg call mask
    (fst before) returned (fst after) ->
  tmr_task_unlock_application effects call before returned after ->
  safeExec (eq before) (bind (tmr_task_continuation_unlock_program call) next) X ->
  safeExec (eq after) (next returned) X.
Proof.
  intros Result call before returned after next X Hsource Happ Hsafe.
  eapply tmr_task_stage_continue; [|exact Hsafe].
  split; [apply os_sched_unlock_continuation_program_iff; exact Hsource|exact Happ].
Qed.

End TaskContinuationLoop.
