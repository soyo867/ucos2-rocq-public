Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_repaired_scan_spec.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_lock_call_api_program_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_unlock_call_api_program_spec.
Require Import Coq.Lists.List.

Import ListNotations Monad MonadNotation.
Local Open Scope Z_scope.

(** Kernel calls keep their existing source relations.  Application effects
    are supplied separately by the actual resource contract: a private
    framed application has the concrete identity instance below; shared
    application storage must use its actual call effects.  Callback effects
    remain arbitrary programs and are never filtered by a scan invariant. *)
Record TmrTaskEffects (Application : Type) : Type := {
  tmr_task_pend_application : OsSchedCallContext ->
    tmr_task_scan_world Application -> Z -> OsSchedCallContext ->
    tmr_task_scan_world Application -> Prop;
  tmr_task_lock_application : OsSchedCallContext ->
    tmr_task_scan_world Application -> tmr_task_scan_world Application -> Prop;
  tmr_task_unlock_application : OsSchedCallContext ->
    tmr_task_scan_world Application -> OsSchedCallContext ->
    tmr_task_scan_world Application -> Prop;
  tmr_task_callback_program : (addr * addr * addr) -> OsSchedCallContext ->
    program (tmr_task_scan_world Application) OsSchedCallContext
}.

Arguments tmr_task_pend_application {Application} _ _ _ _ _ _.
Arguments tmr_task_lock_application {Application} _ _ _ _.
Arguments tmr_task_unlock_application {Application} _ _ _ _ _.
Arguments tmr_task_callback_program {Application} _ _ _.

Definition tmr_task_framed_effects {Application}
  (callback : (addr * addr * addr) -> OsSchedCallContext ->
    program (tmr_task_scan_world Application) OsSchedCallContext)
  : TmrTaskEffects Application :=
  {| tmr_task_pend_application := fun _ before _ _ after => snd after = snd before;
     tmr_task_lock_application := fun _ before after => snd after = snd before;
     tmr_task_unlock_application := fun _ before _ after => snd after = snd before;
     tmr_task_callback_program := callback |}.

Record TmrTaskIterationObservation : Type := {
  tmr_task_wait_error : Z;
  tmr_task_iteration_events : list tmr_task_scan_event;
  tmr_task_iteration_context : OsSchedCallContext
}.

(** Generic StateRelMonad cutpoint rule on the actual kernel/application
    product.  It requires a real step; safeExec does not manufacture one. *)
Lemma tmr_task_stage_continue : forall Application Value Result
  (command : program (tmr_task_scan_world Application) Value)
  (next : Value -> program (tmr_task_scan_world Application) Result)
  before value after (X : Result -> tmr_task_scan_world Application -> Prop),
  command before value after ->
  safeExec (eq before) (bind command next) X ->
  safeExec (eq after) (next value) X.
Proof.
  intros Application Value Result command next before value after X Hstep Hsafe.
  unfold safeExec, safe, StateRelHoare.weakestpre in *.
  destruct Hsafe as [seen [Hseen Hsafe]]; subst seen.
  exists after; split; [reflexivity|].
  intros result final Hnext; apply (Hsafe result final).
  exists value, after; split; assumption.
Qed.

Section TaskLoopProgram.
Context {Application : Type}.
Context (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
  (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (effects : TmrTaskEffects Application).

Definition tmr_task_pend_program (context : OsSchedCallContext) (signal : addr)
  : program (tmr_task_scan_world Application) (Z * OsSchedCallContext) :=
  fun before output after =>
    sem_pend_runtime_program external platform (Some environment) critical sg
      context signal 0 (fst before) (fst output) (fst after) /\
    kernel_stack_call_same_call (snd output) context /\
    tmr_task_pend_application effects context before (fst output) (snd output) after.

Definition tmr_task_lock_program (context : OsSchedCallContext)
  : program (tmr_task_scan_world Application) unit :=
  fun before result after =>
    os_sched_lock_program critical sg context.(os_sched_call_invocation)
      (fst before) result (fst after) /\
    tmr_task_lock_application effects context before after.

Definition tmr_task_unlock_program (context : OsSchedCallContext)
  : program (tmr_task_scan_world Application) OsSchedCallContext :=
  fun before returned after =>
    os_sched_unlock_call_relation external critical sg context
      (fst before) returned (fst after) /\
    tmr_task_unlock_application effects context before returned after.

Definition tmr_task_iteration_program (context : OsSchedCallContext)
  : program (tmr_task_scan_world Application) TmrTaskIterationObservation :=
  bind (get' (fun world => (tmr_task_timers world).(timerSignalSem))) (fun signal =>
  bind (tmr_task_pend_program context signal) (fun waited =>
  bind (tmr_task_lock_program (snd waited)) (fun _ =>
  bind (tmr_task_tick_program sg (tmr_task_callback_program effects) (snd waited))
    (fun scanned =>
  bind (tmr_task_unlock_program (snd scanned)) (fun returned =>
    ret {| tmr_task_wait_error := fst waited;
           tmr_task_iteration_events := fst scanned;
           tmr_task_iteration_context := returned |}))))).

(** n is a proof-observation bound, not a C counter or a replacement for
    for (;;).  Each unit counted here is one ACTUALLY completed iteration,
    including the actual SemPend error, all visits, and Unlock return. *)
Fixpoint tmr_task_loop_prefix_program (n : nat) (context : OsSchedCallContext)
  : program (tmr_task_scan_world Application)
      (list TmrTaskIterationObservation * OsSchedCallContext) :=
  match n with
  | O => ret ([], context)
  | S count => bind (tmr_task_iteration_program context) (fun observation =>
      bind (tmr_task_loop_prefix_program count observation.(tmr_task_iteration_context))
        (fun tail => ret (observation :: fst tail, snd tail)))
  end.

Definition tmr_task_loop_program (context : OsSchedCallContext)
  : program (tmr_task_scan_world Application) unit :=
  @repeat_break (tmr_task_scan_world Application) OsSchedCallContext unit
    (fun current => bind (tmr_task_iteration_program current)
      (fun observation => ret (by_continue observation.(tmr_task_iteration_context))))
    context.

Inductive tmr_task_loop_prefix : tmr_task_scan_world Application ->
  OsSchedCallContext -> list TmrTaskIterationObservation ->
  tmr_task_scan_world Application -> OsSchedCallContext -> Prop :=
| TmrTaskLoopPrefixEmpty : forall before context,
    tmr_task_loop_prefix before context [] before context
| TmrTaskLoopPrefixIteration : forall before context observation middle tail after returned,
    tmr_task_iteration_program context before observation middle ->
    tmr_task_loop_prefix middle observation.(tmr_task_iteration_context) tail after returned ->
    tmr_task_loop_prefix before context (observation :: tail) after returned.

Lemma tmr_task_iteration_source_steps : forall context before signal waited
  after_wait locked events after_scan after_callback_context returned after,
  signal = (tmr_task_timers before).(timerSignalSem) ->
  tmr_task_pend_program context signal before waited after_wait ->
  tmr_task_lock_program (snd waited) after_wait tt locked ->
  tmr_task_tick_program sg (tmr_task_callback_program effects) (snd waited)
    locked (events, after_callback_context) after_scan ->
  tmr_task_unlock_program after_callback_context after_scan returned after ->
  tmr_task_iteration_program context before
    {| tmr_task_wait_error := fst waited;
       tmr_task_iteration_events := events;
       tmr_task_iteration_context := returned |} after.
Proof.
  intros context before signal waited after_wait locked events after_scan
    after_callback_context returned after Hsignal Hwait Hlock Htick Hunlock.
  unfold tmr_task_iteration_program.
  exists signal, before; split; [split; [exact Hsignal|reflexivity]|].
  exists waited, after_wait; split; [exact Hwait|].
  exists tt, locked; split; [exact Hlock|].
  exists (events, after_callback_context), after_scan; split; [exact Htick|].
  exists returned, after; split; [exact Hunlock|split; reflexivity].
Qed.

Lemma tmr_task_loop_prefix_program_from_source : forall before context observations
  after returned,
  tmr_task_loop_prefix before context observations after returned ->
  tmr_task_loop_prefix_program (List.length observations) context
    before (observations, returned) after.
Proof.
  intros before context observations after returned Hprefix; induction Hprefix.
  - split; reflexivity.
  - simpl; exists observation, middle; split; [exact H|].
    exists (tail, returned), after; split; [exact IHHprefix|split; reflexivity].
Qed.

Lemma tmr_task_loop_prefix_program_to_source : forall count context before output after,
  tmr_task_loop_prefix_program count context before output after ->
  tmr_task_loop_prefix before context (fst output) after (snd output) /\
  List.length (fst output) = count.
Proof.
  induction count as [|count IH]; intros context before output after Hprogram.
  - destruct Hprogram as [Houtput Hstate]; subst output; subst after.
    split; [constructor|reflexivity].
  - destruct Hprogram as [observation [middle [Hiteration
      [tail [final [Htail [Houtput Hstate]]]]]]].
    subst output; subst final.
    destruct (IH _ _ _ _ Htail) as [Hprefix Hlength].
    simpl; split.
    + eapply TmrTaskLoopPrefixIteration with (middle := middle).
      * exact Hiteration.
      * exact Hprefix.
    + f_equal; exact Hlength.
Qed.

Lemma tmr_task_loop_prefix_app : forall before context observations middle continued
  tail after returned,
  tmr_task_loop_prefix before context observations middle continued ->
  tmr_task_loop_prefix middle continued tail after returned ->
  tmr_task_loop_prefix before context (observations ++ tail) after returned.
Proof.
  intros before context observations middle continued tail after returned Hprefix Htail.
  induction Hprefix; [exact Htail|simpl; econstructor; eauto].
Qed.

Lemma tmr_task_loop_prefix_continue : forall Result before context observations
  after returned count
  (next : (list TmrTaskIterationObservation * OsSchedCallContext) ->
    program (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop),
  tmr_task_loop_prefix before context observations after returned ->
  safeExec (eq before)
    (bind (tmr_task_loop_prefix_program (List.length observations + count) context) next) X ->
  safeExec (eq after)
    (bind (tmr_task_loop_prefix_program count returned)
      (fun output => next (observations ++ fst output, snd output))) X.
Proof.
  intros Result before context observations after returned count next X Hprefix Hsafe.
  unfold safeExec, safe, StateRelHoare.weakestpre in *.
  destruct Hsafe as [seen [Hseen Hsafe]]; subst seen.
  exists after; split; [reflexivity|].
  intros result final [output [middle [Hprogram Hnext]]].
  destruct (tmr_task_loop_prefix_program_to_source _ _ _ _ _ Hprogram)
    as [Htail Hlength].
  pose proof (tmr_task_loop_prefix_app _ _ _ _ _ _ _ _ Hprefix Htail) as Hwhole.
  pose proof (tmr_task_loop_prefix_program_from_source _ _ _ _ _ Hwhole) as Hsource.
  rewrite app_length, Hlength in Hsource.
  apply (Hsafe result final).
  exists (observations ++ fst output, snd output), middle; split; assumption.
Qed.

(** No equality between LastSeen and eq is used.  The legacy SemPend
    continuation is instantiated only to obtain the original source
    result/resources; the arbitrary product-state X survives separately. *)
Lemma tmr_task_pend_legacy_continuation : forall context signal before,
  safeExec (LastSeen before)
    (bind (atomic_cmd (sem_pend_runtime_program external platform
      (Some environment) critical sg context signal 0)) sem_query_observe_error)
    (fun _ _ => True).
Proof.
  intros context signal before; exists (RTrans_Abs before); split.
  - unfold LastSeen; intro state; split; trivial.
  - unfold safe, StateRelHoare.weakestpre. hnf; intros; exact I.
Qed.

Lemma tmr_task_pend_source_continue : forall Result context signal before error
  returned after
  (next : (Z * OsSchedCallContext) -> program (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop),
  sem_pend_runtime_program external platform (Some environment) critical sg context
    signal 0 (fst before) error (fst after) ->
  kernel_stack_call_same_call returned context ->
  tmr_task_pend_application effects context before error returned after ->
  safeExec (eq before) (bind (tmr_task_pend_program context signal) next) X ->
  safeExec (eq after) (next (error, returned)) X.
Proof.
  intros Result context signal before error returned after next X Hsource Hsame Happ Hsafe.
  eapply tmr_task_stage_continue; [|exact Hsafe].
  split; [exact Hsource|]. split; assumption.
Qed.

Lemma tmr_task_lock_source_continue : forall Result context before entry after
  (next : unit -> program (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop),
  os_sched_lock_call_relation critical sg context.(os_sched_call_invocation)
    (fst before) entry (fst after) ->
  tmr_task_lock_application effects context before after ->
  safeExec (eq before) (bind (tmr_task_lock_program context) next) X ->
  safeExec (eq after) (next tt) X.
Proof.
  intros Result context before entry after next X Hsource Happ Hsafe.
  eapply tmr_task_stage_continue; [|exact Hsafe].
  split; [split; [reflexivity|exists entry; exact Hsource]|exact Happ].
Qed.

Lemma tmr_task_unlock_source_continue : forall Result context before returned after
  (next : OsSchedCallContext -> program (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop),
  os_sched_unlock_call_relation external critical sg context (fst before) returned (fst after) ->
  tmr_task_unlock_application effects context before returned after ->
  safeExec (eq before) (bind (tmr_task_unlock_program context) next) X ->
  safeExec (eq after) (next returned) X.
Proof.
  intros Result context before returned after next X Hsource Happ Hsafe.
  eapply tmr_task_stage_continue; [|exact Hsafe].
  split; assumption.
Qed.

End TaskLoopProgram.

(** Callback-call cutpoint for the repaired scan.  This supplies the
    callback program's same-X precondition before invoking the real fn;
    the existing scan callback-return theorem supplies its continuation. *)
Lemma tmr_task_scan_callback_pre_continue : forall Application sg callback spoke
  Result (before : tmr_task_scan_world Application) context scan index rest future
  cached call dispatched
  (next : (list tmr_task_scan_event * OsSchedCallContext) ->
    program (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop),
  scan.(timerScanRemaining) = index :: rest ->
  timer_scan_advance (tmr_task_timers before) scan = Some future ->
  timer_expire_dispatch sg (tmr_task_timers before) index = Some (cached, Some call, dispatched) ->
  safeExec (eq before)
    (bind (tmr_task_scan_program sg callback spoke context scan) next) X ->
  safeExec (eq (tmr_task_set_timers dispatched before))
    (bind (callback call context) (fun returned after result final =>
      bind (tmr_task_scan_program sg callback spoke returned
        (tmr_task_scan_at_spoke spoke (tmr_task_timers after)))
        (fun output => next ((index, Some call) :: fst output, snd output))
        after result final)) X.
Proof.
  intros Application sg callback spoke Result before context scan index rest future
    cached call dispatched next X Hremaining Hadvance Hdispatch Hsafe.
  unfold safeExec, safe, StateRelHoare.weakestpre in *.
  destruct Hsafe as [seen [Hseen Hsafe]]; subst seen.
  exists (tmr_task_set_timers dispatched before); split; [reflexivity|].
  intros result final [returned [after [Hcall
    [output [scan_after [[finish Hscan] Hnext]]]]]].
  apply (Hsafe result final).
  exists ((index, Some call) :: fst output, snd output), scan_after; split; [|exact Hnext].
  exists finish; simpl.
  eapply TmrTaskScanVisit with (middle := after) (continued := returned)
    (future := tmr_task_scan_at_spoke spoke (tmr_task_timers after)).
  - eapply TmrTaskScanReloadHead with (rest := rest) (future := future)
      (next := cached) (dispatched := dispatched).
    + exact Hremaining.
    + exact Hadvance.
    + exact Hdispatch.
    + exact Hcall.
  - exact Hscan.
Qed.
