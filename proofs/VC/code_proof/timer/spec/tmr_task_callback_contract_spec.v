Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_loop_program_spec.
Require Export Ucos2Verify.VC.code.timer.spec.timer_callback_semantics.
Require Export Ucos2Verify.VC.code.timer.spec.timer_callee_lift_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
From MonadLib.MonadErr Require Import MonadErrBasic.

Import ListNotations.
Local Open Scope Z_scope.
Module TmrTaskCallback := TimerCallback_C_Rules.
Module TmrTaskRules := TimerCallback_C_Rules.Rules.

(** Concrete callback-call interface for the repaired Task scan.  The
    function capability quantifies every logical calling context and world;
    it is not just one invocation's specialized postcondition.  Real body
    source evidence and the source address lookup are its only producers.

    The one err byte is undef-owned because Task never reads it after
    OSSemPend.  SemPend's actual error is observed at its return cutpoint.
    AppRep and the outer frame must exclude that same byte; an argument
    equal to perr may refer to it without a second owned argument cell.
    The actual saved_local continuation capsules remain indexed by the
    CURRENT returned kernel state. *)
Section TaskCallbackContract.
Context {Application : Type} (AppRep : Application -> TmrTaskRules.expr).
Context (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
  (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (saved_local : Armv7aContinuation -> Assertion) (sg : StableGlobVars)
  (callback : (addr * addr * addr) -> OsSchedCallContext ->
    StateRelMonad.M (tmr_task_scan_world Application) OsSchedCallContext)
  (mask perr : Z).

Definition tmr_task_context_rep (context : OsSchedCallContext)
  (kernel : UCOS2_Verify_State) : TmrTaskRules.expr :=
  TmrTaskRules.sepcon
    (TimerCalleeLift.mutex_query_closed platform critical sg
      context.(os_sched_call_invocation) context.(os_sched_call_origin) mask kernel)
    (TmrTaskRules.sepcon (TimerCalleeLift.os_sched_context_resources external context)
      (TimerCalleeLift.unmap_table_rep sg)).

Definition tmr_task_owned (context : OsSchedCallContext)
  (world : tmr_task_scan_world Application) : TmrTaskRules.expr :=
  TmrTaskRules.sepcon (tmr_task_context_rep context (fst world))
    (TmrTaskRules.sepcon (TmrTaskRules.lift (sem_pend_error_cell perr))
      (TmrTaskRules.sepcon
        (TmrTaskRules.lift (sem_pend_optional_continuation_resources external platform
          (Some environment) saved_local context (fst world)))
        (AppRep (snd world)))).

Definition tmr_task_scan_call_ready (context : OsSchedCallContext)
  (world : tmr_task_scan_world Application) : Prop :=
  valid_timer_state sg (tmr_task_timers world) /\
  timer_api_initialized (tmr_task_timers world) /\
  os_sched_unlock_acquire_safety external critical sg context (fst world).

Definition tmr_task_callback_pre (self argument : Z) (context : OsSchedCallContext)
  (before : tmr_task_scan_world Application) (arguments : (Z * Z)%type)
  : TmrTaskRules.expr :=
  TmrTaskRules.andp
    (TmrTaskRules.coq_prop
      (arguments = (self, argument) /\ tmr_task_scan_call_ready context before))
    (tmr_task_owned context before).

Definition tmr_task_callback_post (fn self argument : Z) (context : OsSchedCallContext)
  (before : tmr_task_scan_world Application) (arguments : (Z * Z)%type) (_ : unit)
  : TmrTaskRules.expr :=
  fun heap => exists returned after,
    arguments = (self, argument) /\
    callback (fn, self, argument) context before returned after /\
    tmr_task_scan_call_ready returned after /\
    tmr_task_service_frame (tmr_task_timers before) (tmr_task_timers after) /\
    kernel_stack_call_same_call returned context /\
    tmr_task_owned returned after heap.

Definition tmr_task_callback_specification (fn self argument : Z)
  : TmrTaskCallback.Spec TmrTaskCallback.timer_callback_signature :=
  fun body => @TmrTaskRules.allp OsSchedCallContext (fun context =>
    @TmrTaskRules.allp (tmr_task_scan_world Application) (fun before =>
      TmrTaskCallback.HoareFun TmrTaskCallback.timer_callback_signature
        (tmr_task_callback_pre self argument context before)
        (tmr_task_callback_post fn self argument context before) body)).

Definition tmr_task_callback_capability (fn self argument : Z) : TmrTaskRules.expr :=
  @TmrTaskCallback.func_ptr_spec TmrTaskCallback.timer_callback_signature fn
    (tmr_task_callback_specification fn self argument).

Lemma tmr_task_callback_specification_environment_only : forall fn self argument,
  TmrTaskCallback.specification_environment_only
    (tmr_task_callback_specification fn self argument).
Proof.
  intros fn self argument; apply TmrTaskCallback.allp_specification_environment_only.
  intro context; apply TmrTaskCallback.allp_specification_environment_only.
  intro entry_state; apply TmrTaskCallback.HoareFun_specification_environment_only.
Qed.

Lemma tmr_task_callback_capability_from_source : forall fn self argument
  (functions : TmrTaskCallback.callback_environment)
  (body : TmrTaskCallback.FunSem TmrTaskCallback.timer_callback_signature),
  fn <> 0 ->
  TmrTaskCallback.source_functions functions TmrTaskCallback.timer_callback_signature fn = Some body ->
  (forall context before,
    TmrTaskCallback.callback_source_evidence functions
      TmrTaskCallback.timer_callback_signature body
      (tmr_task_callback_pre self argument context before)
      (tmr_task_callback_post fn self argument context before)) ->
  forall heap, tmr_task_callback_capability fn self argument (heap, functions).
Proof.
  intros fn self argument functions body Hfn Hlookup Hsource heap.
  split; [exact Hfn|]. exists body; split; [exact Hlookup|].
  intros context before; exact (Hsource context before).
Qed.

Definition tmr_task_callback_call_pre (fn self argument : Z)
  (context : OsSchedCallContext) (before : tmr_task_scan_world Application)
  (frame : TmrTaskRules.expr) : TmrTaskRules.expr :=
  @TmrTaskCallback.specified_call_pre TmrTaskCallback.timer_callback_signature
    fn (self, argument) (tmr_task_callback_specification fn self argument)
    (tmr_task_callback_pre self argument context before) frame.

Definition tmr_task_callback_call_post (fn self argument : Z)
  (context : OsSchedCallContext) (before : tmr_task_scan_world Application)
  (frame : TmrTaskRules.expr) : unit -> TmrTaskRules.expr :=
  @TmrTaskCallback.specified_call_post TmrTaskCallback.timer_callback_signature
    fn (self, argument) (tmr_task_callback_specification fn self argument)
    (tmr_task_callback_post fn self argument context before) frame.

Lemma tmr_task_callback_call_pre_open : forall fn self argument context before frame,
  tmr_task_scan_call_ready context before ->
  TmrTaskRules.derivable1
    (TmrTaskRules.andp
      (TmrTaskRules.sepcon (tmr_task_owned context before) frame)
      (tmr_task_callback_capability fn self argument))
    (tmr_task_callback_call_pre fn self argument context before frame).
Proof.
  intros fn self argument context before frame Hready heap
    [[owned [rest [Hjoin [Howned Hframe]]]] Hcap].
  split; [|exact Hcap]. exists owned, rest; split; [exact Hjoin|].
  split; [split; [split; [reflexivity|exact Hready]|exact Howned]|exact Hframe].
Qed.

Definition tmr_task_callback_resume {Result : Type} (fn self argument : Z)
  (context : OsSchedCallContext) (before : tmr_task_scan_world Application)
  (next : OsSchedCallContext -> StateRelMonad.M (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop) (frame : TmrTaskRules.expr)
  : TmrTaskRules.expr :=
  fun heap => exists returned after,
    callback (fn, self, argument) context before returned after /\
    tmr_task_scan_call_ready returned after /\
    tmr_task_service_frame (tmr_task_timers before) (tmr_task_timers after) /\
    kernel_stack_call_same_call returned context /\
    safeExec (eq after) (next returned) X /\
    TmrTaskRules.sepcon (tmr_task_owned returned after) frame heap /\
    tmr_task_callback_capability fn self argument heap.

Lemma tmr_task_callback_call_post_continue : forall Result fn self argument context
  before (next : OsSchedCallContext -> StateRelMonad.M (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop) frame,
  safeExec (eq before)
    (StateRelMonad.bind (callback (fn, self, argument) context) next) X ->
  TmrTaskRules.derivable1
    (tmr_task_callback_call_post fn self argument context before frame tt)
    (tmr_task_callback_resume fn self argument context before next X frame).
Proof.
  intros Result fn self argument context before next X frame Hsafe heap
    [[owned [rest [Hjoin [Hpost Hframe]]]] Hcap].
  destruct Hpost as [returned [after [Hargs [Hstep [Hready [Hservice [Hsame Howned]]]]]]].
  exists returned, after; split; [exact Hstep|]. split; [exact Hready|].
  split; [exact Hservice|]. split; [exact Hsame|]. split.
  - eapply tmr_task_stage_continue; eassumption.
  - split; [|exact Hcap]. exists owned, rest; split; [exact Hjoin|]. split; assumption.
Qed.

(** Every normally returning SOURCE callback outcome is covered, and an
    error execution is excluded by that same full capability.  Invariant,
    service frame, actual effects, same X, current capsules/AppRep, and
    the reusable full capability all occur in the consumed postcondition. *)
Theorem tmr_task_callback_call_rule : forall Result fn self argument context before
  (next : OsSchedCallContext -> StateRelMonad.M (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop) frame initial,
  safeExec (eq before)
    (StateRelMonad.bind (callback (fn, self, argument) context) next) X ->
  tmr_task_callback_call_pre fn self argument context before frame initial ->
  ~ @TmrTaskCallback.source_call_error TmrTaskCallback.timer_callback_signature
      (snd initial) fn (self, argument) (fst initial).(ConAssertion.s_mem) /\
  (forall final_memory,
    @TmrTaskCallback.source_call_normal TmrTaskCallback.timer_callback_signature
      (snd initial) fn (self, argument) (fst initial).(ConAssertion.s_mem) tt final_memory ->
    exists final,
      MonadErr.nrm (@TmrTaskCallback.indirect_call TmrTaskCallback.timer_callback_signature
        fn (self, argument)) initial tt final /\
      (fst final).(ConAssertion.s_mem) = final_memory /\
      tmr_task_callback_resume fn self argument context before next X frame final).
Proof.
  intros Result fn self argument context before next X frame initial Hsafe Hpre.
  assert (Hmatch : forall body, TmrTaskRules.derivable1
    (tmr_task_callback_specification fn self argument body)
    (TmrTaskCallback.HoareFun TmrTaskCallback.timer_callback_signature
      (tmr_task_callback_pre self argument context before)
      (tmr_task_callback_post fn self argument context before) body)).
  { intros body heap Hall; exact (Hall context before). }
  destruct (@TmrTaskCallback.indirect_call_specification_rule
    TmrTaskCallback.timer_callback_signature fn (self, argument)
    (tmr_task_callback_specification fn self argument)
    (tmr_task_callback_pre self argument context before)
    (tmr_task_callback_post fn self argument context before) frame
    (tmr_task_callback_specification_environment_only fn self argument) Hmatch)
    as [Hhoare Hcoverage].
  split.
  - intro Herror; exact (proj2 Hhoare initial Hpre Herror).
  - intros final_memory Hsource.
    destruct (Hcoverage initial tt final_memory Hpre Hsource)
      as [final [Hnormal [Hmemory Hpost]]].
    exists final; split; [exact Hnormal|]. split; [exact Hmemory|].
    exact (tmr_task_callback_call_post_continue Result fn self argument context
      before next X frame Hsafe final Hpost).
Qed.

Lemma tmr_task_callback_resume_reload : forall Result fn self argument context before
  (next : OsSchedCallContext -> StateRelMonad.M (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop) frame spoke,
  tmr_task_spoke_in_range sg spoke ->
  TmrTaskRules.derivable1
    (tmr_task_callback_resume fn self argument context before next X frame)
    (fun heap => exists returned after,
      callback (fn, self, argument) context before returned after /\
      timer_scan_continuation_valid sg (tmr_task_timers after)
        (tmr_task_scan_at_spoke spoke (tmr_task_timers after)) /\
      timer_scan_next_pointer sg (tmr_task_scan_at_spoke spoke (tmr_task_timers after)) =
        timer_id_pointer sg (nth spoke (tmr_task_timers after).(timerWheel) []) /\
      safeExec (eq after) (next returned) X /\
      TmrTaskRules.sepcon (tmr_task_owned returned after) frame heap /\
      tmr_task_callback_capability fn self argument heap).
Proof.
  intros Result fn self argument context before next X frame spoke Hspoke heap
    [returned [after [Hcall [Hready [Hservice [Hsame [Hsafe [Howned Hcap]]]]]]]].
  destruct (tmr_task_scan_at_spoke_valid sg spoke (tmr_task_timers after)
    Hspoke (proj1 Hready)) as [Hscan Hpointer].
  exists returned, after; split; [exact Hcall|]. split; [exact Hscan|].
  split; [exact Hpointer|]. split; [exact Hsafe|]. split; assumption.
Qed.
End TaskCallbackContract.
