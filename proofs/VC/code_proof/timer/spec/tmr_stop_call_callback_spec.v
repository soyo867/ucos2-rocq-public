Require Export Ucos2Verify.VC.code.timer.spec.tmr_stop_call_frame_spec.
From MonadLib.MonadErr Require Import MonadErrBasic.
Require Import Coq.ZArith.ZArith.
Local Open Scope Z_scope.

(** A full callback specification, with the actual fn/self/argument fixed
    at the call site and all logical entry states/contexts quantified.
    The precondition has an explicit call domain, instantiated below with
    the actual source prefix.  A callback is not required to work on an
    unrelated owned kernel state where this Stop call cannot invoke it.
    No body address or C-compatible function type proves this assertion.
    The registered callback must prove the indicated resource contract.
    This is the ordinary modular callee dependency under QCP's source and
    linking boundary; this module adds no instruction-level C proof gate. *)
Section StopCallCallback.
Context {Application : Type} (AppRep : Application -> TmrStopRules.expr).
Context (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (effects : TmrStopEffects Application) (mask perr : Z).
Context (domain : Z -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> Prop).

Definition tmr_stop_call_callback_instance_pre (fn self argument : Z)
  (context : OsSchedCallContext) (before : TmrStopState Application)
  (arguments : (Z * Z)%type) : TmrStopRules.expr :=
  TmrStopRules.andp (TmrStopRules.coq_prop (domain fn self argument context before))
    (tmr_stop_callback_pre AppRep external platform critical sg mask perr
      self argument context before arguments).

Definition tmr_stop_call_callback_specification (fn self argument : Z)
  : TmrStopCallback.Spec TmrStopCallback.timer_callback_signature :=
  fun body => @TmrStopRules.allp OsSchedCallContext (fun context =>
    @TmrStopRules.allp (TmrStopState Application) (fun before =>
      TmrStopCallback.HoareFun TmrStopCallback.timer_callback_signature
        (tmr_stop_call_callback_instance_pre fn self argument context before)
        (tmr_stop_callback_post AppRep external platform critical sg effects mask perr
          fn self argument context before) body)).

Definition tmr_stop_call_callback_capability (fn self argument : Z) : TmrStopRules.expr :=
  TmrStopCallback.func_ptr_spec fn (tmr_stop_call_callback_specification fn self argument).

Lemma tmr_stop_call_callback_specification_environment_only : forall fn self argument,
  TmrStopCallback.specification_environment_only
    (tmr_stop_call_callback_specification fn self argument).
Proof.
  intros fn self argument.
  apply TmrStopCallback.allp_specification_environment_only. intro context.
  apply TmrStopCallback.allp_specification_environment_only. intro entry_state.
  apply TmrStopCallback.HoareFun_specification_environment_only.
Qed.

Lemma tmr_stop_call_callback_specialize : forall fn self argument context before,
  domain fn self argument context before ->
  TmrStopRules.derivable1 (tmr_stop_call_callback_capability fn self argument)
    (tmr_stop_callback_capability AppRep external platform critical sg effects mask perr
      fn self argument context before).
Proof.
  intros fn self argument context before Hdomain. apply TmrStopCallback.func_ptr_spec_mono.
  intros body heap Hall.
  eapply TmrStopCallback.HoareFun_conseq; [| |exact (Hall context before)].
  - intros arguments current Hpre. split; [exact Hdomain|exact Hpre].
  - intros arguments result current Hpost. exact Hpost.
Qed.

Definition tmr_stop_call_callback_pre (fn self argument : Z)
  (context : OsSchedCallContext) (before : TmrStopState Application)
  (frame : TmrStopRules.expr) : TmrStopRules.expr :=
  @TmrStopCallback.specified_call_pre TmrStopCallback.timer_callback_signature
    fn (self, argument) (tmr_stop_call_callback_specification fn self argument)
    (tmr_stop_call_callback_instance_pre fn self argument context before) frame.

Definition tmr_stop_call_callback_post (fn self argument : Z)
  (context : OsSchedCallContext) (before : TmrStopState Application)
  (frame : TmrStopRules.expr) : unit -> TmrStopRules.expr :=
  @TmrStopCallback.specified_call_post TmrStopCallback.timer_callback_signature
    fn (self, argument) (tmr_stop_call_callback_specification fn self argument)
    (tmr_stop_callback_post AppRep external platform critical sg effects mask perr
      fn self argument context before) frame.

Lemma tmr_stop_call_callback_pre_open : forall fn self argument context before frame,
  domain fn self argument context before ->
  TmrStopRules.derivable1
    (TmrStopRules.andp
      (TmrStopRules.sepcon
        (tmr_stop_owned AppRep external platform critical sg mask perr context before) frame)
      (tmr_stop_call_callback_capability fn self argument))
    (tmr_stop_call_callback_pre fn self argument context before frame).
Proof.
  intros fn self argument context before frame Hdomain heap
    [[owned [rest [Hjoin [Howned Hframe]]]] Hcap].
  split; [|exact Hcap]. exists owned, rest. split; [exact Hjoin|].
  split; [|exact Hframe]. split; [exact Hdomain|].
  split; [reflexivity|exact Howned].
Qed.

Definition tmr_stop_call_callback_resume {Result : Type} (fn self argument : Z)
  (context : OsSchedCallContext) (before : TmrStopState Application)
  (next : OsSchedCallContext -> StateRelMonad.M (TmrStopState Application) Result)
  (X : Result -> TmrStopState Application -> Prop) (frame : TmrStopRules.expr)
  : TmrStopRules.expr :=
  fun heap => exists returned after,
    tmr_stop_callback effects fn self argument context before returned after /\
    tmr_stop_unlock_ready external critical sg returned after /\
    safeExec (eq after) (next returned) X /\
    TmrStopRules.sepcon
      (tmr_stop_owned AppRep external platform critical sg mask perr returned after) frame heap /\
    tmr_stop_call_callback_capability fn self argument heap.

Lemma tmr_stop_call_callback_post_continue : forall (Result : Type)
  fn self argument context (before : TmrStopState Application)
  (next : OsSchedCallContext -> StateRelMonad.M (TmrStopState Application) Result)
  (X : Result -> TmrStopState Application -> Prop) frame,
  safeExec (eq before)
    (StateRelMonad.bind (tmr_stop_callback effects fn self argument context) next) X ->
  TmrStopRules.derivable1 (tmr_stop_call_callback_post fn self argument context before frame tt)
    (tmr_stop_call_callback_resume fn self argument context before next X frame).
Proof.
  intros Result fn self argument context before next X frame Hsafe heap
    [[owned [rest [Hjoin [Hpost Hframe]]]] Hcap].
  destruct Hpost as [returned [after [Hargs [Hstep [Hready Howned]]]]].
  exists returned, after. split; [exact Hstep|]. split; [exact Hready|]. split.
  - eapply tmr_stop_stage_continue; eassumption.
  - split; [|exact Hcap]. exists owned, rest. split; [exact Hjoin|]. split; assumption.
Qed.

(** Both source-normal coverage and error exclusion of the SAME full
    capability are consumed.  The full capability is returned, not merely
    the one context/state specialization used for this invocation. *)
Theorem tmr_stop_call_callback_rule : forall (Result : Type)
  fn self argument context (before : TmrStopState Application)
  (next : OsSchedCallContext -> StateRelMonad.M (TmrStopState Application) Result)
  (X : Result -> TmrStopState Application -> Prop) frame initial,
  safeExec (eq before)
    (StateRelMonad.bind (tmr_stop_callback effects fn self argument context) next) X ->
  tmr_stop_call_callback_pre fn self argument context before frame initial ->
  ~ @TmrStopCallback.source_call_error TmrStopCallback.timer_callback_signature
      (snd initial) fn (self, argument) (fst initial).(ConAssertion.s_mem) /\
  (forall final_memory,
    @TmrStopCallback.source_call_normal TmrStopCallback.timer_callback_signature
      (snd initial) fn (self, argument) (fst initial).(ConAssertion.s_mem) tt final_memory ->
    exists final,
      MonadErr.nrm (@TmrStopCallback.indirect_call TmrStopCallback.timer_callback_signature
        fn (self, argument)) initial tt final /\
      (fst final).(ConAssertion.s_mem) = final_memory /\
      tmr_stop_call_callback_resume fn self argument context before next X frame final).
Proof.
  intros Result fn self argument context before next X frame initial Hsafe Hpre.
  assert (Hmatch : forall body, TmrStopRules.derivable1
    (tmr_stop_call_callback_specification fn self argument body)
    (TmrStopCallback.HoareFun TmrStopCallback.timer_callback_signature
      (tmr_stop_call_callback_instance_pre fn self argument context before)
      (tmr_stop_callback_post AppRep external platform critical sg effects mask perr
        fn self argument context before) body)).
  { intros body heap Hall. exact (Hall context before). }
  destruct (@TmrStopCallback.indirect_call_specification_rule
    TmrStopCallback.timer_callback_signature fn (self, argument)
    (tmr_stop_call_callback_specification fn self argument)
    (tmr_stop_call_callback_instance_pre fn self argument context before)
    (tmr_stop_callback_post AppRep external platform critical sg effects mask perr
      fn self argument context before) frame
    (tmr_stop_call_callback_specification_environment_only fn self argument) Hmatch)
    as [Hhoare Hcoverage].
  split.
  - intro Herror. exact (proj2 Hhoare initial Hpre Herror).
  - intros final_memory Hsource.
    destruct (Hcoverage initial tt final_memory Hpre Hsource)
      as [final [Hnormal [Hmemory Hpost]]].
    exists final. split; [exact Hnormal|]. split; [exact Hmemory|].
    exact (tmr_stop_call_callback_post_continue Result fn self argument context before
      next X frame Hsafe final Hpost).
Qed.

Section SourcePrefixes.
Context (pooled : bool) (pointer index opt argument : Z)
  (raw_type raw_state : TmrStopState Application -> Z).

(** Actual source prefix.  In particular an earlier timer image is not
    reused after Lock, callback selection is after Unlink and *perr=0,
    and opt=NONE/default/NULL cannot select a fictitious callback. *)
Definition tmr_stop_call_callback_prefix (context : OsSchedCallContext)
  (before : TmrStopState Application) (fn self arg : Z)
  (selected : TmrStopState Application) : Prop :=
  exists observed locked state_read stopped,
    pointer <> 0 /\
    tmr_stop_type_program pooled index raw_type before 100 observed /\
    os_sched_lock_ints observed.(tmr_stop_kernel) <= 0 /\
    tmr_stop_lock_program critical sg effects context observed tt locked /\
    tmr_stop_state_program pooled index raw_state locked 3 state_read /\
    tmr_stop_unlink_program sg index state_read tt stopped /\
    tmr_stop_select_callback_program pointer index opt argument
      (tmr_stop_set_error (encode_os_err_code OS_ERR_NONE) stopped)
      (Some (fn, self, arg)) selected.

Definition tmr_stop_call_callback_domain (context : OsSchedCallContext)
  (before : TmrStopState Application) (fn self arg : Z)
  (calling_context : OsSchedCallContext) (selected : TmrStopState Application) : Prop :=
  calling_context = context /\
  tmr_stop_call_callback_prefix context before fn self arg selected.

Lemma tmr_stop_call_callback_prefix_domain : forall context before fn self arg selected,
  tmr_stop_call_callback_prefix context before fn self arg selected ->
  tmr_stop_call_callback_domain context before fn self arg context selected.
Proof. intros; split; [reflexivity|assumption]. Qed.

Lemma tmr_stop_call_callback_prefix_continue : forall context before fn self arg selected X,
  tmr_stop_call_callback_prefix context before fn self arg selected ->
  tmr_stop_api_pre external critical sg effects pooled pointer index opt argument
    raw_type raw_state context before X ->
  safeExec (eq selected)
    (StateRelMonad.bind (tmr_stop_callback effects fn self arg context)
      (tmr_stop_unlock_tail external critical sg effects)) X.
Proof.
  intros context before fn self arg selected X
    [observed [locked [state_read [stopped
      [Hpointer [Htype [Hints [Hlock [Hstate [Hunlink Hselect]]]]]]]]]] Hsafe.
  exact (@tmr_stop_running_callback_continue Application external critical sg effects
    pooled pointer index opt argument raw_type raw_state context
    before observed locked state_read stopped selected (Some (fn, self, arg)) X
    Hpointer Htype Hints Hlock Hstate Hunlink Hselect Hsafe).
Qed.

Definition tmr_stop_call_callback_capabilities (context : OsSchedCallContext)
  (before : TmrStopState Application) : TmrStopRules.expr :=
  fun heap => forall fn self arg selected,
    tmr_stop_call_callback_prefix context before fn self arg selected ->
    tmr_stop_call_callback_capability fn self arg heap.

Lemma tmr_stop_call_callback_capabilities_selected : forall context before fn self arg selected,
  tmr_stop_call_callback_prefix context before fn self arg selected ->
  TmrStopRules.derivable1 (tmr_stop_call_callback_capabilities context before)
    (tmr_stop_call_callback_capability fn self arg).
Proof.
  intros context before fn self arg selected Hprefix heap Hcaps.
  exact (Hcaps fn self arg selected Hprefix).
Qed.

Lemma tmr_stop_call_callback_capabilities_environment_only : forall context before,
  TmrStopCallback.assertion_environment_only
    (tmr_stop_call_callback_capabilities context before).
Proof.
  intros context before first second Henv Hcaps fn self arg selected Hprefix.
  apply (TmrStopCallback.func_ptr_spec_environment_eq fn
    (tmr_stop_call_callback_specification fn self arg)
    (tmr_stop_call_callback_specification_environment_only fn self arg)
    first second Henv).
  exact (Hcaps fn self arg selected Hprefix).
Qed.
End SourcePrefixes.
End StopCallCallback.
