Require Export Ucos2Verify.VC.code.timer.spec.tmr_stop_call_callback_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_unlink_spec.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Local Open Scope Z_scope.

(** Callee readiness is required at real source prefixes, rather than for
    all integers/states or only an arbitrarily selected successful trace.
    All prefix relations below are built from the existing source program.
    They contain no abstract closure or readiness guard. *)
Section StopCallRequirements.
Context {Application : Type}.
Context (external : OsSchedExternalResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (effects : TmrStopEffects Application).
Context (pooled : bool) (pointer index opt argument : Z)
  (raw_type raw_state : TmrStopState Application -> Z).

Definition tmr_stop_call_state_prefix (context : OsSchedCallContext)
  (before : TmrStopState Application) (status : Z)
  (state_read : TmrStopState Application) : Prop :=
  exists observed locked,
    pointer <> 0 /\
    tmr_stop_type_program pooled index raw_type before 100 observed /\
    os_sched_lock_ints observed.(tmr_stop_kernel) <= 0 /\
    tmr_stop_lock_program critical sg effects context observed tt locked /\
    tmr_stop_state_program pooled index raw_state locked status state_read.

Definition tmr_stop_call_unlink_ready (context : OsSchedCallContext)
  (before : TmrStopState Application) : Prop :=
  forall state_read,
    tmr_stop_call_state_prefix context before 3 state_read ->
    pointer = timer_pool_addr sg index /\
    timer_api_initialized state_read.(tmr_stop_kernel).(TimerState) /\
    tmr_unlink_running state_read.(tmr_stop_kernel).(TimerState) index.

Definition tmr_stop_call_nonrunning_unlock_ready (context : OsSchedCallContext)
  (before : TmrStopState Application) : Prop :=
  forall status state_read,
    tmr_stop_call_state_prefix context before status state_read -> status <> 3 ->
    tmr_stop_unlock_ready external critical sg context state_read.

Definition tmr_stop_call_no_callback_unlock_ready (context : OsSchedCallContext)
  (before : TmrStopState Application) : Prop :=
  forall state_read stopped selected,
    tmr_stop_call_state_prefix context before 3 state_read ->
    tmr_stop_unlink_program sg index state_read tt stopped ->
    tmr_stop_select_callback_program pointer index opt argument
      (tmr_stop_set_error (encode_os_err_code OS_ERR_NONE) stopped) None selected ->
    tmr_stop_unlock_ready external critical sg context selected.

Definition tmr_stop_call_requirements (context : OsSchedCallContext)
  (before : TmrStopState Application) : Prop :=
  tmr_stop_call_unlink_ready context before /\
  tmr_stop_call_nonrunning_unlock_ready context before /\
  tmr_stop_call_no_callback_unlock_ready context before.

Lemma tmr_stop_call_requirements_unlink : forall context before state_read,
  tmr_stop_call_requirements context before ->
  tmr_stop_call_state_prefix context before 3 state_read ->
  pointer = timer_pool_addr sg index /\
  timer_api_initialized state_read.(tmr_stop_kernel).(TimerState) /\
  tmr_unlink_running state_read.(tmr_stop_kernel).(TimerState) index.
Proof.
  intros context before state_read [Hready Hrest] Hprefix. exact (Hready state_read Hprefix).
Qed.

Lemma tmr_stop_call_requirements_nonrunning : forall context before status state_read,
  tmr_stop_call_requirements context before ->
  tmr_stop_call_state_prefix context before status state_read -> status <> 3 ->
  tmr_stop_unlock_ready external critical sg context state_read.
Proof.
  intros context before status state_read [Hunlink [Hready Hrest]] Hprefix Hstatus.
  exact (Hready status state_read Hprefix Hstatus).
Qed.

Lemma tmr_stop_call_requirements_no_callback : forall context before state_read stopped selected,
  tmr_stop_call_requirements context before ->
  tmr_stop_call_state_prefix context before 3 state_read ->
  tmr_stop_unlink_program sg index state_read tt stopped ->
  tmr_stop_select_callback_program pointer index opt argument
    (tmr_stop_set_error (encode_os_err_code OS_ERR_NONE) stopped) None selected ->
  tmr_stop_unlock_ready external critical sg context selected.
Proof.
  intros context before state_read stopped selected [Hunlink [Hnonrunning Hready]]
    Hprefix Hunlinked Hselect.
  exact (Hready state_read stopped selected Hprefix Hunlinked Hselect).
Qed.
End StopCallRequirements.

(** The running lookup obligation is derivable for a current pooled image
    from the ordinary invariant and the byte read.  Raw State=3 has no such
    implication and is not assigned one here. *)
Lemma tmr_stop_call_image_running : forall sg timers index image,
  valid_timer_state sg timers -> timers.(timerImages) index = Some image ->
  image.(timerImageState) = 3 -> tmr_unlink_running timers index.
Proof.
  intros sg timers index image Hvalid Himage Hstate.
  assert (Hnonzero : image.(timerImageState) <> 0) by lia.
  destruct (valid_timer_state_nonunused_image sg timers index image Hvalid Himage Hnonzero)
    as [node [Hnode Hencode]].
  exists node. split; [exact Hnode|].
  rewrite Hstate in Hencode. destruct node.(timerState); simpl in Hencode; congruence.
Qed.

Lemma tmr_stop_call_lock_pooled_binding : forall (Application : Type) critical sg effects
  context (before after : TmrStopState Application) pointer index,
  tmr_stop_lock_program critical sg effects context before tt after ->
  tmr_stop_pooled_binding sg pointer index before.(tmr_stop_kernel).(TimerState) ->
  tmr_stop_pooled_binding sg pointer index after.(tmr_stop_kernel).(TimerState).
Proof.
  intros Application critical sg effects context before after pointer index
    [[Hresult [entry Hcall]] Happ] Hbinding.
  eapply tmr_stop_pooled_binding_storage_frame; [|exact Hbinding].
  eapply timer_public_trace_public_storage_frame.
  eapply os_sched_lock_call_timer_public_trace; exact Hcall.
Qed.

(** Public concrete input instance.  ClientRep owns only the residual
    application resources.  The raw Type/State view is supplied by the
    wrapper, and the unique output is supplied by entry_owned.  Thus no
    uninterpreted raw getters or unexplained entry_calls are required.

    This records the existing verification domain: a branch which actually
    calls configured Unlink supplies its real pool/initialized/running
    facts and kernel ownership.  It does not claim arbitrary fabricated
    Type=100/State=3 objects are valid configured timers.  Raw byte values
    are unrestricted in their representation, so the true raw 0/1/2/invalid
    paths are retained.  A separate low-level nonpool success contract is
    not added by this interface. *)
Section StopPublicCall.
Context {Client : Type} (ClientRep : Client -> TmrStopRules.expr).
Context (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars).
Context (callback : Z -> Z -> Z -> OsSchedCallContext ->
  StateRelMonad.M (TmrStopState (TmrStopCallApplication Client)) OsSchedCallContext).
Context (mask perr nesting : Z) (pooled : bool) (pointer index opt argument : Z).

Local Notation AppRep := (tmr_stop_call_application_rep ClientRep pooled pointer nesting).
Local Notation effects := (tmr_stop_call_effects callback).

Definition tmr_stop_call_input_binding
  (before : TmrStopState (TmrStopCallApplication Client)) : Prop :=
  if pooled then tmr_stop_pooled_binding sg pointer index before.(tmr_stop_kernel).(TimerState)
  else nesting = os_sched_lock_ints before.(tmr_stop_kernel).

Definition tmr_stop_call_pre (context : OsSchedCallContext)
  (before : TmrStopState (TmrStopCallApplication Client))
  (X : tmr_stop_output -> TmrStopState (TmrStopCallApplication Client) -> Prop)
  : TmrStopRules.expr :=
  TmrStopRules.andp (TmrStopRules.coq_prop
    (tmr_stop_call_input_binding before /\
     tmr_stop_call_requirements external critical sg effects pooled pointer index opt argument
       tmr_stop_call_raw_type tmr_stop_call_raw_state context before /\
     tmr_stop_api_pre external critical sg effects pooled pointer index opt argument
       tmr_stop_call_raw_type tmr_stop_call_raw_state context before X))
    (TmrStopRules.andp
      (tmr_stop_call_callback_capabilities AppRep external platform critical sg effects mask perr
        (tmr_stop_call_callback_domain critical sg effects pooled pointer index opt argument
          tmr_stop_call_raw_type tmr_stop_call_raw_state context before)
        pooled pointer index opt argument tmr_stop_call_raw_type tmr_stop_call_raw_state context before)
      (tmr_stop_entry_owned AppRep external platform critical sg mask perr context before)).

Definition tmr_stop_call_post (context : OsSchedCallContext)
  (before : TmrStopState (TmrStopCallApplication Client)) (retcode : Z)
  (X : tmr_stop_output -> TmrStopState (TmrStopCallApplication Client) -> Prop)
  : TmrStopRules.expr :=
  tmr_stop_post AppRep external platform critical sg effects mask perr pooled
    pointer index opt argument tmr_stop_call_raw_type tmr_stop_call_raw_state
    context before retcode X.

Lemma tmr_stop_call_pre_open : forall context before X,
  TmrStopRules.derivable1 (tmr_stop_call_pre context before X)
    (TmrStopRules.andp
      (TmrStopRules.coq_prop
        (tmr_stop_call_input_binding before /\
         tmr_stop_call_requirements external critical sg effects pooled pointer index opt argument
           tmr_stop_call_raw_type tmr_stop_call_raw_state context before /\
         tmr_stop_api_pre external critical sg effects pooled pointer index opt argument
           tmr_stop_call_raw_type tmr_stop_call_raw_state context before X))
      (TmrStopRules.andp
        (tmr_stop_call_callback_capabilities AppRep external platform critical sg effects mask perr
          (tmr_stop_call_callback_domain critical sg effects pooled pointer index opt argument
            tmr_stop_call_raw_type tmr_stop_call_raw_state context before)
          pooled pointer index opt argument tmr_stop_call_raw_type tmr_stop_call_raw_state
          context before)
        (tmr_stop_entry_owned AppRep external platform critical sg mask perr context before))).
Proof. intros context before X heap Hpre. exact Hpre. Qed.

(** The public post is the original exact observation and same-X return;
    it is not the zero stored before a possible callback. *)
Lemma tmr_stop_call_post_open : forall context before retcode X heap,
  tmr_stop_call_post context before retcode X heap ->
  exists returned after,
    tmr_stop_call_result external critical sg effects pooled pointer index opt argument
      tmr_stop_call_raw_type tmr_stop_call_raw_state context before returned
      (retcode, after.(tmr_stop_error)) after /\
    safeExec (eq after) (StateRelMonad.ret (retcode, after.(tmr_stop_error))) X /\
    tmr_stop_owned AppRep external platform critical sg mask perr returned after heap.
Proof.
  intros context before retcode X heap [returned [after [[Hresult Hsafe] Howned]]].
  exists returned, after. split; [exact Hresult|]. split; assumption.
Qed.
End StopPublicCall.
