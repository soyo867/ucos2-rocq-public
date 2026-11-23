Require Export Ucos2Verify.lib.timer.
Require Export Ucos2Verify.lib.kernel_resources.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.VC.code.sched.spec.sched_spec.
From SimpleC.SL Require Export CNotation.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.

Import ListNotations Monad MonadNotation.
Local Open Scope Z_scope.

(** Source semantics for the repaired inner loop of OSTmr_Task.  The only
    source change is the read of pspoke->OSTmrFirst after an actual non-NULL
    callback returns.  A NULL callback, and a timer which is not due, still
    use the Next cached before dispatch.

    TimerScanState describes the CURRENT finite chain segment.  It is not
    a set of all objects which remain to be visited in this tick: a returning
    callback resets it to the current head of the original spoke.  None of
    the definitions below assumes visit-once, a decreasing global variant,
    a fixed callback result, or callback/scan termination. *)

Definition tmr_task_scan_at_spoke (spoke : nat) (timers : GlobTimerState)
  : TimerScanState :=
  timer_scan_cursor timers timers.(timerTime) (nth spoke timers.(timerWheel) []).

Definition tmr_task_spoke_in_range (sg : StableGlobVars) (spoke : nat) : Prop :=
  Z.of_nat spoke < sg.(osKernelConfig).(cfgTimerWheelSize).

Lemma tmr_task_scan_at_spoke_valid : forall sg spoke timers,
  tmr_task_spoke_in_range sg spoke -> valid_timer_state sg timers ->
  timer_scan_continuation_valid sg timers (tmr_task_scan_at_spoke spoke timers) /\
  timer_scan_next_pointer sg (tmr_task_scan_at_spoke spoke timers) =
    timer_id_pointer sg (nth spoke timers.(timerWheel) []).
Proof.
  intros sg spoke timers Hspoke Hvalid.
  pose proof Hvalid as [_ [Hwheel _]].
  pose proof Hwheel as [Hlength _].
  assert (Hindex : (spoke < List.length timers.(timerWheel))%nat).
  { unfold tmr_task_spoke_in_range in Hspoke; lia. }
  assert (Hrow : nth_error timers.(timerWheel) spoke =
    Some (nth spoke timers.(timerWheel) [])).
  { apply nth_error_nth'; exact Hindex. }
  assert (Hchain : timer_scan_chain_valid sg timers
    (nth spoke timers.(timerWheel) [])).
  { eapply timer_scan_chain_of_wheel_suffix with (pre := []); eauto. }
  unfold tmr_task_scan_at_spoke; split.
  - apply timer_scan_cursor_valid; [reflexivity|exact Hchain].
  - apply timer_scan_cursor_pointer_eq; exact Hchain.
Qed.

Lemma tmr_task_selected_spoke_in_range : forall sg timers,
  0 < sg.(osKernelConfig).(cfgTimerWheelSize) <= 65536 ->
  tmr_task_spoke_in_range sg
    (Z.to_nat (timer_spoke sg.(osKernelConfig) timers.(timerTime))).
Proof.
  intros sg timers Hsize.
  pose proof (timer_spoke_in_range sg.(osKernelConfig) timers.(timerTime) Hsize)
    as Hrange.
  unfold tmr_task_spoke_in_range; rewrite Z2Nat.id by lia; lia.
Qed.

Lemma tmr_task_scan_begin_at_spoke : forall sg timers,
  timer_scan_begin sg timers =
    tmr_task_scan_at_spoke
      (Z.to_nat (timer_spoke sg.(osKernelConfig) timers.(timerTime))) timers.
Proof. reflexivity. Qed.

(** These five fields are owned by the timer service/configuration.  The
    callback source contract must supply this frame for a returning legal
    client.  It deliberately says nothing about timerUsed, timerImages,
    timerWheel, allocation generations, or any application's state. *)
Definition tmr_task_service_frame (before after : GlobTimerState) : Prop :=
  after.(timerTime) = before.(timerTime) /\
  after.(timerSem) = before.(timerSem) /\
  after.(timerSignalSem) = before.(timerSignalSem) /\
  after.(timerTask) = before.(timerTask) /\
  after.(timerInitPhase) = before.(timerInitPhase).

Lemma tmr_task_service_frame_refl : forall timers,
  tmr_task_service_frame timers timers.
Proof. intros; repeat split; reflexivity. Qed.

Lemma tmr_task_service_frame_trans : forall first middle last,
  tmr_task_service_frame first middle -> tmr_task_service_frame middle last ->
  tmr_task_service_frame first last.
Proof. unfold tmr_task_service_frame; intros; intuition congruence. Qed.

Lemma tmr_task_service_frame_initialized_configuration : forall sg before after,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  timer_api_initialized before -> valid_timer_state sg after ->
  tmr_task_service_frame before after ->
  valid_timer_configuration sg after /\ timer_api_initialized after.
Proof.
  intros sg before after Henabled Hinitialized Hvalid
    [Htime [Hsem [Hsignal [Htask Hphase]]]].
  assert (Hafter : timer_api_initialized after).
  { unfold timer_api_initialized in *; rewrite Hphase; exact Hinitialized. }
  split; [|exact Hafter].
  apply (proj2 (timer_initialized_configuration_iff sg after Henabled Hafter));
    exact Hvalid.
Qed.

Lemma tmr_task_u32_positive_delay_changes_time : forall time delay,
  0 <= time < 4294967296 -> 0 < delay < 4294967296 ->
  kernel_u32 (delay + time) <> time.
Proof.
  intros time delay Htime Hdelay; unfold kernel_u32.
  destruct (Z_lt_ge_dec (delay + time) 4294967296) as [Hsmall|Hwrap].
  - rewrite Z.mod_small by lia; lia.
  - replace (delay + time) with
      ((delay + time - 4294967296) + 1 * 4294967296) by lia.
    rewrite Z.mod_add by lia; rewrite Z.mod_small by lia; lia.
Qed.

(** Only the immediate relink result is covered here.  A later callback
    may legally stop/delete/restart an object; no old object identity or
    visit-once claim is transported across that call. *)
Lemma tmr_task_periodic_relink_not_due : forall time object,
  0 <= time < 4294967296 -> valid_timer_object object ->
  object.(timerMode) = TimerPeriodic ->
  (timer_link_object time true object).(timerMatch) <> time.
Proof.
  intros time object Htime [Hdelay [Hperiod [Hmatch [Hstate Hmode]]]] Hperiodic.
  rewrite Hperiodic in Hmode.
  change (kernel_u32 (object.(timerPeriod) + time) <> time).
  apply tmr_task_u32_positive_delay_changes_time; lia.
Qed.

Lemma tmr_task_unlink_service_frame : forall sg before index after,
  timer_unlink sg before index = Some after -> tmr_task_service_frame before after.
Proof.
  intros sg before index after Hstep; unfold timer_unlink in Hstep.
  destruct (timerUsed before index), (timerImages before index); try discriminate.
  inversion Hstep; subst; repeat split; reflexivity.
Qed.

Lemma tmr_task_link_service_frame : forall sg before index periodic after,
  timer_link sg before index periodic = Some after ->
  tmr_task_service_frame before after.
Proof.
  intros sg before index periodic after Hstep; unfold timer_link in Hstep.
  destruct (timerUsed before index), (timerImages before index); try discriminate.
  inversion Hstep; subst; repeat split; reflexivity.
Qed.

Lemma tmr_task_complete_service_frame : forall before index after,
  timer_complete before index = Some after -> tmr_task_service_frame before after.
Proof.
  intros before index after Hstep; unfold timer_complete in Hstep.
  destruct (timerUsed before index), (timerImages before index); try discriminate.
  inversion Hstep; subst; repeat split; reflexivity.
Qed.

Lemma tmr_task_dispatch_service_frame : forall sg before index next request after,
  timer_expire_dispatch sg before index = Some (next, request, after) ->
  tmr_task_service_frame before after.
Proof.
  intros sg before index next request after Hstep.
  unfold timer_expire_dispatch in Hstep.
  destruct (timerImages before index) as [image|]; [|discriminate].
  destruct (Z.eqb (timerTime before) (timerImageMatch image)).
  - destruct (timer_unlink sg before index) as [unlinked|] eqn:Hunlink;
      [|discriminate].
    destruct (timerImages unlinked index) as [stopped|]; [|discriminate].
    destruct (Z.eqb (timerImageOption stopped) 2).
    + destruct (timer_link sg unlinked index true) as [linked|] eqn:Hlink;
        [|discriminate].
      destruct (timerImages linked index); [|discriminate].
      inversion Hstep; subst after.
      eapply tmr_task_service_frame_trans.
      * eapply tmr_task_unlink_service_frame; exact Hunlink.
      * eapply tmr_task_link_service_frame; exact Hlink.
    + destruct (timer_complete unlinked index) as [completed|] eqn:Hcomplete;
        [|discriminate].
      destruct (timerImages completed index); [|discriminate].
      inversion Hstep; subst after.
      eapply tmr_task_service_frame_trans.
      * eapply tmr_task_unlink_service_frame; exact Hunlink.
      * eapply tmr_task_complete_service_frame; exact Hcomplete.
  - inversion Hstep; subst after; apply tmr_task_service_frame_refl.
Qed.

(** The existing cached-tail theorem is used only up to dispatch, before
    any callback has run.  Its callback-return premise is proved by the
    identity step here; it is never asserted of an arbitrary callback. *)
Lemma tmr_task_dispatch_cursor_valid : forall sg before scan index rest future
  next request dispatched,
  0 < sg.(osKernelConfig).(cfgTimerWheelSize) <= 65536 ->
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  valid_timer_state sg before -> timer_scan_continuation_valid sg before scan ->
  scan.(timerScanRemaining) = index :: rest ->
  timer_scan_advance before scan = Some future ->
  timer_expire_dispatch sg before index = Some (next, request, dispatched) ->
  valid_timer_state sg dispatched /\
  timer_scan_continuation_valid sg dispatched future /\
  next = timer_scan_next_pointer sg future /\
  S (List.length future.(timerScanRemaining)) = List.length scan.(timerScanRemaining).
Proof.
  intros sg before scan index rest future next request dispatched Hsize Hlayout
    Hvalid Hscan Hremaining Hadvance Hdispatch.
  destruct (timer_scan_continuation_remaining_running sg before scan index Hscan
    ltac:(rewrite Hremaining; left; reflexivity)) as [object [Hobject Hrunning]].
  assert (Hdvalid : valid_timer_state sg dispatched).
  { eapply timer_expire_dispatch_preserves_state_validity; eauto. }
  assert (Hidentity : valid_timer_callback_return sg dispatched dispatched future request).
  { destruct request; simpl.
    - split; [exact Hdvalid|apply timer_callback_preserves_scan_reflexive].
    - reflexivity. }
  exact (timer_expire_visit_callback_return sg before scan index rest future next
    request dispatched dispatched Hsize Hlayout Hvalid Hscan Hremaining Hadvance
    Hdispatch Hidentity).
Qed.

Definition tmr_task_scan_world (Application : Type) :=
  (UCOS2_Verify_State * Application)%type.

Definition tmr_task_timers {Application} (world : tmr_task_scan_world Application)
  : GlobTimerState := (fst world).(TimerState).

Definition tmr_task_set_timers {Application} (timers : GlobTimerState)
  (world : tmr_task_scan_world Application) : tmr_task_scan_world Application :=
  (replace_TimerS timers (fst world), snd world).

Lemma tmr_task_set_timers_projection : forall Application timers
  (world : tmr_task_scan_world Application),
  tmr_task_timers (tmr_task_set_timers timers world) = timers.
Proof. reflexivity. Qed.

Definition tmr_task_scan_event := (TimerID * option (addr * addr * addr))%type.

Section TaskScan.

Context {Application : Type}.
Context (sg : StableGlobVars).
Context (callback : (addr * addr * addr) -> OsSchedCallContext ->
  program (tmr_task_scan_world Application) OsSchedCallContext).
Context (spoke : nat).

(** Constructors contain literal execution conditions, never the validity
    or service-frame obligations needed to recover the loop invariant.
    The returned context is a resource descriptor, not a new C return value.
    The original pspoke is fixed even when the callback changes the wheel. *)
Inductive tmr_task_scan_step : tmr_task_scan_world Application ->
  OsSchedCallContext -> TimerScanState -> tmr_task_scan_event ->
  tmr_task_scan_world Application -> OsSchedCallContext -> TimerScanState -> Prop :=
| TmrTaskScanCachedNext : forall before context scan index rest future next dispatched,
    scan.(timerScanRemaining) = index :: rest ->
    timer_scan_advance (tmr_task_timers before) scan = Some future ->
    timer_expire_dispatch sg (tmr_task_timers before) index =
      Some (next, None, dispatched) ->
    tmr_task_scan_step before context scan (index, None)
      (tmr_task_set_timers dispatched before) context future
| TmrTaskScanReloadHead : forall before context scan index rest future next call
    dispatched returned after,
    scan.(timerScanRemaining) = index :: rest ->
    timer_scan_advance (tmr_task_timers before) scan = Some future ->
    timer_expire_dispatch sg (tmr_task_timers before) index =
      Some (next, Some call, dispatched) ->
    callback call context (tmr_task_set_timers dispatched before) returned after ->
    tmr_task_scan_step before context scan (index, Some call) after returned
      (tmr_task_scan_at_spoke spoke (tmr_task_timers after)).

Inductive tmr_task_scan_prefix : tmr_task_scan_world Application ->
  OsSchedCallContext -> TimerScanState -> list tmr_task_scan_event ->
  tmr_task_scan_world Application -> OsSchedCallContext -> TimerScanState -> Prop :=
| TmrTaskScanPrefixEmpty : forall before context scan,
    tmr_task_scan_prefix before context scan [] before context scan
| TmrTaskScanPrefixStep : forall before context scan event middle continued future
    events after returned finish,
    tmr_task_scan_step before context scan event middle continued future ->
    tmr_task_scan_prefix middle continued future events after returned finish ->
    tmr_task_scan_prefix before context scan (event :: events) after returned finish.

Inductive tmr_task_scan_execution : tmr_task_scan_world Application ->
  OsSchedCallContext -> TimerScanState -> list tmr_task_scan_event ->
  tmr_task_scan_world Application -> OsSchedCallContext -> TimerScanState -> Prop :=
| TmrTaskScanDone : forall before context scan,
    scan.(timerScanRemaining) = [] ->
    tmr_task_scan_execution before context scan [] before context scan
| TmrTaskScanVisit : forall before context scan event middle continued future
    events after returned finish,
    tmr_task_scan_step before context scan event middle continued future ->
    tmr_task_scan_execution middle continued future events after returned finish ->
    tmr_task_scan_execution before context scan (event :: events) after returned finish.

Lemma tmr_task_scan_prefix_app : forall before context scan events middle continued
  future tail after returned finish,
  tmr_task_scan_prefix before context scan events middle continued future ->
  tmr_task_scan_prefix middle continued future tail after returned finish ->
  tmr_task_scan_prefix before context scan (events ++ tail) after returned finish.
Proof.
  intros before context scan events middle continued future tail after returned finish
    Hprefix Htail; induction Hprefix.
  - exact Htail.
  - simpl; econstructor; eauto.
Qed.

Lemma tmr_task_scan_prefix_execution : forall before context scan events middle
  continued future tail after returned finish,
  tmr_task_scan_prefix before context scan events middle continued future ->
  tmr_task_scan_execution middle continued future tail after returned finish ->
  tmr_task_scan_execution before context scan (events ++ tail) after returned finish.
Proof.
  intros before context scan events middle continued future tail after returned finish
    Hprefix Htail; induction Hprefix.
  - exact Htail.
  - simpl; econstructor; eauto.
Qed.

Lemma tmr_task_scan_execution_prefix : forall before context scan events after
  returned finish,
  tmr_task_scan_execution before context scan events after returned finish ->
  tmr_task_scan_prefix before context scan events after returned finish /\
  finish.(timerScanRemaining) = [].
Proof.
  intros before context scan events after returned finish Hexec; induction Hexec.
  - split; [constructor|assumption].
  - destruct IHHexec as [Hprefix Hempty]; split; [econstructor; eauto|exact Hempty].
Qed.

Lemma tmr_task_scan_step_callback_fields : forall before context scan event after
  returned finish,
  tmr_task_scan_step before context scan event after returned finish ->
  match snd event with
  | None => True
  | Some (fn, self, _) => fn <> 0 /\ self = timer_pool_addr sg (fst event)
  end.
Proof.
  intros before context scan event after returned finish Hstep; destruct Hstep.
  - exact I.
  - destruct call as [[fn self] arg].
    match goal with Hdispatch : timer_expire_dispatch _ _ _ = Some (_, Some _, _) |- _ =>
      destruct (timer_expire_dispatch_callback_request_fields _ _ _ _ _ _ _ _ Hdispatch)
        as [Hself [Hfn Himage]] end.
    simpl; split; assumption.
Qed.

Lemma tmr_task_scan_prefix_callback_fields : forall before context scan events after
  returned finish,
  tmr_task_scan_prefix before context scan events after returned finish ->
  Forall (fun event => match snd event with
    | None => True
    | Some (fn, self, _) => fn <> 0 /\ self = timer_pool_addr sg (fst event)
    end) events.
Proof.
  intros before context scan events after returned finish Hprefix; induction Hprefix.
  - constructor.
  - constructor; [eapply tmr_task_scan_step_callback_fields; eauto|exact IHHprefix].
Qed.

(** This is a proposition to be proved from actual function capabilities
    and returning-call contracts.  It is not an axiom, a guard in callback,
    a blanket property of compatible C function types, or a source bridge.
    The local reload lemma below can instead consume one concrete return
    postcondition; no whole-domain law is needed at that C cutpoint. *)
Definition tmr_task_callback_return_contract : Prop :=
  forall call context before returned after,
    valid_timer_state sg (tmr_task_timers before) ->
    callback call context before returned after ->
    valid_timer_state sg (tmr_task_timers after) /\
    tmr_task_service_frame (tmr_task_timers before) (tmr_task_timers after).

Lemma tmr_task_callback_reload_valid : forall
  (before after : tmr_task_scan_world Application),
  tmr_task_spoke_in_range sg spoke ->
  valid_timer_state sg (tmr_task_timers after) ->
  tmr_task_service_frame (tmr_task_timers before) (tmr_task_timers after) ->
  timer_scan_continuation_valid sg (tmr_task_timers after)
    (tmr_task_scan_at_spoke spoke (tmr_task_timers after)) /\
  timer_scan_next_pointer sg (tmr_task_scan_at_spoke spoke (tmr_task_timers after)) =
    timer_id_pointer sg (nth spoke (tmr_task_timers after).(timerWheel) []) /\
  (tmr_task_timers after).(timerTime) = (tmr_task_timers before).(timerTime).
Proof.
  intros before after Hspoke Hvalid Hframe.
  destruct (tmr_task_scan_at_spoke_valid sg spoke (tmr_task_timers after)
    Hspoke Hvalid) as [Hscan Hpointer].
  split; [exact Hscan|]. split; [exact Hpointer|exact (proj1 Hframe)].
Qed.

Lemma tmr_task_scan_step_preserves_validity : forall before context scan event after
  returned finish,
  0 < sg.(osKernelConfig).(cfgTimerWheelSize) <= 65536 ->
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  tmr_task_spoke_in_range sg spoke -> tmr_task_callback_return_contract ->
  tmr_task_scan_step before context scan event after returned finish ->
  valid_timer_state sg (tmr_task_timers before) ->
  timer_scan_continuation_valid sg (tmr_task_timers before) scan ->
  valid_timer_state sg (tmr_task_timers after) /\
  timer_scan_continuation_valid sg (tmr_task_timers after) finish /\
  tmr_task_service_frame (tmr_task_timers before) (tmr_task_timers after).
Proof.
  intros before context scan event after returned finish Hsize Hlayout Hspoke
    Hcallback Hstep Hvalid Hscan.
  destruct Hstep as
    [before context scan index rest future next dispatched Hremaining Hadvance Hdispatch
    |before context scan index rest future next call dispatched returned after
      Hremaining Hadvance Hdispatch Hcall].
  - rewrite tmr_task_set_timers_projection.
    destruct (tmr_task_dispatch_cursor_valid sg (tmr_task_timers before) scan index
      rest future next None dispatched Hsize Hlayout Hvalid Hscan Hremaining
      Hadvance Hdispatch) as [Hdvalid [Hfuture Hnext]].
    split; [exact Hdvalid|]. split; [exact Hfuture|].
    eapply tmr_task_dispatch_service_frame; exact Hdispatch.
  - destruct (tmr_task_dispatch_cursor_valid sg (tmr_task_timers before) scan index
      rest future next (Some call) dispatched Hsize Hlayout Hvalid Hscan Hremaining
      Hadvance Hdispatch) as [Hdvalid Hfuture].
    destruct (Hcallback call context (tmr_task_set_timers dispatched before)
      returned after Hdvalid Hcall) as [Hafter Hframe].
    rewrite tmr_task_set_timers_projection in Hframe.
    split; [exact Hafter|]. split.
    + exact (proj1 (tmr_task_scan_at_spoke_valid sg spoke
        (tmr_task_timers after) Hspoke Hafter)).
    + eapply tmr_task_service_frame_trans; [|exact Hframe].
      eapply tmr_task_dispatch_service_frame; exact Hdispatch.
Qed.

Lemma tmr_task_scan_prefix_preserves_validity : forall before context scan events after
  returned finish,
  0 < sg.(osKernelConfig).(cfgTimerWheelSize) <= 65536 ->
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  tmr_task_spoke_in_range sg spoke -> tmr_task_callback_return_contract ->
  tmr_task_scan_prefix before context scan events after returned finish ->
  valid_timer_state sg (tmr_task_timers before) ->
  timer_scan_continuation_valid sg (tmr_task_timers before) scan ->
  valid_timer_state sg (tmr_task_timers after) /\
  timer_scan_continuation_valid sg (tmr_task_timers after) finish /\
  tmr_task_service_frame (tmr_task_timers before) (tmr_task_timers after).
Proof.
  intros before context scan events after returned finish Hsize Hlayout Hspoke
    Hcallback Hprefix; induction Hprefix; intros Hvalid Hscan.
  - split; [exact Hvalid|]. split; [exact Hscan|apply tmr_task_service_frame_refl].
  - destruct (tmr_task_scan_step_preserves_validity _ _ _ _ _ _ _
      Hsize Hlayout Hspoke Hcallback H Hvalid Hscan)
      as [Hmiddle [Hfuture Hframe]].
    destruct (IHHprefix Hmiddle Hfuture) as [Hafter [Hfinish Htailframe]].
    split; [exact Hafter|]. split; [exact Hfinish|].
    eapply tmr_task_service_frame_trans; eauto.
Qed.

Lemma tmr_task_scan_execution_exit_pointer : forall before context scan events after
  returned finish,
  0 < sg.(osKernelConfig).(cfgTimerWheelSize) <= 65536 ->
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  tmr_task_spoke_in_range sg spoke -> tmr_task_callback_return_contract ->
  tmr_task_scan_execution before context scan events after returned finish ->
  valid_timer_state sg (tmr_task_timers before) ->
  timer_scan_continuation_valid sg (tmr_task_timers before) scan ->
  valid_timer_state sg (tmr_task_timers after) /\
  timer_scan_next_pointer sg finish = 0 /\
  tmr_task_service_frame (tmr_task_timers before) (tmr_task_timers after).
Proof.
  intros before context scan events after returned finish Hsize Hlayout Hspoke
    Hcallback Hexec Hvalid Hscan.
  destruct (tmr_task_scan_execution_prefix _ _ _ _ _ _ _ Hexec) as [Hprefix Hempty].
  destruct (tmr_task_scan_prefix_preserves_validity _ _ _ _ _ _ _
    Hsize Hlayout Hspoke Hcallback Hprefix Hvalid Hscan)
    as [Hafter [Hfinish Hframe]].
  split; [exact Hafter|]. split; [|exact Hframe].
  apply (proj2 (timer_scan_continuation_pointer_null_iff sg (tmr_task_timers after)
    finish Hlayout Hafter Hfinish)); exact Hempty.
Qed.

(** A completed inner-loop source program.  The output is a logical trace
    plus the actual returning resource context.  The C function is void;
    the caller's continuation is Unlock followed by its next SemPend loop.
    The finite-prefix relation above also records executions which have
    not yet reached the NULL cursor. *)
Definition tmr_task_scan_program (context : OsSchedCallContext) (scan : TimerScanState)
  : program (tmr_task_scan_world Application)
      (list tmr_task_scan_event * OsSchedCallContext) :=
  fun before output after => exists finish,
    tmr_task_scan_execution before context scan (fst output) after (snd output) finish.

(** The exact same X crosses every completed finite prefix.  Appending the
    observed prefix happens in the continuation, not by constraining X to
    True or replacing X with an unrelated postcondition. *)
Lemma tmr_task_scan_prefix_continue : forall (Result : Type) before context scan
  events after returned finish
  (next : (list tmr_task_scan_event * OsSchedCallContext) ->
    program (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop),
  tmr_task_scan_prefix before context scan events after returned finish ->
  safeExec (eq before) (bind (tmr_task_scan_program context scan) next) X ->
  safeExec (eq after)
    (bind (tmr_task_scan_program returned finish)
      (fun output => next (events ++ fst output, snd output))) X.
Proof.
  intros Result before context scan events after returned finish next X Hprefix Hsafe.
  unfold safeExec, safe, StateRelHoare.weakestpre in *.
  destruct Hsafe as [seen [Hseen Hsafe]]; subst seen.
  exists after; split; [reflexivity|].
  intros result final [output [scan_after [[last Hexec] Hnext]]].
  apply (Hsafe result final).
  exists (events ++ fst output, snd output), scan_after; split; [|exact Hnext].
  exists last; simpl; eapply tmr_task_scan_prefix_execution; eauto.
Qed.

Lemma tmr_task_scan_cached_next_continue : forall (Result : Type) before context scan
  index rest future next_pointer dispatched
  (next : (list tmr_task_scan_event * OsSchedCallContext) ->
    program (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop),
  scan.(timerScanRemaining) = index :: rest ->
  timer_scan_advance (tmr_task_timers before) scan = Some future ->
  timer_expire_dispatch sg (tmr_task_timers before) index =
    Some (next_pointer, None, dispatched) ->
  safeExec (eq before) (bind (tmr_task_scan_program context scan) next) X ->
  safeExec (eq (tmr_task_set_timers dispatched before))
    (bind (tmr_task_scan_program context future)
      (fun output => next ((index, None) :: fst output, snd output))) X.
Proof.
  intros Result before context scan index rest future next_pointer dispatched next X
    Hremaining Hadvance Hdispatch Hsafe.
  eapply tmr_task_scan_prefix_continue with (events := [(index, None)]); [|exact Hsafe].
  econstructor; [eapply TmrTaskScanCachedNext; eauto|constructor].
Qed.

Lemma tmr_task_scan_callback_continue : forall (Result : Type) before context scan
  index rest future next_pointer call dispatched returned after
  (next : (list tmr_task_scan_event * OsSchedCallContext) ->
    program (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop),
  scan.(timerScanRemaining) = index :: rest ->
  timer_scan_advance (tmr_task_timers before) scan = Some future ->
  timer_expire_dispatch sg (tmr_task_timers before) index =
    Some (next_pointer, Some call, dispatched) ->
  callback call context (tmr_task_set_timers dispatched before) returned after ->
  safeExec (eq before) (bind (tmr_task_scan_program context scan) next) X ->
  safeExec (eq after)
    (bind (tmr_task_scan_program returned
        (tmr_task_scan_at_spoke spoke (tmr_task_timers after)))
      (fun output => next ((index, Some call) :: fst output, snd output))) X.
Proof.
  intros Result before context scan index rest future next_pointer call dispatched
    returned after next X Hremaining Hadvance Hdispatch Hcall Hsafe.
  eapply tmr_task_scan_prefix_continue with (events := [(index, Some call)]);
    [|exact Hsafe].
  econstructor; [eapply TmrTaskScanReloadHead; eauto|constructor].
Qed.

Lemma tmr_task_scan_empty_continue : forall (Result : Type) before context scan
  (next : (list tmr_task_scan_event * OsSchedCallContext) ->
    program (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop),
  scan.(timerScanRemaining) = [] ->
  safeExec (eq before) (bind (tmr_task_scan_program context scan) next) X ->
  safeExec (eq before) (next ([], context)) X.
Proof.
  intros Result before context scan next X Hempty Hsafe.
  unfold safeExec, safe, StateRelHoare.weakestpre in *.
  destruct Hsafe as [seen [Hseen Hsafe]]; subst seen.
  exists before; split; [reflexivity|].
  intros result after Hnext; apply (Hsafe result after).
  exists ([], context), before; split; [|exact Hnext].
  exists scan; constructor; exact Hempty.
Qed.

End TaskScan.

(** Time++ uses the canonical unsigned transformer; the selected spoke is
    calculated once from the updated time and is passed unchanged through
    all callback restarts.  This is the body AFTER Lock, not a replacement
    for either surrounding call or for the infinite outer C loop. *)
Definition tmr_task_tick_program {Application} (sg : StableGlobVars)
  (callback : (addr * addr * addr) -> OsSchedCallContext ->
    program (tmr_task_scan_world Application) OsSchedCallContext)
  (context : OsSchedCallContext)
  : program (tmr_task_scan_world Application)
      (list tmr_task_scan_event * OsSchedCallContext) :=
  fun before output after =>
    let advanced := tmr_task_set_timers (timer_service_advance (tmr_task_timers before)) before in
    let timers := tmr_task_timers advanced in
    tmr_task_scan_program sg callback
      (Z.to_nat (timer_spoke sg.(osKernelConfig) timers.(timerTime)))
      context (timer_scan_begin sg timers) advanced output after.

Lemma tmr_task_tick_advance_continue : forall Application sg callback context
  (Result : Type) (before : tmr_task_scan_world Application)
  (next : (list tmr_task_scan_event * OsSchedCallContext) ->
    program (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop),
  let advanced := tmr_task_set_timers (timer_service_advance (tmr_task_timers before)) before in
  let timers := tmr_task_timers advanced in
  safeExec (eq before) (bind (tmr_task_tick_program sg callback context) next) X ->
  safeExec (eq advanced)
    (bind (tmr_task_scan_program sg callback
      (Z.to_nat (timer_spoke sg.(osKernelConfig) timers.(timerTime)))
      context (timer_scan_begin sg timers)) next) X.
Proof.
  intros Application sg callback context Result before next X advanced timers Hsafe.
  unfold safeExec, safe, StateRelHoare.weakestpre in *.
  destruct Hsafe as [seen [Hseen Hsafe]]; subst seen.
  exists advanced; split; [reflexivity|].
  intros result final [output [after [Hscan Hnext]]].
  apply (Hsafe result final); exists output, after; split; [exact Hscan|exact Hnext].
Qed.
