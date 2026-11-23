Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_client_annotation_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_annotation_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_continuation_progress_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_callback_registry_spec.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Import ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Section TaskClientProgress.
Context {Application : Type}.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (mask : Z) (effects : TmrTaskEffects Application).

(** The complete iteration program supplies the actual Pend and Lock
    steps.  Only their already observed suffix is removed from the same X. *)
Lemma tmr_task_client_scan_initial : forall original_context original history X,
  tmr_task_profile sg ->
  tmr_task_client_outer_facts environment critical sg mask effects
    original_context original history.(tmr_task_continuation_context)
    history.(tmr_task_continuation_completed) history.(tmr_task_continuation_before) X ->
  tmr_task_client_history environment critical sg mask effects
    original_context original history ->
  valid_timer_state sg (tmr_task_timers (tmr_task_continuation_start history)) ->
  timer_api_initialized (tmr_task_timers (tmr_task_continuation_start history)) ->
  tmr_task_client_scan_facts environment critical sg mask effects
    original_context original history [] history.(tmr_task_continuation_lock_context)
    (tmr_task_continuation_start history) (tmr_task_continuation_scan sg history) X.
Proof.
  intros original_context original history X Hprofile [Hprior Hsafe] Hhistory Hvalid Hinit.
  destruct (tmr_task_profile_scan_geometry sg Hprofile) as [Hsize Hlayout].
  assert (Hspoke : tmr_task_spoke_in_range sg (tmr_task_continuation_spoke sg history)).
  { apply tmr_task_selected_spoke_in_range; exact Hsize. }
  assert (Hscan : timer_scan_continuation_valid sg
    (tmr_task_timers (tmr_task_continuation_start history))
    (tmr_task_continuation_scan sg history)).
  { apply (proj1 (tmr_task_scan_at_spoke_valid sg (tmr_task_continuation_spoke sg history)
      (tmr_task_timers (tmr_task_continuation_start history)) Hspoke Hvalid)). }
  split; [exact Hhistory|]. split; [constructor|]. split; [exact Hscan|].
  split; [exact Hspoke|]. split; [exact Hvalid|]. split; [exact Hinit|].
  split; [apply tmr_task_service_frame_refl|].
  intro count; specialize (Hsafe (S count)).
  unfold safeExec, safe, StateRelHoare.weakestpre in Hsafe |- *.
  destruct Hsafe as [seen [Hseen Hsafe]]; subst seen.
  exists (tmr_task_continuation_start history); split; [reflexivity|].
  intros result final [scanned [after_scan [Hscanned
    [returned [after_unlock [Hunlock [later [last [Hlater Hreturn]]]]]]]]].
  pose proof Hhistory as [_ [Hpend Hlock]].
  set (observation := {| tmr_task_wait_error := history.(tmr_task_continuation_error);
    tmr_task_iteration_events := fst scanned; tmr_task_iteration_context := returned |}).
  assert (Hiteration : tmr_task_client_iteration_program environment critical sg mask effects
    history.(tmr_task_continuation_context) history.(tmr_task_continuation_before)
    observation after_unlock).
  { eapply tmr_task_client_iteration_source_steps with
      (signal := (tmr_task_timers history.(tmr_task_continuation_before)).(timerSignalSem))
      (waited := (history.(tmr_task_continuation_error), history.(tmr_task_continuation_wait_context)))
      (after_wait := history.(tmr_task_continuation_waited))
      (locked := history.(tmr_task_continuation_lock_context))
      (after_lock := history.(tmr_task_continuation_locked))
      (scanned := scanned) (after_scan := after_scan) (returned := returned).
    - reflexivity.
    - exact Hpend.
    - exact Hlock.
    - exact Hscanned.
    - exact Hunlock. }
  apply (Hsafe result final).
  exists (observation :: fst later, snd later), last; split.
  - exists observation, after_unlock; split; [exact Hiteration|].
    exists later, last; split; [exact Hlater|split; reflexivity].
  - exact Hreturn.
Qed.

(** Per-step validity and frame evidence come from this actual dispatch
    and, on the callback arm, this actual capability return.  No universal
    preservation premise is introduced for arbitrary callback bodies. *)
Lemma tmr_task_client_scan_step : forall original_context original history visited
  call before scan event after returned finish X,
  tmr_task_client_scan_facts environment critical sg mask effects
    original_context original history visited call before scan X ->
  tmr_task_scan_step sg (tmr_task_callback_program effects)
    (tmr_task_continuation_spoke sg history) before call scan event after returned finish ->
  valid_timer_state sg (tmr_task_timers after) ->
  timer_scan_continuation_valid sg (tmr_task_timers after) finish ->
  timer_api_initialized (tmr_task_timers after) ->
  tmr_task_service_frame (tmr_task_timers before) (tmr_task_timers after) ->
  tmr_task_client_scan_facts environment critical sg mask effects
    original_context original history (visited ++ [event]) returned after finish X.
Proof.
  intros original_context original history visited call before scan event after returned finish X
    [Hhistory [Hprefix [Hscan [Hspoke [Hvalid [Hinit [Hframe Hsafe]]]]]]]
    Hstep Hafter Hfinish Hafterinit Hstepframe.
  assert (Hsingle : tmr_task_scan_prefix sg (tmr_task_callback_program effects)
    (tmr_task_continuation_spoke sg history) before call scan [event] after returned finish).
  { econstructor; [exact Hstep|constructor]. }
  split; [exact Hhistory|]. split.
  - eapply tmr_task_scan_prefix_app; eassumption.
  - split; [exact Hfinish|]. split; [exact Hspoke|]. split; [exact Hafter|].
    split; [exact Hafterinit|]. split.
    + eapply tmr_task_service_frame_trans; eassumption.
    + intro count; specialize (Hsafe count).
      pose proof (tmr_task_scan_prefix_continue sg (tmr_task_callback_program effects)
        (tmr_task_continuation_spoke sg history) _ before call scan [event] after returned finish
        _ X Hsingle Hsafe) as Hcontinue.
      unfold safeExec, safe, StateRelHoare.weakestpre in Hcontinue |- *.
      destruct Hcontinue as [seen [Hseen Hcontinue]]; subst seen.
      exists after; split; [reflexivity|].
      intros result final [tail [middle [Htail Hnext]]].
      apply (Hcontinue result final); exists tail, middle; split; [exact Htail|].
      cbn in *.
      replace ((visited ++ [event]) ++ fst tail) with (visited ++ event :: fst tail) in Hnext
        by (rewrite <- app_assoc; reflexivity).
      exact Hnext.
Qed.

Lemma tmr_task_client_scan_cached_dispatch : forall original_context original history
  visited call before scan index tail future cached timers X,
  tmr_task_profile sg ->
  tmr_task_client_scan_facts environment critical sg mask effects
    original_context original history visited call before scan X ->
  scan.(timerScanRemaining) = index :: tail ->
  timer_scan_advance (tmr_task_timers before) scan = Some future ->
  timer_expire_dispatch sg (tmr_task_timers before) index = Some (cached, None, timers) ->
  tmr_task_scan_step sg (tmr_task_callback_program effects)
    (tmr_task_continuation_spoke sg history) before call scan (index, None)
    (tmr_task_set_timers timers before) call future /\
  tmr_task_client_scan_facts environment critical sg mask effects
    original_context original history (visited ++ [(index, None)]) call
    (tmr_task_set_timers timers before) future X /\
  cached = timer_scan_next_pointer sg future.
Proof.
  intros original_context original history visited call before scan index tail future cached
    timers X Hprofile Hfacts Hremaining Hadvance Hdispatch.
  pose proof Hfacts as [_ [_ [Hscan [Hspoke [Hvalid [Hinit Hrest]]]]]].
  destruct (tmr_task_profile_scan_geometry sg Hprofile) as [Hsize Hlayout].
  destruct (tmr_task_dispatch_cursor_valid sg (tmr_task_timers before) scan index tail future
    cached None timers Hsize Hlayout Hvalid Hscan Hremaining Hadvance Hdispatch)
    as [Hafter [Hfuture [Hpointer Hlength]]].
  assert (Hstep : tmr_task_scan_step sg (tmr_task_callback_program effects)
    (tmr_task_continuation_spoke sg history) before call scan (index, None)
    (tmr_task_set_timers timers before) call future).
  { eapply TmrTaskScanCachedNext; eassumption. }
  split; [exact Hstep|]. split; [|exact Hpointer].
  eapply tmr_task_client_scan_step; [exact Hfacts|exact Hstep|exact Hafter|exact Hfuture| |].
  - unfold timer_api_initialized in *.
    change (timers.(timerInitPhase) = TimerInitializationFinished).
    rewrite (timer_expire_dispatch_preserves_initialization_phase sg (tmr_task_timers before)
      index cached None timers Hdispatch); exact Hinit.
  - eapply tmr_task_dispatch_service_frame; exact Hdispatch.
Qed.

Lemma tmr_task_client_scan_callback_dispatch : forall original_context original history
  visited call before scan index tail future cached timers fn self argument returned after X,
  tmr_task_client_scan_facts environment critical sg mask effects
    original_context original history visited call before scan X ->
  scan.(timerScanRemaining) = index :: tail ->
  timer_scan_advance (tmr_task_timers before) scan = Some future ->
  timer_expire_dispatch sg (tmr_task_timers before) index =
    Some (cached, Some (fn, self, argument), timers) ->
  tmr_task_fields_callback_return_facts sg (tmr_task_callback_program effects)
    fn self argument call (tmr_task_set_timers timers before) returned after ->
  tmr_task_scan_step sg (tmr_task_callback_program effects)
    (tmr_task_continuation_spoke sg history) before call scan
    (index, Some (fn, self, argument)) after returned
    (tmr_task_scan_at_spoke (tmr_task_continuation_spoke sg history) (tmr_task_timers after)) /\
  tmr_task_client_scan_facts environment critical sg mask effects
    original_context original history (visited ++ [(index, Some (fn, self, argument))])
    returned after
    (tmr_task_scan_at_spoke (tmr_task_continuation_spoke sg history) (tmr_task_timers after)) X /\
  timer_scan_next_pointer sg
    (tmr_task_scan_at_spoke (tmr_task_continuation_spoke sg history) (tmr_task_timers after)) =
    tmr_task_head sg (tmr_task_continuation_spoke sg history) (tmr_task_timers after).
Proof.
  intros original_context original history visited call before scan index tail future cached
    timers fn self argument returned after X Hfacts Hremaining Hadvance Hdispatch Hreturn.
  pose proof Hfacts as [_ [_ [_ [Hspoke Hrest]]]].
  destruct Hreturn as [Hcallback [[Hvalid Hinit] [Hframe [Hsame Hpreserves]]]].
  destruct (tmr_task_scan_at_spoke_valid sg (tmr_task_continuation_spoke sg history)
    (tmr_task_timers after) Hspoke Hvalid) as [Hscan Hpointer].
  assert (Hstep : tmr_task_scan_step sg (tmr_task_callback_program effects)
    (tmr_task_continuation_spoke sg history) before call scan
    (index, Some (fn, self, argument)) after returned
    (tmr_task_scan_at_spoke (tmr_task_continuation_spoke sg history) (tmr_task_timers after))).
  { eapply TmrTaskScanReloadHead; eassumption. }
  split; [exact Hstep|]. split; [|exact Hpointer].
  eapply tmr_task_client_scan_step; [exact Hfacts|exact Hstep|exact Hvalid|exact Hscan|exact Hinit|].
  eapply tmr_task_service_frame_trans; [|exact Hframe].
  eapply tmr_task_dispatch_service_frame; exact Hdispatch.
Qed.

Lemma tmr_task_client_scan_exit : forall original_context original history visited
  call before scan returned after X,
  tmr_task_profile sg ->
  tmr_task_client_scan_facts environment critical sg mask effects
    original_context original history visited call before scan X ->
  timer_scan_next_pointer sg scan = 0 ->
  tmr_task_continuation_unlock_program environment critical sg mask effects
    call before returned after ->
  let observation := {| tmr_task_wait_error := history.(tmr_task_continuation_error);
    tmr_task_iteration_events := visited; tmr_task_iteration_context := returned |} in
  tmr_task_client_iteration_program environment critical sg mask effects
    history.(tmr_task_continuation_context) history.(tmr_task_continuation_before)
    observation after /\
  tmr_task_client_outer_facts environment critical sg mask effects
    original_context original returned (history.(tmr_task_continuation_completed) ++ [observation])
    after X.
Proof.
  intros original_context original history visited call before scan returned after X
    Hprofile [Hhistory [Hprefix [Hscan [Hspoke [Hvalid [Hinit [Hframe Hsafe]]]]]]]
    Hnull Hunlock observation.
  destruct (tmr_task_profile_scan_geometry sg Hprofile) as [Hsize Hlayout].
  pose proof (proj1 (timer_scan_continuation_pointer_null_iff sg (tmr_task_timers before)
    scan Hlayout Hvalid Hscan) Hnull) as Hempty.
  assert (Hdone : tmr_task_scan_program sg (tmr_task_callback_program effects)
    (tmr_task_continuation_spoke sg history) call scan before ([], call) before).
  { exists scan; constructor; exact Hempty. }
  assert (Hwhole : tmr_task_scan_program sg (tmr_task_callback_program effects)
    (tmr_task_continuation_spoke sg history) history.(tmr_task_continuation_lock_context)
    (tmr_task_continuation_scan sg history) (tmr_task_continuation_start history)
    (visited, call) before).
  { exists scan; cbn.
    replace visited with (visited ++ []) by apply app_nil_r.
    eapply tmr_task_scan_prefix_execution; [exact Hprefix|constructor; exact Hempty]. }
  pose proof Hhistory as [Hprior [Hpend Hlock]].
  assert (Hiteration : tmr_task_client_iteration_program environment critical sg mask effects
    history.(tmr_task_continuation_context) history.(tmr_task_continuation_before)
    observation after).
  { eapply tmr_task_client_iteration_source_steps with
      (signal := (tmr_task_timers history.(tmr_task_continuation_before)).(timerSignalSem))
      (waited := (history.(tmr_task_continuation_error), history.(tmr_task_continuation_wait_context)))
      (after_wait := history.(tmr_task_continuation_waited))
      (locked := history.(tmr_task_continuation_lock_context))
      (after_lock := history.(tmr_task_continuation_locked))
      (scanned := (visited, call)) (after_scan := before) (returned := returned).
    - reflexivity.
    - exact Hpend.
    - exact Hlock.
    - exact Hwhole.
    - exact Hunlock. }
  split; [exact Hiteration|]. split.
  - eapply tmr_task_client_prefix_app; [exact Hprior|].
    econstructor; [exact Hiteration|constructor].
  - intro count; specialize (Hsafe count).
    unfold safeExec, safe, StateRelHoare.weakestpre in Hsafe |- *.
    destruct Hsafe as [seen [Hseen Hsafe]]; subst seen.
    exists after; split; [reflexivity|].
    intros result final [later [middle [Hlater Hreturn]]].
    apply (Hsafe result final).
    exists ([], call), before; split; [exact Hdone|].
    exists returned, after; split; [exact Hunlock|].
    exists later, middle; split; [exact Hlater|].
    cbn; rewrite app_nil_r.
    rewrite <- app_assoc in Hreturn; cbn in Hreturn; exact Hreturn.
Qed.

(** The actual non-null cursor selects the image used by the C reads. *)
Lemma tmr_task_client_scan_current_image : forall original_context original history
  visited call before scan X,
  tmr_task_client_scan_facts environment critical sg mask effects
    original_context original history visited call before scan X ->
  timer_scan_next_pointer sg scan <> 0 ->
  exists index tail image future,
    scan.(timerScanRemaining) = index :: tail /\
    timer_scan_advance (tmr_task_timers before) scan = Some future /\
    0 <= index < sg.(osKernelConfig).(cfgMaxTimers) /\
    (tmr_task_timers before).(timerImages) index = Some image /\
    tmr_unlink_running (tmr_task_timers before) index /\
    timer_scan_next_pointer sg scan = timer_pool_addr sg index.
Proof.
  intros original_context original history visited call before scan X
    [_ [_ [Hscan [_ [Hvalid Hrest]]]]] Hnonnull.
  apply tmr_task_scan_current_image; assumption.
Qed.

(** The not-due arm performs no Timer update and keeps the cached cursor.
    Its exact actual dispatch is consumed by the same-X step theorem. *)
Lemma tmr_task_client_scan_not_due : forall original_context original history
  visited call before scan index tail future image X,
  tmr_task_profile sg ->
  tmr_task_client_scan_facts environment critical sg mask effects
    original_context original history visited call before scan X ->
  scan.(timerScanRemaining) = index :: tail ->
  timer_scan_advance (tmr_task_timers before) scan = Some future ->
  (tmr_task_timers before).(timerImages) index = Some image ->
  (tmr_task_timers before).(timerTime) <> image.(timerImageMatch) ->
  tmr_task_scan_step sg (tmr_task_callback_program effects)
    (tmr_task_continuation_spoke sg history) before call scan (index, None) before call future /\
  tmr_task_client_scan_facts environment critical sg mask effects
    original_context original history (visited ++ [(index, None)]) call before future X /\
  image.(timerImageNext) = timer_scan_next_pointer sg future.
Proof.
  intros original_context original history visited call before scan index tail future image X
    Hprofile Hfacts Hremaining Hadvance Himage Hnotdue.
  assert (Hdispatch : timer_expire_dispatch sg (tmr_task_timers before) index =
    Some (image.(timerImageNext), None, tmr_task_timers before)).
  { unfold timer_expire_dispatch; rewrite Himage, (proj2 (Z.eqb_neq _ _) Hnotdue); reflexivity. }
  pose proof (tmr_task_client_scan_cached_dispatch original_context original history
    visited call before scan index tail future image.(timerImageNext) (tmr_task_timers before) X
    Hprofile Hfacts Hremaining Hadvance Hdispatch) as Hresult.
  assert (Hsame : tmr_task_set_timers (tmr_task_timers before) before = before).
  { destruct before as [state app]; destruct state; reflexivity. }
  rewrite Hsame in Hresult; exact Hresult.
Qed.

(** The due/null arm uses the actual post-dispatch image. Its null read
    proves the real request is None; it does not discard a callback result. *)
Lemma tmr_task_client_scan_null_callback : forall original_context original history
  visited call before scan index tail future cached dispatched X,
  tmr_task_profile sg ->
  tmr_task_client_scan_facts environment critical sg mask effects
    original_context original history visited call before scan X ->
  scan.(timerScanRemaining) = index :: tail ->
  timer_scan_advance (tmr_task_timers before) scan = Some future ->
  tmr_task_image_read before index TaskMatchField (tmr_task_timers before).(timerTime) ->
  tmr_task_dispatch_prepared sg before index cached dispatched ->
  tmr_task_image_read dispatched index TaskCallbackField 0 ->
  tmr_task_scan_step sg (tmr_task_callback_program effects)
    (tmr_task_continuation_spoke sg history) before call scan (index, None) dispatched call future /\
  tmr_task_client_scan_facts environment critical sg mask effects
    original_context original history (visited ++ [(index, None)]) call dispatched future X /\
  cached = timer_scan_next_pointer sg future.
Proof.
  intros original_context original history visited call before scan index tail future cached dispatched X
    Hprofile Hfacts Hremaining Hadvance [image [Himage Hdue]]
    [request [timers [Hdispatch ->]]] [call_image [Hpost Hzero]].
  cbn [tmr_task_timers tmr_task_set_timers tmr_task_image_value] in Hpost, Hzero, Hdue.
  pose proof (tmr_task_due_dispatch_request_eq sg (tmr_task_timers before) index image cached request
    timers call_image Himage Hdue Hdispatch Hpost) as Hrequest.
  rewrite <- Hzero, Z.eqb_refl in Hrequest; subst request.
  eapply tmr_task_client_scan_cached_dispatch; eassumption.
Qed.

(** A real callback is arbitrary. Its actual existing return facts supply
    the scan/cursor preservation; this consumer adds no body promise and
    does not infer the new domain's capability from the old registry. *)
Lemma tmr_task_client_scan_callback_from_images : forall original_context original history
  visited call before scan index tail future cached dispatched fn argument returned after X,
  tmr_task_client_scan_facts environment critical sg mask effects
    original_context original history visited call before scan X ->
  scan.(timerScanRemaining) = index :: tail ->
  timer_scan_advance (tmr_task_timers before) scan = Some future ->
  tmr_task_image_read before index TaskMatchField (tmr_task_timers before).(timerTime) ->
  tmr_task_dispatch_prepared sg before index cached dispatched ->
  tmr_task_image_read dispatched index TaskCallbackField fn ->
  tmr_task_image_read dispatched index TaskArgumentField argument -> fn <> 0 ->
  tmr_task_fields_callback_return_facts sg (tmr_task_callback_program effects)
    fn (timer_pool_addr sg index) argument call dispatched returned after ->
  tmr_task_scan_step sg (tmr_task_callback_program effects)
    (tmr_task_continuation_spoke sg history) before call scan
    (index, Some (fn, timer_pool_addr sg index, argument)) after returned
    (tmr_task_scan_at_spoke (tmr_task_continuation_spoke sg history) (tmr_task_timers after)) /\
  tmr_task_client_scan_facts environment critical sg mask effects
    original_context original history (visited ++ [(index, Some (fn, timer_pool_addr sg index, argument))])
    returned after
    (tmr_task_scan_at_spoke (tmr_task_continuation_spoke sg history) (tmr_task_timers after)) X /\
  timer_scan_next_pointer sg
    (tmr_task_scan_at_spoke (tmr_task_continuation_spoke sg history) (tmr_task_timers after)) =
    tmr_task_head sg (tmr_task_continuation_spoke sg history) (tmr_task_timers after).
Proof.
  intros original_context original history visited call before scan index tail future cached dispatched
    fn argument returned after X Hfacts Hremaining Hadvance [image [Himage Hdue]]
    [request [timers [Hdispatch ->]]] [call_image [Hpost Hfn]] [arg_image [Hargpost Harg]] Hnonnull Hreturn.
  cbn [tmr_task_timers tmr_task_set_timers tmr_task_image_value] in Hpost, Hfn, Hargpost, Harg, Hdue.
  assert (arg_image = call_image) by congruence; subst arg_image.
  pose proof (tmr_task_due_dispatch_request_eq sg (tmr_task_timers before) index image cached request
    timers call_image Himage Hdue Hdispatch Hpost) as Hrequest.
  rewrite <- Hfn, <- Harg, (proj2 (Z.eqb_neq _ _) Hnonnull) in Hrequest; subst request.
  eapply tmr_task_client_scan_callback_dispatch; eassumption.
Qed.

End TaskClientProgress.
