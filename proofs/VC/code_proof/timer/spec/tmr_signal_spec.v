Require Export Ucos2Verify.VC.code.sem.spec.sem_post_api_spec.
Require Export Ucos2Verify.lib.timer.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.

Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

Definition tmr_signal_profile (sg : StableGlobVars) : Prop :=
  sg.(osKernelConfig).(cfgTimerEnabled) = true /\ sem_post_profile sg.

Definition tmr_signal_optional_event_layout sg pe eid : Prop :=
  pe = 0 \/ event_object_layout_prop sg eid.

(** The C wrapper reads this cell once, before the SemPost call.  Its later
    environment intervals may change the Timer projection; the argument is
    always the entry observation, never a reread of the returned state. *)
Definition tmr_signal_pointer (state : UCOS2_Verify_State) : addr :=
  state.(TimerState).(timerSignalSem).

Definition tmr_signal_program environment critical sg caller mask eid
  : program UCOS2_Verify_State Z :=
  bind (get' tmr_signal_pointer)
    (fun pe => sem_post_api_program environment critical sg caller mask pe eid).

Definition tmr_signal_safe environment critical sg caller mask eid before
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (tmr_signal_program environment critical sg caller mask eid) X.

Definition tmr_signal_post environment critical saved_local sg original mask eid before error
  (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  sem_post_api_post environment critical saved_local sg original mask
    (tmr_signal_pointer before) eid before error X.

Lemma tmr_signal_program_iff : forall environment critical sg caller mask eid before error current,
  tmr_signal_program environment critical sg caller mask eid before error current <->
  sem_post_api_program environment critical sg caller mask
    (tmr_signal_pointer before) eid before error current.
Proof.
  intros; split.
  - intros [pe [read_state [[Hpe Hstate] Hcall]]].
    change (pe = tmr_signal_pointer before) in Hpe.
    subst pe read_state; exact Hcall.
  - intro Hcall; exists (tmr_signal_pointer before), before.
    split; [split; reflexivity|exact Hcall].
Qed.

Lemma tmr_signal_safe_sem_post : forall environment critical sg caller mask eid before X,
  tmr_signal_safe environment critical sg caller mask eid before X ->
  sem_post_api_safe environment critical sg caller mask
    (tmr_signal_pointer before) eid before X.
Proof.
  intros environment critical sg caller mask eid before X Hsafe.
  eapply (highstepbind_derive (get' tmr_signal_pointer)
    (fun pe => sem_post_api_program environment critical sg caller mask pe eid)
    (fun state => state = before) (tmr_signal_pointer before)
    (fun state => state = before)).
  - intros state ->; exists before; repeat split; reflexivity.
  - exact Hsafe.
Qed.

(** This residual is the existing configured Timer representation with only
    the signal handle cell removed.  The boot case retains its real arrays
    and BSS globals, so initialization success is not an API premise. *)
Definition tmr_signal_globals_frame (sg : StableGlobVars) (timers : GlobTimerState) : Assertion :=
  sg.(g_OSTmrFreeList) # Ptr |-> timer_id_pointer sg timers.(timerFree) **
  sg.(g_OSTmrFree) # UShort |-> timers.(timerFreeCount) **
  sg.(g_OSTmrUsed) # UShort |-> timers.(timerUsedCount) **
  sg.(g_OSTmrTime) # UInt |-> timers.(timerTime) **
  sg.(g_OSTmrSem) # Ptr |-> timers.(timerSem).

Definition tmr_signal_timer_frame (sg : StableGlobVars) (timers : GlobTimerState) : Assertion :=
  match timers.(timerInitPhase) with
  | TimerUninitialized =>
      UCharArray.undef_full sg.(g_OSTmrTbl)
        (timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) **
      UCharArray.undef_full sg.(g_OSTmrWheelTbl)
        (8 * sg.(osKernelConfig).(cfgTimerWheelSize)) **
      tmr_signal_globals_frame sg timer_uninitialized
  | _ => timer_images_rep sg timers **
      timer_wheel_rep_from sg sg.(g_OSTmrWheelTbl) timers.(timerWheel) **
      tmr_signal_globals_frame sg timers
  end.

Lemma tmr_signal_timer_split_signal : forall sg timers,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  valid_timer_configuration sg timers ->
  timer_configured_rep sg timers --||--
    sg.(g_OSTmrSemSignal) # Ptr |-> timers.(timerSignalSem) **
    tmr_signal_timer_frame sg timers.
Proof.
  intros sg timers Henabled Hvalid.
  unfold valid_timer_configuration in Hvalid; rewrite Henabled in Hvalid.
  unfold timer_configured_rep, tmr_signal_timer_frame; rewrite Henabled.
  destruct timers.(timerInitPhase) eqn:Hphase;
    unfold timer_raw_rep, timer_uninitialized_rep, timer_globals_rep,
      tmr_signal_globals_frame.
  - subst timers; cbn [timerSignalSem timer_uninitialized]; split; entailer!.
  - split; entailer!.
  - split; entailer!.
  - split; entailer!.
  - split; entailer!.
Qed.

Definition tmr_signal_read_frame environment saved_local sg caller mask before : Assertion :=
  coq_prop (UCOS2_state_inv sg before) &&
  (tmr_signal_timer_frame sg before.(TimerState) **
   UCOS2_raw_rep_missing_timer sg before **
   q_post_outside_frame environment saved_local sg caller mask before).

Lemma tmr_signal_closed_split_signal : forall environment critical saved_local sg caller mask before,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  UCOS2_state_inv sg before ->
  q_post_closed environment critical saved_local sg caller mask before --||--
    sg.(g_OSTmrSemSignal) # Ptr |-> tmr_signal_pointer before **
    tmr_signal_read_frame environment saved_local sg caller mask before.
Proof.
  intros environment critical saved_local sg caller mask before Henabled Hvalid.
  assert (Htimers : valid_timer_configuration sg before.(TimerState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  rewrite (q_post_closed_equiv environment critical saved_local sg caller mask before Hvalid).
  rewrite UCOS2_inv_split_timer.
  rewrite (tmr_signal_timer_split_signal sg before.(TimerState) Henabled Htimers).
  unfold tmr_signal_read_frame, tmr_signal_pointer; split; entailer!.
Qed.
