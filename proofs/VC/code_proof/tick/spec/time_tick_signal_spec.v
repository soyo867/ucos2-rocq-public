Require Export Ucos2Verify.VC.code.tick.spec.time_tick_sem_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_signal_spec.
Require Import Ucos2Verify.lib.timer Ucos2Verify.lib.ucos2_verify_inv.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.

Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition time_tick_signal_pointer (before : UCOS2_Verify_State) : addr :=
  before.(TimerState).(timerSignalSem).

Definition time_tick_signal_read_frame sg (before : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg before) &&
  (tmr_signal_timer_frame sg before.(TimerState) ** UCOS2_raw_rep_missing_timer sg before).

Lemma time_tick_signal_read_split : forall sg before,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  UCOS2_inv sg before |--
    sg.(g_OSTmrSemSignal) # Ptr |-> time_tick_signal_pointer before **
    time_tick_signal_read_frame sg before.
Proof.
  intros sg before Henabled; rewrite UCOS2_inv_split_timer; Intros.
  match goal with Hvalid : UCOS2_state_inv sg before |- _ =>
    assert (Htimers : valid_timer_configuration sg before.(TimerState))
      by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto)
  end.
  rewrite (tmr_signal_timer_split_signal sg before.(TimerState) Henabled Htimers).
  unfold time_tick_signal_read_frame, time_tick_signal_pointer; entailer!.
Qed.

Lemma time_tick_signal_read_merge : forall sg before,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  sg.(g_OSTmrSemSignal) # Ptr |-> time_tick_signal_pointer before **
    time_tick_signal_read_frame sg before |-- UCOS2_inv sg before.
Proof.
  intros sg before Henabled; unfold time_tick_signal_read_frame; Intros.
  match goal with Hvalid : UCOS2_state_inv sg before |- _ =>
    assert (Htimers : valid_timer_configuration sg before.(TimerState))
      by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto)
  end.
  rewrite UCOS2_inv_split_timer.
  rewrite (tmr_signal_timer_split_signal sg before.(TimerState) Henabled Htimers).
  unfold time_tick_signal_pointer; entailer!.
Qed.
