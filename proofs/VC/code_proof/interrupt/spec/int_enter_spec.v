Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_verify_inv.

Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSIntEnter, Source/os_core.c:661--669, V2.93.01.  Unlike OSIntExit and
    OSSchedLock/Unlock, this function has NO Save/Restore.  The documented
    caller domain has interrupts already disabled.  Under that protocol
    entry supplies the running observation and the subsequent nesting read.
    The current profile's trace macro is disabled; a trace-enabled profile
    must compose the actual OS_TRACE_ISR_ENTER contract after this step. *)
Definition os_int_enter_state (entry : UCOS2_Verify_State) : UCOS2_Verify_State :=
  replace_IntrS (interrupt_enter_state entry.(SchedState).(isRunning) entry.(IntrState)) entry.

Lemma os_int_enter_counters_in_range : forall entry,
  interrupt_counters_in_range entry.(IntrState) ->
  interrupt_counters_in_range (os_int_enter_state entry).(IntrState).
Proof. intros; apply interrupt_enter_preserves_counters_in_range; exact H. Qed.

Lemma os_int_enter_not_running_no_effect : forall entry,
  entry.(SchedState).(isRunning) = false -> os_int_enter_state entry = entry.
Proof.
  intros entry Hrunning; unfold os_int_enter_state; rewrite Hrunning.
  destruct entry; reflexivity.
Qed.

Lemma os_int_enter_preserves_validity : forall sg entry,
  UCOS2_state_inv sg entry ->
  UCOS2_state_inv sg (os_int_enter_state entry).
Proof. intros; exact H. Qed.

Lemma os_int_enter_merge_inv : forall sg entry,
  UCOS2_state_inv sg entry ->
  store_int_state sg (interrupt_enter_state entry.(SchedState).(isRunning) entry.(IntrState)) **
  UCOS2_raw_rep_missing_interrupt sg entry |-- UCOS2_inv sg (os_int_enter_state entry).
Proof.
  intros sg entry Hvalid.
  sep_apply_l_atomic (interrupt_inv_merge_counters sg
    (interrupt_enter_state entry.(SchedState).(isRunning) entry.(IntrState))).
  apply UCOS2_inv_merge_updated_interrupt; exact Hvalid.
Qed.
