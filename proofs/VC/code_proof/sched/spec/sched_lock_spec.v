Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
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

(** OSSchedLock/OSSchedUnlock, Source/os_core.c:776--846, V2.93.01.
    [running_observed] records the source test BEFORE Save.  In that true
    branch [entry] is the state AFTER Save; the flag is not read again.
    The false branch has no Save/Restore and leaves all kernel state alone.

    These checkpoints end before Restore.  The unlock scheduling decision
    is [sched_unlock_requests_schedule running_observed entry.(IntrState)],
    retained as a branch observation across Restore.  OS_Sched subsequently
    performs its OWN Save and reads the then-current ready/table state; it
    must not be evaluated on this checkpoint in place of that call.
    A scheduler lock does not disable interrupts between these calls. *)
Definition os_sched_lock_checkpoint (running_observed : bool)
  (entry : UCOS2_Verify_State) : UCOS2_Verify_State :=
  replace_IntrS (sched_lock_state running_observed entry.(IntrState)) entry.

Definition os_sched_unlock_checkpoint (running_observed : bool)
  (entry : UCOS2_Verify_State) : UCOS2_Verify_State :=
  replace_IntrS (sched_unlock_state running_observed entry.(IntrState)) entry.

Lemma os_sched_lock_checkpoint_counters_in_range : forall observed entry,
  interrupt_counters_in_range entry.(IntrState) ->
  interrupt_counters_in_range (os_sched_lock_checkpoint observed entry).(IntrState).
Proof. intros; apply sched_lock_preserves_counters_in_range; exact H. Qed.

Lemma os_sched_unlock_checkpoint_counters_in_range : forall observed entry,
  interrupt_counters_in_range entry.(IntrState) ->
  interrupt_counters_in_range (os_sched_unlock_checkpoint observed entry).(IntrState).
Proof. intros; apply sched_unlock_preserves_counters_in_range; exact H. Qed.

Lemma os_sched_lock_not_running_no_effect : forall entry,
  os_sched_lock_checkpoint false entry = entry /\
  os_sched_unlock_checkpoint false entry = entry /\
  sched_unlock_requests_schedule false entry.(IntrState) = false.
Proof. destruct entry; repeat split; reflexivity. Qed.

Lemma os_sched_unlock_request_checkpoint : forall observed entry,
  sched_unlock_requests_schedule observed entry.(IntrState) = true ->
  (os_sched_unlock_checkpoint observed entry).(IntrState).(intNesting) = 0 /\
  (os_sched_unlock_checkpoint observed entry).(IntrState).(lockNesting) = 0.
Proof.
  intros observed entry Hrequest; apply sched_unlock_requests_schedule_iff in Hrequest.
  destruct Hrequest as [-> [Hint Hlock]].
  change ((sched_unlock_state true entry.(IntrState)).(intNesting) = 0 /\
    (sched_unlock_state true entry.(IntrState)).(lockNesting) = 0).
  unfold sched_unlock_state; rewrite Hint, Hlock; simpl; split; reflexivity.
Qed.

(** Removing the last lock and already having no lock are different source
    branches.  Only the former calls OS_Sched after Restore. *)
Lemma os_sched_unlock_zero_no_effect : forall observed entry,
  entry.(IntrState).(lockNesting) = 0 ->
  os_sched_unlock_checkpoint observed entry = entry /\
  sched_unlock_requests_schedule observed entry.(IntrState) = false.
Proof.
  intros observed entry Hzero.
  unfold os_sched_unlock_checkpoint, sched_unlock_state, sched_unlock_requests_schedule.
  rewrite Hzero; destruct observed; simpl;
    destruct (entry.(IntrState).(intNesting) =? 0); simpl;
    destruct entry; split; reflexivity.
Qed.

Lemma os_sched_lock_checkpoint_preserves_validity : forall sg observed entry,
  UCOS2_state_inv sg entry ->
  UCOS2_state_inv sg (os_sched_lock_checkpoint observed entry).
Proof. intros; exact H. Qed.

Lemma os_sched_unlock_checkpoint_preserves_validity : forall sg observed entry,
  UCOS2_state_inv sg entry ->
  UCOS2_state_inv sg (os_sched_unlock_checkpoint observed entry).
Proof. intros; exact H. Qed.

(** The updated UChar cells establish their ranges by the shared typed-cell
    interface.  No extra caller range assumption or per-API heap predicate
    is needed; the residual retains every other module's actual resources. *)
Lemma os_sched_lock_merge_inv : forall sg observed entry,
  UCOS2_state_inv sg entry ->
  store_int_state sg (sched_lock_state observed entry.(IntrState)) **
  UCOS2_raw_rep_missing_interrupt sg entry |--
    UCOS2_inv sg (os_sched_lock_checkpoint observed entry).
Proof.
  intros sg observed entry Hvalid.
  sep_apply_l_atomic (interrupt_inv_merge_counters sg (sched_lock_state observed entry.(IntrState))).
  apply UCOS2_inv_merge_updated_interrupt; exact Hvalid.
Qed.

Lemma os_sched_unlock_merge_inv : forall sg observed entry,
  UCOS2_state_inv sg entry ->
  store_int_state sg (sched_unlock_state observed entry.(IntrState)) **
  UCOS2_raw_rep_missing_interrupt sg entry |--
    UCOS2_inv sg (os_sched_unlock_checkpoint observed entry).
Proof.
  intros sg observed entry Hvalid.
  sep_apply_l_atomic (interrupt_inv_merge_counters sg (sched_unlock_state observed entry.(IntrState))).
  apply UCOS2_inv_merge_updated_interrupt; exact Hvalid.
Qed.

(** Conditional uninterrupted pairing, not a claim that no ISR/environment
    step occurs between two public calls.  Saturated 255 is deliberately
    excluded: the shared source theorem gives 254 after that lock/unlock. *)
Lemma os_sched_lock_unlock_checkpoint_eq : forall entry,
  entry.(IntrState).(intNesting) = 0 ->
  0 <= entry.(IntrState).(lockNesting) < 255 ->
  os_sched_unlock_checkpoint true (os_sched_lock_checkpoint true entry) = entry.
Proof.
  intros entry Hint Hlock; unfold os_sched_unlock_checkpoint, os_sched_lock_checkpoint.
  cbn [replace_IntrS IntrState].
  rewrite (sched_lock_unlock_counters_eq entry.(IntrState) Hint Hlock).
  destruct entry; reflexivity.
Qed.
