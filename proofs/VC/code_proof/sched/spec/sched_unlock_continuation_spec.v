Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.micromega.Lia.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Export Ucos2Verify.VC.code.sched.spec.sched_unlock_call_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_unlock_task_scheduler_adapter_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_lock_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.

Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The boolean is the literal protected C decision, made BEFORE Restore.
    It remains fixed even if Restore returns a different current world. *)
Definition os_sched_unlock_checkpoint_program :
  StateRelMonad.M UCOS2_Verify_State bool :=
  fun entry request released =>
    request = os_sched_unlock_requests entry /\
    released = os_sched_unlock_checkpoint true entry.

Definition os_sched_unlock_tail_program environment critical sg mask (request : bool) restored :
  StateRelMonad.M UCOS2_Verify_State OsSchedCallContext :=
  if request then SchedulerPhaseCandidate.os_sched_task_program
    (task_sw_hook_call_environment environment) critical sg restored mask
  else StateRelMonad.ret restored.

Definition os_sched_unlock_continuation_program environment critical sg original mask :
  StateRelMonad.M UCOS2_Verify_State OsSchedCallContext :=
  fun before =>
    if before.(SchedState).(isRunning) then
      (StateRelMonad.bind
        (os_sched_continuation_save_program environment critical sg original mask)
        (fun entered => StateRelMonad.bind os_sched_unlock_checkpoint_program
          (fun request => StateRelMonad.bind
            (os_sched_continuation_restore_program environment critical sg (fst entered))
            (fun restored => os_sched_unlock_tail_program environment critical sg mask request restored)))) before
    else StateRelMonad.ret original before.

Definition os_sched_unlock_continuation_prefix environment critical sg original mask
  before acquired restored unlocked : Prop :=
  before.(SchedState).(isRunning) = true /\
  exists entered saved,
    os_sched_continuation_save_effect environment critical sg original mask saved before entered acquired /\
    os_sched_continuation_restore_effect environment critical sg entered
      (os_sched_unlock_checkpoint true acquired) restored unlocked.

Definition os_sched_unlock_continuation_history environment critical sg original mask
  before returned current : Prop :=
  if before.(SchedState).(isRunning) then
    exists acquired restored unlocked,
      os_sched_unlock_continuation_prefix environment critical sg original mask
        before acquired restored unlocked /\
      os_sched_unlock_tail_program environment critical sg mask
        (os_sched_unlock_requests acquired) restored unlocked returned current
  else returned = original /\ before = current.

Lemma os_sched_unlock_continuation_program_iff : forall environment critical sg original mask
  before returned current,
  os_sched_unlock_continuation_program environment critical sg original mask before returned current <->
  os_sched_unlock_continuation_history environment critical sg original mask before returned current.
Proof.
  intros; unfold os_sched_unlock_continuation_program, os_sched_unlock_continuation_history.
  destruct before.(SchedState).(isRunning) eqn:Hrunning; [|reflexivity].
  unfold StateRelMonad.bind, os_sched_continuation_save_program,
    os_sched_unlock_checkpoint_program, os_sched_continuation_restore_program.
  split.
  - intros [[entered saved] [acquired [Hsave [request [released [[Hrequest Hreleased]
      [restored [unlocked [Hrestore Htail]]]]]]]]].
    subst request; subst released.
    exists acquired, restored, unlocked; split; [|exact Htail].
    split; [exact Hrunning|]. exists entered, saved; split; assumption.
  - intros [acquired [restored [unlocked [[Hrun [entered [saved [Hsave Hrestore]]]] Htail]]]].
    exists (entered, saved), acquired; split; [exact Hsave|].
    exists (os_sched_unlock_requests acquired), (os_sched_unlock_checkpoint true acquired).
    split; [split; reflexivity|]. exists restored, unlocked; split; assumption.
Qed.

Lemma os_sched_unlock_positive_requests_after_decrement : forall acquired,
  os_sched_ints acquired = 0 -> 0 < os_sched_locks acquired ->
  (os_sched_unlock_requests acquired = true <-> os_sched_unlock_counted_locks acquired = 0).
Proof.
  intros acquired Hints Hpositive.
  rewrite (os_sched_unlock_positive_counted_locks acquired Hints Hpositive).
  unfold os_sched_unlock_requests; rewrite sched_unlock_requests_schedule_iff.
  unfold os_sched_ints, os_sched_locks in *; lia.
Qed.

Lemma os_sched_unlock_isr_count : forall acquired,
  os_sched_ints acquired <> 0 ->
  os_sched_unlock_counted_locks acquired = os_sched_locks acquired /\
  os_sched_unlock_requests acquired = false.
Proof.
  intros acquired Hints.
  unfold os_sched_unlock_counted_locks, os_sched_unlock_requests, os_sched_ints,
    os_sched_locks, sched_unlock_state, sched_unlock_requests_schedule in *.
  rewrite (proj2 (Z.eqb_neq _ _) Hints); cbn; split; reflexivity.
Qed.

Lemma os_sched_unlock_zero_count : forall acquired,
  os_sched_locks acquired = 0 ->
  os_sched_unlock_counted_locks acquired = 0 /\ os_sched_unlock_requests acquired = false.
Proof.
  intros acquired Hlocks.
  unfold os_sched_unlock_counted_locks, os_sched_unlock_requests, os_sched_locks,
    sched_unlock_state, sched_unlock_requests_schedule in *.
  rewrite Hlocks; destruct (acquired.(IntrState).(intNesting) =? 0); cbn;
    rewrite ?Hlocks; split; reflexivity.
Qed.

Lemma os_sched_unlock_saturated_count : forall acquired,
  os_sched_ints acquired = 0 -> os_sched_locks acquired = 255 ->
  os_sched_unlock_counted_locks acquired = 254 /\ os_sched_unlock_requests acquired = false.
Proof.
  intros acquired Hints Hlocks.
  unfold os_sched_unlock_counted_locks, os_sched_unlock_requests, os_sched_ints,
    os_sched_locks, sched_unlock_state, sched_unlock_requests_schedule in *.
  rewrite Hints, Hlocks; split; reflexivity.
Qed.

Definition os_sched_unlock_continuation_safe environment critical sg original mask before
  (X : OsSchedCallContext -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun observed => observed = before)
    (os_sched_unlock_continuation_program environment critical sg original mask) X.

Lemma os_sched_unlock_continuation_safeexec_return : forall environment critical sg original mask
  before returned current X,
  os_sched_unlock_continuation_history environment critical sg original mask before returned current ->
  os_sched_unlock_continuation_safe environment critical sg original mask before X ->
  safeExec (fun observed => observed = current) (StateRelMonad.ret returned) X.
Proof.
  intros environment critical sg original mask before returned current X Hhistory Hsafe.
  eapply (highstependret_derive
    (os_sched_unlock_continuation_program environment critical sg original mask)
    (fun observed => observed = before) returned (fun _ observed => observed = current)).
  - intros observed Hobserved; subst observed; exists current; split; [|reflexivity].
    apply os_sched_unlock_continuation_program_iff; exact Hhistory.
  - exact Hsafe.
Qed.

(** Source-prefix consumption at the actual Restore return, for arbitrary
    SAME X. This is the continuation handed to the real Scheduler call. *)
Lemma os_sched_unlock_prefix_safeexec_tail : forall environment critical sg original mask
  before acquired restored unlocked X,
  os_sched_unlock_continuation_prefix environment critical sg original mask
    before acquired restored unlocked ->
  os_sched_unlock_continuation_safe environment critical sg original mask before X ->
  safeExec (fun observed => observed = unlocked)
    (os_sched_unlock_tail_program environment critical sg mask
      (os_sched_unlock_requests acquired) restored) X.
Proof.
  intros environment critical sg original mask before acquired restored unlocked X Hprefix
    [observed [Hobserved Hsafe]]; subst observed.
  exists unlocked; split; [reflexivity|]. intros returned current Htail.
  apply (Hsafe returned current).
  apply os_sched_unlock_continuation_program_iff.
  unfold os_sched_unlock_continuation_history; rewrite (proj1 Hprefix).
  exists acquired, restored, unlocked; split; assumption.
Qed.

Lemma os_sched_unlock_checkpoint_preserves_task_source : forall call acquired,
  kernel_call_task_source call acquired ->
  kernel_call_task_source call (os_sched_unlock_checkpoint true acquired).
Proof. intros; exact H. Qed.

Lemma os_sched_unlock_checkpoint_normal_return : forall call acquired,
  kernel_call_normal_return call acquired call (os_sched_unlock_checkpoint true acquired).
Proof.
  intros; split; [unfold task_tcb_init_stack_same_call; auto|].
  unfold kernel_call_stack_available; destruct (os_sched_call_origin call); auto.
Qed.

Definition os_sched_unlock_continuation_control before current : Prop :=
  current.(SchedState).(isRunning) = before.(SchedState).(isRunning) /\
  current.(IntrState) = sched_unlock_state before.(SchedState).(isRunning) before.(IntrState).

Lemma os_sched_unlock_continuation_control_running : forall sg before acquired unlocked,
  before.(SchedState).(isRunning) = true ->
  kernel_call_control_rely sg before acquired ->
  kernel_call_control_rely sg (os_sched_unlock_checkpoint true acquired) unlocked ->
  os_sched_unlock_continuation_control before unlocked.
Proof.
  intros sg before acquired unlocked Hrunning [Hrun Hints] [Hrun' Hints'].
  unfold os_sched_unlock_continuation_control.
  cbn [os_sched_unlock_checkpoint replace_IntrS SchedState IntrState] in Hrun', Hints'.
  rewrite Hrunning; split; [congruence|]. rewrite Hints', Hints; reflexivity.
Qed.

Lemma os_sched_unlock_continuation_control_sched : forall sg before unlocked current,
  os_sched_unlock_continuation_control before unlocked ->
  kernel_call_control_rely sg unlocked current ->
  os_sched_unlock_continuation_control before current.
Proof. intros sg before unlocked current [Hr Hi] [Hr' Hi']; split; congruence. Qed.

Lemma os_sched_unlock_continuation_control_not_running : forall before,
  before.(SchedState).(isRunning) = false -> os_sched_unlock_continuation_control before before.
Proof.
  intros before Hrunning; unfold os_sched_unlock_continuation_control.
  rewrite Hrunning; split; reflexivity.
Qed.
