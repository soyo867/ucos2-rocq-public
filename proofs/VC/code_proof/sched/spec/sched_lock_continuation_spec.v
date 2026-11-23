Require Import Coq.ZArith.ZArith Coq.Bool.Bool.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Export Ucos2Verify.VC.code.sched.spec.sched_lock_call_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_lock_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.

Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSSchedLock's original C body.  OSRunning is observed before Save;
    only the acquired interrupt counters are changed.  Restore returns
    its own current state, which is not identified with the checkpoint.
    The result is the returned execution descriptor used to own the
    continuation.  It is ghost information, not a new C return value. *)
Definition os_sched_lock_checkpoint_program :
  StateRelMonad.M UCOS2_Verify_State unit :=
  fun entry result released =>
    result = tt /\ released = os_sched_lock_checkpoint true entry.

Definition os_sched_lock_continuation_program environment critical sg original mask :
  StateRelMonad.M UCOS2_Verify_State OsSchedCallContext :=
  fun before =>
    if before.(SchedState).(isRunning) then
      (StateRelMonad.bind
        (os_sched_continuation_save_program environment critical sg original mask)
        (fun entered => StateRelMonad.bind os_sched_lock_checkpoint_program
          (fun _ => os_sched_continuation_restore_program environment critical sg
            (fst entered)))) before
    else StateRelMonad.ret original before.

Definition os_sched_lock_continuation_history environment critical sg original mask
  before returned current : Prop :=
  if before.(SchedState).(isRunning) then
    exists entered acquired saved,
      os_sched_continuation_save_effect environment critical sg
        original mask saved before entered acquired /\
      os_sched_continuation_restore_effect environment critical sg entered
        (os_sched_lock_checkpoint true acquired) returned current
  else returned = original /\ before = current.

Lemma os_sched_lock_continuation_program_iff : forall environment critical sg
  original mask before returned current,
  os_sched_lock_continuation_program environment critical sg original mask
    before returned current <->
  os_sched_lock_continuation_history environment critical sg original mask
    before returned current.
Proof.
  intros; unfold os_sched_lock_continuation_program,
    os_sched_lock_continuation_history.
  destruct before.(SchedState).(isRunning).
  - unfold StateRelMonad.bind, os_sched_continuation_save_program,
      os_sched_lock_checkpoint_program, os_sched_continuation_restore_program.
    split.
    + intros [[entered saved] [acquired [Hsave [result [released [[Hresult Hreleased] Hrestore]]]]]].
      subst released; exists entered, acquired, saved; exact (conj Hsave Hrestore).
    + intros [entered [acquired [saved [Hsave Hrestore]]]].
      exists (entered, saved), acquired; split; [exact Hsave|].
      exists tt, (os_sched_lock_checkpoint true acquired).
      split; [split; reflexivity|exact Hrestore].
  - reflexivity.
Qed.

Lemma os_sched_lock_continuation_history_same_call : forall environment critical sg
  original mask before returned current,
  os_sched_lock_continuation_history environment critical sg original mask
    before returned current ->
  task_tcb_init_stack_same_call returned original.
Proof.
  intros environment critical sg original mask before returned current Hhistory.
  unfold os_sched_lock_continuation_history in Hhistory.
  destruct before.(SchedState).(isRunning).
  - destruct Hhistory as [entered [acquired [saved [Hsave Hrestore]]]].
    pose proof (os_sched_continuation_save_effect_same_call
      _ _ _ _ _ _ _ _ _ Hsave) as Hfirst.
    pose proof (os_sched_continuation_restore_effect_same_call
      _ _ _ _ _ _ _ Hrestore) as Hlast.
    unfold task_tcb_init_stack_same_call in *; intuition congruence.
  - destruct Hhistory as [-> _]; unfold task_tcb_init_stack_same_call; auto.
Qed.

Definition os_sched_lock_continuation_safe environment critical sg original mask before
  (X : OsSchedCallContext -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun observed => observed = before)
    (os_sched_lock_continuation_program environment critical sg original mask) X.

Lemma os_sched_lock_continuation_safeexec_return : forall environment critical sg
  original mask before returned current X,
  os_sched_lock_continuation_history environment critical sg original mask
    before returned current ->
  os_sched_lock_continuation_safe environment critical sg original mask before X ->
  safeExec (fun observed => observed = current) (StateRelMonad.ret returned) X.
Proof.
  intros environment critical sg original mask before returned current X Hhistory Hsafe.
  eapply (highstependret_derive
    (os_sched_lock_continuation_program environment critical sg original mask)
    (fun observed => observed = before) returned (fun _ observed => observed = current)).
  - intros observed Hobserved; subst observed; exists current; split; [|reflexivity].
    apply os_sched_lock_continuation_program_iff; exact Hhistory.
  - exact Hsafe.
Qed.

(** These two transports apply only to the literal counter checkpoint.
    They assert no task-map equality across Save or Restore. *)
Lemma os_sched_lock_checkpoint_preserves_task_source : forall call entry,
  kernel_call_task_source call entry ->
  kernel_call_task_source call (os_sched_lock_checkpoint true entry).
Proof. intros call entry Hsource; exact Hsource. Qed.

Lemma os_sched_lock_checkpoint_normal_return : forall call entry,
  kernel_call_normal_return call entry call (os_sched_lock_checkpoint true entry).
Proof.
  intros; split.
  - unfold task_tcb_init_stack_same_call; auto.
  - unfold kernel_call_stack_available; destruct (os_sched_call_origin call); auto.
Qed.

(** The registered C environment preserves control across each primitive
    normal return.  The Lock operation itself performs the exact counter
    update.  No whole-state frame or future-ready condition is present. *)
Definition os_sched_lock_continuation_control before current : Prop :=
  current.(SchedState).(isRunning) = before.(SchedState).(isRunning) /\
  current.(IntrState) = sched_lock_state before.(SchedState).(isRunning) before.(IntrState).

Lemma os_sched_lock_continuation_control_running : forall sg before acquired current,
  before.(SchedState).(isRunning) = true ->
  kernel_call_control_rely sg before acquired ->
  kernel_call_control_rely sg (os_sched_lock_checkpoint true acquired) current ->
  os_sched_lock_continuation_control before current.
Proof.
  intros sg before acquired current Hrunning [Hrun Hints] [Hrun' Hints'].
  unfold os_sched_lock_continuation_control.
  cbn [os_sched_lock_checkpoint replace_IntrS SchedState IntrState] in Hrun', Hints'.
  rewrite Hrunning; split; [congruence|]. rewrite Hints' , Hints; reflexivity.
Qed.

Lemma os_sched_lock_continuation_control_not_running : forall before,
  before.(SchedState).(isRunning) = false ->
  os_sched_lock_continuation_control before before.
Proof.
  intros before Hrunning; unfold os_sched_lock_continuation_control.
  rewrite Hrunning; split; [reflexivity|].
  unfold sched_lock_state; reflexivity.
Qed.
