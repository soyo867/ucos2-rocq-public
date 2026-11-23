Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_caller_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_selected_call_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef PendPhaseCandidate.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagPendActiveCallerControl.

(** A readable C-annotation name for the same function inequality. *)
Definition flag_pend_active_requires_control
  (active : OsSchedCallContext -> UCOS2_Verify_State -> Assertion) : Prop :=
  active <> (fun _ _ => emp).

(** This is the same active argument used by the real Save/Restore owner.
    The existing Boot-origin and InterruptCaller cases remain in the old
    predicate; inactive First additionally has no counter requirement. *)
Definition flag_pend_caller_counters_zero
  (active : OsSchedCallContext -> UCOS2_Verify_State -> Assertion)
  caller state : Prop :=
  flag_pend_active_requires_control active ->
  FlagPendCallerControl.flag_pend_caller_counters_zero caller state.

(** The initial C guards and the concrete unsigned-byte owners supply these
    two equalities. The same bridge also serves the enabled Scheduler calls. *)
Lemma flag_pend_caller_counters_zero_from_counters : forall active caller state,
  os_sched_ints state = 0 -> os_sched_locks state = 0 ->
  flag_pend_caller_counters_zero active caller state.
Proof.
  intros active caller state Hints Hlocks Hnonempty.
  eapply FlagPendCallerControl.flag_pend_caller_counters_zero_from_counters; eassumption.
Qed.

Lemma flag_pend_caller_counters_zero_nonempty : forall active caller state,
  active <> (fun _ _ => emp) ->
  flag_pend_caller_counters_zero active caller state ->
  FlagPendCallerControl.flag_pend_caller_counters_zero caller state.
Proof. intros active caller state Hnonempty Hzero; exact (Hzero Hnonempty). Qed.

Lemma flag_pend_first_inactive_counters_zero : forall mode reference initial caller state,
  ~ (flag_pend_valid_mode mode \/ flag_pend_task_entry reference initial) ->
  flag_pend_caller_counters_zero
    (flag_pend_first_observation mode reference initial) caller state.
Proof.
  intros mode reference initial caller state Hfalse Hnonempty.
  exfalso; exact (FlagPendActiveControl.flag_pend_first_observation_inactive_control
    mode reference initial Hfalse Hnonempty).
Qed.

Lemma flag_pend_fresh_counters_zero : forall reference caller state,
  flag_pend_caller_counters_zero (flag_pend_fresh_observation reference) caller state ->
  FlagPendCallerControl.flag_pend_caller_counters_zero caller state.
Proof.
  intros reference caller state Hzero.
  exact (Hzero (FlagPendActiveControl.flag_pend_fresh_observation_not_emp reference state)).
Qed.

Lemma flag_pend_wait_counters_zero : forall sg reference node caller state,
  flag_pend_caller_counters_zero (flag_pend_wait_active sg reference node) caller state ->
  FlagPendCallerControl.flag_pend_caller_counters_zero caller state.
Proof.
  intros sg reference node caller state Hzero.
  exact (Hzero (FlagPendActiveControl.flag_pend_wait_active_not_emp sg reference node state)).
Qed.

Lemma flag_pend_first_active_counters_zero : forall mode reference initial caller state,
  (flag_pend_valid_mode mode \/ flag_pend_task_entry reference initial) ->
  flag_pend_caller_counters_zero
    (flag_pend_first_observation mode reference initial) caller state ->
  FlagPendCallerControl.flag_pend_caller_counters_zero caller state.
Proof.
  intros mode reference initial caller state Hcondition Hzero.
  exact (Hzero (FlagPendActiveControl.flag_pend_first_observation_not_emp
    mode reference initial Hcondition)).
Qed.

Lemma flag_pend_first_critical_caller_counters_zero :
  forall sg i requested mode delay active caller before result after,
  flag_pend_first_critical sg i requested mode delay before result after ->
  flag_pend_caller_counters_zero active caller before ->
  flag_pend_caller_counters_zero active caller after.
Proof.
  intros sg i requested mode delay active caller before result after Hstep Hzero Hnonempty.
  eapply FlagPendCallerControl.flag_pend_first_critical_caller_counters_zero.
  - exact Hstep.
  - exact (Hzero Hnonempty).
Qed.

Lemma flag_pend_resume_critical_caller_counters_zero :
  forall sg i node mode active caller before result after,
  flag_pend_resume_critical sg i node mode before result after ->
  flag_pend_caller_counters_zero active caller before ->
  flag_pend_caller_counters_zero active caller after.
Proof.
  intros sg i node mode active caller before result after Hstep Hzero Hnonempty.
  eapply FlagPendCallerControl.flag_pend_resume_critical_caller_counters_zero.
  - exact Hstep.
  - exact (Hzero Hnonempty).
Qed.

(** These two transport lemmas consume the observation and endpoint produced
    together by the new output_open. Inactive completion needs neither normal
    return nor IntrState equality: the same active condition remains false. *)
Lemma flag_pend_caller_save_counters_zero :
  forall environment critical active sg caller original returned_caller returned
    mask saved before acquired,
  FlagPendActiveCaller.flag_pend_caller_save_observation environment critical active sg
    caller original returned_caller returned mask saved before acquired ->
  FlagPendActiveCaller.flag_pend_caller_endpoint_observations environment active sg
    caller original before returned acquired ->
  flag_pend_caller_counters_zero active caller before ->
  flag_pend_caller_counters_zero active returned_caller acquired.
Proof.
  intros environment critical active sg caller original returned_caller returned
    mask saved before acquired Hsave Hendpoint Hzero Hnonempty.
  pose proof (FlagPendActiveCaller.flag_pend_save_observation_nonempty
    environment critical active sg caller original returned_caller returned mask saved
    before acquired Hnonempty Hsave) as Hobs.
  specialize (Hendpoint Hnonempty).
  specialize (Hzero Hnonempty).
  destruct caller as [actual|view key], returned_caller as [next|next_view next_key];
    cbn [CompletedCallerEvents.flag_pend_caller_save_observation] in Hobs; try contradiction.
  - destruct Hobs as [Hactual [Hnext [Heffect [Hsame Hsource]]]].
    subst actual next.
    intros Hreturned.
    assert (Horiginal : original.(os_sched_call_origin) <> BootInvocation).
    { rewrite <- (proj1 (proj2 Hsame)); exact Hreturned. }
    destruct Hendpoint as [_ [_ [_ [_ Hcontrol]]]].
    destruct (Hcontrol Horiginal) as [Hrunning Hintr].
    unfold os_sched_ints, os_sched_locks; rewrite Hintr.
    exact (Hzero Horiginal).
  - exact I.
Qed.

Lemma flag_pend_caller_restore_counters_zero :
  forall environment critical active sg caller original returned_caller returned released current,
  FlagPendActiveCaller.flag_pend_caller_restore_observation environment critical active sg
    caller original returned_caller returned released current ->
  FlagPendActiveCaller.flag_pend_caller_endpoint_observations environment active sg
    caller original released returned current ->
  flag_pend_caller_counters_zero active caller released ->
  flag_pend_caller_counters_zero active returned_caller current.
Proof.
  intros environment critical active sg caller original returned_caller returned
    released current Hrestore Hendpoint Hzero Hnonempty.
  pose proof (FlagPendActiveCaller.flag_pend_restore_observation_nonempty
    environment critical active sg caller original returned_caller returned
    released current Hnonempty Hrestore) as Hobs.
  specialize (Hendpoint Hnonempty).
  specialize (Hzero Hnonempty).
  destruct caller as [actual|view key], returned_caller as [next|next_view next_key];
    cbn [CompletedCallerEvents.flag_pend_caller_restore_observation] in Hobs; try contradiction.
  - destruct Hobs as [Hactual [Hnext [Heffect [Hsame Hsource]]]].
    subst actual next.
    intros Hreturned.
    assert (Horiginal : original.(os_sched_call_origin) <> BootInvocation).
    { rewrite <- (proj1 (proj2 Hsame)); exact Hreturned. }
    destruct Hendpoint as [_ [_ [_ [_ Hcontrol]]]].
    destruct (Hcontrol Horiginal) as [Hrunning Hintr].
    unfold os_sched_ints, os_sched_locks; rewrite Hintr.
    exact (Hzero Horiginal).
  - exact I.
Qed.

End FlagPendActiveCallerControl.

