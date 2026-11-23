Require Import Coq.ZArith.ZArith.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_local_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_counter_entry_spec.
Local Open Scope Z_scope.

Module FlagPendCallerControl.
Import PrimitiveComponent PendPhaseCandidate FlagPendLocalControl FlagPendCounterEntry.

Definition flag_pend_caller_counters_zero caller state : Prop :=
  match caller with
  | FlagPendTaskCaller call => call.(os_sched_call_origin) <> BootInvocation ->
      os_sched_ints state = 0 /\ os_sched_locks state = 0
  | FlagPendInterruptCaller _ _ => True
  end.

Lemma flag_pend_caller_counters_zero_from_counters : forall caller state,
  os_sched_ints state = 0 -> os_sched_locks state = 0 ->
  flag_pend_caller_counters_zero caller state.
Proof. intros caller state Hints Hlocks; destruct caller; cbn [flag_pend_caller_counters_zero]; auto. Qed.

Lemma flag_pend_caller_counters_zero_boot : forall call state,
  call.(os_sched_call_origin) = BootInvocation ->
  flag_pend_caller_counters_zero (FlagPendTaskCaller call) state.
Proof. intros call state Hboot; cbn [flag_pend_caller_counters_zero]; tauto. Qed.

Lemma flag_pend_caller_counters_zero_task_source : forall call state,
  kernel_call_task_source call state ->
  flag_pend_caller_counters_zero (FlagPendTaskCaller call) state ->
  os_sched_ints state = 0 /\ os_sched_locks state = 0.
Proof. intros call state [Horigin _] Hzero; apply Hzero; rewrite Horigin; discriminate. Qed.

Lemma flag_pend_caller_counters_zero_intr_state_eq : forall caller before after,
  before.(IntrState) = after.(IntrState) ->
  flag_pend_caller_counters_zero caller before -> flag_pend_caller_counters_zero caller after.
Proof.
  intros caller before after Hstate Hzero; destruct caller; [|exact I].
  intros Horigin; specialize (Hzero Horigin).
  unfold os_sched_ints, os_sched_locks in *; rewrite <- Hstate; exact Hzero.
Qed.

Lemma flag_pend_first_critical_caller_counters_zero : forall sg i requested mode delay caller before result after,
  flag_pend_first_critical sg i requested mode delay before result after ->
  flag_pend_caller_counters_zero caller before -> flag_pend_caller_counters_zero caller after.
Proof.
  intros sg i requested mode delay caller before result after Hstep Hzero.
  destruct (flag_pend_first_critical_preserves_control _ _ _ _ _ _ _ _ Hstep) as [_ Hstate].
  eapply flag_pend_caller_counters_zero_intr_state_eq; [symmetry; exact Hstate|exact Hzero].
Qed.

Lemma flag_pend_resume_critical_caller_counters_zero : forall sg i node mode caller before result after,
  flag_pend_resume_critical sg i node mode before result after ->
  flag_pend_caller_counters_zero caller before -> flag_pend_caller_counters_zero caller after.
Proof.
  intros sg i node mode caller before result after Hstep Hzero.
  destruct (flag_pend_resume_critical_preserves_control _ _ _ _ _ _ _ Hstep) as [_ Hstate].
  eapply flag_pend_caller_counters_zero_intr_state_eq; [symmetry; exact Hstate|exact Hzero].
Qed.

Lemma flag_pend_caller_counters_zero_same_call : forall original returned before current,
  task_tcb_init_stack_same_call returned original ->
  flag_pend_caller_return_control original before returned current ->
  flag_pend_caller_counters_zero (FlagPendTaskCaller original) before ->
  flag_pend_caller_counters_zero (FlagPendTaskCaller returned) current.
Proof.
  intros original returned before current Hsame Hcontrol Hzero Hreturned.
  assert (Horigin : original.(os_sched_call_origin) <> BootInvocation).
  { rewrite <- (proj1 (proj2 Hsame)); exact Hreturned. }
  destruct (Hzero Horigin) as [Hints Hlocks].
  pose proof (flag_pend_caller_return_control_running_origin _ _ _ _ Horigin Hcontrol) as Htask.
  exact (flag_pend_return_control_counters_zero _ _ _ _ Htask Hints Hlocks).
Qed.

Lemma flag_pend_caller_save_counters_zero : forall environment critical sg caller original
  returned_caller returned mask saved before acquired,
  flag_pend_caller_save_observation environment critical sg caller original returned_caller
    returned mask saved before acquired ->
  flag_pend_call_source_observations environment sg caller original before returned acquired ->
  flag_pend_caller_counters_zero caller before ->
  flag_pend_caller_counters_zero returned_caller acquired.
Proof.
  intros environment critical sg caller original returned_caller returned mask saved before acquired Hsave Hsource Hzero.
  destruct caller, returned_caller; cbn [flag_pend_caller_save_observation] in Hsave; try contradiction.
  - destruct Hsave as [Hactual [Hnext [_ [Hsame _]]]]; subst.
    destruct Hsource as [_ [_ [_ Hcontrol]]].
    eapply flag_pend_caller_counters_zero_same_call; eassumption.
  - exact I.
Qed.

Lemma flag_pend_caller_restore_counters_zero : forall environment critical sg caller original
  returned_caller returned released current,
  flag_pend_caller_restore_observation environment critical sg caller original returned_caller
    returned released current ->
  flag_pend_call_source_observations environment sg caller original released returned current ->
  flag_pend_caller_counters_zero caller released ->
  flag_pend_caller_counters_zero returned_caller current.
Proof.
  intros environment critical sg caller original returned_caller returned released current Hrestore Hsource Hzero.
  destruct caller, returned_caller; cbn [flag_pend_caller_restore_observation] in Hrestore; try contradiction.
  - destruct Hrestore as [Hactual [Hnext [_ [Hsame _]]]]; subst.
    destruct Hsource as [_ [_ [_ Hcontrol]]].
    eapply flag_pend_caller_counters_zero_same_call; eassumption.
  - exact I.
Qed.

End FlagPendCallerControl.
