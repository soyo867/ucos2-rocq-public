Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_entry_control_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagPendLocalControl.
Import PrimitiveComponent PendPhaseCandidate FlagPendEntryControl.

(** These equalities follow the local C updates, including the real Block
    transformer. They do not constrain an interrupt or scheduler execution. *)
Lemma flag_pend_first_critical_preserves_control : forall sg i requested mode delay before result after,
  flag_pend_first_critical sg i requested mode delay before result after ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning) /\
  after.(IntrState) = before.(IntrState).
Proof.
  intros sg i requested mode delay before result after Hstep.
  unfold flag_pend_first_critical in Hstep.
  destruct (decode_flag_wait_mode (osKernelConfig sg) (Z.land mode 127)) as [decoded|].
  - destruct Hstep as [image [Hlookup Hstep]].
    destruct (negb (Z.eqb (flagImageType image) 5)).
    + destruct Hstep as [_ ->]; split; reflexivity.
    + destruct (flag_wait_satisfied decoded
        (flag_ready_bits (osKernelConfig sg) (flagImageBits image) requested decoded) requested).
      * destruct Hstep as [tid [old [_ [_ [_ ->]]]]].
        destruct (Z.testbit mode 7); split; reflexivity.
      * destruct Hstep as [waiter [old [group [blocked
          [_ [_ [_ [_ [Hblock [_ ->]]]]]]]]]].
        destruct (flag_block_result sg before waiter delay blocked Hblock)
          as [tid [task [flags [_ [_ [_ ->]]]]]].
        split; reflexivity.
  - destruct Hstep as [_ ->]; split; reflexivity.
Qed.

Lemma flag_pend_resume_critical_preserves_control : forall sg i node mode before result after,
  flag_pend_resume_critical sg i node mode before result after ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning) /\
  after.(IntrState) = before.(IntrState).
Proof.
  intros sg i node mode before result after [tid [old [Hcurrent [Hlookup Hstep]]]].
  cbv zeta in Hstep.
  destruct (negb (Z.eqb (encode_pend_status (statPend old)) 0)).
  - destruct Hstep as [_ Hstep].
    destruct (Z.eqb (encode_pend_status (statPend old)) 2).
    + subst after; split; reflexivity.
    + destruct Hstep as [waiter [flags [_ ->]]]; split; reflexivity.
  - destruct (Z.testbit mode 7).
    + destruct (decode_flag_wait_mode (osKernelConfig sg) (Z.land mode 127)).
      * destruct Hstep as [image [_ [_ ->]]]; split; reflexivity.
      * destruct Hstep as [_ ->]; split; reflexivity.
    + destruct Hstep as [_ ->]; split; reflexivity.
Qed.

Lemma flag_pend_first_critical_entry_transport : forall sg active i requested mode delay before result after,
  flag_pend_first_critical sg i requested mode delay before result after ->
  flag_pend_active_entry sg active before -> flag_pend_active_entry sg active after.
Proof.
  intros sg active i requested mode delay before result after Hstep Hentry.
  destruct (flag_pend_first_critical_preserves_control _ _ _ _ _ _ _ _ Hstep) as [Hrunning Hints].
  apply (flag_pend_active_entry_running_transport sg active before after);
    [intros Hbefore; rewrite Hrunning; exact Hbefore|exact Hentry].
Qed.

Lemma flag_pend_resume_critical_entry_transport : forall sg active i node mode before result after,
  flag_pend_resume_critical sg i node mode before result after ->
  flag_pend_active_entry sg active before -> flag_pend_active_entry sg active after.
Proof.
  intros sg active i node mode before result after Hstep Hentry.
  destruct (flag_pend_resume_critical_preserves_control _ _ _ _ _ _ _ Hstep) as [Hrunning Hints].
  apply (flag_pend_active_entry_running_transport sg active before after);
    [intros Hbefore; rewrite Hrunning; exact Hbefore|exact Hentry].
Qed.

Lemma flag_pend_source_first_task_running : forall sg caller original i pgrp mode initial image,
  flag_pend_caller_source sg caller original i pgrp mode initial ->
  pgrp <> 0 -> initial.(IntrState).(intNesting) <= 0 -> initial.(IntrState).(lockNesting) <= 0 ->
  flag_pend_group_lookup initial i image -> flag_pend_group_type image = 5 ->
  (flag_pend_valid_mode mode \/ flag_pend_task_entry original initial) ->
  caller = FlagPendTaskCaller original /\ initial.(SchedState).(isRunning) = true.
Proof.
  intros sg caller original i pgrp mode initial image Hsource Hgroup Hints Hlocks Hlookup Htype Hcondition.
  assert (Hrunning : initial.(SchedState).(isRunning) = true).
  { destruct Hcondition as [Hmode|[[Horigin [Hrunning Hstage]] Hactive]].
    - destruct caller as [task_call|view active].
      + destruct Hsource as [Heq Hdomain].
        destruct (Hdomain Hgroup Hints Hlocks image Hlookup Htype Hmode)
          as [[[Horigin [Hrunning Hstage]] Hactive] Hrest]; exact Hrunning.
      + destruct Hsource as [Hinterrupt Hdomain].
        exact (False_ind _ (Hdomain Hgroup Hints Hlocks image Hlookup Htype Hmode)).
    - exact Hrunning. }
  split; [eapply flag_pend_caller_source_task; eassumption|exact Hrunning].
Qed.

Lemma flag_pend_first_source_observations_entry : forall environment sg caller original i pgrp mode
  initial image returned current,
  flag_pend_caller_source sg caller original i pgrp mode initial ->
  pgrp <> 0 -> initial.(IntrState).(intNesting) <= 0 -> initial.(IntrState).(lockNesting) <= 0 ->
  flag_pend_group_lookup initial i image -> flag_pend_group_type image = 5 ->
  flag_pend_call_source_observations environment sg caller original initial returned current ->
  flag_pend_active_entry sg (flag_pend_first_observation mode original initial) current.
Proof.
  intros environment sg caller original i pgrp mode initial image returned current
    Hsource Hgroup Hints Hlocks Hlookup Htype Hobservations.
  apply FlagPendEntryFirst; intros Hcondition.
  destruct (flag_pend_source_first_task_running sg caller original i pgrp mode initial image
    Hsource Hgroup Hints Hlocks Hlookup Htype Hcondition) as [Hcaller Hrunning].
  subst caller.
  assert (Hentry : flag_pend_task_entry original initial).
  { destruct Hcondition as [Hmode|Hentry]; [|exact Hentry].
    exact (proj1 ((proj2 Hsource) Hgroup Hints Hlocks image Hlookup Htype Hmode)). }
  destruct Hobservations as [_ [_ [_ Hcontrol]]].
  pose proof (flag_pend_caller_return_control_task_source _ _ _ _
    (flag_pend_task_entry_call_source _ _ Hentry) Hcontrol) as [_ [Hreturn _]].
  exact (Hreturn Hrunning).
Qed.



End FlagPendLocalControl.
