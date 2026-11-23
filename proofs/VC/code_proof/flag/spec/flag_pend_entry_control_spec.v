Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_protocol_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagPendEntryControl.
Import PrimitiveComponent PendPhaseCandidate FlagPendActiveProtocol.

(** The concrete local family and the Running fact at this actual C call.
    First-observation keeps its original conditional domain, including Boot
    and invalid-mode entries. No constructor constrains a future execution. *)
Inductive flag_pend_active_entry (sg : StableGlobVars) :
  (OsSchedCallContext -> UCOS2_Verify_State -> Assertion) ->
  UCOS2_Verify_State -> Prop :=
| FlagPendEntryFirst : forall mode original initial state,
    ((flag_pend_valid_mode mode \/ flag_pend_task_entry original initial) ->
      state.(SchedState).(isRunning) = true) ->
    flag_pend_active_entry sg
      (flag_pend_first_observation mode original initial) state
| FlagPendEntryWaiting : forall original node state,
    state.(SchedState).(isRunning) = true ->
    flag_pend_active_entry sg (flag_pend_wait_active sg original node) state
| FlagPendEntryFresh : forall original state,
    state.(SchedState).(isRunning) = true ->
    flag_pend_active_entry sg (flag_pend_fresh_observation original) state.

Lemma flag_pend_active_entry_protocol : forall sg active state,
  flag_pend_active_entry sg active state -> flag_pend_active_protocol sg active.
Proof. intros sg active state Hentry; destruct Hentry; constructor. Qed.

Lemma flag_pend_running_protocol_entry : forall sg active state,
  flag_pend_active_protocol sg active -> state.(SchedState).(isRunning) = true ->
  flag_pend_active_entry sg active state.
Proof.
  intros sg active state Hprotocol Hrunning; destruct Hprotocol.
  - apply FlagPendEntryFirst; intros; exact Hrunning.
  - apply FlagPendEntryWaiting; exact Hrunning.
  - apply FlagPendEntryFresh; exact Hrunning.
Qed.

Lemma flag_pend_initial_entry_control : forall sg caller call i pgrp mode state image,
  flag_pend_caller_source sg caller call i pgrp mode state ->
  pgrp <> 0 -> state.(IntrState).(intNesting) <= 0 ->
  state.(IntrState).(lockNesting) <= 0 ->
  flag_pend_group_lookup state i image -> flag_pend_group_type image = 5 ->
  flag_pend_active_entry sg (flag_pend_first_observation mode call state) state.
Proof.
  intros sg caller call i pgrp mode state image Hsource Hgroup Hints Hlocks Hlookup Htype.
  apply FlagPendEntryFirst; intros [Hmode|Hentry].
  - destruct caller as [task_call|view active].
    + destruct Hsource as [Heq Hdomain].
      destruct (Hdomain Hgroup Hints Hlocks image Hlookup Htype Hmode)
        as [[[Horigin [Hrunning Hstage]] Hactive] Hrest].
      exact Hrunning.
    + destruct Hsource as [Hinterrupt Hdomain].
      exact (False_ind _ (Hdomain Hgroup Hints Hlocks image Hlookup Htype Hmode)).
  - destruct Hentry as [[Horigin [Hrunning Hstage]] Hactive]; exact Hrunning.
Qed.

Lemma flag_pend_public_initial_entry_control : forall environment critical sg caller call mask
  i pgrp requested mode delay state X image,
  flag_pend_public_entry environment critical sg caller call mask i pgrp requested mode delay state X ->
  pgrp <> 0 -> state.(IntrState).(intNesting) <= 0 ->
  state.(IntrState).(lockNesting) <= 0 ->
  flag_pend_group_lookup state i image -> flag_pend_group_type image = 5 ->
  flag_pend_active_entry sg (flag_pend_first_observation mode call state) state.
Proof.
  intros environment critical sg caller call mask i pgrp requested mode delay state X image
    [_ [_ [_ [_ [_ [Hsource Hsafe]]]]]] Hgroup Hints Hlocks Hlookup Htype.
  eapply flag_pend_initial_entry_control; eassumption.
Qed.

Lemma flag_pend_waiting_entry_control : forall sg original node call state,
  flag_pend_running_available call state ->
  flag_pend_active_entry sg (flag_pend_wait_active sg original node) state.
Proof. intros sg original node call state [Hrunning Havailable]; constructor; exact Hrunning. Qed.

Lemma flag_pend_fresh_stage_entry_control : forall sg original call state,
  flag_pend_task_stage call state ->
  flag_pend_active_entry sg (flag_pend_fresh_observation original) state.
Proof.
  intros sg original call state [Horigin [Hrunning Hstage]].
  apply FlagPendEntryFresh; exact Hrunning.
Qed.

Lemma flag_pend_active_entry_running_transport : forall sg active before after,
  (before.(SchedState).(isRunning) = true -> after.(SchedState).(isRunning) = true) ->
  flag_pend_active_entry sg active before -> flag_pend_active_entry sg active after.
Proof.
  intros sg active before after Hrunning Hentry; destruct Hentry.
  - apply FlagPendEntryFirst; intros Hcondition; apply Hrunning, H; exact Hcondition.
  - apply FlagPendEntryWaiting; apply Hrunning; exact H.
  - apply FlagPendEntryFresh; apply Hrunning; exact H.
Qed.

Lemma flag_pend_active_entry_return_control : forall sg active original before returned after,
  flag_pend_call_return_control original before returned after ->
  flag_pend_active_entry sg active before -> flag_pend_active_entry sg active after.
Proof.
  intros sg active original before returned after [Hnormal [Hrunning Hints]] Hentry.
  eapply flag_pend_active_entry_running_transport; eassumption.
Qed.

Lemma flag_pend_boot_invalid_entry_control : forall sg mode original initial state,
  ~ flag_pend_valid_mode mode -> original.(os_sched_call_origin) = BootInvocation ->
  flag_pend_active_entry sg (flag_pend_first_observation mode original initial) state.
Proof.
  intros sg mode original initial state Hinvalid Hboot.
  apply FlagPendEntryFirst; intros [Hvalid|[[Horigin Hstage] Hactive]].
  - contradiction.
  - rewrite Hboot in Horigin; discriminate.
Qed.

End FlagPendEntryControl.
