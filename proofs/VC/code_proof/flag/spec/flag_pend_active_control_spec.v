Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.FunctionalExtensionality Coq.Logic.PropExtensionality.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_entry_control_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef PendPhaseCandidate.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagPendActiveControl.

Lemma flag_active_task_fields_not_boot : forall reference call state task,
  flag_active_task_fields reference call state task ->
  call.(os_sched_call_origin) <> BootInvocation.
Proof.
  intros reference call state task [Hsame [Horigin Hrest]].
  destruct Hsame as [Hinv [Hcall_origin Hstack]].
  rewrite Hcall_origin, Horigin; discriminate.
Qed.

(** A Boot descriptor is used only to test equality of two assertion-valued
    functions. It is not a constructed execution or an extra caller premise. *)
Lemma flag_pend_fresh_observation_not_emp :
  forall reference (state : UCOS2_Verify_State),
  flag_pend_fresh_observation reference <> (fun _ _ => emp).
Proof.
  intros reference state Heq.
  set (probe := {| os_sched_call_invocation := reference.(os_sched_call_invocation);
                  os_sched_call_origin := BootInvocation;
                  os_sched_call_stack := reference.(os_sched_call_stack);
                  os_sched_call_fragments := reference.(os_sched_call_fragments) |}).
  assert (Hemp : emp (empty_state : model)).
  { apply empty_state_is_empty. }
  assert (Hactive : flag_pend_fresh_observation reference probe state (empty_state : model)).
  { rewrite Heq; exact Hemp. }
  destruct Hactive as [[task [Htask Hnode]] Hempty].
  exact ((flag_active_task_fields_not_boot reference probe state task Htask) eq_refl).
Qed.

Lemma flag_pend_wait_active_not_emp :
  forall sg reference node (state : UCOS2_Verify_State),
  flag_pend_wait_active sg reference node <> (fun _ _ => emp).
Proof.
  intros sg reference node state Heq.
  set (probe := {| os_sched_call_invocation := reference.(os_sched_call_invocation);
                  os_sched_call_origin := BootInvocation;
                  os_sched_call_stack := reference.(os_sched_call_stack);
                  os_sched_call_fragments := reference.(os_sched_call_fragments) |}).
  assert (Hemp : emp (empty_state : model)).
  { apply empty_state_is_empty. }
  assert (Hactive : flag_pend_wait_active sg reference node probe state (empty_state : model)).
  { rewrite Heq; exact Hemp. }
  destruct Hactive as [Houtcome [[task [Htask Hwaiting]] Hnode]].
  exact ((flag_active_task_fields_not_boot reference probe state task Htask) eq_refl).
Qed.

Lemma flag_pend_first_observation_not_emp : forall mode reference initial,
  (flag_pend_valid_mode mode \/ flag_pend_task_entry reference initial) ->
  flag_pend_first_observation mode reference initial <> (fun _ _ => emp).
Proof.
  intros mode reference initial Hcondition Heq.
  set (probe := {| os_sched_call_invocation := reference.(os_sched_call_invocation);
                  os_sched_call_origin := BootInvocation;
                  os_sched_call_stack := reference.(os_sched_call_stack);
                  os_sched_call_fragments := reference.(os_sched_call_fragments) |}).
  assert (Hemp : emp (empty_state : model)).
  { apply empty_state_is_empty. }
  assert (Hactive : flag_pend_first_observation mode reference initial
    probe initial (empty_state : model)).
  { rewrite Heq; exact Hemp. }
  destruct Hactive as [Hregistration Hempty].
  destruct (Hregistration Hcondition) as [task [Htask Hnode]].
  exact ((flag_active_task_fields_not_boot reference probe initial task Htask) eq_refl).
Qed.

(** This is the existing inactive-observation equality, with no Boot premise. *)
Lemma flag_pend_first_observation_inactive_eq : forall mode reference initial,
  ~ (flag_pend_valid_mode mode \/ flag_pend_task_entry reference initial) ->
  flag_pend_first_observation mode reference initial = (fun _ _ => emp).
Proof.
  intros mode reference initial Hfalse.
  apply functional_extensionality; intro call.
  apply functional_extensionality; intro state.
  apply functional_extensionality; intro heap.
  apply propositional_extensionality.
  change ((flag_pend_first_registration mode reference initial call state /\ emp heap) <-> emp heap).
  unfold flag_pend_first_registration; tauto.
Qed.

Lemma flag_pend_first_observation_inactive_control : forall mode reference initial,
  ~ (flag_pend_valid_mode mode \/ flag_pend_task_entry reference initial) ->
  ~ (flag_pend_first_observation mode reference initial <> (fun _ _ => emp)).
Proof.
  intros mode reference initial Hfalse Hnonemp.
  apply Hnonemp; apply flag_pend_first_observation_inactive_eq; exact Hfalse.
Qed.

(** The already carried entry packet provides Running only when this same
    active family demands control. No conclusion about a future state is used. *)
Lemma flag_pend_active_entry_not_emp_running : forall sg active state,
  FlagPendEntryControl.flag_pend_active_entry sg active state ->
  active <> (fun _ _ => emp) ->
  state.(SchedState).(isRunning) = true.
Proof.
  intros sg active state Hentry Hnonemp.
  destruct Hentry as [mode reference initial state Hrunning
                    |reference node state Hrunning
                    |reference state Hrunning].
  - destruct state.(SchedState).(isRunning) eqn:Hstate.
    + reflexivity.
    + exfalso; apply Hnonemp.
      apply flag_pend_first_observation_inactive_eq.
      intros Hcondition; specialize (Hrunning Hcondition); congruence.
  - exact Hrunning.
  - exact Hrunning.
Qed.

End FlagPendActiveControl.

