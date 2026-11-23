(** High-level Boot adapters for the actual Pend First observation.
    The resource lemmas and completed-call adapters retain their checked modules.
    No low-level phase/source module imports this file. *)
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_boot_primitive_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_selected_call_spec.

Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality Coq.Logic.PropExtensionality.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagPendBootResources.
Import PrimitiveComponent PendPhaseCandidate.

Lemma flag_pend_boot_has_no_task_source : forall original state,
  original.(os_sched_call_origin) = BootInvocation ->
  ~ kernel_call_task_source original state.
Proof.
  intros original state Hboot [Horigin _].
  rewrite Hboot in Horigin; discriminate.
Qed.

Lemma flag_pend_boot_invalid_first_condition_false : forall mode original initial,
  original.(os_sched_call_origin) = BootInvocation ->
  ~ flag_pend_valid_mode mode ->
  ~ (flag_pend_valid_mode mode \/ flag_pend_task_entry original initial).
Proof.
  intros mode original initial Hboot Hinvalid [Hvalid|[Hsource Hactive]].
  - contradiction.
  - destruct Hsource as [Horigin _].
    rewrite Hboot in Horigin; discriminate.
Qed.

Lemma flag_pend_first_observation_inactive_eq : forall mode original initial,
  ~ (flag_pend_valid_mode mode \/ flag_pend_task_entry original initial) ->
  flag_pend_first_observation mode original initial = (fun _ _ => emp).
Proof.
  intros mode original initial Hfalse.
  apply functional_extensionality; intro call.
  apply functional_extensionality; intro state.
  apply functional_extensionality; intro heap.
  apply propositional_extensionality.
  change ((flag_pend_first_registration mode original initial call state /\ emp heap) <-> emp heap).
  unfold flag_pend_first_registration; tauto.
Qed.

Lemma flag_pend_boot_first_observation_eq : forall mode original initial,
  original.(os_sched_call_origin) = BootInvocation ->
  ~ flag_pend_valid_mode mode ->
  flag_pend_first_observation mode original initial = (fun _ _ => emp).
Proof.
  intros mode original initial Hboot Hinvalid.
  apply flag_pend_first_observation_inactive_eq.
  eapply flag_pend_boot_invalid_first_condition_false; eassumption.
Qed.

(** The equality is at every actual state and heap, so a changing kernel
    state does not require transporting a fictitious Task registration. *)
Lemma flag_pend_boot_first_save_input_eq :
  forall environment critical local sg caller call mask state mode original initial,
  original.(os_sched_call_origin) = BootInvocation ->
  ~ flag_pend_valid_mode mode ->
  flag_pend_caller_save_input environment critical local
    (flag_pend_first_observation mode original initial) sg caller call mask state =
  flag_pend_caller_save_input environment critical local
    (fun _ _ => emp) sg caller call mask state.
Proof.
  intros; rewrite (flag_pend_boot_first_observation_eq mode original initial H H0).
  reflexivity.
Qed.

Lemma flag_pend_boot_first_restore_input_eq :
  forall environment critical local sg caller call saved acquired state mode original initial,
  original.(os_sched_call_origin) = BootInvocation ->
  ~ flag_pend_valid_mode mode ->
  flag_pend_caller_restore_input environment critical local
    (flag_pend_first_observation mode original initial) sg caller call saved acquired state =
  flag_pend_caller_restore_input environment critical local
    (fun _ _ => emp) sg caller call saved acquired state.
Proof.
  intros; rewrite (flag_pend_boot_first_observation_eq mode original initial H H0).
  reflexivity.
Qed.

(** The Boot platform owner observes the physical execution view.  Its
    lease's Task slot and generation do not establish an executing TCB. *)
Lemma flag_pend_boot_save_owner_same_view :
  forall environment critical local sg original other mask state,
  original.(os_sched_call_origin) = BootInvocation ->
  other.(os_sched_call_origin) = BootInvocation ->
  os_sched_execution_view original = os_sched_execution_view other ->
  flag_pend_caller_save_input environment critical local (fun _ _ => emp) sg
    (FlagPendTaskCaller original) original mask state =
  flag_pend_caller_save_input environment critical local (fun _ _ => emp) sg
    (FlagPendTaskCaller other) other mask state.
Proof.
  intros environment critical local sg original other mask state Hboot Hother Hview.
  unfold flag_pend_caller_save_input, flag_pend_active_save_input,
    os_sched_fields_save_input, task_stack_call_active_key.
  rewrite Hboot, Hother.
  rewrite !kernel_call_execution_owned_view_eq, Hview.
  assert (Heq : (original = original) = (other = other)).
  { apply propositional_extensionality; tauto. }
  rewrite Heq; reflexivity.
Qed.

Lemma flag_pend_non_idle_absent_slot : forall sg call state,
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = None ->
  ~ flag_pend_non_idle_at sg call state.
Proof.
  intros sg call state Habsent [node [Hnode Hrest]]; congruence.
Qed.

End FlagPendBootResources.

Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagPendBootFirstCallers.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Import PrimitiveComponent PendPhaseCandidate FlagPendBootPrimitive.
Import CompletedCallerEvents CompletedBootCallerEvents FlagPendBootResources.

(** These are the guards already passed before the first Save. The public
    caller-domain implication rules out a valid waiting mode for Boot. *)
Lemma flag_pend_boot_guarded_call_invalid_mode :
  forall sg original initial i pgrp mode observed,
  original.(os_sched_call_origin) = BootInvocation ->
  flag_pend_caller_source sg (FlagPendTaskCaller original) original
    i pgrp mode initial ->
  pgrp <> 0 -> os_sched_ints initial <= 0 -> os_sched_locks initial <= 0 ->
  flag_pend_group_lookup initial i observed -> flag_pend_group_type observed = 5 ->
  ~ flag_pend_valid_mode mode.
Proof.
  intros sg original initial i pgrp mode observed Hboot Hcaller
    Hptr Hints Hlocks Hlookup Htype Hvalid.
  destruct Hcaller as [_ Hdomain].
  destruct (Hdomain Hptr Hints Hlocks observed Hlookup Htype Hvalid)
    as [Hentry Hrest].
  eapply (flag_pend_boot_has_no_task_source original initial Hboot).
  apply flag_pend_task_entry_call_source; exact Hentry.
Qed.

(** The entry guard proof is consumed here, before changing the active
    assertion. No fact is requested about a future output observation. *)
Lemma flag_pend_boot_first_save_event_from_completion :
  forall environment critical local next_local sg original mask saved before
    first_heap returned current last_heap i pgrp mode observed,
  flag_pend_caller_source sg (FlagPendTaskCaller original) original
    i pgrp mode before ->
  pgrp <> 0 -> os_sched_ints before <= 0 -> os_sched_locks before <= 0 ->
  flag_pend_group_lookup before i observed -> flag_pend_group_type observed = 5 ->
  flag_pend_boot_save_completion environment critical local next_local sg
    original mask saved before first_heap returned current last_heap ->
  CompletedCallerEvents.flag_pend_selected_caller_save_event
    environment critical local (flag_pend_first_observation mode original before) sg
    (FlagPendTaskCaller original) original mask saved before
    (FlagPendTaskCaller returned) returned current next_local first_heap last_heap.
Proof.
  intros environment critical local next_local sg original mask saved before
    first_heap returned current last_heap i pgrp mode observed
    Hcaller Hptr Hints Hlocks Hlookup Htype Hactual.
  pose proof (flag_pend_boot_save_completion_post
    _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual) as [Hboot Hpost].
  pose proof (flag_pend_boot_guarded_call_invalid_mode sg original before
    i pgrp mode observed Hboot Hcaller Hptr Hints Hlocks Hlookup Htype) as Hinvalid.
  rewrite (flag_pend_boot_first_observation_eq mode original before Hboot Hinvalid).
  eapply CompletedBootCallerEvents.flag_pend_boot_save_event_from_completion; exact Hactual.
Qed.

(** [reference, initial] remain the first-call observation indices. The
    actual Restore's [original, acquired, before] indices are not replaced. *)
Lemma flag_pend_boot_first_restore_event_from_completion :
  forall environment critical local next_local sg reference initial
    original saved acquired before first_heap returned current last_heap
    i pgrp mode observed,
  reference.(os_sched_call_origin) = BootInvocation ->
  flag_pend_caller_source sg (FlagPendTaskCaller reference) reference
    i pgrp mode initial ->
  pgrp <> 0 -> os_sched_ints initial <= 0 -> os_sched_locks initial <= 0 ->
  flag_pend_group_lookup initial i observed -> flag_pend_group_type observed = 5 ->
  flag_pend_boot_restore_completion environment critical local next_local sg
    original saved acquired before first_heap returned current last_heap ->
  CompletedCallerEvents.flag_pend_selected_caller_restore_event
    environment critical local (flag_pend_first_observation mode reference initial) sg
    (FlagPendTaskCaller original) original saved acquired before
    (FlagPendTaskCaller returned) returned current next_local first_heap last_heap.
Proof.
  intros environment critical local next_local sg reference initial
    original saved acquired before first_heap returned current last_heap
    i pgrp mode observed Hboot Hcaller Hptr Hints Hlocks Hlookup Htype Hactual.
  pose proof (flag_pend_boot_guarded_call_invalid_mode sg reference initial
    i pgrp mode observed Hboot Hcaller Hptr Hints Hlocks Hlookup Htype) as Hinvalid.
  rewrite (flag_pend_boot_first_observation_eq mode reference initial Hboot Hinvalid).
  eapply CompletedBootCallerEvents.flag_pend_boot_restore_event_from_completion; exact Hactual.
Qed.

Lemma flag_pend_boot_first_save_output_from_completion :
  forall environment critical local next_local sg original mask saved before
    first_heap returned current last_heap i pgrp mode observed,
  flag_pend_caller_source sg (FlagPendTaskCaller original) original
    i pgrp mode before ->
  pgrp <> 0 -> os_sched_ints before <= 0 -> os_sched_locks before <= 0 ->
  flag_pend_group_lookup before i observed -> flag_pend_group_type observed = 5 ->
  flag_pend_boot_save_completion environment critical local next_local sg
    original mask saved before first_heap returned current last_heap ->
  CompletedCallerEvents.flag_pend_selected_caller_save_output
    environment critical local (flag_pend_first_observation mode original before) sg
    (FlagPendTaskCaller original) original mask before first_heap saved last_heap.
Proof.
  intros environment critical local next_local sg original mask saved before
    first_heap returned current last_heap i pgrp mode observed
    Hcaller Hptr Hints Hlocks Hlookup Htype Hactual.
  exists (FlagPendTaskCaller returned), returned, current, next_local.
  eapply flag_pend_boot_first_save_event_from_completion; eassumption.
Qed.

Lemma flag_pend_boot_first_restore_output_from_completion :
  forall environment critical local next_local sg reference initial
    original saved acquired before first_heap returned current last_heap
    i pgrp mode observed,
  reference.(os_sched_call_origin) = BootInvocation ->
  flag_pend_caller_source sg (FlagPendTaskCaller reference) reference
    i pgrp mode initial ->
  pgrp <> 0 -> os_sched_ints initial <= 0 -> os_sched_locks initial <= 0 ->
  flag_pend_group_lookup initial i observed -> flag_pend_group_type observed = 5 ->
  flag_pend_boot_restore_completion environment critical local next_local sg
    original saved acquired before first_heap returned current last_heap ->
  CompletedCallerEvents.flag_pend_selected_caller_restore_output
    environment critical local (flag_pend_first_observation mode reference initial) sg
    (FlagPendTaskCaller original) original saved acquired before first_heap last_heap.
Proof.
  intros environment critical local next_local sg reference initial
    original saved acquired before first_heap returned current last_heap
    i pgrp mode observed Hboot Hcaller Hptr Hints Hlocks Hlookup Htype Hactual.
  exists (FlagPendTaskCaller returned), returned, current, next_local.
  eapply flag_pend_boot_first_restore_event_from_completion; eassumption.
Qed.

End FlagPendBootFirstCallers.

