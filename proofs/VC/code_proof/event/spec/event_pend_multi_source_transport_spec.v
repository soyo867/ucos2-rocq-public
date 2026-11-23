Require Import Coq.Lists.List Coq.ZArith.ZArith.
Require Export Ucos2Verify.VC.code.event.spec.event_pend_multi_continuation_phase_spec.
Require Import Ucos2Verify.lib.tick Ucos2Verify.lib.task_context
  Ucos2Verify.lib.atomic_ops_lib Ucos2Verify.lib.event_registration.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec
  Ucos2Verify.VC.code.sched.spec.sched_profile_heap_spec.
Import ListNotations TaskStateDef SchedStateDef.
Local Open Scope Z_scope.

(** This invocation's Task slot and generation are distinct from its
    current/ready scheduling status. None of the following frame proofs
    claims that this continuation can execute after retirement or reuse. *)
Definition event_pend_multi_state_continuation (state : UCOS2_Verify_State)
  (tid : TaskID) (generation : nat) (base : Z) (ids : list EventID) : Prop :=
  exists task, state.(TskState).(inUsedTaskStates) tid = Some task /\
    task.(taskGeneration) = generation /\ event_pend_multi_task_continuation base ids task.

Lemma event_pend_multi_tick_step_transports_continuation :
  forall sg state slot node tid generation base ids,
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  event_pend_multi_state_continuation state tid generation base ids ->
  event_pend_multi_state_continuation (tick_task_step sg slot node state) tid generation base ids.
Proof.
  intros sg state slot node tid generation base ids Hnode [task [Htask [Hg Hphase]]].
  unfold event_pend_multi_state_continuation.
  rewrite (tick_task_step_task_state_eq sg slot node state Hnode).
  cbn [glob_task_set_usedtask inUsedTaskStates].
  destruct (Z.eqb tid slot) eqn:E.
  - apply Z.eqb_eq in E; subst slot; assert (node = task) by congruence; subst node.
    exists (tick_task_update task); split; [reflexivity|]. split.
    + unfold tick_task_update; destruct (Z.eqb task.(dly) 0); exact Hg.
    + apply event_pend_multi_tick_preserves_task_continuation; exact Hphase.
  - exists task; auto.
Qed.

Lemma event_pend_multi_save_current_sp_transports_continuation :
  forall state slot sp tid generation base ids,
  event_pend_multi_state_continuation state tid generation base ids ->
  event_pend_multi_state_continuation (os_sched_save_current_sp state slot sp) tid generation base ids.
Proof.
  intros state slot sp tid generation base ids [task [Htask [Hg Hphase]]].
  unfold os_sched_save_current_sp.
  destruct (state.(TskState).(inUsedTaskStates) slot) as [node|] eqn:Hnode.
  - unfold event_pend_multi_state_continuation; cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
    destruct (Z.eqb tid slot) eqn:E.
    + apply Z.eqb_eq in E; subst slot; assert (node = task) by congruence; subst node.
      exists (task_set_saved_sp task sp); split; [reflexivity|]. split; [exact Hg|].
      apply event_pend_multi_saved_sp_preserves_task_continuation; exact Hphase.
    + exists task; auto.
  - exists task; split; [exact Htask|]; auto.
Qed.

Lemma event_pend_multi_install_context_transports_continuation :
  forall context saved incoming state tid generation base ids,
  event_pend_multi_state_continuation state tid generation base ids ->
  event_pend_multi_state_continuation
    (os_sched_install_context context saved incoming state) tid generation base ids.
Proof. intros; exact H. Qed.

(** Only the existing three proved source cuts are covered here. This is
    not an all-environment family or an opaque preservation certificate. *)
Lemma event_pend_multi_full_profile_cut_transports_continuation :
  forall cut state tid generation base ids,
  kernel_full_profile_cut_input cut state ->
  event_pend_multi_state_continuation state tid generation base ids ->
  event_pend_multi_state_continuation
    (kernel_full_profile_cut_state cut state) tid generation base ids.
Proof.
  intros cut state tid generation base ids Hinput Hphase.
  destruct cut as [|observed|slot node]; [exact Hphase|exact Hphase|].
  destruct Hinput as [Hhigh Hnode].
  destruct Hphase as [task [Htask [Hg Hphase]]].
  unfold kernel_full_profile_cut_state, os_sched_profile_counts_state,
    os_sched_profile_global_state, os_sched_profile_task_state, event_pend_multi_state_continuation.
  cbn [replace_SchedS replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
  destruct (Z.eqb tid slot) eqn:E.
  - apply Z.eqb_eq in E; subst slot; assert (node = task) by congruence; subst node.
    exists (task_record_context_switch task); split; [reflexivity|]. split; [exact Hg|exact Hphase].
  - exists task; auto.
Qed.

Lemma event_pend_multi_full_profile_client_trace_transports_continuation :
  forall sg observer event_observer before stopped after tid generation base ids,
  kernel_client_resource_trace kernel_full_profile_cut_registered sg
    observer event_observer before stopped after ->
  event_pend_multi_state_continuation before tid generation base ids ->
  event_pend_multi_state_continuation after tid generation base ids.
Proof.
  intros sg observer event_observer before stopped after tid generation base ids Htrace.
  induction Htrace; intro Hphase; [exact Hphase|].
  apply IHHtrace.
  destruct H as [cut ->].
  destruct H2 as [Hinput ->].
  eapply event_pend_multi_full_profile_cut_transports_continuation; eassumption.
Qed.

Lemma event_pend_multi_full_profile_resumption_trace_transports_continuation :
  forall sg observer event_observer before stopped after tid generation base ids,
  kernel_resumption_resource_trace kernel_full_profile_cut_registered sg
    observer event_observer before stopped after ->
  event_pend_multi_state_continuation before tid generation base ids ->
  event_pend_multi_state_continuation after tid generation base ids.
Proof.
  intros sg observer event_observer before stopped after tid generation base ids Htrace Hphase.
  eapply event_pend_multi_full_profile_client_trace_transports_continuation;
    [eapply kernel_resumption_resource_trace_erases; exact Htrace|exact Hphase].
Qed.

(** The abstract program here already fixes the source-ordered
    selected-Event removal, original-array removal, TCB suffix and ready
    writes. The actual selected wait-list member supplies the ready id. *)
Lemma event_pend_multi_wake_step_transports_continuation :
  forall sg before after woken_tid selected node kind message result tid generation base ids,
  event_registration_consistency sg before.(TskState) before.(EventState) ->
  before.(EventState).(inUsedEventStates) selected = Some node -> In woken_tid node.(waitList) ->
  (result = PendOK \/ result = PendAbort) ->
  atomic_event_task_wake_multi sg woken_tid selected kind message result before tt after ->
  event_pend_multi_state_continuation before tid generation base ids ->
  event_pend_multi_state_continuation after tid generation base ids.
Proof.
  intros sg before after woken_tid selected node kind message result tid generation base ids
    Hregistration Hnode Hin Hresult [woken [events [Hwoken [Hlinked [Hloop ->]]]]]
    [task [Htask [Hg Hphase]]].
  unfold event_pend_multi_state_continuation, event_multi_wake_state.
  cbn [replace_SchedS replace_TskS replace_EventS TskState glob_task_set_usedtask inUsedTaskStates].
  destruct (Z.eqb tid woken_tid) eqn:E.
  - apply Z.eqb_eq in E; subst woken_tid; assert (woken = task) by congruence; subst woken.
    exists (task_multi_wake task kind message result selected); split; [reflexivity|]. split; [exact Hg|].
    eapply event_pend_multi_wake_establishes_task_continuation; eassumption.
  - exists task; auto.
Qed.

Lemma event_pend_multi_wake_step_inserts_nonsuspended_task :
  forall sg before after tid task selected kind message result,
  before.(TskState).(inUsedTaskStates) tid = Some task -> task_is_suspended task.(stat) = false ->
  atomic_event_task_wake_multi sg tid selected kind message result before tt after ->
  In tid after.(SchedState).(readyList).
Proof.
  intros sg before after tid task selected kind message result Htask Hrunning Hstep.
  destruct (atomic_event_task_wake_multi_ready_membership sg tid selected kind message result
    before after tid Hstep) as [found [Hfound Hmembers]].
  assert (found = task) by congruence; subst found.
  apply Hmembers; right; auto.
Qed.
