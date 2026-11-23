Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait Ucos2Verify.lib.interrupt Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_clients_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** These are fields untouched by the actual masked Del operation. A held
    owner's priority may change and waiters may be woken; neither operation
    retires a task invocation or changes its saved stack pointer. The private
    ECB pool is separate from the public ECB recycled by this call. *)
Definition mutex_del_call_fields_eq (before after : UCOS2_Verify_State) : Prop :=
  (forall slot,
    option_map (fun node => (node.(taskGeneration), node.(tcbStkPtr)))
      (after.(TskState).(inUsedTaskStates) slot) =
    option_map (fun node => (node.(taskGeneration), node.(tcbStkPtr)))
      (before.(TskState).(inUsedTaskStates) slot)) /\
  after.(TskState).(parkedTaskStacks) = before.(TskState).(parkedTaskStacks) /\
  after.(TskState).(taskLifecycle) = before.(TskState).(taskLifecycle) /\
  after.(SchedState).(curTaskID) = before.(SchedState).(curTaskID) /\
  after.(EventState).(eventLifecycle).(eventPrivate) =
    before.(EventState).(eventLifecycle).(eventPrivate).

Lemma mutex_del_call_fields_eq_refl : forall state,
  mutex_del_call_fields_eq state state.
Proof. intros; repeat split; intros; reflexivity. Qed.

Lemma mutex_del_call_fields_eq_trans : forall before middle after,
  mutex_del_call_fields_eq before middle -> mutex_del_call_fields_eq middle after ->
  mutex_del_call_fields_eq before after.
Proof.
  intros before middle after [Hnodes [Hstacks [Hlife [Hcurrent Hprivate]]]]
    [Hnodes' [Hstacks' [Hlife' [Hcurrent' Hprivate']]]].
  split; [intros slot; rewrite Hnodes', Hnodes; reflexivity|].
  repeat split; congruence.
Qed.

Lemma mutex_del_prepare_call_fields_eq : forall sg mutex entry prepared,
  mutex_del_prepare sg mutex entry prepared -> mutex_del_call_fields_eq entry prepared.
Proof.
  intros sg mutex entry prepared Hprepare; unfold mutex_del_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis));
    [subst; apply mutex_del_call_fields_eq_refl|].
  destruct mutex.(mfOwner) as [owner|]; [|subst; repeat split; intros; reflexivity].
  destruct Hprepare as [node [priority [Hnode [_ ->]]]].
  unfold mutex_del_owner_priority_state; destruct Z.eq_dec; [repeat split; intros; reflexivity|].
  split.
  - intros slot; cbn [mutex_del_relocated_state replace_SchedS replace_TskS TskState
      mutex_del_relocated_tasks inUsedTaskStates].
    apply glob_task_set_usedtask_observation with (old := node); [exact Hnode|reflexivity].
  - repeat split; reflexivity.
Qed.

Lemma mutex_del_wake_call_fields_eq : forall sg eid kind message result state priority after,
  event_task_rdy sg state eid kind message result = Some (priority, after) ->
  mutex_del_call_fields_eq state after.
Proof.
  intros sg eid kind message result state priority after Hstep.
  unfold event_task_rdy in Hstep.
  destruct (state.(EventState).(inUsedEventStates) eid) as [event|] eqn:He;
    [|discriminate].
  destruct (state.(TskState).(prioTbl) (event_wait_priority state.(TskState) event))
    as [| |tid]; try discriminate.
  destruct (state.(TskState).(inUsedTaskStates) tid) as [old|] eqn:Hold;
    [|discriminate].
  injection Hstep as Hpriority Hafter; subst after; split.
  - intros slot; cbn [event_wake_state replace_SchedS replace_EventS replace_TskS TskState].
    apply glob_task_set_usedtask_observation with (old := old); [exact Hold|reflexivity].
  - repeat split; try reflexivity.
    cbn [event_wake_state replace_SchedS SchedState].
    unfold sched_wake_by_status.
    match goal with |- context [if ?suspended then _ else _] => destruct suspended end; reflexivity.
Qed.

Lemma mutex_del_broadcast_call_fields_eq : forall sg eid kind message result before priorities after,
  event_broadcast sg eid kind message result before priorities after ->
  mutex_del_call_fields_eq before after.
Proof.
  intros sg eid kind message result before priorities after Hrun; induction Hrun.
  - apply mutex_del_call_fields_eq_refl.
  - eapply mutex_del_call_fields_eq_trans; [|exact IHHrun].
    eapply mutex_del_wake_call_fields_eq; eassumption.
Qed.

Lemma mutex_del_critical_call_fields_eq : forall sg eid option entry result checkpoint,
  mutex_del_critical sg eid option entry result checkpoint ->
  mutex_del_call_fields_eq entry checkpoint.
Proof.
  intros sg eid option entry result checkpoint [event [mutex [_ [_ [_ Hrun]]]]].
  assert (Hrecycle : forall state node,
    mutex_del_call_fields_eq state (mutex_del_recycle_state sg eid node state)).
  { intros; repeat split; intros; reflexivity. }
  destruct (Z.eq_dec option 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) entry.(TskState)) 0).
    + destruct Hrun as [prepared [Hprepare [-> _]]].
      eapply mutex_del_call_fields_eq_trans; [|apply Hrecycle].
      eapply mutex_del_prepare_call_fields_eq; exact Hprepare.
    + destruct Hrun as [-> _]; apply mutex_del_call_fields_eq_refl.
  - destruct (Z.eq_dec option 1).
    + destruct Hrun as [prepared [priorities [drained [Hprepare [Hbroadcast [-> _]]]]]].
      eapply mutex_del_call_fields_eq_trans; [|apply Hrecycle].
      eapply mutex_del_call_fields_eq_trans.
      * eapply mutex_del_prepare_call_fields_eq; exact Hprepare.
      * eapply mutex_del_broadcast_call_fields_eq; exact Hbroadcast.
    + destruct Hrun as [-> _]; apply mutex_del_call_fields_eq_refl.
Qed.

(** This residual is borrowed ONLY while the Del C body is masked. The
    program heap is updated by the original prepare/wake/recycle proofs.
    Both pieces are recombined before the actual Restore transition. *)
Definition mutex_del_stack_critical_frame {external platform port}
  (abi : Armv7aContinuationABI external platform port) sg active entry : Assertion :=
  coq_prop (mutex_program_selected_reachable sg entry /\
    mutex_del_private_types_non_mutex entry.(EventState) /\
    task_stack_live_coverage entry.(TskState) active) &&
  (event_private_pool_rep sg entry.(EventState) **
   armv7a_task_stack_continuations abi entry.(TskState) entry.(TskState).(parkedTaskStacks)).

Lemma mutex_del_stack_world_split_critical_frame : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg active entry,
  kernel_stack_inv abi mutex_del_stack_resources sg active entry --||--
  kernel_program_inv sg entry ** mutex_del_stack_critical_frame abi sg active entry.
Proof.
  intros; unfold kernel_stack_inv, mutex_del_stack_resources, mutex_del_stack_critical_frame;
    split; entailer!.
Qed.

Lemma mutex_del_stack_critical_merge : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg active entry checkpoint eid option result,
  mutex_del_critical sg eid option entry result checkpoint ->
  kernel_program_inv sg checkpoint ** mutex_del_stack_critical_frame abi sg active entry |--
  kernel_stack_inv abi mutex_del_stack_resources sg active checkpoint.
Proof.
  intros external platform port abi sg active entry checkpoint eid option result Hrun.
  destruct (mutex_del_critical_call_fields_eq _ _ _ _ _ _ Hrun)
    as [Hnodes [Hstacks [Hlife [Hcurrent Hprivate]]]].
  assert (Hlookup : forall slot node, checkpoint.(TskState).(inUsedTaskStates) slot = Some node ->
    exists old, entry.(TskState).(inUsedTaskStates) slot = Some old /\
      old.(taskGeneration) = node.(taskGeneration) /\ old.(tcbStkPtr) = node.(tcbStkPtr)).
  { intros slot node Hnode; specialize (Hnodes slot); rewrite Hnode in Hnodes.
    destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold;
      [|discriminate].
    cbn in Hnodes; injection Hnodes as Hg Hsp; exists old; auto. }
  unfold mutex_del_stack_critical_frame; Intros_p Hfacts.
  destruct Hfacts as [Hhistory [Htypes Hcoverage]].
  assert (Hcoverage' : task_stack_live_coverage checkpoint.(TskState) active).
  { eapply task_stack_live_coverage_used_map_frame; [|exact Hstacks|exact Hcoverage].
    intros slot node Hnode; destruct (Hlookup slot node Hnode) as [old [Hold [Hg Hsp]]].
    exists old; split; [exact Hold|symmetry; exact Hg]. }
  assert (Hhistory' : mutex_program_selected_reachable sg checkpoint).
  { eapply mutex_program_source_history_reachable; [exact Hhistory|].
    eapply mutex_program_del_critical_source; exact Hrun. }
  assert (Htypes' : mutex_del_private_types_non_mutex checkpoint.(EventState)).
  { unfold mutex_del_private_types_non_mutex in *; rewrite Hprivate; exact Htypes. }
  assert (Hcapsules : armv7a_task_stack_continuations abi entry.(TskState)
      entry.(TskState).(parkedTaskStacks) |--
    armv7a_task_stack_continuations abi checkpoint.(TskState)
      checkpoint.(TskState).(parkedTaskStacks)).
  { rewrite Hstacks; apply armv7a_task_stack_continuations_reindex.
    intros key payload node Hparked Hnode Hgen; eapply Hlookup; exact Hnode. }
  sep_apply_l_atomic Hcapsules.
  unfold kernel_stack_inv, mutex_del_stack_resources, event_private_pool_rep.
  rewrite Hprivate; entailer!.
Qed.

(** A caller supplies its actual unchanged/recheck branch or its actual
    critical result, not a generic environment-preservation premise. *)
Definition mutex_del_stack_checkpoint sg entry checkpoint : Prop :=
  checkpoint = entry \/ exists eid option result,
    mutex_del_critical sg eid option entry result checkpoint.

Definition mutex_del_stack_restore_input {external platform port}
  (abi : Armv7aContinuationABI external platform port) critical sg active call saved entry checkpoint : Assertion :=
  coq_prop (mutex_del_stack_checkpoint sg entry checkpoint) &&
  (critical_region_masked platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved entry **
   os_sched_context_resources external call ** kernel_program_inv sg checkpoint **
   mutex_del_stack_critical_frame abi sg active entry).

Lemma mutex_del_stack_restore_input_masked : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg active call saved entry checkpoint,
  mutex_del_stack_restore_input abi critical sg active call saved entry checkpoint |--
  kernel_stack_call_masked abi mutex_del_stack_resources critical sg active call saved entry checkpoint.
Proof.
  intros; unfold mutex_del_stack_restore_input; Intros_p Hcheckpoint.
  assert (Hmerge : kernel_program_inv sg checkpoint ** mutex_del_stack_critical_frame abi sg active entry |--
    kernel_stack_inv abi mutex_del_stack_resources sg active checkpoint).
  { destruct Hcheckpoint as [->|[eid [option [result Hrun]]]].
    - apply (proj2 (mutex_del_stack_world_split_critical_frame _ _ _ abi sg active entry)).
    - eapply mutex_del_stack_critical_merge; exact Hrun. }
  sep_apply_l_atomic Hmerge; unfold kernel_stack_call_masked; entailer!.
Qed.
