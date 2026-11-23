Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_proofs.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_program_storage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Import UCOS2_C_Rules ListNotations TaskStateDef EventStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** Internal protected-Type cut, not an extra public precondition.
    The producer annotation has an explicit open source-protocol obligation;
    the following field/slot consumer uses this fact on the same masked heap.
    Keeping it in the residual avoids losing the byte ownership or pretending
    that Type=Mutex establishes the approved owner-use protocol. *)
Definition mutex_del_recheck_owner_residual sg pointer eid state observed : Assertion :=
  coq_prop (mutex_owner_event_unlinked state.(TskState) state.(EventState)) &&
    mutex_del_recheck_residual sg pointer eid state observed.

Lemma mutex_del_parent_recheck_type_address : forall sg pointer eid,
  mutex_del_parent_layout sg -> valid_event_id sg eid -> pointer = event_addr sg eid ->
  &(pointer # "os_event" ->ₛ "OSEventType") = pointer.
Proof.
  intros sg pointer eid [_ [Hlayout _]] Hid ->.
  rewrite (proj1 (proj1 (Hlayout eid Hid))); unfold OSEventType_off; lia.
Qed.

(** These are the task-map effects of the actual masked deletion stores,
    not frame assumptions across Restore or OS_Sched. *)
Lemma mutex_del_prepare_parked_stacks_eq : forall sg mutex entry prepared,
  mutex_del_prepare sg mutex entry prepared ->
  prepared.(TskState).(parkedTaskStacks) = entry.(TskState).(parkedTaskStacks).
Proof.
  intros sg mutex entry prepared Hprepare; unfold mutex_del_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)); [subst; reflexivity|].
  destruct mutex.(mfOwner) as [owner|]; [|subst; reflexivity].
  destruct Hprepare as [node [priority [_ [_ ->]]]].
  unfold mutex_del_owner_priority_state; destruct Z.eq_dec; reflexivity.
Qed.

Lemma mutex_del_broadcast_parked_stacks_eq : forall sg eid kind message result before priorities after,
  event_broadcast sg eid kind message result before priorities after ->
  after.(TskState).(parkedTaskStacks) = before.(TskState).(parkedTaskStacks).
Proof.
  intros sg eid kind message result before priorities after Hrun; induction Hrun.
  - reflexivity.
  - rewrite IHHrun; unfold event_task_rdy in H1; rewrite H in H1.
    destruct (s.(TskState).(prioTbl) (event_wait_priority s.(TskState) e)) as [| |tid]; try discriminate.
    destruct (s.(TskState).(inUsedTaskStates) tid) as [old|]; try discriminate.
    injection H1 as Hpriority Hstate; subst mid; reflexivity.
Qed.

Lemma mutex_del_critical_parked_stacks_eq : forall sg eid option entry outcome checkpoint,
  mutex_del_critical sg eid option entry outcome checkpoint ->
  checkpoint.(TskState).(parkedTaskStacks) = entry.(TskState).(parkedTaskStacks).
Proof.
  intros sg eid option entry outcome checkpoint [event [mutex [_ [_ [_ Hsource]]]]].
  destruct (Z.eq_dec option 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) entry.(TskState)) 0).
    + destruct Hsource as [prepared [Hprepare [-> _]]].
      exact (mutex_del_prepare_parked_stacks_eq sg mutex entry prepared Hprepare).
    + destruct Hsource as [-> _]; reflexivity.
  - destruct (Z.eq_dec option 1).
    + destruct Hsource as [prepared [priorities [drained [Hprepare [Hbroadcast [-> _]]]]]].
      change (drained.(TskState).(parkedTaskStacks) = entry.(TskState).(parkedTaskStacks)).
      rewrite (mutex_del_broadcast_parked_stacks_eq _ _ _ _ _ _ _ _ Hbroadcast).
      exact (mutex_del_prepare_parked_stacks_eq sg mutex entry prepared Hprepare).
    + destruct Hsource as [-> _]; reflexivity.
Qed.

Lemma mutex_del_parent_observation_parked_stacks_eq : forall sg eid option result error request entry checkpoint,
  mutex_del_parent_critical_observation sg eid option result error request entry checkpoint ->
  checkpoint.(TskState).(parkedTaskStacks) = entry.(TskState).(parkedTaskStacks).
Proof.
  intros sg eid option result error request entry checkpoint [code [scheduled [Hrun _]]].
  exact (mutex_del_critical_parked_stacks_eq _ _ _ _ _ _ Hrun).
Qed.

Lemma mutex_del_recheck_type_cast_eq : forall sg pointer eid state value,
  pointer # UChar |-> value ** mutex_del_recheck_residual sg pointer eid state value |--
  coq_prop (unsigned_last_nbits value 32 = value) &&
    (pointer # UChar |-> value ** mutex_del_recheck_residual sg pointer eid state value).
Proof.
  intros; prop_apply_p (store_uchar_range pointer value); Intros_p Hrange.
  assert (Hcast : unsigned_last_nbits value 32 = value).
  { apply unsigned_last_nbits_eq; change (0 <= value <= 255) in Hrange;
      change (0 <= value < 4294967296); lia. }
  entailer!.
Qed.

Lemma mutex_del_parent_program_restore_stage : forall external platform critical sg context
  mask saved before entry checkpoint eid option result error request,
  mutex_del_parent_critical_observation sg eid option result error request entry checkpoint ->
  mutex_del_parent_program_restore_pre platform critical sg context.(os_sched_call_invocation)
      context.(os_sched_call_origin) mask saved before entry checkpoint **
    mutex_del_callsite_acquired external platform critical sg context mask saved before entry |--
  mutex_del_callsite_restore_stage external platform critical sg context mask saved before entry checkpoint.
Proof.
  intros; unfold mutex_del_parent_program_restore_pre; Intros.
  sep_apply_l_atomic (mutex_del_callsite_program_restore_stage external platform critical sg context
    mask saved before entry checkpoint
    (mutex_del_parent_observation_parked_stacks_eq _ _ _ _ _ _ _ _ H)); entailer!.
Qed.

Lemma mutex_del_parent_recheck_restore_stage : forall external platform critical sg context
  mask saved before entry pointer eid,
  mutex_del_parent_recheck_restore_pre platform critical sg context.(os_sched_call_invocation)
      context.(os_sched_call_origin) mask saved before entry pointer eid **
    mutex_del_callsite_acquired external platform critical sg context mask saved before entry |--
  mutex_del_callsite_restore_stage external platform critical sg context mask saved before entry entry.
Proof.
  intros; unfold mutex_del_parent_recheck_restore_pre; Intros.
  sep_apply_l_atomic (mutex_del_callsite_recheck_restore_stage external platform critical sg context
    mask saved before entry pointer eid); entailer!.
Qed.
