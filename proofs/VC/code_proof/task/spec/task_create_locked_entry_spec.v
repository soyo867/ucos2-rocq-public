Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.

(** The actual self-suspend critical transformer removes readiness even
    while scheduling is locked. The following OS_Sched C prefix does not
    change the state. Thus this source endpoint supports the corrected
    Create stage and refutes the old zero-nesting-only readiness clause.
    Save/Restore interference is not collapsed into this local theorem. *)
Lemma task_create_locked_self_suspend_stage : forall sg state call node,
  UCOS2_state_inv sg state ->
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_create_call_stage call state ->
  state.(IntrState).(intNesting) = 0 -> state.(IntrState).(lockNesting) <> 0 ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  let suspended := task_suspend_state state call.(os_sched_call_stack).(stackLeaseSlot) node in
  task_suspend_critical sg sg.(osPrioSelf) state (OS_ERR_NONE, true) suspended /\
  UCOS2_state_inv sg suspended /\ task_create_call_stage call suspended /\
  suspended.(IntrState).(intNesting) = 0 /\
  ~ (exists ready, sched_current_ready_at suspended.(TskState) suspended.(SchedState)
      call.(os_sched_call_stack).(stackLeaseSlot) ready) /\
  os_sched_requests_switch suspended = false /\ os_sched_prefix_state suspended = suspended.
Proof.
  intros sg state call node Hvalid Horigin [Hcurrent Hstage] Hnesting Hlock Hnode suspended.
  rewrite Horigin in Hcurrent, Hstage.
  destruct Hcurrent as [Hrunning [Htid [current [Hcurrent Hgen]]]].
  assert (current = node) by congruence; subst current.
  destruct Hstage as [Hslot [Hgeneration [Habsent Hready]]].
  assert (Hstep : task_suspend_critical sg sg.(osPrioSelf) state (OS_ERR_NONE, true) suspended)
    by (apply task_suspend_critical_self; assumption).
  assert (Hpost : UCOS2_state_inv sg suspended)
    by (eapply task_suspend_critical_preserves_validity; eassumption).
  assert (Hlookup : suspended.(TskState).(inUsedTaskStates)
      call.(os_sched_call_stack).(stackLeaseSlot) = Some (task_suspend node)).
  { unfold suspended, task_suspend_state.
    cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
    rewrite Z.eqb_refl; reflexivity. }
  assert (Hdisabled : os_sched_selection_enabled suspended = false).
  { unfold os_sched_selection_enabled; change ((Z.eqb state.(IntrState).(intNesting) 0 &&
      Z.eqb state.(IntrState).(lockNesting) 0)%bool = false).
    rewrite Hnesting, Z.eqb_refl, (proj2 (Z.eqb_neq _ _) Hlock); reflexivity. }
  split; [exact Hstep|]. split; [exact Hpost|]. split.
  - unfold task_create_call_stage; rewrite Horigin.
    split.
    + split; [exact Hrunning|]. split; [exact Htid|].
      exists (task_suspend node); split; [exact Hlookup|exact Hgen].
    + split; [exact Hslot|]. split; [exact Hgeneration|]. split; [exact Habsent|].
      rewrite Hdisabled; discriminate.
  - split; [exact Hnesting|]. split.
    + intros [ready [Hfound [_ [_ [_ Heffective]]]]].
      assert (ready = task_suspend node) by congruence; subst ready.
      rewrite task_suspend_not_ready in Heffective; discriminate.
    + split.
      * unfold os_sched_requests_switch; rewrite Hdisabled; reflexivity.
      * unfold os_sched_prefix_state, os_sched_ready_checkpoint; rewrite Hdisabled.
        destruct suspended; reflexivity.
Qed.
