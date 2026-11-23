Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_sched_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_idle_protocol_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** These are observations of the three existing C inheritance branches.
    No task or continuation is created, retired, parked or resumed here.
    The critical token continues to name its original acquired world. *)
Lemma mutex_pend_inherit_call_fields_eq :
  forall sg before owner node base waiter ceiling after,
  mutex_pend_inherit_step sg before owner node base waiter ceiling after ->
  after.(TskState).(taskLifecycle) = before.(TskState).(taskLifecycle) /\
  after.(TskState).(parkedTaskStacks) = before.(TskState).(parkedTaskStacks) /\
  after.(IntrState) = before.(IntrState) /\
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros sg before owner node base waiter ceiling after Hstep.
  unfold mutex_pend_inherit_step in Hstep.
  destruct (mutex_pend_inherit_action _ _ _ _ _).
  - subst after; repeat split; reflexivity.
  - subst after; repeat split; reflexivity.
  - destruct Hstep as [events [_ ->]]; repeat split; reflexivity.
Qed.

(** The real owner lookup rules out inserting a fresh live slot. Both
    directions retain each live instance's generation and saved SP. The
    owner's priority may change, so whole used-map equality is not used. *)
Lemma mutex_pend_inherit_stack_nodes :
  forall sg before owner node base waiter ceiling after,
  before.(TskState).(inUsedTaskStates) owner = Some node ->
  mutex_pend_inherit_step sg before owner node base waiter ceiling after ->
  (forall slot current, after.(TskState).(inUsedTaskStates) slot = Some current ->
    exists old, before.(TskState).(inUsedTaskStates) slot = Some old /\
      old.(taskGeneration) = current.(taskGeneration) /\ old.(tcbStkPtr) = current.(tcbStkPtr)) /\
  (forall slot old, before.(TskState).(inUsedTaskStates) slot = Some old ->
    exists current, after.(TskState).(inUsedTaskStates) slot = Some current /\
      current.(taskGeneration) = old.(taskGeneration) /\ current.(tcbStkPtr) = old.(tcbStkPtr)).
Proof.
  intros sg before owner node base waiter ceiling after Howner Hstep.
  unfold mutex_pend_inherit_step in Hstep.
  destruct (mutex_pend_inherit_action _ _ _ _ _).
  - subst after; split; intros slot current Hcurrent; exists current; auto.
  - subst after; split; intros slot current Hcurrent; exists current; auto.
  - destruct Hstep as [events [_ ->]].
    cbn [replace_EventS replace_SchedS replace_TskS TskState
      mutex_pend_demand_tasks glob_task_set_usedtask inUsedTaskStates].
    split; intros slot current Hcurrent; destruct (Z.eqb slot owner) eqn:Hslot.
    + apply Z.eqb_eq in Hslot; subst slot.
      injection Hcurrent as Hcurrent; subst current; exists node; auto.
    + exists current; auto.
    + apply Z.eqb_eq in Hslot; subst slot.
      assert (current = node) by congruence; subst current.
      exists (mutex_priority_task node ceiling); auto.
    + exists current; auto.
Qed.

Lemma mutex_pend_inherit_preserves_task_source :
  forall sg call before owner node base waiter ceiling after,
  before.(TskState).(inUsedTaskStates) owner = Some node ->
  kernel_call_task_source call before ->
  mutex_pend_inherit_step sg before owner node base waiter ceiling after ->
  kernel_call_task_source call after.
Proof.
  intros sg call before owner node base waiter ceiling after Howner
    [Horigin [[Hinv [Hretired Hlive]] Hcurrent]] Hstep.
  destruct (mutex_pend_inherit_call_fields_eq _ _ _ _ _ _ _ _ Hstep)
    as [Hlife [Hparked [Hints Hrunning]]].
  destruct (mutex_pend_inherit_stack_nodes _ _ _ _ _ _ _ _ Howner Hstep) as [_ Hnodes].
  pose proof (proj1 (mutex_pend_inherit_preserves_scheduler_caches _ _ _ _ _ _ _ _ Hstep)) as Hcur.
  split; [exact Horigin|]. split.
  - split; [rewrite Hlife; exact Hinv|]. split; [rewrite Hlife; exact Hretired|].
    rewrite Horigin in *; destruct Hlive as [old [Hold Hg]].
    destruct (Hnodes _ _ Hold) as [current [Hnode [Hgen Hsp]]].
    exists current; split; [exact Hnode|congruence].
  - unfold task_execution_current in *; rewrite Horigin in *; rewrite Hcur; exact Hcurrent.
Qed.

(** This consumer is restricted to the actual busy/wait path. Its running
    and blocking-stage inputs come from the separately checked before-to-
    Save-return consumers. Owner non-Idle priority is DERIVED from the
    actual Idle tail and owner-exclusion protocol, not added as an API or
    platform assumption. Immediate acquisition and early errors do not
    consume this stage. *)
Lemma mutex_pend_inherit_preserves_blocking_stage :
  forall sg call before idle eid event mutex owner node base waiter after,
  UCOS2_state_inv sg before ->
  mutex_idle_slot before.(TskState) idle -> mutex_idle_excluded idle before.(EventState) ->
  before.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> before.(TskState).(inUsedTaskStates) owner = Some node ->
  before.(SchedState).(isRunning) = true -> sem_pend_blocking_call_stage sg call before ->
  mutex_pend_inherit_step sg before owner node base waiter mutex.(mfPCP) after ->
  sem_pend_blocking_call_stage sg call after.
Proof.
  intros sg call before idle eid event mutex owner node base waiter after Hvalid Hslot Hexcluded
    He Htype Hm Ho Howner Hrunning [Hidle [Havailable [Hints Hlocks]]] Hstep.
  assert (Hnonidle : node.(curPrio) <> sg.(osLowestPrio)).
  { eapply mutex_owner_non_idle_priority_when_running; eassumption. }
  unfold mutex_pend_inherit_step in Hstep.
  destruct (mutex_pend_inherit_action _ _ _ _ _).
  - subst after; repeat split; assumption.
  - subst after; repeat split; assumption.
  - destruct Hstep as [events [_ ->]].
    split.
    + change (task_idle_ready sg (glob_task_set_usedtask before.(TskState) owner
        (mutex_priority_task node mutex.(mfPCP)))).
      eapply task_update_non_idle_preserves_idle_ready; eassumption.
    + split; [exact Havailable|]; split; assumption.
Qed.

(** The existing inheritance observations supply the actual other-caller
    map frame. The caller/owner distinction follows at the API cut from
    the busy caller's holds-no-Mutex fact; it is not imposed on the earlier
    immediate-acquire branch. No after-source/cache/stage is a premise. *)
Lemma mutex_pend_inherit_preserves_call_stage :
  forall sg call before idle eid event mutex owner node base waiter after,
  UCOS2_state_inv sg before ->
  mutex_idle_slot before.(TskState) idle -> mutex_idle_excluded idle before.(EventState) ->
  mutex_owner_event_unlinked before.(TskState) before.(EventState) ->
  before.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> before.(TskState).(inUsedTaskStates) owner = Some node ->
  before.(SchedState).(isRunning) = true ->
  call.(os_sched_call_stack).(stackLeaseSlot) <> owner ->
  kernel_call_task_source call before ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sem_pend_blocking_call_stage sg call before ->
  mutex_pend_inherit_step sg before owner node base waiter mutex.(mfPCP) after ->
  kernel_call_task_source call after /\
  sched_current_consistency after.(TskState) after.(SchedState) /\
  sem_pend_blocking_call_stage sg call after.
Proof.
  intros sg call before idle eid event mutex owner node base waiter after Hvalid Hslot Hexcluded
    Huse He Htype Hm Ho Howner Hrunning Hother Hsource Hcache Hstage Hstep.
  split; [eapply mutex_pend_inherit_preserves_task_source; eassumption|].
  split.
  - destruct (mutex_pend_inherit_observations sg before eid event mutex owner node base waiter
      after Hvalid Huse He Htype Hm Ho Howner Hstep) as [Hevents [Hcurrent [Hnodes Hready]]].
    pose proof (proj1 (proj2 (mutex_pend_inherit_preserves_scheduler_caches
      _ _ _ _ _ _ _ _ Hstep))) as Hpriority.
    destruct (kernel_call_task_source_current_at call before Hsource) as [Htid Hlive].
    unfold sched_current_consistency in *; rewrite Hcurrent, Htid; rewrite Htid in Hcache.
    destruct Hcache as [caller [Hcaller Hprio]].
    exists caller; split; [rewrite Hnodes; assumption|rewrite Hpriority; exact Hprio].
  - eapply mutex_pend_inherit_preserves_blocking_stage; eassumption.
Qed.

Lemma mutex_pend_inherit_coverage_iff :
  forall sg before owner node base waiter ceiling after active,
  before.(TskState).(inUsedTaskStates) owner = Some node ->
  mutex_pend_inherit_step sg before owner node base waiter ceiling after ->
  task_stack_live_coverage before.(TskState) active <->
  task_stack_live_coverage after.(TskState) active.
Proof.
  intros sg before owner node base waiter ceiling after active Howner Hstep.
  destruct (mutex_pend_inherit_call_fields_eq _ _ _ _ _ _ _ _ Hstep)
    as [Hlife [Hparked _]].
  destruct (mutex_pend_inherit_stack_nodes _ _ _ _ _ _ _ _ Howner Hstep) as [Hbefore Hafter].
  split; intro Hcoverage.
  - eapply task_stack_live_coverage_used_map_frame; [|exact Hparked|exact Hcoverage].
    intros slot current Hcurrent; destruct (Hbefore _ _ Hcurrent) as [old [Hold [Hg Hsp]]].
    exists old; auto.
  - eapply task_stack_live_coverage_used_map_frame; [|symmetry; exact Hparked|exact Hcoverage].
    intros slot old Hold; destruct (Hafter _ _ Hold) as [current [Hcurrent [Hg Hsp]]].
    exists current; auto.
Qed.

(** Reindex the same owned continuation descriptors and local owners.
    Both directions follow the actual lookup/generation/SP observations;
    no global heap equality or fabricated capsule is assumed. *)
Lemma mutex_pend_inherit_continuation_capsules_equiv :
  forall environment saved_local sg before owner node base waiter ceiling after,
  before.(TskState).(inUsedTaskStates) owner = Some node ->
  mutex_pend_inherit_step sg before owner node base waiter ceiling after ->
  task_tcb_init_continuation_capsules environment saved_local before --||--
  task_tcb_init_continuation_capsules environment saved_local after.
Proof.
  intros environment saved_local sg before owner node base waiter ceiling after Howner Hstep.
  destruct (mutex_pend_inherit_call_fields_eq _ _ _ _ _ _ _ _ Hstep)
    as [Hlife [Hparked _]].
  destruct (mutex_pend_inherit_stack_nodes _ _ _ _ _ _ _ _ Howner Hstep) as [Hbefore Hafter].
  unfold task_tcb_init_continuation_capsules; rewrite Hparked; split.
  - apply kernel_saved_continuation_map_reindex.
    intros key payload current Hpayload Hcurrent Hg; exact (Hbefore _ _ Hcurrent).
  - apply kernel_saved_continuation_map_reindex.
    intros key payload old Hpayload Hold Hg; exact (Hafter _ _ Hold).
Qed.

(** Native masked-frame consumer. The untouched critical token, context
    ownership and perr cell can stay in the separating frame while these
    two indexed resources are moved from entry to inherited. *)
Lemma mutex_pend_inherit_continuation_resources :
  forall environment saved_local sg before owner node base waiter ceiling after active,
  before.(TskState).(inUsedTaskStates) owner = Some node ->
  mutex_pend_inherit_step sg before owner node base waiter ceiling after ->
  coq_prop (task_stack_live_coverage before.(TskState) active) &&
    task_tcb_init_continuation_capsules environment saved_local before --||--
  coq_prop (task_stack_live_coverage after.(TskState) active) &&
    task_tcb_init_continuation_capsules environment saved_local after.
Proof.
  intros environment saved_local sg before owner node base waiter ceiling after active Howner Hstep.
  rewrite (mutex_pend_inherit_continuation_capsules_equiv environment saved_local
    sg before owner node base waiter ceiling after Howner Hstep).
  pose proof (mutex_pend_inherit_coverage_iff sg before owner node base waiter ceiling after
    active Howner Hstep) as Hcoverage.
  split; entailer!; tauto.
Qed.
