Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.sched Ucos2Verify.lib.event Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_idle_protocol_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** [idle] denotes the actual first-published Idle slot, retained as the
    tail of the active list.  The owner/waiter exclusion is established by
    the selected empty-hook client protocol.  No additional priority or
    architecture promise is attached to this concrete heap consumer. *)
Lemma mutex_pend_priority_output_merge_idle_protocol :
  forall sg before idle eid event mutex owner node base,
  UCOS2_state_inv sg before ->
  mutex_idle_slot before.(TskState) idle -> mutex_idle_excluded idle before.(EventState) ->
  mutex_owner_event_unlinked before.(TskState) before.(EventState) ->
  before.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  before.(TskState).(inUsedTaskStates) owner = Some node ->
  task_base_priority sg before.(TskState).(prioTbl) owner base ->
  mutex.(mfPCP) < node.(curPrio) ->
  mutex_pend_priority_output sg before owner node mutex.(mfPCP) **
    mutex_del_priority_frame sg before owner |--
  UCOS2_inv sg (mutex_pend_promoted_state sg before owner node mutex.(mfPCP)).
Proof.
  intros sg before idle eid event mutex owner node base Hvalid Hslot Hidle Huse
    He Htype Hm Ho Henabled Hnode Hbase Hcurrent.
  eapply mutex_pend_priority_output_merge; try eassumption.
  eapply mutex_owner_non_idle_priority_when_running; eassumption.
Qed.

Lemma mutex_pend_inherit_preserves_idle_slot :
  forall sg before idle owner node base waiter ceiling after,
  mutex_idle_slot before.(TskState) idle ->
  mutex_pend_inherit_step sg before owner node base waiter ceiling after ->
  mutex_idle_slot after.(TskState) idle.
Proof.
  intros sg before idle owner node base waiter ceiling after Hslot Hstep.
  unfold mutex_pend_inherit_step in Hstep.
  destruct (mutex_pend_inherit_action sg.(osPrioMutexCeilDis) base node.(curPrio) waiter ceiling).
  - subst after; exact Hslot.
  - subst after; exact Hslot.
  - destruct Hstep as [events [_ ->]]; exact Hslot.
Qed.

(** The entry facts survive all three C branches.  They can therefore be
    passed to the actual subsequent EventTaskWait call, rather than being
    assumed afresh at that call. *)
Lemma mutex_pend_inherit_preserves_idle_protocol :
  forall sg before idle eid event mutex owner node base waiter after,
  UCOS2_state_inv sg before ->
  mutex_idle_slot before.(TskState) idle -> mutex_idle_excluded idle before.(EventState) ->
  mutex_owner_event_unlinked before.(TskState) before.(EventState) ->
  before.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> before.(TskState).(inUsedTaskStates) owner = Some node ->
  task_base_priority sg before.(TskState).(prioTbl) owner base ->
  mutex_pend_inherit_step sg before owner node base waiter mutex.(mfPCP) after ->
  UCOS2_state_inv sg after /\ mutex_idle_slot after.(TskState) idle /\
  mutex_idle_excluded idle after.(EventState) /\
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros sg before idle eid event mutex owner node base waiter after Hvalid Hslot Hidle Huse
    He Htype Hm Ho Hnode Hbase Hstep.
  split.
  - eapply mutex_pend_inherit_preserves_validity; try eassumption.
    eapply mutex_owner_non_idle_priority_when_running; eassumption.
  - split.
    + eapply mutex_pend_inherit_preserves_idle_slot; eassumption.
    + split.
      * destruct (mutex_pend_inherit_observations sg before eid event mutex owner node base waiter
          after Hvalid Huse He Htype Hm Ho Hnode Hstep) as [Hevents _].
        rewrite Hevents; exact Hidle.
      * eapply mutex_pend_inherit_preserves_owner_unlinked; eassumption.
Qed.
