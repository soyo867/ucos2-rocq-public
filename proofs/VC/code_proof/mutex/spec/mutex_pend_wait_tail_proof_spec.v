Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_api_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_accept_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_sched_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma mutex_pend_resume_priority_quot_wait_tail : forall sg state eid tid node,
  sem_pend_resume_entry sg state eid tid node ->
  Z.quot node.(curPrio) 8 = node.(curPrio) / 8.
Proof.
  intros * [Hvalid [_ [Hnode _]]].
  pose proof (sem_pend_task_priority_in_range sg state tid node Hvalid Hnode) as Hrange.
  apply Z.quot_div_nonneg; unfold task_priority_in_range in Hrange; lia.
Qed.

Lemma mutex_pend_wait_execution_result_wait_tail : forall owned critical sg original pe before
  eid timeout entered entry current waiting released unmasked scheduled selected resumed
  resume_entry code cleaned returned after,
  mutex_pend_api_prefix pe before eid ->
  sem_pend_modular_call_history owned critical sg original before entered entry ->
  mutex_pend_wait_at sg original entry current eid timeout waiting entered waiting ->
  sem_pend_modular_call_history owned critical sg entered waiting released unmasked ->
  mutex_pend_sched_return (Some owned) critical sg released unmasked scheduled selected ->
  sem_pend_modular_call_history owned critical sg scheduled selected resumed resume_entry ->
  mutex_pend_resume_result sg eid resume_entry code cleaned ->
  sem_pend_modular_call_history owned critical sg resumed cleaned returned after ->
  mutex_pend_api_program (Some owned) critical sg original pe eid timeout before code after /\
  kernel_stack_call_same_call returned original.
Proof.
  intros * Hprefix Hsave Hwait Hrelease Hsched Hresume Hresult Hfinal.
  pose proof Hwait as [Hentered [_ [_ [Hfirst _]]]].
  destruct Hresult as [result [Hcode Hcritical]].
  split.
  - unfold mutex_pend_api_program; rewrite Hprefix.
    exists entered, entry,
      (MutexPendWaiting original.(os_sched_call_stack).(stackLeaseSlot)
        original.(os_sched_call_stack).(stackLeaseGeneration)), waiting, returned.
    split; [exact Hsave|]. split; [exact Hfirst|]. split; [reflexivity|]. split; [reflexivity|].
    exists released, unmasked, scheduled, selected, resumed, resume_entry, result, cleaned.
    split; [exact Hrelease|]. split; [exact Hsched|]. split; [exact Hresume|].
    split; [exact Hcritical|]. split; [exact Hcode|exact Hfinal].
  - pose proof (proj1 (proj2 Hrelease)) as Hreleased.
    pose proof (proj1 (proj2 Hresume)) as Hresumed.
    pose proof (proj1 (proj2 Hfinal)) as Hreturned.
    destruct Hsched as [sched_entered [acquired [sched_resumed [checkpoint [Hs [Hb Hr]]]]]].
    pose proof (proj1 (proj2 Hs)) as Hsched_entered.
    pose proof (os_sched_c_return_execution_identity _ _ _ _ _ _ _ Hb) as Hbody.
    pose proof (proj1 (proj2 Hr)) as Hsched_returned.
    unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence.
Qed.

Lemma mutex_pend_wait_priority_quot_wait_tail : forall sg state eid event tid node,
  mutex_pend_wait_entry sg state eid event tid node ->
  Z.quot node.(curPrio) 8 = node.(curPrio) / 8.
Proof.
  intros * Hentry.
  pose proof (mutex_pend_wait_entry_prio _ _ _ _ _ _ Hentry) as Hrange.
  apply Z.quot_div_nonneg; unfold valid_task_prio in Hrange; lia.
Qed.

Lemma mutex_pend_wait_initial_observation_wait_tail : forall owned critical sg idle
  original entered mask saved before entry eid observed current mutex tid caller inherited timeout,
  mutex_pend_first_snapshot owned critical sg idle original entered mask saved
    before entry eid observed current mutex tid caller ->
  mutex_pend_inherited_snapshot sg entry eid current mutex tid caller inherited ->
  kernel_call_task_source entered inherited ->
  sched_current_consistency inherited.(TskState) inherited.(SchedState) ->
  sem_pend_blocking_call_stage sg entered inherited -> kernel_tcb_stack_field_layout sg ->
  let waiting := event_pend_state sg inherited eid current tid caller PendMutex timeout in
  mutex_pend_wait_at sg original entry current eid timeout waiting entered waiting /\
  sem_pend_wait_sched_entry sg entered waiting /\ UCOS2_state_inv sg waiting.
Proof.
  intros * Hsnapshot Hinherited Hsource Hcache Hstage Hlayout waiting.
  destruct Hsnapshot as [Hhistory [Hsaved [Hrely [Hacquire [Hentry_source [Hnonidle
    [Hunlinked [Hslot [Hexcluded [Hevent Hcaller]]]]]]]]]].
  destruct Hinherited as [owner [Howner [Hinherit Hwait]]].
  pose proof (mutex_pend_wait_entry_prio _ _ _ _ _ _ Hwait) as Hprio.
  pose proof (mutex_pend_wait_entry_resource_conditions _ _ _ _ _ _ Hwait)
    as [Hkind [Hunavailable Hnotowner]].
  pose proof Hwait as [Hvalid [Hcurrent [Hnode [He [Htype [_ [_ [Hnone [Hmulti [Hflag [Hready _]]]]]]]]]]].
  destruct (mutex_pend_event_wait_call_cut sg entered inherited eid current tid caller timeout
    Hvalid He Hcurrent Hnode Hprio Hnone Hmulti Hflag Hready Hkind Hunavailable
    Hnotowner Hsource Hcache Hstage Hlayout) as [Hvalid' [Hentry' Hwait']].
  pose proof Hhistory as [_ [[Hi [Ho Hstack]] Havailable]].
  pose proof (kernel_call_task_source_current_at entered entry Hentry_source)
    as [Hcurrent_entry [old [Hold Hgeneration]]].
  pose proof Hcaller as [Hcurrent_tid [Hcaller_node _]].
  assert (Htid : tid = entered.(os_sched_call_stack).(stackLeaseSlot)) by congruence.
  assert (Hold_eq : old = caller) by (rewrite <- Htid in Hold; congruence).
  subst old; rewrite Hstack in Htid, Hgeneration.
  assert (Horigin : original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration)).
  { pose proof (proj1 Hentry_source) as Horigin; rewrite Ho, Hstack in Horigin; exact Horigin. }
  pose proof Hevent as [Hinitial [Htype_initial [Hmutex _]]].
  assert (Hfirst : mutex_pend_first_critical sg eid timeout entry
    (MutexPendWaiting original.(os_sched_call_stack).(stackLeaseSlot)
      original.(os_sched_call_stack).(stackLeaseGeneration)) waiting).
  { exists current, mutex, tid, caller.
    split; [exact Hinitial|]. split; [exact Htype_initial|]. split; [exact Hmutex|].
    split; [exact Hcurrent_tid|]. split; [exact Hcaller_node|]. rewrite Howner.
    exists inherited, current, caller. split; [exact Hinherit|].
    split; [exact He|]. split; [exact Hnode|]. split; [rewrite Htid, Hgeneration; reflexivity|reflexivity]. }
  split; [|auto]. unfold mutex_pend_wait_at.
  split; [unfold kernel_stack_call_same_call; auto|]. split; [exact Horigin|].
  split; [exact Hinitial|]. split; [exact Hfirst|].
  unfold mutex_pend_wait_state in Hwait' |- *; rewrite Hstack in Hwait'; exact Hwait'.
Qed.
