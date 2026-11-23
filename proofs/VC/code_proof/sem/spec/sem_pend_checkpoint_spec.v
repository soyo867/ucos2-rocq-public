Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.lib.kernel_runtime_inv.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_task_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_acquire_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The no-stack branch retains its declared nonblocking domain. An owned
    Task call instead carries the source Save history and the semaphore
    incarnation observed on the actual acquired world. *)
Definition sem_pend_optional_acquire_observation environment critical sg original returned
  mask saved before acquired eid observed current : Prop :=
  match environment with
  | Some owned => sem_pend_acquire_observation owned critical sg original returned
      mask saved before acquired eid observed current
  | None => kernel_stack_call_same_call returned original /\ sem_query_acquire_facts critical sg
      original.(os_sched_call_invocation) eid mask saved before acquired observed current
  end.

Lemma sem_pend_optional_acquire_fields : forall environment critical sg original returned
  mask saved before acquired eid observed current,
  sem_pend_optional_acquire_observation environment critical sg original returned
    mask saved before acquired eid observed current ->
  kernel_stack_call_same_call returned original /\ interrupt_saved_value mask saved /\
  UCOS2_state_inv sg acquired /\ mutex_query_lookup before eid observed /\
  mutex_query_lookup acquired eid current /\ observed.(eventType) = OS_EVENT_TYPE_SEM /\
  current.(eventType) = OS_EVENT_TYPE_SEM /\ current.(eventGeneration) = observed.(eventGeneration).
Proof.
  intros [owned|] critical sg original returned mask saved before acquired eid observed current H.
  - exact (proj2 H).
  - destruct H as [Hsame [Hinterval [Hvalid [Hsaved Hfields]]]].
    split; [exact Hsame|].
    repeat first [assumption | split]; tauto.
Qed.

(** The no-stack input keeps its old nonblocking protocol. For owned
    calls the same requirement ranges over actual returning Save paths;
    it contains no readiness or future-success assumption. *)
Definition sem_pend_observed_nonblocking environment critical sg context before eid : Prop :=
  match environment with
  | None => sem_pend_nonblocking_acquire critical sg context before eid
  | Some owned => forall returned mask saved acquired observed current,
      sem_pend_acquire_observation owned critical sg context returned mask saved
        before acquired eid observed current -> 0 < encode_event_cnt_value current
  end.

Definition sem_pend_observed_admission environment critical sg context pevent before eid : Prop :=
  sem_pend_precritical_error pevent (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  (sem_pend_task_call_stage sg context before /\
   match environment with
   | Some _ => kernel_running_idle_ready sg before /\
       kernel_call_stack_available context before
   | None => True
   end) \/
    sem_pend_observed_nonblocking environment critical sg context before eid.

(** Only a normal Task call which may actually block consumes the
    initialized C runtime and active execution observations. Early errors
    do not reach this implication; the alternative nonblocking protocol
    and the no-capsule domain retain their previous obligations. This is
    an explicit correction of the former incomplete blocking admission. *)

(** Address metadata is consumed on the actual zero-count acquisition.
    This corrects the old formula's restricted flat-interval quantifier;
    it is intentionally not claimed equivalent to that old formula. *)
Definition sem_pend_observed_blocking_layout environment critical sg context before eid
  gcur ggrp gtbl : Prop :=
  forall returned mask saved acquired observed current,
    sem_pend_optional_acquire_observation environment critical sg context returned
      mask saved before acquired eid observed current ->
    encode_event_cnt_value current = 0 ->
    gcur = sg.(g_OSTCBCur) /\ ggrp = sg.(g_OSRdyGrp) /\ gtbl = sg.(g_OSRdyTbl) /\
    event_object_layout_prop sg eid.

Definition sem_pend_observed_wait_origin environment critical sg context returned mask saved before observed
  entry eid current tid old : Prop :=
  sem_pend_optional_acquire_observation environment critical sg context returned mask saved
    before entry eid observed current /\
  sem_pend_wait_entry sg entry eid current tid old /\
  context.(os_sched_call_origin) = RunningInvocation tid old.(taskGeneration) /\
  kernel_call_task_source context entry /\
  sched_current_consistency entry.(TskState) entry.(SchedState).

Definition sem_pend_observed_wait_history environment critical sg context mask before observed
  eid timeout waiting : Prop :=
  UCOS2_state_inv sg waiting /\ kernel_call_task_source context waiting /\
  sched_current_consistency waiting.(TskState) waiting.(SchedState) /\
  exists saved returned entry current tid old,
    sem_pend_observed_wait_origin environment critical sg context returned mask saved before observed
      entry eid current tid old /\
    waiting = event_pend_state sg entry eid current tid old PendSem timeout.

Definition sem_pend_observed_resume_origin environment critical sg context mask before observed
  eid timeout resumed tid old : Prop :=
  sem_pend_resume_entry sg resumed eid tid old /\
  context.(os_sched_call_origin) = RunningInvocation tid old.(taskGeneration) /\
  exists owned waiting,
    environment = Some owned /\
    sem_pend_observed_wait_history environment critical sg context mask before observed eid timeout waiting /\
    sem_pend_wait_source_history owned critical sg context eid old.(taskGeneration) waiting resumed.

Definition sem_pend_observed_cleanup_origin environment critical sg context mask before observed
  eid timeout error cleaning tid node : Prop :=
  sem_pend_cleanup_entry sg cleaning tid node /\
  exists resumed old code,
    sem_pend_observed_resume_origin environment critical sg context mask before observed
      eid timeout resumed tid old /\
    error = encode_os_err_code code /\
    sem_pend_resume_critical sg eid resumed code (event_pend_cleanup_state sg false cleaning tid node).

(** Exact semaphore operation before its final Restore. Other-task work
    is represented by the actual acquisition and segmented wait source,
    while the operation's count/wait/cleanup mutations remain exact. Early
    argument errors stay in the existing ordered error relation. *)
Definition sem_pend_checkpoint_result environment critical sg context pevent timeout before error checkpoint : Prop :=
  exists eid observed returned mask saved entry current start waiting,
    pevent <> 0 /\ pevent = event_addr sg eid /\ valid_event_id sg eid /\
    sem_query_public_slot before eid observed /\
    sem_pend_context_error (event_slot_type_value before.(EventState) eid)
      before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None /\
    sem_pend_optional_acquire_observation environment critical sg context returned
      mask saved before entry eid observed current /\
    sem_pend_first_critical sg eid timeout entry start waiting /\
    match start with
    | SemPendAcquired => error = 0 /\ checkpoint = waiting
    | SemPendWaiting tid generation =>
        context.(os_sched_call_origin) = RunningInvocation tid generation /\
        exists owned resumed node code,
          environment = Some owned /\
          sem_pend_wait_source_history owned critical sg context eid generation waiting resumed /\
          sem_pend_resume_entry sg resumed eid tid node /\ node.(taskGeneration) = generation /\
          error = encode_os_err_code code /\ sem_pend_resume_critical sg eid resumed code checkpoint
    end.

Lemma sem_pend_observed_immediate_result : forall environment critical sg context returned pevent timeout
  before eid observed mask saved entry current,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  sem_pend_optional_acquire_observation environment critical sg context returned mask saved
    before entry eid observed current ->
  0 < encode_event_cnt_value current ->
  sem_pend_checkpoint_result environment critical sg context pevent timeout before 0
    (sem_count_update_state entry eid current (encode_event_cnt_value current - 1)).
Proof.
  intros * Hnonnull Haddr Hid Hslot Hcontext Hacquire Hpositive.
  pose proof (sem_pend_optional_acquire_fields _ _ _ _ _ _ _ _ _ _ _ _ Hacquire)
    as [_ [_ [Hvalid [_ [Hlookup [_ [Htype _]]]]]]].
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  specialize (Hpayload eid current Hlookup); unfold event_payload_consistency in Hpayload.
  rewrite Htype in Hpayload; destruct current.(semFields) as [fields|] eqn:Hfields; [|contradiction].
  assert (Hcount : encode_event_cnt_value current = fields.(semCount)).
  { unfold encode_event_cnt_value; rewrite Htype, Hfields; reflexivity. }
  exists eid, observed, returned, mask, saved, entry, current, SemPendAcquired,
    (sem_count_update_state entry eid current (encode_event_cnt_value current - 1)).
  split; [exact Hnonnull|]. split; [exact Haddr|]. split; [exact Hid|]. split; [exact Hslot|].
  split; [exact Hcontext|]. split; [exact Hacquire|]. split.
  - rewrite Hcount; eapply sem_pend_immediate_first_critical; eauto; lia.
  - auto.
Qed.

Lemma sem_pend_observed_wait_origin_history : forall environment critical sg context returned mask saved
  before observed entry eid current tid old timeout,
  sem_pend_observed_wait_origin environment critical sg context returned mask saved before observed
    entry eid current tid old ->
  sem_pend_observed_wait_history environment critical sg context mask before observed eid timeout
    (event_pend_state sg entry eid current tid old PendSem timeout).
Proof.
  intros * Horigin.
  pose proof Horigin as [Hacquire [Hentry [Horiginal [Hsource Hcache]]]].
  destruct (sem_pend_wait_preserves_call_source sg context entry eid current tid old timeout
    Hentry Hsource Hcache) as [Hvalid [Hwaiting Hwaiting_cache]].
  split; [exact Hvalid|]. split; [exact Hwaiting|]. split; [exact Hwaiting_cache|].
  exists saved, returned, entry, current, tid, old; split; [exact Horigin|reflexivity].
Qed.

Lemma sem_pend_observed_wait_history_waiter : forall environment critical sg context mask before observed
  eid timeout waiting,
  sem_pend_observed_wait_history environment critical sg context mask before observed eid timeout waiting ->
  exists node,
    waiting.(TskState).(inUsedTaskStates) context.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
    sem_pend_wait_continuation eid context.(os_sched_call_stack).(stackLeaseGeneration) node.
Proof.
  intros * [_ [Hsource [_ [saved [returned [entry [current [tid [old [Horigin ->]]]]]]]]]].
  destruct Horigin as [_ [Hentry [Horiginal [Hentry_source Hcache]]]].
  pose proof (proj1 Hentry_source) as Hlease.
  rewrite Horiginal in Hlease.
  assert (Htid : tid = context.(os_sched_call_stack).(stackLeaseSlot)) by congruence.
  assert (Hgeneration : old.(taskGeneration) = context.(os_sched_call_stack).(stackLeaseGeneration))
    by congruence.
  subst tid.
  pose proof Hentry as [Hvalid [_ [_ [Hold [_ [_ [_ [_ [Hmulti [Hflag [Hready _]]]]]]]]]]].
  pose proof Hvalid as [_ [_ [[Hrdy Hmeta] _]]].
  destruct (proj1 Hrdy _ Hready) as [found [Hfound [_ Heffective]]].
  assert (found = old) by congruence; subst found.
  exists (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)); split.
  - cbn [event_pend_state event_wait_state replace_TskS replace_SchedS replace_EventS
      TskState glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
  - rewrite <- Hgeneration. apply sem_pend_wait_establishes_continuation; assumption.
Qed.

Lemma sem_pend_observed_resume_cleanup_without_timeout : forall environment critical sg context mask
  before observed eid timeout resumed tid old,
  sem_pend_observed_resume_origin environment critical sg context mask before observed eid timeout resumed tid old ->
  old.(statPend) <> PendTimeout ->
  sem_pend_observed_cleanup_origin environment critical sg context mask before observed eid timeout
    (encode_os_err_code (sem_pend_resume_error (encode_pend_status old.(statPend)))) resumed tid old.
Proof.
  intros * Horigin Hnotimeout.
  pose proof Horigin as [[Hvalid [Hcur [Hold [[Hmulti [Hflag Hregistration]] Hready]]]] Hhistory].
  split.
  - unfold sem_pend_cleanup_entry.
    split; [exact Hvalid|]. split; [exact Hcur|]. split; [exact Hold|].
    split; [destruct old.(statPend); assumption || contradiction|].
    split; [exact Hmulti|]. split; assumption.
  - exists resumed, old, (sem_pend_resume_error (encode_pend_status old.(statPend))).
    split; [exact Horigin|]. split; [reflexivity|].
    exists tid, old; split; [exact Hcur|]. split; [exact Hold|]. split; [reflexivity|].
    destruct old.(statPend); reflexivity || contradiction.
Qed.

Lemma sem_pend_observed_resume_cleanup_timeout : forall environment critical sg context mask
  before observed eid timeout resumed tid old current,
  sem_pend_observed_resume_origin environment critical sg context mask before observed eid timeout resumed tid old ->
  old.(statPend) = PendTimeout -> mutex_query_lookup resumed eid current ->
  sem_pend_observed_cleanup_origin environment critical sg context mask before observed eid timeout 10
    (event_task_remove_state resumed eid current tid old) tid (task_set_event_ptr old None).
Proof.
  intros * Horigin Htimeout He.
  pose proof Horigin as [[Hvalid [Hcur [Hold [[Hmulti [Hflag Hregistration]] Hready]]]] Hhistory].
  rewrite Htimeout in Hregistration.
  destruct (sem_pend_resume_timeout_event sg resumed eid tid old Hvalid Hold Hregistration)
    as [found [Hfound Hin]].
  assert (found = current) by congruence; subst found; split.
  - unfold sem_pend_cleanup_entry; split.
    + eapply UCOS2_event_task_remove_preserves_validity; eassumption.
    + split; [exact Hcur|]. split.
      * cbn [event_task_remove_state replace_TskS replace_EventS TskState glob_task_set_usedtask inUsedTaskStates].
        rewrite Z.eqb_refl; reflexivity.
      * split; [reflexivity|]. split; [exact Hmulti|]. split; assumption.
  - exists resumed, old, OS_ERR_TIMEOUT; split; [exact Horigin|]. split; [reflexivity|].
    exists tid, old; split; [exact Hcur|]. split; [exact Hold|].
    rewrite Htimeout; split; [reflexivity|]. exists current; auto.
Qed.

Lemma sem_pend_observed_cleanup_result : forall environment critical sg context mask before observed eid
  pevent timeout error cleaning tid node,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  sem_pend_observed_cleanup_origin environment critical sg context mask before observed eid timeout
    error cleaning tid node ->
  sem_pend_checkpoint_result environment critical sg context pevent timeout before error
    (event_pend_cleanup_state sg false cleaning tid node).
Proof.
  intros * Hnonzero Haddr Hid Hslot Hcontext [Hclean [resumed [old [code [Hresume [Herror Hstep]]]]]].
  destruct Hresume as [Hresume [Horigin [owned [waiting [Howned [Hhistory Hpath]]]]]].
  destruct Hhistory as [Hwaiting [HwaitingSource [HwaitingCache
    [saved [returned [entry [current [first_tid [first [HfirstOrigin HwaitingEq]]]]]]]]]].
  destruct HfirstOrigin as [Hacquire [Hentry [HfirstOrigin [HfirstSource HfirstCache]]]].
  assert (Hsame : first_tid = tid /\ first.(taskGeneration) = old.(taskGeneration))
    by (rewrite Horigin in HfirstOrigin; inversion HfirstOrigin; auto).
  destruct Hsame as [-> Hgeneration].
  exists eid, observed, returned, mask, saved, entry, current,
    (SemPendWaiting tid first.(taskGeneration)), waiting.
  split; [exact Hnonzero|]. split; [exact Haddr|]. split; [exact Hid|]. split; [exact Hslot|].
  split; [exact Hcontext|]. split; [exact Hacquire|]. split.
  - rewrite HwaitingEq; apply sem_pend_wait_entry_first_critical; exact Hentry.
  - split; [exact HfirstOrigin|]. exists owned, resumed, old, code.
    split; [exact Howned|]. split; [rewrite Hgeneration; exact Hpath|].
    split; [exact Hresume|]. split; [symmetry; exact Hgeneration|]. split; assumption.
Qed.
