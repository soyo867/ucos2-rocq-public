Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Event projection of the SAME Save source execution. The physical
    deposit and final take preserve EventState; their Task/SP writes remain
    in kernel_call_save_history. The registered middle trace may have a
    stopped flag, so it is not converted to a flat false-stop interval.
    This observation contains no acquired readiness or wait-stage law. *)
Definition sem_pend_save_event_trace critical sg invocation before acquired : Prop :=
  exists parked returned stopped,
    parked.(EventState) = before.(EventState) /\
    UCOS2_state_inv sg parked /\
    kernel_client_resource_trace critical.(critical_region_clients) sg invocation None
      parked stopped returned /\
    acquired.(EventState) = returned.(EventState).

Definition sem_pend_acquire_observation environment critical sg original returned
  mask saved before acquired eid observed current : Prop :=
  sem_pend_save_call_history environment critical sg original before returned acquired /\
  kernel_stack_call_same_call returned original /\
  interrupt_saved_value mask saved /\ UCOS2_state_inv sg acquired /\
  mutex_query_lookup before eid observed /\ mutex_query_lookup acquired eid current /\
  observed.(eventType) = OS_EVENT_TYPE_SEM /\ current.(eventType) = OS_EVENT_TYPE_SEM /\
  current.(eventGeneration) = observed.(eventGeneration).

Lemma sem_pend_save_event_trace_preserves_handle : forall critical sg invocation
  before acquired eid observed,
  sem_pend_save_event_trace critical sg invocation before acquired ->
  mutex_query_handle_protocol critical sg invocation eid ->
  mutex_query_lookup before eid observed ->
  exists current, mutex_query_lookup acquired eid current /\
    current.(eventGeneration) = observed.(eventGeneration) /\
    current.(eventType) = observed.(eventType).
Proof.
  intros critical sg invocation before acquired eid observed
    [parked [returned [stopped [Hevent [Hvalid [Htrace Hfinal]]]]]] Hprotocol Hlookup.
  assert (Hparked : mutex_query_lookup parked eid observed).
  { unfold mutex_query_lookup in *; rewrite Hevent; exact Hlookup. }
  clear Hlookup Hevent.
  revert observed Hparked Hvalid.
  induction Htrace as
    [state|action state middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intros previous Hprevious Hvalid.
  - exists previous; unfold mutex_query_lookup in *; rewrite Hfinal.
    repeat split; assumption || reflexivity.
  - destruct (Hprotocol action state middle previous Hin Hforeign Hvalid Hstep Hprevious)
      as [next [Hnext [Hgen Htype]]].
    pose proof (kernel_client_preserves_validity action
      (critical_region_client_certificates critical action Hin)
      sg state middle Hvalid Hstep) as Hmiddle.
    destruct (IH Hfinal next Hnext Hmiddle) as [current [Hcurrent [Hgen' Htype']]].
    exists current; split; [exact Hcurrent|]; split; congruence.
Qed.

Lemma sem_pend_save_event_trace_uninterrupted : forall critical sg invocation state,
  UCOS2_state_inv sg state -> sem_pend_save_event_trace critical sg invocation state state.
Proof.
  intros; exists state, state, false; split; [reflexivity|].
  split; [assumption|]. split; [constructor|reflexivity].
Qed.

Lemma sem_pend_source_acquire_observation : forall environment critical sg original returned
  mask saved before acquired eid observed,
  kernel_call_save_history environment critical sg original before returned acquired ->
  sem_pend_save_event_trace critical sg original.(os_sched_call_invocation) before acquired ->
  interrupt_saved_value mask saved -> UCOS2_state_inv sg acquired ->
  mutex_query_handle_protocol critical sg original.(os_sched_call_invocation) eid ->
  mutex_query_lookup before eid observed -> observed.(eventType) = OS_EVENT_TYPE_SEM ->
  exists current, sem_pend_acquire_observation environment critical sg original returned
    mask saved before acquired eid observed current.
Proof.
  intros * Hhistory Hevents Hsaved Hvalid Hprotocol Hlookup Htype.
  destruct (sem_pend_save_event_trace_preserves_handle critical sg
    original.(os_sched_call_invocation) before acquired eid observed Hevents Hprotocol Hlookup)
    as [current [Hcurrent [Hgeneration Hcurrent_type]]].
  exists current; unfold sem_pend_acquire_observation.
  split; [left; exact Hhistory|]. split.
  - eapply kernel_call_save_history_same_call; exact Hhistory.
  - repeat first [assumption | split]; congruence.
Qed.

(** The first literal count read consumes this observation on its current
    heap. Source history provides identity, while UCOS2_inv provides bytes;
    neither is substituted for the other. *)
Lemma sem_pend_acquire_count_split : forall environment critical sg original returned
  mask saved before acquired eid observed current,
  sem_pend_acquire_observation environment critical sg original returned
    mask saved before acquired eid observed current ->
  UCOS2_inv sg acquired |--
  coq_prop (UCOS2_state_inv sg acquired /\ 0 <= encode_event_cnt_value current <= 65535) &&
  ((event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value current **
    sem_post_count_frame sg acquired eid current).
Proof.
  intros * [_ [_ [_ [Hvalid [_ [Hlookup [_ [Htype Hgen]]]]]]]].
  apply sem_post_count_split_full; assumption.
Qed.

