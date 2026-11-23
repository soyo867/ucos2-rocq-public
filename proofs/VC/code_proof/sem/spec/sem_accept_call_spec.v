Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.sem.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.

Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Save/Restore-aware relation for OSSemAccept. The Event type is observed
    before Save, but [count] and the concrete Event image are selected from
    the post-Save entry state. *) 
Definition sem_accept_call_relation
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (eid : EventID) (etype : Z)
  (before : UCOS2_Verify_State) (e_before e_entry : OSEventAbstractState)
  (count : Z) (after : UCOS2_Verify_State) : Prop :=
  exists entry,
    critical_region_interval critical sg invocation before entry /\
    before.(EventState).(inUsedEventStates) eid = Some e_before /\
    entry.(EventState).(inUsedEventStates) eid = Some e_entry /\
    e_before.(eventType) = OS_EVENT_TYPE_SEM /\
    e_entry.(eventType) = OS_EVENT_TYPE_SEM /\
    e_entry.(eventGeneration) = e_before.(eventGeneration) /\
    etype = encode_event_type e_before.(eventType) /\
    sem_accept_critical sg eid entry count after.

Lemma sem_accept_call_preserves_validity :
  forall critical sg invocation eid etype before e_before e_entry count after,
  UCOS2_state_inv sg before ->
  sem_accept_call_relation critical sg invocation eid etype before e_before e_entry count after ->
  UCOS2_state_inv sg after.
Proof.
  intros critical sg invocation eid etype before e_before e_entry count after Hvalid Hrel.
  destruct Hrel as [entry [Hinterval [Hbefore [Hlookup
    [HbeforeType [HentryType [Hgeneration [Htype Hcritical]]]]]]]].
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation before entry Hinterval Hvalid)) as Hentry.
  eapply sem_accept_critical_preserves_validity; eassumption.
Qed.

Lemma sem_accept_call_result_in_range :
  forall critical sg invocation eid etype before e_before e_entry count after,
  UCOS2_state_inv sg before ->
  sem_accept_call_relation critical sg invocation eid etype before e_before e_entry count after ->
  0 <= count <= 65535.
Proof.
  intros critical sg invocation eid etype before e_before e_entry count after Hvalid Hrel.
  destruct Hrel as [entry [Hinterval [Hbefore [Hlookup
    [HbeforeType [HentryType [Hgeneration [Htype Hcritical]]]]]]]].
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation before entry Hinterval Hvalid)) as Hentry.
  eapply sem_accept_critical_result_in_range; eassumption.
Qed.

(** A live handle excludes deletion/reuse of that instance while this call
    can resume. It does NOT freeze its count, waiters or the rest of the OS.
    This is an explicit application/client protocol, not a CPU guarantee. *)
Definition sem_accept_handle_protocol (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (eid : EventID) : Prop :=
  forall action before after previous,
    critical_region_clients critical action ->
    kernel_client_actor action <> Some invocation ->
    UCOS2_state_inv sg before ->
    kernel_client_step action sg before after ->
    before.(EventState).(inUsedEventStates) eid = Some previous ->
    exists current,
      after.(EventState).(inUsedEventStates) eid = Some current /\
      current.(eventGeneration) = previous.(eventGeneration) /\
      current.(eventType) = previous.(eventType).

Lemma sem_accept_handle_interval_preserves_identity :
  forall critical sg invocation eid before after previous,
  sem_accept_handle_protocol critical sg invocation eid ->
  critical_region_interval critical sg invocation before after ->
  UCOS2_state_inv sg before ->
  before.(EventState).(inUsedEventStates) eid = Some previous ->
  exists current,
    after.(EventState).(inUsedEventStates) eid = Some current /\
    current.(eventGeneration) = previous.(eventGeneration) /\
    current.(eventType) = previous.(eventType).
Proof.
  intros critical sg invocation eid before after previous Hprotocol Hinterval.
  apply critical_region_interval_raw_trace in Hinterval.
  revert previous.
  induction Hinterval as
    [s|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intros previous Hvalid Hlookup.
  - exists previous; repeat split; assumption || reflexivity.
  - destruct (Hprotocol action before middle previous Hin Hforeign Hvalid Hstep Hlookup)
      as [next [Hnext [Hgeneration Htype]]].
    pose proof (kernel_client_preserves_validity action
      (critical_region_client_certificates critical action Hin)
      sg before middle Hvalid Hstep) as Hmiddle.
    destruct (IH next Hmiddle Hnext) as [current [Hcurrent [Hgen Htyp]]].
    exists current; split; [exact Hcurrent|]; split; congruence.
Qed.

Lemma sem_accept_critical_client_preserves_handle :
  forall actor target count sg before after eid previous,
  kernel_client_step (sem_accept_critical_client actor target count) sg before after ->
  before.(EventState).(inUsedEventStates) eid = Some previous ->
  exists current,
    after.(EventState).(inUsedEventStates) eid = Some current /\
    current.(eventGeneration) = previous.(eventGeneration) /\
    current.(eventType) = previous.(eventType).
Proof.
  intros actor target count sg before after eid previous [node [Hnode [Htype Hstep]]] Hlookup.
  eapply sem_accept_critical_preserves_event_identity; eassumption.
Qed.

Definition sem_accept_acquire_facts (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (eid : EventID) (mask saved : Z)
  (before entry : UCOS2_Verify_State) (observed current : OSEventAbstractState) : Prop :=
  critical_region_interval critical sg invocation before entry /\
  UCOS2_state_inv sg entry /\ interrupt_saved_value mask saved /\
  before.(EventState).(inUsedEventStates) eid = Some observed /\
  entry.(EventState).(inUsedEventStates) eid = Some current /\
  observed.(eventType) = OS_EVENT_TYPE_SEM /\
  current.(eventType) = OS_EVENT_TYPE_SEM /\
  current.(eventGeneration) = observed.(eventGeneration).

Lemma sem_accept_save_consequence :
  forall critical sg invocation eid mask saved before entry observed,
  sem_accept_handle_protocol critical sg invocation eid ->
  UCOS2_state_inv sg before ->
  before.(EventState).(inUsedEventStates) eid = Some observed ->
  observed.(eventType) = OS_EVENT_TYPE_SEM ->
  critical_region_interval critical sg invocation before entry ->
  interrupt_saved_value mask saved ->
  UCOS2_raw_rep sg entry |--
    EX current,
      coq_prop (sem_accept_acquire_facts critical sg invocation eid mask saved
        before entry observed current) && UCOS2_inv sg entry.
Proof.
  intros critical sg invocation eid mask saved before entry observed
    Hprotocol Hvalid Hlookup Htype Hinterval Hsaved.
  destruct (sem_accept_handle_interval_preserves_identity
    critical sg invocation eid before entry observed Hprotocol Hinterval Hvalid Hlookup)
    as [current [Hcurrent [Hgeneration HcurrentType]]].
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation before entry Hinterval Hvalid)) as Hentry.
  assert (Hfacts : sem_accept_acquire_facts critical sg invocation eid mask saved
    before entry observed current).
  { unfold sem_accept_acquire_facts.
    split; [exact Hinterval|]; split; [exact Hentry|].
    split; [exact Hsaved|]; split; [exact Hlookup|].
    split; [exact Hcurrent|]; split; [exact Htype|].
    split; [congruence|exact Hgeneration]. }
  Exists current; unfold UCOS2_inv; entailer!.
Qed.

(** The raw count is selected from the entry acquired by Save, never from
    the earlier type observation. No validity premise is placed in this
    executable transformer. *)
Definition sem_accept_checkpoint (entry : UCOS2_Verify_State)
  (eid : EventID) (current : OSEventAbstractState) : UCOS2_Verify_State :=
  let count := encode_event_cnt_value current in
  if Z.ltb 0 count then sem_count_update_state entry eid current (count - 1)
  else entry.

Lemma sem_accept_checkpoint_critical : forall sg entry eid current,
  UCOS2_state_inv sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some current ->
  current.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_accept_critical sg eid entry (encode_event_cnt_value current)
    (sem_accept_checkpoint entry eid current).
Proof.
  intros sg entry eid current Hvalid Hlookup Htype.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  specialize (Hpayload eid current Hlookup).
  unfold event_payload_consistency in Hpayload; rewrite Htype in Hpayload.
  destruct current.(semFields) as [fields|] eqn:Hfields; [|contradiction].
  exists current, fields; split; [exact Hlookup|]; split; [exact Hfields|].
  unfold sem_accept_checkpoint, encode_event_cnt_value; rewrite Htype, Hfields.
  split; reflexivity.
Qed.

Lemma sem_accept_checkpoint_preserves_validity : forall sg entry eid current,
  UCOS2_state_inv sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some current ->
  current.(eventType) = OS_EVENT_TYPE_SEM ->
  UCOS2_state_inv sg (sem_accept_checkpoint entry eid current).
Proof.
  intros sg entry eid current Hvalid Hlookup Htype.
  eapply sem_accept_critical_preserves_validity; try eassumption.
  eapply sem_accept_checkpoint_critical; eassumption.
Qed.

Definition sem_accept_closed (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (state : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg state) &&
    (interrupt_platform_running platform invocation origin mask **
     critical_region_outside critical sg invocation state).

Lemma sem_accept_closed_equiv : forall platform critical sg invocation origin mask state,
  sem_accept_closed platform critical sg invocation origin mask state --||--
    (interrupt_platform_running platform invocation origin mask ** UCOS2_inv sg state).
Proof.
  intros; unfold sem_accept_closed, critical_region_outside.
  rewrite critical_region_outside_without_running_rep.
  rewrite <- UCOS2_raw_rep_split_running.
  unfold UCOS2_inv; split; entailer!.
Qed.

(** The following is the ACTUAL Restore input: saved token and masked
    region plus an already reconstructed full invariant. Restore is not
    responsible for proving the semaphore update preserves that invariant. *)
Definition sem_accept_restore_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (saved : Z)
  (entry : UCOS2_Verify_State) (eid : EventID) (current : OSEventAbstractState)
  : Assertion :=
  critical_region_masked platform critical sg invocation origin saved entry **
  UCOS2_inv sg (sem_accept_checkpoint entry eid current).

Lemma sem_accept_restore_pre_exposes_saved_token :
  forall platform critical sg invocation origin saved entry eid current,
  sem_accept_restore_pre platform critical sg invocation origin saved entry eid current --||--
    (interrupt_platform_running platform invocation origin 192 **
     interrupt_platform_saved platform (save_token saved invocation origin) **
     critical_region_inside critical sg invocation entry **
     UCOS2_inv sg (sem_accept_checkpoint entry eid current)).
Proof.
  intros; unfold sem_accept_restore_pre, critical_region_masked; split; entailer!.
Qed.

Definition sem_accept_type_frame (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (eid : EventID) (observed : OSEventAbstractState) : Assertion :=
  event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_image sg state.(TskState) observed) EventTypeField **
  event_raw_rep_no_eid sg state.(TskState) state.(EventState) eid **
  queue_storage_rep sg state.(EventState) ** UCOS2_raw_rep_missing_event_queue sg state.

Lemma sem_accept_type_split_full : forall sg state eid observed,
  state.(EventState).(inUsedEventStates) eid = Some observed ->
  UCOS2_inv sg state |--
    coq_prop (UCOS2_state_inv sg state) &&
    ((event_addr sg eid + OSEventType_off) # UChar |-> encode_event_type observed.(eventType) **
     sem_accept_type_frame sg state eid observed).
Proof.
  intros sg state eid observed Hlookup.
  rewrite UCOS2_inv_split_event_queue; Intros.
  sep_apply_l_atomic (event_raw_rep_split_eid sg state.(TskState) state.(EventState)
    eid observed Hlookup).
  unfold used_event_rep.
  sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg state.(TskState) observed) EventTypeField ltac:(simpl; tauto)).
  cbn [event_image event_cell event_field_offset].
  unfold sem_accept_type_frame, OSEventType_off; entailer!.
Qed.

Lemma sem_accept_type_merge_full : forall sg state eid observed,
  UCOS2_state_inv sg state ->
  state.(EventState).(inUsedEventStates) eid = Some observed ->
  (event_addr sg eid + OSEventType_off) # UChar |-> encode_event_type observed.(eventType) **
    sem_accept_type_frame sg state eid observed |-- UCOS2_inv sg state.
Proof.
  intros sg state eid observed Hvalid Hlookup.
  unfold sem_accept_type_frame.
  eapply derivable1_trans with (event_cell (event_addr sg eid) EventTypeField
      ((event_image sg state.(TskState) observed) EventTypeField) **
    event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
      (event_image sg state.(TskState) observed) EventTypeField **
    event_raw_rep_no_eid sg state.(TskState) state.(EventState) eid **
    queue_storage_rep sg state.(EventState) ** UCOS2_raw_rep_missing_event_queue sg state).
  { cbn [event_image event_cell event_field_offset]; unfold OSEventType_off; entailer!. }
  sep_apply_l_atomic (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg state.(TskState) observed) EventTypeField ltac:(simpl; tauto)).
  fold (used_event_rep sg state.(TskState) eid observed).
  sep_apply_l_atomic (event_raw_rep_merge_eid sg state.(TskState) state.(EventState)
    eid observed Hlookup).
  rewrite UCOS2_inv_split_event_queue; entailer!.
Qed.

Definition sem_accept_count_frame (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (eid : EventID) (current : OSEventAbstractState) : Assertion :=
  sem_rep_no_count sg entry.(TskState) eid current **
  event_raw_rep_no_eid sg entry.(TskState) entry.(EventState) eid **
  queue_storage_rep sg entry.(EventState) ** UCOS2_raw_rep_missing_event_queue sg entry.

Lemma sem_accept_count_split_full : forall sg entry eid current,
  entry.(EventState).(inUsedEventStates) eid = Some current ->
  current.(eventType) = OS_EVENT_TYPE_SEM ->
  UCOS2_inv sg entry |--
    coq_prop (UCOS2_state_inv sg entry /\ 0 <= encode_event_cnt_value current <= 65535) &&
    ((event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value current **
     sem_accept_count_frame sg entry eid current).
Proof.
  intros sg entry eid current Hlookup Htype.
  rewrite UCOS2_inv_split_event_queue; Intros.
  match goal with Hvalid : UCOS2_state_inv sg entry |- _ =>
    pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]] end.
  specialize (Hpayload eid current Hlookup).
  unfold event_payload_consistency in Hpayload; rewrite Htype in Hpayload.
  destruct current.(semFields) as [fields|] eqn:Hfields; [|contradiction].
  assert (Hcount : encode_event_cnt_value current = fields.(semCount)).
  { unfold encode_event_cnt_value; rewrite Htype, Hfields; reflexivity. }
  sep_apply_l_atomic (event_raw_rep_split_eid sg entry.(TskState) entry.(EventState)
    eid current Hlookup).
  sep_apply_l_atomic (sem_rep_split_count sg entry.(TskState) eid current fields Htype Hfields).
  rewrite Hcount; unfold sem_accept_count_frame.
  destruct Hpayload as [Hrange Hwait]; entailer!.
Qed.

Definition sem_accept_stored_count (current : OSEventAbstractState) : Z :=
  let count := encode_event_cnt_value current in
  if Z.ltb 0 count then count - 1 else count.

Lemma sem_accept_count_merge_checkpoint : forall sg entry eid current,
  UCOS2_state_inv sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some current ->
  current.(eventType) = OS_EVENT_TYPE_SEM ->
  (event_addr sg eid + OSEventCnt_off) # UShort |-> sem_accept_stored_count current **
    sem_accept_count_frame sg entry eid current |--
    UCOS2_inv sg (sem_accept_checkpoint entry eid current).
Proof.
  intros sg entry eid current Hvalid Hlookup Htype.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  specialize (Hpayload eid current Hlookup).
  unfold event_payload_consistency in Hpayload; rewrite Htype in Hpayload.
  destruct current.(semFields) as [fields|] eqn:Hfields; [|contradiction].
  assert (Hcount : encode_event_cnt_value current = fields.(semCount)).
  { unfold encode_event_cnt_value; rewrite Htype, Hfields; reflexivity. }
  unfold sem_accept_stored_count, sem_accept_checkpoint, sem_accept_count_frame.
  rewrite Hcount; destruct (Z.ltb 0 fields.(semCount)) eqn:Hpositive.
  - assert (Hupdated : sem_fields_consistency current.(waitList)
      {| semCount := fields.(semCount) - 1 |}).
    { apply sem_decrement_preserves_consistency; [exact Hpayload|].
      apply Z.ltb_lt; exact Hpositive. }
    sep_apply_l_atomic (UCOS2_inv_merge_sem_count sg entry eid current
      (fields.(semCount) - 1) Hvalid Hlookup Htype Hupdated); entailer!.
  - sep_apply_l_atomic (sem_rep_merge_count sg entry.(TskState) eid current fields Htype Hfields).
    sep_apply_l_atomic (event_raw_rep_merge_eid sg entry.(TskState) entry.(EventState)
      eid current Hlookup).
    rewrite UCOS2_inv_split_event_queue; entailer!.
Qed.

(** Nullable and wrong-type returns remain actual public branches. The
    protected branch observes a fresh entry, with only instance identity
    transported from the earlier type read. *)
Definition sem_accept_call_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pevent : addr)
  : program UCOS2_Verify_State Z :=
  fun before count after =>
    (pevent = 0 /\ count = 0 /\ after = before) \/
    (pevent <> 0 /\ exists eid observed,
      pevent = event_addr sg eid /\ valid_event_id sg eid /\
      before.(EventState).(inUsedEventStates) eid = Some observed /\
      ((observed.(eventType) <> OS_EVENT_TYPE_SEM /\ count = 0 /\ after = before) \/
       (observed.(eventType) = OS_EVENT_TYPE_SEM /\ exists entry current,
        critical_region_interval critical sg invocation before entry /\
        entry.(EventState).(inUsedEventStates) eid = Some current /\
        current.(eventType) = OS_EVENT_TYPE_SEM /\
        current.(eventGeneration) = observed.(eventGeneration) /\
        sem_accept_critical sg eid entry count after))).

Definition sem_accept_lookup (state : UCOS2_Verify_State) (eid : EventID)
  (node : OSEventAbstractState) : Prop :=
  state.(EventState).(inUsedEventStates) eid = Some node.

Definition sem_accept_call_post_prop (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pevent : addr)
  (before : UCOS2_Verify_State) (count : Z) (after : UCOS2_Verify_State) : Prop :=
  sem_accept_call_program critical sg invocation pevent before count after.

Definition sem_accept_call_input (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pevent : addr)
  (before : UCOS2_Verify_State) (eid : EventID) (observed : OSEventAbstractState) : Prop :=
  pevent = 0 \/
  (pevent <> 0 /\ pevent = event_addr sg eid /\ valid_event_id sg eid /\
    before.(EventState).(inUsedEventStates) eid = Some observed /\
    (observed.(eventType) = OS_EVENT_TYPE_SEM ->
      sem_accept_handle_protocol critical sg invocation eid)).

Lemma sem_accept_call_null_return : forall critical sg invocation before,
  sem_accept_call_program critical sg invocation 0 before 0 before.
Proof. intros; left; auto. Qed.

Lemma sem_accept_call_wrong_type_return : forall critical sg invocation pevent before eid observed,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  before.(EventState).(inUsedEventStates) eid = Some observed ->
  observed.(eventType) <> OS_EVENT_TYPE_SEM ->
  sem_accept_call_program critical sg invocation pevent before 0 before.
Proof.
  intros critical sg invocation pevent before eid observed Hnonzero Haddr Hid Hlookup Htype.
  right; split; [exact Hnonzero|]; exists eid, observed.
  split; [exact Haddr|]; split; [exact Hid|]; split; [exact Hlookup|].
  left; auto.
Qed.

Lemma sem_accept_call_checkpoint_return :
  forall critical sg invocation pevent before eid observed mask saved entry current,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_accept_acquire_facts critical sg invocation eid mask saved before entry observed current ->
  sem_accept_call_program critical sg invocation pevent before
    (encode_event_cnt_value current) (sem_accept_checkpoint entry eid current).
Proof.
  intros critical sg invocation pevent before eid observed mask saved entry current
    Hnonzero Haddr Hid [Hinterval [Hvalid [Hsaved [Hbefore [Hlookup [Htype [Hcurrent Hgen]]]]]]].
  right; split; [exact Hnonzero|]; exists eid, observed.
  split; [exact Haddr|]; split; [exact Hid|]; split; [exact Hbefore|].
  right; split; [exact Htype|]; exists entry, current.
  split; [exact Hinterval|]; split; [exact Hlookup|]; split; [exact Hcurrent|].
  split; [exact Hgen|]; apply sem_accept_checkpoint_critical; assumption.
Qed.

Lemma sem_accept_call_program_preserves_validity :
  forall critical sg invocation pevent before count after,
  UCOS2_state_inv sg before ->
  sem_accept_call_program critical sg invocation pevent before count after ->
  UCOS2_state_inv sg after.
Proof.
  intros critical sg invocation pevent before count after Hvalid
    [[_ [_ ->]]|[_ [eid [observed [_ [_ [Hlookup Hbranch]]]]]]]; [exact Hvalid|].
  destruct Hbranch as [[_ [_ ->]]|[Htype [entry [current
    [Hinterval [Hentry [Hcurrent [Hgen Hstep]]]]]]]]; [exact Hvalid|].
  eapply sem_accept_critical_preserves_validity; [|exact Hentry|exact Hcurrent|exact Hstep].
  exact (proj1 (critical_region_interval_transports_resources
    critical sg invocation before entry Hinterval Hvalid)).
Qed.

Definition sem_accept_call_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (pevent : addr) (before : UCOS2_Verify_State) (count : Z) : Assertion :=
  EX after, coq_prop (sem_accept_call_program critical sg invocation pevent before count after) &&
    sem_accept_closed platform critical sg invocation origin mask after.

Lemma sem_accept_restore_consequence :
  forall platform critical sg invocation origin pevent before eid observed mask saved entry current,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_accept_acquire_facts critical sg invocation eid mask saved before entry observed current ->
  interrupt_platform_running platform invocation origin mask **
    critical_region_outside critical sg invocation (sem_accept_checkpoint entry eid current) |--
    sem_accept_call_post platform critical sg invocation origin mask pevent before
      (encode_event_cnt_value current).
Proof.
  intros platform critical sg invocation origin pevent before eid observed mask saved entry current
    Hnonzero Haddr Hid Hfacts.
  pose proof (sem_accept_call_checkpoint_return critical sg invocation pevent before
    eid observed mask saved entry current Hnonzero Haddr Hid Hfacts) as Hreturn.
  destruct Hfacts as [Hinterval [Hentry [Hsaved [Hbefore [Hlookup [Htype [Hcurrent Hgen]]]]]]].
  pose proof (sem_accept_checkpoint_preserves_validity sg entry eid current Hentry Hlookup Hcurrent)
    as Hafter.
  unfold sem_accept_call_post; Exists (sem_accept_checkpoint entry eid current).
  unfold sem_accept_closed; entailer!.
Qed.
