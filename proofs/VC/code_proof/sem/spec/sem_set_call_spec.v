Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Export Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Export Ucos2Verify.lib.sem.
Require Import Ucos2Verify.lib.queue_core.
Import ListNotations UCOS2_C_Rules.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition sem_set_error_cell (p : addr) : Assertion := p # UChar |->_ .

(** The reused public-slot, type split/merge and acquisition protocol are
    type-independent/SEM-specific resource facts, not Query API semantics.
    Full raw Event, Queue and other module ownership is retained throughout.
    The common unmasked ownership and CPU/CSL interfaces remain conditional. *)
Definition sem_set_call_input (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pevent : addr)
  (before : UCOS2_Verify_State) (eid : EventID) (observed : OSEventAbstractState) : Prop :=
  pevent = 0 \/
  (pevent <> 0 /\ pevent = event_addr sg eid /\ valid_event_id sg eid /\
   sem_query_public_slot before eid observed /\
   (event_slot_type_value before.(EventState) eid = 3 ->
    mutex_query_handle_protocol critical sg invocation eid)).

Definition sem_set_can_write (entry : UCOS2_Verify_State)
  (current : OSEventAbstractState) : bool :=
  (Z.ltb 0 (encode_event_cnt_value current) ||
   Z.eqb (encode_event_wait_grp current.(waitList) entry.(TskState)) 0)%bool.

Definition sem_set_checkpoint (entry : UCOS2_Verify_State) (eid : EventID)
  (current : OSEventAbstractState) (count : Z) : UCOS2_Verify_State :=
  if sem_set_can_write entry current then sem_count_update_state entry eid current count else entry.

Definition sem_set_error (entry : UCOS2_Verify_State) (current : OSEventAbstractState) : Z :=
  if sem_set_can_write entry current then 0 else 73.

Definition sem_set_stored_count (entry : UCOS2_Verify_State)
  (current : OSEventAbstractState) (count : Z) : Z :=
  if sem_set_can_write entry current then count else encode_event_cnt_value current.

(** Bind the generated group address only on actual acquired states whose
    zero-count arm reads the group byte. Wrong-type and positive-count arms
    do not consume a group layout premise. *)
Definition sem_set_group_read_layout (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (before : UCOS2_Verify_State)
  (eid : EventID) (group_addr : addr) : Prop :=
  forall entry current,
    critical_region_interval critical sg invocation before entry ->
    mutex_query_lookup entry eid current -> encode_event_cnt_value current <= 0 ->
    group_addr = event_addr sg eid + OSEventGrp_off.

(** V2.93.01: NULL, then type, then Save; no ISR or perr guard in the
    selected non-safety-critical profile. All decisions inside Save use its
    fresh entry, not the earlier unmasked type snapshot. *)
Definition sem_set_call_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pevent count : Z)
  : program UCOS2_Verify_State Z :=
  fun before code after =>
    (pevent = 0 /\ code = 4 /\ after = before) \/
    (pevent <> 0 /\ exists eid observed,
     pevent = event_addr sg eid /\ valid_event_id sg eid /\
     sem_query_public_slot before eid observed /\
     ((event_slot_type_value before.(EventState) eid <> 3 /\ code = 1 /\ after = before) \/
      (mutex_query_lookup before eid observed /\ observed.(eventType) = OS_EVENT_TYPE_SEM /\
       exists entry current,
         critical_region_interval critical sg invocation before entry /\
         mutex_query_lookup entry eid current /\ current.(eventType) = OS_EVENT_TYPE_SEM /\
         current.(eventGeneration) = observed.(eventGeneration) /\
         code = sem_set_error entry current /\
         after = sem_set_checkpoint entry eid current count))).

Definition sem_set_call_post_prop critical sg invocation pevent count before code after : Prop :=
  sem_set_call_program critical sg invocation pevent count before code after.

Lemma sem_set_call_input_nonnull : forall critical sg invocation pevent before eid observed,
  sem_set_call_input critical sg invocation pevent before eid observed -> pevent <> 0 ->
  pevent = event_addr sg eid /\ valid_event_id sg eid /\
  sem_query_public_slot before eid observed /\
  (event_slot_type_value before.(EventState) eid = 3 ->
   mutex_query_handle_protocol critical sg invocation eid).
Proof. intros * [Hnull|[_ Hlive]] Hnonzero; [contradiction|exact Hlive]. Qed.

Lemma sem_set_call_null_return : forall critical sg invocation count before,
  sem_set_call_program critical sg invocation 0 count before 4 before.
Proof. intros; left; auto. Qed.

Lemma sem_set_call_wrong_type_return : forall critical sg invocation pevent count before eid observed,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed -> event_slot_type_value before.(EventState) eid <> 3 ->
  sem_set_call_program critical sg invocation pevent count before 1 before.
Proof.
  intros * Hnonzero Haddr Hid Hslot Htype; right; split; [exact Hnonzero|].
  exists eid, observed; split; [exact Haddr|]; split; [exact Hid|]; split; [exact Hslot|].
  left; auto.
Qed.

Lemma sem_set_call_checkpoint_return :
  forall critical sg invocation pevent count before eid observed mask saved entry current,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_acquire_facts critical sg invocation eid mask saved before entry observed current ->
  sem_set_call_program critical sg invocation pevent count before
    (sem_set_error entry current) (sem_set_checkpoint entry eid current count).
Proof.
  intros * Hnonzero Haddr Hid
    [Hinterval [Hvalid [Hsaved [Hbefore [Hlookup [Htype [Hcurrent Hgen]]]]]]].
  right; split; [exact Hnonzero|]; exists eid, observed.
  split; [exact Haddr|]; split; [exact Hid|]; split; [left; exact Hbefore|].
  right; split; [exact Hbefore|]; split; [exact Htype|]; exists entry, current.
  repeat split; assumption || reflexivity.
Qed.

Lemma sem_set_wait_group_zero_implies_empty : forall sg tasks waiters,
  event_waitList_canonical sg tasks waiters ->
  encode_event_wait_grp waiters tasks = 0 -> waiters = [].
Proof.
  intros sg tasks [|tid rest] Hcanonical Hgrp; [reflexivity|].
  destruct Hcanonical as [_ [_ Hrange]].
  destruct (Hrange tid ltac:(left; reflexivity)) as [t [Hget Hprio]].
  cbn in Hgrp; rewrite Hget in Hgrp.
  apply Z.lor_eq_0_iff in Hgrp; destruct Hgrp as [Hbit _].
  rewrite Z.shiftl_1_l in Hbit; unfold valid_task_prio in Hprio.
  assert (Hnonnegative : 0 <= t.(curPrio) / 8) by (apply Z_div_nonneg_nonneg; lia).
  pose proof (Z.pow_pos_nonneg 2 (t.(curPrio) / 8) ltac:(lia) Hnonnegative); lia.
Qed.

Lemma sem_set_write_preserves_payload : forall sg entry eid current count,
  UCOS2_state_inv sg entry -> mutex_query_lookup entry eid current ->
  current.(eventType) = OS_EVENT_TYPE_SEM -> 0 <= count <= 65535 ->
  sem_set_can_write entry current = true ->
  sem_fields_consistency current.(waitList) {| semCount := count |}.
Proof.
  intros sg entry eid current count Hvalid Hlookup Htype Hcount Hwrite.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload [_ Hentries]]]]]] _]]]].
  specialize (Hpayload eid current Hlookup).
  specialize (Hentries eid current Hlookup).
  unfold event_payload_consistency in Hpayload; rewrite Htype in Hpayload.
  destruct current.(semFields) as [fields|] eqn:Hfields; [|contradiction].
  assert (Hempty : current.(waitList) = []).
  { unfold sem_set_can_write in Hwrite; apply Bool.orb_true_iff in Hwrite.
    destruct Hwrite as [Hpositive|Hgroup].
    - apply Z.ltb_lt in Hpositive; unfold encode_event_cnt_value in Hpositive;
        rewrite Htype, Hfields in Hpositive.
      eapply sem_positive_count_no_waiters; eassumption.
    - apply Z.eqb_eq in Hgroup; eapply sem_set_wait_group_zero_implies_empty;
        [exact (proj1 Hentries)|exact Hgroup]. }
  unfold sem_fields_consistency; split; [exact Hcount|intros H; contradiction].
Qed.

Lemma sem_set_checkpoint_preserves_validity : forall sg entry eid current count,
  UCOS2_state_inv sg entry -> mutex_query_lookup entry eid current ->
  current.(eventType) = OS_EVENT_TYPE_SEM -> 0 <= count <= 65535 ->
  UCOS2_state_inv sg (sem_set_checkpoint entry eid current count).
Proof.
  intros sg entry eid current count Hvalid Hlookup Htype Hcount.
  unfold sem_set_checkpoint; destruct (sem_set_can_write entry current) eqn:Hwrite; [|exact Hvalid].
  eapply UCOS2_sem_count_update_preserves_validity; try eassumption.
  eapply sem_set_write_preserves_payload; eassumption.
Qed.

Definition sem_set_count_frame (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (eid : EventID) (current : OSEventAbstractState) : Assertion :=
  sem_rep_no_count sg entry.(TskState) eid current **
  event_raw_rep_no_eid sg entry.(TskState) entry.(EventState) eid **
  queue_storage_rep sg entry.(EventState) ** UCOS2_raw_rep_missing_event_queue sg entry.

Lemma sem_set_count_split_full : forall sg entry eid current,
  mutex_query_lookup entry eid current -> current.(eventType) = OS_EVENT_TYPE_SEM ->
  UCOS2_inv sg entry |--
    coq_prop (UCOS2_state_inv sg entry /\ 0 <= encode_event_cnt_value current <= 65535) &&
    ((event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value current **
     sem_set_count_frame sg entry eid current).
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
  rewrite Hcount; unfold sem_set_count_frame; destruct Hpayload as [Hrange Hwait]; entailer!.
Qed.

Definition sem_set_group_frame (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (eid : EventID) (current : OSEventAbstractState) : Assertion :=
  EventFieldStorage.store_fields EventField_eq_dec (event_cell (event_addr sg eid))
    (remove EventField_eq_dec EventGrpField
      (remove EventField_eq_dec EventCntField (event_fields sg.(osKernelConfig).(cfgEventNames))))
    (event_image sg entry.(TskState) current) **
  event_raw_rep_no_eid sg entry.(TskState) entry.(EventState) eid **
  queue_storage_rep sg entry.(EventState) ** UCOS2_raw_rep_missing_event_queue sg entry.

Lemma sem_set_fields_without_count_nodup : forall named,
  NoDup (remove EventField_eq_dec EventCntField (event_fields named)).
Proof.
  intros named; pose proof (event_fields_nodup named) as Hnd.
  induction Hnd as [|field fields Hnot Hnd IH]; [constructor|].
  change (NoDup (if EventField_eq_dec EventCntField field
    then remove EventField_eq_dec EventCntField fields
    else field :: remove EventField_eq_dec EventCntField fields)).
  destruct (EventField_eq_dec EventCntField field); [exact IH|].
  constructor; [|exact IH].
  intro Hin; apply Hnot; apply in_remove in Hin; tauto.
Qed.

Lemma sem_set_group_split : forall sg entry eid current,
  sem_set_count_frame sg entry eid current |--
  (event_addr sg eid + OSEventGrp_off) # UChar |->
    encode_event_wait_grp current.(waitList) entry.(TskState) **
  sem_set_group_frame sg entry eid current.
Proof.
  intros; unfold sem_set_count_frame, sem_set_group_frame, sem_rep_no_count,
    event_storage_without_field.
  sep_apply_l_atomic (EventFieldStorage.store_fields_split_field _ _ EventField_eq_dec
    (event_cell (event_addr sg eid))
    (remove EventField_eq_dec EventCntField (event_fields sg.(osKernelConfig).(cfgEventNames)))
    (event_image sg entry.(TskState) current) EventGrpField
    (sem_set_fields_without_count_nodup _) ltac:(simpl; tauto)).
  cbn [event_cell event_field_offset event_image]; unfold OSEventGrp_off; entailer!.
Qed.

Lemma sem_set_group_merge : forall sg entry eid current,
  (event_addr sg eid + OSEventGrp_off) # UChar |->
    encode_event_wait_grp current.(waitList) entry.(TskState) **
  sem_set_group_frame sg entry eid current |-- sem_set_count_frame sg entry eid current.
Proof.
  intros; unfold sem_set_count_frame, sem_set_group_frame, sem_rep_no_count,
    event_storage_without_field.
  pose proof (EventFieldStorage.store_fields_merge_field _ _ EventField_eq_dec
    (event_cell (event_addr sg eid))
    (remove EventField_eq_dec EventCntField (event_fields sg.(osKernelConfig).(cfgEventNames)))
    (event_image sg entry.(TskState) current) EventGrpField
    (sem_set_fields_without_count_nodup _) ltac:(simpl; tauto)) as Hmerge.
  cbn [event_cell event_field_offset event_image] in Hmerge.
  unfold OSEventGrp_off; sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma sem_set_count_merge_checkpoint : forall sg entry eid current count,
  UCOS2_state_inv sg entry -> mutex_query_lookup entry eid current ->
  current.(eventType) = OS_EVENT_TYPE_SEM -> 0 <= count <= 65535 ->
  (event_addr sg eid + OSEventCnt_off) # UShort |-> sem_set_stored_count entry current count **
    sem_set_count_frame sg entry eid current |--
  UCOS2_inv sg (sem_set_checkpoint entry eid current count).
Proof.
  intros sg entry eid current count Hvalid Hlookup Htype Hcount.
  unfold sem_set_stored_count, sem_set_checkpoint, sem_set_count_frame.
  destruct (sem_set_can_write entry current) eqn:Hwrite.
  - pose proof (sem_set_write_preserves_payload sg entry eid current count
      Hvalid Hlookup Htype Hcount Hwrite) as Hpayload.
    sep_apply_l_atomic (UCOS2_inv_merge_sem_count sg entry eid current count
      Hvalid Hlookup Htype Hpayload); entailer!.
  - pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
    specialize (Hpayload eid current Hlookup).
    unfold event_payload_consistency in Hpayload; rewrite Htype in Hpayload.
    destruct current.(semFields) as [fields|] eqn:Hfields; [|contradiction].
    unfold encode_event_cnt_value; rewrite Htype, Hfields.
    sep_apply_l_atomic (sem_rep_merge_count sg entry.(TskState) eid current fields Htype Hfields).
    sep_apply_l_atomic (event_raw_rep_merge_eid sg entry.(TskState) entry.(EventState)
      eid current Hlookup).
    rewrite UCOS2_inv_split_event_queue; entailer!.
Qed.

Lemma sem_set_restore_consequence :
  forall platform critical sg invocation origin eid mask saved before entry observed current count,
  sem_query_acquire_facts critical sg invocation eid mask saved before entry observed current ->
  0 <= count <= 65535 ->
  interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask saved) **
    critical_region_outside critical sg invocation (sem_set_checkpoint entry eid current count) |--
  mutex_query_closed platform critical sg invocation origin mask (sem_set_checkpoint entry eid current count).
Proof.
  intros platform critical sg invocation origin eid mask saved before entry observed current count
    [_ [Hvalid [[Hsaved Hmask] [_ [Hlookup [_ [Htype _]]]]]]] Hcount.
  pose proof (sem_set_checkpoint_preserves_validity sg entry eid current count
    Hvalid Hlookup Htype Hcount) as Hafter.
  rewrite Hmask; unfold mutex_query_closed; entailer!.
Qed.
