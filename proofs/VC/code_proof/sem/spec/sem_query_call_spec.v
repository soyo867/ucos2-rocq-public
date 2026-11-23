Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.mutex_query_spec.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.lib.event.
Require Export Ucos2Verify.lib.event_pool.
Require Export Ucos2Verify.lib.event_wait.
Require Export Ucos2Verify.lib.array_abstraction.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import ListNotations UCOS2_C_Rules.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The imported lookup, handle protocol, closed region, full Event residual
    and array-copy lemmas are type-independent despite their historical
    mutex_query prefix. No slice-to-full coercion is used. *)
Definition sem_query_public_slot (state : UCOS2_Verify_State)
  (eid : EventID) (observed : OSEventAbstractState) : Prop :=
  mutex_query_lookup state eid observed \/
  (state.(EventState).(inUsedEventStates) eid = None /\
   In eid state.(EventState).(unUsedEventStates)).

(** A public handle can name a live ECB or a recycled free ECB. Private
    creator-owned storage is not manufactured from a bare numerical ID.
    The free case keeps its exact image, all other free images, the public
    map/root, and the full non-Event module frame (including Queue). *)
Definition sem_query_type_frame (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (eid : EventID) : Assertion :=
  match state.(EventState).(inUsedEventStates) eid with
  | Some observed => mutex_query_type_frame sg state eid observed
  | None => EX image : EventStorage,
      coq_prop (state.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image) &&
      (event_storage_without_field sg.(osKernelConfig).(cfgEventNames)
        (event_addr sg eid) image EventTypeField **
       event_free_storage_without_eid sg state.(EventState) eid **
       store_map (used_event_rep sg state.(TskState)) state.(EventState).(inUsedEventStates) **
       event_free_root_rep sg state.(EventState) **
       UCOS2_raw_rep_missing_module sg state EventModule)
  end.

Lemma sem_query_type_split_full : forall sg state eid observed,
  sem_query_public_slot state eid observed ->
  UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state) &&
    ((event_addr sg eid + OSEventType_off) # UChar |->
      event_slot_type_value state.(EventState) eid ** sem_query_type_frame sg state eid).
Proof.
  intros sg state eid observed [Hused|[Hnone Hfree]].
  - unfold sem_query_type_frame, event_slot_type_value.
    unfold mutex_query_lookup in Hused; rewrite Hused.
    apply mutex_query_type_split_full; exact Hused.
  - unfold sem_query_type_frame, event_slot_type_value; rewrite Hnone.
    rewrite (UCOS2_inv_split_module sg state EventModule); Intros.
    match goal with H : UCOS2_state_inv sg state |- _ =>
      pose proof H as [_ [_ [_ [[_ [Hstorage _]] _]]]] end.
    destruct Hstorage as [Hdomain [_ Htype]].
    destruct (proj2 (Hdomain eid) Hfree) as [image Himage].
    cbn [UCOS2_module_rep]; unfold event_raw_rep.
    sep_apply_l_atomic (event_free_storage_split_eid sg state.(EventState) eid image Himage).
    sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
      (event_pool_addr sg eid) image EventTypeField ltac:(simpl; tauto)).
    rewrite (Htype eid image Himage).
    cbn [event_cell event_field_offset].
    Exists image; unfold OSEventType_off, event_addr; entailer!.
Qed.

Lemma sem_query_type_merge_full : forall sg state eid,
  UCOS2_state_inv sg state ->
  (event_addr sg eid + OSEventType_off) # UChar |->
    event_slot_type_value state.(EventState) eid ** sem_query_type_frame sg state eid
  |-- UCOS2_inv sg state.
Proof.
  intros sg state eid Hvalid.
  unfold sem_query_type_frame, event_slot_type_value.
  destruct (state.(EventState).(inUsedEventStates) eid) as [observed|] eqn:Hslot.
  - apply mutex_query_type_merge_full; assumption.
  - Intros image.
    match goal with H : state.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image |- _ =>
      rename H into Himage end.
    pose proof Hvalid as [_ [_ [_ [[_ [Hstorage _]] _]]]].
    assert (Htype : image EventTypeField = Some 0) by (apply (proj2 (proj2 Hstorage) eid image Himage)).
    eapply derivable1_trans with
      (event_cell (event_pool_addr sg eid) EventTypeField (image EventTypeField) **
       event_storage_without_field sg.(osKernelConfig).(cfgEventNames)
         (event_pool_addr sg eid) image EventTypeField **
       event_free_storage_without_eid sg state.(EventState) eid **
       store_map (used_event_rep sg state.(TskState)) state.(EventState).(inUsedEventStates) **
       event_free_root_rep sg state.(EventState) **
       UCOS2_raw_rep_missing_module sg state EventModule).
    { rewrite Htype; cbn [event_cell event_field_offset]; unfold OSEventType_off, event_addr; entailer!. }
    sep_apply_l_atomic (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
      (event_pool_addr sg eid) image EventTypeField ltac:(simpl; tauto)).
    sep_apply_l_atomic (event_free_storage_merge_eid sg state.(EventState) eid image Himage).
    rewrite (UCOS2_inv_split_module sg state EventModule).
    cbn [UCOS2_module_rep]; unfold event_raw_rep; entailer!.
Qed.

Lemma sem_query_public_slot_is_sem : forall state eid observed,
  sem_query_public_slot state eid observed ->
  event_slot_type_value state.(EventState) eid = 3 ->
  mutex_query_lookup state eid observed /\ observed.(eventType) = OS_EVENT_TYPE_SEM.
Proof.
  intros state eid observed [Hused|[Hnone Hfree]] Htype;
    unfold event_slot_type_value in Htype.
  - unfold mutex_query_lookup in Hused; rewrite Hused in Htype.
    split; [exact Hused|].
    destruct observed.(eventType); simpl in Htype; try lia; reflexivity.
  - rewrite Hnone in Htype; discriminate.
Qed.

Definition sem_query_acquire_facts (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (eid : EventID) (mask saved : Z)
  (before entry : UCOS2_Verify_State) (observed current : OSEventAbstractState) : Prop :=
  critical_region_interval critical sg invocation before entry /\
  UCOS2_state_inv sg entry /\ interrupt_saved_value mask saved /\
  mutex_query_lookup before eid observed /\ mutex_query_lookup entry eid current /\
  observed.(eventType) = OS_EVENT_TYPE_SEM /\
  current.(eventType) = OS_EVENT_TYPE_SEM /\
  current.(eventGeneration) = observed.(eventGeneration).

Lemma sem_query_save_consequence :
  forall platform critical sg invocation origin eid mask saved before entry observed,
  mutex_query_handle_protocol critical sg invocation eid ->
  UCOS2_state_inv sg before -> mutex_query_lookup before eid observed ->
  observed.(eventType) = OS_EVENT_TYPE_SEM ->
  critical_region_interval critical sg invocation before entry ->
  interrupt_saved_value mask saved ->
  critical_region_masked platform critical sg invocation origin saved entry **
    UCOS2_raw_rep sg entry |--
  EX current, coq_prop (sem_query_acquire_facts critical sg invocation eid mask saved
    before entry observed current) &&
    (critical_region_masked platform critical sg invocation origin saved entry **
     UCOS2_inv sg entry).
Proof.
  intros platform critical sg invocation origin eid mask saved before entry observed
    Hprotocol Hvalid Hlookup Htype Hinterval Hsaved.
  destruct (mutex_query_handle_interval_preserves_identity critical sg invocation eid
    before entry observed Hprotocol Hinterval Hvalid Hlookup)
    as [current [Hcurrent [Hgeneration HcurrentType]]].
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation before entry Hinterval Hvalid)) as Hentry.
  assert (Hfacts : sem_query_acquire_facts critical sg invocation eid mask saved
    before entry observed current).
  { unfold sem_query_acquire_facts.
    split; [exact Hinterval|]; split; [exact Hentry|]; split; [exact Hsaved|].
    split; [exact Hlookup|]; split; [exact Hcurrent|]; split; [exact Htype|].
    split; [congruence|exact Hgeneration]. }
  Exists current; unfold UCOS2_inv; entailer!.
Qed.

Lemma sem_query_restore_consequence :
  forall platform critical sg invocation origin eid mask saved before entry observed current,
  sem_query_acquire_facts critical sg invocation eid mask saved before entry observed current ->
  interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask saved) **
    critical_region_outside critical sg invocation entry |--
  mutex_query_closed platform critical sg invocation origin mask entry.
Proof.
  intros platform critical sg invocation origin eid mask saved before entry observed current
    [_ [Hentry [[Hsaved Hmask] _]]].
  rewrite Hmask; unfold mutex_query_closed; entailer!.
Qed.

Lemma sem_query_copy_fields_split_full : forall sg entry eid current,
  mutex_query_lookup entry eid current -> current.(eventType) = OS_EVENT_TYPE_SEM ->
  UCOS2_inv sg entry |--
  EX count group table,
    coq_prop (UCOS2_state_inv sg entry /\ mutex_query_copy_snapshot entry eid current count group table) &&
    (interrupt_inv sg entry.(IntrState) **
     (event_addr sg eid + OSEventType_off) # UChar |-> 3 **
     (event_addr sg eid + OSEventCnt_off) # UShort |-> count **
     used_event_rest_no_type_cnt_ptr sg entry.(TskState) (event_addr sg eid) eid current **
     mutex_query_event_unread sg entry.(TskState) eid current **
     mutex_query_raw_frame sg entry eid).
Proof.
  intros sg entry eid current Hlookup Htype.
  rewrite (UCOS2_inv_split_module sg entry InterruptModule); Intros.
  cbn [UCOS2_module_rep]; fold (mutex_query_whole_frame sg entry).
  sep_apply_l_atomic (mutex_query_whole_frame_split_event sg entry eid current Hlookup).
  match goal with Hvalid : UCOS2_state_inv sg entry |- _ =>
    sep_apply_l_atomic (proj1 (mutex_query_event_rep_read_fields_equiv
      sg entry eid current Hvalid Hlookup)) end.
  rewrite Htype; cbn [encode_event_type].
  Exists (encode_event_cnt_value current)
    (encode_event_wait_grp current.(waitList) entry.(TskState))
    (encode_event_wait_tbl_values current entry.(TskState)).
  unfold mutex_query_copy_snapshot; entailer!.
Qed.

Lemma sem_query_copy_fields_merge_full :
  forall sg entry eid current base type_addr count_addr count group table,
  UCOS2_state_inv sg entry ->
  mutex_query_copy_snapshot entry eid current count group table ->
  current.(eventType) = OS_EVENT_TYPE_SEM ->
  base = event_addr sg eid -> type_addr = event_addr sg eid + OSEventType_off ->
  count_addr = event_addr sg eid + OSEventCnt_off ->
  interrupt_inv sg entry.(IntrState) ** type_addr # UChar |-> 3 ** count_addr # UShort |-> count **
    used_event_rest_no_type_cnt_ptr sg entry.(TskState) base eid current **
    mutex_query_event_unread sg entry.(TskState) eid current ** mutex_query_raw_frame sg entry eid
  |-- UCOS2_inv sg entry.
Proof.
  intros sg entry eid current base type_addr count_addr count group table
    Hvalid [Hlookup [Hcount _]] Htype Hbase Htypeaddr Hcntaddr.
  rewrite Hbase, Htypeaddr, Hcntaddr, Hcount.
  pose proof (proj2 (mutex_query_event_rep_read_fields_equiv sg entry eid current Hvalid Hlookup))
    as Hmerge.
  rewrite Htype in Hmerge; cbn [encode_event_type] in Hmerge.
  sep_apply_l_atomic Hmerge.
  sep_apply_l_atomic (mutex_query_frame_merge_inv sg entry eid current Hvalid Hlookup).
  entailer!.
Qed.


Lemma sem_query_encoded_type_is_sem : forall observed,
  encode_event_type observed.(eventType) = 3 -> observed.(eventType) = OS_EVENT_TYPE_SEM.
Proof. intros observed H; destruct observed.(eventType); simpl in H; try lia; reflexivity. Qed.

(** OSSemQuery has no ISR rejection. Null guards precede the type read;
    only the sem arm acquires a fresh protected snapshot. *)
Definition sem_query_call_input (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pevent pdata : addr)
  (before : UCOS2_Verify_State) (eid : EventID) (observed : OSEventAbstractState) : Prop :=
  pevent = 0 \/ (pevent <> 0 /\ pdata = 0) \/
  (pevent <> 0 /\ pdata <> 0 /\ pevent = event_addr sg eid /\ valid_event_id sg eid /\
   sem_query_public_slot before eid observed /\
   (event_slot_type_value before.(EventState) eid = 3 ->
    mutex_query_handle_protocol critical sg invocation eid)).

Definition sem_query_call_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pevent pdata : addr)
  : program UCOS2_Verify_State Z :=
  fun before code after =>
    (pevent = 0 /\ code = 4 /\ after = before) \/
    (pevent <> 0 /\ pdata = 0 /\ code = 9 /\ after = before) \/
    (pevent <> 0 /\ pdata <> 0 /\
     exists eid observed,
       pevent = event_addr sg eid /\ valid_event_id sg eid /\
       sem_query_public_slot before eid observed /\
       ((event_slot_type_value before.(EventState) eid <> 3 /\ code = 1 /\ after = before) \/
        (mutex_query_lookup before eid observed /\ observed.(eventType) = OS_EVENT_TYPE_SEM /\ exists entry current,
         critical_region_interval critical sg invocation before entry /\
         mutex_query_lookup entry eid current /\ current.(eventType) = OS_EVENT_TYPE_SEM /\
         current.(eventGeneration) = observed.(eventGeneration) /\ code = 0 /\ after = entry))).

Definition sem_query_call_post_prop critical sg invocation pevent pdata before code after : Prop :=
  sem_query_call_program critical sg invocation pevent pdata before code after.

Definition sem_query_observe_error (code : Z) : program (UCOS2_Verify_State -> Prop) Z :=
  StateRelMonad.ret code.

Lemma sem_query_call_input_live : forall critical sg invocation pevent pdata before eid observed,
  sem_query_call_input critical sg invocation pevent pdata before eid observed ->
  pevent <> 0 -> pdata <> 0 ->
  pevent = event_addr sg eid /\ valid_event_id sg eid /\ sem_query_public_slot before eid observed /\
  (event_slot_type_value before.(EventState) eid = 3 -> mutex_query_handle_protocol critical sg invocation eid).
Proof.
  intros critical sg invocation pevent pdata before eid observed [Hnull|[[_ Hnull]|[_ [_ Hlive]]]] Hpe Hpd;
    try contradiction; exact Hlive.
Qed.

Lemma sem_query_call_success :
  forall critical sg invocation pevent pdata before eid observed mask saved entry current,
  pevent <> 0 -> pdata <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_acquire_facts critical sg invocation eid mask saved before entry observed current ->
  sem_query_call_program critical sg invocation pevent pdata before 0 entry.
Proof.
  intros critical sg invocation pevent pdata before eid observed mask saved entry current
    Hpe Hpd Haddr Hid [Hinterval [Hvalid [Hsaved [Hbefore [Hlookup [Htype [Hcurrent Hgen]]]]]]].
  right; right; split; [exact Hpe|]; split; [exact Hpd|].
  exists eid, observed; split; [exact Haddr|]; split; [exact Hid|]; split; [left; exact Hbefore|].
  right; split; [exact Hbefore|]; split; [exact Htype|]; exists entry, current;
    repeat split; assumption || reflexivity.
Qed.

Lemma sem_query_call_null_event_return : forall critical sg invocation pdata before,
  sem_query_call_program critical sg invocation 0 pdata before 4 before.
Proof. intros; left; auto. Qed.

Lemma sem_query_call_null_data_return : forall critical sg invocation pevent before,
  pevent <> 0 -> sem_query_call_program critical sg invocation pevent 0 before 9 before.
Proof. intros; right; left; auto. Qed.

Lemma sem_query_call_wrong_type_return : forall critical sg invocation pevent pdata before eid observed,
  pevent <> 0 -> pdata <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed -> event_slot_type_value before.(EventState) eid <> 3 ->
  sem_query_call_program critical sg invocation pevent pdata before 1 before.
Proof.
  intros critical sg invocation pevent pdata before eid observed Hpe Hpd Haddr Hid Hlookup Htype.
  right; right; split; [exact Hpe|]; split; [exact Hpd|].
  exists eid, observed; split; [exact Haddr|]; split; [exact Hid|]; split; [exact Hlookup|].
  left; auto.
Qed.

Lemma sem_query_safe_return : forall (c : program UCOS2_Verify_State Z) before after error X,
  c before error after ->
  safeExec (LastSeen before) (bind (atomic_cmd c) sem_query_observe_error) X ->
  safeExec (LastSeen after) (StateRelMonad.ret error) X.
Proof.
  intros c before after error X Hsem Hexec.
  assert (Hatomic : hs_eval (atomic_cmd c) (LastSeen before) (LastSeen after) error).
  { unfold hs_eval, LastSeen, atomic_cmd; intros P0 HP0.
    exists (RTrans_Abs after); split.
    - exists before, after; split; [apply HP0; exact I|].
      split; [exact Hsem|intro state; split; trivial].
    - intro state; split; trivial. }
  exact (highstepbind_derive _ _ _ error (LastSeen after) Hatomic X Hexec).
Qed.

Definition sem_query_output_fields (pdata count group : Z) : Assertion :=
  (&(pdata # "os_sem_data" ->ₛ "OSCnt")) # UShort |-> count **
  (&(pdata # "os_sem_data" ->ₛ "OSEventGrp")) # UChar |-> group.

(** Query writes, but never reads, the caller's output buffer. The prefix
    is initialized by this invocation; the untouched suffix remains real
    undefined byte ownership rather than invented initial values. *)
Definition sem_query_output_table (base : addr) (table : list Z) (i : Z) : Assertion :=
  UCharArray.seg base 0 i (firstn (Z.to_nat i) table) **
  UCharArray.undef_seg base i OS_EVENT_TBL_SIZE.

Definition sem_query_output_table_missing_i (base : addr) (table : list Z) (i : Z) : Assertion :=
  UCharArray.seg base 0 i (firstn (Z.to_nat i) table) **
  UCharArray.undef_seg base (i + 1) OS_EVENT_TBL_SIZE.

Lemma sem_query_output_table_init : forall base table,
  UCharArray.undef_full base OS_EVENT_TBL_SIZE |-- sem_query_output_table base table 0.
Proof.
  intros; unfold sem_query_output_table; cbn [Z.to_nat firstn].
  sep_apply_l_atomic (UCharArray.undef_full_to_undef_seg base OS_EVENT_TBL_SIZE).
  unfold UCharArray.seg, store_array_rec; entailer!.
Qed.

Lemma sem_query_output_table_split : forall base table i,
  0 <= i < OS_EVENT_TBL_SIZE ->
  sem_query_output_table base table i |--
    (base + i) # UChar |->_ ** sem_query_output_table_missing_i base table i.
Proof.
  intros base table i Hi; unfold sem_query_output_table, sem_query_output_table_missing_i.
  rewrite UCharArray.undef_seg_unfold by lia.
  unfold StoreUCharAsElement.undefstoreA; rewrite sizeof_uchar.
  replace (base + i * 1) with (base + i) by lia; entailer!.
Qed.

Lemma sem_query_table_prefix_step : forall table i,
  0 <= i < Zlength table ->
  firstn (Z.to_nat (i + 1)) table = firstn (Z.to_nat i) table ++ [Znth i table 0].
Proof.
  intros table i Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  unfold Znth.
  assert (Hprefix : forall (n : nat) (xs : list Z),
    (n < List.length xs)%nat -> firstn (S n) xs = firstn n xs ++ [nth n xs 0]).
  { induction n; intros [|x xs] Hn; cbn in *; try lia; [reflexivity|].
    f_equal; apply IHn; lia. }
  apply Hprefix; rewrite Zlength_correct in Hi; lia.
Qed.

Lemma sem_query_output_table_merge : forall base table i,
  0 <= i < Zlength table ->
  (base + i) # UChar |-> Znth i table 0 ** sem_query_output_table_missing_i base table i
  |-- sem_query_output_table base table (i + 1).
Proof.
  intros base table i Hi; unfold sem_query_output_table, sem_query_output_table_missing_i.
  assert (Hcell : (base + i) # UChar |-> Znth i table 0 |--
    StoreUCharAsElement.storeA base i (Znth i table 0)).
  { unfold StoreUCharAsElement.storeA; rewrite sizeof_uchar.
    replace (base + i * 1) with (base + i) by lia; reflexivity. }
  sep_apply_l_atomic Hcell.
  sep_apply_l_atomic (UCharArray.seg_single base i (Znth i table 0)).
  sep_apply_l_atomic (UCharArray.seg_merge_to_seg base 0 i (i + 1)
    (firstn (Z.to_nat i) table) [Znth i table 0] ltac:(lia)).
  rewrite sem_query_table_prefix_step by exact Hi; entailer!.
Qed.

Lemma sem_query_output_table_complete : forall base table i,
  Zlength table = OS_EVENT_TBL_SIZE -> i = OS_EVENT_TBL_SIZE ->
  sem_query_output_table base table i |-- store_osprio_array base table.
Proof.
  intros base table i Hlen ->; unfold sem_query_output_table.
  rewrite firstn_all2 by (rewrite Zlength_correct in Hlen; unfold OS_EVENT_TBL_SIZE in *; lia).
  rewrite UCharArray.undef_seg_empty.
  sep_apply_l_atomic (UCharArray.seg_to_full base 0 OS_EVENT_TBL_SIZE table).
  unfold UCharArray.full, StoreUCharAsElement.sizeA, store_osprio_array, oseventtbl_element_store,
    StoreUCharAsElement.storeA, sizeof_OS_PRIO.
  rewrite sizeof_uchar.
  replace (base + 0 * 1) with base by lia.
  replace (OS_EVENT_TBL_SIZE - 0) with OS_EVENT_TBL_SIZE by lia; entailer!.
Qed.

(** Count is kept as an explicit cell outside this loop frame: the source
    reads it only after copying the bitmap. Caller output-count ownership is
    likewise retained separately, until that final assignment. *)
Definition sem_query_copy_frame (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask saved : Z)
  (before entry : UCOS2_Verify_State) (eid : EventID)
  (observed current : OSEventAbstractState) (pdata count group : Z)
  (table : list Z) : Assertion :=
  coq_prop (sem_query_acquire_facts critical sg invocation eid mask saved
    before entry observed current /\ mutex_query_copy_snapshot entry eid current count group table) &&
  (critical_region_masked platform critical sg invocation origin saved entry **
   interrupt_inv sg entry.(IntrState) ** mutex_query_raw_frame sg entry eid **
   mutex_query_event_unread sg entry.(TskState) eid current **
   (event_addr sg eid + OSEventType_off) # UChar |-> 3 **
   (event_addr sg eid + OSEventGrp_off) # UChar |-> group **
   (&(pdata # "os_sem_data" ->ₛ "OSEventGrp")) # UChar |-> group).

Lemma sem_query_copy_frame_restore :
  forall platform critical sg invocation origin mask saved before entry eid observed current
    pdata count group table base count_addr,
  base = event_addr sg eid -> count_addr = event_addr sg eid + OSEventCnt_off ->
  sem_query_copy_frame platform critical sg invocation origin mask saved
    before entry eid observed current pdata count group table ** store_oseventtbl sg base table **
    count_addr # UShort |-> count ** (&(pdata # "os_sem_data" ->ₛ "OSCnt")) # UShort |-> count |--
  coq_prop (sem_query_acquire_facts critical sg invocation eid mask saved before entry observed current /\
    mutex_query_copy_snapshot entry eid current count group table) &&
  (critical_region_masked platform critical sg invocation origin saved entry **
   UCOS2_inv sg entry ** sem_query_output_fields pdata count group).
Proof.
  intros platform critical sg invocation origin mask saved before entry eid observed current
    pdata count group table base count_addr Hbase Hcount.
  unfold sem_query_copy_frame; Intros.
  assert (Hfacts : sem_query_acquire_facts critical sg invocation eid mask saved
    before entry observed current) by tauto.
  assert (Hsnapshot : mutex_query_copy_snapshot entry eid current count group table) by tauto.
  pose proof Hfacts as [_ [Hvalid [_ [_ [_ [_ [Htype _]]]]]]].
  sep_apply_l_atomic (mutex_query_copy_table_group_merge sg entry eid current base
    (event_addr sg eid + OSEventGrp_off) count group table Hsnapshot Hbase eq_refl).
  sep_apply_l_atomic (sem_query_copy_fields_merge_full sg entry eid current base
    (event_addr sg eid + OSEventType_off) count_addr
    count group table Hvalid Hsnapshot Htype Hbase eq_refl Hcount).
  unfold sem_query_output_fields; entailer!.
Qed.
