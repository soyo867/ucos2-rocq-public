Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import Coq.Strings.String.
Require Export Ucos2Verify.lib.mutex_query_spec.
Require Export Ucos2Verify.lib.mbox.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.lib.event.
Require Export Ucos2Verify.lib.event_pool.
Require Export Ucos2Verify.lib.event_wait.
Require Export Ucos2Verify.lib.array_abstraction.
From SimpleC.SL Require Import Mem SeparationLogic MapLib ArrayLib.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import ListNotations UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** V2.93.01 OSMboxQuery, selected eight-row ABI.  The output observes
    the message pointer only; it never owns the application message. *)
Record MboxQuerySnapshot := {
  mbox_query_message : addr;
  mbox_query_wait_rows : list Z;
  mbox_query_wait_group : Z
}.

Definition mbox_query_snapshot (tasks : Glob_TaskAbstractState)
  (node : OSEventAbstractState) (message : MboxFields) : MboxQuerySnapshot :=
  {| mbox_query_message := mbox_message_ptr message;
     mbox_query_wait_rows := encode_event_wait_tbl_values_or node tasks;
     mbox_query_wait_group := encode_event_wait_grp node.(waitList) tasks |}.

Definition mbox_query_critical (eid : EventID)
  : program UCOS2_Verify_State MboxQuerySnapshot :=
  fun entry snapshot after => after = entry /\ exists node message,
    mutex_query_lookup entry eid node /\ node.(eventType) = OS_EVENT_TYPE_MBOX /\
    node.(mboxFields) = Some message /\
    snapshot = mbox_query_snapshot entry.(TskState) node message.

Definition mbox_query_public_slot (state : UCOS2_Verify_State)
  (eid : EventID) (observed : OSEventAbstractState) : Prop :=
  mutex_query_lookup state eid observed \/
  (state.(EventState).(inUsedEventStates) eid = None /\
   In eid state.(EventState).(unUsedEventStates)).

Definition mbox_query_call_input (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pe pd : addr)
  (before : UCOS2_Verify_State) (eid : EventID) (observed : OSEventAbstractState) : Prop :=
  pe = 0 \/ (pe <> 0 /\ pd = 0) \/
  (pe <> 0 /\ pd <> 0 /\ pe = event_addr sg eid /\ valid_event_id sg eid /\
   mbox_query_public_slot before eid observed /\
   (event_slot_type_value before.(EventState) eid = 1 ->
    mutex_query_handle_protocol critical sg invocation eid)).

(** Existing caller lifetime rely, restricted to the arm which acquires.
    This producer uses the actual registered Task lifecycle action family;
    clients that modify Events must establish the same existing protocol.
    It is not an additional CPU promise or a payload-stability assumption. *)
Lemma mbox_query_handle_protocol_task_creation_clients :
  forall critical sg invocation eid,
  (forall action, critical_region_clients critical action ->
    task_creation_client_family action) ->
  mutex_query_handle_protocol critical sg invocation eid.
Proof.
  intros critical sg invocation eid Hclients action before after previous
    Hin Hforeign Hvalid Hstep Hlookup.
  destruct (Hclients action Hin) as [source ->].
  destruct Hstep as [_ [_ ->]].
  exists previous; destruct source; repeat split; assumption || reflexivity.
Qed.

Definition mbox_query_type_frame (sg : StableGlobVars) (state : UCOS2_Verify_State)
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

Lemma mbox_query_type_split_full : forall sg state eid observed,
  mbox_query_public_slot state eid observed ->
  UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state) &&
    ((event_addr sg eid + OSEventType_off) # UChar |->
      event_slot_type_value state.(EventState) eid ** mbox_query_type_frame sg state eid).
Proof.
  intros sg state eid observed [Hused|[Hnone Hfree]].
  - unfold mbox_query_type_frame, event_slot_type_value.
    unfold mutex_query_lookup in Hused; rewrite Hused.
    apply mutex_query_type_split_full; exact Hused.
  - unfold mbox_query_type_frame, event_slot_type_value; rewrite Hnone.
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

Lemma mbox_query_type_merge_full : forall sg state eid,
  UCOS2_state_inv sg state ->
  (event_addr sg eid + OSEventType_off) # UChar |->
    event_slot_type_value state.(EventState) eid ** mbox_query_type_frame sg state eid
  |-- UCOS2_inv sg state.
Proof.
  intros sg state eid Hvalid.
  unfold mbox_query_type_frame, event_slot_type_value.
  destruct (state.(EventState).(inUsedEventStates) eid) as [observed|] eqn:Hslot.
  - apply mutex_query_type_merge_full; assumption.
  - Intros image.
    match goal with H : state.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image |- _ =>
      rename H into Himage end.
    pose proof Hvalid as [_ [_ [_ [[_ [Hstorage _]] _]]]].
    assert (Htype : image EventTypeField = Some 0)
      by (apply (proj2 (proj2 Hstorage) eid image Himage)).
    assert (Hcell : (event_addr sg eid + OSEventType_off) # UChar |-> 0 |--
      event_cell (event_pool_addr sg eid) EventTypeField (image EventTypeField)).
    { rewrite Htype; cbn [event_cell event_field_offset]; unfold OSEventType_off, event_addr; reflexivity. }
    sep_apply_l_atomic Hcell.
    unfold event_addr.
    sep_apply_l_atomic (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
      (event_pool_addr sg eid) image EventTypeField ltac:(simpl; tauto)).
    sep_apply_l_atomic (event_free_storage_merge_eid sg state.(EventState) eid image Himage).
    rewrite (UCOS2_inv_split_module sg state EventModule).
    cbn [UCOS2_module_rep]; unfold event_raw_rep; entailer!.
Qed.

Lemma mbox_query_public_slot_is_mbox : forall state eid observed,
  mbox_query_public_slot state eid observed ->
  event_slot_type_value state.(EventState) eid = 1 ->
  mutex_query_lookup state eid observed /\ observed.(eventType) = OS_EVENT_TYPE_MBOX.
Proof.
  intros state eid observed [Hused|[Hnone Hfree]] Htype;
    unfold event_slot_type_value in Htype.
  - unfold mutex_query_lookup in Hused; rewrite Hused in Htype.
    split; [exact Hused|].
    destruct observed.(eventType); simpl in Htype; try lia; reflexivity.
  - rewrite Hnone in Htype; discriminate.
Qed.

Definition mbox_query_acquire_facts (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (eid : EventID) (mask saved : Z)
  (before entry : UCOS2_Verify_State) (observed current : OSEventAbstractState) : Prop :=
  critical_region_interval critical sg invocation before entry /\
  UCOS2_state_inv sg entry /\ interrupt_saved_value mask saved /\
  mutex_query_lookup before eid observed /\ mutex_query_lookup entry eid current /\
  observed.(eventType) = OS_EVENT_TYPE_MBOX /\ current.(eventType) = OS_EVENT_TYPE_MBOX /\
  current.(eventGeneration) = observed.(eventGeneration).

Lemma mbox_query_save_consequence :
  forall platform critical sg invocation origin eid mask saved before entry observed,
  mutex_query_handle_protocol critical sg invocation eid ->
  UCOS2_state_inv sg before -> mutex_query_lookup before eid observed ->
  observed.(eventType) = OS_EVENT_TYPE_MBOX ->
  critical_region_interval critical sg invocation before entry ->
  interrupt_saved_value mask saved ->
  critical_region_masked platform critical sg invocation origin saved entry **
    UCOS2_raw_rep sg entry |--
  EX current, coq_prop (mbox_query_acquire_facts critical sg invocation eid mask saved
    before entry observed current) &&
    (critical_region_masked platform critical sg invocation origin saved entry ** UCOS2_inv sg entry).
Proof.
  intros platform critical sg invocation origin eid mask saved before entry observed
    Hprotocol Hvalid Hlookup Htype Hinterval Hsaved.
  destruct (mutex_query_handle_interval_preserves_identity critical sg invocation eid
    before entry observed Hprotocol Hinterval Hvalid Hlookup)
    as [current [Hcurrent [Hgeneration HcurrentType]]].
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation before entry Hinterval Hvalid)) as Hentry.
  assert (Hfacts : mbox_query_acquire_facts critical sg invocation eid mask saved
    before entry observed current).
  { unfold mbox_query_acquire_facts.
    split; [exact Hinterval|]; split; [exact Hentry|]; split; [exact Hsaved|].
    split; [exact Hlookup|]; split; [exact Hcurrent|]; split; [exact Htype|].
    split; [congruence|exact Hgeneration]. }
  Exists current; unfold UCOS2_inv; entailer!.
Qed.

Definition mbox_query_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (eid : EventID) (pe pd : addr)
  : program UCOS2_Verify_State (Z * option MboxQuerySnapshot) :=
  if Z.eqb pe 0 then StateRelMonad.ret (4, None)
  else if Z.eqb pd 0 then StateRelMonad.ret (9, None)
  else StateRelMonad.bind (get' (fun s => s)) (fun before =>
    if Z.eqb (event_slot_type_value before.(EventState) eid) 1 then
      StateRelMonad.bind (update (critical_region_interval critical sg invocation))
        (fun _ => StateRelMonad.bind (mbox_query_critical eid) (fun snapshot =>
          StateRelMonad.bind (update (critical_region_interval critical sg invocation))
            (fun _ => StateRelMonad.ret (0, Some snapshot))))
    else StateRelMonad.ret (1, None)).

Definition mbox_query_safe critical sg invocation eid pe pd before
  (X : Z -> option MboxQuerySnapshot -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (mbox_query_program critical sg invocation eid pe pd)
    (fun result current => X (fst result) (snd result) current).

Lemma mbox_query_program_null_event : forall critical sg invocation eid pd before,
  mbox_query_program critical sg invocation eid 0 pd before (4, None) before.
Proof. intros; unfold mbox_query_program, StateRelMonad.ret; cbn; auto. Qed.

Lemma mbox_query_program_null_output : forall critical sg invocation eid pe before,
  pe <> 0 -> mbox_query_program critical sg invocation eid pe 0 before (9, None) before.
Proof.
  intros; unfold mbox_query_program; rewrite (proj2 (Z.eqb_neq _ _) H).
  unfold StateRelMonad.ret; cbn; auto.
Qed.

Lemma mbox_query_program_wrong_type : forall critical sg invocation eid pe pd before,
  pe <> 0 -> pd <> 0 -> event_slot_type_value before.(EventState) eid <> 1 ->
  mbox_query_program critical sg invocation eid pe pd before (1, None) before.
Proof.
  intros critical sg invocation eid pe pd before Hpe Hpd Htype.
  unfold mbox_query_program; rewrite (proj2 (Z.eqb_neq _ _) Hpe), (proj2 (Z.eqb_neq _ _) Hpd).
  unfold StateRelMonad.bind, get', get.
  exists before, before; split; [split; reflexivity|].
  rewrite (proj2 (Z.eqb_neq _ _) Htype); split; reflexivity.
Qed.

Lemma mbox_query_program_success :
  forall critical sg invocation eid pe pd before entry current snapshot,
  pe <> 0 -> pd <> 0 -> event_slot_type_value before.(EventState) eid = 1 ->
  critical_region_interval critical sg invocation before entry ->
  mbox_query_critical eid entry snapshot entry ->
  critical_region_interval critical sg invocation entry current ->
  mbox_query_program critical sg invocation eid pe pd before (0, Some snapshot) current.
Proof.
  intros critical sg invocation eid pe pd before entry current snapshot
    Hpe Hpd Htype Hacquire Hread Hrestore.
  unfold mbox_query_program; rewrite (proj2 (Z.eqb_neq _ _) Hpe), (proj2 (Z.eqb_neq _ _) Hpd).
  unfold StateRelMonad.bind, get', get.
  exists before, before; split; [split; reflexivity|].
  rewrite Htype; cbn.
  exists tt, entry; split; [exact Hacquire|].
  exists snapshot, entry; split; [exact Hread|].
  exists tt, current; split; [exact Hrestore|]; split; reflexivity.
Qed.

Lemma mbox_query_api_safe_return :
  forall critical sg invocation eid pe pd before current code snapshot X,
  mbox_query_program critical sg invocation eid pe pd before (code, snapshot) current ->
  mbox_query_safe critical sg invocation eid pe pd before X ->
  safeExec (eq current) (StateRelMonad.ret (code, snapshot))
    (fun result state => X (fst result) (snd result) state).
Proof.
  intros critical sg invocation eid pe pd before current code snapshot X Hprogram Hsafe.
  unfold mbox_query_safe in Hsafe.
  eapply (highstependret_derive (mbox_query_program critical sg invocation eid pe pd)
    (eq before) (code, snapshot) (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; split; assumption || reflexivity.
Qed.

Lemma mbox_query_program_result_iff :
  forall critical sg invocation eid pe pd before result current,
  mbox_query_program critical sg invocation eid pe pd before result current <->
  if Z.eqb pe 0 then result = (4, None) /\ before = current
  else if Z.eqb pd 0 then result = (9, None) /\ before = current
  else if Z.eqb (event_slot_type_value before.(EventState) eid) 1 then
    exists entry snapshot,
      critical_region_interval critical sg invocation before entry /\
      mbox_query_critical eid entry snapshot entry /\
      critical_region_interval critical sg invocation entry current /\ result = (0, Some snapshot)
  else result = (1, None) /\ before = current.
Proof.
  intros critical sg invocation eid pe pd before result current.
  unfold mbox_query_program; destruct (Z.eqb pe 0); [reflexivity|].
  destruct (Z.eqb pd 0); [reflexivity|].
  unfold StateRelMonad.bind, get', get, update, StateRelMonad.ret.
  split.
  - intros [observed [state [[-> <-] Hbranch]]].
    destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 1); [|exact Hbranch].
    destruct Hbranch as [u [entry [Hentry [snapshot [released [Hread
      [v [returned [Hreturn [Hresult Hcurrent]]]]]]]]]].
    assert (Hreleased : released = entry) by exact (proj1 Hread).
    subst released; subst current.
    exists entry, snapshot; auto.
  - intro Hbranch; exists before, before; split; [split; reflexivity|].
    destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 1); [|exact Hbranch].
    destruct Hbranch as [entry [snapshot [Hentry [Hread [Hreturn Hresult]]]]].
    exists tt, entry; split; [exact Hentry|].
    exists snapshot, entry; split; [exact Hread|].
    exists tt, current; split; [exact Hreturn|]; split; [exact Hresult|reflexivity].
Qed.

Definition mbox_query_output_fields_rep (base : addr) (snapshot : MboxQuerySnapshot) : Assertion :=
  (&(base # "os_mbox_data" ->ₛ "OSEventGrp")) # UChar |-> snapshot.(mbox_query_wait_group) **
  store_osprio_array (&(base # "os_mbox_data" ->ₛ "OSEventTbl")) snapshot.(mbox_query_wait_rows) **
  (&(base # "os_mbox_data" ->ₛ "OSMsg")) # Ptr |-> snapshot.(mbox_query_message).

Definition mbox_query_restore_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (saved : Z)
  (released : UCOS2_Verify_State) : Assertion :=
  EX current, coq_prop (critical_region_interval critical sg invocation released current) &&
    mutex_query_closed platform critical sg invocation origin (armv7a_irq_fiq_mask saved) current.

Definition mbox_query_output_post (pd : addr) (snapshot : option MboxQuerySnapshot) : Assertion :=
  match snapshot with None => emp | Some copied => mbox_query_output_fields_rep pd copied end.

Definition mbox_query_api_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (before : UCOS2_Verify_State) (eid : EventID) (pe pd code : Z)
  (X : Z -> option MboxQuerySnapshot -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX snapshot current,
    coq_prop (mbox_query_program critical sg invocation eid pe pd before (code, snapshot) current /\
      safeExec (eq current) (StateRelMonad.ret (code, snapshot))
        (fun result state => X (fst result) (snd result) state)) **
    (mutex_query_closed platform critical sg invocation origin mask current **
     mbox_query_output_post pd snapshot).

(** Only the observed fields leave Event ownership.  In particular Ptr is
    exposed, whereas Cnt, all padding, optional Name and every other object
    remain in the original-value residual. *)
Definition mbox_query_event_unread (sg : StableGlobVars) (eid : EventID)
  (node : OSEventAbstractState) : Assertion :=
  event_cell (event_addr sg eid) EventTypeField (Some (encode_event_type node.(eventType))) **
  event_cell (event_addr sg eid) EventPadding1 node.(eventPadding1) **
  event_cell (event_addr sg eid) EventPadding2 node.(eventPadding2) **
  event_cell (event_addr sg eid) EventPadding3 node.(eventPadding3) **
  event_cell (event_addr sg eid) EventCntField (Some (encode_event_cnt_value node)) **
  event_cell (event_addr sg eid) EventPadding19 node.(eventPadding19) **
  (if sg.(osKernelConfig).(cfgEventNames)
   then event_cell (event_addr sg eid) EventNameField (Some node.(eventName)) else emp).

Definition mbox_query_read_facts (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (eid : EventID) (node : OSEventAbstractState) (message : MboxFields)
  (pointer group : Z) (rows : list Z) : Prop :=
  UCOS2_state_inv sg entry /\ mutex_query_lookup entry eid node /\
  node.(eventType) = OS_EVENT_TYPE_MBOX /\ node.(mboxFields) = Some message /\
  pointer = mbox_message_ptr message /\
  group = encode_event_wait_grp node.(waitList) entry.(TskState) /\
  rows = encode_event_wait_tbl_values_or node entry.(TskState).

Definition mbox_query_copy_frame (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask saved : Z) (before entry : UCOS2_Verify_State)
  (eid : EventID) (observed node : OSEventAbstractState) (message : MboxFields)
  (pointer group : Z) (rows : list Z) : Assertion :=
  coq_prop (mbox_query_acquire_facts critical sg invocation eid mask saved before entry observed node /\
    mbox_query_read_facts sg entry eid node message pointer group rows) &&
  (critical_region_masked platform critical sg invocation origin saved entry **
   mbox_query_event_unread sg eid node **
   event_raw_rep_no_eid sg entry.(TskState) entry.(EventState) eid **
   UCOS2_raw_rep_missing_module sg entry EventModule).

(** Original header ABI correspondence. The group immediately follows the
    output rows; its owned cell bounds the final one-past destination. The
    source padding at offset 19 similarly bounds the source's one-past. *)
Definition mbox_query_layout (sg : StableGlobVars) (eid : EventID) (pd : addr) : Prop :=
  event_object_layout_prop sg eid /\
  (&(pd # "os_mbox_data" ->ₛ "OSEventGrp")) =
    (&(pd # "os_mbox_data" ->ₛ "OSEventTbl")) + 8.

Definition mbox_query_output_table (base : addr) (table : list Z) (i : Z) : Assertion :=
  UCharArray.seg base 0 i (firstn (Z.to_nat i) table) **
  UCharArray.undef_seg base i OS_EVENT_TBL_SIZE.

Definition mbox_query_output_table_missing_i (base : addr) (table : list Z) (i : Z) : Assertion :=
  UCharArray.seg base 0 i (firstn (Z.to_nat i) table) **
  UCharArray.undef_seg base (i + 1) OS_EVENT_TBL_SIZE.

Lemma mbox_query_current_fields : forall sg state eid node,
  UCOS2_state_inv sg state -> mutex_query_lookup state eid node ->
  node.(eventType) = OS_EVENT_TYPE_MBOX -> exists message, node.(mboxFields) = Some message.
Proof.
  intros sg state eid node Hvalid Hlookup Htype.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [Hfields _]]]] _]]]].
  specialize (Hfields eid node Hlookup).
  unfold event_fields_consistency in Hfields; rewrite Htype in Hfields.
  destruct node.(mboxFields) as [message|]; [eauto|tauto].
Qed.

Lemma mbox_query_program_has_result :
  forall critical sg invocation eid pe pd before observed,
  mbox_query_call_input critical sg invocation pe pd before eid observed ->
  UCOS2_state_inv sg before ->
  exists result, mbox_query_program critical sg invocation eid pe pd before result before.
Proof.
  intros critical sg invocation eid pe pd before observed Hinput Hvalid.
  destruct (Z.eq_dec pe 0) as [->|Hpe].
  - exists (4, None); apply mbox_query_program_null_event.
  - destruct (Z.eq_dec pd 0) as [->|Hpd].
    + exists (9, None); apply mbox_query_program_null_output; exact Hpe.
    + destruct (Z.eq_dec (event_slot_type_value before.(EventState) eid) 1) as [Htype|Htype].
      * assert (Hslot : mbox_query_public_slot before eid observed)
          by (unfold mbox_query_call_input in Hinput; tauto).
        destruct (mbox_query_public_slot_is_mbox before eid observed Hslot Htype) as [Hlookup Hmbox].
        destruct (mbox_query_current_fields sg before eid observed Hvalid Hlookup Hmbox) as [message Hmessage].
        exists (0, Some (mbox_query_snapshot before.(TskState) observed message)).
        eapply mbox_query_program_success with (entry := before).
        -- exact Hpe.
        -- exact Hpd.
        -- exact Htype.
        -- constructor.
        -- unfold mbox_query_critical; split; [reflexivity|].
           exists observed, message; repeat split; assumption || reflexivity.
        -- constructor.
      * exists (1, None); apply mbox_query_program_wrong_type; assumption.
Qed.

Lemma mbox_query_restore_consequence :
  forall platform critical sg invocation origin saved released current,
  UCOS2_state_inv sg released ->
  critical_region_interval critical sg invocation released current ->
  interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask saved) **
    critical_region_outside critical sg invocation current |--
  mbox_query_restore_post platform critical sg invocation origin saved released.
Proof.
  intros platform critical sg invocation origin saved released current Hvalid Hinterval.
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation released current Hinterval Hvalid)) as Hcurrent.
  unfold mbox_query_restore_post, mutex_query_closed; Exists current; entailer!.
Qed.

Lemma mbox_query_event_read_fields_equiv : forall sg tasks eid node message,
  node.(eventType) = OS_EVENT_TYPE_MBOX -> node.(mboxFields) = Some message ->
  used_event_rep sg tasks eid node --||--
    (event_addr sg eid + OSEventPtr_off) # Ptr |-> mbox_message_ptr message **
    (event_addr sg eid + OSEventGrp_off) # UChar |-> encode_event_wait_grp node.(waitList) tasks **
    store_osprio_array (event_addr sg eid + OSEventTbl_off)
      (encode_event_wait_tbl_values_or node tasks) ** mbox_query_event_unread sg eid node.
Proof.
  intros sg tasks eid node message Htype Hmessage.
  unfold used_event_rep, event_storage_rep, event_fields.
  destruct (cfgEventNames (osKernelConfig sg)) eqn:Hnames;
    cbn [app];
    repeat rewrite EventFieldStorage.store_fields_cons by
      (repeat constructor; simpl; intuition discriminate);
    rewrite EventFieldStorage.store_fields_nil;
    unfold mbox_query_event_unread; rewrite Hnames;
    cbn [event_image event_cell event_field_offset];
    unfold encode_event_ptr_value, verification_slice_encode_event_ptr_value;
    rewrite Htype, Hmessage;
    unfold mbox_message_ptr, store_osprio_array, encode_event_wait_tbl_values_or,
      oseventtbl_element_store, sizeof_OS_PRIO, OSEventPtr_off, OSEventGrp_off, OSEventTbl_off;
    cbn [store_array store_array_rec];
    split; entailer!.
  all: repeat rewrite <- Z.add_assoc; entailer!.
Qed.

Lemma mbox_query_fields_split_full : forall sg entry eid node message,
  mutex_query_lookup entry eid node ->
  node.(eventType) = OS_EVENT_TYPE_MBOX -> node.(mboxFields) = Some message ->
  UCOS2_inv sg entry |-- coq_prop (UCOS2_state_inv sg entry) &&
    ((event_addr sg eid + OSEventPtr_off) # Ptr |-> mbox_message_ptr message **
     (event_addr sg eid + OSEventGrp_off) # UChar |-> encode_event_wait_grp node.(waitList) entry.(TskState) **
     store_osprio_array (event_addr sg eid + OSEventTbl_off)
       (encode_event_wait_tbl_values_or node entry.(TskState)) **
     mbox_query_event_unread sg eid node **
     event_raw_rep_no_eid sg entry.(TskState) entry.(EventState) eid **
     UCOS2_raw_rep_missing_module sg entry EventModule).
Proof.
  intros sg entry eid node message Hlookup Htype Hmessage.
  rewrite (UCOS2_inv_split_module sg entry EventModule); Intros.
  cbn [UCOS2_module_rep].
  sep_apply_l_atomic (event_raw_rep_split_eid sg entry.(TskState) entry.(EventState) eid node Hlookup).
  sep_apply_l_atomic (proj1 (mbox_query_event_read_fields_equiv sg entry.(TskState) eid node message Htype Hmessage)).
  entailer!.
Qed.

Lemma mbox_query_fields_merge_full : forall sg entry eid node message,
  UCOS2_state_inv sg entry -> mutex_query_lookup entry eid node ->
  node.(eventType) = OS_EVENT_TYPE_MBOX -> node.(mboxFields) = Some message ->
  (event_addr sg eid + OSEventPtr_off) # Ptr |-> mbox_message_ptr message **
  (event_addr sg eid + OSEventGrp_off) # UChar |-> encode_event_wait_grp node.(waitList) entry.(TskState) **
  store_osprio_array (event_addr sg eid + OSEventTbl_off)
    (encode_event_wait_tbl_values_or node entry.(TskState)) **
  mbox_query_event_unread sg eid node **
  event_raw_rep_no_eid sg entry.(TskState) entry.(EventState) eid **
  UCOS2_raw_rep_missing_module sg entry EventModule |-- UCOS2_inv sg entry.
Proof.
  intros sg entry eid node message Hvalid Hlookup Htype Hmessage.
  sep_apply_l_atomic (proj2 (mbox_query_event_read_fields_equiv sg entry.(TskState) eid node message Htype Hmessage)).
  sep_apply_l_atomic (event_raw_rep_merge_eid sg entry.(TskState) entry.(EventState) eid node Hlookup).
  rewrite (UCOS2_inv_split_module sg entry EventModule).
  cbn [UCOS2_module_rep]; entailer!.
Qed.

Lemma mbox_query_output_table_init : forall base table,
  UCharArray.undef_full base OS_EVENT_TBL_SIZE |-- mbox_query_output_table base table 0.
Proof.
  intros; unfold mbox_query_output_table; cbn [Z.to_nat firstn].
  sep_apply_l_atomic (UCharArray.undef_full_to_undef_seg base OS_EVENT_TBL_SIZE).
  unfold UCharArray.seg, store_array_rec; entailer!.
Qed.

Lemma mbox_query_output_table_split : forall base table i,
  0 <= i < OS_EVENT_TBL_SIZE ->
  mbox_query_output_table base table i |--
    (base + i) # UChar |->_ ** mbox_query_output_table_missing_i base table i.
Proof.
  intros base table i Hi; unfold mbox_query_output_table, mbox_query_output_table_missing_i.
  rewrite UCharArray.undef_seg_unfold by lia.
  unfold StoreUCharAsElement.undefstoreA; rewrite sizeof_uchar.
  replace (base + i * 1) with (base + i) by lia; entailer!.
Qed.

Lemma mbox_query_table_prefix_step : forall table i,
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

Lemma mbox_query_output_table_merge : forall base table i,
  0 <= i < Zlength table ->
  (base + i) # UChar |-> Znth i table 0 ** mbox_query_output_table_missing_i base table i
  |-- mbox_query_output_table base table (i + 1).
Proof.
  intros base table i Hi; unfold mbox_query_output_table, mbox_query_output_table_missing_i.
  assert (Hcell : (base + i) # UChar |-> Znth i table 0 |--
    StoreUCharAsElement.storeA base i (Znth i table 0)).
  { unfold StoreUCharAsElement.storeA; rewrite sizeof_uchar.
    replace (base + i * 1) with (base + i) by lia; reflexivity. }
  sep_apply_l_atomic Hcell.
  sep_apply_l_atomic (UCharArray.seg_single base i (Znth i table 0)).
  sep_apply_l_atomic (UCharArray.seg_merge_to_seg base 0 i (i + 1)
    (firstn (Z.to_nat i) table) [Znth i table 0] ltac:(lia)).
  rewrite mbox_query_table_prefix_step by exact Hi; entailer!.
Qed.

Lemma mbox_query_output_table_complete : forall base table i,
  Zlength table = OS_EVENT_TBL_SIZE -> i = OS_EVENT_TBL_SIZE ->
  mbox_query_output_table base table i |-- store_osprio_array base table.
Proof.
  intros base table i Hlen ->; unfold mbox_query_output_table.
  rewrite firstn_all2 by (rewrite Zlength_correct in Hlen; unfold OS_EVENT_TBL_SIZE in *; lia).
  rewrite UCharArray.undef_seg_empty.
  sep_apply_l_atomic (UCharArray.seg_to_full base 0 OS_EVENT_TBL_SIZE table).
  unfold UCharArray.full, StoreUCharAsElement.sizeA, store_osprio_array, oseventtbl_element_store,
    StoreUCharAsElement.storeA, sizeof_OS_PRIO.
  rewrite sizeof_uchar.
  replace (base + 0 * 1) with base by lia.
  replace (OS_EVENT_TBL_SIZE - 0) with OS_EVENT_TBL_SIZE by lia; entailer!.
Qed.

Lemma mbox_query_event_table_bounds : forall sg eid node,
  mbox_query_event_unread sg eid node |--
  coq_prop (0 <= event_addr sg eid + OSEventTbl_off /\
    event_addr sg eid + OSEventTbl_off + 8 <= Int.max_unsigned).
Proof.
  intros sg eid node; unfold mbox_query_event_unread.
  cbn [event_cell event_field_offset].
  prop_apply_p (valid_store_uchar (event_addr sg eid + 0) (encode_event_type node.(eventType))).
  destruct node.(eventPadding19) as [byte|].
  - prop_apply_p (valid_store_uchar (event_addr sg eid + 19) byte).
    unfold OSEventTbl_off; entailer!;
      unfold isvalidptr_char, addr_max_unsigned in *; cbn in *; lia.
  - prop_apply_p (valid_undef_store_uchar (event_addr sg eid + 19)).
    unfold OSEventTbl_off; entailer!;
      unfold isvalidptr_char, addr_max_unsigned in *; cbn in *; lia.
Qed.

Lemma mbox_query_output_table_bounds : forall base group,
  group = base + 8 ->
  group # UChar |->_ ** UCharArray.undef_full base 8 |--
  coq_prop (0 <= base /\ base + 8 <= Int.max_unsigned).
Proof.
  intros base group ->.
  sep_apply_l_atomic (UCharArray.undef_full_split_to_undef_missing_i base 0 8 ltac:(lia)).
  unfold StoreUCharAsElement.undefstoreA; rewrite sizeof_uchar.
  replace (base + 0 * 1) with base by lia.
  prop_apply_p (valid_undef_store_uchar base).
  prop_apply_p (valid_undef_store_uchar (base + 8)).
  entailer!; unfold isvalidptr_char, addr_max_unsigned in *; cbn in *; lia.
Qed.
