Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.VC.code.event.spec.event_pend_multi_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Import ListNotations UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Arguments store_map {A B} _ _.
Local Arguments store_map_missing_i {A B} _ _ _.

(** Pure, source-ordered public return relation.  All intervening resource
    producers remain proof obligations.  A relation on snapshots is never
    used as ownership of the input/output arrays or as a Save axiom. *)
Definition event_pend_multi_ids_valid (sg : StableGlobVars) (pointers : list addr)
  (ids : list EventID) : Prop :=
  pointers = map (event_addr sg) ids /\ Forall (valid_event_id sg) ids.
Definition event_pend_multi_readable_slots (state : UCOS2_Verify_State) (ids : list EventID) : Prop :=
  Forall (fun eid => exists observed, sem_query_public_slot state eid observed) ids.
Definition event_pend_multi_output_input (ready messages : addr) (pointers : list addr)
  (old_ready old_messages : EventPendMultiSlots) : Assertion :=
  match pointers with [] => emp | _ =>
    if Z.eq_dec ready 0 then emp else if Z.eq_dec messages 0 then emp else
      coq_prop (Zlength pointers + 1 <= Zlength old_ready /\ Zlength pointers <= Zlength old_messages) &&
      (event_pend_multi_output_rep ready old_ready ** event_pend_multi_output_rep messages old_messages)
  end.
Definition event_pend_multi_cpu_context (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (sg : StableGlobVars) (call : OsSchedCallContext)
  (mask : Z) : Assertion :=
  interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) mask **
  os_sched_context_resources external call ** unmap_table_rep sg.
Definition event_pend_multi_output_missing (base : addr) (slots : EventPendMultiSlots)
  (index : Z) : Assertion := PtrArray.mixed_missing_i base index 0 (Zlength slots) slots.
Definition event_pend_multi_type_valid (events : Glob_EventAbstractState) (eid : EventID) : bool :=
  match events.(inUsedEventStates) eid with
  | None => false
  | Some e => event_pend_multi_supported_type e.(eventType)
  end.
Definition event_pend_multi_types_valid (events : Glob_EventAbstractState) (ids : list EventID) : bool :=
  forallb (event_pend_multi_type_valid events) ids.
Definition event_pend_multi_validation_loop (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (pointers : list addr) (ids : list EventID) (index : Z) : Assertion :=
  coq_prop (event_pend_multi_ids_valid sg pointers ids /\ event_pend_multi_readable_slots state ids /\
    0 <= index <= Zlength pointers /\
    event_pend_multi_types_valid state.(EventState) (firstn (Z.to_nat index) ids) = true) && emp.
Definition event_pend_multi_selected (sg : StableGlobVars) (pointers ids : list Z)
  (index eid pointer : Z) : Prop :=
  eid = Znth index ids 0 /\ pointer = event_addr sg eid /\
  pointer = event_task_wait_multi_pointer pointers index /\ 0 <= index < Zlength pointers.
Definition event_pend_multi_supported_code (value : Z) : Prop := value = 1 \/ value = 2 \/ value = 3.
(** Selected C/ABI interpretation, not a condition on a runtime waiter.
    The frontend leaves arrow-field addresses opaque.  The same Event/Queue
    layout interface used by native Sem/Queue cases is therefore explicit. *)
Definition event_pend_multi_abi (sg : StableGlobVars) : Prop :=
  event_table_layout_prop sg /\ queue_table_layout_prop sg sg.(g_OSQTbl) /\
  sizeof ("os_q") = sizeof_OS_Q.

Lemma event_pend_multi_queue_layout_from_table : forall sg qid,
  event_pend_multi_abi sg -> 0 <= qid < sg.(osMaxQs) ->
  queue_control_block_layout_prop sg qid
    (&(((qcb_addr (sg) (qid))) # "os_q" ->ₛ "OSQPtr"))
    (&(((qcb_addr (sg) (qid))) # "os_q" ->ₛ "OSQStart"))
    (&(((qcb_addr (sg) (qid))) # "os_q" ->ₛ "OSQEnd"))
    (&(((qcb_addr (sg) (qid))) # "os_q" ->ₛ "OSQIn"))
    (&(((qcb_addr (sg) (qid))) # "os_q" ->ₛ "OSQOut"))
    (&(((qcb_addr (sg) (qid))) # "os_q" ->ₛ "OSQSize"))
    (&(((qcb_addr (sg) (qid))) # "os_q" ->ₛ "OSQEntries")).
Proof.
  intros sg qid [_ [Htable Hsize]] Hqid.
  specialize (Htable qid Hqid); rewrite Hsize in Htable; exact Htable.
Qed.
Definition event_pend_multi_scalar_observation (actual expected : Z) : Prop := actual = expected.
Definition event_pend_multi_event_pointer (sg : StableGlobVars) (eid pointer : Z) : Prop :=
  pointer = event_addr sg eid.
Definition event_pend_multi_sem_kind : OSEventType := OS_EVENT_TYPE_SEM.
Definition event_pend_multi_mbox_kind : OSEventType := OS_EVENT_TYPE_MBOX.
Definition event_pend_multi_queue_kind : OSEventType := OS_EVENT_TYPE_Q.
Definition event_pend_multi_queue_head (q : QueueFields) : addr := hd 0 q.(qMessages).
Definition event_pend_multi_queue_tail (q : QueueFields) : QueueFields :=
  queue_with_contents q q.(qInIndex) (queue_advance_index q.(qSize) q.(qOutIndex)) (tl q.(qMessages)).
Definition event_pend_multi_append_pointer (prefix : list addr) (value : addr) : list addr := prefix ++ [value].
Definition event_pend_multi_output_cursor (base : addr) (prefix : list addr) (cursor : addr) : Assertion :=
  coq_prop (cursor = base + Zlength prefix * 4) && emp.
Definition event_pend_multi_sem_after (events : Glob_EventAbstractState) (eid : EventID)
  (node : OSEventAbstractState) : Glob_EventAbstractState :=
  update_event_field_raw events eid (sem_set_count node (encode_event_cnt_value node - 1)).
Definition event_pend_multi_mbox_after (events : Glob_EventAbstractState) (eid : EventID)
  (node : OSEventAbstractState) : Glob_EventAbstractState :=
  update_event_field_raw events eid (mbox_set_message node (mbox_message_from_ptr 0)).
Definition event_pend_multi_scan_loop (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (pointers ids : list Z) (index : Z) (events : Glob_EventAbstractState)
  (ready messages : list addr) (mask : EventPendMultiMask) : Assertion :=
  coq_prop (event_pend_multi_ids_valid sg pointers ids /\
    event_pend_multi_readable_slots (replace_EventS events entry) ids /\
    event_pend_multi_scan_history sg ids entry.(EventState) index events ready messages mask) && emp.
Definition event_pend_multi_invalid_code (code : Z) : Prop := code <> 1 /\ code <> 2 /\ code <> 3.
Definition event_pend_multi_scan_finished (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (ids : list Z) (events : Glob_EventAbstractState) (ready messages : list addr)
  (mask : EventPendMultiMask) (code : Z) : Assertion :=
  coq_prop (event_pend_multi_scan sg ids entry.(EventState) event_pend_multi_empty_mask = Some
    {| event_pend_multi_scan_events := events; event_pend_multi_scan_ready := ready;
       event_pend_multi_scan_messages := messages; event_pend_multi_scan_mask := mask;
       event_pend_multi_scan_type_error := Z.eqb code 1 |}) && emp.

(** Each scan branch owns one selected ECB and one copy of the remaining
    kernel heap.  The Event/Queue collections are never copied per input
    occurrence, so duplicate input pointers select the updated map again. *)
Definition event_pend_multi_live_selected (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (eid : EventID) (node : OSEventAbstractState) (code pointer : Z) : Prop :=
  state.(EventState).(inUsedEventStates) eid = Some node /\
  encode_event_type node.(eventType) = code /\ pointer = event_addr sg eid.
Definition event_pend_multi_payload_frame (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (eid : EventID) (node : OSEventAbstractState) (field : EventField) : Assertion :=
  event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_image sg state.(TskState) node) field **
  event_raw_rep_no_eid sg state.(TskState) state.(EventState) eid **
  UCOS2_raw_rep_missing_module sg state EventModule.
Definition event_pend_multi_queue_frame (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (eid : EventID) (node : OSEventAbstractState) (free : list QueueID) : Assertion :=
  event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_image sg state.(TskState) node) EventPtrField **
  event_raw_rep_no_eid sg state.(TskState) state.(EventState) eid **
  store_map_missing_i (published_queue_node_rep sg state.(EventState)) state.(EventState).(inUsedEventStates) eid **
  store_free_queue_list sg free ** UCOS2_raw_rep_missing_two sg state EventModule QueueModule.
Definition event_pend_multi_queue_selected (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (node : OSEventAbstractState) (q : QueueFields) (free : list QueueID)
  (slots : list (option addr)) (pointer : addr) : Prop :=
  node.(queueFields) = Some q /\ pointer = qcb_addr sg q.(qID) /\
  state.(EventState).(publishedQueueBytes) q.(qID) = Some slots /\
  queue_published_storage_binding state.(EventState) /\
  queue_pool_partition sg state.(EventState) free /\ queue_fields_consistency sg node.(waitList) q.

Definition event_pend_multi_prepare_fields : list TCBLayoutField :=
  [TCBCommonField TCBStat; TCBCommonField TCBStatPend; TCBCommonField TCBDly].
Definition event_pend_multi_resume_fields : list TCBLayoutField :=
  [TCBCommonField TCBStat; TCBCommonField TCBStatPend; TCBEventMultiPtr; TCBEventMultiRdy;
   TCBCommonField TCBMsg; TCBCommonField TCBY; TCBCommonField TCBBitX; TCBCommonField TCBBitY].
Definition event_pend_multi_tcb_rest (sg : StableGlobVars) (tid : TaskID)
  (task : TaskAbstractState) (exposed : list TCBLayoutField) : Assertion :=
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec (tcb_layout_cell true (task_slot_addr sg tid))
    (fold_right (remove TCBLayoutField_eq_dec) (tcb_configured_fields true true) exposed)
    (task_layout_image sg task).
Definition event_pend_multi_sched_without_current (sg : StableGlobVars)
  (state : UCOS2_Verify_State) : Assertion :=
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
  sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte state.(SchedState).(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte state.(SchedState).(highRdyPrio) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg state.(SchedState).(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> state.(SchedState).(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if state.(SchedState).(isRunning) then 1 else 0).
Definition event_pend_multi_task_frame (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (tid : TaskID) (task : TaskAbstractState) (exposed : list TCBLayoutField) : Assertion :=
  event_pend_multi_tcb_rest sg tid task exposed **
  task_public_storage_without_task sg state.(TskState) tid **
  event_pend_multi_sched_without_current sg state **
  UCOS2_raw_rep_missing_task_storage_sched_event sg state.
Definition event_pend_multi_task_selected (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (tid : TaskID) (task : TaskAbstractState) : Prop :=
  state.(SchedState).(curTaskID) = Some tid /\ state.(TskState).(inUsedTaskStates) tid = Some task /\
  0 <= task.(curPrio) / 8 < 8.
Definition event_pend_multi_task_status (task : TaskAbstractState) : Z := encode_task_status task.(stat).
Definition event_pend_multi_task_pend_status (task : TaskAbstractState) : Z := encode_pend_status task.(statPend).
Definition event_pend_multi_task_delay (task : TaskAbstractState) : Z := task.(dly).
Definition event_pend_multi_task_multi_pointer (task : TaskAbstractState) : addr := task.(tcbEventMultiPtr).
Definition event_pend_multi_task_ready_pointer (sg : StableGlobVars) (task : TaskAbstractState) : addr := encode_event_link sg task.(eventMultiRdy).
Definition event_pend_multi_task_message (task : TaskAbstractState) : addr := encode_msg task.(msg).
Definition event_pend_multi_ready_row (state : UCOS2_Verify_State) (task : TaskAbstractState) : Z :=
  encode_ready_tbl_at_or state.(SchedState).(readyList) state.(TskState) (task.(curPrio) / 8).
Definition event_pend_multi_ready_group (state : UCOS2_Verify_State) : Z :=
  encode_ready_grp state.(SchedState).(readyList) state.(TskState).
Definition event_pend_multi_prepared_tasks (state : UCOS2_Verify_State) (tid : TaskID)
  (task : TaskAbstractState) (mask timeout : Z) : Glob_TaskAbstractState :=
  glob_task_set_usedtask state.(TskState) tid (task_prepare_multi_wait task mask timeout).
Definition event_pend_multi_wait_input (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (tid : TaskID) (task : TaskAbstractState) (mask timeout : Z)
  (pointers ids : list Z) (instances : EventTaskWaitMultiInstances) : Prop :=
  event_pend_multi_task_selected sg state tid task /\ map fst instances = ids /\
  event_task_wait_multi_input sg (event_pend_multi_prepared_tasks state tid task mask timeout)
    state.(EventState) tid (task_prepare_multi_wait task mask timeout) pointers instances.
Definition event_pend_multi_wait_frame (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (tid : TaskID) (task : TaskAbstractState) (mask timeout : Z) : Assertion :=
  event_task_wait_multi_task_frame sg (event_pend_multi_prepared_tasks state tid task mask timeout)
    tid (task_prepare_multi_wait task mask timeout) **
  event_task_wait_multi_sched_frame sg (event_pend_multi_prepared_tasks state tid task mask timeout)
    state.(SchedState) (task_prepare_multi_wait task mask timeout) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg state.

Lemma event_pend_multi_queue_nonempty_dequeue : forall q,
  0 < queue_entries q ->
  queue_dequeue_front q = Some (event_pend_multi_queue_head q, event_pend_multi_queue_tail q).
Proof.
  intros q H; unfold queue_entries in H.
  unfold queue_dequeue_front, event_pend_multi_queue_head, event_pend_multi_queue_tail.
  destruct (qMessages q); [rewrite Zlength_nil in H; lia|reflexivity].
Qed.

Lemma event_pend_multi_payload_split_field : forall sg state eid node field,
  state.(EventState).(inUsedEventStates) eid = Some node ->
  In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
  UCOS2_full_inv sg state |-- coq_prop (UCOS2_full_state_inv sg state) &&
    (event_cell (event_addr sg eid) field (event_image sg state.(TskState) node field) **
     event_pend_multi_payload_frame sg state eid node field).
Proof.
  intros sg state eid node field Hnode Hfield.
  rewrite (UCOS2_full_inv_split_module sg state EventModule); Intros.
  cbn [UCOS2_module_rep].
  sep_apply_l_atomic (event_raw_rep_split_eid sg state.(TskState) state.(EventState) eid node Hnode).
  unfold used_event_rep.
  sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg state.(TskState) node) field Hfield).
  unfold event_pend_multi_payload_frame; entailer!.
  all: match goal with |- ?P |-- _ =>
    change (P |-- “ UCOS2_full_state_inv sg state ” && P) end; entailer!.
Qed.

Lemma event_pend_multi_payload_merge_field : forall sg state eid node field,
  UCOS2_full_state_inv sg state -> state.(EventState).(inUsedEventStates) eid = Some node ->
  In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
  event_cell (event_addr sg eid) field (event_image sg state.(TskState) node field) **
    event_pend_multi_payload_frame sg state eid node field |-- UCOS2_full_inv sg state.
Proof.
  intros sg state eid node field Hvalid Hnode Hfield.
  unfold event_pend_multi_payload_frame.
  sep_apply_l_atomic (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg state.(TskState) node) field Hfield).
  fold (used_event_rep sg state.(TskState) eid node).
  sep_apply_l_atomic (event_raw_rep_merge_eid sg state.(TskState) state.(EventState) eid node Hnode).
  rewrite <- (UCOS2_raw_rep_split_module sg state EventModule).
  unfold UCOS2_full_inv; entailer!.
  all: match goal with |- ?P |-- _ =>
    change (P |-- “ UCOS2_full_state_inv sg state ” && P) end; entailer!.
Qed.

Lemma event_pend_multi_supported_slot_is_live : forall events eid code,
  event_pend_multi_supported_code code -> event_slot_type_value events eid = code ->
  exists node, events.(inUsedEventStates) eid = Some node /\ encode_event_type node.(eventType) = code.
Proof.
  intros events eid code Hcode Hvalue; unfold event_slot_type_value in Hvalue.
  destruct (inUsedEventStates events eid) as [node|] eqn:Hnode.
  - exists node; auto.
  - unfold event_pend_multi_supported_code in Hcode; lia.
Qed.

(** Full-profile public ECB type access includes recycled free objects.
    The existing frame is raw storage and therefore reusable; the old
    selected-invariant split/merge theorems are not used as full bridges. *)
Lemma event_pend_multi_type_split : forall sg state eid observed,
  sem_query_public_slot state eid observed ->
  UCOS2_full_inv sg state |-- coq_prop (UCOS2_full_state_inv sg state) &&
    ((event_addr sg eid + OSEventType_off) # UChar |->
      event_slot_type_value state.(EventState) eid ** sem_query_type_frame sg state eid).
Proof.
  intros sg state eid observed [Hused|[Hnone Hfree]].
  - unfold sem_query_type_frame, event_slot_type_value.
    unfold mutex_query_lookup in Hused; rewrite Hused.
    pose proof (event_pend_multi_payload_split_field sg state eid observed EventTypeField
      Hused ltac:(simpl; tauto)) as Hsplit.
    unfold event_pend_multi_payload_frame in Hsplit.
    cbn [event_image event_cell event_field_offset] in Hsplit.
    unfold mutex_query_type_frame, OSEventType_off; exact Hsplit.
  - unfold sem_query_type_frame, event_slot_type_value; rewrite Hnone.
    rewrite (UCOS2_full_inv_split_module sg state EventModule); Intros.
    match goal with H : UCOS2_full_state_inv sg state |- _ =>
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
    all: match goal with |- ?P |-- _ && ?R =>
      change (P |-- “ UCOS2_full_state_inv sg state ” && R) end; entailer!.
Qed.

Lemma event_pend_multi_type_merge : forall sg state eid,
  UCOS2_full_state_inv sg state ->
  (event_addr sg eid + OSEventType_off) # UChar |->
    event_slot_type_value state.(EventState) eid ** sem_query_type_frame sg state eid |--
  UCOS2_full_inv sg state.
Proof.
  intros sg state eid Hvalid; unfold sem_query_type_frame, event_slot_type_value.
  destruct (state.(EventState).(inUsedEventStates) eid) as [observed|] eqn:Hslot.
  - pose proof (event_pend_multi_payload_merge_field sg state eid observed EventTypeField
      Hvalid Hslot ltac:(simpl; tauto)) as Hmerge.
    unfold event_pend_multi_payload_frame in Hmerge.
    cbn [event_image event_cell event_field_offset] in Hmerge.
    unfold mutex_query_type_frame, OSEventType_off; exact Hmerge.
  - Intros image.
    match goal with H : state.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image |- _ =>
      rename H into Himage end.
    pose proof Hvalid as [_ [_ [_ [[_ [Hstorage _]] _]]]].
    assert (Htype : image EventTypeField = Some 0) by (apply (proj2 (proj2 Hstorage) eid image Himage)).
    pose proof (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
      (event_pool_addr sg eid) image EventTypeField ltac:(simpl; tauto)) as Hmerge.
    rewrite Htype in Hmerge; cbn [event_cell event_field_offset] in Hmerge.
    unfold OSEventType_off, event_addr; sep_apply_l_atomic Hmerge.
    sep_apply_l_atomic (event_free_storage_merge_eid sg state.(EventState) eid image Himage).
    rewrite (UCOS2_full_inv_split_module sg state EventModule).
    cbn [UCOS2_module_rep]; unfold event_raw_rep; entailer!.
Qed.

Definition event_pend_multi_precritical_error (state : UCOS2_Verify_State) (ids : list EventID)
  : option Z :=
  if negb (event_pend_multi_types_valid state.(EventState) ids) then Some 1 else
  if Z.ltb 0 state.(IntrState).(intNesting) then Some 2 else
  if Z.ltb 0 state.(IntrState).(lockNesting) then Some 13 else None.

Definition event_pend_multi_waiting_state (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (tid : TaskID) (t : TaskAbstractState) (mask timeout base : Z) (ids : list EventID)
  : UCOS2_Verify_State :=
  let prepared := task_prepare_multi_wait t mask timeout in
  let tasks := glob_task_set_usedtask state.(TskState) tid prepared in
  replace_SchedS (sched_remove_ready_task state.(SchedState) tid)
    (replace_EventS (event_multi_insert_waiters sg tasks state.(EventState) tid ids)
      (replace_TskS (glob_task_set_usedtask tasks tid (task_set_multi_fields prepared base ids None)) state)).

(** Both PendOK and PendAbort read the actual MultiRdy pointer before the
    null test. Ghost Some/None is not that test: without a valid-id fact a
    Some id can encode NULL. This total source transformer gives no right
    to dereference a non-NULL invalid id or an unpublished payload. *)
Definition event_pend_multi_remove_needed (sg : StableGlobVars) (t : TaskAbstractState) : bool :=
  match t.(statPend) with
  | PendTimeout => true
  | _ => Z.eqb (encode_event_link sg t.(eventMultiRdy)) 0
  end.
Definition event_pend_multi_resumed_ready (sg : StableGlobVars) (t : TaskAbstractState) : list addr :=
  if event_pend_multi_remove_needed sg t then [] else
  match t.(eventMultiRdy) with None => [] | Some eid => [event_addr sg eid] end.
Definition event_pend_multi_resumed_error (sg : StableGlobVars) (state : UCOS2_Verify_State) (t : TaskAbstractState) : Z :=
  if event_pend_multi_remove_needed sg t then 10 else
  match t.(statPend) with
  | PendOK => match t.(eventMultiRdy) with
      | None => 10
      | Some eid => if event_pend_multi_type_valid state.(EventState) eid then 0 else 1
      end
  | PendAbort => 14
  | PendTimeout => 10
  end.
Definition event_pend_multi_resumed_messages (sg : StableGlobVars) (state : UCOS2_Verify_State) (t : TaskAbstractState)
  : list addr :=
  if Z.eqb (event_pend_multi_resumed_error sg state t) 1 then [] else
  if event_pend_multi_remove_needed sg t then [0] else
  match t.(statPend), t.(eventMultiRdy) with
  | PendOK, Some eid => match state.(EventState).(inUsedEventStates) eid with
      | Some e => match e.(eventType) with
          | OS_EVENT_TYPE_SEM => [0]
          | OS_EVENT_TYPE_MBOX | OS_EVENT_TYPE_Q => [encode_msg t.(msg)]
          | _ => []
          end
      | None => []
      end
  | _, _ => [0]
  end.

(** Invalid readied type returns before Stat / StatPend / MultiPtr /
    MultiRdy / Msg cleanup.  No error outcome is replaced by the normal tail.
    The temporary PendTimeout store on a null-ready outcome is subsequently
    overwritten by PendOK, while Dly and EventPtr are left unchanged. *)
Definition event_pend_multi_resumed_state (sg : StableGlobVars) (state : UCOS2_Verify_State) (tid : TaskID)
  (t : TaskAbstractState) (ids : list EventID) : UCOS2_Verify_State :=
  if Z.eqb (event_pend_multi_resumed_error sg state t) 1 then state else
  let events := if event_pend_multi_remove_needed sg t
    then event_multi_remove_waiters state.(EventState) tid ids else state.(EventState) in
  replace_TskS (glob_task_set_usedtask state.(TskState) tid (task_multi_cleanup t))
    (replace_EventS events state).

Definition event_pend_multi_schedule_return (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (original returned : OsSchedCallContext) (waiting resumed : UCOS2_Verify_State) : Prop :=
  exists sched_entry scheduled,
    critical_region_interval critical sg original.(os_sched_call_invocation) waiting sched_entry /\
    os_sched_c_return external critical sg sched_entry original returned scheduled /\
    critical_region_interval critical sg original.(os_sched_call_invocation) scheduled resumed.

(** Pure source checkpoints.  Their introduction is a generated entailment,
    not a public Require or an axiom about scheduler/Save interference. *)
Definition event_pend_multi_blocked_checkpoint (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) (ids : list EventID) (base timeout : Z)
  (waiting : UCOS2_Verify_State) : Assertion :=
  coq_prop (exists result tid task,
    event_pend_multi_scan sg ids entry.(EventState) event_pend_multi_empty_mask = Some result /\
    result.(event_pend_multi_scan_type_error) = false /\ result.(event_pend_multi_scan_ready) = [] /\
    entry.(SchedState).(curTaskID) = Some tid /\ entry.(TskState).(inUsedTaskStates) tid = Some task /\
    waiting = event_pend_multi_waiting_state sg
      (replace_EventS result.(event_pend_multi_scan_events) entry) tid task
      (event_pend_multi_mask_value result.(event_pend_multi_scan_mask)) timeout base ids) && emp.
Definition event_pend_multi_schedule_checkpoint (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (call returned : OsSchedCallContext)
  (entry : UCOS2_Verify_State) (ids : list EventID) (base timeout : Z)
  (scheduled : UCOS2_Verify_State) : Assertion :=
  EX waiting, EX sched_entry,
    coq_prop (critical_region_interval critical sg call.(os_sched_call_invocation) waiting sched_entry /\
      os_sched_c_return external critical sg sched_entry call returned scheduled) &&
    event_pend_multi_blocked_checkpoint sg entry ids base timeout waiting.
Definition event_pend_multi_resume_history (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (call returned : OsSchedCallContext)
  (entry : UCOS2_Verify_State) (ids : list EventID) (base timeout : Z)
  (resumed : UCOS2_Verify_State) (tid : TaskID) (task : TaskAbstractState) : Assertion :=
  coq_prop (exists result original_task,
    event_pend_multi_scan sg ids entry.(EventState) event_pend_multi_empty_mask = Some result /\
    result.(event_pend_multi_scan_type_error) = false /\ result.(event_pend_multi_scan_ready) = [] /\
    entry.(SchedState).(curTaskID) = Some tid /\ entry.(TskState).(inUsedTaskStates) tid = Some original_task /\
    event_pend_multi_schedule_return external critical sg call returned
      (event_pend_multi_waiting_state sg (replace_EventS result.(event_pend_multi_scan_events) entry)
        tid original_task (event_pend_multi_mask_value result.(event_pend_multi_scan_mask)) timeout base ids) resumed /\
    resumed.(SchedState).(curTaskID) = Some tid /\ resumed.(TskState).(inUsedTaskStates) tid = Some task /\
    taskGeneration task = taskGeneration original_task /\
    returned.(os_sched_call_invocation) = call.(os_sched_call_invocation) /\
    returned.(os_sched_call_origin) = call.(os_sched_call_origin) /\
    returned.(os_sched_call_stack) = call.(os_sched_call_stack)) && emp.
Definition event_pend_multi_resumed_pending (sg : StableGlobVars) (task : TaskAbstractState) : Z :=
  if event_pend_multi_remove_needed sg task then 1 else encode_pend_status task.(statPend).
Definition event_pend_multi_resumed_events (sg : StableGlobVars) (resumed : UCOS2_Verify_State)
  (tid : TaskID) (task : TaskAbstractState) (ids : list EventID) : Glob_EventAbstractState :=
  if event_pend_multi_remove_needed sg task
  then event_multi_remove_waiters resumed.(EventState) tid ids else resumed.(EventState).
Definition event_pend_multi_remove_input (sg : StableGlobVars) (resumed : UCOS2_Verify_State)
  (tid : TaskID) (task : TaskAbstractState) (ids pointers : list Z)
  (instances : EventTaskRemoveMultiInstances) : Prop :=
  map fst instances = ids /\
  event_task_remove_multi_input sg resumed.(TskState) resumed.(EventState) tid task pointers instances.
Definition event_pend_multi_resume_cells (sg : StableGlobVars) (tid : TaskID)
  (task : TaskAbstractState) (pending : Z) : Assertion :=
  let tcb := task_slot_addr sg tid in
  sg.(g_OSTCBCur) # Ptr |-> tcb **
  &(tcb # "os_tcb" ->ₛ "OSTCBStat") # UChar |-> event_pend_multi_task_status task **
  &(tcb # "os_tcb" ->ₛ "OSTCBStatPend") # UChar |-> pending **
  &(tcb # "os_tcb" ->ₛ "OSTCBEventMultiPtr") # Ptr |-> event_pend_multi_task_multi_pointer task **
  &(tcb # "os_tcb" ->ₛ "OSTCBEventMultiRdy") # Ptr |-> event_pend_multi_task_ready_pointer sg task **
  &(tcb # "os_tcb" ->ₛ "OSTCBMsg") # Ptr |-> event_pend_multi_task_message task **
  event_task_remove_multi_tcb_reads tcb task.
Definition event_pend_multi_resume_stage (sg : StableGlobVars) (resumed : UCOS2_Verify_State)
  (tid : TaskID) (task : TaskAbstractState) (ids pointers : list Z) (base ready messages : Z)
  (old_ready old_messages : EventPendMultiSlots) : Assertion :=
  event_pend_multi_resume_cells sg tid task (event_pend_multi_resumed_pending sg task) **
  event_pend_multi_task_frame sg resumed tid task event_pend_multi_resume_fields **
  event_raw_rep sg resumed.(TskState) (event_pend_multi_resumed_events sg resumed tid task ids) **
  event_multi_array_rep base pointers **
  PtrArray.mixed_full ready (Zlength old_ready)
    (event_pend_multi_ready_values (event_pend_multi_resumed_ready sg task) old_ready) **
  PtrArray.mixed_full messages (Zlength old_messages) old_messages.

Inductive event_pend_multi_protected_result (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (call : OsSchedCallContext)
  (entry : UCOS2_Verify_State) (ids : list EventID) (base timeout : Z)
  : list addr -> list addr -> Z -> UCOS2_Verify_State -> Prop :=
| event_pend_multi_immediate_result : forall result,
    event_pend_multi_scan sg ids entry.(EventState) event_pend_multi_empty_mask = Some result ->
    (result.(event_pend_multi_scan_type_error) = true \/
     event_pend_multi_any_ready result.(event_pend_multi_scan_ready) = true) ->
    event_pend_multi_protected_result external critical sg call entry ids base timeout
      result.(event_pend_multi_scan_ready) result.(event_pend_multi_scan_messages)
      (if result.(event_pend_multi_scan_type_error) then 1 else 0)
      (replace_EventS result.(event_pend_multi_scan_events) entry)
| event_pend_multi_blocking_result : forall result tid t returned resumed resumed_task,
    event_pend_multi_scan sg ids entry.(EventState) event_pend_multi_empty_mask = Some result ->
    result.(event_pend_multi_scan_type_error) = false -> result.(event_pend_multi_scan_ready) = [] ->
    entry.(SchedState).(curTaskID) = Some tid -> entry.(TskState).(inUsedTaskStates) tid = Some t ->
    event_pend_multi_schedule_return external critical sg call returned
      (event_pend_multi_waiting_state sg
        (replace_EventS result.(event_pend_multi_scan_events) entry) tid t
        (event_pend_multi_mask_value result.(event_pend_multi_scan_mask)) timeout base ids) resumed ->
    resumed.(SchedState).(curTaskID) = Some tid ->
    resumed.(TskState).(inUsedTaskStates) tid = Some resumed_task ->
    taskGeneration resumed_task = taskGeneration t ->
    event_pend_multi_protected_result external critical sg call entry ids base timeout
      (event_pend_multi_resumed_ready sg resumed_task)
      (event_pend_multi_resumed_messages sg resumed resumed_task)
      (event_pend_multi_resumed_error sg resumed resumed_task)
      (event_pend_multi_resumed_state sg resumed tid resumed_task ids).

Inductive event_pend_multi_nonnull_result (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (call : OsSchedCallContext)
  (before : UCOS2_Verify_State) (ids : list EventID) (base timeout : Z)
  : list addr -> list addr -> Z -> UCOS2_Verify_State -> Prop :=
| event_pend_multi_before_save_error : forall code,
    event_pend_multi_precritical_error before ids = Some code ->
    event_pend_multi_nonnull_result external critical sg call before ids base timeout [] [] code before
| event_pend_multi_after_save_result : forall entry ready messages code final,
    event_pend_multi_precritical_error before ids = None ->
    critical_region_interval critical sg call.(os_sched_call_invocation) before entry ->
    event_pend_multi_protected_result external critical sg call entry ids base timeout
      ready messages code final ->
    event_pend_multi_nonnull_result external critical sg call before ids base timeout
      ready messages code final.

Definition event_pend_multi_call_pre (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (call : OsSchedCallContext) (mask : Z) (state : UCOS2_Verify_State)
  (pend ready messages error timeout : addr) (pointers : list addr) (ids : list EventID)
  (old_ready old_messages : EventPendMultiSlots) (old_error : Z) : Assertion :=
  coq_prop (full_features_kernel_profile sg /\
    (event_pend_multi_guard_error pend ready messages pointers = false ->
      event_pend_multi_ids_valid sg pointers ids /\ event_pend_multi_readable_slots state ids)) &&
  (interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) mask **
   os_sched_context_resources external call ** unmap_table_rep sg **
   event_pend_multi_pre sg state pend ready messages error pointers old_ready old_messages old_error).

(** The source reads only the input head before the ready/messages NULL
    guards. Object-slot readability is needed only after all four guards. *)
Lemma event_pend_multi_slot_guard_from_nonnull : forall sg state pend ready messages pointers ids,
  (pend <> 0 -> event_pend_multi_ids_valid sg pointers ids /\ event_pend_multi_readable_slots state ids) ->
  (event_pend_multi_guard_error pend ready messages pointers = false ->
    event_pend_multi_ids_valid sg pointers ids /\ event_pend_multi_readable_slots state ids).
Proof.
  intros sg state pend ready messages pointers ids Hslots Hguard.
  apply event_pend_multi_nonnull_guard_cases in Hguard; apply Hslots; tauto.
Qed.

Lemma event_pend_multi_call_pre_split_entry :
  forall external platform critical sg call mask state pend ready messages error timeout
    pointers ids old_ready old_messages old_error,
  event_pend_multi_call_pre external platform critical sg call mask state pend ready messages error
    timeout pointers ids old_ready old_messages old_error |--
  “ full_features_kernel_profile sg ” &&
  “ (pend <> 0 /\ 0 < Zlength pointers /\ ready <> 0 /\ messages <> 0 ->
       event_pend_multi_ids_valid sg pointers ids /\ event_pend_multi_readable_slots state ids) ” &&
  (event_pend_multi_cpu_context external platform sg call mask ** UCOS2_full_inv sg state **
   event_pend_multi_input_arrays pend ready messages pointers old_ready old_messages **
   error # UChar |-> old_error).
Proof.
  intros; unfold event_pend_multi_call_pre.
  apply coq_prop_andp_left; intros [Hprofile Hslots].
  assert (Hpre : event_pend_multi_pre sg state pend ready messages error
      pointers old_ready old_messages old_error |--
    UCOS2_full_inv sg state **
    event_pend_multi_input_arrays pend ready messages pointers old_ready old_messages **
    error # UChar |-> old_error).
  { unfold event_pend_multi_pre; apply coq_prop_andp_left; intros; reflexivity. }
  sep_apply_l_atomic Hpre.
  unfold event_pend_multi_cpu_context.
  pose proof (event_pend_multi_nonnull_guard_length pend ready messages pointers) as Hguard.
  entailer!; tauto.
Qed.

Lemma event_pend_multi_call_pre_null_equiv :
  forall external platform critical sg call mask state pend ready messages error timeout
    pointers ids old_ready old_messages old_error,
  event_pend_multi_guard_error pend ready messages pointers = true ->
  event_pend_multi_call_pre external platform critical sg call mask state pend ready messages error
    timeout pointers ids old_ready old_messages old_error --||--
  “ full_features_kernel_profile sg ” &&
  (interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) mask **
   os_sched_context_resources external call ** unmap_table_rep sg **
   event_pend_multi_pre sg state pend ready messages error pointers old_ready old_messages old_error).
Proof.
  intros; unfold event_pend_multi_call_pre; split.
  - Intros; entailer!; tauto.
  - Intros.
    assert (Hslots : event_pend_multi_guard_error pend ready messages pointers = false ->
      event_pend_multi_ids_valid sg pointers ids /\ event_pend_multi_readable_slots state ids).
    { intro Hfalse; congruence. }
    entailer!.
Qed.

Definition event_pend_multi_call_post (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (call : OsSchedCallContext) (mask : Z) (before : UCOS2_Verify_State)
  (pend ready messages error timeout : addr) (pointers : list addr) (ids : list EventID)
  (old_ready old_messages : EventPendMultiSlots) (returned : Z) : Assertion :=
  if event_pend_multi_guard_error pend ready messages pointers then
    interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) mask **
    os_sched_context_resources external call ** unmap_table_rep sg **
    event_pend_multi_null_post sg before pend ready messages error pointers old_ready old_messages returned
  else EX final, EX ready_prefix, EX message_prefix, EX code, EX resumed,
    coq_prop (event_pend_multi_nonnull_result external critical sg call before ids pend timeout
      ready_prefix message_prefix code final /\
      returned = event_pend_multi_return_count ready_prefix /\
      resumed.(os_sched_call_invocation) = call.(os_sched_call_invocation) /\
      resumed.(os_sched_call_origin) = call.(os_sched_call_origin) /\
      resumed.(os_sched_call_stack) = call.(os_sched_call_stack)) &&
    (interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) mask **
     os_sched_context_resources external resumed ** unmap_table_rep sg ** UCOS2_raw_rep sg final **
     event_multi_array_rep pend pointers **
     event_pend_multi_output_rep ready (event_pend_multi_ready_values ready_prefix old_ready) **
     event_pend_multi_output_rep messages (event_pend_multi_messages_values message_prefix old_messages) **
     error # UChar |-> code).

Lemma event_pend_multi_remove_needed_null_pointer : forall sg task,
  encode_event_link sg task.(eventMultiRdy) = 0 ->
  event_pend_multi_remove_needed sg task = true.
Proof.
  intros sg task Hnull; unfold event_pend_multi_remove_needed.
  destruct task.(statPend); try rewrite Hnull; reflexivity.
Qed.

Lemma event_pend_multi_remove_needed_nonnull_pointer : forall sg task,
  encode_event_link sg task.(eventMultiRdy) <> 0 ->
  event_pend_multi_remove_needed sg task =
    match task.(statPend) with PendTimeout => true | _ => false end.
Proof.
  intros sg task Hnonnull; unfold event_pend_multi_remove_needed.
  destruct task.(statPend); try rewrite (proj2 (Z.eqb_neq _ _) Hnonnull); reflexivity.
Qed.

(** The first C switch tests the stored pointer value, including when an
    abstract Some encodes the null sentinel. No identifier validity or
    publication fact is inferred from this branch equation. *)
Lemma event_pend_multi_resumed_ready_encoded_branch : forall sg task,
  event_pend_multi_resumed_ready sg task =
  if event_pend_multi_remove_needed sg task then []
  else [encode_event_link sg task.(eventMultiRdy)].
Proof.
  intros sg task; unfold event_pend_multi_resumed_ready, event_pend_multi_remove_needed.
  destruct task.(statPend); destruct task.(eventMultiRdy) as [eid|];
    cbn [encode_event_link]; try reflexivity;
    destruct (Z.eqb (event_pool_addr sg eid) 0); reflexivity.
Qed.

Lemma event_pend_multi_encoded_null_return : forall sg state task,
  encode_event_link sg task.(eventMultiRdy) = 0 ->
  event_pend_multi_resumed_ready sg task = [] /\
  event_pend_multi_resumed_messages sg state task = [0] /\
  event_pend_multi_resumed_error sg state task = 10 /\
  event_pend_multi_resumed_pending sg task = 1.
Proof.
  intros sg state task Hnull.
  unfold event_pend_multi_resumed_ready, event_pend_multi_resumed_messages,
    event_pend_multi_resumed_error, event_pend_multi_resumed_pending.
  rewrite (event_pend_multi_remove_needed_null_pointer sg task Hnull).
  repeat split; reflexivity.
Qed.

Lemma event_pend_multi_timeout_return : forall sg state t,
  statPend t = PendTimeout ->
  event_pend_multi_resumed_ready sg t = [] /\
  event_pend_multi_resumed_messages sg state t = [0] /\
  event_pend_multi_resumed_error sg state t = 10.
Proof.
  intros sg state t H; unfold event_pend_multi_resumed_ready, event_pend_multi_resumed_messages,
    event_pend_multi_resumed_error, event_pend_multi_remove_needed; rewrite H; repeat split; reflexivity.
Qed.
Lemma event_pend_multi_null_ready_return : forall sg state t,
  eventMultiRdy t = None ->
  event_pend_multi_resumed_ready sg t = [] /\
  event_pend_multi_resumed_messages sg state t = [0] /\
  event_pend_multi_resumed_error sg state t = 10.
Proof.
  intros sg state t H; unfold event_pend_multi_resumed_ready, event_pend_multi_resumed_messages,
    event_pend_multi_resumed_error, event_pend_multi_remove_needed; rewrite H; destruct (statPend t);
    repeat split; reflexivity.
Qed.
Lemma event_pend_multi_abort_return : forall sg state t eid,
  statPend t = PendAbort -> eventMultiRdy t = Some eid -> event_addr sg eid <> 0 ->
  event_pend_multi_resumed_ready sg t = [event_addr sg eid] /\
  event_pend_multi_resumed_messages sg state t = [0] /\ event_pend_multi_resumed_error sg state t = 14.
Proof.
  intros sg state t eid H H0 Hpointer; unfold event_pend_multi_resumed_ready, event_pend_multi_resumed_messages,
    event_pend_multi_resumed_error, event_pend_multi_remove_needed; rewrite H, H0.
  cbn [encode_event_link].
  change (event_pool_addr sg eid) with (event_addr sg eid).
  rewrite (proj2 (Z.eqb_neq _ _) Hpointer); repeat split; reflexivity.
Qed.
Lemma event_pend_multi_bad_ready_type_skips_cleanup : forall sg state tid t ids,
  event_pend_multi_resumed_error sg state t = 1 ->
  event_pend_multi_resumed_state sg state tid t ids = state /\
  event_pend_multi_resumed_messages sg state t = [].
Proof.
  intros; unfold event_pend_multi_resumed_state, event_pend_multi_resumed_messages;
    rewrite H; split; reflexivity.
Qed.
