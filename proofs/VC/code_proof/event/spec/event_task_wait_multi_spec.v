Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.task.
Require Export Ucos2Verify.lib.task_storage.
Require Export Ucos2Verify.lib.event.
Require Export Ucos2Verify.lib.event_pool.
Require Export Ucos2Verify.lib.event_wait.
Require Export Ucos2Verify.lib.sched.
Require Export Ucos2Verify.lib.event_multi.
Require Export Ucos2Verify.VC.code.event.spec.event_task_wait_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

Definition EventTaskWaitMultiInstances := list (EventID * nat).
Definition event_task_wait_multi_pointer (pointers : list addr) (index : Z) : addr :=
  Znth index (pointers ++ [0]) 0.
Definition event_task_wait_multi_cursor (cursor base index : Z) : Prop := cursor = base + index * 4.
Definition event_task_wait_multi_value (value : Z) (pointers : list addr) (index : Z) : Prop :=
  value = event_task_wait_multi_pointer pointers index.
Definition event_task_wait_multi_array_missing (base : addr) (pointers : list addr) (index : Z) : Assertion :=
  PtrArray.missing_i base index 0 (Zlength pointers + 1) (pointers ++ [0]).
Definition event_task_wait_multi_selected (sg : StableGlobVars)
  (events : Glob_EventAbstractState) (pointers : list addr)
  (instances : EventTaskWaitMultiInstances) (index eid : Z) (e : OSEventAbstractState) : Prop :=
  eid = fst (Znth index instances (0, 0%nat)) /\
  event_task_wait_multi_pointer pointers index = event_addr sg eid /\
  events.(inUsedEventStates) eid = Some e /\ event_object_layout_prop sg eid /\
  index < Zlength pointers.

(** OS_EventTaskWaitMulti is an internal protected-cell operation, not a
    critical-section acquisition.  Its caller has already changed Stat,
    StatPend and Dly.  This contract therefore retains raw resources and
    does not require an intermediate full invariant or ready membership. *)
Definition event_task_wait_multi_input (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (events : Glob_EventAbstractState)
  (tid : TaskID) (t : TaskAbstractState) (pointers : list addr)
  (instances : list (EventID * nat)) : Prop :=
  sg.(osKernelConfig).(cfgEventMultiEnabled) = true /\
  sg.(osKernelConfig).(cfgTaskProfile) = true /\
  sg.(osKernelConfig).(cfgEventNames) = true /\
  tasks.(inUsedTaskStates) tid = Some t /\ 0 <= t.(curPrio) / 8 < 8 /\
  event_multi_array_binding sg events pointers instances /\
  Forall (fun instance => event_object_layout_prop sg (fst instance)) instances.

Definition event_task_wait_multi_events (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (events : Glob_EventAbstractState)
  (tid : TaskID) (instances : list (EventID * nat)) : Glob_EventAbstractState :=
  event_multi_insert_waiters sg tasks events tid (map fst instances).

(** The equality is the remaining-loop continuation of actual source
    updates, not an assumed valid endpoint.  Array order and generations
    are retained, including repeated entries and the empty sequence. *)
Definition event_task_wait_multi_loop (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (entry : Glob_EventAbstractState)
  (tid : TaskID) (pointers : list addr) (instances : list (EventID * nat))
  (index : Z) (events : Glob_EventAbstractState) : Prop :=
  0 <= index <= Zlength pointers /\
  event_multi_array_binding sg events pointers instances /\
  event_task_wait_multi_events sg tasks events tid (skipn (Z.to_nat index) instances) =
    event_task_wait_multi_events sg tasks entry tid instances.

(** A pure loop fact with empty spatial footprint.  The frontend retains
    this indexed assertion to infer the local existential index; unlike
    [coq_prop P] alone it owns no arbitrary discarded heap. *)
Definition event_task_wait_multi_loop_assert (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (entry : Glob_EventAbstractState)
  (tid : TaskID) (pointers : list addr) (instances : EventTaskWaitMultiInstances)
  (index : Z) (events : Glob_EventAbstractState) : Assertion :=
  coq_prop (event_task_wait_multi_loop sg tasks entry tid pointers instances index events) && emp.

Definition event_task_wait_multi_event_frame (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (events : Glob_EventAbstractState)
  (eid : EventID) (e : OSEventAbstractState) (row : Z) : Assertion :=
  event_task_wait_event_rest sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) row (event_image sg tasks e) **
  event_raw_rep_no_eid sg tasks events eid.

Definition event_task_wait_multi_post
  (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (events : Glob_EventAbstractState) (tid : TaskID) (t : TaskAbstractState)
  (instances : list (EventID * nat)) (pointers : list addr)
  (current tcb base ready_group ready_table ready_row ready_grp : Z) : Assertion :=
  current # Ptr |-> tcb **
  &(tcb # "os_tcb" ->ₛ "OSTCBEventMultiPtr") # Ptr |-> base **
  &(tcb # "os_tcb" ->ₛ "OSTCBEventMultiRdy") # Ptr |-> 0 **
  &(tcb # "os_tcb" ->ₛ "OSTCBY") # UChar |-> (t.(curPrio) / 8) **
  &(tcb # "os_tcb" ->ₛ "OSTCBBitX") # UChar |-> tcb_bit_x_of_prio t.(curPrio) **
  &(tcb # "os_tcb" ->ₛ "OSTCBBitY") # UChar |-> tcb_bit_y_of_prio t.(curPrio) **
  event_multi_array_rep base pointers **
  event_raw_rep sg tasks (event_task_wait_multi_events sg tasks events tid instances) **
  (ready_table + t.(curPrio) / 8 * sizeof(UCHAR)) # UChar |->
    event_task_wait_ready_row ready_row (tcb_bit_x_of_prio t.(curPrio)) **
  ready_group # UChar |-> event_task_wait_ready_group ready_row ready_grp
    (tcb_bit_x_of_prio t.(curPrio)) (tcb_bit_y_of_prio t.(curPrio)).

Lemma event_task_wait_multi_binding_length : forall sg events pointers instances,
  event_multi_array_binding sg events pointers instances ->
  List.length pointers = List.length instances.
Proof. intros; eapply Forall2_length; eassumption. Qed.

Lemma event_task_wait_multi_loop_start : forall sg tasks events tid pointers instances,
  event_multi_array_binding sg events pointers instances ->
  event_task_wait_multi_loop sg tasks events tid pointers instances 0 events.
Proof. intros; split; [pose proof (Zlength_nonneg pointers); lia|]; split; [assumption|reflexivity]. Qed.

Lemma event_task_wait_multi_skipn_head : forall (instances : list (EventID * nat)) index,
  0 <= index < Zlength instances ->
  skipn (Z.to_nat index) instances =
    Znth index instances (0, 0%nat) :: skipn (Z.to_nat (index + 1)) instances.
Proof.
  intros instances index Hindex.
  replace (Z.to_nat (index + 1)) with (S (Z.to_nat index)) by lia.
  assert (Hn : (Z.to_nat index < List.length instances)%nat).
  { rewrite Zlength_correct in Hindex; lia. }
  unfold Znth; remember (Z.to_nat index) as n; clear Heqn Hindex index.
  revert instances Hn; induction n; intros [|head tail] Hn; simpl in *;
    try lia; [reflexivity|apply IHn; lia].
Qed.

Lemma event_task_wait_multi_loop_step : forall sg tasks entry tid pointers instances index events eid e,
  event_task_wait_multi_loop sg tasks entry tid pointers instances index events ->
  index < Zlength pointers -> eid = fst (Znth index instances (0, 0%nat)) ->
  events.(inUsedEventStates) eid = Some e ->
  event_task_wait_multi_loop sg tasks entry tid pointers instances (index + 1)
    (update_event_field_raw events eid (event_insert_waiter sg tasks e tid)).
Proof.
  intros sg tasks entry tid pointers instances index events eid e
    [Hindex [Hbinding Hcontinuation]] Hlt Heid Hlookup.
  pose proof (event_task_wait_multi_binding_length sg events pointers instances Hbinding) as Hlength.
  assert (HlengthZ : Zlength pointers = Zlength instances) by
    (rewrite !Zlength_correct, Hlength; reflexivity).
  split; [lia|]; split.
  - pose proof (event_multi_insert_waiters_preserves_binding sg tasks events tid [eid]
      pointers instances Hbinding) as Hnext.
    rewrite (event_multi_insert_waiters_source_order sg tasks events tid eid [] e Hlookup),
      event_multi_insert_waiters_nil in Hnext; exact Hnext.
  - unfold event_task_wait_multi_events in *.
    rewrite (event_task_wait_multi_skipn_head instances index ltac:(lia)) in Hcontinuation.
    cbn [map] in Hcontinuation; rewrite <- Heid in Hcontinuation.
    rewrite (event_multi_insert_waiters_source_order sg tasks events tid eid
      (map fst (skipn (Z.to_nat (index + 1)) instances)) e Hlookup) in Hcontinuation.
    exact Hcontinuation.
Qed.

Lemma event_task_wait_multi_loop_end : forall sg tasks entry tid pointers instances index events,
  event_task_wait_multi_loop sg tasks entry tid pointers instances index events ->
  index = Zlength pointers ->
  events = event_task_wait_multi_events sg tasks entry tid instances.
Proof.
  intros sg tasks entry tid pointers instances index events
    [_ [Hbinding Hcontinuation]] ->.
  pose proof (event_task_wait_multi_binding_length sg events pointers instances Hbinding) as Hlength.
  rewrite Zlength_correct, Nat2Z.id, Hlength, skipn_all in Hcontinuation.
  unfold event_task_wait_multi_events in Hcontinuation; cbn [map] in Hcontinuation.
  rewrite event_multi_insert_waiters_nil in Hcontinuation; exact Hcontinuation.
Qed.

Lemma event_task_wait_multi_current_entry : forall sg tasks entry tid t base pointers instances index events,
  event_task_wait_multi_input sg tasks entry tid t pointers instances ->
  event_task_wait_multi_loop sg tasks entry tid pointers instances index events ->
  event_multi_array_valid base pointers -> Znth index (pointers ++ [0]) 0 <> 0 ->
  exists eid e, eid = fst (Znth index instances (0, 0%nat)) /\
    Znth index (pointers ++ [0]) 0 = event_addr sg eid /\
    events.(inUsedEventStates) eid = Some e /\ event_object_layout_prop sg eid /\
    index < Zlength pointers.
Proof.
  intros sg tasks entry tid t base pointers instances index events
    [_ [_ [_ [_ [_ [_ Hlayouts]]]]]] [Hindex [Hbinding _]] Hvalid Hnonzero.
  assert (Hlt : index < Zlength pointers).
  { destruct (Z.eq_dec index (Zlength pointers)); [subst; rewrite event_multi_array_terminator in Hnonzero; contradiction|lia]. }
  destruct (event_multi_array_binding_index sg events pointers instances index Hbinding ltac:(lia))
    as [Haddress [e [Hlookup Hgeneration]]].
  exists (fst (Znth index instances (0, 0%nat))), e.
  split; [reflexivity|]; split; [exact Haddress|]; split; [exact Hlookup|]; split; [|exact Hlt].
  rewrite Forall_forall in Hlayouts; apply Hlayouts.
  unfold Znth; apply nth_In.
  pose proof (event_task_wait_multi_binding_length sg events pointers instances Hbinding) as Hlength.
  rewrite Zlength_correct in Hlt; lia.
Qed.

Lemma event_task_wait_multi_split_event : forall sg tasks events eid e row,
  events.(inUsedEventStates) eid = Some e -> event_object_layout_prop sg eid -> 0 <= row < 8 ->
  event_raw_rep sg tasks events |--
  (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl") + row * sizeof(UCHAR)) # UChar |->
    encode_event_wait_tbl_at_or e.(waitList) tasks row **
  &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp") # UChar |->
    encode_event_wait_grp e.(waitList) tasks **
  event_task_wait_multi_event_frame sg tasks events eid e row.
Proof.
  intros sg tasks events eid e row Hlookup Hlayout Hrow.
  sep_apply_l_atomic (event_raw_rep_split_eid sg tasks events eid e Hlookup).
  unfold used_event_rep.
  sep_apply_l_atomic (event_task_wait_event_split_c_fields sg eid (event_image sg tasks e)
    row (encode_event_wait_tbl_at_or e.(waitList) tasks row)
    (encode_event_wait_grp e.(waitList) tasks) Hlayout Hrow
    (event_table_image_eq sg tasks e row Hrow) eq_refl).
  unfold event_task_wait_multi_event_frame; entailer!.
Qed.

Lemma event_task_wait_multi_merge_event : forall sg tasks events eid e tid t,
  tasks.(inUsedTaskStates) tid = Some t -> event_object_layout_prop sg eid -> 0 <= t.(curPrio) / 8 < 8 ->
  (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl") + t.(curPrio) / 8 * sizeof(UCHAR)) # UChar |->
    Z.lor (encode_event_wait_tbl_at_or e.(waitList) tasks (t.(curPrio) / 8)) (tcb_bit_x_of_prio t.(curPrio)) **
  &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp") # UChar |->
    Z.lor (encode_event_wait_grp e.(waitList) tasks) (tcb_bit_y_of_prio t.(curPrio)) **
  event_task_wait_multi_event_frame sg tasks events eid e (t.(curPrio) / 8) |--
  event_raw_rep sg tasks (update_event_field_raw events eid (event_insert_waiter sg tasks e tid)).
Proof.
  intros sg tasks events eid e tid t Hlookup Hlayout Hrow.
  unfold event_task_wait_multi_event_frame.
  sepcon_assoc_change.
  sep_apply_l_atomic (event_task_wait_event_merge_inserted_task sg tasks eid e tid t Hlayout Hlookup Hrow).
  sep_apply_l_atomic (event_raw_rep_merge_updated_eid sg tasks events eid (event_insert_waiter sg tasks e tid)).
  entailer!.
Qed.

(** The exact full-features 92-byte inventory is retained.  The frame
    includes both shifted padding bytes, names and every profiling field. *)
Definition event_task_wait_multi_task_reads (base : addr) (t : TaskAbstractState) : Assertion :=
  &(base # "os_tcb" ->ₛ "OSTCBY") # UChar |-> tcb_y_of_prio t.(curPrio) **
  &(base # "os_tcb" ->ₛ "OSTCBBitX") # UChar |-> tcb_bit_x_of_prio t.(curPrio) **
  &(base # "os_tcb" ->ₛ "OSTCBBitY") # UChar |-> tcb_bit_y_of_prio t.(curPrio).

Definition event_task_wait_multi_tcb_rest (base : addr) (image : TCBLayoutImage) : Assertion :=
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec TCBEventMultiRdy (remove TCBLayoutField_eq_dec TCBEventMultiPtr (tcb_configured_fields true true)))))) image.

Lemma event_task_wait_multi_tcb_split : forall base image t,
  image (TCBCommonField TCBY) = Some (tcb_y_of_prio t.(curPrio)) ->
  image (TCBCommonField TCBBitX) = Some (tcb_bit_x_of_prio t.(curPrio)) ->
  image (TCBCommonField TCBBitY) = Some (tcb_bit_y_of_prio t.(curPrio)) ->
  tcb_configured_storage_rep true true base image |--
  &(base # "os_tcb" ->ₛ "OSTCBEventMultiPtr") # Ptr |->_ **
  &(base # "os_tcb" ->ₛ "OSTCBEventMultiRdy") # Ptr |->_ **
  event_task_wait_multi_task_reads base t ** event_task_wait_multi_tcb_rest base image.
Proof.
  intros base image t Hy Hx Hb; unfold tcb_configured_storage_rep.
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell true base) (tcb_configured_fields true true) image TCBEventMultiPtr
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell true base) (remove TCBLayoutField_eq_dec TCBEventMultiPtr (tcb_configured_fields true true)) image TCBEventMultiRdy
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell true base) (remove TCBLayoutField_eq_dec TCBEventMultiRdy (remove TCBLayoutField_eq_dec TCBEventMultiPtr (tcb_configured_fields true true))) image (TCBCommonField TCBY)
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell true base) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec TCBEventMultiRdy (remove TCBLayoutField_eq_dec TCBEventMultiPtr (tcb_configured_fields true true)))) image (TCBCommonField TCBBitX)
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell true base) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec TCBEventMultiRdy (remove TCBLayoutField_eq_dec TCBEventMultiPtr (tcb_configured_fields true true))))) image (TCBCommonField TCBBitY)
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  rewrite Hy, Hx, Hb.
  unfold event_task_wait_multi_tcb_rest, event_task_wait_multi_task_reads.
  cbn [tcb_layout_cell tcb_cell tcb_field_address].
  destruct (image TCBEventMultiPtr); destruct (image TCBEventMultiRdy);
    try sep_apply_l_atomic (store_ptr_undef_store_ptr (&(base # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) z);
    try sep_apply_l_atomic (store_ptr_undef_store_ptr (&(base # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) z0);
    try sep_apply_l_atomic (store_ptr_undef_store_ptr (&(base # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) z);
    entailer!.
Qed.

Lemma event_task_wait_multi_tcb_merge : forall base image t array,
  image (TCBCommonField TCBY) = Some (tcb_y_of_prio t.(curPrio)) ->
  image (TCBCommonField TCBBitX) = Some (tcb_bit_x_of_prio t.(curPrio)) ->
  image (TCBCommonField TCBBitY) = Some (tcb_bit_y_of_prio t.(curPrio)) ->
  task_multi_fields_rep base array 0 ** event_task_wait_multi_task_reads base t **
    event_task_wait_multi_tcb_rest base image |--
  tcb_configured_storage_rep true true base (tcb_multi_wait_image image array).
Proof.
  intros base image t array Hy Hx Hb.
  unfold event_task_wait_multi_task_reads, event_task_wait_multi_tcb_rest.
  change (&(base # "os_tcb" ->ₛ "OSTCBY") # UChar |-> tcb_y_of_prio t.(curPrio)) with
    (tcb_layout_cell true base (TCBCommonField TCBY) (Some (tcb_y_of_prio t.(curPrio)))).
  change (&(base # "os_tcb" ->ₛ "OSTCBBitX") # UChar |-> tcb_bit_x_of_prio t.(curPrio)) with
    (tcb_layout_cell true base (TCBCommonField TCBBitX) (Some (tcb_bit_x_of_prio t.(curPrio)))).
  change (&(base # "os_tcb" ->ₛ "OSTCBBitY") # UChar |-> tcb_bit_y_of_prio t.(curPrio)) with
    (tcb_layout_cell true base (TCBCommonField TCBBitY) (Some (tcb_bit_y_of_prio t.(curPrio)))).
  rewrite <- Hy, <- Hx, <- Hb; sepcon_assoc_change.
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell true base) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec TCBEventMultiRdy (remove TCBLayoutField_eq_dec TCBEventMultiPtr (tcb_configured_fields true true))))) image (TCBCommonField TCBBitY)
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell true base) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec TCBEventMultiRdy (remove TCBLayoutField_eq_dec TCBEventMultiPtr (tcb_configured_fields true true)))) image (TCBCommonField TCBBitX)
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell true base) (remove TCBLayoutField_eq_dec TCBEventMultiRdy (remove TCBLayoutField_eq_dec TCBEventMultiPtr (tcb_configured_fields true true))) image (TCBCommonField TCBY)
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  fold (tcb_configured_without_multi true base image).
  sep_apply_l_atomic (tcb_configured_storage_merge_multi true base image array 0); entailer!.
Qed.

Definition event_task_wait_multi_task_frame (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (tid : TaskID) (t : TaskAbstractState) : Assertion :=
  event_task_wait_multi_tcb_rest (task_slot_addr sg tid) (task_layout_image sg t) **
  task_public_storage_without_task sg tasks tid.

Lemma event_task_wait_multi_task_storage_split : forall sg tasks tid t,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = true ->
  sg.(osKernelConfig).(cfgTaskProfile) = true -> tasks.(inUsedTaskStates) tid = Some t ->
  task_public_storage sg tasks |--
  &(((task_slot_addr sg tid)) # "os_tcb" ->ₛ "OSTCBEventMultiPtr") # Ptr |->_ **
  &(((task_slot_addr sg tid)) # "os_tcb" ->ₛ "OSTCBEventMultiRdy") # Ptr |->_ **
  event_task_wait_multi_task_reads (task_slot_addr sg tid) t **
  event_task_wait_multi_task_frame sg tasks tid t.
Proof.
  intros sg tasks tid t Hmulti Hprofile Hlookup.
  sep_apply_l_atomic (task_public_storage_split_task sg tasks tid t Hlookup).
  unfold used_task_rep, task_slot_storage_rep; rewrite Hmulti, Hprofile.
  sep_apply_l_atomic (event_task_wait_multi_tcb_split (task_slot_addr sg tid)
    (task_layout_image sg t) t eq_refl eq_refl eq_refl).
  unfold event_task_wait_multi_task_frame; entailer!.
Qed.

Lemma event_task_wait_multi_task_storage_merge : forall sg tasks tid t array ids,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = true ->
  sg.(osKernelConfig).(cfgTaskProfile) = true ->
  task_multi_fields_rep (task_slot_addr sg tid) array 0 **
  event_task_wait_multi_task_reads (task_slot_addr sg tid) t **
  event_task_wait_multi_task_frame sg tasks tid t |--
  task_public_storage sg (glob_task_set_usedtask tasks tid (task_set_multi_fields t array ids None)).
Proof.
  intros sg tasks tid t array ids Hmulti Hprofile.
  unfold event_task_wait_multi_task_frame; sepcon_assoc_change.
  sep_apply_l_atomic (event_task_wait_multi_tcb_merge (task_slot_addr sg tid)
    (task_layout_image sg t) t array eq_refl eq_refl eq_refl).
  rewrite <- (task_register_multi_wait_image_eq sg t array ids).
  pose proof (task_public_storage_merge_updated_task sg tasks tid
    (task_set_multi_fields t array ids None)) as Hmerge.
  unfold used_task_rep, task_slot_storage_rep in Hmerge; rewrite Hmulti, Hprofile in Hmerge.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

(** This is the actual scheduler residual of the callee footprint.  The
    bitmap is permitted to describe a transient pending task still in the
    ready list.  No ready-membership premise is introduced. *)
Definition event_task_wait_multi_sched_frame (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (s : SchedAbstractState) (t : TaskAbstractState) : Assertion :=
  UCharArray.missing_i sg.(g_OSRdyTbl) (t.(curPrio) / 8) 0 8
    (sched_row_values tasks s.(readyList)) **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte s.(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte s.(highRdyPrio) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg s.(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> s.(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if s.(isRunning) then 1 else 0).

Definition event_task_wait_multi_pre (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (events : Glob_EventAbstractState)
  (s : SchedAbstractState) (tid : TaskID) (t : TaskAbstractState)
  (array : addr) (pointers : list addr) : Assertion :=
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  &(((task_slot_addr sg tid)) # "os_tcb" ->ₛ "OSTCBEventMultiPtr") # Ptr |->_ **
  &(((task_slot_addr sg tid)) # "os_tcb" ->ₛ "OSTCBEventMultiRdy") # Ptr |->_ **
  event_task_wait_multi_task_reads (task_slot_addr sg tid) t **
  event_multi_array_rep array pointers ** event_raw_rep sg tasks events **
  (sg.(g_OSRdyTbl) + t.(curPrio) / 8 * sizeof(UCHAR)) # UChar |->
    encode_ready_tbl_at_or s.(readyList) tasks (t.(curPrio) / 8) **
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp s.(readyList) tasks.

Lemma event_task_wait_multi_pre_split : forall sg tasks events s tid t array pointers instances,
  event_task_wait_multi_input sg tasks events tid t pointers instances ->
  s.(curTaskID) = Some tid ->
  task_public_storage sg tasks ** event_raw_rep sg tasks events **
    sched_raw_rep sg tasks s ** event_multi_array_rep array pointers |--
  event_task_wait_multi_pre sg tasks events s tid t array pointers **
    event_task_wait_multi_task_frame sg tasks tid t **
    event_task_wait_multi_sched_frame sg tasks s t.
Proof.
  intros sg tasks events s tid t array pointers instances
    [Hmulti [Hprofile [_ [Hlookup [Hrow _]]]]] Hcurrent.
  sep_apply_l_atomic (event_task_wait_multi_task_storage_split sg tasks tid t Hmulti Hprofile Hlookup).
  unfold sched_raw_rep.
  sep_apply_l_atomic (sched_rows_split_cell sg tasks s.(readyList) (t.(curPrio) / 8) Hrow).
  unfold event_task_wait_multi_pre, event_task_wait_multi_sched_frame, sched_physical_rep.
  rewrite Hcurrent; cbn [encode_task_link]; entailer!.
Qed.

(** Exact post-call resource consumer for the real PendMulti transient
    state: re-index event/scheduler bytes using unchanged priorities and
    restore their whole raw frames with the updated 92-byte TCB. *)
Lemma event_task_wait_multi_post_merge : forall sg tasks events s tid t array pointers instances,
  event_task_wait_multi_input sg tasks events tid t pointers instances ->
  valid_stable_glob_vars sg -> task_priority_unique tasks ->
  task_priority_in_range sg t.(curPrio) -> sched_ready_structure sg tasks s ->
  s.(curTaskID) = Some tid ->
  event_task_wait_multi_post sg tasks events tid t instances pointers
    sg.(g_OSTCBCur) (task_slot_addr sg tid) array sg.(g_OSRdyGrp) sg.(g_OSRdyTbl)
    (encode_ready_tbl_at_or s.(readyList) tasks (t.(curPrio) / 8))
    (encode_ready_grp s.(readyList) tasks) **
  event_task_wait_multi_task_frame sg tasks tid t **
  event_task_wait_multi_sched_frame sg tasks s t |--
  task_public_storage sg (glob_task_set_usedtask tasks tid
    (task_set_multi_fields t array (map fst instances) None)) **
  event_raw_rep sg (glob_task_set_usedtask tasks tid
    (task_set_multi_fields t array (map fst instances) None))
    (event_task_wait_multi_events sg tasks events tid instances) **
  sched_raw_rep sg (glob_task_set_usedtask tasks tid
    (task_set_multi_fields t array (map fst instances) None)) (sched_remove_ready_task s tid) **
  event_multi_array_rep array pointers.
Proof.
  intros sg tasks events s tid t array pointers instances
    [Hmulti [Hprofile [_ [Hlookup [Hrow _]]]]] Hsg Hunique Hprio Hstructure Hcurrent.
  set (after_tasks := glob_task_set_usedtask tasks tid
    (task_set_multi_fields t array (map fst instances) None)).
  assert (Hpriority : forall slot, option_map curPrio (tasks.(inUsedTaskStates) slot) =
      option_map curPrio (after_tasks.(inUsedTaskStates) slot)).
  { intros slot; symmetry; unfold after_tasks; eapply glob_task_set_usedtask_observation;
      [exact Hlookup|reflexivity]. }
  assert (Hevent : event_raw_rep sg tasks (event_task_wait_multi_events sg tasks events tid instances) =
      event_raw_rep sg after_tasks (event_task_wait_multi_events sg tasks events tid instances)).
  { apply event_raw_rep_change_task_index, event_wait_priority_agreement_encodes.
    intros eid e slot He Hin; apply Hpriority. }
  assert (Hsched : sched_raw_rep sg tasks (sched_remove_ready_task s tid) =
      sched_raw_rep sg after_tasks (sched_remove_ready_task s tid)).
  { apply sched_raw_rep_priority_ext; intros; apply Hpriority. }
  rewrite <- Hevent, <- Hsched.
  unfold event_task_wait_multi_post, event_task_wait_multi_sched_frame.
  sepcon_assoc_change.
  pose proof (event_task_wait_multi_task_storage_merge sg tasks tid t array
    (map fst instances) Hmulti Hprofile) as Htask_merge.
  unfold task_multi_fields_rep, event_task_wait_multi_task_reads, tcb_y_of_prio in Htask_merge.
  sep_apply_r_atomic Htask_merge.
  sep_apply_l_atomic (event_task_wait_ready_merge_removed_task sg tasks s tid t
    Hsg Hunique Hlookup Hprio Hstructure Hrow).
  unfold sched_raw_rep, sched_physical_rep; cbn [sched_remove_ready_task sched_set_ready curTaskID
    curSchedPrio highRdyPrio highRdyTid ctxSwCtr isRunning readyList].
  rewrite Hcurrent; cbn [encode_task_link]; unfold after_tasks; entailer!.
Qed.

(** This consumes the same array binding as the real source call.  It is
    the canonical three-owner endpoint, without an after-validity guard. *)
Lemma event_task_wait_multi_source_step : forall sg tasks events tid t pointers instances image s array,
  event_task_wait_multi_input sg tasks events tid t pointers instances ->
  s.(curTaskID) = Some tid ->
  event_multi_wait_step sg tasks tid array (map fst instances) image events s
    (tcb_multi_wait_image image array)
    (event_task_wait_multi_events sg tasks events tid instances) (sched_remove_ready_task s tid) /\
  event_multi_array_binding sg (event_task_wait_multi_events sg tasks events tid instances) pointers instances.
Proof.
  intros sg tasks events tid t pointers instances image s array
    [_ [_ [_ [_ [_ [Hbinding _]]]]]] Hcurrent.
  destruct (event_multi_wait_loop_from_binding sg tasks events tid pointers instances Hbinding) as [Hloop Hafter].
  split; [unfold event_multi_wait_step, event_task_wait_multi_events; tauto|exact Hafter].
Qed.
