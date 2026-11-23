Require Export Ucos2Verify.VC.code.queue.spec.q_post_call_spec.
Require Import Ucos2Verify.lib.queue_core Ucos2Verify.lib.event Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.error_codes Ucos2Verify.lib.stable_glob_vars.
Require Import Coq.Strings.String Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic MapLib ArrayLib.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

Definition q_post_profile (sg : StableGlobVars) : Prop :=
  valid_stable_glob_vars sg /\ event_table_layout_prop sg /\
  queue_table_layout_prop sg sg.(g_OSQTbl) /\ queue_first_round_profile sg /\
  sg.(osKernelConfig).(cfgArgumentChecks) = true.

Definition q_post_queue_frame (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (eid : EventID) (free : list QueueID) : Assertion :=
  event_raw_rep sg state.(TskState) state.(EventState) **
  store_map_missing_i (published_queue_node_rep sg state.(EventState))
    state.(EventState).(inUsedEventStates) eid **
  store_free_queue_list sg free ** UCOS2_raw_rep_missing_event_queue sg state.

Definition q_post_queue_facts sg state eid node q free slots : Prop :=
  UCOS2_state_inv sg state /\ q_post_lookup state eid node /\
  node.(eventType) = OS_EVENT_TYPE_Q /\ node.(queueFields) = Some q /\
  node.(waitList) = [] /\ queue_fields_consistency sg [] q /\
  queue_published_storage_binding state.(EventState) /\
  queue_pool_partition sg state.(EventState) free /\
  state.(EventState).(publishedQueueBytes) q.(qID) = Some slots /\
  queue_slots_model q slots.

Lemma q_post_queue_current : forall sg state eid node,
  UCOS2_state_inv sg state -> q_post_lookup state eid node ->
  node.(eventType) = OS_EVENT_TYPE_Q -> q_post_group state node = 0 ->
  exists q, node.(queueFields) = Some q /\ node.(waitList) = [] /\
    queue_fields_consistency sg [] q.
Proof.
  intros sg state eid node Hvalid Hnode Htype Hgroup.
  pose proof Hvalid as [_ [_ [_ [Hevents _]]]].
  pose proof Hevents as [_ [_ [_ [_ [Hpayload [_ Hentries]]]]]].
  pose proof (proj1 (encode_event_wait_grp_zero_iff_empty sg state.(TskState)
    node.(waitList) (proj1 (Hentries eid node Hnode))) Hgroup) as Hempty.
  specialize (Hpayload eid node Hnode); unfold event_payload_consistency in Hpayload.
  rewrite Htype in Hpayload; destruct node.(queueFields) as [q|] eqn:Hq;
    [exists q; rewrite Hempty in Hpayload; auto|contradiction].
Qed.

Definition q_post_qcb_readonly (base : addr) (q : QueueFields) : Assertion :=
  (&(base # "os_q" ->ₛ "OSQPtr")) # Ptr |->_ **
  (&(base # "os_q" ->ₛ "OSQOut")) # Ptr |-> queue_out_addr q.

Definition q_post_qcb_cells (base : addr) (q : QueueFields) (qin count : Z) : Assertion :=
  (&(base # "os_q" ->ₛ "OSQIn")) # Ptr |-> qin **
  (&(base # "os_q" ->ₛ "OSQEntries")) # UShort |-> count **
  (&(base # "os_q" ->ₛ "OSQSize")) # UShort |-> q.(qSize) **
  (&(base # "os_q" ->ₛ "OSQEnd")) # Ptr |-> queue_end_addr q **
  (&(base # "os_q" ->ₛ "OSQStart")) # Ptr |-> q.(qStart) **
  q_post_qcb_readonly base q.

Lemma q_post_qcb_cells_equiv : forall sg q,
  q_post_profile sg -> valid_queue_id sg q.(qID) ->
  used_queue_control_block sg q --||--
    q_post_qcb_cells (qcb_addr sg q.(qID)) q (queue_in_addr q) (queue_entries q).
Proof.
  intros sg q [_ [_ [Hlayout [[Hmax Hsize] Harg]]]] Hqid.
  specialize (Hlayout q.(qID) Hqid).
  change (sizeof ("os_q") = sizeof_OS_Q) in Hsize.
  rewrite Hsize in Hlayout; fold (qcb_addr sg q.(qID)) in Hlayout.
  destruct Hlayout as [Hptr [Hstart [Hend [Hin [Hout [Hsz Hentries]]]]]].
  unfold q_post_qcb_cells, q_post_qcb_readonly.
  rewrite Hptr, Hstart, Hend, Hin, Hout, Hsz, Hentries.
  unfold used_queue_control_block; split; entailer!.
Qed.

Lemma q_post_queue_split : forall sg state eid node q,
  q_post_lookup state eid node -> node.(eventType) = OS_EVENT_TYPE_Q ->
  node.(queueFields) = Some q -> node.(waitList) = [] ->
  UCOS2_inv sg state |-- EX free slots,
    coq_prop (q_post_queue_facts sg state eid node q free slots) &&
    (used_queue_control_block sg q ** queue_buffer_rep q slots **
     q_post_queue_frame sg state eid free).
Proof.
  intros sg state eid node q Hnode Htype Hq Hempty.
  rewrite UCOS2_inv_split_event_queue; Intros.
  sep_apply_l_atomic (queue_storage_split_event sg state.(EventState) eid node q Hnode Hq).
  Intros free slots; unfold queue_buffer_rep; Intros.
  assert (Hqvalid : queue_fields_consistency sg [] q).
  { match goal with H : UCOS2_state_inv sg state |- _ =>
      pose proof H as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]] end.
    specialize (Hpayload eid node Hnode); unfold event_payload_consistency in Hpayload.
    rewrite Htype, Hq, Hempty in Hpayload; exact Hpayload. }
  Exists free slots; unfold q_post_queue_frame, q_post_queue_facts, queue_buffer_rep; entailer!.
Qed.

Lemma q_post_queue_merge_original : forall sg state eid node q free slots,
  q_post_queue_facts sg state eid node q free slots ->
  used_queue_control_block sg q ** queue_buffer_rep q slots **
    q_post_queue_frame sg state eid free |-- UCOS2_inv sg state.
Proof.
  intros sg state eid node q free slots
    [Hvalid [Hnode [Htype [Hq [Hempty [Hqvalid [Hbinding [Hpart [Hslots Hmodel]]]]]]]]].
  assert (Hfocus : used_queue_control_block sg q ** queue_buffer_rep q slots |--
    published_queue_node_rep sg state.(EventState) eid node).
  { unfold published_queue_node_rep; rewrite Hq; Exists slots; entailer!. }
  unfold q_post_queue_frame; sep_apply_l_atomic Hfocus.
  sep_apply_l_atomic (store_map_merge (published_queue_node_rep sg state.(EventState))
    eid node state.(EventState).(inUsedEventStates) Hnode).
  rewrite UCOS2_inv_split_event_queue; unfold queue_storage_rep.
  entailer!; Exists free; entailer!.
Qed.

Definition q_post_enqueued_fields q message : QueueFields :=
  queue_with_contents q (queue_advance_index q.(qSize) q.(qInIndex))
    q.(qOutIndex) (q.(qMessages) ++ [message]).

Definition q_post_enqueue_state state eid node q message slots : UCOS2_Verify_State :=
  replace_EventS (queue_update state.(EventState) eid node
    (q_post_enqueued_fields q message) (q_post_enqueue_slots false q message slots)) state.

Lemma q_post_enqueue_back_some : forall q message,
  queue_entries q < q.(qSize) ->
  queue_enqueue_back q message = Some (q_post_enqueued_fields q message).
Proof.
  intros; unfold queue_enqueue_back, q_post_enqueued_fields.
  rewrite (proj2 (Z.ltb_lt _ _) H); reflexivity.
Qed.

Lemma q_post_nonfull_bounds : forall sg q,
  queue_fields_consistency sg [] q -> queue_entries q < q.(qSize) ->
  0 < q.(qSize) /\ 0 <= q.(qInIndex) < q.(qSize) /\
  0 <= queue_entries q < 65535 /\
  queue_in_addr q + 4 <= queue_end_addr q.
Proof.
  intros sg q Hvalid Hroom.
  pose proof (Zlength_nonneg q.(qMessages)) as Hcount.
  fold (queue_entries q) in Hcount.
  assert (Hsize : 0 < q.(qSize)) by lia.
  pose proof (queue_fields_consistency_positive sg [] q Hvalid Hsize) as [Hin Hrest].
  pose proof Hvalid as [_ [_ [Hsize_bound _]]].
  unfold queue_in_addr, queue_end_addr, event.sizeof_ptr; repeat split; lia.
Qed.

Lemma q_post_slot_split : forall sg q slots,
  queue_fields_consistency sg [] q -> queue_entries q < q.(qSize) ->
  queue_buffer_rep q slots |--
  coq_prop (queue_slots_model q slots) &&
    (queue_in_addr q # Ptr |->_ **
     PtrArray.mixed_missing_i q.(qStart) q.(qInIndex) 0 q.(qSize) slots).
Proof.
  intros sg q slots Hvalid Hroom.
  pose proof (q_post_nonfull_bounds sg q Hvalid Hroom) as [_ [Hin _]].
  sep_apply_l_atomic (queue_buffer_split_slot q slots q.(qInIndex) Hin).
  Intros.
  unfold PtrArray.mixedstoreA.
  destruct (Znth q.(qInIndex) slots None) as [value|];
    cbn [StorePtrAsElement.storeA StorePtrAsElement.undefstoreA].
  - sep_apply_l_atomic (store_ptr_undef_store_ptr
      (q.(qStart) + q.(qInIndex) * ptr_size_Z) value); entailer!.
  - entailer!.
Qed.

Lemma q_post_enqueue_merge : forall sg state eid node q free slots message,
  q_post_queue_facts sg state eid node q free slots ->
  queue_entries q < q.(qSize) ->
  used_queue_control_block sg (q_post_enqueued_fields q message) **
    queue_in_addr q # Ptr |-> message **
    PtrArray.mixed_missing_i q.(qStart) q.(qInIndex) 0 q.(qSize) slots **
    q_post_queue_frame sg state eid free |--
  UCOS2_inv sg (q_post_enqueue_state state eid node q message slots).
Proof.
  intros sg state eid node q free slots message
    [Hvalid [Hnode [Htype [Hq [Hempty [Hqvalid [Hbinding [Hpart [Hslots Hmodel]]]]]]]]] Hroom.
  pose proof (q_post_enqueue_back_some q message Hroom) as Hstep.
  sep_apply_l_atomic (queue_enqueue_back_merge_buffer sg q slots message
    (q_post_enqueued_fields q message) Hqvalid Hmodel Hstep).
  unfold q_post_enqueue_state, q_post_queue_frame, queue_buffer_rep; Intros.
  pose proof (q_post_enqueue_merge_global sg QueuePostBack state eid node q message
    (q_post_enqueued_fields q message) slots free Hvalid Hbinding Hpart Hnode Htype Hq
    Hempty Hmodel Hstep) as Hmerge.
  cbn zeta in Hmerge; sep_apply_r_atomic Hmerge.
  unfold q_post_enqueue_slots; entailer!.
Qed.

Definition q_post_next_in (q : QueueFields) : addr :=
  if Z.eqb (queue_in_addr q + Ucos2Verify.lib.event.sizeof_ptr) (queue_end_addr q)
  then q.(qStart) else queue_in_addr q + Ucos2Verify.lib.event.sizeof_ptr.

Lemma q_post_qcb_enqueued_equiv : forall sg q message,
  q_post_profile sg -> valid_queue_id sg q.(qID) -> queue_entries q < q.(qSize) ->
  q_post_qcb_cells (qcb_addr sg q.(qID)) q (q_post_next_in q) (queue_entries q + 1) --||--
  used_queue_control_block sg (q_post_enqueued_fields q message).
Proof.
  intros sg q message Hprofile Hqid Hroom.
  assert (Hnext : queue_in_addr (q_post_enqueued_fields q message) = q_post_next_in q).
  { unfold q_post_next_in; rewrite queue_in_advance_end_eqb.
    unfold queue_in_addr, q_post_enqueued_fields, queue_with_contents; cbn.
    unfold queue_advance_index; destruct (Z.eqb (q.(qInIndex) + 1) q.(qSize));
      unfold Ucos2Verify.lib.event.sizeof_ptr; lia. }
  assert (Hcount : queue_entries (q_post_enqueued_fields q message) = queue_entries q + 1).
  { unfold queue_entries, q_post_enqueued_fields, queue_with_contents; cbn.
    rewrite Zlength_app, Zlength_cons, Zlength_nil; lia. }
  rewrite (q_post_qcb_cells_equiv sg (q_post_enqueued_fields q message) Hprofile Hqid).
  rewrite Hnext, Hcount.
  unfold q_post_qcb_cells, q_post_qcb_readonly, queue_end_addr, queue_out_addr,
    q_post_enqueued_fields, queue_with_contents; reflexivity.
Qed.

Lemma q_post_pointer_split : forall sg state eid node q,
  q_post_lookup state eid node -> node.(eventType) = OS_EVENT_TYPE_Q ->
  node.(queueFields) = Some q ->
  UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state) &&
    ((event_addr sg eid + OSEventPtr_off) # Ptr |-> qcb_addr sg q.(qID) **
      q_post_field_frame sg state eid node EventPtrField).
Proof.
  intros sg state eid node q Hnode Htype Hq.
  pose proof (q_post_field_split_full sg state eid node EventPtrField Hnode ltac:(simpl; tauto)) as Hsplit.
  cbn [event_image event_cell event_field_offset] in Hsplit.
  unfold encode_event_ptr_value, verification_slice_encode_event_ptr_value in Hsplit.
  rewrite Htype, Hq in Hsplit; exact Hsplit.
Qed.

Lemma q_post_pointer_merge : forall sg state eid node q,
  UCOS2_state_inv sg state -> q_post_lookup state eid node ->
  node.(eventType) = OS_EVENT_TYPE_Q -> node.(queueFields) = Some q ->
  (event_addr sg eid + OSEventPtr_off) # Ptr |-> qcb_addr sg q.(qID) **
    q_post_field_frame sg state eid node EventPtrField |-- UCOS2_inv sg state.
Proof.
  intros sg state eid node q Hvalid Hnode Htype Hq.
  pose proof (q_post_field_merge_full sg state eid node EventPtrField Hvalid Hnode ltac:(simpl; tauto)) as Hmerge.
  cbn [event_image event_cell event_field_offset] in Hmerge.
  unfold encode_event_ptr_value, verification_slice_encode_event_ptr_value in Hmerge.
  rewrite Htype, Hq in Hmerge; exact Hmerge.
Qed.
