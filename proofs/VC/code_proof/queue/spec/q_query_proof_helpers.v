Require Export Ucos2Verify.VC.code.queue.spec.q_query_annotation_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic MapLib ArrayLib.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

Lemma q_query_call_input_live : forall critical sg invocation pe pd before eid observed,
  q_query_call_input critical sg invocation pe pd before eid observed -> pe <> 0 -> pd <> 0 ->
  pe = event_addr sg eid /\ valid_event_id sg eid /\ q_query_public_slot before eid observed /\
  (event_slot_type_value before.(EventState) eid = 2 -> mutex_query_handle_protocol critical sg invocation eid).
Proof. intros critical sg invocation pe pd before eid observed [Hnull|[[Hpe Hpd]|Hlive]] Hnonnull1 Hnonnull2;
  try contradiction; tauto. Qed.

Lemma q_query_public_slot_is_queue : forall state eid observed,
  q_query_public_slot state eid observed -> event_slot_type_value state.(EventState) eid = 2 ->
  mutex_query_lookup state eid observed /\ observed.(eventType) = OS_EVENT_TYPE_Q.
Proof.
  intros state eid observed [Hused|[Hnone Hfree]] Htype; unfold event_slot_type_value in Htype.
  - unfold mutex_query_lookup in Hused; rewrite Hused in Htype; split; [exact Hused|].
    destruct observed.(eventType); simpl in Htype; try discriminate; reflexivity.
  - rewrite Hnone in Htype; discriminate.
Qed.

Lemma q_query_safe_return : forall (c : program UCOS2_Verify_State (Z * option QueueQuerySnapshot))
  before after code snapshot X,
  c before (code, snapshot) after ->
  safeExec (LastSeen before) (bind (atomic_cmd c) q_query_observe_error) X ->
  safeExec (LastSeen after) (StateRelMonad.ret code) X.
Proof.
  intros c before after code snapshot X Hsem Hexec.
  assert (Hatomic : hs_eval (atomic_cmd c) (LastSeen before) (LastSeen after) (code, snapshot)).
  { unfold hs_eval, LastSeen, atomic_cmd; intros P0 HP0.
    exists (RTrans_Abs after); split.
    - exists before, after; split; [apply HP0; exact I|].
      split; [exact Hsem|intro state; split; trivial].
    - intro state; split; trivial. }
  exact (highstepbind_derive _ _ _ (code, snapshot) (LastSeen after) Hatomic X Hexec).
Qed.

Lemma q_query_current_fields : forall sg entry eid node,
  UCOS2_state_inv sg entry -> mutex_query_lookup entry eid node -> node.(eventType) = OS_EVENT_TYPE_Q ->
  exists q, node.(queueFields) = Some q /\ queue_fields_consistency sg node.(waitList) q.
Proof.
  intros sg entry eid node Hvalid Hlookup Htype.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  specialize (Hpayload eid node Hlookup); unfold event_payload_consistency in Hpayload.
  rewrite Htype in Hpayload; destruct node.(queueFields) as [q|] eqn:Hq; [eauto|contradiction].
Qed.

Lemma q_query_read_facts_critical : forall sg entry eid node q free slots group rows message,
  q_query_read_facts sg entry eid node q free slots group rows -> q_query_read_message q slots message ->
  q_query_critical sg eid entry (queue_query_snapshot entry.(TskState) node q message) entry.
Proof.
  intros sg entry eid node q free slots group rows message
    [Hvalid [Hlookup [Htype [Hq [Hqvalid [Hbinding [Hpart [Hslots Hrest]]]]]]]] Hmessage.
  split; [reflexivity|]; exists node, q; split; [exact Hlookup|]; split; [exact Hq|].
  unfold q_query_read_message in Hmessage; destruct (Z.ltb 0 (queue_entries q)).
  - exists slots, message; auto.
  - subst message; reflexivity.
Qed.

Lemma q_query_queue_valid_bounds : forall sg q,
  q_query_queue_valid sg q -> valid_queue_id sg q.(qID) /\ 0 <= queue_entries q <= 65535.
Proof.
  intros sg q [waiters Hvalid].
  unfold queue_fields_consistency in Hvalid.
  destruct Hvalid as [Hqid [Hsize [Halign [Hshape Hrest]]]].
  split; [exact Hqid|].
  destruct Hshape as [[Hzero [_ [_ Hmessages]]]|[Hpositive [_ [_ [Hcount _]]]]].
  - unfold queue_entries; rewrite Hmessages, Zlength_nil; lia.
  - lia.
Qed.

Lemma q_query_head_split : forall sg q slots,
  q_query_queue_valid sg q -> 0 < queue_entries q ->
  queue_buffer_rep q slots |-- EX message,
    coq_prop (q_query_read_message q slots message) &&
    (queue_out_addr q # Ptr |-> message ** q_query_head_slot q slots).
Proof.
  intros sg q slots [waiters Hvalid] Hcount.
  assert (Hpop : exists message next, queue_dequeue_front q = Some (message, next)).
  { unfold queue_dequeue_front; destruct q.(qMessages) as [|message rest] eqn:Hmessages; [|eauto].
    unfold queue_entries in Hcount; rewrite Hmessages, Zlength_nil in Hcount; lia. }
  destruct Hpop as [message [next Hpop]].
  sep_apply_l_atomic (queue_buffer_split_head sg waiters q slots message next Hvalid Hpop).
  Exists message; unfold q_query_read_message, q_query_head_slot.
  rewrite (proj2 (Z.ltb_lt 0 (queue_entries q)) Hcount).
  Intros.
  match goal with Hmodel : queue_slots_model q slots |- _ =>
    pose proof (queue_dequeue_front_head_slot sg waiters q slots message next Hvalid Hmodel Hpop) as Hhead end.
  entailer!.
Qed.

Lemma q_query_event_fields_equiv : forall sg tasks eid node q,
  node.(eventType) = OS_EVENT_TYPE_Q -> node.(queueFields) = Some q ->
  used_event_rep sg tasks eid node --||--
  (q_query_event_unread sg eid node **
   (event_addr sg eid + OSEventPtr_off) # Ptr |-> qcb_addr sg q.(qID) **
   (event_addr sg eid + OSEventGrp_off) # UChar |-> encode_event_wait_grp node.(waitList) tasks **
   store_osprio_array (event_addr sg eid + OSEventTbl_off) (encode_event_wait_tbl_values_or node tasks)).
Proof.
  intros sg tasks eid node q Htype Hq.
  unfold used_event_rep, event_storage_rep, event_fields.
  destruct (cfgEventNames (osKernelConfig sg)) eqn:Hnames;
    cbn [app];
    repeat rewrite EventFieldStorage.store_fields_cons by
      (repeat constructor; simpl; intuition discriminate);
    rewrite EventFieldStorage.store_fields_nil;
    unfold q_query_event_unread; rewrite Hnames;
    cbn [event_image event_cell event_field_offset];
    unfold encode_event_ptr_value, verification_slice_encode_event_ptr_value;
    rewrite Htype, Hq;
    unfold store_osprio_array, store_array, oseventtbl_element_store,
      encode_event_wait_tbl_values_or, sizeof_OS_PRIO, OS_EVENT_TBL_SIZE,
      OSEventType_off, OSEventPtr_off, OSEventCnt_off, OSEventGrp_off, OSEventTbl_off;
    simpl; split; entailer!.
  all: rewrite <- !Z.add_assoc; entailer!.
Qed.

Lemma q_query_head_merge : forall sg q slots message,
  q_query_queue_valid sg q -> 0 < queue_entries q -> q_query_read_message q slots message ->
  queue_out_addr q # Ptr |-> message ** q_query_head_slot q slots |-- queue_buffer_rep q slots.
Proof.
  intros sg q slots message [waiters Hvalid] Hcount Hmessage.
  assert (Hsize : 0 < q.(qSize)).
  { destruct Hvalid as [_ [_ [_ [Hshape _]]]].
    destruct Hshape as [[Hsz [_ [_ Hmsgs]]]|[Hsz _]]; [|exact Hsz].
    unfold queue_entries in Hcount; rewrite Hmsgs, Zlength_nil in Hcount; lia. }
  pose proof (queue_fields_consistency_positive sg waiters q Hvalid Hsize) as [_ [Hout _]].
  unfold q_query_read_message in Hmessage; rewrite (proj2 (Z.ltb_lt _ _) Hcount) in Hmessage.
  unfold q_query_head_slot; Intros.
  match goal with H : _ /\ queue_slots_model q slots |- _ => destruct H as [_ Hmodel] end.
  match goal with Hmodel : queue_slots_model q slots |- _ =>
    pose proof (queue_buffer_merge_slot q slots q.(qOutIndex) Hmodel Hout) as Hmerge end.
  rewrite Hmessage in Hmerge.
  unfold PtrArray.mixedstoreA, StorePtrAsElement.storeA in Hmerge.
  change (queue_out_addr q # Ptr |-> message **
    PtrArray.mixed_missing_i q.(qStart) q.(qOutIndex) 0 q.(qSize) slots |-- queue_buffer_rep q slots) in Hmerge.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma q_query_qcb_read_equiv : forall sg q base,
  q_query_queue_at sg base q -> q_query_queue_layout sg q ->
  used_queue_control_block sg q --||--
    ((&(base # "os_q" ->ₛ "OSQOut")) # Ptr |-> queue_out_addr q **
     (&(base # "os_q" ->ₛ "OSQEntries")) # UShort |-> queue_entries q **
     (&(base # "os_q" ->ₛ "OSQSize")) # UShort |-> q.(qSize) ** q_query_qcb_unread sg q).
Proof.
  intros sg q base Hbase [Hout [Hsize Hentries]]; unfold q_query_queue_at in Hbase; subst base.
  rewrite Hout, Hsize, Hentries; unfold used_queue_control_block, q_query_qcb_unread; split; entailer!.
Qed.

Lemma q_query_source_row_split : forall base rows i,
  0 <= i < 8 -> store_osprio_array base rows |--
  (base + i) # UChar |-> Znth i rows 0 ** store_osprio_array_missing_i base rows i.
Proof.
  intros base rows i Hi; unfold store_osprio_array, store_osprio_array_missing_i.
  pose proof (store_array_split_to_missing_i Z oseventtbl_element_store base i
    OS_EVENT_TBL_SIZE rows 0 Hi) as Hsplit.
  unfold oseventtbl_element_store, sizeof_OS_PRIO in Hsplit.
  rewrite Z.mul_1_r in Hsplit; exact Hsplit.
Qed.

Lemma q_query_source_row_merge : forall base rows i,
  0 <= i < 8 ->
  (base + i) # UChar |-> Znth i rows 0 ** store_osprio_array_missing_i base rows i
    |-- store_osprio_array base rows.
Proof.
  intros base rows i Hi; unfold store_osprio_array, store_osprio_array_missing_i.
  pose proof (store_array_missing_i_merge_to_array Z oseventtbl_element_store base i
    OS_EVENT_TBL_SIZE (Znth i rows 0) rows Hi) as Hmerge.
  unfold oseventtbl_element_store, sizeof_OS_PRIO in Hmerge |- *.
  rewrite Z.mul_1_r, replace_Znth_Znth in Hmerge; exact Hmerge.
Qed.

Lemma q_query_output_array_equiv : forall base rows,
  store_osprio_array base rows --||-- UCharArray.full base 8 rows.
Proof.
  intros; unfold store_osprio_array, UCharArray.full, StoreUCharAsElement.sizeA,
    StoreUCharAsElement.storeA, oseventtbl_element_store, sizeof_OS_PRIO, OS_EVENT_TBL_SIZE.
  rewrite sizeof_uchar; split; reflexivity.
Qed.

Lemma q_query_read_split : forall sg entry eid node q,
  UCOS2_state_inv sg entry -> mutex_query_lookup entry eid node ->
  node.(eventType) = OS_EVENT_TYPE_Q -> node.(queueFields) = Some q ->
  queue_fields_consistency sg node.(waitList) q ->
  UCOS2_inv sg entry |-- EX free, EX slots,
    coq_prop (q_query_read_facts sg entry eid node q free slots
      (encode_event_wait_grp node.(waitList) entry.(TskState))
      (encode_event_wait_tbl_values_or node entry.(TskState))) &&
    (q_query_event_unread sg eid node **
     (event_addr sg eid + OSEventPtr_off) # Ptr |-> qcb_addr sg q.(qID) **
     (event_addr sg eid + OSEventGrp_off) # UChar |-> encode_event_wait_grp node.(waitList) entry.(TskState) **
     store_osprio_array (event_addr sg eid + OSEventTbl_off) (encode_event_wait_tbl_values_or node entry.(TskState)) **
     used_queue_control_block sg q ** queue_buffer_rep q slots ** q_query_kernel_rest sg entry eid free).
Proof.
  intros sg entry eid node q Hvalid Hlookup Htype Hq Hqvalid.
  sep_apply_l_atomic (q_query_queue_split sg entry eid node q Hlookup Hq).
  Intros free slots; unfold q_query_queue_frame.
  sep_apply_l_atomic (event_raw_rep_split_eid sg entry.(TskState) entry.(EventState) eid node Hlookup).
  sep_apply_l_atomic (proj1 (q_query_event_fields_equiv sg entry.(TskState) eid node q Htype Hq)).
  Exists free slots; unfold q_query_read_facts, q_query_kernel_rest; entailer!.
Qed.

Lemma q_query_read_merge : forall sg entry eid node q free slots group rows,
  q_query_read_facts sg entry eid node q free slots group rows ->
  q_query_event_unread sg eid node **
    (event_addr sg eid + OSEventPtr_off) # Ptr |-> qcb_addr sg q.(qID) **
    (event_addr sg eid + OSEventGrp_off) # UChar |-> group **
    store_osprio_array (event_addr sg eid + OSEventTbl_off) rows **
    used_queue_control_block sg q ** queue_buffer_rep q slots ** q_query_kernel_rest sg entry eid free
    |-- UCOS2_inv sg entry.
Proof.
  intros sg entry eid node q free slots group rows
    [Hvalid [Hlookup [Htype [Hq [Hqvalid [Hbinding [Hpart [Hslots [-> ->]]]]]]]]].
  sep_apply_l_atomic (proj2 (q_query_event_fields_equiv sg entry.(TskState) eid node q Htype Hq)).
  unfold q_query_kernel_rest.
  eapply derivable1_trans with
    ((used_event_rep sg entry.(TskState) eid node **
      event_raw_rep_no_eid sg entry.(TskState) entry.(EventState) eid) **
     used_queue_control_block sg q ** queue_buffer_rep q slots **
     store_map_missing_i (published_queue_node_rep sg entry.(EventState)) entry.(EventState).(inUsedEventStates) eid **
     store_free_queue_list sg free ** UCOS2_raw_rep_missing_event_queue sg entry).
  - entailer!.
  -
  sep_apply_l_atomic (event_raw_rep_merge_eid sg entry.(TskState) entry.(EventState) eid node Hlookup).
  pose proof (q_query_queue_merge sg entry eid node q free slots Hvalid Hbinding Hpart Hlookup Hq Hslots) as Hmerge.
  unfold q_query_queue_frame in Hmerge.
  eapply derivable1_trans; [|exact Hmerge]; entailer!.
Qed.
