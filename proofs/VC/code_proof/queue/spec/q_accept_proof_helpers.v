Require Export Ucos2Verify.VC.code.queue.spec.q_accept_annotation_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_query_proof_helpers.
Require Import Ucos2Verify.lib.field_storage.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic MapLib ArrayLib.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

Lemma q_accept_pointer_split : forall sg entry eid current q,
  mutex_query_lookup entry eid current -> current.(eventType) = OS_EVENT_TYPE_Q ->
  current.(queueFields) = Some q ->
  UCOS2_inv sg entry |-- coq_prop (UCOS2_state_inv sg entry) &&
    ((event_addr sg eid + OSEventPtr_off) # Ptr |-> qcb_addr sg q.(qID) **
      q_accept_pointer_frame sg entry eid current).
Proof.
  intros sg entry eid current q Hlookup Htype Hq.
  rewrite UCOS2_inv_split_event_queue; Intros.
  sep_apply_l_atomic (event_raw_rep_split_eid sg entry.(TskState) entry.(EventState) eid current Hlookup).
  unfold used_event_rep.
  sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg entry.(TskState) current) EventPtrField ltac:(simpl; tauto)).
  cbn [event_cell event_field_offset event_image].
  unfold encode_event_ptr_value, verification_slice_encode_event_ptr_value; rewrite Htype, Hq.
  unfold q_accept_pointer_frame, OSEventPtr_off; entailer!.
Qed.

Lemma q_accept_pointer_merge : forall sg entry eid current q,
  UCOS2_state_inv sg entry -> mutex_query_lookup entry eid current ->
  current.(eventType) = OS_EVENT_TYPE_Q -> current.(queueFields) = Some q ->
  (event_addr sg eid + OSEventPtr_off) # Ptr |-> qcb_addr sg q.(qID) **
    q_accept_pointer_frame sg entry eid current |-- UCOS2_inv sg entry.
Proof.
  intros sg entry eid current q Hvalid Hlookup Htype Hq.
  assert (Hptr : event_image sg entry.(TskState) current EventPtrField = Some (qcb_addr sg q.(qID))).
  { unfold event_image, encode_event_ptr_value, verification_slice_encode_event_ptr_value; rewrite Htype, Hq; reflexivity. }
  pose proof (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg entry.(TskState) current) EventPtrField ltac:(simpl; tauto)) as Hmerge.
  rewrite Hptr in Hmerge; cbn [event_cell event_field_offset] in Hmerge.
  unfold q_accept_pointer_frame, OSEventPtr_off; sepcon_right_assoc.
  sep_apply_l_atomic Hmerge; fold (used_event_rep sg entry.(TskState) eid current).
  sep_apply_l_atomic (event_raw_rep_merge_eid sg entry.(TskState) entry.(EventState) eid current Hlookup).
  rewrite UCOS2_inv_split_event_queue; entailer!.
Qed.

Lemma q_accept_qcb_cells_equiv : forall sg base q,
  base = qcb_addr sg q.(qID) -> q_accept_queue_layout sg q.(qID) ->
  used_queue_control_block sg q --||-- q_accept_qcb_cells base q (queue_out_addr q) (queue_entries q).
Proof.
  intros sg base q -> [Hptr [Hstart [Hend [Hin [Hout [Hsize Hentries]]]]]].
  unfold q_accept_qcb_cells, q_accept_qcb_readonly.
  rewrite Hptr, Hstart, Hend, Hin, Hout, Hsize, Hentries.
  unfold used_queue_control_block; split; entailer!.
Qed.

Lemma q_accept_qcb_dequeue_equiv : forall sg base q,
  base = qcb_addr sg q.(qID) -> q_accept_queue_layout sg q.(qID) ->
  q_accept_qcb_cells base q (q_accept_next_out q) (queue_entries q - 1) --||--
  qcb_storage_rep sg q.(qID) (qcb_dequeue_front q (qcb_fields_image q)).
Proof.
  intros sg base q -> [Hptr [Hstart [Hend [Hin [Hout [Hsize Hentries]]]]]].
  unfold q_accept_qcb_cells, q_accept_qcb_readonly.
  rewrite Hptr, Hstart, Hend, Hin, Hout, Hsize, Hentries.
  unfold qcb_storage_rep, qcb_fields.
  repeat rewrite QueueFieldStorage.store_fields_cons by
    (repeat constructor; simpl; intuition discriminate).
  rewrite QueueFieldStorage.store_fields_nil.
  unfold qcb_dequeue_front, q_accept_next_out.
  destruct (Z.eqb (queue_out_addr q + Ucos2Verify.lib.event.sizeof_ptr) (queue_end_addr q));
    unfold qcb_write, field_update, qcb_fields_image; simpl;
    cbn [qcb_cell qcb_field_offset];
    split; entailer!.
Qed.

Lemma q_accept_dequeue_merge : forall sg entry eid current q next message slots free,
  UCOS2_state_inv sg entry -> mutex_query_lookup entry eid current -> current.(eventType) = OS_EVENT_TYPE_Q ->
  q_accept_store_facts sg entry eid current q free slots (qcb_addr sg q.(qID)) ->
  queue_dequeue_front q = Some (message, next) ->
  qcb_storage_rep sg q.(qID) (qcb_dequeue_front q (qcb_fields_image q)) ** queue_buffer_rep q slots **
    q_query_queue_frame sg entry eid free |-- UCOS2_inv sg (q_accept_after entry eid current next slots).
Proof.
  intros sg entry eid current q next message slots free Hvalid Hlookup Htype
    [Hprofile [Hid [Hbase [Hq [Hqvalid [Hbinding [Hpart Hslots]]]]]]] Hstep.
  sep_apply_l_atomic (queue_dequeue_front_reconstructs_node sg current.(waitList) q slots message next Hqvalid Hstep).
  unfold queue_buffer_rep; Intros.
  unfold q_query_queue_frame, q_accept_after.
  assert (Hqmodel : queue_slots_model q slots).
  { destruct (proj1 Hbinding eid current q Hlookup Hq) as [_ [bytes [Hbytes Hmodel]]].
    assert (bytes = slots) by congruence; subst bytes; exact Hmodel. }
  pose proof (UCOS2_inv_merge_queue_dequeue sg entry eid current q message next slots free
    Hvalid Hbinding Hpart Hlookup Htype Hq Hqmodel Hstep) as Hmerge.
  sep_apply_r_atomic Hmerge; entailer!.
Qed.

Lemma q_accept_dequeue_endpoint : forall sg entry eid current q next message slots,
  mutex_query_lookup entry eid current -> current.(queueFields) = Some q ->
  entry.(EventState).(publishedQueueBytes) q.(qID) = Some slots ->
  queue_dequeue_front q = Some (message, next) ->
  q_accept_critical sg eid entry (message, OS_ERR_NONE) (q_accept_after entry eid current next slots).
Proof.
  intros sg entry eid current q next message slots Hlookup Hq Hslots Hstep.
  assert (Hcount : 0 < queue_entries q).
  { unfold queue_dequeue_front in Hstep; destruct q.(qMessages) as [|head rest] eqn:Hmessages; [discriminate|].
    unfold queue_entries; rewrite Hmessages, Zlength_cons; pose proof (Zlength_nonneg rest); lia. }
  exists current, q; split; [exact Hlookup|]; split; [exact Hq|].
  rewrite (proj2 (Z.ltb_lt _ _) Hcount); exists message, next, slots; repeat split; assumption || reflexivity.
Qed.

Lemma q_accept_empty_endpoint : forall sg entry eid current q,
  mutex_query_lookup entry eid current -> current.(queueFields) = Some q -> queue_entries q <= 0 ->
  q_accept_critical sg eid entry (0, OS_ERR_Q_EMPTY) entry.
Proof.
  intros; exists current, q; split; [assumption|]; split; [assumption|].
  rewrite (proj2 (Z.ltb_ge _ _) H1); split; reflexivity.
Qed.
