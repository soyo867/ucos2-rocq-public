Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From Ucos2Verify.VC.code.queue Require Import q_accept_goal.
From Ucos2Verify.VC.code.queue Require Import q_accept_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.queue.spec.q_accept_api_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

Require Import Ucos2Verify.VC.code.queue.spec.q_accept_proof_helpers.
Require Import Ucos2Verify.VC.code.queue.spec.q_query_proof_helpers.

Lemma proof_of_OSQAccept_entail_wit_1 : OSQAccept_entail_wit_1.
Proof.
  pre_process.
  prop_apply_p (store_uchar_range (&(pe # "os_event" ->ₛ "OSEventType")) (event_slot_type_value before.(EventState) eid)).
  entailer!.
Qed.

Lemma proof_of_OSQAccept_return_wit_1 : OSQAccept_return_wit_1.
Proof.
  pre_process.
  unfold q_accept_api_restore_post; Intros returned.
  match goal with H : q_accept_finished _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hfinished Hinterval] end.
  assert (Hstep : q_accept_call_program critical sg invocation pe before (message_2, q_accept_success) after_2).
  { eapply (q_accept_call_endpoint critical sg invocation pe before eid observed mask retval entry_2 after_2 current_2 message_2 q_accept_success); try eassumption; congruence. }
  assert (Hapi : q_accept_api_program critical sg invocation pe before (q_accept_success, message_2) returned).
  { eapply q_accept_api_restored_return; [reflexivity|exact Hstep|exact Hinterval]. }
  assert (Hsafe : q_accept_return_safe returned message_2 q_accept_success X).
  { eapply q_accept_api_safe_return; eassumption. }
  Exists q_accept_success returned.
  unfold q_accept_api_post; subst; cbn [q_accept_success q_accept_empty encode_os_err_code]; entailer!.
Qed.

Lemma proof_of_OSQAccept_return_wit_2 : OSQAccept_return_wit_2.
Proof.
  pre_process.
  unfold q_accept_api_restore_post; Intros returned.
  match goal with H : q_accept_finished _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hfinished Hinterval] end.
  assert (Hstep : q_accept_call_program critical sg invocation pe before (message_2, q_accept_success) after_2).
  { eapply (q_accept_call_endpoint critical sg invocation pe before eid observed mask retval entry_2 after_2 current_2 message_2 q_accept_success); try eassumption; congruence. }
  assert (Hapi : q_accept_api_program critical sg invocation pe before (q_accept_success, message_2) returned).
  { eapply q_accept_api_restored_return; [reflexivity|exact Hstep|exact Hinterval]. }
  assert (Hsafe : q_accept_return_safe returned message_2 q_accept_success X).
  { eapply q_accept_api_safe_return; eassumption. }
  Exists q_accept_success returned.
  unfold q_accept_api_post; subst; cbn [q_accept_success q_accept_empty encode_os_err_code]; entailer!.
Qed.

Lemma proof_of_OSQAccept_return_wit_3 : OSQAccept_return_wit_3.
Proof.
  pre_process.
  unfold q_accept_api_restore_post; Intros returned.
  match goal with H : q_accept_finished _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hfinished Hinterval] end.
  assert (Hstep : q_accept_call_program critical sg invocation pe before (0, q_accept_empty) entry_2).
  { eapply (q_accept_call_endpoint critical sg invocation pe before eid observed mask retval entry_2 entry_2 current_2 0 q_accept_empty); try eassumption; congruence. }
  assert (Hapi : q_accept_api_program critical sg invocation pe before (q_accept_empty, 0) returned).
  { eapply q_accept_api_restored_return; [reflexivity|exact Hstep|exact Hinterval]. }
  assert (Hsafe : q_accept_return_safe returned 0 q_accept_empty X).
  { eapply q_accept_api_safe_return; eassumption. }
  Exists q_accept_empty returned.
  unfold q_accept_api_post; subst; cbn [q_accept_success q_accept_empty encode_os_err_code]; entailer!.
Qed.

Lemma proof_of_OSQAccept_return_wit_4 : OSQAccept_return_wit_4.
Proof.
  pre_process.
  assert (Hstep : q_accept_call_program critical sg invocation pe before (0, OS_ERR_EVENT_TYPE) before).
  { eapply q_accept_call_wrong_type; try eassumption; congruence. }
  assert (Hapi : q_accept_api_program critical sg invocation pe before (OS_ERR_EVENT_TYPE, 0) before).
  { eapply q_accept_api_early_return; [reflexivity|exact Hstep]. }
  assert (Hsafe : q_accept_return_safe before 0 OS_ERR_EVENT_TYPE X).
  { eapply q_accept_api_safe_return; eassumption. }
  Exists OS_ERR_EVENT_TYPE before; unfold q_accept_api_post; subst; cbn [encode_os_err_code]; entailer!.
Qed.

Lemma proof_of_OSQAccept_return_wit_5 : OSQAccept_return_wit_5.
Proof.
  pre_process.
  assert (Hzero : pe = 0) by congruence.
  assert (Hstep : q_accept_call_program critical sg invocation pe before (0, OS_ERR_PEVENT_NULL) before).
  { rewrite Hzero; apply q_accept_call_null. }
  assert (Hapi : q_accept_api_program critical sg invocation pe before (OS_ERR_PEVENT_NULL, 0) before).
  { eapply q_accept_api_early_return; [reflexivity|exact Hstep]. }
  assert (Hsafe : q_accept_return_safe before 0 OS_ERR_PEVENT_NULL X).
  { eapply q_accept_api_safe_return; eassumption. }
  Exists OS_ERR_PEVENT_NULL before; unfold q_accept_api_post; subst; cbn [encode_os_err_code]; entailer!.
Qed.

Lemma proof_of_OSQAccept_partial_solve_wit_9_pure : OSQAccept_partial_solve_wit_9_pure.
Proof.
  pre_process; unfold q_accept_next_out, Ucos2Verify.lib.event.sizeof_ptr;
  destruct (Z.eqb (queue_out_addr q + 4) (queue_end_addr q)) eqn:Hwrap;
  [apply Z.eqb_eq in Hwrap|apply Z.eqb_neq in Hwrap]; entailer!.
Qed.

Lemma proof_of_OSQAccept_partial_solve_wit_10_pure : OSQAccept_partial_solve_wit_10_pure.
Proof.
  pre_process; unfold q_accept_next_out, Ucos2Verify.lib.event.sizeof_ptr;
  destruct (Z.eqb (queue_out_addr q + 4) (queue_end_addr q)) eqn:Hwrap;
  [apply Z.eqb_eq in Hwrap|apply Z.eqb_neq in Hwrap]; entailer!.
Qed.

Lemma proof_of_OSQAccept_which_implies_wit_1 : OSQAccept_which_implies_wit_1.
Proof.
  pre_process.
  pose proof PreH3 as [Hzero|[_ [Haddr [Hid [Hslot Hprotocol]]]]]; [contradiction|].
  rewrite mutex_query_closed_equiv.
  change (sem_query_public_slot before eid observed) in Hslot.
  sep_apply_l_atomic (sem_query_type_split_full sg before eid observed Hslot).
  pose proof PreH2 as [_ [_ [Hlayout _]]]; destruct (Hlayout eid Hid) as [Htype Hptr].
  rewrite Haddr in *; rewrite Htype; unfold q_accept_type_frame; entailer!.
Qed.

Lemma proof_of_OSQAccept_which_implies_wit_2 : OSQAccept_which_implies_wit_2.
Proof.
  pre_process.
  pose proof PreH2 as [_ [_ [Hlayout _]]]; destruct (Hlayout eid PreH4) as [Htype Hptr].
  rewrite PreH3, Htype; unfold q_accept_type_frame.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid PreH1).
  rewrite mutex_query_closed_equiv; entailer!.
Qed.

Lemma proof_of_OSQAccept_which_implies_wit_3 : OSQAccept_which_implies_wit_3.
Proof.
  pre_process.
  pose proof PreH7 as [Hzero|[_ [Haddr [Hid [Hslot Hprotocol]]]]]; [contradiction|].
  specialize (Hprotocol PreH8).
  destruct (q_query_public_slot_is_queue before eid observed Hslot PreH8) as [Hlookup Htype].
  pose proof PreH3 as [_ [_ [Hlayout _]]]; destruct (Hlayout eid Hid) as [Htypeaddr Hptr].
  rewrite Haddr, Htypeaddr; unfold q_accept_type_frame.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid PreH2).
  unfold q_accept_save_pre; entailer!.
Qed.

Lemma proof_of_OSQAccept_which_implies_wit_4 : OSQAccept_which_implies_wit_4.
Proof.
  pre_process.
  pose proof PreH1 as [_ [Hvalid [_ [_ [Hlookup [_ [Htype _]]]]]]].
  destruct (q_query_current_fields sg entry_2 eid current_2 Hvalid Hlookup Htype) as [q [Hq Hqvalid]].
  sep_apply_l_atomic (q_accept_pointer_split sg entry_2 eid current_2 q Hlookup Htype Hq).
  Intros. Exists entry_2 current_2 q.
  pose proof PreH2 as [_ [_ [Hlayout _]]]; destruct (Hlayout eid PreH3) as [Htypeaddr Hptr].
  rewrite PreH4, Hptr; unfold q_accept_pointer_context; entailer!.
Qed.

Lemma proof_of_OSQAccept_which_implies_wit_5 : OSQAccept_which_implies_wit_5.
Proof.
  pre_process.
  unfold q_accept_pointer_context; Intros.
  match goal with H : q_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hfacts [Hprofile [Hid Hq]]] end.
  pose proof Hfacts as [_ [Hvalid [_ [_ [Hlookup [_ [Htype _]]]]]]].
  destruct (q_query_current_fields sg entry_2 eid current_2 Hvalid Hlookup Htype) as [q0 [Hq0 Hqvalid]].
  assert (q0 = q_2) by congruence; subst q0.
  pose proof Hprofile as [_ [_ [Hevents Hqueues]]].
  destruct (Hevents eid Hid) as [Htypeaddr Hptr].
  rewrite PreH2, Hptr.
  sep_apply_l_atomic (q_accept_pointer_merge sg entry_2 eid current_2 q_2 Hvalid Hlookup Htype Hq).
  sep_apply_l_atomic (q_query_queue_split sg entry_2 eid current_2 q_2 Hlookup Hq).
  Intros free slots.
  pose proof Hqvalid as [Hqid _].
  sep_apply_l_atomic (proj1 (q_accept_qcb_cells_equiv sg pq q_2 PreH1 (Hqueues _ Hqid))).
  Exists entry_2 current_2 free slots q_2.
  pose proof (queue_entries_in_range sg current_2.(waitList) q_2 Hqvalid) as Hbounds.
  unfold q_accept_store_context, q_accept_store_facts, q_accept_qcb_cells; entailer!.
Qed.

Lemma proof_of_OSQAccept_which_implies_wit_6 : OSQAccept_which_implies_wit_6.
Proof.
  pre_process.
  unfold q_accept_store_context; Intros.
  match goal with H : q_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hfacts Hstore] end.
  pose proof Hstore as [Hprofile [Hid [Hbase [Hq [Hqvalid [Hbinding [Hpart Hslots]]]]]]].
  assert (Hpop : exists message next, queue_dequeue_front q_2 = Some (message, next)).
  { unfold queue_dequeue_front; destruct q_2.(qMessages) as [|message rest] eqn:Hmessages; [|eauto].
    unfold queue_entries in PreH1; rewrite Hmessages, Zlength_nil in PreH1; lia. }
  destruct Hpop as [message [next Hpop]].
  sep_apply_l_atomic (queue_buffer_split_head sg current_2.(waitList) q_2 slots_2 message next Hqvalid Hpop).
  Intros.
  match goal with Hmodel : queue_slots_model q_2 slots_2 |- _ =>
    pose proof (queue_dequeue_front_head_slot sg current_2.(waitList) q_2 slots_2 message next Hqvalid Hmodel Hpop) as Hhead end.
  pose proof (queue_entries_in_range sg current_2.(waitList) q_2 Hqvalid) as Hbounds.
  Exists entry_2 current_2 next free_2 slots_2 message q_2.
  unfold q_accept_dequeue_context, q_accept_store_context, q_accept_head_slot; entailer!.
Qed.

Lemma proof_of_OSQAccept_which_implies_wit_7 : OSQAccept_which_implies_wit_7.
Proof.
  pre_process.
  unfold q_accept_dequeue_context, q_accept_store_context, q_accept_head_slot; Intros.
  match goal with H : queue_dequeue_front _ = _ /\ _ |- _ => destruct H as [Hpop Hhead] end.
  match goal with H : q_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H as [Hfacts Hstore] end.
  match goal with H : 0 < queue_entries _ /\ _ |- _ => destruct H as [Hcount Hmodel] end.
  pose proof Hstore as [_ [_ [_ [_ [Hqvalid _]]]]].
  assert (Hqvalid' : q_query_queue_valid sg q_2) by (exists current_2.(waitList); exact Hqvalid).
  assert (Hread : q_query_read_message q_2 slots_2 message).
  { unfold q_query_read_message; rewrite (proj2 (Z.ltb_lt _ _) Hcount); exact Hhead. }
  pose proof (q_query_head_merge sg q_2 slots_2 message Hqvalid' Hcount Hread) as Hmerge.
  unfold q_query_head_slot in Hmerge.
  assert (Hmerge' : queue_out_addr q_2 # Ptr |-> message **
      PtrArray.mixed_missing_i q_2.(qStart) q_2.(qOutIndex) 0 q_2.(qSize) slots_2 |-- queue_buffer_rep q_2 slots_2).
  { sep_apply_r_atomic Hmerge; entailer!. }
  sep_apply_l_atomic Hmerge'.
  pose proof (queue_entries_in_range sg current_2.(waitList) q_2 Hqvalid) as Hbounds.
  Exists entry_2 current_2 next_2 free_2 slots_2 q_2 message; entailer!.
Qed.

Lemma proof_of_OSQAccept_which_implies_wit_8 : OSQAccept_which_implies_wit_8.
Proof.
  pre_process.
  unfold q_accept_dequeue_context, q_accept_store_context; Intros.
  match goal with H : queue_dequeue_front _ = _ /\ _ |- _ => destruct H as [Hpop Hhead] end.
  match goal with H : q_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H as [Hfacts Hstore] end.
  pose proof Hfacts as [_ [Hvalid [_ [_ [Hlookup [_ [Htype _]]]]]]].
  pose proof Hstore as [Hprofile [Hid [Hbase [Hq [Hqvalid [Hbinding [Hpart Hslots]]]]]]].
  pose proof Hqvalid as [Hqid _].
  pose proof Hprofile as [_ [_ [_ Hqueues]]].
  pose proof (proj1 (q_accept_qcb_dequeue_equiv sg pq q Hbase (Hqueues _ Hqid))) as Hcells.
  unfold q_accept_qcb_cells in Hcells; sep_apply_l_atomic Hcells.
  assert (Hstore' : q_accept_store_facts sg entry_2 eid current_2 q free slots (qcb_addr sg q.(qID))) by (rewrite <- Hbase; exact Hstore).
  sep_apply_l_atomic (q_accept_dequeue_merge sg entry_2 eid current_2 q next message slots free Hvalid Hlookup Htype Hstore' Hpop).
  Exists entry_2 (q_accept_after entry_2 eid current_2 next slots) current_2.
  pose proof (q_accept_dequeue_endpoint sg entry_2 eid current_2 q next message slots Hlookup Hq Hslots Hpop) as Hstep.
  unfold q_accept_restore_pre, q_accept_finished, q_accept_success; entailer!.
Qed.

Lemma proof_of_OSQAccept_which_implies_wit_9 : OSQAccept_which_implies_wit_9.
Proof.
  pre_process.
  unfold q_accept_store_context; Intros.
  match goal with H : q_accept_acquire_facts _ _ _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H as [Hfacts Hstore] end.
  pose proof Hfacts as [_ [Hvalid [_ [_ [Hlookup [_ [Htype _]]]]]]].
  pose proof Hstore as [Hprofile [Hid [Hbase [Hq [Hqvalid [Hbinding [Hpart Hslots]]]]]]].
  pose proof Hqvalid as [Hqid _]. pose proof Hprofile as [_ [_ [_ Hqueues]]].
  pose proof (proj2 (q_accept_qcb_cells_equiv sg pq q Hbase (Hqueues _ Hqid))) as Hcells.
  unfold q_accept_qcb_cells in Hcells; sep_apply_l_atomic Hcells.
  sep_apply_l_atomic (q_query_queue_merge sg entry_2 eid current_2 q free slots Hvalid Hbinding Hpart Hlookup Hq Hslots).
  Exists entry_2 current_2.
  pose proof (q_accept_empty_endpoint sg entry_2 eid current_2 q Hlookup Hq PreH1) as Hstep.
  unfold q_accept_restore_pre, q_accept_finished, q_accept_empty; entailer!.
Qed.
