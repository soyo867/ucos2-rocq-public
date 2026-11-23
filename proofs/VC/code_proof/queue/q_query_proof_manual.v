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
From Ucos2Verify.VC.code.queue Require Import q_query_goal.
From Ucos2Verify.VC.code.queue Require Import q_query_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.queue.spec.q_query_api_spec.
Require Import Ucos2Verify.lib.array_abstraction.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.
Require Import Ucos2Verify.VC.code.queue.spec.q_query_proof_helpers.

Lemma proof_of_OSQQuery_entail_wit_1_2 : OSQQuery_entail_wit_1_2.
Proof.
  pre_process.
  prop_apply_p (store_uchar_range (&(pe # "os_event" ->ₛ "OSEventType")) (event_slot_type_value before.(EventState) eid)).
  entailer!.
Qed.

Lemma proof_of_OSQQuery_entail_wit_2 : OSQQuery_entail_wit_2.
Proof.
  pre_process. Exists entry_2 current_2 free_2 slots_2 grp_2 q_2 rows_2. entailer!.
Qed.

Lemma proof_of_OSQQuery_entail_wit_3 : OSQQuery_entail_wit_3.
Proof.
  pre_process. Exists entry_2 current_2 free_2 slots_2 grp_2 q_2 rows_6. entailer!.
  all: cbn in *; lia.
Qed.

Lemma proof_of_OSQQuery_return_wit_1 : OSQQuery_return_wit_1.
Proof.
  pre_process.
  assert (Hfacts : q_query_acquire_facts critical sg invocation eid mask cpu_sr before entry observed current) by assumption.
  unfold q_query_restore_post; Intros returned.
  pose proof Hfacts as [Hentry [_ [[Hsaved Hmask] _]]].
  assert (Hprogram : q_query_program critical sg invocation eid pe pd before (0, Some snapshot) returned).
  { eapply q_query_program_success; try eassumption; congruence. }
  pose proof (q_query_api_safe_return critical sg invocation eid pe pd before returned
    0 (Some snapshot) X Hprogram PreH30) as Hsafe.
  unfold q_query_api_post; Exists (Some snapshot) returned.
  cbn [q_query_output_post]; rewrite Hmask.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSQQuery_return_wit_2 : OSQQuery_return_wit_2.
Proof.
  pre_process.
  assert (Hfacts : q_query_acquire_facts critical sg invocation eid mask cpu_sr before entry observed current) by assumption.
  unfold q_query_restore_post; Intros returned.
  pose proof Hfacts as [Hentry [_ [[Hsaved Hmask] _]]].
  assert (Hprogram : q_query_program critical sg invocation eid pe pd before (0, Some snapshot) returned).
  { eapply q_query_program_success; try eassumption; congruence. }
  pose proof (q_query_api_safe_return critical sg invocation eid pe pd before returned
    0 (Some snapshot) X Hprogram PreH30) as Hsafe.
  unfold q_query_api_post; Exists (Some snapshot) returned.
  cbn [q_query_output_post]; rewrite Hmask.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSQQuery_return_wit_3 : OSQQuery_return_wit_3.
Proof.
  pre_process.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  assert (Hslot : q_query_public_slot before eid observed) by assumption.
  assert (Hid : valid_event_id sg eid) by assumption.
  assert (Hprogram : q_query_program critical sg invocation eid pe pd before (1, None) before).
  { apply q_query_program_wrong_type; try assumption; congruence. }
  pose proof (q_query_api_safe_return critical sg invocation eid pe pd before before
    1 None X Hprogram PreH12) as Hsafe.
  unfold q_query_api_post; Exists (@None QueueQuerySnapshot) before.
  cbn [q_query_output_post]; rewrite PreH7; unfold q_query_type_frame.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid Hvalid).
  rewrite mutex_query_closed_equiv; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSQQuery_return_wit_4 : OSQQuery_return_wit_4.
Proof.
  pre_process.
  assert (Hzero : pd = 0) by congruence.
  assert (Hprogram : q_query_program critical sg invocation eid pe pd before (9, None) before).
  { rewrite Hzero; apply q_query_program_null_output; congruence. }
  pose proof (q_query_api_safe_return critical sg invocation eid pe pd before before
    9 None X Hprogram PreH5) as Hsafe.
  unfold q_query_api_post; Exists (@None QueueQuerySnapshot) before.
  cbn [q_query_output_post]; repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSQQuery_return_wit_5 : OSQQuery_return_wit_5.
Proof.
  pre_process.
  assert (Hzero : pe = 0) by congruence.
  assert (Hprogram : q_query_program critical sg invocation eid pe pd before (4, None) before).
  { rewrite Hzero; apply q_query_program_null_event. }
  pose proof (q_query_api_safe_return critical sg invocation eid pe pd before before
    4 None X Hprogram PreH4) as Hsafe.
  unfold q_query_api_post; Exists (@None QueueQuerySnapshot) before.
  cbn [q_query_output_post]; repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSQQuery_which_implies_wit_1 : OSQQuery_which_implies_wit_1.
Proof.
  pre_process.
  assert (Hinput : q_query_call_input critical sg invocation pe pd before eid observed) by assumption.
  destruct (q_query_call_input_live critical sg invocation pe pd before eid observed Hinput PreH1 PreH2)
    as [Haddr [Hid [Hslot Hprotocol]]].
  rewrite mutex_query_closed_equiv.
  change (sem_query_public_slot before eid observed) in Hslot.
  sep_apply_l_atomic (sem_query_type_split_full sg before eid observed Hslot).
  unfold q_query_type_frame; rewrite PreH3 in *; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSQQuery_which_implies_wit_2 : OSQQuery_which_implies_wit_2.
Proof.
  pre_process.
  assert (Hinput : q_query_call_input critical sg invocation pe pd before eid observed) by assumption.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  destruct (q_query_call_input_live critical sg invocation pe pd before eid observed Hinput PreH1 PreH2)
    as [Haddr [Hid [Hslot Hprotocol]]].
  specialize (Hprotocol PreH3).
  destruct (q_query_public_slot_is_queue before eid observed Hslot PreH3) as [Hlookup Htype].
  assert (Hencoded : encode_event_type observed.(eventType) = 2) by (rewrite Htype; reflexivity).
  rewrite PreH4 in *; unfold q_query_type_frame.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid Hvalid).
  sep_apply_l_atomic (q_query_save_pre_closed critical sg invocation before); entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSQQuery_which_implies_wit_3 : OSQQuery_which_implies_wit_3.
Proof.
  pre_process.
  assert (Hfacts : q_query_acquire_facts critical sg invocation eid mask cpu_sr before entry_2 observed current_2) by assumption.
  pose proof Hfacts as [_ [Hvalid [_ [_ [Hlookup [_ [Htype _]]]]]]].
  destruct (q_query_current_fields sg entry_2 eid current_2 Hvalid Hlookup Htype) as [q [Hq Hqvalid]].
  sep_apply_l_atomic (q_query_read_split sg entry_2 eid current_2 q Hvalid Hlookup Htype Hq Hqvalid).
  Intros free slots.
  Exists entry_2 current_2 free slots (encode_event_wait_grp current_2.(waitList) entry_2.(TskState))
    (encode_event_wait_tbl_values_or current_2 entry_2.(TskState)) q.
  assert (Hlayout : q_query_layout sg eid) by assumption.
  destruct Hlayout as [[Htypeaddr [Hptr Hcnt]] [[Hgrp Htbl] Hqueue]].
  rewrite PreH1 in *; rewrite Hptr, Hgrp, Htbl.
  unfold q_query_copy_frame.
  assert (Hqvalid' : q_query_queue_valid sg q) by (exists current_2.(waitList); exact Hqvalid).
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSQQuery_which_implies_wit_4 : OSQQuery_which_implies_wit_4.
Proof.
  pre_process. Exists entry_2 current_2 q_2 free_2 slots_2 grp_2 rows_2.
  unfold q_query_output_table.
  sep_apply_l_atomic (sem_query_output_table_init (&(p_q_data # "os_q_data" ->ₛ "OSEventTbl")) rows_2).
  entailer!.
Qed.

Lemma proof_of_OSQQuery_which_implies_wit_5 : OSQQuery_which_implies_wit_5.
Proof.
  pre_process. Exists entry_2 current_2 q_2 free_2 slots_2 grp_2 rows_2.
  sep_apply_l_atomic (q_query_source_row_split (&(pevent # "os_event" ->ₛ "OSEventTbl")) rows_2 i ltac:(lia)).
  unfold q_query_output_table, q_query_output_table_missing_i.
  sep_apply_l_atomic (sem_query_output_table_split (&(p_q_data # "os_q_data" ->ₛ "OSEventTbl")) rows_2 i ltac:(unfold OS_EVENT_TBL_SIZE; lia)).
  rewrite PreH4, PreH5; cbn; rewrite !Z.mul_1_r; entailer!.
Qed.

Lemma proof_of_OSQQuery_which_implies_wit_6 : OSQQuery_which_implies_wit_6.
Proof.
  pre_process. Exists entry_2 current_2 q_2 free_2 slots_2 grp_2 rows_2.
  cbn; rewrite !Z.mul_1_r.
  sep_apply_l_atomic (q_query_source_row_merge (&(pevent # "os_event" ->ₛ "OSEventTbl")) rows_2 i ltac:(lia)).
  unfold q_query_output_table, q_query_output_table_missing_i.
  sep_apply_l_atomic (sem_query_output_table_merge (&(p_q_data # "os_q_data" ->ₛ "OSEventTbl")) rows_2 i ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_OSQQuery_which_implies_wit_7 : OSQQuery_which_implies_wit_7.
Proof.
  pre_process. Exists entry_2 current_2 q_2 free_2 slots_2 grp_2 rows_2.
  unfold q_query_output_table.
  sep_apply_l_atomic (sem_query_output_table_complete (&(p_q_data # "os_q_data" ->ₛ "OSEventTbl")) rows_2 i
    ltac:(unfold OS_EVENT_TBL_SIZE; lia) ltac:(unfold OS_EVENT_TBL_SIZE; lia)).
  entailer!.
Qed.

Lemma proof_of_OSQQuery_which_implies_wit_8 : OSQQuery_which_implies_wit_8.
Proof.
  pre_process.
  assert (Hvalid : q_query_queue_valid sg q_2) by assumption.
  destruct (q_query_queue_valid_bounds sg q_2 Hvalid) as [Hqid Hbounds].
  assert (Hlayout : q_query_layout sg eid) by assumption.
  destruct Hlayout as [Hcore [Hwait Hqueues]].
  assert (Hat : q_query_queue_at sg pq q_2) by exact PreH1.
  sep_apply_l_atomic (proj1 (q_query_qcb_read_equiv sg q_2 pq Hat (Hqueues q_2 Hqid))).
  Exists entry_2 current_2 free_2 slots_2 grp_2 rows_2 q_2.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSQQuery_which_implies_wit_9 : OSQQuery_which_implies_wit_9.
Proof.
  pre_process.
  assert (Hvalid : q_query_queue_valid sg q_2) by assumption.
  sep_apply_l_atomic (q_query_head_split sg q_2 slots_2 Hvalid ltac:(lia)).
  Intros message.
  Exists entry_2 current_2 free_2 grp_2 rows_2 slots_2 message q_2.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSQQuery_which_implies_wit_10 : OSQQuery_which_implies_wit_10.
Proof.
  pre_process.
  assert (Hvalid : q_query_queue_valid sg q_2) by assumption.
  assert (Hread : q_query_read_message q_2 slots_2 message_2) by assumption.
  unfold q_query_head_slot; Intros.
  assert (Hcount : 0 < queue_entries q_2) by tauto.
  pose proof (q_query_head_merge sg q_2 slots_2 message_2 Hvalid Hcount Hread) as Hmerge.
  unfold q_query_head_slot in Hmerge.
  assert (Hcells : queue_out_addr q_2 # Ptr |-> message_2 **
    PtrArray.mixed_missing_i q_2.(qStart) q_2.(qOutIndex) 0 q_2.(qSize) slots_2 |-- queue_buffer_rep q_2 slots_2).
  { sep_apply_r_atomic Hmerge; entailer!. }
  sep_apply_l_atomic Hcells.
  Exists entry_2 current_2 free_2 grp_2 rows_2 slots_2 message_2 q_2.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSQQuery_which_implies_wit_11 : OSQQuery_which_implies_wit_11.
Proof.
  pre_process. Exists entry_2 current_2 free_2 grp_2 rows_2 slots_2 q_2.
  assert (Hread : q_query_read_message q_2 slots_2 0).
  { unfold q_query_read_message. rewrite (proj2 (Z.ltb_ge 0 (queue_entries q_2)) ltac:(lia)); reflexivity. }
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSQQuery_which_implies_wit_12 : OSQQuery_which_implies_wit_12.
Proof.
  pre_process.
  assert (Hat : q_query_queue_at sg pq q) by assumption.
  assert (Hlayout : q_query_layout sg eid) by assumption.
  assert (Hmessage : q_query_read_message q slots message) by assumption.
  unfold q_query_copy_frame; Intros.
  assert (Hfacts : q_query_acquire_facts critical sg invocation eid mask cpu_sr before entry_2 observed current_2) by tauto.
  assert (Hread : q_query_read_facts sg entry_2 eid current_2 q free slots grp rows) by tauto.
  pose proof Hread as [_ [_ [_ [_ [Hqvalid [_ [_ [_ [Hgrp Hrows]]]]]]]]].
  destruct Hlayout as [[Htypeaddr [Hptr Hcnt]] [[Hgroup Htable] Hqueues]].
  assert (Hqid : valid_queue_id sg q.(qID)) by exact (proj1 Hqvalid).
  sep_apply_l_atomic (proj2 (q_query_qcb_read_equiv sg q pq Hat (Hqueues q Hqid))).
  rewrite PreH1 in *; rewrite Hptr, Hgroup, Htable.
  sep_apply_l_atomic (q_query_read_merge sg entry_2 eid current_2 q free slots grp rows Hread).
  sep_apply_l_atomic (proj1 (q_query_output_array_equiv (&(pd # "os_q_data" ->ₛ "OSEventTbl")) rows)).
  assert (Hcritical : q_query_critical sg eid entry_2 (queue_query_snapshot entry_2.(TskState) current_2 q message) entry_2).
  { eapply q_query_read_facts_critical; eassumption. }
  Exists (queue_query_snapshot entry_2.(TskState) current_2 q message) entry_2 current_2.
  assert (HA : coq_prop (q_query_acquire_facts critical sg invocation eid mask cpu_sr before entry_2 observed current_2) --||-- TT).
  { split; [apply derivable1_truep_intros|apply derivable1s_coq_prop_r; exact Hfacts]. }
  assert (HC : coq_prop (q_query_critical sg eid entry_2 (queue_query_snapshot entry_2.(TskState) current_2 q message) entry_2) --||-- TT).
  { split; [apply derivable1_truep_intros|apply derivable1s_coq_prop_r; exact Hcritical]. }
  rewrite HA, HC.
  unfold q_query_output_fields_rep;
    cbn [queue_query_snapshot q_query_wait_group q_query_wait_rows q_query_message q_query_entries q_query_capacity];
    rewrite Hgrp, Hrows.
  rewrite !mutex_query_truep_sepcon_equiv.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.
