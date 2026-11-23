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
From Ucos2Verify.VC.code.sem Require Import set_goal.
From Ucos2Verify.VC.code.sem Require Import set_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.sem.spec.sem_set_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_set_source_api_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSSemSet_entail_wit_1_1 : OSSemSet_entail_wit_1_1.
Proof.
  pre_process.
  prop_apply_p (store_uchar_range (&(pe # "os_event" ->ₛ "OSEventType"))
    (event_slot_type_value before.(EventState) eid)).
  entailer!.
Qed. 

Lemma proof_of_OSSemSet_return_wit_1 : OSSemSet_return_wit_1.
Proof.
  pre_process.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  assert (Hid : valid_event_id sg eid) by assumption.
  assert (Hslot : sem_query_public_slot before eid observed) by assumption.
  assert (Hprogram : sem_set_source_api_program critical sg invocation pe requested before 1 before).
  { eapply sem_set_source_api_wrong_type_return; try eassumption; try lia; congruence. }
  assert (Hexec : sem_set_source_api_safe critical sg invocation pe requested before X) by assumption.
  pose proof (sem_set_source_api_safe_return _ _ _ _ _ _ _ _ _ Hprogram Hexec) as Hsafe.
  unfold sem_set_source_api_post; Exists 1 before.
  rewrite PreH7.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid Hvalid).
  rewrite mutex_query_closed_equiv.

  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed. 

Lemma proof_of_OSSemSet_return_wit_2 : OSSemSet_return_wit_2.
Proof.
  pre_process.
  assert (Hzero : pe = 0) by congruence.
  assert (Hprogram : sem_set_source_api_program critical sg invocation pe requested before 4 before).
  { rewrite Hzero; apply sem_set_source_api_null_return. }
  assert (Hexec : sem_set_source_api_safe critical sg invocation pe requested before X) by assumption.
  pose proof (sem_set_source_api_safe_return _ _ _ _ _ _ _ _ _ Hprogram Hexec) as Hsafe.
  unfold sem_set_source_api_post; Exists 4 before.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.

  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed. 

Lemma proof_of_OSSemSet_return_wit_3 : OSSemSet_return_wit_3.
Proof.
  pre_process.
  assert (Hid : valid_event_id sg eid) by assumption.
  assert (Haddr : pe = event_addr sg eid) by assumption.
  assert (Hnonnull : pe <> 0) by congruence.
  assert (Hexec : sem_set_source_api_safe critical sg invocation pe requested before X) by assumption.
  match goal with
  | Hfacts : sem_query_acquire_facts critical sg invocation eid mask ?saved before ?acquired observed ?node |- _ =>
    pose proof (sem_set_source_api_restored_return critical sg invocation pe requested before eid observed
      mask saved acquired node after Hnonnull Haddr Hid Hfacts PreH1) as Hprogram;
    pose proof (sem_set_source_api_safe_return _ _ _ _ _ _ _ _ _ Hprogram Hexec) as Hsafe;
    unfold sem_set_source_api_post; Exists (sem_set_error acquired node) after
  end.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.

  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed. 

Lemma proof_of_OSSemSet_return_wit_4 : OSSemSet_return_wit_4.
Proof.
  pre_process.
  assert (Hid : valid_event_id sg eid) by assumption.
  assert (Haddr : pe = event_addr sg eid) by assumption.
  assert (Hnonnull : pe <> 0) by congruence.
  assert (Hexec : sem_set_source_api_safe critical sg invocation pe requested before X) by assumption.
  match goal with
  | Hfacts : sem_query_acquire_facts critical sg invocation eid mask ?saved before ?acquired observed ?node |- _ =>
    pose proof (sem_set_source_api_restored_return critical sg invocation pe requested before eid observed
      mask saved acquired node after Hnonnull Haddr Hid Hfacts PreH1) as Hprogram;
    pose proof (sem_set_source_api_safe_return _ _ _ _ _ _ _ _ _ Hprogram Hexec) as Hsafe;
    unfold sem_set_source_api_post; Exists (sem_set_error acquired node) after
  end.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.

  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed. 

Lemma proof_of_OSSemSet_return_wit_5 : OSSemSet_return_wit_5.
Proof.
  pre_process.
  assert (Hid : valid_event_id sg eid) by assumption.
  assert (Haddr : pe = event_addr sg eid) by assumption.
  assert (Hnonnull : pe <> 0) by congruence.
  assert (Hexec : sem_set_source_api_safe critical sg invocation pe requested before X) by assumption.
  match goal with
  | Hfacts : sem_query_acquire_facts critical sg invocation eid mask ?saved before ?acquired observed ?node |- _ =>
    pose proof (sem_set_source_api_restored_return critical sg invocation pe requested before eid observed
      mask saved acquired node after Hnonnull Haddr Hid Hfacts PreH1) as Hprogram;
    pose proof (sem_set_source_api_safe_return _ _ _ _ _ _ _ _ _ Hprogram Hexec) as Hsafe;
    unfold sem_set_source_api_post; Exists (sem_set_error acquired node) after
  end.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.

  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed. 

Lemma proof_of_OSSemSet_partial_solve_wit_11_pure : OSSemSet_partial_solve_wit_11_pure.
Proof.
  pre_process.
  prop_apply_p (store_uchar_range (&(pe # "os_event" ->ₛ "OSEventGrp"))
    (encode_event_wait_grp current.(waitList) entry.(TskState))).
  Intros.
  match goal with H : 0 <= encode_event_wait_grp current.(waitList) entry.(TskState) <= Byte.max_unsigned |- _ =>
    change (0 <= encode_event_wait_grp current.(waitList) entry.(TskState) <= 255) in H end.
  rewrite unsigned_last_nbits_eq in PreH1 by (change (0 <= encode_event_wait_grp current.(waitList) entry.(TskState) < 4294967296); lia).
  entailer!.
Qed. 

Lemma proof_of_OSSemSet_partial_solve_wit_12_pure : OSSemSet_partial_solve_wit_12_pure.
Proof.
  pre_process.
  prop_apply_p (store_uchar_range (&(pe # "os_event" ->ₛ "OSEventGrp"))
    (encode_event_wait_grp current.(waitList) entry.(TskState))).
  Intros.
  match goal with H : 0 <= encode_event_wait_grp current.(waitList) entry.(TskState) <= Byte.max_unsigned |- _ =>
    change (0 <= encode_event_wait_grp current.(waitList) entry.(TskState) <= 255) in H end.
  rewrite unsigned_last_nbits_eq in PreH1 by (change (0 <= encode_event_wait_grp current.(waitList) entry.(TskState) < 4294967296); lia).
  entailer!.
Qed. 

Lemma proof_of_OSSemSet_which_implies_wit_1 : OSSemSet_which_implies_wit_1.
Proof.
  unfold OSSemSet_which_implies_wit_1; left; intros.
  unfold sem_set_error_cell; reflexivity.
Qed. 

Lemma proof_of_OSSemSet_which_implies_wit_2 : OSSemSet_which_implies_wit_2.
Proof.
  pre_process.
  assert (Hinput : sem_set_call_input critical sg invocation pe before eid observed) by assumption.
  destruct (sem_set_call_input_nonnull critical sg invocation pe before eid observed Hinput PreH1)
    as [Haddr [Hid [Hslot Hprotocol]]].
  rewrite mutex_query_closed_equiv.
  sep_apply_l_atomic (sem_query_type_split_full sg before eid observed Hslot).
  rewrite PreH2.

  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed. 

Lemma proof_of_OSSemSet_which_implies_wit_3 : OSSemSet_which_implies_wit_3.
Proof.
  pre_process.
  assert (Hinput : sem_set_call_input critical sg invocation pe before eid observed) by assumption.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  destruct (sem_set_call_input_nonnull critical sg invocation pe before eid observed Hinput PreH1)
    as [Haddr [Hid [Hslot Hprotocol]]].
  specialize (Hprotocol PreH2).
  destruct (sem_query_public_slot_is_sem before eid observed Hslot PreH2) as [Hlookup Htype].
  assert (Hencoded : encode_event_type observed.(eventType) = 3) by (rewrite Htype; reflexivity).
  rewrite PreH3.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid Hvalid).

  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed. 

Lemma proof_of_OSSemSet_which_implies_wit_4 : OSSemSet_which_implies_wit_4.
Proof.
  pre_process.
  assert (Hfacts : sem_query_acquire_facts critical sg invocation eid mask cpu_sr
    before entry_2 observed current_2) by assumption.
  pose proof Hfacts as [_ [Hvalid [_ [_ [Hlookup [_ [Htype _]]]]]]].
  sep_apply_l_atomic (sem_set_count_split_full sg entry_2 eid current_2 Hlookup Htype).
  Intros; Exists entry_2 current_2.
  rewrite PreH4.

  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed. 

Lemma proof_of_OSSemSet_which_implies_wit_5 : OSSemSet_which_implies_wit_5.
Proof.
  pre_process.
  assert (Hfacts : sem_query_acquire_facts critical sg invocation eid mask cpu_sr
    before entry_2 observed current_2) by assumption.
  pose proof Hfacts as [_ [Hvalid [_ [_ [Hlookup [_ [Htype _]]]]]]].
  assert (Hrequested : 0 <= requested <= 65535) by lia.
  assert (Hwrite : sem_set_can_write entry_2 current_2 = true).
  { unfold sem_set_can_write; apply Bool.orb_true_iff; left; apply Z.ltb_lt; lia. }
  rewrite PreH4.
  pose proof (sem_set_count_merge_checkpoint sg entry_2 eid current_2 requested
    Hvalid Hlookup Htype Hrequested) as Hmerge.
  unfold sem_set_stored_count in Hmerge; rewrite Hwrite in Hmerge.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  sep_apply_l_atomic Hmerge.
  Exists entry_2 current_2; unfold sem_set_error; rewrite Hwrite.
  unfold sem_set_source_api_restore_pre.
  pose proof Hfacts as [_ [_ [Hsaved _]]].
  pose proof (sem_set_checkpoint_preserves_validity sg entry_2 eid current_2 requested
    Hvalid Hlookup Htype Hrequested) as Hcheckpoint.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed. 

Lemma proof_of_OSSemSet_which_implies_wit_6 : OSSemSet_which_implies_wit_6.
Proof.
  pre_process.
  assert (Hfacts : sem_query_acquire_facts critical sg invocation eid mask cpu_sr
    before entry_2 observed current_2) by assumption.
  pose proof Hfacts as [Hinterval [Hvalid [_ [_ [Hlookup [_ [Htype _]]]]]]].
  assert (Hlayout : sem_set_group_read_layout critical sg invocation before eid
    (&(pe # "os_event" ->ₛ "OSEventGrp"))) by assumption.
  specialize (Hlayout entry_2 current_2 Hinterval Hlookup PreH5).
  sep_apply_l_atomic (sem_set_group_split sg entry_2 eid current_2).
  Exists entry_2 current_2; rewrite Hlayout.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.

  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed. 

Lemma proof_of_OSSemSet_which_implies_wit_7 : OSSemSet_which_implies_wit_7.
Proof.
  pre_process.
  assert (Hfacts : sem_query_acquire_facts critical sg invocation eid mask cpu_sr
    before entry_2 observed current_2) by assumption.
  pose proof Hfacts as [_ [Hvalid [_ [_ [Hlookup [_ [Htype _]]]]]]].
  assert (Hrequested : 0 <= requested <= 65535) by lia.
  assert (Hwrite : sem_set_can_write entry_2 current_2 = true).
  { unfold sem_set_can_write; apply Bool.orb_true_iff; right; apply Z.eqb_eq; exact PreH6. }
  rewrite PreH4, PreH7.
  sep_apply_l_atomic (sem_set_group_merge sg entry_2 eid current_2).
  pose proof (sem_set_count_merge_checkpoint sg entry_2 eid current_2 requested
    Hvalid Hlookup Htype Hrequested) as Hmerge.
  unfold sem_set_stored_count in Hmerge; rewrite Hwrite in Hmerge.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  sep_apply_l_atomic Hmerge.
  Exists entry_2 current_2; unfold sem_set_error; rewrite Hwrite.
  unfold sem_set_source_api_restore_pre.
  pose proof Hfacts as [_ [_ [Hsaved _]]].
  pose proof (sem_set_checkpoint_preserves_validity sg entry_2 eid current_2 requested
    Hvalid Hlookup Htype Hrequested) as Hcheckpoint.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed. 

Lemma proof_of_OSSemSet_which_implies_wit_8 : OSSemSet_which_implies_wit_8.
Proof.
  pre_process.
  assert (Hfacts : sem_query_acquire_facts critical sg invocation eid mask cpu_sr
    before entry_2 observed current_2) by assumption.
  pose proof Hfacts as [_ [Hvalid [_ [_ [Hlookup [_ [Htype _]]]]]]].
  assert (Hrequested : 0 <= requested <= 65535) by lia.
  assert (Hwrite : sem_set_can_write entry_2 current_2 = false).
  { unfold sem_set_can_write; apply Bool.orb_false_iff; split;
      [apply Z.ltb_ge; lia|apply Z.eqb_neq; exact PreH6]. }
  rewrite PreH4, PreH7.
  sep_apply_l_atomic (sem_set_group_merge sg entry_2 eid current_2).
  pose proof (sem_set_count_merge_checkpoint sg entry_2 eid current_2 requested
    Hvalid Hlookup Htype Hrequested) as Hmerge.
  unfold sem_set_stored_count in Hmerge; rewrite Hwrite in Hmerge.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  sep_apply_l_atomic Hmerge.
  Exists entry_2 current_2; unfold sem_set_error; rewrite Hwrite.
  unfold sem_set_source_api_restore_pre.
  pose proof Hfacts as [_ [_ [Hsaved _]]].
  pose proof (sem_set_checkpoint_preserves_validity sg entry_2 eid current_2 requested
    Hvalid Hlookup Htype Hrequested) as Hcheckpoint.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed. 

