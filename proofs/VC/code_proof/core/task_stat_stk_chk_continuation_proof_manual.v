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
From Ucos2Verify.VC.code.core Require Import task_stat_stk_chk_continuation_goal.
From Ucos2Verify.VC.code.core Require Import task_stat_stk_chk_continuation_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.core.spec.task_stat_stk_chk_continuation_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OS_TaskStatStkChk_entail_wit_1 : OS_TaskStatStkChk_entail_wit_1.
Proof.
  unfold OS_TaskStatStkChk_entail_wit_1; left; intros.
  pose proof (task_stat_stk_chk_continuation_prefix_start environment critical saved_local
    sg mask caller_frame (&("stk_data")) original before) as Hprefix.
  Exists (@nil TaskStatStkChkContinuationObservation) original before.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_entail_wit_2 : OS_TaskStatStkChk_entail_wit_2.
Proof.
  unfold OS_TaskStatStkChk_entail_wit_2; left; intros.
  subst retval.
  unfold task_stk_chk_continuation_post.
  Intros returned_after data_after after_state.
  Exists data_after returned_after after_state.
  unfold task_stat_stk_chk_continuation_call_result.
  rewrite !time_dly_closed_inv_equiv.
  unfold UCOS2_inv.
  Intros; entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_entail_wit_3_1 : OS_TaskStatStkChk_entail_wit_3_1.
Proof.
  unfold OS_TaskStatStkChk_entail_wit_3_1; left; intros.
  assert (Hrange : 0 <= err < 256).
  { eapply task_stat_stk_chk_continuation_error_in_range; eassumption. }
  assert (Herr : err = 0).
  { rewrite unsigned_last_nbits_eq in PreH12 by (cbn; lia).
    exact PreH12. }
  assert (Htable : task_stat_stk_chk_continuation_table_result sg prio err after
    (Some (task_stk_chk_table_pointer sg after prio))).
  { unfold task_stat_stk_chk_continuation_table_result; rewrite Herr; reflexivity. }
  Exists (Some (task_stk_chk_table_pointer sg after prio)).
  sep_apply_l_atomic (store_ptr_undef_store_ptr (&("ptcb")) (task_stk_chk_table_pointer sg after prio)).
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_entail_wit_3_2 : OS_TaskStatStkChk_entail_wit_3_2.
Proof.
  unfold OS_TaskStatStkChk_entail_wit_3_2; left; intros.
  assert (Hrange : 0 <= err < 256).
  { eapply task_stat_stk_chk_continuation_error_in_range; eassumption. }
  assert (Herr : err = 0).
  { rewrite unsigned_last_nbits_eq in PreH12 by (cbn; lia).
    exact PreH12. }
  assert (Htable : task_stat_stk_chk_continuation_table_result sg prio err after
    (Some (task_stk_chk_table_pointer sg after prio))).
  { unfold task_stat_stk_chk_continuation_table_result; rewrite Herr; reflexivity. }
  Exists (Some (task_stk_chk_table_pointer sg after prio)).
  sep_apply_l_atomic (store_ptr_undef_store_ptr (&("ptcb")) (task_stk_chk_table_pointer sg after prio)).
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_entail_wit_3_3 : OS_TaskStatStkChk_entail_wit_3_3.
Proof.
  unfold OS_TaskStatStkChk_entail_wit_3_3; left; intros.
  assert (Hrange : 0 <= err < 256).
  { eapply task_stat_stk_chk_continuation_error_in_range; eassumption. }
  assert (Herr : err = 0).
  { rewrite unsigned_last_nbits_eq in PreH11 by (cbn; lia).
    exact PreH11. }
  assert (Htable : task_stat_stk_chk_continuation_table_result sg prio err after
    (Some (task_stk_chk_table_pointer sg after prio))).
  { unfold task_stat_stk_chk_continuation_table_result; rewrite Herr; reflexivity. }
  Exists (Some (task_stk_chk_table_pointer sg after prio)).
  sep_apply_l_atomic (store_ptr_undef_store_ptr (&("ptcb")) (task_stk_chk_table_pointer sg after prio)).
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_entail_wit_3_4 : OS_TaskStatStkChk_entail_wit_3_4.
Proof.
  unfold OS_TaskStatStkChk_entail_wit_3_4; left; intros.
  assert (Herr : err <> 0).
  { intros Hzero; subst err; cbn in PreH1; contradiction. }
  assert (Htable : task_stat_stk_chk_continuation_table_result sg prio err after None).
  { unfold task_stat_stk_chk_continuation_table_result.
    rewrite (proj2 (Z.eqb_neq err 0) Herr); reflexivity. }
  Exists (@None Z).
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_entail_wit_4 : OS_TaskStatStkChk_entail_wit_4.
Proof.
  unfold OS_TaskStatStkChk_entail_wit_4; left; intros.
  assert (Hprio : 0 <= prio < 64) by lia.
  pose proof (task_stat_stk_chk_continuation_prefix_append environment critical saved_local sg
    mask caller_frame (&("stk_data")) original before prio history current_caller current
    err data returned after observed PreH9 PreH10 PreH11) as Hprefix.
  Exists (List.app history (cons
    {| stack_observed_priority := prio; stack_observed_error := err;
       stack_observed_data := data; stack_observed_caller := returned;
       stack_observed_state := after; stack_observed_table := observed |} nil)).
  sep_apply_l_atomic (task_stat_stk_chk_continuation_output_forget environment critical saved_local sg
    current_caller mask caller_frame prio (&("stk_data")) current err data returned after
    PreH2 Hprio PreH6 PreH10).
  sep_apply_l_atomic (store_uchar_undef_store_uchar (&("err")) err).
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_entail_wit_5 : OS_TaskStatStkChk_entail_wit_5.
Proof.
  unfold OS_TaskStatStkChk_entail_wit_5; left; intros.
  Exists next_history returned after.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_return_wit_1 : OS_TaskStatStkChk_return_wit_1.
Proof.
  unfold OS_TaskStatStkChk_return_wit_1; left; intros.
  assert (Hpriority : prio = 64) by lia; subst prio.
  pose proof (task_stat_stk_chk_continuation_safe_result environment critical saved_local sg
    original mask caller_frame before (&("stk_data")) history current_caller current X
    PreH6 PreH7 PreH10) as Hresult.
  unfold task_stat_stk_chk_continuation_post.
  Exists (&("stk_data")) history current_caller current.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_which_implies_wit_1 : OS_TaskStatStkChk_which_implies_wit_1.
Proof.
  unfold OS_TaskStatStkChk_which_implies_wit_1; left.
  unfold task_stk_chk_output_undef; csimpl.
  entailer!; apply addr_of_LE_var_not_zero.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_which_implies_wit_2 : OS_TaskStatStkChk_which_implies_wit_2.
Proof.
  unfold OS_TaskStatStkChk_which_implies_wit_2; left; intros.
  pose proof (proj1 PreH1) as Hcallee_configuration.
  pose proof (task_stat_stk_chk_continuation_protocol_call environment critical saved_local sg
    mask caller_frame (&("stk_data")) original before prio history current_caller current
    PreH5 PreH6 PreH2 (conj PreH3 PreH4)) as Hadmission.
  pose proof (task_stat_stk_chk_continuation_call_safe environment critical saved_local sg
    current_caller mask caller_frame prio (&("stk_data")) current) as Hsafe.
  unfold task_stk_chk_output_pre.
  rewrite (task_stat_stk_chk_no_argument_error sg prio (&("stk_data"))
    PreH1 (conj PreH3 PreH4) PreH2).
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_which_implies_wit_3 : OS_TaskStatStkChk_which_implies_wit_3.
Proof.
  unfold OS_TaskStatStkChk_which_implies_wit_3; left; intros.
  pose proof (task_stat_stk_chk_continuation_table_split environment critical saved_local sg
    returned mask after prio (conj PreH3 PreH4)) as Hsplit.
  pose proof (proj1 (proj2 PreH2)) as Htable.
  rewrite Htable in Hsplit.
  sep_apply_l_atomic Hsplit.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_which_implies_wit_4 : OS_TaskStatStkChk_which_implies_wit_4.
Proof.
  unfold OS_TaskStatStkChk_which_implies_wit_4; left; intros.
  pose proof (task_stat_stk_chk_continuation_table_merge environment critical saved_local sg
    returned mask after prio (conj PreH3 PreH4)) as Hmerge.
  pose proof (proj1 (proj2 PreH2)) as Htable.
  rewrite Htable in Hmerge.
  assert (Hspatial :
    ((&("OSTCBPrioTbl")) + prio * sizeof(PTR)) # Ptr |->
      task_stk_chk_table_pointer sg after prio **
      task_stat_stk_chk_continuation_table_frame environment saved_local sg returned mask after prio
    |-- task_suspend_closed environment critical saved_local sg returned mask after).
  { intros heap Hresources.
    apply (Hmerge heap).
    split; assumption. }
  sep_apply_l_atomic Hspatial.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_which_implies_wit_5 : OS_TaskStatStkChk_which_implies_wit_5.
Proof.
  unfold OS_TaskStatStkChk_which_implies_wit_5; left.
  unfold task_stk_chk_output_undef; csimpl; entailer!.
Qed. 

