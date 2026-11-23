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
From Ucos2Verify.VC.code.core Require Import task_stat_stk_chk_goal.
From Ucos2Verify.VC.code.core Require Import task_stat_stk_chk_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.core.spec.task_stat_stk_chk_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OS_TaskStatStkChk_entail_wit_1 : OS_TaskStatStkChk_entail_wit_1.
Proof.
  unfold OS_TaskStatStkChk_entail_wit_1.
  left; intros.
  pose proof (task_stat_stk_chk_prefix_start critical sg invocation mask caller
    (&("stk_data")) before) as Hprefix.
  Exists before (@nil TaskStatStkChkObservation).
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_entail_wit_2 : OS_TaskStatStkChk_entail_wit_2.
Proof.
  unfold OS_TaskStatStkChk_entail_wit_2.
  left; intros.
  subst retval.
  Exists data_2 after_2.
  unfold task_stat_stk_chk_call_result.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_entail_wit_3_1 : OS_TaskStatStkChk_entail_wit_3_1.
Proof.
  unfold OS_TaskStatStkChk_entail_wit_3_1.
  left; intros.
  assert (Hprio : 0 <= prio < 64) by lia.
  pose proof (task_stat_stk_chk_prefix_append critical sg invocation mask caller
    (&("stk_data")) before prio current history err data after
    PreH20 PreH21 PreH22) as Hprefix.
  destruct (task_stat_stk_chk_result_has_data critical sg invocation mask current
    caller prio (&("stk_data")) err data after PreH14 Hprio PreH17 PreH21)
    as [value Hdata].
  subst data.
  cbn [task_stk_chk_output_post].
  Exists (List.app history (cons
    {| stat_stack_priority := prio; stat_stack_error := err;
       stat_stack_data := Some value; stat_stack_returned := after |} nil)).
  sep_apply (task_stat_stk_chk_output_forget (&("stk_data")) value).
  sep_apply (store_ptr_undef_store_ptr (&("ptcb"))
    (task_stk_chk_table_pointer sg after prio)).
  sep_apply (store_uchar_undef_store_uchar (&("err")) err).
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_entail_wit_3_2 : OS_TaskStatStkChk_entail_wit_3_2.
Proof.
  unfold OS_TaskStatStkChk_entail_wit_3_2.
  left; intros.
  assert (Hprio : 0 <= prio < 64) by lia.
  pose proof (task_stat_stk_chk_prefix_append critical sg invocation mask caller
    (&("stk_data")) before prio current history err data after
    PreH20 PreH21 PreH22) as Hprefix.
  destruct (task_stat_stk_chk_result_has_data critical sg invocation mask current
    caller prio (&("stk_data")) err data after PreH14 Hprio PreH17 PreH21)
    as [value Hdata].
  subst data.
  cbn [task_stk_chk_output_post].
  Exists (List.app history (cons
    {| stat_stack_priority := prio; stat_stack_error := err;
       stat_stack_data := Some value; stat_stack_returned := after |} nil)).
  sep_apply (task_stat_stk_chk_output_forget (&("stk_data")) value).
  sep_apply (store_ptr_undef_store_ptr (&("ptcb"))
    (task_stk_chk_table_pointer sg after prio)).
  sep_apply (store_uchar_undef_store_uchar (&("err")) err).
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_entail_wit_3_3 : OS_TaskStatStkChk_entail_wit_3_3.
Proof.
  unfold OS_TaskStatStkChk_entail_wit_3_3.
  left; intros.
  assert (Hprio : 0 <= prio < 64) by lia.
  pose proof (task_stat_stk_chk_prefix_append critical sg invocation mask caller
    (&("stk_data")) before prio current history err data after
    PreH19 PreH20 PreH21) as Hprefix.
  destruct (task_stat_stk_chk_result_has_data critical sg invocation mask current
    caller prio (&("stk_data")) err data after PreH13 Hprio PreH16 PreH20)
    as [value Hdata].
  subst data.
  cbn [task_stk_chk_output_post].
  Exists (List.app history (cons
    {| stat_stack_priority := prio; stat_stack_error := err;
       stat_stack_data := Some value; stat_stack_returned := after |} nil)).
  sep_apply (task_stat_stk_chk_output_forget (&("stk_data")) value).
  sep_apply (store_ptr_undef_store_ptr (&("ptcb"))
    (task_stk_chk_table_pointer sg after prio)).
  sep_apply (store_uchar_undef_store_uchar (&("err")) err).
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_entail_wit_3_4 : OS_TaskStatStkChk_entail_wit_3_4.
Proof.
  unfold OS_TaskStatStkChk_entail_wit_3_4.
  left; intros.
  assert (Hprio : 0 <= prio < 64) by lia.
  pose proof (task_stat_stk_chk_prefix_append critical sg invocation mask caller
    (&("stk_data")) before prio current history err data after
    PreH9 PreH10 PreH11) as Hprefix.
  destruct (task_stat_stk_chk_result_has_data critical sg invocation mask current
    caller prio (&("stk_data")) err data after PreH3 Hprio PreH6 PreH10)
    as [value Hdata].
  subst data.
  cbn [task_stk_chk_output_post].
  Exists (List.app history (cons
    {| stat_stack_priority := prio; stat_stack_error := err;
       stat_stack_data := Some value; stat_stack_returned := after |} nil)).
  sep_apply (task_stat_stk_chk_output_forget (&("stk_data")) value).
  sep_apply (store_uchar_undef_store_uchar (&("err")) err).
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_entail_wit_4 : OS_TaskStatStkChk_entail_wit_4.
Proof.
  unfold OS_TaskStatStkChk_entail_wit_4.
  left; intros.
  Exists after next_history.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_return_wit_1 : OS_TaskStatStkChk_return_wit_1.
Proof.
  unfold OS_TaskStatStkChk_return_wit_1.
  left; intros.
  assert (Hpriority : prio = 64) by lia.
  subst prio.
  assert (Hpost : task_stat_stk_chk_post critical sg invocation mask caller before current).
  { unfold task_stat_stk_chk_post.
    exists (&("stk_data")), history; split; assumption. }
  Exists current.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_which_implies_wit_1 : OS_TaskStatStkChk_which_implies_wit_1.
Proof.
  unfold OS_TaskStatStkChk_which_implies_wit_1; left.
  unfold task_stk_chk_output_undef.
  csimpl.
  entailer!; apply addr_of_LE_var_not_zero.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_which_implies_wit_2 : OS_TaskStatStkChk_which_implies_wit_2.
Proof.
  unfold OS_TaskStatStkChk_which_implies_wit_2; left.
  intros caller before mask invocation sg critical current history prio
    Hconfiguration Houtput Hlo Hhi Hprotocol Hprefix.
  pose proof (proj1 Hconfiguration) as Hcallee_configuration.
  pose proof (task_stat_stk_chk_protocol_call critical sg invocation mask caller
    before (&("stk_data")) prio current history Hprotocol Hprefix Houtput
    (conj Hlo Hhi)) as Hadmission.
  pose proof (task_stat_stk_chk_call_safe critical sg invocation current caller
    prio (&("stk_data"))) as Hsafe.
  unfold task_stk_chk_output_pre.
  rewrite (task_stat_stk_chk_no_argument_error sg prio (&("stk_data"))
    Hconfiguration (conj Hlo Hhi) Houtput).
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_which_implies_wit_3 : OS_TaskStatStkChk_which_implies_wit_3.
Proof.
  unfold OS_TaskStatStkChk_which_implies_wit_3; left.
  intros invocation sg critical after prio Hstate Haddresses Hlo Hhi.
  pose proof (task_stat_stk_chk_table_split critical sg invocation after prio
    Hstate (conj Hlo Hhi)) as Hsplit.
  pose proof (proj1 (proj2 Haddresses)) as Htable.
  rewrite Htable in Hsplit.
  sep_apply_l_atomic Hsplit.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_which_implies_wit_4 : OS_TaskStatStkChk_which_implies_wit_4.
Proof.
  unfold OS_TaskStatStkChk_which_implies_wit_4; left.
  intros invocation sg critical after prio ptcb Hstate Haddresses Hlo Hhi Hptcb.
  pose proof (task_stat_stk_chk_table_merge critical sg invocation after prio
    (conj Hlo Hhi)) as Hmerge.
  pose proof (proj1 (proj2 Haddresses)) as Htable.
  rewrite Htable in Hmerge.
  sep_apply_l_atomic Hmerge.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStatStkChk_which_implies_wit_5 : OS_TaskStatStkChk_which_implies_wit_5.
Proof.
  unfold OS_TaskStatStkChk_which_implies_wit_5; left.
  unfold task_stk_chk_output_undef.
  csimpl.
  entailer!.
Qed. 

