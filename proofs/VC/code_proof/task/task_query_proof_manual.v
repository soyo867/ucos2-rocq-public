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
From Ucos2Verify.VC.code.task Require Import task_query_goal.
From Ucos2Verify.VC.code.task Require Import task_query_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.task.spec.task_query_spec.
Import UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OSTaskQuery_entail_wit_1 : OSTaskQuery_entail_wit_1.
Proof.
  unfold OSTaskQuery_entail_wit_1; left; intros.
  subst prio_pre.
  prop_apply_p (store_uchar_range (&( "prio" )) request).
  change Byte.max_unsigned with 255; entailer!.
Qed.

Lemma proof_of_OSTaskQuery_entail_wit_3_1 : OSTaskQuery_entail_wit_3_1.
Proof.
  unfold OSTaskQuery_entail_wit_3_1; left; intros.
  prop_apply_p (task_query_restore_pre_state_inv platform critical sg invocation
    origin retval acquired).
  entailer!.
Qed.

Lemma proof_of_OSTaskQuery_entail_wit_3_2 : OSTaskQuery_entail_wit_3_2.
Proof.
  unfold OSTaskQuery_entail_wit_3_2; left; intros.
  prop_apply_p (task_query_restore_pre_state_inv platform critical sg invocation
    origin retval_2 acquired).
  prop_apply_p (store_uint_range (&( "cpu_sr" )) retval_2).
  entailer!.
Qed.

Lemma proof_of_OSTaskQuery_entail_wit_4_1 : OSTaskQuery_entail_wit_4_1.
Proof.
  unfold OSTaskQuery_entail_wit_4_1; left; intros.
  prop_apply_p (task_query_restore_pre_state_inv platform critical sg invocation
    origin retval acquired).
  entailer!.
Qed.

Lemma proof_of_OSTaskQuery_entail_wit_4_2 : OSTaskQuery_entail_wit_4_2.
Proof.
  unfold OSTaskQuery_entail_wit_4_2; left; intros.
  prop_apply_p (task_query_restore_pre_state_inv platform critical sg invocation
    origin retval_2 acquired).
  prop_apply_p (store_uint_range (&( "cpu_sr" )) retval_2).
  entailer!.
Qed.

Lemma proof_of_OSTaskQuery_entail_wit_5_1 : OSTaskQuery_entail_wit_5_1.
Proof.
  unfold OSTaskQuery_entail_wit_5_1; left; intros.
  unfold task_query_entry_frame; Intros.
  unfold task_query_restore_pre.
  assert (Hreserved : UCOS2_inv sg acquired |--
    coq_prop (task_query_reserved_entry acquired key)).
  { sep_apply_r_atomic (derivable1_andp_elim1
      (coq_prop (task_query_reserved_entry acquired key)) (UCOS2_inv sg acquired)).
    apply task_query_reserved_table_entry; [tauto | lia | assumption]. }
  prop_apply_p Hreserved; entailer!.
Qed.

Lemma proof_of_OSTaskQuery_entail_wit_5_2 : OSTaskQuery_entail_wit_5_2.
Proof.
  unfold OSTaskQuery_entail_wit_5_2; left; intros.
  unfold task_query_entry_frame; Intros.
  unfold task_query_restore_pre.
  assert (Hreserved : UCOS2_inv sg acquired |--
    coq_prop (task_query_reserved_entry acquired key)).
  { sep_apply_r_atomic (derivable1_andp_elim1
      (coq_prop (task_query_reserved_entry acquired key)) (UCOS2_inv sg acquired)).
    apply task_query_reserved_table_entry; [tauto | lia | assumption]. }
  prop_apply_p Hreserved; entailer!.
Qed.

Lemma proof_of_OSTaskQuery_entail_wit_6_1 : OSTaskQuery_entail_wit_6_1.
Proof.
  unfold OSTaskQuery_entail_wit_6_1; left; intros.
  prop_apply_p (task_query_restore_pre_state_inv platform critical sg invocation
    origin retval acquired).
  entailer!.
Qed.

Lemma proof_of_OSTaskQuery_entail_wit_6_2 : OSTaskQuery_entail_wit_6_2.
Proof.
  unfold OSTaskQuery_entail_wit_6_2; left; intros.
  prop_apply_p (task_query_restore_pre_state_inv platform critical sg invocation
    origin retval_2 acquired).
  prop_apply_p (store_uint_range (&( "cpu_sr" )) retval_2).
  entailer!.
Qed.

Lemma proof_of_OSTaskQuery_return_wit_1 : OSTaskQuery_return_wit_1.
Proof.
  unfold OSTaskQuery_return_wit_1; left; intros.
  assert (Hprefix : task_query_prefix_error request output = None).
  { apply task_query_prefix_valid_output; [right; assumption|lia]. }
  pose proof (proj2 PreH29) as Hmask.
  unfold task_query_restore_post, task_query_success_frame.
  Intros after.
  rewrite Hmask.
  assert (Hcall : task_query_call_result critical sg invocation mask request
    output 0 caller before after old_output (map (@Some Z) bytes)).
  { unfold task_query_call_result; rewrite Hprefix.
    exists acquired, retval, (Some bytes).
    repeat first [assumption | split | reflexivity]. }
  pose proof (task_query_safe_return critical sg invocation mask request output 0 caller
    before after old_output (map (@Some Z) bytes) X Hcall ltac:(assumption)) as Hsafe.
  unfold task_query_post; rewrite Hprefix.
  Exists after (map (@Some Z) bytes); entailer!.
Qed.

Lemma proof_of_OSTaskQuery_return_wit_2 : OSTaskQuery_return_wit_2.
Proof.
  unfold OSTaskQuery_return_wit_2; left; intros.
  assert (Hprefix : task_query_prefix_error request output = None).
  { apply task_query_prefix_valid_output; [left; lia|lia]. }
  pose proof (proj2 PreH24) as Hmask.
  unfold task_query_restore_post, task_query_success_frame.
  Intros after.
  rewrite Hmask.
  assert (Hcall : task_query_call_result critical sg invocation mask request
    output 0 caller before after old_output (map (@Some Z) bytes)).
  { unfold task_query_call_result; rewrite Hprefix.
    exists acquired, retval, (Some bytes).
    repeat first [assumption | split | reflexivity]. }
  pose proof (task_query_safe_return critical sg invocation mask request output 0 caller
    before after old_output (map (@Some Z) bytes) X Hcall ltac:(assumption)) as Hsafe.
  unfold task_query_post; rewrite Hprefix.
  Exists after (map (@Some Z) bytes); entailer!.
Qed.

Lemma proof_of_OSTaskQuery_return_wit_3 : OSTaskQuery_return_wit_3.
Proof.
  unfold OSTaskQuery_return_wit_3; left; intros.
  assert (Hprefix : task_query_prefix_error request output = None).
  { apply task_query_prefix_valid_output; [right; assumption|lia]. }
  assert (Hprotected : task_query_protected_result sg acquired caller request 67 None).
  { apply (task_query_protected_reserved_result sg acquired caller request key);
      [exact PreH7|exact PreH1]. }
  pose proof (proj2 PreH17) as Hmask.
  unfold task_query_restore_post, task_query_entry_frame.
  Intros after.
  rewrite Hmask.
  assert (Hcall : task_query_call_result critical sg invocation mask request
    output 67 caller before after old_output old_output).
  { unfold task_query_call_result; rewrite Hprefix.
    exists acquired, retval, (None : option (list Z)).
    repeat first [assumption | split | reflexivity]. }
  pose proof (task_query_safe_return critical sg invocation mask request output 67 caller
    before after old_output old_output X Hcall ltac:(assumption)) as Hsafe.
  unfold task_query_post; rewrite Hprefix.
  Exists after old_output; entailer!.
Qed.

Lemma proof_of_OSTaskQuery_return_wit_4 : OSTaskQuery_return_wit_4.
Proof.
  unfold OSTaskQuery_return_wit_4; left; intros.
  assert (Hprefix : task_query_prefix_error request output = None).
  { apply task_query_prefix_valid_output; [left; lia|lia]. }
  assert (Hprotected : task_query_protected_result sg acquired caller request 67 None).
  { apply (task_query_protected_reserved_result sg acquired caller request key);
      [exact PreH9|exact PreH1]. }
  pose proof (proj2 PreH12) as Hmask.
  unfold task_query_restore_post, task_query_entry_frame.
  Intros after.
  rewrite Hmask.
  assert (Hcall : task_query_call_result critical sg invocation mask request
    output 67 caller before after old_output old_output).
  { unfold task_query_call_result; rewrite Hprefix.
    exists acquired, retval, (None : option (list Z)).
    repeat first [assumption | split | reflexivity]. }
  pose proof (task_query_safe_return critical sg invocation mask request output 67 caller
    before after old_output old_output X Hcall ltac:(assumption)) as Hsafe.
  unfold task_query_post; rewrite Hprefix.
  Exists after old_output; entailer!.
Qed.

Lemma proof_of_OSTaskQuery_return_wit_5 : OSTaskQuery_return_wit_5.
Proof.
  unfold OSTaskQuery_return_wit_5; left; intros.
  assert (Hprefix : task_query_prefix_error request output = None).
  { apply task_query_prefix_valid_output; [right; assumption|lia]. }
  assert (Hfree : acquired.(TskState).(prioTbl) key = PTFree).
  { eapply task_query_table_zero_is_free__exact_return_observations;
      [eassumption|lia|eassumption]. }
  assert (Hprotected : task_query_protected_result sg acquired caller request 41 None).
  { apply (task_query_protected_free_result sg acquired caller request key);
      [exact PreH5|exact Hfree]. }
  pose proof (proj2 PreH15) as Hmask.
  unfold task_query_restore_post, task_query_entry_frame.
  Intros after.
  rewrite Hmask.
  assert (Hcall : task_query_call_result critical sg invocation mask request
    output 41 caller before after old_output old_output).
  { unfold task_query_call_result; rewrite Hprefix.
    exists acquired, retval, (None : option (list Z)).
    repeat first [assumption | split | reflexivity]. }
  pose proof (task_query_safe_return critical sg invocation mask request output 41 caller
    before after old_output old_output X Hcall ltac:(assumption)) as Hsafe.
  unfold task_query_post; rewrite Hprefix.
  Exists after old_output; entailer!.
Qed.

Lemma proof_of_OSTaskQuery_return_wit_6 : OSTaskQuery_return_wit_6.
Proof.
  unfold OSTaskQuery_return_wit_6; left; intros.
  assert (Hprefix : task_query_prefix_error request output = None).
  { apply task_query_prefix_valid_output; [left; lia|lia]. }
  assert (Hfree : acquired.(TskState).(prioTbl) key = PTFree).
  { eapply task_query_table_zero_is_free__exact_return_observations;
      [eassumption|lia|eassumption]. }
  assert (Hprotected : task_query_protected_result sg acquired caller request 41 None).
  { apply (task_query_protected_free_result sg acquired caller request key);
      [exact PreH7|exact Hfree]. }
  pose proof (proj2 PreH10) as Hmask.
  unfold task_query_restore_post, task_query_entry_frame.
  Intros after.
  rewrite Hmask.
  assert (Hcall : task_query_call_result critical sg invocation mask request
    output 41 caller before after old_output old_output).
  { unfold task_query_call_result; rewrite Hprefix.
    exists acquired, retval, (None : option (list Z)).
    repeat first [assumption | split | reflexivity]. }
  pose proof (task_query_safe_return critical sg invocation mask request output 41 caller
    before after old_output old_output X Hcall ltac:(assumption)) as Hsafe.
  unfold task_query_post; rewrite Hprefix.
  Exists after old_output; entailer!.
Qed.

Lemma proof_of_OSTaskQuery_return_wit_7 : OSTaskQuery_return_wit_7.
Proof.
  unfold OSTaskQuery_return_wit_7; left; intros.
  assert (Hprefix : task_query_prefix_error request output = Some 9).
  { replace output with 0 by lia; apply task_query_prefix_null_output;
      right; lia. }
  pose proof (task_query_call_result_early_error critical sg invocation mask request output
    9 caller before old_output Hprefix) as Hcall.
  pose proof (task_query_safe_return critical sg invocation mask request output 9 caller
    before before old_output old_output X Hcall ltac:(assumption)) as Hsafe.
  unfold task_query_pre, task_query_post; rewrite Hprefix; entailer!.
Qed.

Lemma proof_of_OSTaskQuery_return_wit_8 : OSTaskQuery_return_wit_8.
Proof.
  unfold OSTaskQuery_return_wit_8; left; intros.
  assert (Hprefix : task_query_prefix_error request output = Some 9).
  { replace output with 0 by lia; apply task_query_prefix_null_output;
      left; lia. }
  pose proof (task_query_call_result_early_error critical sg invocation mask request output
    9 caller before old_output Hprefix) as Hcall.
  pose proof (task_query_safe_return critical sg invocation mask request output 9 caller
    before before old_output old_output X Hcall ltac:(assumption)) as Hsafe.
  unfold task_query_pre, task_query_post; rewrite Hprefix; entailer!.
Qed.

Lemma proof_of_OSTaskQuery_return_wit_9 : OSTaskQuery_return_wit_9.
Proof.
  unfold OSTaskQuery_return_wit_9; left; intros.
  assert (Hprefix : task_query_prefix_error request output = Some 42).
  { apply task_query_prefix_invalid_priority; lia. }
  pose proof (task_query_call_result_early_error critical sg invocation mask request output
    42 caller before old_output Hprefix) as Hcall.
  pose proof (task_query_safe_return critical sg invocation mask request output 42 caller
    before before old_output old_output X Hcall ltac:(assumption)) as Hsafe.
  unfold task_query_pre, task_query_post; rewrite Hprefix; entailer!.
Qed.

Lemma proof_of_OSTaskQuery_partial_solve_wit_1_pure : OSTaskQuery_partial_solve_wit_1_pure.
Proof.
  left; intros; unfold task_query_valid_arguments; entailer!; intuition lia.
Qed.

Lemma proof_of_OSTaskQuery_partial_solve_wit_2_pure : OSTaskQuery_partial_solve_wit_2_pure.
Proof.
  left; intros; unfold task_query_valid_arguments; entailer!; intuition lia.
Qed.

Lemma proof_of_OSTaskQuery_partial_solve_wit_11_pure : OSTaskQuery_partial_solve_wit_11_pure.
Proof.
  left; intros; subst key request output.
  unfold task_query_priority_resolution; entailer!; auto.
Qed.

Lemma proof_of_OSTaskQuery_partial_solve_wit_12_pure : OSTaskQuery_partial_solve_wit_12_pure.
Proof.
  left; intros; subst key.
  destruct PreH5 as [Hrange Hcut]; entailer!.
Qed.

Lemma proof_of_OSTaskQuery_which_implies_wit_1 : OSTaskQuery_which_implies_wit_1.
Proof.
  left; intros; destruct PreH1 as [Hpriority Houtput].
  unfold task_query_pre, task_query_entry_frame.
  rewrite (task_query_prefix_valid_output request output Hpriority Houtput).
  entailer!.
Qed.

Lemma proof_of_OSTaskQuery_which_implies_wit_2 : OSTaskQuery_which_implies_wit_2.
Proof.
  left; intros; unfold task_query_save_post, task_query_restore_pre.
  Intros acquired; Exists acquired; entailer!.
Qed.

Lemma proof_of_OSTaskQuery_which_implies_wit_3 : OSTaskQuery_which_implies_wit_3.
Proof.
  left; intros.
  unfold task_query_restore_pre, task_query_entry_frame, UCOS2_inv; Intros.
  match goal with H : UCOS2_state_inv sg acquired |- _ => rename H into Hvalid end.
  match goal with H : task_query_layout sg /\ _ |- _ =>
    destruct H as [Hlayout [Hself Hbounds]] end.
  destruct (Hself PreH1 acquired PreH2 Hvalid)
    as [resolved [Hrange [residual [Hopen Hclose]]]].
  assert (Hcut : task_query_current_cut sg acquired caller
    (encode_task_link sg acquired.(SchedState).(SchedStateDef.curTaskID)) resolved residual).
  { unfold task_query_current_cut; auto. }
  destruct PreH3 as [Hcurrent Htable].
  rewrite Hcurrent; cbn [tcb_field_address] in Hopen.
  sep_apply Hopen.
  Exists (encode_task_link sg acquired.(SchedState).(SchedStateDef.curTaskID)) resolved residual.
  unfold task_query_current_tail; entailer!.
Qed.

Lemma proof_of_OSTaskQuery_which_implies_wit_4 : OSTaskQuery_which_implies_wit_4.
Proof.
  left; intros.
  destruct PreH2 as [Hrange [Hpointer [Hopen Hclose]]].
  assert (Hresolution : task_query_priority_resolution sg acquired caller request resolved).
  { right; split; [assumption|].
    split; [exact Hrange|]; exists residual; subst current; auto. }
  unfold task_query_current_tail; Intros.
  destruct PreH3 as [Hcurrent Htable].
  rewrite Hcurrent; cbn [tcb_field_address] in Hclose.
  sep_apply Hclose.
  unfold task_query_restore_pre, task_query_entry_frame, UCOS2_inv; entailer!.
Qed.

Lemma proof_of_OSTaskQuery_which_implies_wit_6 : OSTaskQuery_which_implies_wit_6.
Proof.
  left; intros; unfold task_query_restore_pre.
  sep_apply_l_atomic (UCOS2_inv_split_priority_cell sg acquired key ltac:(lia)).
  destruct PreH4 as [Hcurrent Htable]; rewrite Htable.
  unfold task_query_table_tail, task_query_table_value; entailer!.
Qed.

Lemma proof_of_OSTaskQuery_which_implies_wit_7 : OSTaskQuery_which_implies_wit_7.
Proof.
  left; intros; unfold task_query_table_tail; Intros.
  prop_apply (store_prio_tbl_missing_i_index_in_range__resource_views_and_call_preconditions
    sg acquired.(TskState).(TaskStateDef.prioTbl) key).
  Intros.
  destruct PreH1 as [Hcurrent Htable]; rewrite Htable.
  unfold task_query_table_value.
  sep_apply (Ucos2Verify.lib.array_abstraction.store_prio_tbl_merge_cell
    sg acquired.(TskState).(TaskStateDef.prioTbl) key ltac:(lia)).
  unfold task_query_restore_pre, UCOS2_inv.
  rewrite UCOS2_raw_rep_priority_table_equiv; entailer!.
Qed.

Lemma proof_of_OSTaskQuery_which_implies_wit_8 : OSTaskQuery_which_implies_wit_8.
Proof.
  left; intros.
  unfold task_query_restore_pre, task_query_entry_frame, UCOS2_inv; Intros.
  match goal with H : UCOS2_state_inv sg acquired |- _ => rename H into Hvalid end.
  match goal with H : task_query_layout sg /\ _ |- _ =>
    destruct H as [Hlayout [Hself Hbounds]] end.
  destruct (acquired.(TskState).(TaskStateDef.prioTbl) key) as [| |tid] eqn:Hentry.
  - unfold task_query_table_value in PreH4; rewrite Hentry in PreH4; contradiction.
  - unfold task_query_table_value in PreH5; rewrite Hentry in PreH5; contradiction.
  - assert (Hpriority : task_priority_in_range sg key).
    { pose proof (proj1 Hvalid) as Hprofile.
      unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile.
      unfold task_priority_in_range; intuition lia. }
    assert (Htask : task_query_task_entry acquired key tid) by exact Hentry.
    destruct (task_query_acquired_task_slot_bounds sg acquired key tid Hvalid Hpriority Htask)
      as [Hslot [Hsource_lower Hsource_upper]].
    pose proof Hvalid as Hparts.
    destruct Hparts as [_ [_ [_ [_ [Hcross _]]]]].
    destruct Hcross as [[_ [Htable _]] _].
    specialize (Htable key Hpriority); rewrite Hentry in Htable.
    destruct Htable as [t Hlookup].
    assert (Hvalue : task_query_table_value sg acquired key = task_slot_addr sg tid).
    { unfold task_query_table_value; rewrite Hentry; reflexivity. }
    rewrite Hvalue.
    sep_apply_l_atomic (task_query_source_open_bytes sg acquired tid t Hlayout Hslot Hlookup).
    Intros bytes.
    match goal with H : task_query_source_byte_view sg acquired tid t bytes |- _ =>
      pose proof (task_query_source_byte_view_length sg acquired tid t bytes H) as Hlength end.
    sep_apply_l_atomic (UCharArray.mixed_full_to_undef_full output 64 old_output).
    Exists t bytes tid.
    pose proof (proj1 Hlayout) as Hsize.
    change (sizeof("os_tcb") = 64) in Hsize.
    change (sizeof(UCHAR)) with 1; rewrite Hsize.
    unfold mem_copy_pre, task_query_copy_frame; entailer!.
Qed.

Lemma proof_of_OSTaskQuery_which_implies_wit_9 : OSTaskQuery_which_implies_wit_9.
Proof.
  left; intros; subst p_task_data_pre; rewrite PreH5.
  eapply task_query_copy_reclose; eassumption.
Qed.

