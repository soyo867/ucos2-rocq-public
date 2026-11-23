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
From Ucos2Verify.VC.code.time Require Import time_dly_goal.
From Ucos2Verify.VC.code.time Require Import time_dly_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.time.spec.time_dly_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTimeDly_entail_wit_1 : OSTimeDly_entail_wit_1.
Proof.
  left; intros.
  subst ticks_pre.
  assert (Hpositive : time_dly_noop request before = false).
  { apply time_dly_positive; lia. }
  destruct PreH6 as [Hticks Hentry].
  destruct (Hentry Hpositive) as [_ [Hcompleted Hclients]].
  unfold task_suspend_save_history_post; Intros active acquired.
  assert (Hsave : task_suspend_save_effect environment critical sg caller active
    mask retval before acquired) by tauto.
  assert (Hmask : armv7a_irq_fiq_mask retval = mask).
  { assert (Hobservation : task_suspend_save_observation critical sg caller active
      mask retval before acquired) by tauto.
    destruct caller, active; cbn [task_suspend_save_observation] in Hobservation;
      try contradiction; unfold interrupt_saved_value in Hobservation; tauto. }
  unfold task_suspend_masked.
  sep_apply_l_atomic (UCOS2_inv_open_task_storage_sched sg acquired).
  Intros.
  assert (Hvalid : UCOS2_state_inv sg acquired) by tauto.
  destruct (proj1 Hcompleted active retval acquired Hsave Hvalid)
    as [Hsource [tid [target Htarget]]].
  assert (Hcurrent : curTaskID (SchedState acquired) = Some tid).
  { unfold time_dly_target_facts, sched_current_ready_at in Htarget; tauto. }
  assert (Hfacts : time_dly_acquired_facts environment critical sg caller mask request
    before retval active acquired tid target).
  { unfold time_dly_acquired_facts; split; [lia|tauto]. }
  Exists active acquired target tid (task_slot_addr sg tid).
  pose proof PreH2 as Haddresses.
  unfold task_suspend_addresses, os_sched_global_addresses, sched_new_global_addresses
    in Haddresses.
  destruct Haddresses as [Hcur [Hints [Hlocks [Hhigh [Hprio [Hhighptr
    [Htable [Hctr [Hunmap [Hgrp [Hrows Hhigh2]]]]]]]]]]].
  unfold task_suspend_tokens, task_suspend_work_frame, sched_raw_rep, sched_physical_rep,
    os_sched_group, os_sched_rows.
  rewrite sched_rows_array_equiv, Hcurrent.
  cbn [encode_task_link].
  rewrite <- Hcur, <- Hgrp, <- Hrows.
  entailer!.
Qed.

Lemma proof_of_OSTimeDly_entail_wit_2_1 : OSTimeDly_entail_wit_2_1.
Proof.
  left; intros.
  repeat rewrite replace_Znth_Znth in *.
  rewrite (os_sched_rows_Znth_eq__fields_bitmap acquired
    (tcb_y_of_prio target.(curPrio)) ltac:(lia)) in *.
  fold (task_suspend_cleared_row acquired target) in *.
  fold (time_dly_cleared_row acquired target) in *.
  rewrite Znth_replace_Znth_Same in PreH7 by
    (rewrite os_sched_rows_length_eq__fields_bitmap; lia).
  pose proof (task_suspend_cleared_row_in_range__fields_bitmap acquired target) as Hrowrange.
  change (0 <= time_dly_cleared_row acquired target < 256) in Hrowrange.
  rewrite unsigned_last_nbits_eq in PreH7 by (change (0 <= time_dly_cleared_row acquired target < 4294967296); lia).
  assert (Hgroup : time_dly_updated_group acquired target =
    Z.land (os_sched_group acquired) (unsigned_last_nbits (Z.lnot (tcb_bit_y_of_prio target.(curPrio))) 8)).
  { unfold time_dly_updated_group, task_suspend_updated_group.
    fold (time_dly_cleared_row acquired target).
    rewrite (proj2 (Z.eqb_eq _ 0) PreH7); reflexivity. }
  rewrite Hgroup.
  sep_apply (UCharArray.full_split_to_missing_i (&("OSRdyTbl")) (tcb_y_of_prio target.(curPrio)) 8
    (replace_Znth (tcb_y_of_prio target.(curPrio)) (time_dly_cleared_row acquired target)
      (os_sched_rows acquired)) 0 ltac:(lia)).
  rewrite Znth_replace_Znth_Same by (rewrite os_sched_rows_length_eq__fields_bitmap; lia).
  pose proof (uchar_array_missing_i_replace_equiv__fields_bitmap (os_sched_rows acquired)
    (&("OSRdyTbl")) (tcb_y_of_prio target.(curPrio)) 0 8
    (time_dly_cleared_row acquired target) ltac:(lia)) as Hmissing.
  rewrite Z.sub_0_r in Hmissing; rewrite Hmissing; entailer!.
Qed. 

Lemma proof_of_OSTimeDly_entail_wit_2_2 : OSTimeDly_entail_wit_2_2.
Proof.
  left; intros.
  repeat rewrite replace_Znth_Znth in *.
  rewrite (os_sched_rows_Znth_eq__fields_bitmap acquired
    (tcb_y_of_prio target.(curPrio)) ltac:(lia)) in *.
  fold (task_suspend_cleared_row acquired target) in *.
  fold (time_dly_cleared_row acquired target) in *.
  rewrite Znth_replace_Znth_Same in PreH1 by
    (rewrite os_sched_rows_length_eq__fields_bitmap; lia).
  pose proof (task_suspend_cleared_row_in_range__fields_bitmap acquired target) as Hrowrange.
  change (0 <= time_dly_cleared_row acquired target < 256) in Hrowrange.
  rewrite unsigned_last_nbits_eq in PreH1 by (change (0 <= time_dly_cleared_row acquired target < 4294967296); lia).
  assert (Hgroup : time_dly_updated_group acquired target = os_sched_group acquired).
  { unfold time_dly_updated_group, task_suspend_updated_group.
    fold (time_dly_cleared_row acquired target).
    rewrite (proj2 (Z.eqb_neq _ 0) PreH1); reflexivity. }
  rewrite Hgroup.
  sep_apply (UCharArray.full_split_to_missing_i (&("OSRdyTbl")) (tcb_y_of_prio target.(curPrio)) 8
    (replace_Znth (tcb_y_of_prio target.(curPrio)) (time_dly_cleared_row acquired target)
      (os_sched_rows acquired)) 0 ltac:(lia)).
  rewrite Znth_replace_Znth_Same by (rewrite os_sched_rows_length_eq__fields_bitmap; lia).
  pose proof (uchar_array_missing_i_replace_equiv__fields_bitmap (os_sched_rows acquired)
    (&("OSRdyTbl")) (tcb_y_of_prio target.(curPrio)) 0 8
    (time_dly_cleared_row acquired target) ltac:(lia)) as Hmissing.
  rewrite Z.sub_0_r in Hmissing; rewrite Hmissing; entailer!.
Qed. 

Lemma proof_of_OSTimeDly_entail_wit_3 : OSTimeDly_entail_wit_3.
Proof.
  left; intros; subst pointer y.
  pose proof PreH1 as [Hvalid [Hready Hrest]].
  pose proof Hready as [Hlookup [Hcurrent [Hcurrentprio [Hmember Heffective]]]].
  assert (Hsg : valid_stable_glob_vars sg).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile in Hvalid; tauto. }
  assert (Htasks : task_in_range sg acquired.(TskState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  assert (Hsched : sched_in_range sg acquired.(TskState) acquired.(SchedState)).
  { unfold sched_in_range; unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  assert (Hpriority : task_priority_in_range sg target.(curPrio)).
  { unfold task_in_range in Htasks.
    assert (Hranges : forall slot node, acquired.(TskState).(inUsedTaskStates) slot = Some node ->
      task_priority_in_range sg node.(curPrio)) by tauto.
    exact (Hranges tid target Hlookup). }
  pose proof (task_priority_y_in_range__fields_bitmap sg target.(curPrio) Hsg Hpriority) as Hy.
  assert (Hticks : request <> 0).
  { unfold time_dly_acquired_facts in PreH7; lia. }
  assert (Hstate : time_dly_state acquired tid target request =
    replace_SchedS (sched_remove_ready_task acquired.(SchedState) tid)
      (replace_TskS (glob_task_set_usedtask acquired.(TskState) tid
        (task_set_delay target request)) acquired)).
  { unfold time_dly_state; rewrite (proj2 (Z.eqb_neq request 0) Hticks); reflexivity. }
  assert (Hcuraddr : sg.(g_OSTCBCur) = &("OSTCBCur")) by
    (symmetry; unfold task_suspend_addresses in PreH5; tauto).
  assert (Hrowaddr : sg.(g_OSRdyTbl) = &("OSRdyTbl")) by
    (symmetry; unfold task_suspend_addresses, os_sched_global_addresses, sched_new_global_addresses in PreH5; tauto).
  assert (Hgroupaddr : sg.(g_OSRdyGrp) = &("OSRdyGrp")) by
    (symmetry; unfold task_suspend_addresses, os_sched_global_addresses, sched_new_global_addresses in PreH5; tauto).
  pose proof (sched_rows_merge_removed_ready_member sg acquired.(TskState) acquired.(SchedState)
    tid target (task_set_delay target request) Hsg Htasks Hsched Hlookup Hmember Hy) as Hrows.
  rewrite Hrowaddr in Hrows.
  change (((&("OSRdyTbl")) + tcb_y_of_prio target.(curPrio) * sizeof(UCHAR)) # UChar |->
    time_dly_cleared_row acquired target **
    UCharArray.missing_i (&("OSRdyTbl")) (tcb_y_of_prio target.(curPrio)) 0 8
      (os_sched_rows acquired) |--
    sched_rows_rep sg (glob_task_set_usedtask acquired.(TskState) tid (task_set_delay target request))
      (sched_remove_ready_task acquired.(SchedState) tid).(readyList)
      (0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: nil)) in Hrows.
  pose proof (proj1 (sched_remove_ready_member_encoding sg acquired.(TskState) acquired.(SchedState)
    tid target (task_set_delay target request) Hsg Htasks Hsched Hlookup Hmember)) as Hgroup.
  change (encode_ready_grp (sched_remove_ready_task acquired.(SchedState) tid).(readyList)
    (glob_task_set_usedtask acquired.(TskState) tid (task_set_delay target request)) =
    time_dly_updated_group acquired target) in Hgroup.
  pose proof (time_dly_delay_field_merge sg acquired.(TskState) tid target request) as Hdelay.
  cbn [tcb_field_address] in Hdelay.
  sep_apply_l_atomic Hdelay.
  sep_apply_l_atomic Hrows.
  sep_apply (store_uchar_undef_store_uchar (&("y")) (tcb_y_of_prio target.(curPrio))).
  unfold task_suspend_tokens.
  sep_apply_l_atomic (time_dly_call_resources_updated environment saved_local sg active
    acquired tid target request Hlookup).
  unfold task_suspend_masked.
  entailer!.
  sep_apply_r_atomic (time_dly_inv_merge_updated sg acquired tid target request PreH1).
  rewrite Hstate; cbn [replace_SchedS replace_TskS TskState SchedState].
  unfold sched_raw_rep; rewrite Hgroup, Hgroupaddr.
  unfold task_suspend_work_frame, sched_physical_rep.
  cbn [sched_remove_ready_task sched_set_ready curSchedPrio highRdyPrio curTaskID highRdyTid ctxSwCtr isRunning].
  rewrite Hcurrent, Hcuraddr; cbn [encode_task_link].
  entailer!.
Qed. 

Lemma proof_of_OSTimeDly_entail_wit_4 : OSTimeDly_entail_wit_4.
Proof.
  left; intros.
  unfold task_suspend_restore_history_post; Intros checkpoint_call checkpoint.
  assert (Hrestore : task_suspend_restore_effect environment critical sg active
    checkpoint_call (time_dly_state acquired tid target request) checkpoint) by tauto.
  pose proof (time_dly_acquired_restore_continuation environment critical sg caller mask
    request before cpu_sr active acquired tid target checkpoint_call checkpoint X
    PreH3 Hrestore PreH2) as [Hprefix [Hsource Hsafe]].
  assert (Hmask : armv7a_irq_fiq_mask cpu_sr = mask).
  { unfold time_dly_acquired_facts in PreH3; tauto. }
  assert (Hclients : kernel_sched_ready_clients critical).
  { unfold time_dly_acquired_facts in PreH3; tauto. }
  rewrite Hmask.
  Exists checkpoint_call checkpoint; entailer!.
Qed.

Lemma proof_of_OSTimeDly_return_wit_1 : OSTimeDly_return_wit_1.
Proof.
  left; intros.
  assert (Hnoop : time_dly_noop request before = true).
  { apply time_dly_noop_locked; lia. }
  pose proof (time_dly_closed_split_counters environment critical saved_local sg caller
    mask before) as Hcounters.
  destruct PreH3 as [_ [Hints [Hlocks _]]].
  rewrite <- Hints, <- Hlocks in Hcounters.
  sep_apply_l_atomic (proj2 Hcounters).
  apply time_dly_noop_call_post; assumption.
Qed.

Lemma proof_of_OSTimeDly_return_wit_2 : OSTimeDly_return_wit_2.
Proof.
  left; intros.
  assert (Hnoop : time_dly_noop request before = true).
  { apply time_dly_noop_isr; lia. }
  pose proof (time_dly_closed_split_counters environment critical saved_local sg caller
    mask before) as Hcounters.
  destruct PreH2 as [_ [Hints [Hlocks _]]].
  rewrite <- Hints, <- Hlocks in Hcounters.
  sep_apply_l_atomic (proj2 Hcounters).
  apply time_dly_noop_call_post; assumption.
Qed.

Lemma proof_of_OSTimeDly_return_wit_3 : OSTimeDly_return_wit_3.
Proof.
  left; intros.
  eapply time_dly_schedule_call_post.
  - unfold time_dly_acquired_facts in PreH3; tauto.
  - exact PreH4.
Qed.

Lemma proof_of_OSTimeDly_return_wit_4 : OSTimeDly_return_wit_4.
Proof.
  left; intros.
  assert (Hzero : request = 0).
  { destruct PreH6 as [Hrange _]; lia. }
  apply time_dly_noop_call_post; [rewrite Hzero; apply time_dly_noop_zero|exact PreH13].
Qed.

Lemma proof_of_OSTimeDly_which_implies_wit_1 : OSTimeDly_which_implies_wit_1.
Proof.
  left; intros.
  unfold time_dly_call_pre; Intros.
  rewrite time_dly_closed_split_counters.
  prop_apply_p (store_uchar_range (g_OSIntNesting sg) (os_sched_ints before)); Intros.
  prop_apply_p (store_uchar_range (g_OSLockNesting sg) (os_sched_locks before)); Intros.
  pose proof PreH1 as Haddresses.
  destruct Haddresses as [_ [Hints [Hlocks _]]].
  rewrite <- Hints, <- Hlocks.
  entailer!.
Qed.

Lemma proof_of_OSTimeDly_which_implies_wit_2 : OSTimeDly_which_implies_wit_2.
Proof.
  left; intros.
  pose proof (time_dly_closed_split_counters environment critical saved_local sg caller
    mask before) as Hcounters.
  pose proof PreH1 as Haddresses.
  destruct Haddresses as [_ [Hints [Hlocks _]]].
  rewrite <- Hints, <- Hlocks in Hcounters.
  sep_apply_l_atomic (proj2 Hcounters); entailer!.
Qed.

Lemma proof_of_OSTimeDly_which_implies_wit_3 : OSTimeDly_which_implies_wit_3.
Proof.
  left; intros sg acquired tid target pointer Hfacts Hpointer; subst pointer.
  pose proof Hfacts as [Hvalid [Hready Hrest]].
  pose proof Hready as [Hlookup Hcurrent].
  assert (Hsg : valid_stable_glob_vars sg).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile in Hvalid; tauto. }
  assert (Htasks : task_in_range sg acquired.(TskState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  assert (Hpriority : task_priority_in_range sg target.(curPrio)).
  { unfold task_in_range in Htasks.
    assert (Hranges : forall slot node, acquired.(TskState).(inUsedTaskStates) slot = Some node ->
      task_priority_in_range sg node.(curPrio)) by tauto.
    exact (Hranges tid target Hlookup). }
  pose proof (task_priority_y_in_range__fields_bitmap sg target.(curPrio) Hsg Hpriority) as Hy.
  pose proof (task_public_storage_split_field sg acquired.(TskState) tid target
    (TCBCommonField TCBY) Hlookup (tcb_configured_common_field_in _ _ _)) as Hsplit.
  cbn [tcb_layout_cell tcb_cell task_layout_image tcb_layout_image task_tcb64_image tcb_field_address] in Hsplit.
  rewrite Hsplit; entailer!; tauto.
Qed. 

Lemma proof_of_OSTimeDly_which_implies_wit_4 : OSTimeDly_which_implies_wit_4.
Proof.
  left; intros sg acquired tid target pointer Hfacts Hpointer; subst pointer.
  assert (Hlookup : acquired.(TskState).(inUsedTaskStates) tid = Some target).
  { unfold time_dly_target_facts, sched_current_ready_at in Hfacts; tauto. }
  pose proof (task_public_storage_merge_field sg acquired.(TskState) tid target
    (TCBCommonField TCBY) Hlookup (tcb_configured_common_field_in _ _ _)) as Hmerge.
  cbn [tcb_layout_cell tcb_cell task_layout_image tcb_layout_image task_tcb64_image tcb_field_address] in Hmerge.
  rewrite Hmerge; entailer!.
Qed. 

Lemma proof_of_OSTimeDly_which_implies_wit_5 : OSTimeDly_which_implies_wit_5.
Proof.
  left; intros sg acquired tid target pointer y Hfacts Hpointer Hy Hylo Hyhi; subst pointer.
  assert (Hlookup : acquired.(TskState).(inUsedTaskStates) tid = Some target).
  { unfold time_dly_target_facts, sched_current_ready_at in Hfacts; tauto. }
  pose proof (task_public_storage_split_field sg acquired.(TskState) tid target
    (TCBCommonField TCBBitX) Hlookup (tcb_configured_common_field_in _ _ _)) as Hsplit.
  cbn [tcb_layout_cell tcb_cell task_layout_image tcb_layout_image task_tcb64_image tcb_field_address] in Hsplit.
  rewrite Hsplit.
  sep_apply (UCharArray.full_split_to_missing_i (&("OSRdyTbl")) y 8 (os_sched_rows acquired) 0 ltac:(lia)).
  prop_apply_p (store_uchar_range (tcb_field_address (task_slot_addr sg tid) TCBBitX)
    (tcb_bit_x_of_prio target.(curPrio))); Intros.
  entailer!.
Qed. 

Lemma proof_of_OSTimeDly_which_implies_wit_6 : OSTimeDly_which_implies_wit_6.
Proof.
  left; intros sg acquired tid target pointer Hfacts Hpointer; subst pointer.
  assert (Hlookup : acquired.(TskState).(inUsedTaskStates) tid = Some target).
  { unfold time_dly_target_facts, sched_current_ready_at in Hfacts; tauto. }
  pose proof (task_public_storage_merge_field sg acquired.(TskState) tid target
    (TCBCommonField TCBBitX) Hlookup (tcb_configured_common_field_in _ _ _)) as Hmerge.
  cbn [tcb_layout_cell tcb_cell task_layout_image tcb_layout_image task_tcb64_image tcb_field_address] in Hmerge.
  rewrite Hmerge; entailer!.
Qed. 

Lemma proof_of_OSTimeDly_which_implies_wit_7 : OSTimeDly_which_implies_wit_7.
Proof.
  left; intros sg acquired tid target pointer Hfacts Hpointer; subst pointer.
  assert (Hlookup : acquired.(TskState).(inUsedTaskStates) tid = Some target).
  { unfold time_dly_target_facts, sched_current_ready_at in Hfacts; tauto. }
  pose proof (task_public_storage_split_field sg acquired.(TskState) tid target
    (TCBCommonField TCBBitY) Hlookup (tcb_configured_common_field_in _ _ _)) as Hsplit.
  cbn [tcb_layout_cell tcb_cell task_layout_image tcb_layout_image task_tcb64_image tcb_field_address] in Hsplit.
  rewrite Hsplit.
  prop_apply_p (store_uchar_range (tcb_field_address (task_slot_addr sg tid) TCBBitY)
    (tcb_bit_y_of_prio target.(curPrio))); Intros.
  entailer!.
Qed. 

Lemma proof_of_OSTimeDly_which_implies_wit_8 : OSTimeDly_which_implies_wit_8.
Proof.
  left; intros sg acquired tid target pointer Hfacts Hpointer; subst pointer.
  assert (Hlookup : acquired.(TskState).(inUsedTaskStates) tid = Some target).
  { unfold time_dly_target_facts, sched_current_ready_at in Hfacts; tauto. }
  pose proof (task_public_storage_merge_field sg acquired.(TskState) tid target
    (TCBCommonField TCBBitY) Hlookup (tcb_configured_common_field_in _ _ _)) as Hmerge.
  cbn [tcb_layout_cell tcb_cell task_layout_image tcb_layout_image task_tcb64_image tcb_field_address] in Hmerge.
  rewrite Hmerge; entailer!.
Qed. 

Lemma proof_of_OSTimeDly_which_implies_wit_9 : OSTimeDly_which_implies_wit_9.
Proof.
  left; intros sg acquired tid target pointer Hfacts Hpointer; subst pointer.
  assert (Hlookup : acquired.(TskState).(inUsedTaskStates) tid = Some target).
  { unfold time_dly_target_facts, sched_current_ready_at in Hfacts; tauto. }
  pose proof (task_public_storage_split_field sg acquired.(TskState) tid target
    (TCBCommonField TCBDly) Hlookup (tcb_configured_common_field_in _ _ _)) as Hsplit.
  cbn [tcb_layout_cell tcb_cell task_layout_image tcb_layout_image task_tcb64_image tcb_field_address] in Hsplit.
  rewrite Hsplit; entailer!.
Qed. 

Lemma proof_of_OSTimeDly_which_implies_wit_10 : OSTimeDly_which_implies_wit_10.
Proof.
  left; intros; apply time_dly_scheduler_source_pre; assumption.
Qed.

