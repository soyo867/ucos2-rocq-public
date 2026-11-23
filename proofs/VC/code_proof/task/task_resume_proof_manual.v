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
From Ucos2Verify.VC.code.task Require Import task_resume_goal.
From Ucos2Verify.VC.code.task Require Import task_resume_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_api_spec.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_status Ucos2Verify.lib.sched Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTaskResume_entail_wit_1 : OSTaskResume_entail_wit_1.
Proof.
  unfold OSTaskResume_entail_wit_1; right; intros.
  sep_apply_l_atomic (task_resume_save_output_acquire__resume_calls_returns
    environment critical saved_local sg caller mask retval initial PreH11 PreH12 PreH13).
  Intros active acquired; Exists active acquired; entailer!.
Qed.

Lemma proof_of_OSTaskResume_entail_wit_2 : OSTaskResume_entail_wit_2.
Proof.
  left; intros.
  assert (Hrange : 0 <= priority < 64) by lia.
  pose proof (task_resume_entry_addr_eq_null__resume_storage sg acquired priority PreH2 Hrange PreH1) as Hentry.
  assert (Hcode : task_resume_critical_code sg priority acquired (70, false) acquired).
  { exists error_codes.OS_ERR_TASK_RESUME_PRIO; split; [reflexivity|].
    unfold task_resume_critical; split.
    - apply task_resume_priority_in_range__resume_storage; assumption.
    - rewrite Hentry; split; reflexivity. }
  destruct PreH9 as [_ [_ [_ [_ [_ [Htable _]]]]]].
  pose proof (task_resume_priority_cell_merge__resume_storage sg acquired priority Hrange PreH2) as Hmerge.
  rewrite <- Htable in Hmerge.
  rewrite task_resume_masked_split_inv__resume_storage.
  sep_apply_l_atomic Hmerge; rewrite PreH1; entailer!.
Qed.

Lemma proof_of_OSTaskResume_entail_wit_3 : OSTaskResume_entail_wit_3.
Proof.
  left; intros.
  assert (Hrange : 0 <= priority < 64) by lia.
  pose proof (task_resume_entry_addr_eq_reserved sg (acquired.(TskState).(prioTbl) priority)
    PreH6 PreH7 PreH1) as Hentry.
  assert (Hcode : task_resume_critical_code sg priority acquired (67, false) acquired).
  { exists error_codes.OS_ERR_TASK_NOT_EXIST; split; [reflexivity|].
    unfold task_resume_critical; split.
    - apply task_resume_priority_in_range__resume_storage; assumption.
    - rewrite Hentry; split; reflexivity. }
  destruct PreH10 as [_ [_ [_ [_ [_ [Htable _]]]]]].
  pose proof (task_resume_priority_cell_merge__resume_storage sg acquired priority Hrange PreH3) as Hmerge.
  rewrite <- Htable in Hmerge.
  rewrite task_resume_masked_split_inv__resume_storage.
  sep_apply_l_atomic Hmerge; rewrite PreH1; entailer!.
Qed.

Lemma proof_of_OSTaskResume_entail_wit_4 : OSTaskResume_entail_wit_4.
Proof.
  left; intros.
  assert (Hrange : 0 <= priority < 64) by lia.
  destruct (acquired.(TskState).(prioTbl) priority) as [| |tid] eqn:Hentry;
    [contradiction PreH2; reflexivity|contradiction PreH1; reflexivity|].
  destruct (task_resume_priority_task_live__resume_storage sg acquired priority tid PreH3 Hrange Hentry)
    as [node Hnode].
  destruct (task_resume_live_priority_range__resume_storage sg acquired tid node PreH3 Hnode)
    as [Hprio [Hylow Hyhigh]].
  pose proof PreH10 as Haddresses.
  destruct Haddresses as [_ [_ [_ [_ [_ [Htable [_ [_ [Hgroup [Hrows _]]]]]]]]]].
  pose proof (task_resume_priority_cell_merge__resume_storage sg acquired priority Hrange PreH3) as Hmerge.
  rewrite <- Htable, Hentry in Hmerge.
  pose proof (task_resume_node_split__resume_storage sg acquired tid node PreH3 Hnode) as Hsplit.
  rewrite <- Hgroup, <- Hrows in Hsplit.
  cbn [tcb_layout_cell tcb_cell tcb_field_address] in Hsplit.
  sep_apply_l_atomic Hmerge; sep_apply_l_atomic Hsplit.
  Exists node tid; entailer!.
Qed.

Lemma proof_of_OSTaskResume_entail_wit_5 : OSTaskResume_entail_wit_5.
Proof.
  left; intros; subst ptcb.
  change (unsigned_last_nbits (Z.lnot 8) 8) with 247 in *.
  assert (Hsuspended : task_is_suspended node.(stat) = true).
  { change (negb (Z.eqb (Z.land (encode_task_status node.(stat)) 8) 0) = true).
    apply Bool.negb_true_iff; apply Z.eqb_neq; exact PreH3. }
  assert (Hready : task_resume_ready_test node = true).
  { apply task_resume_ready_test_iff.
    rewrite <- Z.land_assoc in PreH2.
    change (Z.land (encode_task_status node.(stat)) 55 = 0) in PreH2.
    split; assumption. }
  assert (Hcode : task_resume_critical_code sg priority acquired (0, true)
    (task_resume_state sg acquired tid node)).
  { exists error_codes.OS_ERR_NONE; split; [reflexivity|].
    unfold task_resume_critical; split.
    - apply task_resume_priority_in_range__resume_storage; [exact PreH6|lia].
    - rewrite PreH12; exists node; split; [exact PreH13|].
      rewrite Hsuspended, Hready; split; reflexivity. }
  assert (Hsource : task_resume_caller_source sg active (task_resume_state sg acquired tid node)).
  { apply task_resume_caller_source_update__resume_storage; [exact PreH13|].
    destruct PreH10 as [_ [_ [_ [_ [_ [Hsource _]]]]]]; exact Hsource. }
  destruct (task_resume_bitmap_bytes__resume_storage sg acquired tid node PreH11 PreH13)
    as [Hgroupbyte [Hrowbyte [Hxbyte Hybyte]]].
  rewrite Hgroupbyte, Hrowbyte, Hxbyte, Hybyte.
  pose proof PreH9 as Haddresses.
  destruct Haddresses as [_ [_ [_ [_ [_ [_ [_ [_ [Hgroup [Hrows _]]]]]]]]]].
  pose proof (task_resume_node_merge_updated__resume_storage sg acquired tid node
    PreH11 PreH13 Hsuspended) as Hmerge.
  rewrite Hready, <- Hgroup, <- Hrows in Hmerge.
  cbn [tcb_layout_cell tcb_cell tcb_field_address] in Hmerge.
  rewrite task_resume_masked_split_inv__resume_storage.
  entailer!.
  sepcon_assoc_change.
  sep_apply_r_atomic Hmerge.
  sep_apply_l_atomic (task_resume_mask_frame_update__resume_storage environment critical saved_local
    sg active saved acquired acquired tid node PreH13).
  entailer!.
Qed.

Lemma proof_of_OSTaskResume_entail_wit_6 : OSTaskResume_entail_wit_6.
Proof.
  unfold OSTaskResume_entail_wit_6; left; intros.
  sep_apply_l_atomic (task_resume_restore_output_return__resume_calls_returns
    environment critical saved_local sg caller active mask initial acquired saved priority 0 true
    (task_resume_state sg acquired tid node) PreH1 PreH6 PreH7).
  Intros returned restored; Exists returned restored; entailer!.
Qed.

Lemma proof_of_OSTaskResume_entail_wit_7 : OSTaskResume_entail_wit_7.
Proof.
  unfold OSTaskResume_entail_wit_7; left; intros.
  assert (Hrunning : restored.(SchedState).(isRunning) = true).
  { unfold task_resume_running in PreH1.
    destruct restored.(SchedState).(isRunning); [reflexivity|discriminate]. }
  assert (Hguard : task_resume_requests_schedule true restored = true)
    by (unfold task_resume_requests_schedule; exact Hrunning).
  pose proof (task_resume_return_facts_sched_safe environment critical sg caller returned mask
    initial priority 0 true restored X PreH3 PreH6 Hguard PreH7) as Hschedule.
  rewrite <- PreH4, <- task_resume_running_split.
  sep_apply_l_atomic (task_resume_closed_sched_pre__resume_calls_returns
    environment critical saved_local sg caller returned mask initial priority restored PreH6 Hrunning).
  unfold task_resume_requests_schedule; rewrite Hrunning; entailer!.
Qed.

Lemma proof_of_OSTaskResume_entail_wit_8 : OSTaskResume_entail_wit_8.
Proof.
  left; intros; subst ptcb.
  change (unsigned_last_nbits (Z.lnot 8) 8) with 247 in *.
  assert (Hsuspended : task_is_suspended node.(stat) = true).
  { change (negb (Z.eqb (Z.land (encode_task_status node.(stat)) 8) 0) = true).
    apply Bool.negb_true_iff; apply Z.eqb_neq; exact PreH3. }
  assert (Hready : task_resume_ready_test node = false).
  { destruct (task_resume_ready_test node) eqn:Hready; [|reflexivity].
    apply task_resume_ready_test_iff in Hready; destruct Hready as [_ Hdly]; contradiction. }
  assert (Hcode : task_resume_critical_code sg priority acquired (0, false)
    (task_resume_state sg acquired tid node)).
  { exists error_codes.OS_ERR_NONE; split; [reflexivity|].
    unfold task_resume_critical; split.
    - apply task_resume_priority_in_range__resume_storage; [exact PreH6|lia].
    - rewrite PreH12; exists node; split; [exact PreH13|].
      rewrite Hsuspended, Hready; split; reflexivity. }
  assert (Hsource : task_resume_caller_source sg active (task_resume_state sg acquired tid node)).
  { apply task_resume_caller_source_update__resume_storage; [exact PreH13|].
    destruct PreH10 as [_ [_ [_ [_ [_ [Hsource _]]]]]]; exact Hsource. }
  pose proof PreH9 as Haddresses.
  destruct Haddresses as [_ [_ [_ [_ [_ [_ [_ [_ [Hgroup [Hrows _]]]]]]]]]].
  pose proof (task_resume_node_merge_updated__resume_storage sg acquired tid node
    PreH11 PreH13 Hsuspended) as Hmerge.
  rewrite Hready, <- Hgroup, <- Hrows in Hmerge.
  cbn [tcb_layout_cell tcb_cell tcb_field_address] in Hmerge.
  rewrite task_resume_masked_split_inv__resume_storage.
  entailer!.
  sepcon_assoc_change.
  sep_apply_r_atomic Hmerge.
  sep_apply_l_atomic (task_resume_mask_frame_update__resume_storage environment critical saved_local
    sg active saved acquired acquired tid node PreH13).
  entailer!.
Qed.

Lemma proof_of_OSTaskResume_entail_wit_9 : OSTaskResume_entail_wit_9.
Proof.
  left; intros; subst ptcb.
  change (unsigned_last_nbits (Z.lnot 8) 8) with 247 in *.
  assert (Hsuspended : task_is_suspended node.(stat) = true).
  { change (negb (Z.eqb (Z.land (encode_task_status node.(stat)) 8) 0) = true).
    apply Bool.negb_true_iff; apply Z.eqb_neq; exact PreH2. }
  assert (Hready : task_resume_ready_test node = false).
  { destruct (task_resume_ready_test node) eqn:Hready; [|reflexivity].
    apply task_resume_ready_test_iff in Hready; destruct Hready as [Hpending _].
    rewrite <- Z.land_assoc in PreH1.
    change (Z.land (encode_task_status node.(stat)) 55 <> 0) in PreH1.
    contradiction. }
  assert (Hcode : task_resume_critical_code sg priority acquired (0, false)
    (task_resume_state sg acquired tid node)).
  { exists error_codes.OS_ERR_NONE; split; [reflexivity|].
    unfold task_resume_critical; split.
    - apply task_resume_priority_in_range__resume_storage; [exact PreH5|lia].
    - rewrite PreH11; exists node; split; [exact PreH12|].
      rewrite Hsuspended, Hready; split; reflexivity. }
  assert (Hsource : task_resume_caller_source sg active (task_resume_state sg acquired tid node)).
  { apply task_resume_caller_source_update__resume_storage; [exact PreH12|].
    destruct PreH9 as [_ [_ [_ [_ [_ [Hsource _]]]]]]; exact Hsource. }
  pose proof PreH8 as Haddresses.
  destruct Haddresses as [_ [_ [_ [_ [_ [_ [_ [_ [Hgroup [Hrows _]]]]]]]]]].
  pose proof (task_resume_node_merge_updated__resume_storage sg acquired tid node
    PreH10 PreH12 Hsuspended) as Hmerge.
  rewrite Hready, <- Hgroup, <- Hrows in Hmerge.
  cbn [tcb_layout_cell tcb_cell tcb_field_address] in Hmerge.
  rewrite task_resume_masked_split_inv__resume_storage.
  entailer!.
  sepcon_assoc_change.
  sep_apply_r_atomic Hmerge.
  sep_apply_l_atomic (task_resume_mask_frame_update__resume_storage environment critical saved_local
    sg active saved acquired acquired tid node PreH12).
  entailer!.
Qed.

Lemma proof_of_OSTaskResume_entail_wit_10 : OSTaskResume_entail_wit_10.
Proof.
  left; intros; subst ptcb.
  assert (Hsuspended : task_is_suspended node.(stat) = false).
  { change (negb (Z.eqb (Z.land (encode_task_status node.(stat)) 8) 0) = false).
    rewrite PreH1; reflexivity. }
  assert (Hcode : task_resume_critical_code sg priority acquired (68, false) acquired).
  { exists error_codes.OS_ERR_TASK_NOT_SUSPENDED; split; [reflexivity|].
    unfold task_resume_critical; split.
    - apply task_resume_priority_in_range__resume_storage; [exact PreH4|lia].
    - rewrite PreH10; exists node; split; [exact PreH11|].
      rewrite Hsuspended; split; reflexivity. }
  pose proof PreH7 as Haddresses.
  destruct Haddresses as [_ [_ [_ [_ [_ [_ [_ [_ [Hgroup [Hrows _]]]]]]]]]].
  pose proof (task_resume_node_merge__resume_storage sg acquired tid node PreH9 PreH11) as Hmerge.
  rewrite <- Hgroup, <- Hrows in Hmerge.
  cbn [tcb_layout_cell tcb_cell tcb_field_address] in Hmerge.
  rewrite task_resume_masked_split_inv__resume_storage.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma proof_of_OSTaskResume_return_wit_1 : OSTaskResume_return_wit_1.
Proof.
  unfold OSTaskResume_return_wit_1; left; intros.
  assert (Hcaller : task_resume_caller_source sg active acquired)
    by (unfold task_resume_acquire_facts in PreH1; tauto).
  sep_apply_l_atomic (task_resume_restore_output_return__resume_calls_returns
    environment critical saved_local sg caller active mask initial acquired saved priority 68 false
    acquired PreH1 PreH4 Hcaller).
  Intros returned restored.
  exact (task_resume_closed_return_post environment critical saved_local sg caller returned mask
    initial priority 68 false restored X ltac:(lia) H eq_refl PreH5).
Qed.

Lemma proof_of_OSTaskResume_return_wit_2 : OSTaskResume_return_wit_2.
Proof.
  unfold OSTaskResume_return_wit_2; left; intros.
  exact (task_resume_sched_return_post environment critical saved_local sg caller returned mask
    initial priority 0 true restored X ltac:(lia) PreH1 PreH4 PreH6).
Qed.

Lemma proof_of_OSTaskResume_return_wit_3 : OSTaskResume_return_wit_3.
Proof.
  unfold OSTaskResume_return_wit_3; left; intros.
  assert (Hrunning : restored.(SchedState).(isRunning) = false).
  { unfold task_resume_running in PreH1.
    destruct restored.(SchedState).(isRunning); [exfalso; apply PreH1; reflexivity|reflexivity]. }
  assert (Hguard : task_resume_requests_schedule true restored = false)
    by (unfold task_resume_requests_schedule; exact Hrunning).
  rewrite <- PreH4, <- task_resume_running_split.
  exact (task_resume_closed_return_post environment critical saved_local sg caller returned mask
    initial priority 0 true restored X ltac:(lia) PreH6 Hguard PreH7).
Qed.

Lemma proof_of_OSTaskResume_return_wit_4 : OSTaskResume_return_wit_4.
Proof.
  unfold OSTaskResume_return_wit_4; left; intros.
  sep_apply_l_atomic (task_resume_restore_output_return__resume_calls_returns
    environment critical saved_local sg caller active mask initial acquired saved priority 0 false
    (task_resume_state sg acquired tid node) PreH1 PreH4 PreH5).
  Intros returned restored.
  exact (task_resume_closed_return_post environment critical saved_local sg caller returned mask
    initial priority 0 false restored X ltac:(lia) H eq_refl PreH6).
Qed.

Lemma proof_of_OSTaskResume_return_wit_5 : OSTaskResume_return_wit_5.
Proof.
  unfold OSTaskResume_return_wit_5; left; intros.
  sep_apply_l_atomic (task_resume_restore_output_return__resume_calls_returns
    environment critical saved_local sg caller active mask initial acquired saved priority 0 false
    (task_resume_state sg acquired tid node) PreH1 PreH4 PreH5).
  Intros returned restored.
  exact (task_resume_closed_return_post environment critical saved_local sg caller returned mask
    initial priority 0 false restored X ltac:(lia) H eq_refl PreH6).
Qed.

Lemma proof_of_OSTaskResume_return_wit_6 : OSTaskResume_return_wit_6.
Proof.
  unfold OSTaskResume_return_wit_6; left; intros.
  assert (Hcaller : task_resume_caller_source sg active acquired)
    by (unfold task_resume_acquire_facts in PreH1; tauto).
  sep_apply_l_atomic (task_resume_restore_output_return__resume_calls_returns
    environment critical saved_local sg caller active mask initial acquired saved priority 67 false
    acquired PreH1 PreH4 Hcaller).
  Intros returned restored.
  exact (task_resume_closed_return_post environment critical saved_local sg caller returned mask
    initial priority 67 false restored X ltac:(lia) H eq_refl PreH5).
Qed.

Lemma proof_of_OSTaskResume_return_wit_7 : OSTaskResume_return_wit_7.
Proof.
  unfold OSTaskResume_return_wit_7; left; intros.
  assert (Hcaller : task_resume_caller_source sg active acquired)
    by (unfold task_resume_acquire_facts in PreH1; tauto).
  sep_apply_l_atomic (task_resume_restore_output_return__resume_calls_returns
    environment critical saved_local sg caller active mask initial acquired saved priority 70 false
    acquired PreH1 PreH4 Hcaller).
  Intros returned restored.
  exact (task_resume_closed_return_post environment critical saved_local sg caller returned mask
    initial priority 70 false restored X ltac:(lia) H eq_refl PreH5).
Qed.

Lemma proof_of_OSTaskResume_return_wit_8 : OSTaskResume_return_wit_8.
Proof.
  unfold OSTaskResume_return_wit_8; left; intros.
  pose proof (task_resume_early_safe_return environment critical sg caller mask priority initial X
    ltac:(lia) PreH14) as Hreturn.
  unfold task_resume_post; Left; entailer!.
Qed.

Lemma proof_of_OSTaskResume_return_wit_9 : OSTaskResume_return_wit_9.
Proof.
  unfold OSTaskResume_return_wit_9; left; intros.
  pose proof (task_resume_early_safe_return environment critical sg caller mask priority initial X
    PreH10 PreH11) as Hreturn.
  unfold task_resume_post; Left; entailer!.
Qed.

Lemma proof_of_OSTaskResume_which_implies_wit_1 : OSTaskResume_which_implies_wit_1.
Proof.
  left; intros; apply (proj1 (task_resume_masked_split_inv__resume_storage _ _ _ _ _ _ _ _)).
Qed.

Lemma proof_of_OSTaskResume_which_implies_wit_2 : OSTaskResume_which_implies_wit_2.
Proof.
  left; intros.
  destruct PreH3 as [_ [_ [_ [_ [_ [Htable _]]]]]].
  unfold task_resume_priority_frame; rewrite Htable.
  sep_apply_l_atomic (UCOS2_inv_split_priority_cell sg acquired priority ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_OSTaskResume_which_implies_wit_3 : OSTaskResume_which_implies_wit_3.
Proof.
  left; intros.
  pose proof (proj1 (task_resume_running_split environment critical saved_local sg returned mask restored)) as Hsplit.
  rewrite PreH1 in Hsplit; exact Hsplit.
Qed.

