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
From Ucos2Verify.VC.code.task Require Import init_tcb_list_goal.
From Ucos2Verify.VC.code.task Require Import init_tcb_list_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_full_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_full_prio_spec.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope Z_scope.
Local Open Scope sac.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_proof_helpers.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.task.

Lemma proof_of_OS_InitTCBList_entail_wit_2 : OS_InitTCBList_entail_wit_2.
Proof.
  right; intros LitMap sg ix Hprofile Hglobals Hlayout Hfields; intros.
  destruct Hglobals as [Hpool [Hprios [Hused Hfree]]].
  pose proof (init_tcb_list_full_profile_valid sg Hprofile) as Hconfig.
  pose proof (init_tcb_list_full_layout_source_size sg Hlayout) as Hsizeof.
  assert (Hslot : forall tid,
    (( &( "OSTCBTbl" ) ) + tid * sizeof("os_tcb")) = task_slot_addr sg tid).
  { intro tid.
    rewrite Hpool.
    replace (sizeof("os_tcb")) with 92 by (symmetry; exact Hsizeof).
    unfold task_slot_addr, task_object_size, tcb_configured_size, tcb_layout_size.
    rewrite Hconfig; reflexivity. }
  rewrite !Hslot.
  rewrite Z.mul_0_l, Z.add_0_r.
  unfold init_tcb_list_full_loop_state, init_tcb_list_full_loop_residual.
  fold (init_tcb_list_full_node_residual sg ix).
  pose proof (init_tcb_list_full_node_merge_next_name sg ix
    (Some (ix + 1)) (LitMap "?") Hprofile) as Hmerge.
  cbn [tcb_layout_cell tcb_cell tcb_field_address encode_task_link] in Hmerge.
  sepcon_right_assoc.
  sep_apply_l_atomic Hmerge.
  unfold init_tcb_list_full_prefix.
  sep_apply_l_atomic (task_free_storage_range_extend_full
    sg (task_boot_storage sg (LitMap "?") (SumLib.ZRange.Zrange 0 22)) 0 ix
    (tcb_init_free_image sg (Some (ix + 1)) (LitMap "?")) ltac:(lia)
    ltac:(rewrite task_boot_storage_range_lookup_full by lia;
      rewrite (init_tcb_list_full_zrange_head (ix + 1) 22) by lia;
      cbn [task_boot_image]; reflexivity)).
  entailer!.
Qed.

Lemma proof_of_OS_InitTCBList_entail_wit_4 : OS_InitTCBList_entail_wit_4.
Proof.
  right; intros LitMap sg ix Hprofile Hglobals Hlayout Hfields; intros.
  subst ix.
  destruct Hglobals as [Hpool [Hprios [Hused Hfree]]].
  pose proof (init_tcb_list_full_profile_valid sg Hprofile) as Hconfig.
  pose proof (init_tcb_list_full_layout_source_size sg Hlayout) as Hsizeof.
  assert (Hslot : forall tid,
    (( &( "OSTCBTbl" ) ) + tid * sizeof("os_tcb")) = task_slot_addr sg tid).
  { intro tid.
    rewrite Hpool.
    replace (sizeof("os_tcb")) with 92 by (symmetry; exact Hsizeof).
    unfold task_slot_addr, task_object_size, tcb_configured_size, tcb_layout_size.
    rewrite Hconfig; reflexivity. }
  rewrite !Hslot.
  rewrite Z.mul_0_l, Z.add_0_r.
  unfold init_tcb_list_full_loop_state, init_tcb_list_full_loop_residual.
  fold (init_tcb_list_full_node_residual sg 21).
  pose proof (init_tcb_list_full_node_merge_next_name sg 21
    None (LitMap "?") Hprofile) as Hmerge.
  cbn [tcb_layout_cell tcb_cell tcb_field_address encode_task_link] in Hmerge.
  sepcon_right_assoc.
  sep_apply_l_atomic Hmerge.
  unfold init_tcb_list_full_prefix.
  sep_apply_l_atomic (task_free_storage_range_extend_full
    sg (task_boot_storage sg (LitMap "?") (SumLib.ZRange.Zrange 0 22)) 0 21
    (tcb_init_free_image sg None (LitMap "?")) ltac:(lia)
    ltac:(rewrite task_boot_storage_range_lookup_full by lia;
      cbn [task_boot_image]; reflexivity)).
  entailer!.
Qed.

Lemma proof_of_OS_InitTCBList_return_wit_1 : OS_InitTCBList_return_wit_1.
Proof.
  right; intros LitMap sg Hprofile Hglobals Hlayout Hfield
    Hprofile' Hglobals' Hlayout' Hfield'.
  destruct Hglobals as [Hpool [Hprios [Hused Hfree]]].
  unfold init_tcb_list_full_post, init_tcb_list_full_prefix.
  rewrite Hpool, Hused, Hfree.
  rewrite Z.mul_0_l, Z.add_0_r.
  entailer!.
Qed.

Lemma proof_of_OS_InitTCBList_which_implies_wit_1 : OS_InitTCBList_which_implies_wit_1.
Proof.
  right; intros sg Hprofile Hglobals Hlayout Hfields.
  destruct Hglobals as [Hpool [Hprios [Hused Hfree]]].
  destruct Hlayout as [Hsizeof [Hsize [Hpoolpos [Hpoolend [Hpoolalign [Hpriopos [Hprioend Hprioalign]]]]]]].
  rewrite Hpool, Hprios, Hsizeof.
  change (sizeof(PTR)) with 4; change (sizeof(UCHAR)) with 1.
  unfold init_tcb_list_full_pre, init_tcb_list_full_roots, mem_clr_pre.
  repeat rewrite Z.mul_0_l; repeat rewrite Z.add_0_r.
  entailer!; unfold UINT_MAX; lia.
Qed.

Lemma proof_of_OS_InitTCBList_which_implies_wit_2 : OS_InitTCBList_which_implies_wit_2.
Proof.
  right; intros LitMap sg Hprofile Hglobals Hlayout Hfields.
  destruct Hglobals as [Hpool [Hprios [Hused Hfree]]].
  pose proof (init_tcb_list_full_layout_source_size sg Hlayout) as Hsizeof.
  rewrite Hpool, Hprios, Hsizeof.
  change (sizeof(PTR)) with 4.
  repeat rewrite Z.mul_0_l; repeat rewrite Z.add_0_r.
  unfold mem_clr_post.
  pose proof (zero_bytes_to_full_task_storage sg 22%nat 0 Hprofile Hlayout Hfields
    ltac:(lia) ltac:(lia)) as Htcb.
  rewrite (init_tcb_list_full_slot_addr_stride sg 0 Hprofile), Z.mul_0_l, Z.add_0_r in Htcb.
  sep_apply_l_atomic Htcb.
  sep_apply_l_atomic (zero_bytes_to_full_prio_table sg Hlayout).
  unfold init_tcb_list_full_loop_state, init_tcb_list_full_prefix,
    init_tcb_list_full_priority_zero, init_tcb_list_full_zero_suffix.
  change (SumLib.ZRange.Zrange 0 0) with (@nil Z).
  change (task_free_storage_rep sg (task_boot_storage sg (LitMap "?")
    (SumLib.ZRange.Zrange 0 22)) []) with emp.
  entailer!.
  change (task_free_storage_rep sg
    (fun _ => Some init_tcb_list_full_zero_image) (SumLib.ZRange.Zrange 0 22)
    |-- emp ** task_free_storage_rep sg
      (fun _ => Some init_tcb_list_full_zero_image) (SumLib.ZRange.Zrange 0 22)).
  entailer!.
Qed.

Lemma proof_of_OS_InitTCBList_which_implies_wit_3 : OS_InitTCBList_which_implies_wit_3.
Proof.
  right; intros LitMap sg ix ix_next ptcb1 ptcb2 Hprofile Hglobals Hlayout Hfields Hlo Hhi Hnext Hptr1 Hptr2.
  destruct Hglobals as [Hpool Hrest].
  subst ptcb1.
  rewrite Hpool, (init_tcb_list_full_layout_source_size sg Hlayout).
  rewrite <- (init_tcb_list_full_slot_addr_stride sg ix Hprofile).
  pose proof (init_tcb_list_full_loop_split_next_name sg (LitMap "?") ix Hprofile ltac:(lia)) as Hsplit.
  cbn [tcb_layout_cell tcb_cell tcb_field_address] in Hsplit.
  exact Hsplit.
Qed.

Lemma proof_of_OS_InitTCBList_which_implies_wit_4 : OS_InitTCBList_which_implies_wit_4.
Proof.
  right; intros LitMap sg ix ptcb1 Hprofile Hglobals Hlayout Hfields Hlo Hhi Hptr.
  assert (ix = 21) by lia; subst ix ptcb1.
  destruct Hglobals as [Hpool Hrest].
  rewrite Hpool, (init_tcb_list_full_layout_source_size sg Hlayout).
  rewrite <- (init_tcb_list_full_slot_addr_stride sg 21 Hprofile).
  pose proof (init_tcb_list_full_loop_split_next_name sg (LitMap "?") 21 Hprofile ltac:(lia)) as Hsplit.
  cbn [tcb_layout_cell tcb_cell tcb_field_address] in Hsplit.
  exact Hsplit.
Qed.

Lemma proof_of_OS_InitTCBList_which_implies_wit_5 : OS_InitTCBList_which_implies_wit_5.
Proof.
  left; intros LitMap sg Hprofile Hglobals Hlayout Hfields.
  pose proof Hglobals as [_ [_ [Hused Hfree]]].
  unfold init_tcb_list_full_loop_state, init_tcb_list_full_roots,
    init_tcb_list_full_zero_suffix.
  rewrite (init_tcb_list_full_zrange_empty 22 22) by lia.
  change (task_free_storage_rep sg (fun _ => Some init_tcb_list_full_zero_image) []) with emp.
  rewrite Hused, Hfree.
  rewrite Hused, Hfree in Hglobals.
  entailer!.
  change (init_tcb_list_full_prefix sg (LitMap "?") 22 ** emp
    |-- init_tcb_list_full_prefix sg (LitMap "?") 22).
  entailer!.
Qed.

Lemma proof_of_OS_MemClr_entail_wit_1 : OS_MemClr_entail_wit_1.
Proof.
  unfold OS_MemClr_entail_wit_1.
  right; intros.
  apply mem_clr_pre_to_loop_state.
Qed.

Lemma proof_of_OS_MemClr_entail_wit_2 : OS_MemClr_entail_wit_2.
Proof.
  unfold OS_MemClr_entail_wit_2.
  right; intros.
  change (sizeof(UCHAR)) with 1.
  rewrite Z.mul_1_r.
  apply mem_clr_loop_state_merge_zero_byte; lia.
Qed.

Lemma proof_of_OS_MemClr_return_wit_1 : OS_MemClr_return_wit_1.
Proof.
  unfold OS_MemClr_return_wit_1.
  left; intros size_pre pdest_pre pdest size Hexit Hsize Hbound
    Hsize_pre Hpdest Haddress Hcursor.
  assert (size = 0) by lia.
  subst size.
  apply mem_clr_loop_state_to_post.
Qed.

Lemma proof_of_OS_MemClr_which_implies_wit_1 : OS_MemClr_which_implies_wit_1.
Proof.
  unfold OS_MemClr_which_implies_wit_1.
  left; intros size_pre pdest_pre size pdest Hsize Hbound Hsize_pre
    Hpdest Haddress Hcursor.
  subst pdest.
  change (sizeof(UCHAR)) with 1 in *.
  repeat rewrite Z.mul_1_r in *.
  sep_apply (mem_clr_loop_state_split_byte pdest_pre size_pre size ltac:(lia)).
  entailer!.
Qed.
