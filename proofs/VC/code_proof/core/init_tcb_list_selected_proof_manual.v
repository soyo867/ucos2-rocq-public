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
From Ucos2Verify.VC.code.core Require Import init_tcb_list_selected_goal.
From Ucos2Verify.VC.code.core Require Import init_tcb_list_selected_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.VC.code.core.spec.init_tcb_list_selected_spec.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OS_InitTCBList_entail_wit_2 : OS_InitTCBList_entail_wit_2.
Proof.
  right; intros LitMap sg ix Hp Hg Hl Hlo Hhi Hguard Hp' Hg' Hl' Hlo' Hhi'.
  destruct Hg as [Hpool [Hprios [Hused Hfree]]].
  destruct Hl as [Hsize Hlayout].
  change (sizeof("os_tcb") = 64) in Hsize.
  rewrite Hpool, Hsize, Z.mul_0_l, Z.add_0_r.
  fold (Ucos2Verify.lib.task_storage.tcb64_addr sg ix) (Ucos2Verify.lib.task_storage.tcb64_addr sg (ix + 1)).
  assert (Hnext : Ucos2Verify.lib.task.encode_task_link sg (Some (ix + 1)) = Ucos2Verify.lib.task_storage.tcb64_addr sg (ix + 1)).
  { unfold Ucos2Verify.lib.task.encode_task_link.
    apply Ucos2Verify.lib.task_storage.task_slot_addr_tcb64.
    - apply init_tcb_list_profile_no_multi; exact Hp.
    - apply init_tcb_list_profile_no_profiling; exact Hp. }
  rewrite <- Hnext.
  unfold init_tcb_list_loop_residual, init_tcb_list_loop_state.
  pose proof (init_tcb_list_node_merge_next_name_updated__tcb_link_and_publication
    sg ix (Some (ix + 1)) (LitMap "?") Hp) as Hmerge.
  cbn [Ucos2Verify.lib.task_storage.tcb_cell Ucos2Verify.lib.task_storage.tcb_field_address] in Hmerge.
  sepcon_right_assoc.
  sep_apply_l_atomic Hmerge.
  unfold init_tcb_list_prefix.
  sep_apply_l_atomic (task_free_storage_range_extend__tcb_link_and_publication
    sg (Ucos2Verify.lib.task.task_boot_storage sg (LitMap "?") (SumLib.ZRange.Zrange 0 22)) 0 ix
    (Ucos2Verify.lib.task.tcb_init_free_image sg (Some (ix + 1)) (LitMap "?")) Hlo
    ltac:(rewrite task_boot_storage_range_lookup__tcb_link_and_publication by lia;
      rewrite Zrange_head__tcb_link_and_publication by lia; reflexivity)).
  entailer!.
Qed.

Lemma proof_of_OS_InitTCBList_entail_wit_4 : OS_InitTCBList_entail_wit_4.
Proof.
  right; intros LitMap sg ix Hp Hg Hl Hix Hguard Hp' Hg' Hl' Hlo Hhi.
  subst ix.
  destruct Hg as [Hpool [Hprios [Hused Hfree]]].
  destruct Hl as [Hsize Hlayout].
  change (sizeof("os_tcb") = 64) in Hsize.
  rewrite Hpool, Hsize, Z.mul_0_l, Z.add_0_r.
  fold (Ucos2Verify.lib.task_storage.tcb64_addr sg 21).
  unfold init_tcb_list_loop_residual, init_tcb_list_loop_state.
  pose proof (init_tcb_list_node_merge_next_name_updated__tcb_link_and_publication
    sg 21 None (LitMap "?") Hp) as Hmerge.
  cbn [Ucos2Verify.lib.task_storage.tcb_cell Ucos2Verify.lib.task_storage.tcb_field_address Ucos2Verify.lib.task.encode_task_link] in Hmerge.
  sepcon_right_assoc.
  sep_apply_l_atomic Hmerge.
  unfold init_tcb_list_prefix.
  sep_apply_l_atomic (task_free_storage_range_extend__tcb_link_and_publication
    sg (Ucos2Verify.lib.task.task_boot_storage sg (LitMap "?") (SumLib.ZRange.Zrange 0 22)) 0 21
    (Ucos2Verify.lib.task.tcb_init_free_image sg None (LitMap "?")) ltac:(lia)
    ltac:(rewrite task_boot_storage_range_lookup__tcb_link_and_publication by lia; reflexivity)).
  entailer!.
Qed.

Lemma proof_of_OS_InitTCBList_return_wit_1 : OS_InitTCBList_return_wit_1.
Proof.
  right; intros LitMap sg Hp Hg Hl Hp' Hg' Hl'.
  destruct Hg as [Hpool [Hprios [Hused Hfree]]].
  unfold init_tcb_list_post, init_tcb_list_prefix.
  rewrite Hpool, Hused, Hfree, Z.mul_0_l, Z.add_0_r.
  entailer!.
Qed.

Lemma proof_of_OS_InitTCBList_which_implies_wit_1 : OS_InitTCBList_which_implies_wit_1.
Proof.
  right; intros sg Hprofile Hglobals Hlayout.
  destruct Hglobals as [Hpool [Hprios [Hused Hfree]]].
  destruct Hlayout as [Hsize [Hpoollo [Hpoolhi [Halign
    [Hpriolo [Hpriohi [Hprioalign Hfields]]]]]]].
  change (sizeof(PTR)) with 4.
  change (sizeof(UCHAR)) with 1.
  change (sizeof("os_tcb")) with (sizeof_alias_type "os_tcb").
  rewrite Hsize, Hpool, Hprios.
  unfold init_tcb_list_pre, init_tcb_list_roots.
  replace (g_OSTCBTbl sg + 0 * 64) with (g_OSTCBTbl sg) by lia.
  replace (g_OSTCBPrioTbl sg + 0 * 4) with (g_OSTCBPrioTbl sg) by lia.
  entailer!; change UINT_MAX with 4294967295; lia.
Qed.

Lemma proof_of_OS_InitTCBList_which_implies_wit_2 : OS_InitTCBList_which_implies_wit_2.
Proof.
  right; intros LitMap sg Hprofile Hglobals Hlayout.
  destruct Hglobals as [Hpool [Hprios [Hused Hfree]]].
  pose proof Hlayout as Hlayout_facts.
  destruct Hlayout_facts as [Hsize [Hpoollo [Hpoolhi [Halign
    [Hpriolo [Hpriohi [Hprioalign Hfields]]]]]]].
  change (sizeof(PTR)) with 4.
  change (sizeof("os_tcb")) with (sizeof_alias_type "os_tcb").
  rewrite Hsize, Hpool, Hprios.
  replace (g_OSTCBTbl sg + 0 * 64) with (g_OSTCBTbl sg) by lia.
  replace (g_OSTCBPrioTbl sg + 0 * 4) with (g_OSTCBPrioTbl sg) by lia.
  change (64 * 22) with 1408.
  change (4 * 64) with 256.
  unfold mem_clr_post.
  pose proof (zero_bytes_to_task_free_storage__tcb_zero_byte_reconstruction sg 22%nat 0 Hprofile Hlayout
    ltac:(lia) ltac:(lia)) as Hpool_rep.
  replace (Ucos2Verify.lib.task_storage.tcb64_addr sg 0) with (g_OSTCBTbl sg) in Hpool_rep
    by (unfold Ucos2Verify.lib.task_storage.tcb64_addr; lia).
  sep_apply Hpool_rep.
  sep_apply (zero_bytes_to_ptr_array__tcb_zero_byte_reconstruction 64%nat (g_OSTCBPrioTbl sg) Hprioalign).
  unfold init_tcb_list_loop_state, init_tcb_list_priority_zero,
    init_tcb_list_prefix, init_tcb_list_zero_suffix, Ucos2Verify.lib.task.store_prio_tbl.
  change (SumLib.ZRange.Zrange 0 0) with (@nil Z).
  cbn [Ucos2Verify.lib.task.task_free_storage_rep].
  change (map (fun p => Ucos2Verify.lib.task.prio_tbl_entry_to_addr sg PTFree) (SumLib.ZRange.Zrange 0 64))
    with (repeat 0 64%nat).
  change (Z.of_nat 64) with 64.
  change (SumLib.ZRange.Zrange 0 22) with (SumLib.ZRange.Zrange_aux 0 22%nat).
  entailer!.
Qed.

Lemma proof_of_OS_InitTCBList_which_implies_wit_3 : OS_InitTCBList_which_implies_wit_3.
Proof.
  right; intros LitMap sg ix ix_next ptcb1 ptcb2 Hp Hg Hl Hlo Hhi Hix Hp1 Hp2.
  destruct Hg as [Hpool [Hprios [Hused Hfree]]].
  destruct Hl as [Hsize Hlayout].
  change (sizeof("os_tcb") = 64) in Hsize.
  subst ptcb1; rewrite Hpool, Hsize.
  fold (Ucos2Verify.lib.task_storage.tcb64_addr sg ix).
  unfold init_tcb_list_loop_state, init_tcb_list_loop_residual.
  sep_apply_l_atomic (init_tcb_list_zero_suffix_split_next_name__tcb_link_and_publication
    sg ix Hp ltac:(lia)).
  cbn [Ucos2Verify.lib.task_storage.tcb_cell Ucos2Verify.lib.task_storage.tcb_field_address].
  entailer!.
Qed.

Lemma proof_of_OS_InitTCBList_which_implies_wit_4 : OS_InitTCBList_which_implies_wit_4.
Proof.
  right; intros LitMap sg ix ptcb1 Hp Hg Hl Hlo Hhi Hp1.
  destruct Hg as [Hpool [Hprios [Hused Hfree]]].
  destruct Hl as [Hsize Hlayout].
  change (sizeof("os_tcb") = 64) in Hsize.
  subst ptcb1; rewrite Hpool, Hsize.
  fold (Ucos2Verify.lib.task_storage.tcb64_addr sg ix).
  unfold init_tcb_list_loop_state, init_tcb_list_loop_residual.
  sep_apply_l_atomic (init_tcb_list_zero_suffix_split_next_name__tcb_link_and_publication
    sg ix Hp ltac:(lia)).
  cbn [Ucos2Verify.lib.task_storage.tcb_cell Ucos2Verify.lib.task_storage.tcb_field_address].
  entailer!.
Qed.

Lemma proof_of_OS_InitTCBList_which_implies_wit_5 : OS_InitTCBList_which_implies_wit_5.
Proof.
  left; intros LitMap sg Hp Hg Hl.
  destruct Hg as [Hpool [Hprios [Hused Hfree]]].
  unfold init_tcb_list_loop_state, init_tcb_list_roots,
    init_tcb_list_zero_suffix.
  change (SumLib.ZRange.Zrange 22 22) with (@nil Z).
  cbn [Ucos2Verify.lib.task.task_free_storage_rep].
  rewrite Hused, Hfree.
  entailer!.
  unfold init_tcb_list_global_addresses; auto.
Qed.

