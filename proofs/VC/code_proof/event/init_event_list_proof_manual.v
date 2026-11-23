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
From Ucos2Verify.VC.code.event Require Import init_event_list_goal.
From Ucos2Verify.VC.code.event Require Import init_event_list_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.VC.code.event.spec.init_event_list_spec.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OS_InitEventList_entail_wit_1 : OS_InitEventList_entail_wit_1.
Proof.
  right; intros.
  unfold init_event_list_loop_state, init_event_list_prefix.
  rewrite !init_event_list_pool_addr_eq by assumption.
  change (SumLib.ZRange.Zrange 0 0) with (@nil Z); cbn [map].
  change (iter_sepcon (@nil Assertion)) with emp.
  rewrite <- PreH1, PreH2.
  replace (g_OSEventTbl sg + 0 * sizeof("os_event")) with (g_OSEventTbl sg) by lia.
  replace (g_OSEventTbl sg + 0 * 20) with (g_OSEventTbl sg) by lia.
  entailer!.
Qed. 

Lemma proof_of_OS_InitEventList_entail_wit_2 : OS_InitEventList_entail_wit_2.
Proof.
  right; intros.
  rewrite <- PreH2, PreH4.
  replace (g_OSEventTbl sg + ix * 20) with (event_addr sg ix) by
    (unfold event_addr; rewrite init_event_list_pool_addr_eq by assumption; reflexivity).
  replace (g_OSEventTbl sg + (ix + 1) * 20) with (event_pool_addr sg (ix + 1)) by
    (rewrite init_event_list_pool_addr_eq by assumption; reflexivity).
  destruct (event_table_layout_select sg ix PreH8
    ltac:(unfold valid_event_id; lia)) as [[Htype [Hptr Hcnt]] Hwait].
  rewrite Htype, Hptr.
  unfold init_event_list_loop_residual, init_event_list_loop_state.
  pose proof (event_storage_merge_boot_type_ptr__event_boot_storage sg ix) as Hmerge.
  rewrite PreH1, kernel_list_next_event_range_eq__event_boot_storage in Hmerge by lia.
  cbn [Ucos2Verify.lib.event_pool.event_encode_pool_link Ucos2Verify.lib.event_pool.event_cell Ucos2Verify.lib.event_pool.event_field_offset] in Hmerge.
  sep_apply Hmerge.
  pose proof (init_event_list_prefix_merge_node__event_boot_storage sg ix ltac:(lia)) as Hprefix.
  rewrite PreH1 in Hprefix; sep_apply Hprefix.
  replace (20 * (10 - (ix + 1))) with (20 * (9 - ix)) by lia.
  entailer!.
Qed. 

Lemma proof_of_OS_InitEventList_entail_wit_4 : OS_InitEventList_entail_wit_4.
Proof.
  left; intros; subst ix.
  rewrite <- PreH2, PreH4.
  replace (g_OSEventTbl sg + 9 * 20) with (event_addr sg 9) by
    (unfold event_addr; rewrite init_event_list_pool_addr_eq by assumption; reflexivity).
  destruct (event_table_layout_select sg 9 PreH8
    ltac:(unfold valid_event_id; lia)) as [[Htype [Hptr Hcnt]] Hwait].
  rewrite Htype, Hptr.
  unfold init_event_list_loop_residual.
  rewrite <- PreH3; entailer!.
  pose proof (event_storage_merge_boot_type_ptr__event_boot_storage sg 9) as Hmerge.
  rewrite PreH1 in Hmerge.
  change (Ucos2Verify.lib.kernel_resources.kernel_list_next (SumLib.ZRange.Zrange 0 10) 9) with (@None Z) in Hmerge.
  cbn [Ucos2Verify.lib.event_pool.event_encode_pool_link Ucos2Verify.lib.event_pool.event_cell Ucos2Verify.lib.event_pool.event_field_offset] in Hmerge.
  rewrite event_addr_shared_pool_binding.
  unfold OSEventType_off, OSEventPtr_off.
  sep_apply Hmerge.
  pose proof (init_event_list_prefix_merge_node__event_boot_storage sg 9 ltac:(lia)) as Hprefix.
  rewrite PreH1 in Hprefix; sep_apply Hprefix.
  unfold mem_clr_post; change (repeat_Z 0 (20 * (9 - 9))) with (@nil Z).
  rewrite UCharArray.full_empty.
  Intros.
  sep_apply (store_ushort_undef_store_ushort (&("ix")) 9).
  sep_apply (store_ptr_undef_store_ptr (&("pevent1")) (event_pool_addr sg 9)).
  entailer!.
Qed. 

Lemma proof_of_OS_InitEventList_return_wit_1 : OS_InitEventList_return_wit_1.
Proof.
  right; intros.
  unfold init_event_list_post.
  pose proof (init_event_list_initial_valid sg) as Hvalid.
  entailer!.
  pose proof (init_event_list_prefix_implies_free_storage__event_boot_storage sg PreH9) as Hfree.
  rewrite PreH1 in Hfree; sep_apply Hfree.
  unfold Ucos2Verify.lib.event_pool.event_free_root_rep; cbn [Ucos2Verify.lib.event_pool.event_pool_initial Ucos2Verify.lib.ucos2_verify_state_def.EventStateDef.unUsedEventStates].
  rewrite PreH1.
  change (hd_error (SumLib.ZRange.Zrange 0 10)) with (Some 0).
  cbn [Ucos2Verify.lib.event_pool.event_encode_pool_link].
  rewrite !init_event_list_pool_addr_eq by assumption.
  rewrite <- PreH2, <- PreH3.
  replace (g_OSEventTbl sg + 0 * sizeof("os_event")) with (g_OSEventTbl sg) by lia.
  replace (g_OSEventTbl sg + 0 * 20) with (g_OSEventTbl sg) by lia.
  entailer!.
Qed. 

Lemma proof_of_OS_InitEventList_which_implies_wit_1 : OS_InitEventList_which_implies_wit_1.
Proof.
  left; intros; unfold init_event_list_pre.
  rewrite <- PreH1, PreH2.
  replace (g_OSEventTbl sg + 0 * sizeof("os_event")) with (g_OSEventTbl sg) by lia.
  entailer!.
Qed. 

Lemma proof_of_OS_InitEventList_which_implies_wit_2 : OS_InitEventList_which_implies_wit_2.
Proof.
  right; intros; subst pevent1.
  rewrite <- PreH2, PreH4.
  replace (g_OSEventTbl sg + ix * 20) with (event_addr sg ix) by
    (unfold event_addr; rewrite init_event_list_pool_addr_eq by assumption; reflexivity).
  destruct (event_table_layout_select sg ix PreH8
    ltac:(unfold valid_event_id; lia)) as [[Htype [Hptr Hcnt]] Hwait].
  rewrite Htype, Hptr.
  rewrite Z.rem_mod_nonneg in PreH7 by lia.
  apply (init_event_list_loop_split_zero_node__event_boot_storage sg ix PreH9);
    change UINT_MAX with 4294967295 in *; lia.
Qed. 

Lemma proof_of_OS_InitEventList_which_implies_wit_3 : OS_InitEventList_which_implies_wit_3.
Proof.
  right; intros.
  assert (ix = 9) by lia; subst ix; subst pevent1.
  rewrite <- PreH2, PreH4.
  replace (g_OSEventTbl sg + 9 * 20) with (event_addr sg 9) by
    (unfold event_addr; rewrite init_event_list_pool_addr_eq by assumption; reflexivity).
  destruct (event_table_layout_select sg 9 PreH8
    ltac:(unfold valid_event_id; lia)) as [[Htype [Hptr Hcnt]] Hwait].
  rewrite Htype, Hptr.
  rewrite Z.rem_mod_nonneg in PreH7 by lia.
  apply (init_event_list_loop_split_zero_node__event_boot_storage sg 9 PreH9);
    change UINT_MAX with 4294967295 in *; lia.
Qed.
