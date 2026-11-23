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
From Ucos2Verify.VC.code.event Require Import init_event_list_named_goal.
From Ucos2Verify.VC.code.event Require Import init_event_list_named_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.VC.code.event.spec.init_event_list_names_spec.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OS_InitEventList_entail_wit_1 : OS_InitEventList_entail_wit_1.
Proof.
  right; intros.

  pose proof (init_event_list_named_profile_names sg ltac:(assumption)) as Hnames.
  assert (Hsize : event_object_size (osKernelConfig sg) = 24) by
    (unfold event_object_size; rewrite Hnames; reflexivity).
  assert (Hmax : osMaxEvents sg = 10) by assumption.
  assert (Htbl : g_OSEventTbl sg = &("OSEventTbl")) by assumption.
  assert (Hctype : sizeof("os_event") = 24) by lia.

  unfold init_event_list_named_loop_state, init_event_list_named_prefix.
  change (SumLib.ZRange.Zrange 0 0) with (@nil Z); cbn [map].
  change (iter_sepcon (@nil Assertion)) with emp.
  unfold event_pool_addr; rewrite Hsize, Hmax, <- Htbl, Hctype.
  replace (g_OSEventTbl sg + 0 * 24) with (g_OSEventTbl sg) by lia.
  entailer!.
Qed. 

Lemma proof_of_OS_InitEventList_entail_wit_2 : OS_InitEventList_entail_wit_2.
Proof.
  right; intros.

  pose proof (init_event_list_named_profile_names sg ltac:(assumption)) as Hnames.
  assert (Hsize : event_object_size (osKernelConfig sg) = 24) by
    (unfold event_object_size; rewrite Hnames; reflexivity).
  assert (Hmax : osMaxEvents sg = 10) by assumption.
  assert (Htbl : g_OSEventTbl sg = &("OSEventTbl")) by assumption.
  assert (Hctype : sizeof("os_event") = 24) by lia.

  rewrite <- Htbl, Hctype.
  replace (g_OSEventTbl sg + ix * 24) with (event_pool_addr sg ix) by
    (unfold event_pool_addr; rewrite Hsize; lia).

  replace (g_OSEventTbl sg + (ix + 1) * 24) with (event_pool_addr sg (ix + 1)) by
    (unfold event_pool_addr; rewrite Hsize; lia).
  replace (LitMap "?" + 0 * sizeof(CHAR)) with (LitMap "?") by lia.

  destruct (init_event_list_named_table_layout_select sg ix ltac:(assumption)
    ltac:(unfold valid_event_id; lia)) as [Htype [Hptr Hname]].
  rewrite Htype, Hptr, Hname.

  pose proof (init_event_list_named_loop_merge_node sg (LitMap "?") ix Hnames ltac:(lia)) as Hmerge.
  rewrite Hmax, init_event_list_named_range_next in Hmerge by lia.
  cbn [Ucos2Verify.lib.event_pool.event_encode_pool_link Ucos2Verify.lib.event_pool.event_cell Ucos2Verify.lib.event_pool.event_field_offset] in Hmerge.
  rewrite Z.add_0_r in Hmerge.
  sep_apply Hmerge; entailer!.
Qed. 

Lemma proof_of_OS_InitEventList_entail_wit_4 : OS_InitEventList_entail_wit_4.
Proof.
  left; intros; assert (ix = 9) by lia; subst ix.

  pose proof (init_event_list_named_profile_names sg ltac:(assumption)) as Hnames.
  assert (Hsize : event_object_size (osKernelConfig sg) = 24) by
    (unfold event_object_size; rewrite Hnames; reflexivity).
  assert (Hmax : osMaxEvents sg = 10) by assumption.
  assert (Htbl : g_OSEventTbl sg = &("OSEventTbl")) by assumption.
  assert (Hctype : sizeof("os_event") = 24) by lia.

  rewrite <- Htbl, Hctype.
  replace (g_OSEventTbl sg + 9 * 24) with (event_pool_addr sg 9) by
    (unfold event_pool_addr; rewrite Hsize; lia).

  assert (Hroot : g_OSEventFreeList sg = &("OSEventFreeList")) by assumption.
  replace (LitMap "?" + 0 * sizeof(CHAR)) with (LitMap "?") by lia.

  destruct (init_event_list_named_table_layout_select sg 9 ltac:(assumption)
    ltac:(unfold valid_event_id; lia)) as [Htype [Hptr Hname]].
  rewrite Htype, Hptr, Hname.

  sep_apply (GlobalStrings_merge LitMap "?").
  pose proof (init_event_list_named_loop_merge_node sg (LitMap "?") 9 Hnames ltac:(lia)) as Hmerge.
  rewrite Hmax in Hmerge.
  change (Ucos2Verify.lib.kernel_resources.kernel_list_next (SumLib.ZRange.Zrange 0 10) 9) with (@None Z) in Hmerge.
  cbn [Ucos2Verify.lib.event_pool.event_encode_pool_link Ucos2Verify.lib.event_pool.event_cell Ucos2Verify.lib.event_pool.event_field_offset] in Hmerge.
  rewrite Z.add_0_r in Hmerge.
  sep_apply Hmerge.
  unfold init_event_list_named_loop_state; rewrite Hsize, Hmax, Hroot.
  change (9 + 1) with 10.
  unfold mem_clr_post; change (repeat_Z 0 (24 * (10 - 10))) with (@nil Z).
  replace (24 * (10 - 10)) with 0 by lia.
  rewrite UCharArray.full_empty.
  Intros.
  sep_apply (store_ushort_undef_store_ushort (&("ix")) 9).
  sep_apply (store_ptr_undef_store_ptr (&("pevent1")) (event_pool_addr sg 9)).
  entailer!.
Qed. 

Lemma proof_of_OS_InitEventList_return_wit_1 : OS_InitEventList_return_wit_1.
Proof.
  right; intros.

  pose proof (init_event_list_named_profile_names sg ltac:(assumption)) as Hnames.
  assert (Hsize : event_object_size (osKernelConfig sg) = 24) by
    (unfold event_object_size; rewrite Hnames; reflexivity).
  assert (Hmax : osMaxEvents sg = 10) by assumption.
  assert (Htbl : g_OSEventTbl sg = &("OSEventTbl")) by assumption.
  assert (Hctype : sizeof("os_event") = 24) by lia.

  assert (Hroot : g_OSEventFreeList sg = &("OSEventFreeList")) by assumption.
  rewrite <- Htbl, <- Hroot.
  replace (g_OSEventTbl sg + 0 * sizeof("os_event")) with (event_pool_addr sg 0) by
    (unfold event_pool_addr; lia).
  rewrite <- Hmax.
  sep_apply (init_event_list_named_finish sg (LitMap "?") Hnames ltac:(lia)).
  entailer!.
Qed. 

Lemma proof_of_OS_InitEventList_which_implies_wit_1 : OS_InitEventList_which_implies_wit_1.
Proof.
  left; intros.

  pose proof (init_event_list_named_profile_names sg ltac:(assumption)) as Hnames.
  assert (Hsize : event_object_size (osKernelConfig sg) = 24) by
    (unfold event_object_size; rewrite Hnames; reflexivity).
  assert (Hmax : osMaxEvents sg = 10) by assumption.
  assert (Htbl : g_OSEventTbl sg = &("OSEventTbl")) by assumption.
  assert (Hctype : sizeof("os_event") = 24) by lia.

  unfold init_event_list_named_pre; rewrite Hsize, Hmax, <- Htbl, Hctype.
  replace (g_OSEventTbl sg + 0 * 24) with (g_OSEventTbl sg) by lia.
  entailer!.
Qed. 

Lemma proof_of_OS_InitEventList_which_implies_wit_2 : OS_InitEventList_which_implies_wit_2.
Proof.
  right; intros; subst pevent1.

  pose proof (init_event_list_named_profile_names sg ltac:(assumption)) as Hnames.
  assert (Hsize : event_object_size (osKernelConfig sg) = 24) by
    (unfold event_object_size; rewrite Hnames; reflexivity).
  assert (Hmax : osMaxEvents sg = 10) by assumption.
  assert (Htbl : g_OSEventTbl sg = &("OSEventTbl")) by assumption.
  assert (Hctype : sizeof("os_event") = 24) by lia.

  rewrite <- Htbl, Hctype.
  replace (g_OSEventTbl sg + ix * 24) with (event_pool_addr sg ix) by
    (unfold event_pool_addr; rewrite Hsize; lia).

  destruct (init_event_list_named_table_layout_select sg ix ltac:(assumption)
    ltac:(unfold valid_event_id; lia)) as [Htype [Hptr Hname]].
  rewrite Htype, Hptr, Hname.

  assert (Hmod : g_OSEventTbl sg mod 4 = 0).
  { rewrite <- Z.rem_mod_nonneg by lia; assumption. }
  pose proof (init_event_list_named_loop_split_node sg (LitMap "?") ix Hnames
    ltac:(lia) ltac:(lia) ltac:(change UINT_MAX with 4294967295 in *; lia) Hmod) as Hsplit.
  cbn [Ucos2Verify.lib.event_pool.event_cell Ucos2Verify.lib.event_pool.event_field_offset] in Hsplit.
  rewrite Z.add_0_r in Hsplit.
  exact Hsplit.
Qed. 

Lemma proof_of_OS_InitEventList_which_implies_wit_3 : OS_InitEventList_which_implies_wit_3.
Proof.
  right; intros; assert (ix = 9) by lia; subst ix; subst pevent1.

  pose proof (init_event_list_named_profile_names sg ltac:(assumption)) as Hnames.
  assert (Hsize : event_object_size (osKernelConfig sg) = 24) by
    (unfold event_object_size; rewrite Hnames; reflexivity).
  assert (Hmax : osMaxEvents sg = 10) by assumption.
  assert (Htbl : g_OSEventTbl sg = &("OSEventTbl")) by assumption.
  assert (Hctype : sizeof("os_event") = 24) by lia.

  rewrite <- Htbl, Hctype.
  replace (g_OSEventTbl sg + 9 * 24) with (event_pool_addr sg 9) by
    (unfold event_pool_addr; rewrite Hsize; lia).

  destruct (init_event_list_named_table_layout_select sg 9 ltac:(assumption)
    ltac:(unfold valid_event_id; lia)) as [Htype [Hptr Hname]].
  rewrite Htype, Hptr, Hname.

  assert (Hmod : g_OSEventTbl sg mod 4 = 0).
  { rewrite <- Z.rem_mod_nonneg by lia; assumption. }
  pose proof (init_event_list_named_loop_split_node sg (LitMap "?") 9 Hnames
    ltac:(lia) ltac:(lia) ltac:(change UINT_MAX with 4294967295 in *; lia) Hmod) as Hsplit.
  cbn [Ucos2Verify.lib.event_pool.event_cell Ucos2Verify.lib.event_pool.event_field_offset] in Hsplit.
  rewrite Z.add_0_r in Hsplit.
  exact Hsplit.
Qed. 
