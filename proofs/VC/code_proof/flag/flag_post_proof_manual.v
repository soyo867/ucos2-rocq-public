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
From Ucos2Verify.VC.code.flag Require Import flag_post_goal.
From Ucos2Verify.VC.code.flag Require Import flag_post_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import SimpleC.SL.Mem SimpleC.SL.SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt Ucos2Verify.lib.flag Ucos2Verify.lib.flag_node_fields Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_fields_spec Ucos2Verify.VC.code.flag.spec.flag_post_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec Ucos2Verify.VC.code.sched.spec.sched_fields_disabled_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope sac.

Lemma proof_of_OSFlagPost_entail_wit_1 : OSFlagPost_entail_wit_1.
Proof.
  left; intros.
  subst perr_pre opt_pre flags_pre pgrp_pre.
  assert (Hpointer : pointer = 0) by lia.
  subst pointer.
  pose proof (flag_post_api_null_return environment critical sg id requested option_word
    mask original before X PreH4) as Hsafe.
  unfold flag_post_public_post.
  Exists original before local 110.
  sep_apply store_uint_undef_store_uint.
  entailer!.
  apply flag_post_same_execution_refl.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_2 : OSFlagPost_entail_wit_2.
Proof.
  left; intros.
  subst perr_pre opt_pre flags_pre.
  assert (Htype_bad : flagImageType image <> 5).
  { intro Htype; rewrite Htype in PreH1; change (5 <> 5) in PreH1; contradiction. }
  pose proof (flag_post_api_type_return environment critical sg pointer id requested option_word
    mask original before image X PreH4 PreH6 Htype_bad PreH10) as Hsafe.
  pose proof PreH2 as (Hcfg & Hpointer & Hr & Ho & Hu & Hstack & Htype & Hflags & Hnode & Hwait).
  destruct Hpointer as [Hz | Hp]; [contradiction |].
  assert (Henabled : cfgFlagEnabled (osKernelConfig sg) = true) by (rewrite Hcfg; reflexivity).
  unfold flag_post_public_post.
  Exists original before local 1.
  sep_apply store_uint_undef_store_uint.
  unfold flag_post_source_closed, flag_post_closed,
    kernel_continuation_world_spec.kernel_continuation_inv,
    kernel_program_fields_inv, kernel_program_fields_rep,
    UCOS2_fields_raw_rep, flag_fields_configured_rep,
    flag_post_type_frame, flag_post_group_frame, flag_post_execution_frame.
  rewrite Hp in *; rewrite Henabled, Htype.
  destruct PreH5 as (Hinv & Hcoverage & Hobservation).
  rewrite (flag_fields_raw_rep_split_group sg (FlagState before) id image PreH6).
  unfold flag_group_rep.
  pose proof (flag_post_same_execution_refl original).
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_3 : OSFlagPost_entail_wit_3.
Proof.
  left; intros.
  subst perr_pre opt_pre flags_pre.
  sep_apply_l_atomic (flag_post_save_output_protected_cut environment critical local sg original mask before
    (flag_post_caller_frame error_cell old_error F) captured retval pointer id requested option_word
    PreH1 PreH6 PreH2).
  Intros entry.
  Exists entry.
  unfold flag_post_caller_frame.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_4_1 : OSFlagPost_entail_wit_4_1.
Proof.
  unfold OSFlagPost_entail_wit_4_1; left; intros.
  pose proof PreH4 as [Hcfg [Hp [Hr [Ho [Hu [Hs [Htype Hfields]]]]]]].
  pose proof PreH5 as [[Hnonnull Hprefix] [Hinv [Hcoverage Hobs]]].
  assert (Hptr : pointer = flag_pool_addr sg id) by (destruct Hp; congruence).
  assert (Haddr : &(pointer # "os_flag_grp" ->ₛ "OSFlagType") = flag_pool_addr sg id) by (rewrite Htype; exact Hptr).
  assert (Hoption : option_word = 1).
  { unfold unsigned_last_nbits in PreH2.
    rewrite Z.mod_small in PreH2; [exact PreH2|].
    change (0 <= option_word < 4294967296); lia. }
  assert (Htype_ne : flagImageType image <> 5).
  { intro Heq; rewrite Heq in PreH1; vm_compute in PreH1; contradiction. }
  assert (Hrun : flag_post_protected_program sg id requested option_word
    (flag_post_acquired entry_2) (FlagPostProtectedRejected 1) (flag_post_acquired entry_2)).
  { unfold flag_post_protected_program; exists image; split; [exact PreH6|].
    rewrite Hoption; unfold flag_post_valid_option; cbn [Z.eqb Pos.eqb].
    rewrite (proj2 (Z.eqb_neq (flagImageType image) 5) Htype_ne); cbn; auto. }
  Exists entry_2 (flag_post_acquired entry_2) (flag_post_local entry_2) (FlagPostProtectedRejected 1).
  unfold flag_post_exit_cut, flag_post_result_error, flag_post_protected_error.
  unfold flag_post_source_masked, flag_post_masked,
    kernel_continuation_world_spec.kernel_continuation_inv,
    kernel_program_fields_inv, kernel_program_fields_rep,
    UCOS2_fields_raw_rep, flag_fields_configured_rep.
  assert (Henabled : cfgFlagEnabled (osKernelConfig sg) = true) by (rewrite Hcfg; reflexivity).
  rewrite Henabled.
  rewrite (flag_fields_raw_rep_split_group sg (FlagState (flag_post_acquired entry_2)) id image PreH6).
  unfold flag_group_rep, flag_post_type_frame, flag_post_group_frame, flag_post_critical_frame.
  rewrite Haddr.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_4_2 : OSFlagPost_entail_wit_4_2.
Proof.
  unfold OSFlagPost_entail_wit_4_2; left; intros.
  pose proof PreH3 as [Hcfg [Hp [Hr [Ho [Hu [Hs [Htype Hfields]]]]]]].
  pose proof PreH4 as [[Hnonnull Hprefix] [Hinv [Hcoverage Hobs]]].
  assert (Hptr : pointer = flag_pool_addr sg id) by (destruct Hp; congruence).
  assert (Haddr : &(pointer # "os_flag_grp" ->ₛ "OSFlagType") = flag_pool_addr sg id) by (rewrite Htype; exact Hptr).
  assert (Hoption : option_word = 0).
  { unfold unsigned_last_nbits in PreH2.
    rewrite Z.mod_small in PreH2; [exact PreH2|].
    change (0 <= option_word < 4294967296); lia. }
  assert (Htype_ne : flagImageType image <> 5).
  { intro Heq; rewrite Heq in PreH1; vm_compute in PreH1; contradiction. }
  assert (Hrun : flag_post_protected_program sg id requested option_word
    (flag_post_acquired entry_2) (FlagPostProtectedRejected 1) (flag_post_acquired entry_2)).
  { unfold flag_post_protected_program; exists image; split; [exact PreH5|].
    rewrite Hoption; unfold flag_post_valid_option; cbn [Z.eqb Pos.eqb].
    rewrite (proj2 (Z.eqb_neq (flagImageType image) 5) Htype_ne); cbn; auto. }
  Exists entry_2 (flag_post_acquired entry_2) (flag_post_local entry_2) (FlagPostProtectedRejected 1).
  unfold flag_post_exit_cut, flag_post_result_error, flag_post_protected_error.
  unfold flag_post_source_masked, flag_post_masked,
    kernel_continuation_world_spec.kernel_continuation_inv,
    kernel_program_fields_inv, kernel_program_fields_rep,
    UCOS2_fields_raw_rep, flag_fields_configured_rep.
  assert (Henabled : cfgFlagEnabled (osKernelConfig sg) = true) by (rewrite Hcfg; reflexivity).
  rewrite Henabled.
  rewrite (flag_fields_raw_rep_split_group sg (FlagState (flag_post_acquired entry_2)) id image PreH5).
  unfold flag_group_rep, flag_post_type_frame, flag_post_group_frame, flag_post_critical_frame.
  rewrite Haddr.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_5 : OSFlagPost_entail_wit_5.
Proof.
  unfold OSFlagPost_entail_wit_5; left; intros.
  pose proof (flag_post_error_restore_public_post environment critical sg pointer id requested option_word
    mask original before cpu_sr entry result released returned current returned_local 1 error_cell F X
    PreH3 PreH4 PreH12 PreH2 PreH11) as Hpost.
  sep_apply Hpost.
  sep_apply store_uint_undef_store_uint.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_8 : OSFlagPost_entail_wit_8.
Proof.
  unfold OSFlagPost_entail_wit_8; left; intros.
  pose proof (flag_post_error_restore_public_post environment critical sg pointer id requested option_word
    mask original before cpu_sr entry result released returned current returned_local 113 error_cell F X
    PreH3 PreH4 PreH12 PreH2 PreH11) as Hpost.
  sep_apply Hpost.
  sep_apply store_uint_undef_store_uint.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_1 : OSFlagPost_entail_wit_9_1.
Proof.
  left. intros.
  Exists entry_3 (flag_post_acquired entry_3) (flag_post_local entry_3)
    (FlagPostProtectedRejected 113).
  unfold flag_post_exit_cut.
  entailer!.
  - destruct PreH1 as [Hcfg [Hpointer [Hrequested [Hoption
      [Hlayout_unlink [Hlayout_stack Hlayout_flag]]]]]].
    assert (Hnonnull : pointer <> 0) by exact (proj1 (proj1 PreH2)).
    destruct Hpointer as [Hzero | Hpointer]; [contradiction |].
    destruct Hlayout_flag as [_ [Hflags_address _]].
    rewrite (Hflags_address pointer), Hpointer.
    pose proof (proj1 (proj2 PreH2)) as Hstate_inv.
    pose proof (proj1 (proj2 (proj2 PreH2))) as Hlive_coverage.
    pose proof (proj2 (proj2 (proj2 PreH2))) as Hsource_observation.
    assert (Hmerge :
      (flag_pool_addr sg id + 8) # UShort |-> flagImageBits image_2 **
      flag_post_current_word_frame sg (flag_post_acquired entry_3) id image_2
      |-- kernel_program_fields_inv sg (flag_post_acquired entry_3)).
    { rewrite (flag_post_current_word_resources sg (flag_post_acquired entry_3)
        id image_2 Hcfg PreH3).
      entailer!. }
    unfold flag_post_source_masked, flag_post_masked, flag_post_critical_frame,
      kernel_continuation_world_spec.kernel_continuation_inv.
    sep_apply_l_atomic Hmerge.
    entailer!.
  - assert (Hinvalid : flag_post_valid_option option_word = false).
    { unfold flag_post_valid_option.
      apply Bool.orb_false_iff; split; apply Z.eqb_neq; lia. }
    exists image_2. split; [exact PreH3 |].
    rewrite Hinvalid. cbn [andb].
    rewrite (flag_post_bits_invalid_option _ _ _ _ Hinvalid).
    auto.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_2 : OSFlagPost_entail_wit_9_2.
Proof. exact proof_of_OSFlagPost_entail_wit_9_1. Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_3 : OSFlagPost_entail_wit_9_3.
Proof. exact proof_of_OSFlagPost_entail_wit_9_1. Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_4 : OSFlagPost_entail_wit_9_4.
Proof. exact proof_of_OSFlagPost_entail_wit_9_1. Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_5 : OSFlagPost_entail_wit_9_5.
Proof. exact proof_of_OSFlagPost_entail_wit_9_1. Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_6 : OSFlagPost_entail_wit_9_6.
Proof. exact proof_of_OSFlagPost_entail_wit_9_1. Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_7 : OSFlagPost_entail_wit_9_7.
Proof. exact proof_of_OSFlagPost_entail_wit_9_1. Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_8 : OSFlagPost_entail_wit_9_8.
Proof. exact proof_of_OSFlagPost_entail_wit_9_1. Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_9 : OSFlagPost_entail_wit_9_9.
Proof. exact proof_of_OSFlagPost_entail_wit_9_1. Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_10 : OSFlagPost_entail_wit_9_10.
Proof.
  left; intros.
  destruct PreH1 as (_ & _ & _ & Hoption & _).
  rewrite (unsigned_last_nbits_eq option_word 32) in PreH6 by (cbn; lia).
  exfalso; apply PreH19; lia.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_11 : OSFlagPost_entail_wit_9_11.
Proof.
  left; intros.
  destruct PreH1 as (_ & _ & _ & Hoption & _).
  rewrite (unsigned_last_nbits_eq option_word 32) in PreH6 by (cbn; lia).
  exfalso; apply PreH19; lia.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_12 : OSFlagPost_entail_wit_9_12.
Proof.
  left; intros.
  destruct PreH1 as (_ & _ & _ & Hoption & _).
  rewrite (unsigned_last_nbits_eq option_word 32) in PreH6 by (cbn; lia).
  exfalso; apply PreH19; lia.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_13 : OSFlagPost_entail_wit_9_13.
Proof.
  left; intros.
  destruct PreH1 as (_ & _ & _ & Hoption & _).
  rewrite (unsigned_last_nbits_eq option_word 32) in PreH6 by (cbn; lia).
  exfalso; apply PreH19; lia.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_14 : OSFlagPost_entail_wit_9_14.
Proof.
  left; intros.
  destruct PreH1 as (_ & _ & _ & Hoption & _).
  rewrite (unsigned_last_nbits_eq option_word 32) in PreH6 by (cbn; lia).
  exfalso; apply PreH19; lia.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_15 : OSFlagPost_entail_wit_9_15.
Proof.
  left; intros.
  destruct PreH1 as (_ & _ & _ & Hoption & _).
  rewrite (unsigned_last_nbits_eq option_word 32) in PreH6 by (cbn; lia).
  exfalso; apply PreH19; lia.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_16 : OSFlagPost_entail_wit_9_16.
Proof.
  left; intros.
  destruct PreH1 as (_ & _ & _ & Hoption & _).
  rewrite (unsigned_last_nbits_eq option_word 32) in PreH6 by (cbn; lia).
  exfalso; apply PreH19; lia.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_17 : OSFlagPost_entail_wit_9_17.
Proof.
  left; intros.
  destruct PreH1 as (_ & _ & _ & Hoption & _).
  rewrite (unsigned_last_nbits_eq option_word 32) in PreH6 by (cbn; lia).
  exfalso; apply PreH19; lia.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_18 : OSFlagPost_entail_wit_9_18.
Proof.
  left; intros.
  destruct PreH1 as (_ & _ & _ & Hoption & _).
  rewrite (unsigned_last_nbits_eq option_word 32) in PreH6 by (cbn; lia).
  exfalso; apply PreH19; lia.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_19 : OSFlagPost_entail_wit_9_19.
Proof.
  left. intros.
  unfold flag_post_parameters in PreH1.
  destruct PreH1 as [_ [_ [_ [Hoption _]]]].
  rewrite IntLib.unsigned_last_nbits_eq in PreH6 by
    (change (0 <= option_word < 4294967296); lia).
  lia.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_20 : OSFlagPost_entail_wit_9_20.
Proof.
  left. intros.
  unfold flag_post_parameters in PreH1.
  destruct PreH1 as [_ [_ [_ [Hoption _]]]].
  rewrite IntLib.unsigned_last_nbits_eq in PreH6 by
    (change (0 <= option_word < 4294967296); lia).
  lia.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_21 : OSFlagPost_entail_wit_9_21.
Proof.
  left. intros.
  unfold flag_post_parameters in PreH1.
  destruct PreH1 as [_ [_ [_ [Hoption _]]]].
  rewrite IntLib.unsigned_last_nbits_eq in PreH6 by
    (change (0 <= option_word < 4294967296); lia).
  lia.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_22 : OSFlagPost_entail_wit_9_22.
Proof.
  left. intros.
  unfold flag_post_parameters in PreH1.
  destruct PreH1 as [_ [_ [_ [Hoption _]]]].
  rewrite IntLib.unsigned_last_nbits_eq in PreH6 by
    (change (0 <= option_word < 4294967296); lia).
  lia.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_23 : OSFlagPost_entail_wit_9_23.
Proof.
  left. intros.
  unfold flag_post_parameters in PreH1.
  destruct PreH1 as [_ [_ [_ [Hoption _]]]].
  rewrite IntLib.unsigned_last_nbits_eq in PreH6 by
    (change (0 <= option_word < 4294967296); lia).
  lia.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_24 : OSFlagPost_entail_wit_9_24.
Proof.
  left. intros.
  unfold flag_post_parameters in PreH1.
  destruct PreH1 as [_ [_ [_ [Hoption _]]]].
  rewrite IntLib.unsigned_last_nbits_eq in PreH6 by
    (change (0 <= option_word < 4294967296); lia).
  lia.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_25 : OSFlagPost_entail_wit_9_25.
Proof.
  left. intros.
  unfold flag_post_parameters in PreH1.
  destruct PreH1 as [_ [_ [_ [Hoption _]]]].
  rewrite IntLib.unsigned_last_nbits_eq in PreH6 by
    (change (0 <= option_word < 4294967296); lia).
  lia.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_26 : OSFlagPost_entail_wit_9_26.
Proof.
  left. intros.
  unfold flag_post_parameters in PreH1.
  destruct PreH1 as [_ [_ [_ [Hoption _]]]].
  rewrite IntLib.unsigned_last_nbits_eq in PreH6 by
    (change (0 <= option_word < 4294967296); lia).
  lia.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_9_27 : OSFlagPost_entail_wit_9_27.
Proof.
  left. intros.
  unfold flag_post_parameters in PreH1.
  destruct PreH1 as [_ [_ [_ [Hoption _]]]].
  rewrite IntLib.unsigned_last_nbits_eq in PreH6 by
    (change (0 <= option_word < 4294967296); lia).
  lia.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_1 : OSFlagPost_entail_wit_10_1.
Proof.
 left; intros; subst option_word; discriminate PreH6. Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_2 : OSFlagPost_entail_wit_10_2.
Proof.
 left; intros; subst option_word; discriminate PreH6. Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_3 : OSFlagPost_entail_wit_10_3.
Proof.
 left; intros; subst option_word; discriminate PreH6. Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_4 : OSFlagPost_entail_wit_10_4.
Proof.
  left; intros; subst option_word.
  pose proof PreH1 as [Hcfg [Hpointer [Hrequested [Hoption [Hunlink [Htcb Hlayout]]]]]].
  pose proof PreH2 as [Hprefix [Hvalid [Hcoverage Hsource]]].
  assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true)
    by (rewrite Hcfg; reflexivity).
  assert (Hflags : valid_flag_state sg (flag_post_acquired entry_2).(FlagState)).
  { destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ [Hflags _]]]]]]]].
    unfold valid_flag_configuration in Hflags; rewrite Henabled in Hflags; exact Hflags. }
  assert (Htype : image_2.(flagImageType) = 5) by (apply PreH4; reflexivity).
  destruct (flag_image_type_used_group__word_update_first sg _ id image_2
    Hflags PreH3 Htype) as [group Hgroup].
  set (posted := Z.land image_2.(flagImageBits) (unsigned_last_nbits (Z.lnot requested) 16)).
  assert (Hposted : flag_post_bits sg.(osKernelConfig) image_2.(flagImageBits) requested 0 = Some posted)
    by (rewrite Hcfg; apply flag_post_clear_word_16__word_update_first).
  assert (Hbits : flag_word_in_range sg.(osKernelConfig) posted).
  { eapply flag_post_bits_in_range; [rewrite Hcfg; cbn; lia|exact Hposted]. }
  pose proof (flag_replace_bits_preserves_current_valid__word_update_first sg
    (flag_post_entered entry_2) (flag_post_acquired entry_2) id group image_2 posted
    Hcfg (proj2 PreH2) Hgroup PreH3 Hbits) as Hcurrent.
  set (context := {| flag_post_loop_entry := entry_2;
    flag_post_posted_word := posted;
    flag_post_initial_order := flagWaitOrder group;
    flag_post_visited := nil;
    flag_post_remaining := flagWaitOrder group;
    flag_post_accumulator := flag_post_scan_initial
      (replace_FlagS (flag_replace_bits (FlagState (flag_post_acquired entry_2))
        id group image_2 posted) (flag_post_acquired entry_2));
    flag_post_loop_local := flag_post_local entry_2 |}).
  assert (Hinitial : flag_post_initial_scan context) by reflexivity.
  assert (Hloop : flag_post_loop_facts environment critical sg pointer id requested 0
    mask original before cpu_sr context (flag_post_remaining_node (flag_post_remaining context)) 0).
  { unfold flag_post_loop_facts; subst context; cbn [flag_post_loop_entry
      flag_post_posted_word flag_post_initial_order flag_post_visited flag_post_remaining
      flag_post_accumulator flag_post_loop_local flag_post_scan_initial flag_post_scan_state
      flag_post_scan_visits].
    split; [exact PreH2|]. split.
    - apply flag_post_scan_initial_loop_state__word_update_first; assumption.
    - split; [reflexivity|]. split; [reflexivity|exact Hcurrent]. }
  Exists context.
  unfold flag_post_loop_cut; entailer!.
  destruct Hlayout as [_ [Hword_address _]].
  destruct Hpointer as [Hzero|Hpointer]; [exfalso; exact ((proj1 Hprefix) Hzero)|].
  rewrite Hword_address, Hpointer at 1.
  sep_apply_l_atomic (flag_post_current_word_merge_updated__word_update_first sg
    (flag_post_acquired entry_2) id group image_2 posted Hcfg (proj1 Hcurrent)).
  subst context.
  unfold flag_post_source_masked, flag_post_masked, flag_post_critical_frame,
    kernel_continuation_world_spec.kernel_continuation_inv.
  cbn [flag_post_loop_local flag_post_loop_entry flag_post_accumulator
    flag_post_scan_initial flag_post_scan_state replace_FlagS TskState].
  entailer!.
  exact (proj2 (proj2 Hcurrent)).
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_5 : OSFlagPost_entail_wit_10_5.
Proof.
  left; intros; subst option_word.
  pose proof PreH1 as [Hcfg [Hpointer [Hrequested [Hoption [Hunlink [Htcb Hlayout]]]]]].
  pose proof PreH2 as [Hprefix [Hvalid [Hcoverage Hsource]]].
  assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true)
    by (rewrite Hcfg; reflexivity).
  assert (Hflags : valid_flag_state sg (flag_post_acquired entry_2).(FlagState)).
  { destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ [Hflags _]]]]]]]].
    unfold valid_flag_configuration in Hflags; rewrite Henabled in Hflags; exact Hflags. }
  assert (Htype : image_2.(flagImageType) = 5) by (apply PreH4; reflexivity).
  destruct (flag_image_type_used_group__word_update_first sg _ id image_2
    Hflags PreH3 Htype) as [group Hgroup].
  set (posted := Z.land image_2.(flagImageBits) (unsigned_last_nbits (Z.lnot requested) 16)).
  assert (Hposted : flag_post_bits sg.(osKernelConfig) image_2.(flagImageBits) requested 0 = Some posted)
    by (rewrite Hcfg; apply flag_post_clear_word_16__word_update_first).
  assert (Hbits : flag_word_in_range sg.(osKernelConfig) posted).
  { eapply flag_post_bits_in_range; [rewrite Hcfg; cbn; lia|exact Hposted]. }
  pose proof (flag_replace_bits_preserves_current_valid__word_update_first sg
    (flag_post_entered entry_2) (flag_post_acquired entry_2) id group image_2 posted
    Hcfg (proj2 PreH2) Hgroup PreH3 Hbits) as Hcurrent.
  set (context := {| flag_post_loop_entry := entry_2;
    flag_post_posted_word := posted;
    flag_post_initial_order := flagWaitOrder group;
    flag_post_visited := nil;
    flag_post_remaining := flagWaitOrder group;
    flag_post_accumulator := flag_post_scan_initial
      (replace_FlagS (flag_replace_bits (FlagState (flag_post_acquired entry_2))
        id group image_2 posted) (flag_post_acquired entry_2));
    flag_post_loop_local := flag_post_local entry_2 |}).
  assert (Hinitial : flag_post_initial_scan context) by reflexivity.
  assert (Hloop : flag_post_loop_facts environment critical sg pointer id requested 0
    mask original before cpu_sr context (flag_post_remaining_node (flag_post_remaining context)) 0).
  { unfold flag_post_loop_facts; subst context; cbn [flag_post_loop_entry
      flag_post_posted_word flag_post_initial_order flag_post_visited flag_post_remaining
      flag_post_accumulator flag_post_loop_local flag_post_scan_initial flag_post_scan_state
      flag_post_scan_visits].
    split; [exact PreH2|]. split.
    - apply flag_post_scan_initial_loop_state__word_update_first; assumption.
    - split; [reflexivity|]. split; [reflexivity|exact Hcurrent]. }
  Exists context.
  unfold flag_post_loop_cut; entailer!.
  destruct Hlayout as [_ [Hword_address _]].
  destruct Hpointer as [Hzero|Hpointer]; [exfalso; exact ((proj1 Hprefix) Hzero)|].
  rewrite Hword_address, Hpointer at 1.
  sep_apply_l_atomic (flag_post_current_word_merge_updated__word_update_first sg
    (flag_post_acquired entry_2) id group image_2 posted Hcfg (proj1 Hcurrent)).
  subst context.
  unfold flag_post_source_masked, flag_post_masked, flag_post_critical_frame,
    kernel_continuation_world_spec.kernel_continuation_inv.
  cbn [flag_post_loop_local flag_post_loop_entry flag_post_accumulator
    flag_post_scan_initial flag_post_scan_state replace_FlagS TskState].
  entailer!.
  exact (proj2 (proj2 Hcurrent)).
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_6 : OSFlagPost_entail_wit_10_6.
Proof.
  left; intros; subst option_word.
  pose proof PreH1 as [Hcfg [Hpointer [Hrequested [Hoption [Hunlink [Htcb Hlayout]]]]]].
  pose proof PreH2 as [Hprefix [Hvalid [Hcoverage Hsource]]].
  assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true)
    by (rewrite Hcfg; reflexivity).
  assert (Hflags : valid_flag_state sg (flag_post_acquired entry_2).(FlagState)).
  { destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ [Hflags _]]]]]]]].
    unfold valid_flag_configuration in Hflags; rewrite Henabled in Hflags; exact Hflags. }
  assert (Htype : image_2.(flagImageType) = 5) by (apply PreH4; reflexivity).
  destruct (flag_image_type_used_group__word_update_first sg _ id image_2
    Hflags PreH3 Htype) as [group Hgroup].
  set (posted := Z.land image_2.(flagImageBits) (unsigned_last_nbits (Z.lnot requested) 16)).
  assert (Hposted : flag_post_bits sg.(osKernelConfig) image_2.(flagImageBits) requested 0 = Some posted)
    by (rewrite Hcfg; apply flag_post_clear_word_16__word_update_first).
  assert (Hbits : flag_word_in_range sg.(osKernelConfig) posted).
  { eapply flag_post_bits_in_range; [rewrite Hcfg; cbn; lia|exact Hposted]. }
  pose proof (flag_replace_bits_preserves_current_valid__word_update_first sg
    (flag_post_entered entry_2) (flag_post_acquired entry_2) id group image_2 posted
    Hcfg (proj2 PreH2) Hgroup PreH3 Hbits) as Hcurrent.
  set (context := {| flag_post_loop_entry := entry_2;
    flag_post_posted_word := posted;
    flag_post_initial_order := flagWaitOrder group;
    flag_post_visited := nil;
    flag_post_remaining := flagWaitOrder group;
    flag_post_accumulator := flag_post_scan_initial
      (replace_FlagS (flag_replace_bits (FlagState (flag_post_acquired entry_2))
        id group image_2 posted) (flag_post_acquired entry_2));
    flag_post_loop_local := flag_post_local entry_2 |}).
  assert (Hinitial : flag_post_initial_scan context) by reflexivity.
  assert (Hloop : flag_post_loop_facts environment critical sg pointer id requested 0
    mask original before cpu_sr context (flag_post_remaining_node (flag_post_remaining context)) 0).
  { unfold flag_post_loop_facts; subst context; cbn [flag_post_loop_entry
      flag_post_posted_word flag_post_initial_order flag_post_visited flag_post_remaining
      flag_post_accumulator flag_post_loop_local flag_post_scan_initial flag_post_scan_state
      flag_post_scan_visits].
    split; [exact PreH2|]. split.
    - apply flag_post_scan_initial_loop_state__word_update_first; assumption.
    - split; [reflexivity|]. split; [reflexivity|exact Hcurrent]. }
  Exists context.
  unfold flag_post_loop_cut; entailer!.
  destruct Hlayout as [_ [Hword_address _]].
  destruct Hpointer as [Hzero|Hpointer]; [exfalso; exact ((proj1 Hprefix) Hzero)|].
  rewrite Hword_address, Hpointer at 1.
  sep_apply_l_atomic (flag_post_current_word_merge_updated__word_update_first sg
    (flag_post_acquired entry_2) id group image_2 posted Hcfg (proj1 Hcurrent)).
  subst context.
  unfold flag_post_source_masked, flag_post_masked, flag_post_critical_frame,
    kernel_continuation_world_spec.kernel_continuation_inv.
  cbn [flag_post_loop_local flag_post_loop_entry flag_post_accumulator
    flag_post_scan_initial flag_post_scan_state replace_FlagS TskState].
  entailer!.
  exact (proj2 (proj2 Hcurrent)).
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_7 : OSFlagPost_entail_wit_10_7.
Proof.
  left; intros; subst option_word.
  pose proof PreH1 as [Hcfg [Hpointer [Hrequested [Hoption [Hunlink [Htcb Hlayout]]]]]].
  pose proof PreH2 as [Hprefix [Hvalid [Hcoverage Hsource]]].
  assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true)
    by (rewrite Hcfg; reflexivity).
  assert (Hflags : valid_flag_state sg (flag_post_acquired entry_2).(FlagState)).
  { destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ [Hflags _]]]]]]]].
    unfold valid_flag_configuration in Hflags; rewrite Henabled in Hflags; exact Hflags. }
  assert (Htype : image_2.(flagImageType) = 5) by (apply PreH4; reflexivity).
  destruct (flag_image_type_used_group__word_update_first sg _ id image_2
    Hflags PreH3 Htype) as [group Hgroup].
  set (posted := Z.lor (unsigned_last_nbits image_2.(flagImageBits) 16) (unsigned_last_nbits requested 16)).
  assert (Hposted : flag_post_bits sg.(osKernelConfig) image_2.(flagImageBits) requested 1 = Some posted)
    by (rewrite Hcfg; apply flag_post_set_word_16__word_update_first).
  assert (Hbits : flag_word_in_range sg.(osKernelConfig) posted).
  { eapply flag_post_bits_in_range; [rewrite Hcfg; cbn; lia|exact Hposted]. }
  pose proof (flag_replace_bits_preserves_current_valid__word_update_first sg
    (flag_post_entered entry_2) (flag_post_acquired entry_2) id group image_2 posted
    Hcfg (proj2 PreH2) Hgroup PreH3 Hbits) as Hcurrent.
  set (context := {| flag_post_loop_entry := entry_2;
    flag_post_posted_word := posted;
    flag_post_initial_order := flagWaitOrder group;
    flag_post_visited := nil;
    flag_post_remaining := flagWaitOrder group;
    flag_post_accumulator := flag_post_scan_initial
      (replace_FlagS (flag_replace_bits (FlagState (flag_post_acquired entry_2))
        id group image_2 posted) (flag_post_acquired entry_2));
    flag_post_loop_local := flag_post_local entry_2 |}).
  assert (Hinitial : flag_post_initial_scan context) by reflexivity.
  assert (Hloop : flag_post_loop_facts environment critical sg pointer id requested 1
    mask original before cpu_sr context (flag_post_remaining_node (flag_post_remaining context)) 0).
  { unfold flag_post_loop_facts; subst context; cbn [flag_post_loop_entry
      flag_post_posted_word flag_post_initial_order flag_post_visited flag_post_remaining
      flag_post_accumulator flag_post_loop_local flag_post_scan_initial flag_post_scan_state
      flag_post_scan_visits].
    split; [exact PreH2|]. split.
    - apply flag_post_scan_initial_loop_state__word_update_first; assumption.
    - split; [reflexivity|]. split; [reflexivity|exact Hcurrent]. }
  Exists context.
  unfold flag_post_loop_cut; entailer!.
  destruct Hlayout as [_ [Hword_address _]].
  destruct Hpointer as [Hzero|Hpointer]; [exfalso; exact ((proj1 Hprefix) Hzero)|].
  rewrite Hword_address, Hpointer at 1.
  sep_apply_l_atomic (flag_post_current_word_merge_updated__word_update_first sg
    (flag_post_acquired entry_2) id group image_2 posted Hcfg (proj1 Hcurrent)).
  subst context.
  unfold flag_post_source_masked, flag_post_masked, flag_post_critical_frame,
    kernel_continuation_world_spec.kernel_continuation_inv.
  cbn [flag_post_loop_local flag_post_loop_entry flag_post_accumulator
    flag_post_scan_initial flag_post_scan_state replace_FlagS TskState].
  entailer!.
  exact (proj2 (proj2 Hcurrent)).
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_8 : OSFlagPost_entail_wit_10_8.
Proof.
  left; intros; subst option_word.
  pose proof PreH1 as [Hcfg [Hpointer [Hrequested [Hoption [Hunlink [Htcb Hlayout]]]]]].
  pose proof PreH2 as [Hprefix [Hvalid [Hcoverage Hsource]]].
  assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true)
    by (rewrite Hcfg; reflexivity).
  assert (Hflags : valid_flag_state sg (flag_post_acquired entry_2).(FlagState)).
  { destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ [Hflags _]]]]]]]].
    unfold valid_flag_configuration in Hflags; rewrite Henabled in Hflags; exact Hflags. }
  assert (Htype : image_2.(flagImageType) = 5) by (apply PreH4; reflexivity).
  destruct (flag_image_type_used_group__word_update_first sg _ id image_2
    Hflags PreH3 Htype) as [group Hgroup].
  set (posted := Z.lor (unsigned_last_nbits image_2.(flagImageBits) 16) (unsigned_last_nbits requested 16)).
  assert (Hposted : flag_post_bits sg.(osKernelConfig) image_2.(flagImageBits) requested 1 = Some posted)
    by (rewrite Hcfg; apply flag_post_set_word_16__word_update_first).
  assert (Hbits : flag_word_in_range sg.(osKernelConfig) posted).
  { eapply flag_post_bits_in_range; [rewrite Hcfg; cbn; lia|exact Hposted]. }
  pose proof (flag_replace_bits_preserves_current_valid__word_update_first sg
    (flag_post_entered entry_2) (flag_post_acquired entry_2) id group image_2 posted
    Hcfg (proj2 PreH2) Hgroup PreH3 Hbits) as Hcurrent.
  set (context := {| flag_post_loop_entry := entry_2;
    flag_post_posted_word := posted;
    flag_post_initial_order := flagWaitOrder group;
    flag_post_visited := nil;
    flag_post_remaining := flagWaitOrder group;
    flag_post_accumulator := flag_post_scan_initial
      (replace_FlagS (flag_replace_bits (FlagState (flag_post_acquired entry_2))
        id group image_2 posted) (flag_post_acquired entry_2));
    flag_post_loop_local := flag_post_local entry_2 |}).
  assert (Hinitial : flag_post_initial_scan context) by reflexivity.
  assert (Hloop : flag_post_loop_facts environment critical sg pointer id requested 1
    mask original before cpu_sr context (flag_post_remaining_node (flag_post_remaining context)) 0).
  { unfold flag_post_loop_facts; subst context; cbn [flag_post_loop_entry
      flag_post_posted_word flag_post_initial_order flag_post_visited flag_post_remaining
      flag_post_accumulator flag_post_loop_local flag_post_scan_initial flag_post_scan_state
      flag_post_scan_visits].
    split; [exact PreH2|]. split.
    - apply flag_post_scan_initial_loop_state__word_update_first; assumption.
    - split; [reflexivity|]. split; [reflexivity|exact Hcurrent]. }
  Exists context.
  unfold flag_post_loop_cut; entailer!.
  destruct Hlayout as [_ [Hword_address _]].
  destruct Hpointer as [Hzero|Hpointer]; [exfalso; exact ((proj1 Hprefix) Hzero)|].
  rewrite Hword_address, Hpointer at 1.
  sep_apply_l_atomic (flag_post_current_word_merge_updated__word_update_first sg
    (flag_post_acquired entry_2) id group image_2 posted Hcfg (proj1 Hcurrent)).
  subst context.
  unfold flag_post_source_masked, flag_post_masked, flag_post_critical_frame,
    kernel_continuation_world_spec.kernel_continuation_inv.
  cbn [flag_post_loop_local flag_post_loop_entry flag_post_accumulator
    flag_post_scan_initial flag_post_scan_state replace_FlagS TskState].
  entailer!.
  exact (proj2 (proj2 Hcurrent)).
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_9 : OSFlagPost_entail_wit_10_9.
Proof.
  left; intros; subst option_word.
  pose proof PreH1 as [Hcfg [Hpointer [Hrequested [Hoption [Hunlink [Htcb Hlayout]]]]]].
  pose proof PreH2 as [Hprefix [Hvalid [Hcoverage Hsource]]].
  assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true)
    by (rewrite Hcfg; reflexivity).
  assert (Hflags : valid_flag_state sg (flag_post_acquired entry_2).(FlagState)).
  { destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ [Hflags _]]]]]]]].
    unfold valid_flag_configuration in Hflags; rewrite Henabled in Hflags; exact Hflags. }
  assert (Htype : image_2.(flagImageType) = 5) by (apply PreH4; reflexivity).
  destruct (flag_image_type_used_group__word_update_first sg _ id image_2
    Hflags PreH3 Htype) as [group Hgroup].
  set (posted := Z.lor (unsigned_last_nbits image_2.(flagImageBits) 16) (unsigned_last_nbits requested 16)).
  assert (Hposted : flag_post_bits sg.(osKernelConfig) image_2.(flagImageBits) requested 1 = Some posted)
    by (rewrite Hcfg; apply flag_post_set_word_16__word_update_first).
  assert (Hbits : flag_word_in_range sg.(osKernelConfig) posted).
  { eapply flag_post_bits_in_range; [rewrite Hcfg; cbn; lia|exact Hposted]. }
  pose proof (flag_replace_bits_preserves_current_valid__word_update_first sg
    (flag_post_entered entry_2) (flag_post_acquired entry_2) id group image_2 posted
    Hcfg (proj2 PreH2) Hgroup PreH3 Hbits) as Hcurrent.
  set (context := {| flag_post_loop_entry := entry_2;
    flag_post_posted_word := posted;
    flag_post_initial_order := flagWaitOrder group;
    flag_post_visited := nil;
    flag_post_remaining := flagWaitOrder group;
    flag_post_accumulator := flag_post_scan_initial
      (replace_FlagS (flag_replace_bits (FlagState (flag_post_acquired entry_2))
        id group image_2 posted) (flag_post_acquired entry_2));
    flag_post_loop_local := flag_post_local entry_2 |}).
  assert (Hinitial : flag_post_initial_scan context) by reflexivity.
  assert (Hloop : flag_post_loop_facts environment critical sg pointer id requested 1
    mask original before cpu_sr context (flag_post_remaining_node (flag_post_remaining context)) 0).
  { unfold flag_post_loop_facts; subst context; cbn [flag_post_loop_entry
      flag_post_posted_word flag_post_initial_order flag_post_visited flag_post_remaining
      flag_post_accumulator flag_post_loop_local flag_post_scan_initial flag_post_scan_state
      flag_post_scan_visits].
    split; [exact PreH2|]. split.
    - apply flag_post_scan_initial_loop_state__word_update_first; assumption.
    - split; [reflexivity|]. split; [reflexivity|exact Hcurrent]. }
  Exists context.
  unfold flag_post_loop_cut; entailer!.
  destruct Hlayout as [_ [Hword_address _]].
  destruct Hpointer as [Hzero|Hpointer]; [exfalso; exact ((proj1 Hprefix) Hzero)|].
  rewrite Hword_address, Hpointer at 1.
  sep_apply_l_atomic (flag_post_current_word_merge_updated__word_update_first sg
    (flag_post_acquired entry_2) id group image_2 posted Hcfg (proj1 Hcurrent)).
  subst context.
  unfold flag_post_source_masked, flag_post_masked, flag_post_critical_frame,
    kernel_continuation_world_spec.kernel_continuation_inv.
  cbn [flag_post_loop_local flag_post_loop_entry flag_post_accumulator
    flag_post_scan_initial flag_post_scan_state replace_FlagS TskState].
  entailer!.
  exact (proj2 (proj2 Hcurrent)).
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_10 : OSFlagPost_entail_wit_10_10.
Proof.
  left; intros; subst option_word.
  pose proof PreH1 as [Hcfg [Hpointer [Hrequested [Hoption [Hunlink [Htcb Hlayout]]]]]].
  pose proof PreH2 as [Hprefix [Hvalid [Hcoverage Hsource]]].
  assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true)
    by (rewrite Hcfg; reflexivity).
  assert (Hflags : valid_flag_state sg (flag_post_acquired entry_2).(FlagState)).
  { destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ [Hflags _]]]]]]]].
    unfold valid_flag_configuration in Hflags; rewrite Henabled in Hflags; exact Hflags. }
  assert (Htype : image_2.(flagImageType) = 5) by (apply PreH4; reflexivity).
  destruct (flag_image_type_used_group__word_update_first sg _ id image_2
    Hflags PreH3 Htype) as [group Hgroup].
  set (posted := Z.lor (unsigned_last_nbits image_2.(flagImageBits) 16) (unsigned_last_nbits requested 16)).
  assert (Hposted : flag_post_bits sg.(osKernelConfig) image_2.(flagImageBits) requested 1 = Some posted)
    by (rewrite Hcfg; apply flag_post_set_word_16__word_update_first).
  assert (Hbits : flag_word_in_range sg.(osKernelConfig) posted).
  { eapply flag_post_bits_in_range; [rewrite Hcfg; cbn; lia|exact Hposted]. }
  pose proof (flag_replace_bits_preserves_current_valid__word_update_first sg
    (flag_post_entered entry_2) (flag_post_acquired entry_2) id group image_2 posted
    Hcfg (proj2 PreH2) Hgroup PreH3 Hbits) as Hcurrent.
  set (context := {| flag_post_loop_entry := entry_2;
    flag_post_posted_word := posted;
    flag_post_initial_order := flagWaitOrder group;
    flag_post_visited := nil;
    flag_post_remaining := flagWaitOrder group;
    flag_post_accumulator := flag_post_scan_initial
      (replace_FlagS (flag_replace_bits (FlagState (flag_post_acquired entry_2))
        id group image_2 posted) (flag_post_acquired entry_2));
    flag_post_loop_local := flag_post_local entry_2 |}).
  assert (Hinitial : flag_post_initial_scan context) by reflexivity.
  assert (Hloop : flag_post_loop_facts environment critical sg pointer id requested 1
    mask original before cpu_sr context (flag_post_remaining_node (flag_post_remaining context)) 0).
  { unfold flag_post_loop_facts; subst context; cbn [flag_post_loop_entry
      flag_post_posted_word flag_post_initial_order flag_post_visited flag_post_remaining
      flag_post_accumulator flag_post_loop_local flag_post_scan_initial flag_post_scan_state
      flag_post_scan_visits].
    split; [exact PreH2|]. split.
    - apply flag_post_scan_initial_loop_state__word_update_first; assumption.
    - split; [reflexivity|]. split; [reflexivity|exact Hcurrent]. }
  Exists context.
  unfold flag_post_loop_cut; entailer!.
  destruct Hlayout as [_ [Hword_address _]].
  destruct Hpointer as [Hzero|Hpointer]; [exfalso; exact ((proj1 Hprefix) Hzero)|].
  rewrite Hword_address, Hpointer at 1.
  sep_apply_l_atomic (flag_post_current_word_merge_updated__word_update_first sg
    (flag_post_acquired entry_2) id group image_2 posted Hcfg (proj1 Hcurrent)).
  subst context.
  unfold flag_post_source_masked, flag_post_masked, flag_post_critical_frame,
    kernel_continuation_world_spec.kernel_continuation_inv.
  cbn [flag_post_loop_local flag_post_loop_entry flag_post_accumulator
    flag_post_scan_initial flag_post_scan_state replace_FlagS TskState].
  entailer!.
  exact (proj2 (proj2 Hcurrent)).
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_11 : OSFlagPost_entail_wit_10_11.
Proof.
  left; intros; subst option_word.
  pose proof PreH1 as [Hcfg [Hpointer [Hrequested [Hoption [Hunlink [Htcb Hlayout]]]]]].
  pose proof PreH2 as [Hprefix [Hvalid [Hcoverage Hsource]]].
  assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true)
    by (rewrite Hcfg; reflexivity).
  assert (Hflags : valid_flag_state sg (flag_post_acquired entry_2).(FlagState)).
  { destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ [Hflags _]]]]]]]].
    unfold valid_flag_configuration in Hflags; rewrite Henabled in Hflags; exact Hflags. }
  assert (Htype : image_2.(flagImageType) = 5) by (apply PreH4; reflexivity).
  destruct (flag_image_type_used_group__word_update_first sg _ id image_2
    Hflags PreH3 Htype) as [group Hgroup].
  set (posted := Z.lor (unsigned_last_nbits image_2.(flagImageBits) 16) (unsigned_last_nbits requested 16)).
  assert (Hposted : flag_post_bits sg.(osKernelConfig) image_2.(flagImageBits) requested 1 = Some posted)
    by (rewrite Hcfg; apply flag_post_set_word_16__word_update_first).
  assert (Hbits : flag_word_in_range sg.(osKernelConfig) posted).
  { eapply flag_post_bits_in_range; [rewrite Hcfg; cbn; lia|exact Hposted]. }
  pose proof (flag_replace_bits_preserves_current_valid__word_update_first sg
    (flag_post_entered entry_2) (flag_post_acquired entry_2) id group image_2 posted
    Hcfg (proj2 PreH2) Hgroup PreH3 Hbits) as Hcurrent.
  set (context := {| flag_post_loop_entry := entry_2;
    flag_post_posted_word := posted;
    flag_post_initial_order := flagWaitOrder group;
    flag_post_visited := nil;
    flag_post_remaining := flagWaitOrder group;
    flag_post_accumulator := flag_post_scan_initial
      (replace_FlagS (flag_replace_bits (FlagState (flag_post_acquired entry_2))
        id group image_2 posted) (flag_post_acquired entry_2));
    flag_post_loop_local := flag_post_local entry_2 |}).
  assert (Hinitial : flag_post_initial_scan context) by reflexivity.
  assert (Hloop : flag_post_loop_facts environment critical sg pointer id requested 1
    mask original before cpu_sr context (flag_post_remaining_node (flag_post_remaining context)) 0).
  { unfold flag_post_loop_facts; subst context; cbn [flag_post_loop_entry
      flag_post_posted_word flag_post_initial_order flag_post_visited flag_post_remaining
      flag_post_accumulator flag_post_loop_local flag_post_scan_initial flag_post_scan_state
      flag_post_scan_visits].
    split; [exact PreH2|]. split.
    - apply flag_post_scan_initial_loop_state__word_update_first; assumption.
    - split; [reflexivity|]. split; [reflexivity|exact Hcurrent]. }
  Exists context.
  unfold flag_post_loop_cut; entailer!.
  destruct Hlayout as [_ [Hword_address _]].
  destruct Hpointer as [Hzero|Hpointer]; [exfalso; exact ((proj1 Hprefix) Hzero)|].
  rewrite Hword_address, Hpointer at 1.
  sep_apply_l_atomic (flag_post_current_word_merge_updated__word_update_first sg
    (flag_post_acquired entry_2) id group image_2 posted Hcfg (proj1 Hcurrent)).
  subst context.
  unfold flag_post_source_masked, flag_post_masked, flag_post_critical_frame,
    kernel_continuation_world_spec.kernel_continuation_inv.
  cbn [flag_post_loop_local flag_post_loop_entry flag_post_accumulator
    flag_post_scan_initial flag_post_scan_state replace_FlagS TskState].
  entailer!.
  exact (proj2 (proj2 Hcurrent)).
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_12 : OSFlagPost_entail_wit_10_12.
Proof.
  left; intros; subst option_word.
  pose proof PreH1 as [Hcfg [Hpointer [Hrequested [Hoption [Hunlink [Htcb Hlayout]]]]]].
  pose proof PreH2 as [Hprefix [Hvalid [Hcoverage Hsource]]].
  assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true)
    by (rewrite Hcfg; reflexivity).
  assert (Hflags : valid_flag_state sg (flag_post_acquired entry_2).(FlagState)).
  { destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ [Hflags _]]]]]]]].
    unfold valid_flag_configuration in Hflags; rewrite Henabled in Hflags; exact Hflags. }
  assert (Htype : image_2.(flagImageType) = 5) by (apply PreH4; reflexivity).
  destruct (flag_image_type_used_group__word_update_first sg _ id image_2
    Hflags PreH3 Htype) as [group Hgroup].
  set (posted := Z.lor (unsigned_last_nbits image_2.(flagImageBits) 16) (unsigned_last_nbits requested 16)).
  assert (Hposted : flag_post_bits sg.(osKernelConfig) image_2.(flagImageBits) requested 1 = Some posted)
    by (rewrite Hcfg; apply flag_post_set_word_16__word_update_first).
  assert (Hbits : flag_word_in_range sg.(osKernelConfig) posted).
  { eapply flag_post_bits_in_range; [rewrite Hcfg; cbn; lia|exact Hposted]. }
  pose proof (flag_replace_bits_preserves_current_valid__word_update_first sg
    (flag_post_entered entry_2) (flag_post_acquired entry_2) id group image_2 posted
    Hcfg (proj2 PreH2) Hgroup PreH3 Hbits) as Hcurrent.
  set (context := {| flag_post_loop_entry := entry_2;
    flag_post_posted_word := posted;
    flag_post_initial_order := flagWaitOrder group;
    flag_post_visited := nil;
    flag_post_remaining := flagWaitOrder group;
    flag_post_accumulator := flag_post_scan_initial
      (replace_FlagS (flag_replace_bits (FlagState (flag_post_acquired entry_2))
        id group image_2 posted) (flag_post_acquired entry_2));
    flag_post_loop_local := flag_post_local entry_2 |}).
  assert (Hinitial : flag_post_initial_scan context) by reflexivity.
  assert (Hloop : flag_post_loop_facts environment critical sg pointer id requested 1
    mask original before cpu_sr context (flag_post_remaining_node (flag_post_remaining context)) 0).
  { unfold flag_post_loop_facts; subst context; cbn [flag_post_loop_entry
      flag_post_posted_word flag_post_initial_order flag_post_visited flag_post_remaining
      flag_post_accumulator flag_post_loop_local flag_post_scan_initial flag_post_scan_state
      flag_post_scan_visits].
    split; [exact PreH2|]. split.
    - apply flag_post_scan_initial_loop_state__word_update_first; assumption.
    - split; [reflexivity|]. split; [reflexivity|exact Hcurrent]. }
  Exists context.
  unfold flag_post_loop_cut; entailer!.
  destruct Hlayout as [_ [Hword_address _]].
  destruct Hpointer as [Hzero|Hpointer]; [exfalso; exact ((proj1 Hprefix) Hzero)|].
  rewrite Hword_address, Hpointer at 1.
  sep_apply_l_atomic (flag_post_current_word_merge_updated__word_update_first sg
    (flag_post_acquired entry_2) id group image_2 posted Hcfg (proj1 Hcurrent)).
  subst context.
  unfold flag_post_source_masked, flag_post_masked, flag_post_critical_frame,
    kernel_continuation_world_spec.kernel_continuation_inv.
  cbn [flag_post_loop_local flag_post_loop_entry flag_post_accumulator
    flag_post_scan_initial flag_post_scan_state replace_FlagS TskState].
  entailer!.
  exact (proj2 (proj2 Hcurrent)).
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_13 : OSFlagPost_entail_wit_10_13.
Proof.
  left; intros.
  subst option_word.
  pose proof PreH1 as [Hcfg [Hpointer [Hrequested [Hoption
    [Hunlink [Htcb [Htypeaddr [Hwordaddr Hnodeaddr]]]]]]]].
  assert (Hnonnull : pointer <> 0) by exact (proj1 (proj1 PreH2)).
  assert (Hpointer_eq : pointer = flag_pool_addr sg id) by tauto.
  assert (Haddress : &(pointer # "os_flag_grp" ->ₛ "OSFlagFlags") =
    flag_pool_addr sg id + 8).
  { rewrite Hwordaddr, Hpointer_eq; reflexivity. }
  assert (Htype : flagImageType image_2 = 5).
  { apply PreH4; reflexivity. }
  assert (Hposted : flag_post_bits (osKernelConfig sg) (flagImageBits image_2) requested 1 =
    Some (Z.lor (unsigned_last_nbits (flagImageBits image_2) 16)
      (unsigned_last_nbits requested 16))).
  { rewrite Hcfg; unfold flag_post_bits.
    change (Some (unsigned_last_nbits (Z.lor (flagImageBits image_2) requested) 16) =
      Some (Z.lor (unsigned_last_nbits (flagImageBits image_2) 16)
        (unsigned_last_nbits requested 16))).
    rewrite unsigned_last_nbits_lor_distr by lia; reflexivity. }
  rewrite Haddress.
  sep_apply_l_atomic (flag_post_word_update_starts_scan__word_update_remaining
    environment critical sg pointer id requested 1 mask original before cpu_sr entry_2 image_2
    (Z.lor (unsigned_last_nbits (flagImageBits image_2) 16) (unsigned_last_nbits requested 16))
    Hcfg PreH2 PreH3 Htype Hposted).
  Intros context; Exists context; entailer!.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_14 : OSFlagPost_entail_wit_10_14.
Proof.
  left; intros.
  subst option_word.
  pose proof PreH1 as [Hcfg [Hpointer [Hrequested [Hoption
    [Hunlink [Htcb [Htypeaddr [Hwordaddr Hnodeaddr]]]]]]]].
  assert (Hnonnull : pointer <> 0) by exact (proj1 (proj1 PreH2)).
  assert (Hpointer_eq : pointer = flag_pool_addr sg id) by tauto.
  assert (Haddress : &(pointer # "os_flag_grp" ->ₛ "OSFlagFlags") =
    flag_pool_addr sg id + 8).
  { rewrite Hwordaddr, Hpointer_eq; reflexivity. }
  assert (Htype : flagImageType image_2 = 5).
  { apply PreH4; reflexivity. }
  assert (Hposted : flag_post_bits (osKernelConfig sg) (flagImageBits image_2) requested 1 =
    Some (Z.lor (unsigned_last_nbits (flagImageBits image_2) 16)
      (unsigned_last_nbits requested 16))).
  { rewrite Hcfg; unfold flag_post_bits.
    change (Some (unsigned_last_nbits (Z.lor (flagImageBits image_2) requested) 16) =
      Some (Z.lor (unsigned_last_nbits (flagImageBits image_2) 16)
        (unsigned_last_nbits requested 16))).
    rewrite unsigned_last_nbits_lor_distr by lia; reflexivity. }
  rewrite Haddress.
  sep_apply_l_atomic (flag_post_word_update_starts_scan__word_update_remaining
    environment critical sg pointer id requested 1 mask original before cpu_sr entry_2 image_2
    (Z.lor (unsigned_last_nbits (flagImageBits image_2) 16) (unsigned_last_nbits requested 16))
    Hcfg PreH2 PreH3 Htype Hposted).
  Intros context; Exists context; entailer!.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_15 : OSFlagPost_entail_wit_10_15.
Proof.
  left; intros.
  subst option_word.
  pose proof PreH1 as [Hcfg [Hpointer [Hrequested [Hoption
    [Hunlink [Htcb [Htypeaddr [Hwordaddr Hnodeaddr]]]]]]]].
  assert (Hnonnull : pointer <> 0) by exact (proj1 (proj1 PreH2)).
  assert (Hpointer_eq : pointer = flag_pool_addr sg id) by tauto.
  assert (Haddress : &(pointer # "os_flag_grp" ->ₛ "OSFlagFlags") =
    flag_pool_addr sg id + 8).
  { rewrite Hwordaddr, Hpointer_eq; reflexivity. }
  assert (Htype : flagImageType image_2 = 5).
  { apply PreH4; reflexivity. }
  assert (Hposted : flag_post_bits (osKernelConfig sg) (flagImageBits image_2) requested 1 =
    Some (Z.lor (unsigned_last_nbits (flagImageBits image_2) 16)
      (unsigned_last_nbits requested 16))).
  { rewrite Hcfg; unfold flag_post_bits.
    change (Some (unsigned_last_nbits (Z.lor (flagImageBits image_2) requested) 16) =
      Some (Z.lor (unsigned_last_nbits (flagImageBits image_2) 16)
        (unsigned_last_nbits requested 16))).
    rewrite unsigned_last_nbits_lor_distr by lia; reflexivity. }
  rewrite Haddress.
  sep_apply_l_atomic (flag_post_word_update_starts_scan__word_update_remaining
    environment critical sg pointer id requested 1 mask original before cpu_sr entry_2 image_2
    (Z.lor (unsigned_last_nbits (flagImageBits image_2) 16) (unsigned_last_nbits requested 16))
    Hcfg PreH2 PreH3 Htype Hposted).
  Intros context; Exists context; entailer!.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_16 : OSFlagPost_entail_wit_10_16.
Proof.
  left; intros.
  subst option_word.
  match goal with H : unsigned_last_nbits 1 32 = 0 |- _ =>
    vm_compute in H; discriminate H
  end.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_17 : OSFlagPost_entail_wit_10_17.
Proof.
  left; intros.
  subst option_word.
  match goal with H : unsigned_last_nbits 1 32 = 0 |- _ =>
    vm_compute in H; discriminate H
  end.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_18 : OSFlagPost_entail_wit_10_18.
Proof.
  left; intros.
  subst option_word.
  match goal with H : unsigned_last_nbits 1 32 = 0 |- _ =>
    vm_compute in H; discriminate H
  end.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_19 : OSFlagPost_entail_wit_10_19.
Proof.
  left; intros.
  subst option_word.
  match goal with H : unsigned_last_nbits 1 32 = 0 |- _ =>
    vm_compute in H; discriminate H
  end.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_20 : OSFlagPost_entail_wit_10_20.
Proof.
  left; intros.
  subst option_word.
  match goal with H : unsigned_last_nbits 1 32 = 0 |- _ =>
    vm_compute in H; discriminate H
  end.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_21 : OSFlagPost_entail_wit_10_21.
Proof.
  left; intros.
  subst option_word.
  match goal with H : unsigned_last_nbits 1 32 = 0 |- _ =>
    vm_compute in H; discriminate H
  end.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_22 : OSFlagPost_entail_wit_10_22.
Proof.
  left; intros.
  subst option_word.
  match goal with H : unsigned_last_nbits 1 32 = 0 |- _ =>
    vm_compute in H; discriminate H
  end.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_23 : OSFlagPost_entail_wit_10_23.
Proof.
  left; intros.
  subst option_word.
  match goal with H : unsigned_last_nbits 1 32 = 0 |- _ =>
    vm_compute in H; discriminate H
  end.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_10_24 : OSFlagPost_entail_wit_10_24.
Proof.
  left; intros.
  subst option_word.
  match goal with H : unsigned_last_nbits 1 32 = 0 |- _ =>
    vm_compute in H; discriminate H
  end.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_11 : OSFlagPost_entail_wit_11.
Proof.
  left; intros.
  pose proof PreH1 as [Hcfg [Hpointer [_ [_ [Hlayout _]]]]].
  pose proof PreH3 as [Hprotected [_ [_ [_ Hvalid]]]].
  assert (Hp : pointer = flag_pool_addr sg id).
  { destruct Hpointer as [Hnull|Hp]; [destruct Hprotected as [[Hnonzero _] _]; contradiction|exact Hp]. }
  destruct Hlayout as [_ [_ [_ [_ Hhead]]]].
  Exists context_3.
  unfold flag_post_loop_cut.
  rewrite (flag_post_masked_split_fields__loop_views_and_progress _ _ _ _ _ _ _ _ Hvalid).
  unfold kernel_program_fields_inv, kernel_program_fields_rep, UCOS2_fields_raw_rep, flag_fields_configured_rep.
  rewrite Hcfg; cbn [selected_kernel_configuration cfgFlagEnabled].
  rewrite (flag_fields_raw_rep_split_group sg _ id image PreH4).
  rewrite Hhead, Hp.
  unfold flag_post_group_head_frame, flag_post_group_frame, flag_group_rep, flag_group_rep_without_head.
  entailer!; try exact (proj1 Hvalid); try (rewrite <- Hp; assumption).
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_13 : OSFlagPost_entail_wit_13.
Proof.
  left; intros.
  pose proof PreH2 as [Hcfg [Hpointer [_ [_ [Hlayout [_ Hpostlayout]]]]]].
  pose proof PreH3 as [Hprotected [_ [_ [Hschedule Hvalid]]]].
  assert (Hp : pointer = flag_pool_addr sg id).
  { destruct Hpointer as [Hnull|Hp];
      [destruct Hprotected as [[Hnonzero _] _]; contradiction|exact Hp]. }
  destruct (flag_post_loop_image_and_mask__satisfied_helper_inputs
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcfg PreH3 PreH5 PreH4) as [Hposted Hmask_range].
  assert (Hunsigned : unsigned_last_nbits waiter.(flagWaitImage).(flagNodeMask) 16 =
    waiter.(flagWaitImage).(flagNodeMask)).
  { apply unsigned_last_nbits_eq; exact Hmask_range. }
  rewrite Hunsigned in PreH1 |- *.
  destruct (flag_post_land_word_in_range__satisfied_helper_inputs (flagImageBits image) _
    Hmask_range) as [Hready_range Hword].
  assert (Hsatisfied : flag_post_waiter_satisfied sg context_2 waiter
    (Z.land (flagImageBits image) (flagNodeMask (flagWaitImage waiter)))).
  { unfold flag_post_waiter_satisfied; rewrite Hcfg, <- PreH21, <- Hposted.
    rewrite flag_post_node_test_set_all, Hword.
    f_equal; f_equal; apply Z.eqb_eq; exact PreH1. }
  destruct (flag_task_rdy_stable_domain sg _ pnode waiter
    (Z.land (flagImageBits image) (flagNodeMask (flagWaitImage waiter)))
    Hcfg Hlayout Hready_range (proj1 Hvalid) PreH4) as [old Hdomain].
  Exists waiter old context_2.
  assert (Hpre :
    flag_fields_raw_rep sg context_2.(flag_post_accumulator).(flag_post_scan_state).(FlagState) **
    UCOS2_raw_rep_missing_flag sg context_2.(flag_post_accumulator).(flag_post_scan_state) **
    unmap_table_rep sg |--
    flag_task_rdy_fields_pre sg context_2.(flag_post_accumulator).(flag_post_scan_state)
      pnode waiter old (Z.land (flagImageBits image) (flagNodeMask (flagWaitImage waiter))) **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg
      context_2.(flag_post_accumulator).(flag_post_scan_state) ** unmap_table_rep sg).
  { pose proof (UCOS2_fields_raw_rep_split_task_storage_sched_flag sg
      context_2.(flag_post_accumulator).(flag_post_scan_state)) as Hsplit.
    unfold UCOS2_fields_raw_rep, flag_fields_configured_rep in Hsplit.
    rewrite Hcfg in Hsplit; cbn [selected_kernel_configuration cfgFlagEnabled] in Hsplit.
    rewrite Hsplit.
    unfold flag_task_rdy_fields_pre, flag_task_rdy_fields_resources; entailer!. }
  unfold flag_post_helper_cut.
  entailer!; try (rewrite <- Hschedule; exact PreH3).
  lazymatch goal with |- _ |-- ?Q =>
    assert (Hpre_normalized :
      flag_fields_raw_rep sg context_2.(flag_post_accumulator).(flag_post_scan_state).(FlagState) **
      UCOS2_raw_rep_missing_flag sg context_2.(flag_post_accumulator).(flag_post_scan_state) **
      unmap_table_rep sg |-- Q)
      by (sep_apply_l_atomic Hpre; entailer!)
  end.
  sep_apply_r_atomic Hpre_normalized.
  rewrite (flag_post_node_word_resources_equiv__satisfied_helper_inputs sg _ id pnode
    image waiter PreH5 PreH4).
  destruct Hlayout as [Hnext [Hprev [Htcb [Hgroup Hhead]]]].
  destruct Hpostlayout as [_ [Hbits [Hmask Hmode]]].
  rewrite Hnext, Hprev, Htcb, Hgroup, Hbits, Hmask, Hmode, Hp.
  unfold flag_node_fields_rep; rewrite Hcfg.
  cbn [flag_word_rep selected_kernel_configuration cfgFlagBits flag_node_mode_offset flag_word_bytes].
  entailer!; try (rewrite <- Hp; assumption);
    try (rewrite <- Hp, <- Hschedule; exact PreH3).
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_14 : OSFlagPost_entail_wit_14.
Proof.
  left; intros.
  pose proof PreH2 as [Hcfg [Hpointer [_ [_ [Hlayout [_ Hpostlayout]]]]]].
  pose proof PreH3 as [Hprotected [_ [_ [Hschedule Hvalid]]]].
  assert (Hp : pointer = flag_pool_addr sg id).
  { destruct Hpointer as [Hnull|Hp];
      [destruct Hprotected as [[Hnonzero _] _]; contradiction|exact Hp]. }
  destruct (flag_post_loop_image_and_mask__satisfied_helper_inputs
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcfg PreH3 PreH5 PreH4) as [Hposted Hmask_range].
  assert (Hunsigned : unsigned_last_nbits waiter.(flagWaitImage).(flagNodeMask) 16 =
    waiter.(flagWaitImage).(flagNodeMask)).
  { apply unsigned_last_nbits_eq; exact Hmask_range. }
  rewrite Hunsigned in PreH1 |- *.
  destruct (flag_post_land_word_in_range__satisfied_helper_inputs (flagImageBits image) _
    Hmask_range) as [Hready_range Hword].
  assert (Hsatisfied : flag_post_waiter_satisfied sg context_2 waiter
    (Z.land (flagImageBits image) (flagNodeMask (flagWaitImage waiter)))).
  { unfold flag_post_waiter_satisfied; rewrite Hcfg, <- PreH22, <- Hposted.
    rewrite flag_post_node_test_set_any, Hword.
    f_equal; f_equal; apply Bool.negb_true_iff, Z.eqb_neq; exact PreH1. }
  destruct (flag_task_rdy_stable_domain sg _ pnode waiter
    (Z.land (flagImageBits image) (flagNodeMask (flagWaitImage waiter)))
    Hcfg Hlayout Hready_range (proj1 Hvalid) PreH4) as [old Hdomain].
  Exists waiter old context_2.
  assert (Hpre :
    flag_fields_raw_rep sg context_2.(flag_post_accumulator).(flag_post_scan_state).(FlagState) **
    UCOS2_raw_rep_missing_flag sg context_2.(flag_post_accumulator).(flag_post_scan_state) **
    unmap_table_rep sg |--
    flag_task_rdy_fields_pre sg context_2.(flag_post_accumulator).(flag_post_scan_state)
      pnode waiter old (Z.land (flagImageBits image) (flagNodeMask (flagWaitImage waiter))) **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg
      context_2.(flag_post_accumulator).(flag_post_scan_state) ** unmap_table_rep sg).
  { pose proof (UCOS2_fields_raw_rep_split_task_storage_sched_flag sg
      context_2.(flag_post_accumulator).(flag_post_scan_state)) as Hsplit.
    unfold UCOS2_fields_raw_rep, flag_fields_configured_rep in Hsplit.
    rewrite Hcfg in Hsplit; cbn [selected_kernel_configuration cfgFlagEnabled] in Hsplit.
    rewrite Hsplit.
    unfold flag_task_rdy_fields_pre, flag_task_rdy_fields_resources; entailer!. }
  unfold flag_post_helper_cut.
  entailer!; try (rewrite <- Hschedule; exact PreH3).
  lazymatch goal with |- _ |-- ?Q =>
    assert (Hpre_normalized :
      flag_fields_raw_rep sg context_2.(flag_post_accumulator).(flag_post_scan_state).(FlagState) **
      UCOS2_raw_rep_missing_flag sg context_2.(flag_post_accumulator).(flag_post_scan_state) **
      unmap_table_rep sg |-- Q)
      by (sep_apply_l_atomic Hpre; entailer!)
  end.
  sep_apply_r_atomic Hpre_normalized.
  rewrite (flag_post_node_word_resources_equiv__satisfied_helper_inputs sg _ id pnode
    image waiter PreH5 PreH4).
  destruct Hlayout as [Hnext [Hprev [Htcb [Hgroup Hhead]]]].
  destruct Hpostlayout as [_ [Hbits [Hmask Hmode]]].
  rewrite Hnext, Hprev, Htcb, Hgroup, Hbits, Hmask, Hmode, Hp.
  unfold flag_node_fields_rep; rewrite Hcfg.
  cbn [flag_word_rep selected_kernel_configuration cfgFlagBits flag_node_mode_offset flag_word_bytes].
  entailer!; try (rewrite <- Hp; assumption);
    try (rewrite <- Hp, <- Hschedule; exact PreH3).
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_15 : OSFlagPost_entail_wit_15.
Proof.
  left; intros.
  pose proof PreH2 as [Hcfg [Hpointer [_ [_ [Hlayout [_ Hpostlayout]]]]]].
  pose proof PreH3 as [Hprotected [_ [_ [Hschedule Hvalid]]]].
  assert (Hp : pointer = flag_pool_addr sg id).
  { destruct Hpointer as [Hnull|Hp];
      [destruct Hprotected as [[Hnonzero _] _]; contradiction|exact Hp]. }
  destruct (flag_post_loop_image_and_mask__satisfied_helper_inputs
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcfg PreH3 PreH5 PreH4) as [Hposted Hmask_range].
  assert (Hunsigned : unsigned_last_nbits waiter.(flagWaitImage).(flagNodeMask) 16 =
    waiter.(flagWaitImage).(flagNodeMask)).
  { apply unsigned_last_nbits_eq; exact Hmask_range. }
  rewrite Hunsigned in PreH1 |- *.
  destruct (flag_post_land_word_in_range__satisfied_helper_inputs (Z.lnot (flagImageBits image)) _
    Hmask_range) as [Hready_range Hword].
  assert (Hsatisfied : flag_post_waiter_satisfied sg context_2 waiter
    (Z.land (Z.lnot (flagImageBits image)) (flagNodeMask (flagWaitImage waiter)))).
  { unfold flag_post_waiter_satisfied; rewrite Hcfg, <- PreH23, <- Hposted.
    rewrite flag_post_node_test_clear_all, Hword.
    f_equal; f_equal; apply Z.eqb_eq; exact PreH1. }
  destruct (flag_task_rdy_stable_domain sg _ pnode waiter
    (Z.land (Z.lnot (flagImageBits image)) (flagNodeMask (flagWaitImage waiter)))
    Hcfg Hlayout Hready_range (proj1 Hvalid) PreH4) as [old Hdomain].
  Exists waiter old context_2.
  assert (Hpre :
    flag_fields_raw_rep sg context_2.(flag_post_accumulator).(flag_post_scan_state).(FlagState) **
    UCOS2_raw_rep_missing_flag sg context_2.(flag_post_accumulator).(flag_post_scan_state) **
    unmap_table_rep sg |--
    flag_task_rdy_fields_pre sg context_2.(flag_post_accumulator).(flag_post_scan_state)
      pnode waiter old (Z.land (Z.lnot (flagImageBits image)) (flagNodeMask (flagWaitImage waiter))) **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg
      context_2.(flag_post_accumulator).(flag_post_scan_state) ** unmap_table_rep sg).
  { pose proof (UCOS2_fields_raw_rep_split_task_storage_sched_flag sg
      context_2.(flag_post_accumulator).(flag_post_scan_state)) as Hsplit.
    unfold UCOS2_fields_raw_rep, flag_fields_configured_rep in Hsplit.
    rewrite Hcfg in Hsplit; cbn [selected_kernel_configuration cfgFlagEnabled] in Hsplit.
    rewrite Hsplit.
    unfold flag_task_rdy_fields_pre, flag_task_rdy_fields_resources; entailer!. }
  unfold flag_post_helper_cut.
  entailer!; try (rewrite <- Hschedule; exact PreH3).
  lazymatch goal with |- _ |-- ?Q =>
    assert (Hpre_normalized :
      flag_fields_raw_rep sg context_2.(flag_post_accumulator).(flag_post_scan_state).(FlagState) **
      UCOS2_raw_rep_missing_flag sg context_2.(flag_post_accumulator).(flag_post_scan_state) **
      unmap_table_rep sg |-- Q)
      by (sep_apply_l_atomic Hpre; entailer!)
  end.
  sep_apply_r_atomic Hpre_normalized.
  rewrite (flag_post_node_word_resources_equiv__satisfied_helper_inputs sg _ id pnode
    image waiter PreH5 PreH4).
  destruct Hlayout as [Hnext [Hprev [Htcb [Hgroup Hhead]]]].
  destruct Hpostlayout as [_ [Hbits [Hmask Hmode]]].
  rewrite Hnext, Hprev, Htcb, Hgroup, Hbits, Hmask, Hmode, Hp.
  unfold flag_node_fields_rep; rewrite Hcfg.
  cbn [flag_word_rep selected_kernel_configuration cfgFlagBits flag_node_mode_offset flag_word_bytes].
  entailer!; try (rewrite <- Hp; assumption);
    try (rewrite <- Hp, <- Hschedule; exact PreH3).
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_16 : OSFlagPost_entail_wit_16.
Proof.
  left; intros.
  pose proof PreH2 as [Hcfg [Hpointer [_ [_ [Hlayout [_ Hpostlayout]]]]]].
  pose proof PreH3 as [Hprotected [_ [_ [Hschedule Hvalid]]]].
  assert (Hp : pointer = flag_pool_addr sg id).
  { destruct Hpointer as [Hnull|Hp];
      [destruct Hprotected as [[Hnonzero _] _]; contradiction|exact Hp]. }
  destruct (flag_post_loop_image_and_mask__satisfied_helper_inputs
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcfg PreH3 PreH5 PreH4) as [Hposted Hmask_range].
  assert (Hunsigned : unsigned_last_nbits waiter.(flagWaitImage).(flagNodeMask) 16 =
    waiter.(flagWaitImage).(flagNodeMask)).
  { apply unsigned_last_nbits_eq; exact Hmask_range. }
  rewrite Hunsigned in PreH1 |- *.
  destruct (flag_post_land_word_in_range__satisfied_helper_inputs (Z.lnot (flagImageBits image)) _
    Hmask_range) as [Hready_range Hword].
  assert (Hsatisfied : flag_post_waiter_satisfied sg context_2 waiter
    (Z.land (Z.lnot (flagImageBits image)) (flagNodeMask (flagWaitImage waiter)))).
  { unfold flag_post_waiter_satisfied; rewrite Hcfg, <- PreH24, <- Hposted.
    rewrite flag_post_node_test_clear_any, Hword.
    f_equal; f_equal; apply Bool.negb_true_iff, Z.eqb_neq; exact PreH1. }
  destruct (flag_task_rdy_stable_domain sg _ pnode waiter
    (Z.land (Z.lnot (flagImageBits image)) (flagNodeMask (flagWaitImage waiter)))
    Hcfg Hlayout Hready_range (proj1 Hvalid) PreH4) as [old Hdomain].
  Exists waiter old context_2.
  assert (Hpre :
    flag_fields_raw_rep sg context_2.(flag_post_accumulator).(flag_post_scan_state).(FlagState) **
    UCOS2_raw_rep_missing_flag sg context_2.(flag_post_accumulator).(flag_post_scan_state) **
    unmap_table_rep sg |--
    flag_task_rdy_fields_pre sg context_2.(flag_post_accumulator).(flag_post_scan_state)
      pnode waiter old (Z.land (Z.lnot (flagImageBits image)) (flagNodeMask (flagWaitImage waiter))) **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg
      context_2.(flag_post_accumulator).(flag_post_scan_state) ** unmap_table_rep sg).
  { pose proof (UCOS2_fields_raw_rep_split_task_storage_sched_flag sg
      context_2.(flag_post_accumulator).(flag_post_scan_state)) as Hsplit.
    unfold UCOS2_fields_raw_rep, flag_fields_configured_rep in Hsplit.
    rewrite Hcfg in Hsplit; cbn [selected_kernel_configuration cfgFlagEnabled] in Hsplit.
    rewrite Hsplit.
    unfold flag_task_rdy_fields_pre, flag_task_rdy_fields_resources; entailer!. }
  unfold flag_post_helper_cut.
  entailer!; try (rewrite <- Hschedule; exact PreH3).
  lazymatch goal with |- _ |-- ?Q =>
    assert (Hpre_normalized :
      flag_fields_raw_rep sg context_2.(flag_post_accumulator).(flag_post_scan_state).(FlagState) **
      UCOS2_raw_rep_missing_flag sg context_2.(flag_post_accumulator).(flag_post_scan_state) **
      unmap_table_rep sg |-- Q)
      by (sep_apply_l_atomic Hpre; entailer!)
  end.
  sep_apply_r_atomic Hpre_normalized.
  rewrite (flag_post_node_word_resources_equiv__satisfied_helper_inputs sg _ id pnode
    image waiter PreH5 PreH4).
  destruct Hlayout as [Hnext [Hprev [Htcb [Hgroup Hhead]]]].
  destruct Hpostlayout as [_ [Hbits [Hmask Hmode]]].
  rewrite Hnext, Hprev, Htcb, Hgroup, Hbits, Hmask, Hmode, Hp.
  unfold flag_node_fields_rep; rewrite Hcfg.
  cbn [flag_word_rep selected_kernel_configuration cfgFlagBits flag_node_mode_offset flag_word_bytes].
  entailer!; try (rewrite <- Hp; assumption);
    try (rewrite <- Hp, <- Hschedule; exact PreH3).
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_17 : OSFlagPost_entail_wit_17.
Proof.
  unfold OSFlagPost_entail_wit_17; left; intros.
  pose proof (flag_post_error_restore_public_post environment critical sg pointer id requested option_word
    mask original before cpu_sr entry result released returned current returned_local 111 error_cell F X
    PreH3 PreH4 PreH12 PreH2 PreH11) as Hpost.
  sep_apply Hpost.
  sep_apply store_uint_undef_store_uint.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_18 : OSFlagPost_entail_wit_18.
Proof.
  left; intros.
  assert (Hvalid : UCOS2_state_inv sg
    (flag_post_scan_state (flag_post_accumulator context))).
  { unfold flag_post_loop_facts, flag_post_current_valid in PreH2; tauto. }
  assert (Hconfigured : valid_flag_configuration sg
    (FlagState (flag_post_scan_state (flag_post_accumulator context)))).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  pose proof (proj1 PreH1) as Hcfg.
  unfold valid_flag_configuration in Hconfigured; rewrite Hcfg in Hconfigured.
  destruct (valid_flag_state_node_position sg _ pnode waiter Hconfigured PreH3)
    as [group [prefix [suffix [_ [_ [_ [_ [_ [_ [_ [_ Hmode]]]]]]]]]]].
  destruct (flagWaitMode waiter); cbn [encode_flag_wait_mode] in Hmode; congruence.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_19_1 : OSFlagPost_entail_wit_19_1.
Proof.
  left; intros.
  prop_apply_p (store_ushort_range (&("flags_rdy")) flags_rdy); Intros.
  assert (Hbits : 0 <= flags_rdy < 65536) by lia.
  sep_apply_l_atomic (flag_post_task_rdy_next_resources__helper_outcomes
    environment critical sg pointer id requested option_word mask original before cpu_sr
    context_2 pnode (flag_post_schedule_word (flag_post_scan_visits (flag_post_accumulator context)))
    waiter flags_rdy retval PreH6 PreH3 PreH4 PreH5 Hbits).
  Intros scheduled pending.
  assert (Hscheduled : scheduled = true).
  { destruct scheduled; [reflexivity|].
    assert (retval = 0) by tauto; subst retval.
    vm_compute in PreH1; discriminate. }
  subst scheduled.
  Exists pending.
  sep_apply store_ushort_undef_store_ushort.
  sep_apply_l_atomic (store_uchar_undef_store_uchar (&("rdy")) retval).
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_19_2 : OSFlagPost_entail_wit_19_2.
Proof.
  left; intros.
  prop_apply_p (store_ushort_range (&("flags_rdy")) flags_rdy); Intros.
  assert (Hbits : 0 <= flags_rdy < 65536) by lia.
  sep_apply_l_atomic (flag_post_task_rdy_next_resources__helper_outcomes
    environment critical sg pointer id requested option_word mask original before cpu_sr
    context_2 pnode (flag_post_schedule_word (flag_post_scan_visits (flag_post_accumulator context)))
    waiter flags_rdy retval PreH6 PreH3 PreH4 PreH5 Hbits).
  Intros scheduled pending.
  assert (Hscheduled : scheduled = false).
  { destruct scheduled; [|reflexivity].
    assert (retval = 1) by tauto; subst retval.
    vm_compute in PreH1; contradiction. }
  subst scheduled.
  Exists pending.
  sep_apply store_ushort_undef_store_ushort.
  sep_apply_l_atomic (store_uchar_undef_store_uchar (&("rdy")) retval).
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_19_3 : OSFlagPost_entail_wit_19_3.
Proof.
  left; intros.
  pose proof PreH2 as [Hcfg [Hpointer [_ [_ [Hunlink [_ Hlayout]]]]]].
  pose proof (flag_post_loop_node_image__helper_outcomes environment critical sg pointer id
    requested option_word mask original before cpu_sr context pnode sched waiter image
    Hcfg PreH3 PreH4 PreH5) as [Hnode [Hrange Hposted]].
  assert (Hnonnull : pointer <> 0).
  { pose proof PreH3 as [[[H _] _] _]; exact H. }
  destruct Hpointer as [Hpointer|Hpointer]; [contradiction|].
  assert (Hcast : unsigned_last_nbits (flagNodeMask (flagWaitImage waiter)) 16 =
    flagNodeMask (flagWaitImage waiter)).
  { apply unsigned_last_nbits_eq; exact Hrange. }
  rewrite Hcast in PreH1.
  assert (Htest : flag_post_node_test (osKernelConfig sg) (flag_post_posted_word context)
    (flagNodeMask (flagWaitImage waiter)) (flagNodeMode (flagWaitImage waiter)) =
    Some ((Z.land (flagImageBits image) (flagNodeMask (flagWaitImage waiter))), false)).
  { rewrite Hcfg, Hposted, <- PreH21.
    rewrite flag_post_node_test_set_all.
    rewrite !flag_post_word_land_eq__helper_outcomes by exact Hrange.
    f_equal; f_equal; apply Z.eqb_neq; exact PreH1. }
  destruct Hunlink as [Hnext [Hprev [Htcb [Hgroup _]]]].
  destruct Hlayout as [_ [Hflags [Hmask Hmode]]].
  assert (Hflagsaddr : &((pointer) # "os_flag_grp" ->ₛ "OSFlagFlags") =
    flag_pool_addr sg id + 8) by (rewrite Hflags, Hpointer; reflexivity).
  rewrite Hnext, Hprev, Htcb, Hgroup, Hmask, Hmode, Hflagsaddr.
  assert (Hword : forall p bits, p # UShort |-> bits =
    flag_word_rep (osKernelConfig sg) p bits).
  { intros; rewrite Hcfg; reflexivity. }
  rewrite (Hword (flag_pool_addr sg id + 8) (flagImageBits image)).
  sep_apply_l_atomic (flag_post_node_word_frame_merge__helper_outcomes sg
    (flag_post_scan_state (flag_post_accumulator context)) id image PreH5 pnode).
  set (lease := {| stackLeaseRegion := os_execution_stack
      (flag_post_execution_view (flag_post_entered (flag_post_loop_entry context)));
    stackLeaseSlot := flagTask waiter; stackLeaseGeneration := flagTaskGeneration waiter |}).
  pose proof (flag_post_unsatisfied_next_resources__helper_outcomes environment critical sg pointer id
    requested option_word mask original before cpu_sr context pnode sched waiter (Z.land (flagImageBits image) (flagNodeMask (flagWaitImage waiter))) lease
    PreH3 PreH4 Hnode Htest) as Hnextcut.
  unfold flag_node_fields_return_loan in Hnextcut; rewrite Hnode, Hcfg in Hnextcut.
  rewrite flag_node_fields_rep_selected in Hnextcut.
  sep_apply_l_atomic Hnextcut.
  Intros pending; Exists pending.
  sep_apply store_ushort_undef_store_ushort.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_19_4 : OSFlagPost_entail_wit_19_4.
Proof.
  exact proof_of_OSFlagPost_entail_wit_19_1.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_19_5 : OSFlagPost_entail_wit_19_5.
Proof.
  exact proof_of_OSFlagPost_entail_wit_19_2.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_19_6 : OSFlagPost_entail_wit_19_6.
Proof.
  left; intros.
  pose proof PreH2 as [Hcfg [Hpointer [_ [_ [Hunlink [_ Hlayout]]]]]].
  pose proof (flag_post_loop_node_image__helper_outcomes environment critical sg pointer id
    requested option_word mask original before cpu_sr context pnode sched waiter image
    Hcfg PreH3 PreH4 PreH5) as [Hnode [Hrange Hposted]].
  assert (Hnonnull : pointer <> 0).
  { pose proof PreH3 as [[[H _] _] _]; exact H. }
  destruct Hpointer as [Hpointer|Hpointer]; [contradiction|].
  assert (Hcast : unsigned_last_nbits (flagNodeMask (flagWaitImage waiter)) 16 =
    flagNodeMask (flagWaitImage waiter)).
  { apply unsigned_last_nbits_eq; exact Hrange. }
  rewrite Hcast in PreH1.
  assert (Htest : flag_post_node_test (osKernelConfig sg) (flag_post_posted_word context)
    (flagNodeMask (flagWaitImage waiter)) (flagNodeMode (flagWaitImage waiter)) =
    Some ((Z.land (flagImageBits image) (flagNodeMask (flagWaitImage waiter))), false)).
  { rewrite Hcfg, Hposted, <- PreH22.
    rewrite flag_post_node_test_set_any.
    rewrite !flag_post_word_land_eq__helper_outcomes by exact Hrange.
    f_equal; f_equal; apply Bool.negb_false_iff; apply Z.eqb_eq; exact PreH1. }
  destruct Hunlink as [Hnext [Hprev [Htcb [Hgroup _]]]].
  destruct Hlayout as [_ [Hflags [Hmask Hmode]]].
  assert (Hflagsaddr : &((pointer) # "os_flag_grp" ->ₛ "OSFlagFlags") =
    flag_pool_addr sg id + 8) by (rewrite Hflags, Hpointer; reflexivity).
  rewrite Hnext, Hprev, Htcb, Hgroup, Hmask, Hmode, Hflagsaddr.
  assert (Hword : forall p bits, p # UShort |-> bits =
    flag_word_rep (osKernelConfig sg) p bits).
  { intros; rewrite Hcfg; reflexivity. }
  rewrite (Hword (flag_pool_addr sg id + 8) (flagImageBits image)).
  sep_apply_l_atomic (flag_post_node_word_frame_merge__helper_outcomes sg
    (flag_post_scan_state (flag_post_accumulator context)) id image PreH5 pnode).
  set (lease := {| stackLeaseRegion := os_execution_stack
      (flag_post_execution_view (flag_post_entered (flag_post_loop_entry context)));
    stackLeaseSlot := flagTask waiter; stackLeaseGeneration := flagTaskGeneration waiter |}).
  pose proof (flag_post_unsatisfied_next_resources__helper_outcomes environment critical sg pointer id
    requested option_word mask original before cpu_sr context pnode sched waiter (Z.land (flagImageBits image) (flagNodeMask (flagWaitImage waiter))) lease
    PreH3 PreH4 Hnode Htest) as Hnextcut.
  unfold flag_node_fields_return_loan in Hnextcut; rewrite Hnode, Hcfg in Hnextcut.
  rewrite flag_node_fields_rep_selected in Hnextcut.
  sep_apply_l_atomic Hnextcut.
  Intros pending; Exists pending.
  sep_apply store_ushort_undef_store_ushort.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_19_7 : OSFlagPost_entail_wit_19_7.
Proof.
  exact proof_of_OSFlagPost_entail_wit_19_1.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_19_8 : OSFlagPost_entail_wit_19_8.
Proof.
  exact proof_of_OSFlagPost_entail_wit_19_2.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_19_9 : OSFlagPost_entail_wit_19_9.
Proof.
  left; intros.
  pose proof PreH2 as [Hcfg [Hpointer [_ [_ [Hunlink [_ Hlayout]]]]]].
  pose proof (flag_post_loop_node_image__helper_outcomes environment critical sg pointer id
    requested option_word mask original before cpu_sr context pnode sched waiter image
    Hcfg PreH3 PreH4 PreH5) as [Hnode [Hrange Hposted]].
  assert (Hnonnull : pointer <> 0).
  { pose proof PreH3 as [[[H _] _] _]; exact H. }
  destruct Hpointer as [Hpointer|Hpointer]; [contradiction|].
  assert (Hcast : unsigned_last_nbits (flagNodeMask (flagWaitImage waiter)) 16 =
    flagNodeMask (flagWaitImage waiter)).
  { apply unsigned_last_nbits_eq; exact Hrange. }
  rewrite Hcast in PreH1.
  assert (Htest : flag_post_node_test (osKernelConfig sg) (flag_post_posted_word context)
    (flagNodeMask (flagWaitImage waiter)) (flagNodeMode (flagWaitImage waiter)) =
    Some ((Z.land (Z.lnot (flagImageBits image)) (flagNodeMask (flagWaitImage waiter))), false)).
  { rewrite Hcfg, Hposted, <- PreH23.
    rewrite flag_post_node_test_clear_all.
    rewrite !flag_post_word_land_eq__helper_outcomes by exact Hrange.
    f_equal; f_equal; apply Z.eqb_neq; exact PreH1. }
  destruct Hunlink as [Hnext [Hprev [Htcb [Hgroup _]]]].
  destruct Hlayout as [_ [Hflags [Hmask Hmode]]].
  assert (Hflagsaddr : &((pointer) # "os_flag_grp" ->ₛ "OSFlagFlags") =
    flag_pool_addr sg id + 8) by (rewrite Hflags, Hpointer; reflexivity).
  rewrite Hnext, Hprev, Htcb, Hgroup, Hmask, Hmode, Hflagsaddr.
  assert (Hword : forall p bits, p # UShort |-> bits =
    flag_word_rep (osKernelConfig sg) p bits).
  { intros; rewrite Hcfg; reflexivity. }
  rewrite (Hword (flag_pool_addr sg id + 8) (flagImageBits image)).
  sep_apply_l_atomic (flag_post_node_word_frame_merge__helper_outcomes sg
    (flag_post_scan_state (flag_post_accumulator context)) id image PreH5 pnode).
  set (lease := {| stackLeaseRegion := os_execution_stack
      (flag_post_execution_view (flag_post_entered (flag_post_loop_entry context)));
    stackLeaseSlot := flagTask waiter; stackLeaseGeneration := flagTaskGeneration waiter |}).
  pose proof (flag_post_unsatisfied_next_resources__helper_outcomes environment critical sg pointer id
    requested option_word mask original before cpu_sr context pnode sched waiter (Z.land (Z.lnot (flagImageBits image)) (flagNodeMask (flagWaitImage waiter))) lease
    PreH3 PreH4 Hnode Htest) as Hnextcut.
  unfold flag_node_fields_return_loan in Hnextcut; rewrite Hnode, Hcfg in Hnextcut.
  rewrite flag_node_fields_rep_selected in Hnextcut.
  sep_apply_l_atomic Hnextcut.
  Intros pending; Exists pending.
  sep_apply store_ushort_undef_store_ushort.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_19_10 : OSFlagPost_entail_wit_19_10.
Proof.
  exact proof_of_OSFlagPost_entail_wit_19_1.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_19_11 : OSFlagPost_entail_wit_19_11.
Proof.
  exact proof_of_OSFlagPost_entail_wit_19_2.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_19_12 : OSFlagPost_entail_wit_19_12.
Proof.
  left; intros.
  pose proof PreH2 as [Hcfg [Hpointer [_ [_ [Hunlink [_ Hlayout]]]]]].
  pose proof (flag_post_loop_node_image__helper_outcomes environment critical sg pointer id
    requested option_word mask original before cpu_sr context pnode sched waiter image
    Hcfg PreH3 PreH4 PreH5) as [Hnode [Hrange Hposted]].
  assert (Hnonnull : pointer <> 0).
  { pose proof PreH3 as [[[H _] _] _]; exact H. }
  destruct Hpointer as [Hpointer|Hpointer]; [contradiction|].
  assert (Hcast : unsigned_last_nbits (flagNodeMask (flagWaitImage waiter)) 16 =
    flagNodeMask (flagWaitImage waiter)).
  { apply unsigned_last_nbits_eq; exact Hrange. }
  rewrite Hcast in PreH1.
  assert (Htest : flag_post_node_test (osKernelConfig sg) (flag_post_posted_word context)
    (flagNodeMask (flagWaitImage waiter)) (flagNodeMode (flagWaitImage waiter)) =
    Some ((Z.land (Z.lnot (flagImageBits image)) (flagNodeMask (flagWaitImage waiter))), false)).
  { rewrite Hcfg, Hposted, <- PreH24.
    rewrite flag_post_node_test_clear_any.
    rewrite !flag_post_word_land_eq__helper_outcomes by exact Hrange.
    f_equal; f_equal; apply Bool.negb_false_iff; apply Z.eqb_eq; exact PreH1. }
  destruct Hunlink as [Hnext [Hprev [Htcb [Hgroup _]]]].
  destruct Hlayout as [_ [Hflags [Hmask Hmode]]].
  assert (Hflagsaddr : &((pointer) # "os_flag_grp" ->ₛ "OSFlagFlags") =
    flag_pool_addr sg id + 8) by (rewrite Hflags, Hpointer; reflexivity).
  rewrite Hnext, Hprev, Htcb, Hgroup, Hmask, Hmode, Hflagsaddr.
  assert (Hword : forall p bits, p # UShort |-> bits =
    flag_word_rep (osKernelConfig sg) p bits).
  { intros; rewrite Hcfg; reflexivity. }
  rewrite (Hword (flag_pool_addr sg id + 8) (flagImageBits image)).
  sep_apply_l_atomic (flag_post_node_word_frame_merge__helper_outcomes sg
    (flag_post_scan_state (flag_post_accumulator context)) id image PreH5 pnode).
  set (lease := {| stackLeaseRegion := os_execution_stack
      (flag_post_execution_view (flag_post_entered (flag_post_loop_entry context)));
    stackLeaseSlot := flagTask waiter; stackLeaseGeneration := flagTaskGeneration waiter |}).
  pose proof (flag_post_unsatisfied_next_resources__helper_outcomes environment critical sg pointer id
    requested option_word mask original before cpu_sr context pnode sched waiter (Z.land (Z.lnot (flagImageBits image)) (flagNodeMask (flagWaitImage waiter))) lease
    PreH3 PreH4 Hnode Htest) as Hnextcut.
  unfold flag_node_fields_return_loan in Hnextcut; rewrite Hnode, Hcfg in Hnextcut.
  rewrite flag_node_fields_rep_selected in Hnextcut.
  sep_apply_l_atomic Hnextcut.
  Intros pending; Exists pending.
  sep_apply store_ushort_undef_store_ushort.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_20 : OSFlagPost_entail_wit_20.
Proof.
  left; intros.
  unfold flag_post_next_frame; Intros.
  destruct H as [Hloop [Hpending Hcurrent]].
  destruct pending as [context waiter ready returned post lease].
  destruct context as [entry posted initial visited remaining scan local].
  cbn [flag_post_pending_loop flag_post_pending_waiter flag_post_pending_ready
    flag_post_pending_returned flag_post_pending_state flag_post_pending_lease
    flag_post_loop_entry flag_post_posted_word flag_post_initial_order flag_post_visited
    flag_post_remaining flag_post_accumulator flag_post_loop_local] in *.
  unfold flag_post_pending_facts in Hpending; cbn in Hpending.
  destruct Hpending as [Hnode [Hlookup [Haddr [Hbranch Hschedule]]]].
  unfold flag_post_loop_facts in Hloop; cbn in Hloop.
  destruct Hloop as [Hentry [Hstate [_ [_ Hvalid]]]].
  pose proof (proj1 PreH1) as Hcfg.
  assert (Hflags : valid_flag_state sg (FlagState (flag_post_scan_state scan))).
  { destruct Hvalid as [Hinv _].
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hinv.
    assert (Hconfigured : valid_flag_configuration sg (FlagState (flag_post_scan_state scan))) by tauto.
    unfold valid_flag_configuration in Hconfigured; rewrite Hcfg in Hconfigured; exact Hconfigured. }
  assert (Hnonzero : pnode <> 0).
  { eapply valid_flag_state_node_nonzero; eassumption. }
  destruct remaining as [|head rest]; [cbn in Hnode; contradiction|].
  cbn in Hnode; subst head.
  destruct Hstate as [group [im [Hgroup [Him [Htype [Hbits [Hinitial [Hpartition
    [Hscan [Herr [cg [ci [kept [Hcg [Hci [Hcb Horder]]]]]]]]]]]]]]]].
  pose proof Hflags as [_ [_ [_ [Hused _]]]].
  destruct (Hused id cg Hcg) as [[Hword Hnodup] [_ [Hwait Himage]]].
  destruct (Hwait kept pnode rest Horder) as [other [Hother Hfields]].
  assert (other = waiter) by congruence; subst other.
  assert (Hgid : flagGroup waiter = id) by tauto.
  assert (Hnext : flagNodeNext (flagWaitImage waiter) = hd 0 rest) by tauto.
  unfold flag_post_next_is in PreH2; cbn in PreH2.
  assert (Hremaining_next : next = flag_post_remaining_node rest).
  { rewrite PreH2, Hnext; destruct rest; reflexivity. }
  assert (Hnext_layout : &(pnode # "os_flag_node" ->ₛ "OSFlagNodeNext") = pnode).
  { unfold flag_post_parameters in PreH1; destruct PreH1 as [_ [_ [_ [_ [Hlayout _]]]]].
    exact (proj1 Hlayout pnode). }
  rewrite Hnext_layout, PreH2.
  sep_apply_l_atomic (flag_node_fields_rep_merge_next (osKernelConfig sg) pnode (flagWaitImage waiter)).
  assert (Hloan : flag_node_fields_rep (osKernelConfig sg) pnode (flagWaitImage waiter) =
    flag_node_fields_return_loan (osKernelConfig sg) waiter).
  { unfold flag_node_fields_return_loan; rewrite Haddr; reflexivity. }
  rewrite Hloan.
  set (nscan := flag_post_scan_append scan post
    (flag_post_visit pnode waiter (Some ready) returned
      (Some (flagNodeNext (flagWaitImage waiter)))) None).
  assert (Hstep : flag_post_scan_step sg posted (Some scan) pnode = Some nscan).
  { unfold nscan.
    destruct returned as [r|].
    - destruct Hbranch as [Htest [Hcall Hrest]].
      eapply flag_post_scan_satisfied_call; eassumption.
    - destruct Hbranch as [Htest Hpost]; subst post.
      eapply flag_post_scan_unsatisfied; eassumption. }
  assert (Hpost_order : exists cgroup cimage prefix,
    flagUsed (FlagState post) id = Some cgroup /\
    flagImages (FlagState post) id = Some cimage /\
    flagImageBits cimage = posted /\ flagWaitOrder cgroup = prefix ++ rest).
  { destruct returned as [r|].
    - destruct Hbranch as [Htest [Hcall Hrest]].
      destruct (flag_task_rdy_result _ _ _ _ _ _ _ Hcall)
        as [w [flags [old [Hunlink [Htask [Hpost Hrdy]]]]]].
      pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hunlink)) as Hw.
      assert (w = waiter) by congruence; subst w.
      pose proof (flag_unlink_group_fields _ _ _ _ _ _ Hunlink
        (eq_ind_r (fun k => flagUsed (FlagState (flag_post_scan_state scan)) k = Some cg) Hcg Hgid)
        (eq_ind_r (fun k => flagImages (FlagState (flag_post_scan_state scan)) k = Some ci) Hci Hgid))
        as [Hused_after [Himages_after Hother_fields]].
      assert (Hremove : remove Z.eq_dec pnode (flagWaitOrder cg) = kept ++ rest).
      { rewrite Horder in Hnodup |- *.
        pose proof (NoDup_remove_2 kept rest pnode Hnodup) as Hnotin.
        rewrite remove_app, remove_cons.
        rewrite !notin_remove; try reflexivity.
        - intro Hin; apply Hnotin; apply in_or_app; right; exact Hin.
        - intro Hin; apply Hnotin; apply in_or_app; left; exact Hin. }
      rewrite Hpost; cbn [flag_wake_state replace_FlagS FlagState].
      exists (flag_group_set_wait_order cg (kept ++ rest)).
      rewrite Hused_after, Hgid, kernel_resources.kernel_map_set_same, Hremove.
      rewrite Himages_after, Hgid.
      destruct (Z.eqb (flagNodePrev (flagWaitImage waiter)) 0).
      + rewrite kernel_resources.kernel_map_set_same.
        exists (flag_image_set_head ci (flagNodeNext (flagWaitImage waiter))), kept.
        cbn; auto.
      + exists ci, kept; cbn; auto.
    - destruct Hbranch as [Htest Hpost]; subst post.
      exists cg, ci, (kept ++ (pnode :: nil)).
      repeat split; try assumption.
      rewrite Horder, <- app_assoc; reflexivity. }
  assert (Hstate_after : flag_post_loop_state sg id requested option_word
    (flag_post_acquired entry) posted initial (visited ++ (pnode :: nil)) rest nscan).
  { unfold flag_post_loop_state.
    exists group, im; repeat split; try assumption.
    - rewrite Hpartition, <- app_assoc; reflexivity.
    - rewrite flag_post_scan_visited_extension, Hscan.
      cbn [fold_left]; exact Hstep. }
  assert (Hschedule_after : sched = flag_post_schedule_word (flag_post_scan_visits nscan)).
  { unfold nscan, flag_post_scan_append, flag_post_schedule_word; cbn.
    rewrite flag_post_schedule_append; exact Hschedule. }
  assert (Hnode_after : flagNodeNext (flagWaitImage waiter) = flag_post_remaining_node rest).
  { rewrite Hnext; destruct rest; reflexivity. }
  destruct returned as [r|].
  - destruct Hbranch as [Htest [Hcall [Hkey [fragments Hparked]]]].
    destruct (flag_task_rdy_result _ _ _ _ _ _ _ Hcall)
      as [w [flags [old [Hunlink [Htask [Hpost Hrdy]]]]]].
    pose proof (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hunlink) as [Hw Hnone].
    assert (w = waiter) by congruence; subst w.
    assert (Hpost_none : flagWaitNodes (FlagState post) pnode = None).
    { rewrite Hpost; exact Hnone. }
    assert (Hpost_parked : parkedTaskStacks (TskState post) (task_stack_key lease) =
      Some (stackLeaseRegion lease, fragments)).
    { rewrite Hpost; exact Hparked. }
    unfold flag_post_pending_world; cbn [flag_post_pending_returned flag_post_pending_state].
    unfold flag_post_critical_frame; Intros.
    sep_apply_l_atomic (flag_continuation_fields_resources_spec.flag_wake_fields_publish_returned_node
      _ _ _ (task_stack_call_continuations environment) sg post pnode waiter lease local fragments
      Haddr Hpost_none Hkey Hpost_parked).
    Exists {| flag_post_loop_entry := entry; flag_post_posted_word := posted;
      flag_post_initial_order := initial; flag_post_visited := visited ++ (pnode :: nil);
      flag_post_remaining := rest; flag_post_accumulator := nscan;
      flag_post_loop_local := flag_continuation_resources_spec.flag_continuation_local_node lease
        (flag_continuation_fields_resources_spec.flag_pend_sched_node_fields_rep sg pnode post) local |}.
    unfold flag_post_loop_cut, flag_post_loop_facts; cbn.
    unfold flag_post_source_masked, flag_post_masked,
      kernel_continuation_world_spec.kernel_continuation_inv.
    destruct Hcurrent as [Hpost_valid [Hcoverage Hsource]].
    entailer!.
    unfold flag_post_current_valid; auto.
  - destruct Hbranch as [Htest Hpost]; subst post.
    unfold flag_post_pending_world; cbn [flag_post_pending_returned flag_post_pending_state].
    Intros.
    assert (Hmerge : flag_node_fields_return_loan (osKernelConfig sg) waiter **
      flag_post_registered_node_frame sg (flag_post_scan_state scan) pnode |--
      kernel_program_fields_inv sg (flag_post_scan_state scan)).
    { rewrite (flag_post_registered_node_resources sg (flag_post_scan_state scan) pnode waiter Hcfg Hlookup).
      unfold flag_node_fields_return_loan; rewrite Haddr; entailer!. }
    sep_apply_l_atomic Hmerge.
    Exists {| flag_post_loop_entry := entry; flag_post_posted_word := posted;
      flag_post_initial_order := initial; flag_post_visited := visited ++ (pnode :: nil);
      flag_post_remaining := rest; flag_post_accumulator := nscan; flag_post_loop_local := local |}.
    unfold flag_post_loop_cut, flag_post_loop_facts; cbn.
    unfold flag_post_source_masked, flag_post_masked, flag_post_critical_frame,
      kernel_continuation_world_spec.kernel_continuation_inv.
    destruct Hcurrent as [Hpost_valid [Hcoverage Hsource]].
    entailer!.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_22 : OSFlagPost_entail_wit_22.
Proof.
  left; intros.
  unfold flag_post_loop_cut; Intros.
  rename H into Hloop.
  pose proof Hloop as [Hentry [Hstate [Hnode [Hschedule Hcurrent]]]].
  destruct Hstate as [group [im [Hgroup [Him [Htype [Hbits [Hinitial [Hpartition
    [Hscan [Herr [cg [ci [kept [Hcg [Hci [Hcb Horder]]]]]]]]]]]]]]]].
  assert (Hflag : valid_flag_state sg
    (FlagState (flag_post_scan_state (flag_post_accumulator context)))).
  { destruct Hcurrent as [Hinv _].
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hinv.
    assert (Hcfg := proj1 PreH2).
    assert (Hconfigured : valid_flag_configuration sg
      (FlagState (flag_post_scan_state (flag_post_accumulator context)))) by tauto.
    unfold valid_flag_configuration in Hconfigured; rewrite Hcfg in Hconfigured.
    exact Hconfigured. }
  assert (Hremaining : flag_post_remaining context = nil).
  { destruct (flag_post_remaining context) as [|head tail] eqn:Hremaining; [reflexivity|].
    cbn [flag_post_remaining_node] in Hnode.
    assert (Hnonzero : head <> 0).
    { eapply valid_flag_wait_order_nonzero; [exact Hflag|exact Hcg|].
      rewrite Horder; apply in_or_app; right; simpl; auto. }
    exfalso; apply Hnonzero; lia. }
  assert (Hprogram : flag_post_protected_program sg id requested option_word
    (flag_post_acquired (flag_post_loop_entry context))
    (FlagPostProtectedScanned (flag_post_posted_word context)
      (flag_post_scan_visits (flag_post_accumulator context)) None)
    (flag_post_scan_state (flag_post_accumulator context))).
  { unfold flag_post_protected_program.
    exists im; split; [exact Him|].
    rewrite Htype; cbn [Z.eqb negb]; rewrite Bool.andb_false_r, Hbits.
    exists group, (flag_post_accumulator context).
    split; [exact Hgroup|]. split.
    - rewrite <- Hinitial, Hpartition, Hremaining, app_nil_r; exact Hscan.
    - rewrite Herr; auto. }
  assert (Hsuccess : flag_post_result_success
    (FlagPostProtectedScanned (flag_post_posted_word context)
      (flag_post_scan_visits (flag_post_accumulator context)) None) sched).
  { unfold flag_post_result_success, flag_post_protected_error,
      flag_post_protected_schedule; split; [reflexivity|exact Hschedule]. }
  Exists (flag_post_loop_entry context)
    (flag_post_scan_state (flag_post_accumulator context))
    (flag_post_loop_local context)
    (FlagPostProtectedScanned (flag_post_posted_word context)
      (flag_post_scan_visits (flag_post_accumulator context)) None).
  unfold flag_post_exit_cut.
  sep_apply store_ptr_undef_store_ptr.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_23 : OSFlagPost_entail_wit_23.
Proof.
  left; intros.
  Exists ({| flag_post_released_entry := entry;
             flag_post_released_result := result;
             flag_post_released_state := released;
             flag_post_released_execution := returned;
             flag_post_restored_state := current;
             flag_post_restored_local := returned_local |}).
  unfold flag_post_restored_cut, flag_post_restored_facts,
    flag_post_success_result; cbn.
  unfold flag_post_protected_run in PreH4.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_24_1 : OSFlagPost_entail_wit_24_1.
Proof.
  left; intros.
  assert (Hscheduled : flag_post_scheduled_facts environment critical sg pointer id
    requested option_word mask original before cpu_sr released_context returned current_2).
  { unfold flag_post_scheduled_facts.
    split; [exact PreH6|].
    unfold flag_post_success_result, flag_post_result_success in PreH5.
    destruct PreH5 as [Herror Hschedule].
    split; [exact Herror|].
    destruct (flag_post_protected_schedule (flag_post_released_result released_context));
      [exact PreH1|discriminate]. }
  Exists returned_local released_context returned current_2.
  sep_apply store_uchar_undef_store_uchar.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_24_2 : OSFlagPost_entail_wit_24_2.
Proof.
  left; intros.
  unfold flag_post_restored_cut; Intros.
  assert (Hscheduled : flag_post_scheduled_facts environment critical sg pointer id
    requested option_word mask original before cpu_sr released_context
    (flag_post_released_execution released_context) (flag_post_restored_state released_context)).
  { unfold flag_post_scheduled_facts.
    split; [exact H|].
    unfold flag_post_success_result, flag_post_result_success in PreH9.
    destruct PreH9 as [Herror Hschedule].
    split; [exact Herror|].
    destruct (flag_post_protected_schedule (flag_post_released_result released_context)).
    - subst sched; exfalso; apply PreH1; reflexivity.
    - split; reflexivity. }
  Exists (flag_post_restored_local released_context) released_context
    (flag_post_released_execution released_context) (flag_post_restored_state released_context).
  sep_apply store_uchar_undef_store_uchar.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_25 : OSFlagPost_entail_wit_25.
Proof.
  left; intros.
  rewrite flag_post_save_output_resources.
  Intros reader acquired next_local.
  rename H into Hsave.
  assert (Hgetvalid : flag_post_source_masked environment critical next_local sg reader retval acquired acquired
    |-- coq_prop (flag_post_current_valid sg reader acquired)).
  { unfold flag_post_source_masked, flag_post_masked,
      kernel_continuation_world_spec.kernel_continuation_inv,
      kernel_program_fields_inv, flag_post_current_valid.
    entailer!. }
  prop_apply_p Hgetvalid; Intros.
  rename H into Hvalid.
  pose proof PreH1 as [Hcfg _].
  pose proof PreH8 as [Hrest [Herror Hschedule]].
  pose proof Hrest as [Hentry [Hprotected Hrestore]].
  destruct Hentry as [Hprefix [Hfirst_inv Hfirst_rest]].
  destruct Hprotected as [first_image [Hfirst_image Hfirst_effect]].
  assert (Hfirst_flags : valid_flag_configuration sg
    (FlagState (flag_post_acquired (flag_post_released_entry prefix)))).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hfirst_inv; tauto. }
  unfold valid_flag_configuration in Hfirst_flags; rewrite Hcfg in Hfirst_flags.
  cbn [selected_kernel_configuration cfgFlagEnabled] in Hfirst_flags.
  destruct Hfirst_flags as [_ [Hfirst_domain _]].
  pose proof (proj1 (Hfirst_domain id) (ex_intro _ first_image Hfirst_image)) as Hid.
  assert (Hcurrent_flags : valid_flag_configuration sg (FlagState acquired)).
  { pose proof (proj1 Hvalid) as Hinv.
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hinv; tauto. }
  unfold valid_flag_configuration in Hcurrent_flags; rewrite Hcfg in Hcurrent_flags.
  cbn [selected_kernel_configuration cfgFlagEnabled] in Hcurrent_flags.
  destruct Hcurrent_flags as [_ [Hcurrent_domain _]].
  destruct (proj2 (Hcurrent_domain id) Hid) as [image Himage].
  Exists cpu_sr {| flag_post_read_prefix := prefix;
    flag_post_scheduled_execution := scheduled;
    flag_post_scheduled_state := current;
    flag_post_reader := reader;
    flag_post_read_state := acquired;
    flag_post_read_image := image;
    flag_post_read_local := next_local |}.
  unfold flag_post_read_cut, flag_post_caller_frame; cbn.
  entailer!.
  unfold flag_post_read_facts; cbn.
  exact (conj Hrest (conj Herror (conj Hschedule (conj Hsave (conj Himage Hvalid))))).
Qed. 

Lemma proof_of_OSFlagPost_entail_wit_26 : OSFlagPost_entail_wit_26.
Proof.
  left; intros.
  pose proof (flag_post_read_restore_public_post environment critical sg pointer id requested option_word
    mask original before first_saved cpu_sr read_context returned current returned_local error_cell F X
    PreH4 PreH2 PreH13) as Hpost.
  sep_apply_l_atomic Hpost.
  sep_apply store_uint_undef_store_uint.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_partial_solve_wit_5_pure : OSFlagPost_partial_solve_wit_5_pure.
Proof.
  unfold OSFlagPost_partial_solve_wit_5_pure; left; intros.
  prop_apply (store_uchar_range (&(pointer # "os_flag_grp" ->ₛ "OSFlagType")) (flagImageType image)).
  Intros.
  assert (Htype : flagImageType image = 5).
  { unfold unsigned_last_nbits in PreH1.
    rewrite Z.mod_small in PreH1; [exact PreH1|].
    change (0 <= flagImageType image < 4294967296); change (0 <= flagImageType image <= 255) in H; lia. }
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_partial_solve_wit_10_pure : OSFlagPost_partial_solve_wit_10_pure.
Proof.
  unfold OSFlagPost_partial_solve_wit_10_pure; left; intros.
  pose proof PreH1 as [[Hp [Hi [Ht [Hsaved Hsave]]]] Hvalid].
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_partial_solve_wit_12_pure : OSFlagPost_partial_solve_wit_12_pure.
Proof.
  unfold OSFlagPost_partial_solve_wit_12_pure; left; intros.
  prop_apply (store_uchar_range (&(pointer # "os_flag_grp" ->ₛ "OSFlagType")) (flagImageType image)).
  Intros.
  assert (Htype : flagImageType image = 5).
  { unfold unsigned_last_nbits in PreH1.
    rewrite Z.mod_small in PreH1; [exact PreH1|].
    change (0 <= flagImageType image < 4294967296); change (0 <= flagImageType image <= 255) in H; lia. }
  unfold flag_post_checked_type; entailer!.
Qed. 

Lemma proof_of_OSFlagPost_partial_solve_wit_13_pure : OSFlagPost_partial_solve_wit_13_pure.
Proof.
  unfold OSFlagPost_partial_solve_wit_13_pure; left; intros.
  prop_apply (store_uchar_range (&(pointer # "os_flag_grp" ->ₛ "OSFlagType")) (flagImageType image)).
  Intros.
  assert (Htype : flagImageType image = 5).
  { unfold unsigned_last_nbits in PreH1.
    rewrite Z.mod_small in PreH1; [exact PreH1|].
    change (0 <= flagImageType image < 4294967296); change (0 <= flagImageType image <= 255) in H; lia. }
  unfold flag_post_checked_type; entailer!.
Qed. 

Lemma proof_of_OSFlagPost_partial_solve_wit_14_pure : OSFlagPost_partial_solve_wit_14_pure.
Proof.
  unfold OSFlagPost_partial_solve_wit_14_pure; left; intros.
  assert (Hoption_range : 0 <= option_word < 256) by (destruct PreH3 as [? [? [? [? ?]]]]; assumption).
  assert (Hoption : unsigned_last_nbits option_word 32 = option_word).
  { unfold unsigned_last_nbits; apply Z.mod_small; change (0 <= option_word < 4294967296); lia. }
  rewrite Hoption in PreH1, PreH2.
  assert (Hchecked : flag_post_checked_type option_word image).
  { unfold flag_post_checked_type; intro Hvalid.
    apply flag_post_valid_option_iff in Hvalid; lia. }
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_partial_solve_wit_16_pure : OSFlagPost_partial_solve_wit_16_pure.
Proof.
  unfold OSFlagPost_partial_solve_wit_16_pure; left; intros.
  pose proof PreH1 as [[Hp [Hi [Ht [Hsaved Hsave]]]] Hvalid].
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_partial_solve_wit_29_pure : OSFlagPost_partial_solve_wit_29_pure.
Proof.
  unfold OSFlagPost_partial_solve_wit_29_pure; left; intros.
  pose proof PreH1 as [[Hp [Hi [Ht [Hsaved Hsave]]]] Hvalid].
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_partial_solve_wit_33_pure : OSFlagPost_partial_solve_wit_33_pure.
Proof.
  left; intros.
  pose proof PreH1 as [[_ [_ [_ Hsave]]] _].
  pose proof (proj1 Hsave) as Hsaved.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_partial_solve_wit_35_pure : OSFlagPost_partial_solve_wit_35_pure.
Proof.
  left; intros.
  assert (Hsched : sched = 1).
  { unfold flag_post_success_result, flag_post_result_success in PreH9.
    destruct PreH9 as [Herror Hschedule].
    destruct (flag_post_protected_schedule (flag_post_released_result released_context));
      [exact Hschedule|].
    subst sched; discriminate PreH1. }
  subst sched; entailer!.
Qed. 

Lemma proof_of_OSFlagPost_partial_solve_wit_42_pure : OSFlagPost_partial_solve_wit_42_pure.
Proof.
  left; intros.
  pose proof PreH2 as [_ [_ [_ [Hsave _]]]].
  pose proof (proj1 Hsave) as Hsaved.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_1 : OSFlagPost_which_implies_wit_1.
Proof.
  left; intros.
  unfold flag_post_public_pre; Intros.
  destruct H as [Henv [Hsg [Hparams [Himage Hsafe]]]].
  sep_apply_l_atomic (flag_post_actual_call_entry_resources linked original mask before local
    pointer requested option_word error_cell old_error F).
  rewrite Henv, Hsg.
  unfold flag_post_pointer_image; entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_2 : OSFlagPost_which_implies_wit_2.
Proof.
  left; intros.
  destruct (PreH2 PreH3) as [image Himage].
  pose proof PreH1 as (Hcfg & Hpointer & Hr & Ho & Hu & Hstack & Htype & Hflags & Hnode & Hwait).
  destruct Hpointer as [Hz | Hp]; [contradiction |].
  assert (Henabled : cfgFlagEnabled (osKernelConfig sg) = true) by (rewrite Hcfg; reflexivity).
  unfold flag_post_source_closed, flag_post_closed,
    kernel_continuation_world_spec.kernel_continuation_inv,
    kernel_program_fields_inv, kernel_program_fields_rep,
    UCOS2_fields_raw_rep, flag_fields_configured_rep.
  rewrite Henabled; Intros.
  sep_apply_l_atomic (proj1 (flag_fields_raw_rep_split_group sg (FlagState before) id image Himage)).
  Exists image.
  rewrite Hp in *; rewrite Htype.
  unfold flag_post_type_frame, flag_post_group_frame, flag_post_execution_frame,
    flag_group_rep, flag_post_image_at, flag_post_current_valid.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_3 : OSFlagPost_which_implies_wit_3.
Proof.
  left; intros.
  assert (Hinitial : flag_post_initial_type_ok before id).
  { exists image; split; assumption. }
  pose proof PreH1 as (Hcfg & Hpointer & Hr & Ho & Hu & Hstack & Htype & Hflags & Hnode & Hwait).
  destruct Hpointer as [Hz | Hp]; [contradiction |].
  assert (Henabled : cfgFlagEnabled (osKernelConfig sg) = true) by (rewrite Hcfg; reflexivity).
  unfold flag_post_source_closed, flag_post_closed,
    kernel_continuation_world_spec.kernel_continuation_inv,
    kernel_program_fields_inv, kernel_program_fields_rep,
    UCOS2_fields_raw_rep, flag_fields_configured_rep,
    flag_post_type_frame, flag_post_group_frame, flag_post_execution_frame.
  rewrite Hp in *; rewrite Henabled, Htype.
  destruct PreH3 as (Hinv & Hcoverage & Hobservation).
  rewrite (flag_fields_raw_rep_split_group sg (FlagState before) id image PreH4).
  unfold flag_group_rep; entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_4 : OSFlagPost_which_implies_wit_4.
Proof.
  left; intros.
  unfold flag_post_caller_frame.
  sep_apply_r_atomic (flag_post_save_input_capture environment critical local sg original mask before (error_cell # UChar |-> old_error ** F)).
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_5 : OSFlagPost_which_implies_wit_5.
Proof.
  left; intros.
  unfold flag_post_protected_cut; Intros.
  destruct H as [Hrange Hfacts].
  pose proof Hfacts as [Hprefix [Hinv [Hcoverage Hobservation]]].
  pose proof PreH1 as (Hcfg & Hpointer & Hr & Ho & Hu & Hstack & Htype & Hflags & Hnode & Hwait).
  destruct Hprefix as [Hnonzero Hprefix].
  destruct Hpointer as [Hz | Hp]; [contradiction |].
  assert (Henabled : cfgFlagEnabled (osKernelConfig sg) = true) by (rewrite Hcfg; reflexivity).
  pose proof Hinv as Hstate_inv.
  destruct Hstate_inv as [_ [_ [_ [_ [_ [_ [_ [Hflag_inv _]]]]]]]].
  unfold valid_flag_configuration in Hflag_inv; rewrite Henabled in Hflag_inv.
  destruct Hflag_inv as [_ [Hdomain _]].
  destruct (proj2 (Hdomain id) Hrange) as [image Himage].
  unfold flag_post_source_masked, flag_post_masked,
    kernel_continuation_world_spec.kernel_continuation_inv,
    kernel_program_fields_inv, kernel_program_fields_rep,
    UCOS2_fields_raw_rep, flag_fields_configured_rep.
  rewrite Henabled; Intros.
  sep_apply_l_atomic (proj1 (flag_fields_raw_rep_split_group sg
    (FlagState (flag_post_acquired entry_2)) id image Himage)).
  Exists image entry_2.
  rewrite Hp in *; rewrite Htype.
  unfold flag_post_type_frame, flag_post_group_frame, flag_post_critical_frame,
    flag_group_rep, flag_post_image_at.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_6 : OSFlagPost_which_implies_wit_6.
Proof.
  left; intros.
  unfold flag_post_exit_cut.
  Intros.
  unfold flag_post_caller_frame.
  rewrite (flag_post_restore_input_capture environment critical active_local sg (flag_post_entered entry) mask cpu_sr (flag_post_acquired entry) released (error_cell # UChar |-> old_error ** F)).
  Intros captured. Exists captured. entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_7 : OSFlagPost_which_implies_wit_7.
Proof.
  left; intros.
  sep_apply_l_atomic (flag_post_restore_output_resources environment critical sg (flag_post_entered entry) mask cpu_sr (flag_post_acquired entry) released active_local (flag_post_caller_frame error_cell old_error F) captured).
  Intros returned current returned_local.
  Exists returned_local returned current.
  unfold flag_post_caller_frame. entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_8 : OSFlagPost_which_implies_wit_8.
Proof.
  left; intros.
  pose proof PreH1 as (Hcfg & Hp & Hr & Ho & Hu & Hstack & Htype & Hflags & Hnode & Hwait).
  assert (Hptr : pointer = flag_pool_addr sg id).
  { destruct Hp; [destruct PreH2 as [[Hnonzero Hprefix] Hvalid]; contradiction|assumption]. }
  Exists image_2 entry_2.
  unfold flag_post_type_frame, flag_post_group_frame, flag_post_current_word_frame.
  rewrite Htype, Hflags, Hptr.
  assert (Hword : flag_word_rep (osKernelConfig sg) (flag_pool_addr sg id + 8) (flagImageBits image_2) =
    ((flag_pool_addr sg id + 8) # UShort |-> flagImageBits image_2)).
  { rewrite Hcfg; reflexivity. }
  rewrite Hword.
  entailer!; rewrite <- Hptr; assumption.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_9 : OSFlagPost_which_implies_wit_9.
Proof.
  left; intros.
  sep_apply_l_atomic (flag_post_restore_output_resources environment critical sg (flag_post_entered entry) mask cpu_sr (flag_post_acquired entry) released active_local (flag_post_caller_frame error_cell old_error F) captured).
  Intros returned current returned_local.
  Exists returned_local returned current.
  unfold flag_post_caller_frame. entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_10 : OSFlagPost_which_implies_wit_10.
Proof.
  left; intros.
  unfold flag_post_exit_cut.
  Intros.
  unfold flag_post_caller_frame.
  rewrite (flag_post_restore_input_capture environment critical active_local sg (flag_post_entered entry) mask cpu_sr (flag_post_acquired entry) released (error_cell # UChar |-> old_error ** F)).
  Intros captured. Exists captured. entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_11 : OSFlagPost_which_implies_wit_11.
Proof.
  left; intros.
  pose proof PreH1 as [Hcfg [Hpointer [_ [_ [Hlayout _]]]]].
  unfold flag_post_loop_cut. Intros.
  pose proof H as [Hprotected [_ [_ [_ Hvalid]]]].
  assert (Hp : pointer = flag_pool_addr sg id).
  { destruct Hpointer as [Hnull|Hp]; [destruct Hprotected as [[Hnonzero _] _]; contradiction|exact Hp]. }
  destruct (flag_post_initial_scan_head__loop_views_and_progress _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcfg PreH2 H)
    as [image [Himage Hhead]].
  assert (Hfacts : flag_post_loop_facts environment critical sg pointer id requested option_word mask original before cpu_sr context_2 image.(flagImageHead) 0).
  { rewrite Hhead; exact H. }
  rewrite (flag_post_masked_split_fields__loop_views_and_progress _ _ _ _ _ _ _ _ Hvalid).
  Exists image context_2.
  unfold kernel_program_fields_inv, kernel_program_fields_rep, UCOS2_fields_raw_rep, flag_fields_configured_rep.
  rewrite Hcfg; cbn [selected_kernel_configuration cfgFlagEnabled].
  rewrite (flag_fields_raw_rep_split_group sg _ id image Himage).
  destruct Hlayout as [_ [_ [_ [_ Hhead_address]]]].
  rewrite Hhead_address, Hp.
  unfold flag_post_group_head_frame, flag_post_group_frame, flag_group_rep, flag_group_rep_without_head.
  entailer!; try exact (proj1 Hvalid); try (rewrite <- Hp; assumption).
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_12 : OSFlagPost_which_implies_wit_12.
Proof.
  left; intros.
  pose proof PreH2 as [Hcfg [Hpointer [_ [_ [Hlayout [_ Hpostlayout]]]]]].
  unfold flag_post_loop_cut. Intros.
  pose proof H as [Hprotected [_ [_ [_ Hvalid]]]].
  assert (Hp : pointer = flag_pool_addr sg id).
  { destruct Hpointer as [Hnull|Hp]; [destruct Hprotected as [[Hnonzero _] _]; contradiction|exact Hp]. }
  destruct (flag_post_remaining_waiter__loop_views_and_progress _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcfg PreH1 H)
    as [image [waiter [Himage Hwaiter]]].
  rewrite (flag_post_masked_split_fields__loop_views_and_progress _ _ _ _ _ _ _ _ Hvalid).
  Exists image waiter context_2.
  unfold kernel_program_fields_inv, kernel_program_fields_rep, UCOS2_fields_raw_rep, flag_fields_configured_rep.
  rewrite Hcfg; cbn [selected_kernel_configuration cfgFlagEnabled].
  rewrite (flag_post_node_word_resources_equiv__loop_views_and_progress sg _ id pnode image waiter Himage Hwaiter).
  destruct Hlayout as [Hnext [Hprev [Htcb [Hgroup Hhead]]]].
  destruct Hpostlayout as [_ [Hbits [Hmask Hmode]]].
  rewrite Hnext, Hprev, Htcb, Hgroup, Hbits, Hmask, Hmode, Hp.
  unfold flag_node_fields_rep; rewrite Hcfg; cbn [flag_word_rep selected_kernel_configuration cfgFlagBits flag_node_mode_offset flag_word_bytes].
  entailer!; try exact (proj1 Hvalid); try (rewrite <- Hp; assumption).
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_13 : OSFlagPost_which_implies_wit_13.
Proof.
  left; intros.
  unfold flag_post_helper_cut. Intros.
  Exists old_2 waiter_2 context_2.
  subst sched; unfold flag_post_waiter_at; entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_14 : OSFlagPost_which_implies_wit_14.
Proof.
  left; intros.
  unfold flag_post_helper_cut. Intros.
  Exists old_2 waiter_2 context_2.
  subst sched; unfold flag_post_waiter_at; entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_15 : OSFlagPost_which_implies_wit_15.
Proof.
  left; intros.
  unfold flag_post_helper_cut. Intros.
  Exists old_2 waiter_2 context_2.
  subst sched; unfold flag_post_waiter_at; entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_16 : OSFlagPost_which_implies_wit_16.
Proof.
  left; intros.
  unfold flag_post_helper_cut. Intros.
  Exists old_2 waiter_2 context_2.
  subst sched; unfold flag_post_waiter_at; entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_17 : OSFlagPost_which_implies_wit_17.
Proof.
  left; intros.
  sep_apply_l_atomic (flag_post_restore_output_resources environment critical sg (flag_post_entered entry) mask cpu_sr (flag_post_acquired entry) released active_local (flag_post_caller_frame error_cell old_error F) captured).
  Intros returned current returned_local.
  Exists returned_local returned current.
  unfold flag_post_caller_frame. entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_18 : OSFlagPost_which_implies_wit_18.
Proof.
  left; intros.
  unfold flag_post_exit_cut.
  Intros.
  unfold flag_post_caller_frame.
  rewrite (flag_post_restore_input_capture environment critical active_local sg (flag_post_entered entry) mask cpu_sr (flag_post_acquired entry) released (error_cell # UChar |-> old_error ** F)).
  Intros captured. Exists captured. entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_19 : OSFlagPost_which_implies_wit_19.
Proof.
  left; intros.
  unfold flag_post_next_cut; Intros.
  destruct H as [Hloop [Hpending Hvalid]].
  assert (Hnode : flagNodeAddr (flag_post_pending_waiter pending_2) = pnode).
  { unfold flag_post_pending_facts in Hpending; tauto. }
  pose proof PreH1 as [Hcfg [Hptr [Hr [Ho [Hlayout Hrest]]]]].
  destruct Hlayout as [Hnext Hlayout].
  Exists pending_2 (flagNodeNext (flagWaitImage (flag_post_pending_waiter pending_2))).
  unfold flag_post_next_frame, flag_post_next_is, flag_node_fields_return_loan.
  rewrite Hnode, Hnext.
  sep_apply_l_atomic (flag_node_fields_rep_split_next (osKernelConfig sg) pnode
    (flagWaitImage (flag_post_pending_waiter pending_2))).
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_20 : OSFlagPost_which_implies_wit_20.
Proof.
  left; intros.
  unfold flag_post_exit_cut.
  Intros.
  unfold flag_post_caller_frame.
  rewrite (flag_post_restore_input_capture environment critical active_local sg (flag_post_entered entry) mask cpu_sr (flag_post_acquired entry) released (error_cell # UChar |-> old_error ** F)).
  Intros captured. Exists captured. entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_21 : OSFlagPost_which_implies_wit_21.
Proof.
  left; intros.
  sep_apply_l_atomic (flag_post_restore_output_resources environment critical sg (flag_post_entered entry) mask cpu_sr (flag_post_acquired entry) released active_local (flag_post_caller_frame error_cell old_error F) captured).
  Intros returned current returned_local.
  Exists returned_local returned current.
  unfold flag_post_caller_frame. entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_22 : OSFlagPost_which_implies_wit_22.
Proof.
  left; intros; subst sched.
  rewrite (flag_post_restored_scheduler_pre environment critical sg pointer id requested
    option_word mask original before cpu_sr released_context PreH1 PreH2 PreH4).
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_23 : OSFlagPost_which_implies_wit_23.
Proof.
  left; intros.
  rewrite (flag_post_scheduler_call_post_resources environment critical
    (flag_post_restored_local released_context) sg
    (flag_post_released_execution released_context) mask (flag_post_restored_state released_context)).
  Intros returned current next_local.
  Exists next_local returned current.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_24 : OSFlagPost_which_implies_wit_24.
Proof.
  left; intros.
  unfold flag_post_caller_frame.
  sep_apply_r_atomic (flag_post_save_input_capture environment critical current_local sg scheduled mask current (error_cell # UChar |-> old_error ** F)).
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_25 : OSFlagPost_which_implies_wit_25.
Proof.
  left; intros.
  unfold flag_post_read_cut; Intros.
  rename H into Hread.
  pose proof PreH1 as [Hcfg [Hptr [_ [_ [_ [_ Hlayout]]]]]].
  pose proof Hread as [Hrest [_ [_ [_ [Himage Hvalid]]]]].
  pose proof Hrest as [[[Hnonnull _] _] _].
  destruct Hptr as [Hnull|Hptr]; [contradiction|].
  destruct Hlayout as [_ [Hword _]].
  Exists first_saved_2 read_context_2.
  assert (Haddress : &((pointer) # "os_flag_grp" ->ₛ "OSFlagFlags") = flag_pool_addr sg id + 8)
    by (rewrite Hword, Hptr; reflexivity).
  rewrite Haddress.
  unfold flag_post_source_masked, flag_post_masked,
    kernel_continuation_world_spec.kernel_continuation_inv.
  rewrite (flag_post_current_word_resources sg (flag_post_read_state read_context_2) id
    (flag_post_read_image read_context_2) Hcfg Himage).
  unfold flag_post_critical_frame.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_26 : OSFlagPost_which_implies_wit_26.
Proof.
  left; intros.
  pose proof PreH2 as [Hcfg [Hptr [_ [_ [_ [_ Hlayout]]]]]].
  pose proof PreH3 as [Hrest [_ [_ [_ [Himage Hvalid]]]]].
  pose proof Hrest as [[[Hnonnull _] _] _].
  destruct Hptr as [Hnull|Hptr]; [contradiction|].
  destruct Hlayout as [_ [Hword _]].
  assert (Haddress : &((pointer) # "os_flag_grp" ->ₛ "OSFlagFlags") = flag_pool_addr sg id + 8)
    by (rewrite Hword, Hptr; reflexivity).
  rewrite PreH1, Haddress.
  assert (Hmerge :
    (flag_pool_addr sg id + 8) # UShort |-> flagImageBits (flag_post_read_image read_context) **
    flag_post_current_word_frame sg (flag_post_read_state read_context) id (flag_post_read_image read_context) **
    flag_post_critical_frame environment critical (flag_post_read_local read_context) sg
      (flag_post_reader read_context) cpu_sr (flag_post_read_state read_context) (flag_post_read_state read_context)
    |-- flag_post_source_masked environment critical (flag_post_read_local read_context) sg
      (flag_post_reader read_context) cpu_sr (flag_post_read_state read_context) (flag_post_read_state read_context)).
  { unfold flag_post_source_masked, flag_post_masked, flag_post_critical_frame,
      kernel_continuation_world_spec.kernel_continuation_inv.
    rewrite (flag_post_current_word_resources sg (flag_post_read_state read_context) id
      (flag_post_read_image read_context) Hcfg Himage).
    destruct Hvalid as [Hinv [Hcoverage Hsource]].
    entailer!. }
  rewrite Hmerge.
  pose proof (flag_post_restore_input_capture environment critical (flag_post_read_local read_context) sg
    (flag_post_reader read_context) mask cpu_sr (flag_post_read_state read_context) (flag_post_read_state read_context)
    (flag_post_caller_frame error_cell old_error F)) as Hcapture.
  unfold flag_post_caller_frame in Hcapture.
  sepcon_assoc_change.
  rewrite Hcapture.
  Intros captured; Exists captured; entailer!.
Qed. 

Lemma proof_of_OSFlagPost_which_implies_wit_27 : OSFlagPost_which_implies_wit_27.
Proof.
  left; intros.
  sep_apply_l_atomic (flag_post_restore_output_resources environment critical sg (flag_post_reader read_context) mask cpu_sr (flag_post_read_state read_context) (flag_post_read_state read_context) (flag_post_read_local read_context) (flag_post_caller_frame error_cell old_error F) read_captured).
  Intros returned current returned_local.
  Exists returned_local returned current.
  unfold flag_post_caller_frame. entailer!.
Qed. 

