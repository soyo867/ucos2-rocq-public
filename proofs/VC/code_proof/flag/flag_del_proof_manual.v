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
From Ucos2Verify.VC.code.flag Require Import flag_del_goal.
From Ucos2Verify.VC.code.flag Require Import flag_del_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.flag.spec.flag_del_spec.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope sac_scope.
Local Open Scope sac.

Lemma proof_of_OSFlagDel_entail_wit_1 : OSFlagDel_entail_wit_1.
Proof.
  left; intros.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range (&("opt")) opt_pre).
  Intros; entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_2 : OSFlagDel_entail_wit_2.
Proof.
  left; intros; subst pgrp_pre; subst pointer; subst opt_pre; subst perr_pre.
  pose proof (flag_del_prefix_null environment critical sg caller mask view option name before) as Hprefix.
  pose proof (flag_del_prefix_no_schedule_implies_program__entry_and_early_returns environment critical sg caller mask view 0 option name
    before _ caller before Hprefix) as Hprogram.
  pose proof (flag_del_no_schedule_safe_return environment critical sg caller mask view 0 option name
    before _ caller before X Hprefix PreH17) as Hsafe.
  pose proof (task_suspend_same_call_refl caller) as Hsame.
  unfold flag_del_source_return_cut, flag_del_return_cut.
  sep_apply store_uint_undef_store_uint; entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_3 : OSFlagDel_entail_wit_3.
Proof.
  left; intros; subst pgrp_pre; subst opt_pre; subst perr_pre.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range (&("OSIntNesting")) (os_sched_ints before)).
  Intros.
  match goal with H : 0 <= os_sched_ints before <= _ |- _ =>
    change (0 <= os_sched_ints before <= 255) in H end.
  assert (Hnorm : unsigned_last_nbits (os_sched_ints before) 32 = os_sched_ints before).
  { apply unsigned_last_nbits_eq; change (0 <= os_sched_ints before < 4294967296); lia. }
  rewrite Hnorm in PreH1.
  pose proof (proj2 (flag_del_closed_nesting_equiv__entry_and_early_returns environment local sg caller mask before)) as Hmerge.
  destruct PreH11 as [Haddr Haddresses]; rewrite <- Haddr in Hmerge.
  sep_apply_l_atomic Hmerge.
  pose proof (flag_del_prefix_isr environment critical sg caller mask view pointer option name before
    PreH2 ltac:(lia)) as Hprefix.
  pose proof (flag_del_prefix_no_schedule_implies_program__entry_and_early_returns environment critical sg caller mask view pointer option name
    before _ caller before Hprefix) as Hprogram.
  pose proof (flag_del_no_schedule_safe_return environment critical sg caller mask view pointer option name
    before _ caller before X Hprefix PreH18) as Hsafe.
  pose proof (task_suspend_same_call_refl caller) as Hsame.
  unfold flag_del_source_return_cut, flag_del_return_cut.
  sep_apply store_uint_undef_store_uint; entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_4 : OSFlagDel_entail_wit_4.
Proof.
  left; intros; subst pgrp_pre; subst opt_pre; subst perr_pre.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range (&("OSIntNesting")) (os_sched_ints before)).
  Intros.
  match goal with H : 0 <= os_sched_ints before <= _ |- _ =>
    change (0 <= os_sched_ints before <= 255) in H end.
  assert (Hnorm : unsigned_last_nbits (os_sched_ints before) 32 = os_sched_ints before).
  { apply unsigned_last_nbits_eq; change (0 <= os_sched_ints before < 4294967296); lia. }
  rewrite Hnorm in PreH1.
  assert (Hzero : os_sched_ints before = 0) by lia.
  pose proof (proj2 (flag_del_closed_nesting_equiv__entry_and_early_returns environment local sg caller mask before)) as Hmerge.
  pose proof PreH11 as Haddresses; destruct Haddresses as [Haddr _]; rewrite <- Haddr in Hmerge.
  sep_apply_l_atomic Hmerge.
  pose proof PreH17 as Hargument.
  destruct Hargument as [Hz|[_ [Hlayout [Haddress [Hselected Hraw]]]]]; [contradiction|].
  assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true).
  { rewrite (flag_del_build_configuration sg PreH14); reflexivity. }
  sep_apply_l_atomic (proj1 (flag_del_closed_type_cut_equiv__entry_and_early_returns
    environment local sg caller mask pointer view before observed PreH2 Haddress Hselected Henabled)).
  sep_apply store_uint_undef_store_uint; entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_5 : OSFlagDel_entail_wit_5.
Proof.
  left; intros.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range (&(pointer # "os_flag_grp" ->ₛ "OSFlagType")) (flagImageType observed)).
  Intros.
  match goal with H : 0 <= flagImageType observed <= _ |- _ =>
    change (0 <= flagImageType observed <= 255) in H end.
  assert (Hnorm : unsigned_last_nbits (flagImageType observed) 32 = flagImageType observed).
  { apply unsigned_last_nbits_eq; change (0 <= flagImageType observed < 4294967296); lia. }
  rewrite Hnorm in PreH1.
  pose proof PreH11 as Hargument.
  destruct Hargument as [Hz|[_ [[Htype Hlayout] [Haddress [Hselected Hraw]]]]]; [contradiction|].
  assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true).
  { rewrite (flag_del_build_configuration sg PreH7); reflexivity. }
  rewrite Htype.
  assert (Hfocus : pointer # UChar |-> flagImageType observed **
    flag_del_type_read_frame environment local sg caller mask pointer view before observed |--
    flag_del_type_cut environment local sg caller mask pointer view before observed).
  { unfold flag_del_type_read_frame, flag_del_type_cut; entailer!. }
  sep_apply_l_atomic Hfocus.
  sep_apply_l_atomic (proj2 (flag_del_closed_type_cut_equiv__entry_and_early_returns
    environment local sg caller mask pointer view before observed PreH13 Haddress Hselected Henabled)).
  pose proof (flag_del_prefix_wrong_type environment critical sg caller mask view pointer option name before observed
    PreH13 PreH14 Hselected PreH1) as Hprefix.
  pose proof (flag_del_prefix_no_schedule_implies_program__entry_and_early_returns environment critical sg caller mask view pointer option name
    before _ caller before Hprefix) as Hprogram.
  pose proof (flag_del_no_schedule_safe_return environment critical sg caller mask view pointer option name
    before _ caller before X Hprefix PreH12) as Hsafe.
  pose proof (task_suspend_same_call_refl caller) as Hsame.
  unfold flag_del_source_return_cut, flag_del_return_cut; entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_6 : OSFlagDel_entail_wit_6.
Proof.
  left; intros.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range (&(pointer # "os_flag_grp" ->ₛ "OSFlagType")) (flagImageType observed)).
  Intros.
  match goal with H : 0 <= flagImageType observed <= _ |- _ =>
    change (0 <= flagImageType observed <= 255) in H end.
  assert (Hnorm : unsigned_last_nbits (flagImageType observed) 32 = flagImageType observed).
  { apply unsigned_last_nbits_eq; change (0 <= flagImageType observed < 4294967296); lia. }
  rewrite Hnorm in PreH1.
  pose proof PreH11 as Hargument.
  destruct Hargument as [Hz|[_ [[Htype Hlayout] [Haddress [Hselected Hraw]]]]]; [contradiction|].
  assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true).
  { rewrite (flag_del_build_configuration sg PreH7); reflexivity. }
  rewrite Htype.
  assert (Hfocus : pointer # UChar |-> flagImageType observed **
    flag_del_type_read_frame environment local sg caller mask pointer view before observed |--
    flag_del_type_cut environment local sg caller mask pointer view before observed).
  { unfold flag_del_type_read_frame, flag_del_type_cut; entailer!. }
  sep_apply_l_atomic Hfocus.
  sep_apply_l_atomic (proj2 (flag_del_closed_type_cut_equiv__entry_and_early_returns
    environment local sg caller mask pointer view before observed PreH13 Haddress Hselected Henabled)).
  destruct view as [raw|id].
  - cbn [flag_query_selected] in Hselected; subst observed; contradiction.
  - unfold flag_del_raw_type; rewrite (proj2 (Z.eqb_neq _ _) PreH13); entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_7 : OSFlagDel_entail_wit_7.
Proof.
  left; intros.
  pose proof PreH9 as Hargument.
  destruct Hargument as [Hnull|[Hnonnull [Hlayout [Haddress [Hselected Hkind]]]]].
  { contradiction. }
  destruct view as [original|id].
  { cbn [flag_query_selected] in Hselected; subst observed; contradiction. }
  sep_apply_l_atomic (flag_del_source_save_output_open
    environment critical local sg caller mask before save_heap retval).
  Intros active acquired protected_local.
  prop_apply_p (flag_del_masked_state_inv__acquired_type_and_group_fields
    environment critical protected_local sg active retval acquired acquired).
  Intros.
  assert (Hinv : UCOS2_state_inv sg acquired) by assumption.
  destruct (flag_query_acquired_image sg pointer (FlagQueryPool id) acquired Haddress Hinv)
    as [image Himage].
  assert (Henabled : cfgFlagEnabled (osKernelConfig sg) = true).
  { rewrite (flag_del_build_configuration sg PreH6); reflexivity. }
  pose proof Haddress as [Hpointer Hid].
  sep_apply_l_atomic (flag_del_masked_type_cut_split__acquired_type_and_group_fields
    environment critical protected_local sg active retval acquired acquired pointer id image Henabled Hpointer Himage).
  Exists protected_local image id active acquired.
  entailer!.
  unfold flag_del_source_prefix_facts, flag_del_prefix_facts; tauto.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_8 : OSFlagDel_entail_wit_8.
Proof.
  left; intros.
  assert (Hnonnull : pointer <> 0).
  { unfold flag_del_source_prefix_facts, flag_del_prefix_facts in PreH10; tauto. }
  assert (Hlayout : flag_del_layout pointer).
  { unfold flag_del_argument in PreH9; tauto. }
  destruct Hlayout as [Htype _].
  Exists protected_local_2 image_2 id_2 active_2 acquired_2.
  unfold flag_del_masked_type_cut, flag_del_masked_type_frame.
  rewrite Htype. Intros. entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_9_1 : OSFlagDel_entail_wit_9_1.
Proof.
  left; intros.
  assert (Hnonnull : pointer <> 0).
  { unfold flag_del_source_prefix_facts, flag_del_prefix_facts in PreH13; tauto. }
  assert (Hlayout : flag_del_layout pointer).
  { unfold flag_del_argument in PreH12; tauto. }
  assert (Haddress : pointer = flag_pool_addr sg id).
  { rewrite PreH14 in PreH12.
    unfold flag_del_argument, flag_query_address in PreH12; tauto. }
  assert (Himage : flagImages (FlagState acquired_2) id = Some image).
  { rewrite PreH14 in PreH15; exact PreH15. }
  assert (Henabled : cfgFlagEnabled (osKernelConfig sg) = true).
  { rewrite (flag_del_build_configuration sg PreH9); reflexivity. }
  assert (Hbad : flagImageType image <> 5).
  { intro E; rewrite E in PreH1; apply PreH1; reflexivity. }
  assert (Hresult : flag_del_protected_result sg view pointer option name acquired_2 pointer 1 false acquired_2).
  { unfold flag_del_protected_result.
    change (flag_del_protected sg view pointer option name acquired_2
      (flag_del_observation pointer Ucos2Verify.lib.error_codes.OS_ERR_EVENT_TYPE, false) acquired_2).
    apply (flag_del_protected_recheck_error sg view pointer option name acquired_2 image).
    - exact PreH15.
    - unfold flag_del_valid_option; rewrite PreH2; reflexivity.
    - exact Hbad. }
  destruct Hlayout as [Htype _].
  Exists protected_local_2 active_2 acquired_2.
  entailer!.
  sep_apply_r_atomic (flag_del_masked_type_cut_merge__acquired_type_and_group_fields
    environment critical protected_local_2 sg active_2 cpu_sr acquired_2 acquired_2 pointer id image Henabled Haddress Himage).
  unfold flag_del_masked_type_cut, flag_del_masked_type_frame.
  rewrite Htype. Intros. entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_9_2 : OSFlagDel_entail_wit_9_2.
Proof.
  left; intros.
  assert (Hnonnull : pointer <> 0).
  { unfold flag_del_source_prefix_facts, flag_del_prefix_facts in PreH12; tauto. }
  assert (Hlayout : flag_del_layout pointer).
  { unfold flag_del_argument in PreH11; tauto. }
  assert (Haddress : pointer = flag_pool_addr sg id).
  { rewrite PreH13 in PreH11.
    unfold flag_del_argument, flag_query_address in PreH11; tauto. }
  assert (Himage : flagImages (FlagState acquired_2) id = Some image).
  { rewrite PreH13 in PreH14; exact PreH14. }
  assert (Henabled : cfgFlagEnabled (osKernelConfig sg) = true).
  { rewrite (flag_del_build_configuration sg PreH8); reflexivity. }
  assert (Hbad : flagImageType image <> 5).
  { intro E; rewrite E in PreH1; apply PreH1; reflexivity. }
  assert (Hresult : flag_del_protected_result sg view pointer option name acquired_2 pointer 1 false acquired_2).
  { unfold flag_del_protected_result.
    change (flag_del_protected sg view pointer option name acquired_2
      (flag_del_observation pointer Ucos2Verify.lib.error_codes.OS_ERR_EVENT_TYPE, false) acquired_2).
    apply (flag_del_protected_recheck_error sg view pointer option name acquired_2 image).
    - exact PreH14.
    - unfold flag_del_valid_option; rewrite PreH2; reflexivity.
    - exact Hbad. }
  destruct Hlayout as [Htype _].
  Exists protected_local_2 active_2 acquired_2.
  entailer!.
  sep_apply_r_atomic (flag_del_masked_type_cut_merge__acquired_type_and_group_fields
    environment critical protected_local_2 sg active_2 cpu_sr acquired_2 acquired_2 pointer id image Henabled Haddress Himage).
  unfold flag_del_masked_type_cut, flag_del_masked_type_frame.
  rewrite Htype. Intros. entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_10 : OSFlagDel_entail_wit_10.
Proof.
  unfold OSFlagDel_entail_wit_10; right; intros.
  sep_apply (flag_del_restore_output_after_restore__restore_and_scheduler_returns
    environment critical protected_local sg caller mask view pointer option name before observed
    active cpu_sr acquired pointer 1 false acquired restore_heap X
    PreH9 (proj1 PreH10) PreH11).
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_11 : OSFlagDel_entail_wit_11.
Proof.
  unfold OSFlagDel_entail_wit_11; left; intros.
  unfold flag_del_source_after_restore; Intros returned current next_local.
  assert (Hprogram : flag_del_program environment critical sg caller mask view pointer option name
    before (pointer,1) current).
  { unfold flag_del_program, StateRelBasic.StateRelMonad.bind.
    exists (((pointer,1),false),returned), current; split; [tauto|].
    split; reflexivity. }
  Exists next_local returned current.
  unfold flag_del_source_return_cut, flag_del_return_cut.
  cbn [flag_del_tail_program] in *.
  unfold flag_del_source_restore_cut in *.
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_12_1 : OSFlagDel_entail_wit_12_1.
Proof.
  left; intros.
  assert (Hnonnull : pointer <> 0).
  { unfold flag_del_source_prefix_facts, flag_del_prefix_facts in PreH12; tauto. }
  assert (Hlayout : flag_del_layout pointer).
  { unfold flag_del_argument in PreH11; tauto. }
  destruct Hlayout as [Htype _].
  assert (Hchecked : flag_del_rechecked option image_2).
  { unfold flag_del_rechecked; tauto. }
  Exists protected_local_2 image_2 id_2 active_2 acquired_2.
  rewrite <- (flag_del_masked_type_cut_group_cut_equiv__acquired_type_and_group_fields
    environment critical protected_local_2 sg active_2 cpu_sr acquired_2 acquired_2 pointer id_2 image_2 PreH8).
  unfold flag_del_masked_type_cut, flag_del_masked_type_frame.
  rewrite Htype. Intros. entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_12_2 : OSFlagDel_entail_wit_12_2.
Proof.
  left; intros.
  assert (Hnonnull : pointer <> 0).
  { unfold flag_del_source_prefix_facts, flag_del_prefix_facts in PreH13; tauto. }
  assert (Hlayout : flag_del_layout pointer).
  { unfold flag_del_argument in PreH12; tauto. }
  destruct Hlayout as [Htype _].
  prop_apply_p (UCOS2_C_Rules.store_uchar_range
    (&((pointer) # "os_flag_grp" ->ₛ "OSFlagType")) (flagImageType image_2)).
  Intros.
  match goal with Hrange : 0 <= flagImageType image_2 <= _ |- _ =>
    change (0 <= flagImageType image_2 <= 255) in Hrange end.
  assert (Hcast : unsigned_last_nbits (flagImageType image_2) 32 = flagImageType image_2).
  { apply unsigned_last_nbits_eq; change (0 <= flagImageType image_2 < 4294967296); lia. }
  rewrite Hcast in PreH1.
  assert (Hchecked : flag_del_rechecked option image_2).
  { unfold flag_del_rechecked; auto. }
  Exists protected_local_2 image_2 id_2 active_2 acquired_2.
  rewrite <- (flag_del_masked_type_cut_group_cut_equiv__acquired_type_and_group_fields
    environment critical protected_local_2 sg active_2 cpu_sr acquired_2 acquired_2 pointer id_2 image_2 PreH9).
  unfold flag_del_masked_type_cut, flag_del_masked_type_frame.
  rewrite Htype. Intros. entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_12_3 : OSFlagDel_entail_wit_12_3.
Proof.
  left; intros.
  assert (Hnonnull : pointer <> 0).
  { unfold flag_del_source_prefix_facts, flag_del_prefix_facts in PreH12; tauto. }
  assert (Hlayout : flag_del_layout pointer).
  { unfold flag_del_argument in PreH11; tauto. }
  destruct Hlayout as [Htype _].
  prop_apply_p (UCOS2_C_Rules.store_uchar_range
    (&((pointer) # "os_flag_grp" ->ₛ "OSFlagType")) (flagImageType image_2)).
  Intros.
  match goal with Hrange : 0 <= flagImageType image_2 <= _ |- _ =>
    change (0 <= flagImageType image_2 <= 255) in Hrange end.
  assert (Hcast : unsigned_last_nbits (flagImageType image_2) 32 = flagImageType image_2).
  { apply unsigned_last_nbits_eq; change (0 <= flagImageType image_2 < 4294967296); lia. }
  rewrite Hcast in PreH1.
  assert (Hchecked : flag_del_rechecked option image_2).
  { unfold flag_del_rechecked; auto. }
  Exists protected_local_2 image_2 id_2 active_2 acquired_2.
  rewrite <- (flag_del_masked_type_cut_group_cut_equiv__acquired_type_and_group_fields
    environment critical protected_local_2 sg active_2 cpu_sr acquired_2 acquired_2 pointer id_2 image_2 PreH8).
  unfold flag_del_masked_type_cut, flag_del_masked_type_frame.
  rewrite Htype. Intros. entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_13 : OSFlagDel_entail_wit_13.
Proof.
  left; intros.
  assert (Hnonnull : pointer <> 0).
  { unfold flag_del_source_prefix_facts, flag_del_prefix_facts in PreH10; tauto. }
  assert (Hlayout : flag_del_layout pointer).
  { unfold flag_del_argument in PreH9; tauto. }
  destruct Hlayout as [Htype [Hhead [Hbits Hname]]].
  Exists protected_local_2 image_2 id_2 active_2 acquired_2.
  unfold flag_del_group_cut, flag_del_group_frame, flag_del_free_head_state.
  rewrite Htype, Hhead, Hbits, Hname, PreH4. Intros. entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_14_1 : OSFlagDel_entail_wit_14_1.
Proof.
  left; intros.
  assert (Hnonnull : pointer <> 0).
  { unfold flag_del_source_prefix_facts, flag_del_prefix_facts in PreH11; tauto. }
  assert (Hlayout : flag_del_layout pointer).
  { unfold flag_del_argument in PreH10; tauto. }
  destruct Hlayout as [Htype [Hhead [Hbits Hname]]].
  assert (Hwaiting : 1 = flag_del_waiting image_2).
  { unfold flag_del_waiting.
    rewrite (proj2 (Z.eqb_neq _ _) PreH1); reflexivity. }
  Exists protected_local_2 image_2 id_2 active_2 acquired_2.
  unfold flag_del_group_cut, flag_del_group_frame, flag_del_free_head_state.
  rewrite Htype, Hhead, Hbits, Hname, PreH5. Intros. entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_14_2 : OSFlagDel_entail_wit_14_2.
Proof.
  left; intros.
  assert (Hnonnull : pointer <> 0).
  { unfold flag_del_source_prefix_facts, flag_del_prefix_facts in PreH11; tauto. }
  assert (Hlayout : flag_del_layout pointer).
  { unfold flag_del_argument in PreH10; tauto. }
  destruct Hlayout as [Htype [Hhead [Hbits Hname]]].
  assert (Hwaiting : 0 = flag_del_waiting image_2).
  { unfold flag_del_waiting.
    rewrite (PreH1); reflexivity. }
  Exists protected_local_2 image_2 id_2 active_2 acquired_2.
  unfold flag_del_group_cut, flag_del_group_frame, flag_del_free_head_state.
  rewrite Htype, Hhead, Hbits, Hname, PreH5. Intros. entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_15 : OSFlagDel_entail_wit_15.
Proof.
  left; intros.
  assert (Hnonnull : pointer <> 0).
  { unfold flag_del_source_prefix_facts, flag_del_prefix_facts in PreH10; tauto. }
  assert (Hlayout : flag_del_layout pointer).
  { unfold flag_del_argument in PreH9; tauto. }
  destruct Hlayout as [Htype [Hhead [Hbits Hname]]].
  Exists protected_local_2 image_2 id_2 active_2 acquired_2.
  unfold flag_del_group_cut, flag_del_group_frame, flag_del_free_head_state.
  rewrite Htype, Hhead, Hbits, Hname, PreH4. Intros. entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_16 : OSFlagDel_entail_wit_16.
Proof.
  right; intros.
  assert (Hp : pointer <> 0) by (unfold flag_del_source_prefix_facts, flag_del_prefix_facts in PreH12; tauto).
  destruct (flag_del_pool_argument_implies_layout_address__drain_and_release_results sg pointer view before observed id_2 PreH11 Hp PreH13)
    as [[Ht [Hh [Hb Hn]]] Hpointer].
  assert (Hinv : UCOS2_state_inv sg acquired_2) by (unfold flag_del_source_prefix_facts in PreH12; tauto).
  assert (Htype : flagImageType image_2 = 5) by (apply PreH15; auto).
  assert (Himage : acquired_2.(FlagState).(flagImages) id_2 = Some image_2) by (rewrite PreH13 in PreH14; exact PreH14).
  assert (Hhead : flagImageHead image_2 = 0).
  { unfold flag_del_waiting in PreH16.
    destruct (flagImageHead image_2) eqn:Hhead_value; [reflexivity|..];
      cbn in PreH16;
      rewrite PreH16 in PreH1; discriminate PreH1. }
  destruct (flag_del_acquired_live_empty sg acquired_2 id_2 image_2 Hinv Himage Htype Hhead) as [group [Hgroup Hempty]].
  assert (Hresult : flag_del_protected_result sg view pointer option name acquired_2 0 0 false (flag_del_release_state sg acquired_2 id_2 image_2 name)).
  { subst option view. apply flag_del_protected_no_pend_empty; assumption. }
  pose proof (flag_del_release_preserves_source_cut__drain_and_release_results sg active_2 acquired_2 id_2 image_2 name PreH17) as Hcut.
  replace (LitMap "?" + 0 * sizeof(CHAR)) with name by lia.
  rewrite Ht, Hh, Hb, Hn, PreH6.
  sep_apply_l_atomic (flag_del_group_merge_released__drain_and_release_results environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 group image_2 name Hpointer Himage Hgroup Hempty (flag_del_build_flag_names sg PreH8)).
  Exists protected_local_2 image_2 id_2 active_2 acquired_2. entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_17 : OSFlagDel_entail_wit_17.
Proof.
  unfold OSFlagDel_entail_wit_17; right; intros.
  rewrite <- PreH6.
  sep_apply (flag_del_restore_output_after_restore__restore_and_scheduler_returns
    environment critical protected_local sg caller mask view pointer option name before observed
    active cpu_sr acquired 0 0 false (flag_del_release_state sg acquired id image name) restore_heap X
    PreH10 (proj1 PreH11) PreH13).
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_18 : OSFlagDel_entail_wit_18.
Proof.
  left; intros.
  assert (Hp : pointer <> 0) by (unfold flag_del_source_prefix_facts, flag_del_prefix_facts in PreH12; tauto).
  destruct (flag_del_pool_argument_implies_layout_address__drain_and_release_results sg pointer view before observed id PreH11 Hp PreH13)
    as [[Ht [Hh [Hb Hn]]] Hpointer].
  assert (Htype : flagImageType image = 5) by (apply PreH15; auto).
  assert (Hhead : flagImageHead image <> 0).
  { intro Hzero. unfold flag_del_waiting in PreH16. rewrite Hzero in PreH16. subst tasks_waiting.
    apply PreH1; reflexivity. }
  assert (Hresult : flag_del_protected_result sg view pointer option name acquired_2 pointer 73 false acquired_2).
  { subst option; apply (flag_del_protected_waiting sg view pointer name acquired_2 image PreH14 Htype Hhead). }
  assert (Himage : acquired_2.(FlagState).(flagImages) id = Some image) by (rewrite PreH13 in PreH14; exact PreH14).
  Exists protected_local_2 active_2 acquired_2.
  sep_apply store_uchar_undef_store_uchar.
  rewrite Ht, Hh, Hb, Hn, PreH6. entailer!.
  sep_apply_r_atomic (flag_del_group_merge_original__drain_and_release_results environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id acquired_2 image Hpointer Himage (flag_del_build_flag_names sg PreH8)).
  unfold flag_del_group_cut, flag_del_group_frame, flag_del_free_head_state. entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_19 : OSFlagDel_entail_wit_19.
Proof.
  unfold OSFlagDel_entail_wit_19; right; intros.
  sep_apply (flag_del_restore_output_after_restore__restore_and_scheduler_returns
    environment critical protected_local sg caller mask view pointer option name before observed
    active cpu_sr acquired pointer 73 false acquired restore_heap X
    PreH10 (proj1 PreH11) PreH12).
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_20 : OSFlagDel_entail_wit_20.
Proof.
  left; intros.
  assert (Hnonnull : pointer <> 0).
  { unfold flag_del_source_prefix_facts, flag_del_prefix_facts in PreH10; tauto. }
  assert (Hlayout : flag_del_layout pointer).
  { unfold flag_del_argument in PreH9; tauto. }
  destruct Hlayout as [Htype [Hhead [Hbits Hname]]].
  Exists protected_local_2 image_2 id_2 active_2 acquired_2.
  unfold flag_del_group_cut, flag_del_group_frame, flag_del_free_head_state.
  rewrite Htype, Hhead, Hbits, Hname, PreH4. Intros. entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_21 : OSFlagDel_entail_wit_21.
Proof.
  left; intros.
  assert (Hvalid : UCOS2_state_inv sg acquired_2) by (unfold flag_del_source_prefix_facts in PreH11; tauto).
  assert (Hnonzero : pointer <> 0) by (unfold flag_del_source_prefix_facts, flag_del_prefix_facts in PreH11; tauto).
  pose proof PreH10 as Hargument; destruct Hargument as [Hz|[_ [Hlayout [Haddress _]]]]; [contradiction|].
  rewrite PreH12 in Haddress, PreH13; cbn [flag_query_address] in Haddress; cbn [flag_query_selected] in PreH13.
  destruct Haddress as [Hpointer Hrange].
  assert (Htype : flagImageType image = 5) by (apply PreH14; tauto).
  destruct (flag_query_state_configuration sg acquired_2 Hvalid) as [Henabled [Hbits Hflags]].
  destruct (flag_name_set_pool_type_is_live sg acquired_2.(FlagState) id_2 image Hflags PreH13 Htype) as [group Hgroup].
  pose proof Hflags as [_ [_ [_ [Hgroups _]]]].
  destruct (Hgroups id_2 group Hgroup) as [_ [_ [_ [found [Hfound [_ [Hhead _]]]]]]].
  assert (found = image) by congruence; subst found.
  assert (Hacquired : flag_del_acquired_group acquired_2 id_2 image (flagWaitOrder group)).
  { split; [exact PreH13|]. split; [exact Htype|]. exists group; auto. }
  assert (Hloop : flag_del_source_loop_facts sg active_2 acquired_2 id_2 (flagWaitOrder group) nil (flagWaitOrder group) acquired_2 (flagImageHead image)).
  { split.
    - split; [reflexivity|]. split; [reflexivity|]. split; [exists group; auto|].
      split; [rewrite Hhead; destruct (flagWaitOrder group); reflexivity|].
      apply flag_del_source_cut_call_cut; exact PreH16.
    - exact PreH16. }
  Exists (flagWaitOrder group) image (flagWaitOrder group) id_2 active_2 (@nil Z) acquired_2 protected_local_2 acquired_2 protected_local_2.
  unfold flag_del_group_frame; Intros.
  assert (Hfields :
    (&(pointer # "os_flag_grp" ->ₛ "OSFlagType")) # UChar |-> flagImageType image **
    (&(pointer # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr |-> flagImageHead image **
    (&(pointer # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort |-> flagImageBits image **
    (&(pointer # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr |-> flagImageName image **
    flag_del_group_padding pointer image |-- flag_group_rep (osKernelConfig sg) (flag_pool_addr sg id_2) image).
  { destruct Hlayout as [Hty [Hwait [Hflag Hname]]].
    rewrite <- Hpointer, Hty, Hwait, Hflag, Hname.
    apply (proj2 (flag_del_group_fields (osKernelConfig sg) pointer image Hbits (flag_del_build_flag_names sg PreH7))). }
  sep_apply_l_atomic Hfields.
  rewrite PreH5; unfold flag_del_free_head_state.
  sep_apply_l_atomic (flag_del_pool_fields_merge_original sg acquired_2 id_2 image Henabled Hvalid PreH13).
  unfold flag_del_masked, kernel_continuation_inv.
  rewrite kernel_program_fields_inv_split_unmap.
  fold (os_sched_fields_capsules environment protected_local_2 acquired_2).
  entailer!; split; reflexivity.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_22 : OSFlagDel_entail_wit_22.
Proof.
  left; intros.
  Exists remaining image order id active visited acquired protected_local current now_local.
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_23 : OSFlagDel_entail_wit_23.
Proof.
  left; intros.
  pose proof PreH17 as [[Horder [Hfold [[group [Hgroup Hremaining]] [Hnode Hcut]]]] Hsource].
  destruct remaining_3 as [|head rest]; [cbn in Hnode; contradiction|].
  cbn in Hnode; subst head.
  assert (Hinitial : UCOS2_state_inv sg acquired_3) by (unfold flag_del_source_prefix_facts in PreH13; tauto).
  pose proof (flag_del_abort_waiters_preserves_validity__waiter_loop_and_publication sg visited_3 acquired_3 current_3 Hinitial Hfold) as Hvalid.
  destruct (flag_del_abort_head sg current_3 id_3 group pnode rest Hvalid Hgroup Hremaining)
    as [waiter [ready [post [Hwaiter [Hnext [Hstep [Hpost Hgroupnext]]]]]]].
  assert (Hconfig := flag_del_build_configuration sg PreH9).
  assert (Hlayout := flag_del_build_unlink_layout sg PreH9).
  destruct (flag_task_rdy_stable_domain sg current_3 pnode waiter 0 Hconfig Hlayout ltac:(lia) Hvalid Hwaiter) as [old Hdomain].
  pose proof Hdomain as [_ [[_ [_ [_ [Haddress _]]]] [Hold _]]].
  assert (Hconsistent : task_flag_waiter_consistency sg current_3.(TskState) current_3.(FlagState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, cross_module_consistency in Hvalid; tauto. }
  unfold flag_del_masked, kernel_continuation_inv.
  rewrite kernel_program_fields_inv_split_unmap; Intros.
  assert (Hcoverage : task_stack_live_coverage current_3.(TskState) (flag_del_active_key active_3)) by assumption.
  assert (Hparked : exists region fragments, current_3.(TskState).(parkedTaskStacks) (waiter.(flagTask),waiter.(flagTaskGeneration)) = Some (region, fragments)).
  { eapply flag_del_other_waiter_parked; [exact Hconsistent|exact Hwaiter|exact Hcoverage|].
    destruct active_3 as [call|execution]; [|discriminate].
    unfold flag_del_active_key, task_stack_call_active_key.
    unfold flag_del_call_cut in Hcut.
    destruct (os_sched_call_origin call) eqn:Horigin; [discriminate|].
    destruct Hcut as [Hrun Hentry].
    pose proof (flag_del_task_entry_waiter_other_key sg call current_3 pnode waiter Hentry Hconsistent Hwaiter) as Hother.
    destruct Hentry as [[Hidentity _] _].
    rewrite Horigin in Hidentity; injection Hidentity as Hslot Hgen.
    intro Heq; inversion Heq; apply Hother; unfold task_stack_key; congruence. }
  destruct Hparked as [region [fragments Hparked]].
  set (lease := {| stackLeaseSlot := waiter.(flagTask); stackLeaseRegion := region; stackLeaseGeneration := waiter.(flagTaskGeneration) |}).
  Exists lease fragments waiter old (pnode::rest) image_3 order_3 id_3 active_3 visited_3 acquired_3 protected_local_3 current_3 now_local_3.
  assert (Hloan : flag_del_loan_origin current_3 waiter lease fragments) by (split; [reflexivity|exact Hparked]).
  assert (Hat : flag_del_waiter_at current_3 pnode waiter old) by (repeat split; assumption).
  sep_apply_l_atomic (flag_task_rdy_fields_stable_split sg current_3 pnode waiter 0 Hconfig Hlayout ltac:(lia) Hwaiter).
  Intros found.
  unfold flag_task_rdy_fields_pre; Intros.
  assert (found = old) by (match goal with H : flag_task_rdy_domain _ _ _ _ found _ |- _ => destruct H as [_ [_ [Hfound _]]]; congruence end).
  subst found; unfold flag_task_rdy_fields_pre, flag_del_iteration_frame, os_sched_fields_capsules; entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_24 : OSFlagDel_entail_wit_24.
Proof.
  left; intros.
  pose proof PreH16 as [[Horder [Hfold Hrest]] Hsource].
  pose proof PreH17 as [Hwaiter [Hold Haddress]].
  assert (Hinitial : UCOS2_state_inv sg acquired_2) by (unfold flag_del_source_prefix_facts in PreH12; tauto).
  pose proof (flag_del_abort_waiters_preserves_validity__waiter_loop_and_publication sg visited_2 acquired_2 current_2 Hinitial Hfold) as Hvalid.
  destruct (flag_task_rdy_stable_domain sg current_2 pnode waiter_2 0
    (flag_del_build_configuration sg PreH8) (flag_del_build_unlink_layout sg PreH8)
    ltac:(lia) Hvalid Hwaiter) as [found Hdomain].
  assert (found = old_2) by (pose proof Hdomain as [_ [_ [Hfound _]]]; congruence).
  subst found.
  sep_apply_l_atomic (flag_del_iteration_task_rdy_next environment critical now_local_2 sg active_2
    cpu_sr acquired_2 current_2 pnode waiter_2 old_2 retval Hvalid Hdomain Haddress).
  Intros post.
  assert (Hloan : flag_del_loan_origin post waiter_2 original_2 fragments_2).
  { destruct PreH18 as [Hkey Hparked]; split; [exact Hkey|].
    match goal with Hstep : flag_del_step sg current_2 pnode post |- _ =>
      destruct Hstep as [ready Hstep];
      destruct (FlagPendSchedulerResources.flag_task_rdy_preserves_stack_metadata
        sg current_2 pnode 0 PendAbort ready post Hstep) as [Hstacks Hmetadata];
      rewrite Hstacks; exact Hparked
    end. }
  Exists post original_2 fragments_2 waiter_2 old_2 remaining_2 image_2 order_2 id_2 active_2 visited_2 acquired_2 protected_local_2 current_2 now_local_2.
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_25 : OSFlagDel_entail_wit_25.
Proof.
  left; intros.
  Exists post_2 original_2 fragments_2 waiter_2 old_2 remaining_2 image_2 order_2 id_2 active_2 visited_2 acquired_2 protected_local_2 current_2 now_local_2.
  unfold flag_del_iteration_next, flag_del_iteration_next_frame, flag_del_node_next.
  rewrite (flag_del_build_node_next_address sg node PreH8).
  Intros; entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_26 : OSFlagDel_entail_wit_26.
Proof.
  left; intros.
  pose proof PreH16 as [[Horder [Hfold [[group [Hgroup Hremaining]] [Hnode Hcut]]]] Hsource].
  pose proof PreH17 as [Hwaiter [Hold Haddress]].
  pose proof PreH18 as [Hkey Hparked].
  destruct PreH19 as [ready Hstep].
  assert (Hinitial : UCOS2_state_inv sg acquired_2) by (unfold flag_del_source_prefix_facts in PreH12; tauto).
  pose proof (flag_del_abort_waiters_preserves_validity__waiter_loop_and_publication sg visited_2 acquired_2 current Hinitial Hfold) as Hvalid.
  assert (Hnonzero : node <> 0).
  { destruct (flag_query_state_configuration sg current Hvalid) as [_ [_ [_ [_ [_ [_ [_ Hnodes]]]]]]].
    destruct (Hnodes node waiter Hwaiter); assumption. }
  destruct remaining_2 as [|head rest]; [cbn in Hnode; contradiction|].
  cbn in Hnode; subst head.
  destruct (flag_del_abort_head sg current id_2 group node rest Hvalid Hgroup Hremaining)
    as [selected [schedule [after [Hselected [Hnext [Hactual [Hpost Haftergroup]]]]]]].
  assert (selected = waiter) by congruence; subst selected.
  assert (after = post_2) by congruence; subst after.
  destruct (FlagPendSchedulerResources.flag_task_rdy_preserves_stack_metadata sg current node 0 PendAbort ready post_2 Hstep) as [Hstacks Hmetadata].
  assert (Hloan : flag_del_loan_origin current waiter original fragments).
  { split; [exact Hkey|]. rewrite <- Hstacks; exact Hparked. }
  assert (Hsourcepost : flag_del_source_cut sg active_2 post_2).
  { eapply flag_del_step_preserves_source_cut__waiter_loop_and_publication; [exists ready; exact Hstep|exact Hsource]. }
  assert (Hfoldpost : flag_del_abort_waiters sg (visited_2 ++ node::nil) acquired_2 = Some post_2).
  { pose proof (flag_del_abort_waiters_append sg visited_2 (node::nil) acquired_2 current Hfold) as Happend.
    etransitivity; [exact Happend|].
    cbn [flag_del_abort_waiters]; rewrite Hstep; reflexivity. }
  assert (Hlocal : flag_del_local_prefix sg (visited_2 ++ node::nil) acquired_2 protected_local_2 post_2
    (flag_del_published_local sg post_2 node waiter original now_local)).
  { eapply flag_del_local_prefix_append__waiter_loop_and_publication; [exact PreH2|].
    exists waiter, original, fragments, post_2; split; [exact Hwaiter|].
    split; [exact Hloan|]. split; [exists ready; exact Hstep|]. split; reflexivity. }
  assert (Hloop : flag_del_source_loop_facts sg active_2 acquired_2 id_2 order_2 (visited_2 ++ node::nil) rest post_2 (flag_del_node_next waiter)).
  { split.
    - split; [rewrite Horder, <- app_assoc; reflexivity|].
      split; [exact Hfoldpost|]. split.
      + exists (flag_group_set_wait_order group rest); split; [exact Haftergroup|reflexivity].
      + split; [unfold flag_del_node_next; rewrite Hnext; destruct rest; reflexivity|].
        apply flag_del_source_cut_call_cut; exact Hsourcepost.
    - exact Hsourcepost. }
  assert (Hdetached : post_2.(FlagState).(flagWaitNodes) node = None).
  { destruct (flag_task_rdy_result sg current node 0 PendAbort ready post_2 Hstep)
      as [chosen [flags [task [Hunlink [_ [Hafter _]]]]]].
    subst post_2; change (flags.(flagWaitNodes) node = None).
    exact (proj2 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hunlink)). }
  Exists rest image_2 order_2 id_2 active_2 (visited_2 ++ node::nil) acquired_2 protected_local_2 post_2
    (flag_del_published_local sg post_2 node waiter original now_local).
  unfold flag_del_iteration_next_frame; Intros.
  rewrite (flag_del_build_node_next_address sg node PreH8).
  unfold flag_del_node_next, os_sched_fields_capsules.
  pose proof (flag_del_fields_next_read_publish _ _ _ environment.(task_stack_call_continuations) sg post_2 node waiter original now_local fragments Haddress Hdetached Hkey Hparked) as Hpublish.
  rewrite Haddress in Hpublish.
  sep_apply_l_atomic Hpublish.
  unfold flag_del_masked, kernel_continuation_inv, flag_del_published_local.
  rewrite kernel_program_fields_inv_split_unmap.
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_27 : OSFlagDel_entail_wit_27.
Proof.
  left; intros.
  Exists remaining_3 image_3 order_3 id_3 active_3 visited_3 acquired_3 protected_local_3 post next_local.
  Exists remaining_3 pnode_2 tasks_waiting_2 image_3 order_3 id_3 active_3 cpu_sr_2 visited_3 acquired_3 protected_local_3 post next_local.
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_28 : OSFlagDel_entail_wit_28.
Proof.
  left; intros.
  assert (Hp : pointer <> 0) by (unfold flag_del_source_prefix_facts, flag_del_prefix_facts in PreH13; tauto).
  destruct (flag_del_pool_argument_implies_layout_address__drain_and_release_results sg pointer view before observed id_3 PreH12 Hp PreH14)
    as [Hlayout Hpointer].
  sep_apply_l_atomic (flag_del_masked_implies_state_inv__drain_and_release_results environment critical now_local_3 sg active_3 cpu_sr acquired_3 current_2). Intros.
  assert (Hinv : UCOS2_state_inv sg current_2) by assumption.
  pose proof PreH17 as Hloop. rewrite PreH1 in Hloop.
  destruct (flag_del_loop_zero_head_remaining_empty__drain_and_release_results sg active_3 acquired_3 id_3 order_3 visited_2 remaining_2 current_2 Hinv Hloop) as [Hnil [Horder [drained_image Himage]]].
  assert (Hloop' : flag_del_source_loop_facts sg active_3 acquired_3 id_3 order_3 order_3 nil current_2 0).
  { rewrite Hnil, <- Horder in Hloop. exact Hloop. }
  assert (Hlocal : flag_del_local_prefix sg order_3 acquired_3 protected_local_3 current_2 now_local_3).
  { rewrite Horder; exact PreH3. }
  assert (Hselected : flag_query_selected view current_2 drained_image) by (rewrite PreH14; exact Himage).
  sep_apply_l_atomic (flag_del_masked_split_group__drain_and_release_results environment critical now_local_3 sg active_3 cpu_sr acquired_3 pointer id_3 current_2 drained_image Hpointer Himage (flag_del_build_flag_names sg PreH9)).
  sep_apply store_ptr_undef_store_ptr.
  Exists drained_image image_3 id_3 active_3 order_3 acquired_3 protected_local_3 current_2 now_local_3.
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_29 : OSFlagDel_entail_wit_29.
Proof.
  left; intros.
  assert (Hp : pointer <> 0) by (unfold flag_del_source_prefix_facts, flag_del_prefix_facts in PreH12; tauto).
  destruct (flag_del_pool_argument_implies_layout_address__drain_and_release_results sg pointer view before observed id_2 PreH11 Hp PreH13)
    as [[Ht [Hh [Hb Hn]]] Hpointer].
  Exists drained_image_2 image_2 id_2 active_2 order_2 acquired_2 protected_local_2 drained_2 now_local_2.
  unfold flag_del_group_cut, flag_del_group_frame, flag_del_free_head_state.
  rewrite Ht, Hh, Hb, Hn, PreH6. entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_30 : OSFlagDel_entail_wit_30.
Proof.
  right; intros.
  assert (Hp : pointer <> 0) by (unfold flag_del_source_prefix_facts, flag_del_prefix_facts in PreH12; tauto).
  destruct (flag_del_pool_argument_implies_layout_address__drain_and_release_results sg pointer view before observed id PreH11 Hp PreH13)
    as [[Ht [Hh [Hb Hn]]] Hpointer].
  destruct PreH14 as [Himage [Htype [group [Hgroup Horder]]]].
  pose proof PreH16 as Hloop.
  destruct Hloop as [[Horder' [Hfold [[drained_group [Hdg Hempty]] [Hpn Hcall]]]] Hsource].
  assert (Hdi : drained.(FlagState).(flagImages) id = Some drained_image) by (rewrite PreH13 in PreH17; exact PreH17).
  assert (Hscheduled : flag_del_schedule_bit tasks_waiting = negb (Z.eqb (flagImageHead image) 0)).
  { rewrite PreH15. unfold flag_del_schedule_bit, flag_del_waiting.
    destruct (flagImageHead image); reflexivity. }
  assert (Hresult : flag_del_protected_result sg view pointer option name acquired_2 0 0 (flag_del_schedule_bit tasks_waiting) (flag_del_release_state sg drained id drained_image name)).
  { subst view option. rewrite Hscheduled.
    apply (flag_del_protected_always sg pointer name acquired_2 id group image drained drained_image Himage Htype Hgroup).
    - rewrite Horder; exact Hfold.
    - exact Hdi. }
  pose proof (flag_del_release_preserves_source_cut__drain_and_release_results sg active_2 drained id drained_image name Hsource) as Hcut.
  replace (LitMap "?" + 0 * sizeof(CHAR)) with name by lia.
  rewrite Ht, Hh, Hb, Hn, PreH6.
  sep_apply_l_atomic (flag_del_group_merge_released__drain_and_release_results environment critical now_local_2 sg active_2 cpu_sr acquired_2 pointer id drained drained_group drained_image name Hpointer Hdi Hdg Hempty (flag_del_build_flag_names sg PreH8)).
  Exists now_local_2 (flag_del_release_state sg drained id drained_image name) active_2 acquired_2.
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_31 : OSFlagDel_entail_wit_31.
Proof.
  unfold OSFlagDel_entail_wit_31; right; intros.
  subst scheduled_2.
  sep_apply (flag_del_restore_output_after_restore__restore_and_scheduler_returns
    environment critical now_local sg caller mask view pointer option name before observed
    active cpu_sr acquired 0 0 (flag_del_schedule_bit tasks_waiting) released restore_heap X
    PreH10 (proj1 PreH11) PreH13).
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_32 : OSFlagDel_entail_wit_32.
Proof.
  unfold OSFlagDel_entail_wit_32; left; intros.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range (&("tasks_waiting")) tasks_waiting); Intros.
  assert (Hbits : unsigned_last_nbits tasks_waiting 32 = tasks_waiting).
  { apply IntLib.unsigned_last_nbits_eq; change (0 <= tasks_waiting < 4294967296).
    change (0 <= tasks_waiting <= 255) in H; lia. }
  rewrite Hbits in PreH1.
  assert (Htrue : scheduled = true).
  { rewrite PreH12; unfold flag_del_schedule_bit; apply Z.eqb_eq; exact PreH1. }
  rewrite Htrue.
  unfold flag_del_source_after_restore; Intros returned current next_local.
  assert (Hprefix : flag_del_prefix_program environment critical sg caller mask view pointer option name
    before (((0,0),true),returned) current) by tauto.
  destruct (flag_del_scheduled_prefix_pool_view__restore_and_scheduler_returns
    environment critical sg caller mask view pointer option name before (0,0) returned current Hprefix) as [id Hview].
  assert (Hraw : flag_del_raw_type pointer view = emp).
  { rewrite Hview; unfold flag_del_raw_type.
    match goal with |- (if ?test then _ else _) = _ => destruct test; reflexivity end. }
  rewrite Hraw.
  assert (Hsource : flag_del_source_restore_cut sg returned current true) by tauto.
  destruct Hsource as [Hsource Hsched].
  destruct (Hsched eq_refl) as [context [Hreturned [Horigin Hcut]]].
  subst returned.
  pose proof (flag_del_source_active_stable sg) as Hstable.
  sep_apply (flag_del_source_scheduler_pre environment next_local sg context mask current Hcut Hsource).
  sep_apply (UCOS2_C_Rules.store_uchar_undef_store_uchar (&("tasks_waiting")) tasks_waiting).
  Exists next_local context current.
  unfold flag_del_prefix_to_scheduler, flag_del_same_task_call, flag_del_scheduler_safe.
  cbn [flag_del_tail_program] in *.
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_33 : OSFlagDel_entail_wit_33.
Proof.
  unfold OSFlagDel_entail_wit_33; right; intros.
  sep_apply (flag_del_restore_output_after_restore__restore_and_scheduler_returns
    environment critical protected_local sg caller mask view pointer option name before observed
    active cpu_sr acquired pointer 7 false acquired restore_heap X
    PreH11 (proj1 PreH12) PreH13).
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_34 : OSFlagDel_entail_wit_34.
Proof.
  left; intros.
  assert (Hp : pointer <> 0) by (unfold flag_del_source_prefix_facts, flag_del_prefix_facts in PreH10; tauto).
  destruct (flag_del_pool_argument_implies_layout_address__drain_and_release_results sg pointer view before observed id PreH9 Hp PreH11)
    as [Hlayout Hpointer].
  assert (Himage : acquired_2.(FlagState).(flagImages) id = Some image) by (rewrite PreH11 in PreH12; exact PreH12).
  assert (Hresult : flag_del_protected_result sg view pointer option name acquired_2 pointer 7 false acquired_2).
  { apply (flag_del_protected_invalid_option sg view pointer option name acquired_2 image PreH12); congruence. }
  sep_apply_l_atomic (flag_del_group_merge_original__drain_and_release_results environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id acquired_2 image Hpointer Himage (flag_del_build_flag_names sg PreH6)).
  sep_apply store_uchar_undef_store_uchar.
  Exists protected_local_2 active_2 acquired_2. entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_35_1 : OSFlagDel_entail_wit_35_1.
Proof.
  unfold OSFlagDel_entail_wit_35_1; left; intros.
  unfold flag_del_source_after_restore; Intros returned current next_local.
  assert (Hprogram : flag_del_program environment critical sg caller mask view pointer option name
    before (0,0) current).
  { unfold flag_del_program, StateRelBasic.StateRelMonad.bind.
    exists (((0,0),false),returned), current; split; [tauto|].
    split; reflexivity. }
  Exists next_local returned current 0.
  unfold flag_del_source_return_cut, flag_del_return_cut.
  cbn [flag_del_tail_program] in *.
  unfold flag_del_source_restore_cut in *.
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_35_2 : OSFlagDel_entail_wit_35_2.
Proof.
  unfold OSFlagDel_entail_wit_35_2; left; intros.
  unfold flag_del_source_after_restore; Intros returned current next_local.
  assert (Hprogram : flag_del_program environment critical sg caller mask view pointer option name
    before (pointer,73) current).
  { unfold flag_del_program, StateRelBasic.StateRelMonad.bind.
    exists (((pointer,73),false),returned), current; split; [tauto|].
    split; reflexivity. }
  Exists next_local returned current 73.
  unfold flag_del_source_return_cut, flag_del_return_cut.
  cbn [flag_del_tail_program] in *.
  unfold flag_del_source_restore_cut in *.
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_35_3 : OSFlagDel_entail_wit_35_3.
Proof.
  unfold OSFlagDel_entail_wit_35_3; left; intros.
  assert (Hprefix : flag_del_prefix_program environment critical sg caller mask view pointer option name
    before (((0,0),true),TaskSuspendTask context) current_2) by exact PreH12.
  destruct (flag_del_scheduled_prefix_pool_view__restore_and_scheduler_returns
    environment critical sg caller mask view pointer option name before (0,0)
    (TaskSuspendTask context) current_2 Hprefix) as [id Hview].
  assert (Hraw : flag_del_raw_type pointer view = emp).
  { rewrite Hview; unfold flag_del_raw_type.
    match goal with |- (if ?test then _ else _) = _ => destruct test; reflexivity end. }
  unfold os_sched_active_history_return_post, flag_del_source_active; Intros returned current next_local.
  assert (Hhistory : os_sched_continuation_call_history environment critical sg context mask current_2 returned current) by tauto.
  assert (Hstep : task_suspend_schedule_program environment critical sg
    (TaskSuspendTask context) mask current_2 (TaskSuspendTask returned) current).
  { cbn [task_suspend_schedule_program]. exists returned, current; split.
    - apply os_sched_continuation_program_iff; exact Hhistory.
    - split; reflexivity. }
  assert (Hprogram : flag_del_program environment critical sg caller mask view pointer option name before (0,0) current).
  { unfold flag_del_program, StateRelBasic.StateRelMonad.bind.
    exists (((0,0),true),TaskSuspendTask context),current_2; split; [exact Hprefix|].
    cbn [flag_del_tail_program].
    exists (TaskSuspendTask returned),current; split; [exact Hstep|].
    split; reflexivity. }
  pose proof (flag_del_schedule_safe_return environment critical sg (TaskSuspendTask context) mask
    current_2 (TaskSuspendTask returned) current (0,0) X Hstep PreH13) as Hsafe.
  assert (Hsame : task_suspend_same_call (TaskSuspendTask returned) caller).
  { eapply task_suspend_same_call_trans; [|exact PreH14].
    cbn [task_suspend_same_call]; tauto. }
  Exists next_local (TaskSuspendTask returned) current 0.
  unfold flag_del_source_return_cut, flag_del_return_cut.
  rewrite Hraw.
  unfold flag_del_closed, flag_del_context, flag_del_active_key, task_suspend_view,
    os_sched_execution_view, kernel_continuation_call_closed, kernel_call_execution_owned.
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_35_4 : OSFlagDel_entail_wit_35_4.
Proof.
  unfold OSFlagDel_entail_wit_35_4; left; intros.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range (&("tasks_waiting")) tasks_waiting); Intros.
  assert (Hbits : unsigned_last_nbits tasks_waiting 32 = tasks_waiting).
  { apply IntLib.unsigned_last_nbits_eq; change (0 <= tasks_waiting < 4294967296).
    change (0 <= tasks_waiting <= 255) in H; lia. }
  rewrite Hbits in PreH1.
  assert (Hfalse : scheduled = false).
  { rewrite PreH12; unfold flag_del_schedule_bit; apply Z.eqb_neq; exact PreH1. }
  rewrite Hfalse.
  unfold flag_del_source_after_restore; Intros returned current next_local.
  assert (Hprogram : flag_del_program environment critical sg caller mask view pointer option name
    before (0,0) current).
  { unfold flag_del_program, StateRelBasic.StateRelMonad.bind.
    exists (((0,0),false),returned), current; split; [tauto|].
    split; reflexivity. }
  Exists next_local returned current 0.
  unfold flag_del_source_return_cut, flag_del_return_cut.
  cbn [flag_del_tail_program] in *.
  unfold flag_del_source_restore_cut in *.
  sep_apply (UCOS2_C_Rules.store_uchar_undef_store_uchar (&("tasks_waiting")) tasks_waiting).
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_entail_wit_35_5 : OSFlagDel_entail_wit_35_5.
Proof.
  unfold OSFlagDel_entail_wit_35_5; left; intros.
  unfold flag_del_source_after_restore; Intros returned current next_local.
  assert (Hprogram : flag_del_program environment critical sg caller mask view pointer option name
    before (pointer,7) current).
  { unfold flag_del_program, StateRelBasic.StateRelMonad.bind.
    exists (((pointer,7),false),returned), current; split; [tauto|].
    split; reflexivity. }
  Exists next_local returned current 7.
  unfold flag_del_source_return_cut, flag_del_return_cut.
  cbn [flag_del_tail_program] in *.
  unfold flag_del_source_restore_cut in *.
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_partial_solve_wit_6_pure : OSFlagDel_partial_solve_wit_6_pure.
Proof.
  left; intros.
  unfold flag_del_source_restore_cut.
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_partial_solve_wit_8_pure : OSFlagDel_partial_solve_wit_8_pure.
Proof.
  left; intros.
  unfold flag_del_source_restore_cut.
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_partial_solve_wit_10_pure : OSFlagDel_partial_solve_wit_10_pure.
Proof.
  left; intros.
  unfold flag_del_source_restore_cut.
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_partial_solve_wit_12_pure : OSFlagDel_partial_solve_wit_12_pure.
Proof.
  left; intros.
  unfold os_sched_global_addresses, sched_new_global_addresses in PreH5.
  entailer!; try reflexivity; tauto.
Qed. 

Lemma proof_of_OSFlagDel_partial_solve_wit_13_pure : OSFlagDel_partial_solve_wit_13_pure.
Proof.
  left; intros; subst option.
  assert (Hrestore : UCOS2_state_inv sg released ->
    flag_del_source_restore_cut sg active released scheduled).
  {
    intro Hreleased.
    split; [exact PreH14|]. intro Hscheduled.
    destruct PreH11 as [Hprefix [Hacquired [Hsource [Hbefore Hphase]]]].
    destruct active as [call|handler].
    - exists call; split; [reflexivity|].
      assert (Hrunning : os_sched_call_origin call <> BootInvocation).
      {
        intro Hboot.
        unfold flag_del_source_cut in Hsource; rewrite Hboot in Hsource.
        destruct Hsource as [_ [_ Hnone]].
        pose proof (flag_del_protected_always_no_waiters_unscheduled__save_restore_call_cuts
          sg view pointer name acquired scheduled released Hacquired Hnone PreH13).
        congruence.
      }
      split; [exact Hrunning|].
      apply flag_del_running_source_sched_cut__save_restore_call_cuts;
        [exact Hrunning|exact PreH14|exact Hreleased|exact PreH8].
    - destruct caller as [call|original_view].
      + destruct Hprefix as [_ [_ [_ [_ [_ [Hsame _]]]]]].
        contradiction.
      + assert (Horiginal_facts : flag_del_source_prefix_facts environment critical sg
          (TaskSuspendDisabled original_view) mask view pointer 1 name before observed
          (TaskSuspendDisabled handler) cpu_sr acquired X).
        { exact (conj Hprefix (conj Hacquired (conj Hsource (conj Hbefore Hphase)))). }
        destruct (flag_del_source_prefix_disabled_boot environment critical sg original_view
          mask view pointer 1 name before observed (TaskSuspendDisabled handler)
          cpu_sr acquired X Horiginal_facts) as [_ Hboot].
        destruct Hboot as [interrupt [interrupted [_ [_ [_ [_ Hnone]]]]]].
        pose proof (flag_del_protected_always_no_waiters_unscheduled__save_restore_call_cuts
          sg view pointer name acquired scheduled released Hacquired Hnone PreH13).
        congruence.
  }
  unfold flag_del_masked, kernel_continuation_inv, kernel_program_fields_inv.
  Intros.
  match goal with Hvalid : UCOS2_state_inv sg released |- _ =>
    pose proof (Hrestore Hvalid) as Hcut
  end.
  rewrite <- PreH12.
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_partial_solve_wit_17_pure : OSFlagDel_partial_solve_wit_17_pure.
Proof.
  left; intros.
  unfold flag_del_source_restore_cut.
  entailer!.
Qed. 

Lemma proof_of_OSFlagDel_which_implies_wit_1 : OSFlagDel_which_implies_wit_1.
Proof. left; intros; apply flag_del_source_public_entry_open. Qed. 

Lemma proof_of_OSFlagDel_which_implies_wit_2 : OSFlagDel_which_implies_wit_2.
Proof.
  left; intros.
  unfold os_sched_global_addresses in PreH1; destruct PreH1 as [Haddr _].
  rewrite Haddr.
  apply (proj1 (flag_del_closed_nesting_equiv__entry_and_early_returns environment local sg caller mask before)).
Qed. 

Lemma proof_of_OSFlagDel_which_implies_wit_3 : OSFlagDel_which_implies_wit_3.
Proof.
  left; intros.
  destruct PreH2 as [Hz|[_ [[Htype _] _]]]; [contradiction|].
  rewrite Htype.
  unfold flag_del_type_cut, flag_del_type_read_frame; entailer!.
Qed. 

Lemma proof_of_OSFlagDel_which_implies_wit_4 : OSFlagDel_which_implies_wit_4.
Proof.
  left; intros; intros heap Howned.
  exists heap; split; [reflexivity|].
  split; [split; assumption|exact Howned].
Qed. 

Lemma proof_of_OSFlagDel_which_implies_wit_5 : OSFlagDel_which_implies_wit_5.
Proof.
  left; intros; intros heap Howned.
  exists heap; split; [reflexivity|].
  split; [split; assumption|exact Howned].
Qed. 

Lemma proof_of_OSFlagDel_which_implies_wit_6 : OSFlagDel_which_implies_wit_6.
Proof.
  left; intros; intros heap Howned.
  exists heap; split; [reflexivity|].
  split; [split; assumption|exact Howned].
Qed. 

Lemma proof_of_OSFlagDel_which_implies_wit_7 : OSFlagDel_which_implies_wit_7.
Proof.
  left; intros; intros heap Howned.
  exists heap; split; [reflexivity|].
  split; [split; assumption|exact Howned].
Qed. 

Lemma proof_of_OSFlagDel_which_implies_wit_8 : OSFlagDel_which_implies_wit_8.
Proof.
  left; intros; intros heap Howned.
  exists heap; split; [reflexivity|].
  split; [split; assumption|exact Howned].
Qed. 

Lemma proof_of_OSFlagDel_which_implies_wit_9 : OSFlagDel_which_implies_wit_9.
Proof.
  left; intros; intros heap Howned.
  exists heap; split; [reflexivity|].
  split; [split; assumption|exact Howned].
Qed. 

