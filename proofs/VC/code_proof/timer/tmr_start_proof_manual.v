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
From Ucos2Verify.VC.code.timer Require Import tmr_start_goal.
From Ucos2Verify.VC.code.timer Require Import tmr_start_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_start_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTmrStart_return_wit_1 : OSTmrStart_return_wit_1.
Proof.
  left; intros; subst.
  eapply tmr_start_post_after_unlock; eassumption.
Qed.

Lemma proof_of_OSTmrStart_return_wit_2 : OSTmrStart_return_wit_2.
Proof.
  left; intros; subst.
  eapply tmr_start_post_after_unlock; eassumption.
Qed.

Lemma proof_of_OSTmrStart_return_wit_3 : OSTmrStart_return_wit_3.
Proof.
  left; intros; subst perr_pre.
  eapply tmr_start_post_after_unlock; eassumption.
Qed.

Lemma proof_of_OSTmrStart_return_wit_4 : OSTmrStart_return_wit_4.
Proof.
  left; intros; subst perr_pre.
  eapply tmr_start_post_after_unlock; eassumption.
Qed.

Lemma proof_of_OSTmrStart_return_wit_5 : OSTmrStart_return_wit_5.
Proof.
  left; intros; subst perr_pre.
  eapply tmr_start_post_after_unlock; eassumption.
Qed.

Lemma proof_of_OSTmrStart_return_wit_6 : OSTmrStart_return_wit_6.
Proof.
  left; intros; subst perr_pre.
  rewrite (unsigned_last_nbits_eq ty 32) in PreH11 by
    (change (0 <= ty < 4294967296); lia).
  eapply tmr_start_post_early; [exact PreH5|].
  unfold tmr_start_call_result.
  destruct (Z.eq_dec p 0); [contradiction|].
  destruct (Z.eq_dec ty 100); [|contradiction].
  destruct (Z_gt_dec (os_sched_lock_ints before) 0); [auto|lia].
Qed.

Lemma proof_of_OSTmrStart_return_wit_7 : OSTmrStart_return_wit_7.
Proof.
  left; intros; subst perr_pre.
  assert (Htype : ty <> 100).
  { intro E; subst ty; apply PreH2; reflexivity. }
  eapply tmr_start_post_early; [exact PreH1|].
  unfold tmr_start_call_result.
  destruct (Z.eq_dec p 0); [contradiction|].
  destruct (Z.eq_dec ty 100); [contradiction|auto].
Qed.

Lemma proof_of_OSTmrStart_return_wit_8 : OSTmrStart_return_wit_8.
Proof.
  left; intros; subst perr_pre.
  assert (Hp : p = 0) by lia.
  eapply tmr_start_post_early; [exact PreH9|].
  unfold tmr_start_call_result; rewrite Hp.
  destruct (Z.eq_dec 0 0); [auto|contradiction].
Qed.

Lemma proof_of_OSTmrStart_partial_solve_wit_6_pure : OSTmrStart_partial_solve_wit_6_pure.
Proof.
  left; intros.
  unfold os_sched_lock_global_addresses.
  unfold os_sched_unlock_global_addresses, os_sched_global_addresses in PreH19.
  entailer!; tauto.
Qed.

Lemma proof_of_OSTmrStart_partial_solve_wit_7_pure : OSTmrStart_partial_solve_wit_7_pure.
Proof.
  left; intros.
  rewrite (unsigned_last_nbits_eq ty 32) in PreH11 by
    (change (0 <= ty < 4294967296); lia).
  assert (Hints : os_sched_lock_ints before = 0) by lia.
  entailer!.
Qed.

Lemma proof_of_OSTmrStart_partial_solve_wit_17_pure : OSTmrStart_partial_solve_wit_17_pure.
Proof.
  left; intros; unfold tmr_start_nonrunning_status; entailer!.
Qed.

Lemma proof_of_OSTmrStart_partial_solve_wit_18_pure : OSTmrStart_partial_solve_wit_18_pure.
Proof.
  left; intros; unfold tmr_start_nonrunning_status; entailer!.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_1 : OSTmrStart_which_implies_wit_1.
Proof.
  left; intros.
  destruct PreH2 as [Htype Hstate]; rewrite Htype.
  pose proof PreH3 as Hfacts.
  destruct Hfacts as [_ [_ [Hprofile [Hclient _]]]].
  destruct Hprofile as [Henabled Hprofile].
  unfold tmr_start_owned, tmr_start_type_rest, tmr_start_raw_rep.
  destruct pooled.
  - destruct Hclient as [Hp [Hnonzero [Hinitialized [image [Himage Hty]]]]].
    rewrite UCOS2_inv_split_timer; Intros.
    sep_apply_l_atomic (timer_configured_rep_split_type sg (TimerState before) i image
      Henabled Hinitialized Himage).
    Exists image; rewrite Hp, Hty; entailer!.
    + rewrite <- Hp, <- Hty; exact PreH3.
    + unfold tmr_start_layout; split; [reflexivity|].
      rewrite <- Hp; exact Hstate.
  - destruct (Z.eq_dec p 0); [contradiction|].
    entailer!; unfold tmr_start_layout; auto.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_2 : OSTmrStart_which_implies_wit_2.
Proof.
  left; intros.
  destruct PreH2 as [Htype Hstate]; rewrite Htype.
  pose proof PreH3 as Hfacts.
  destruct Hfacts as [_ [_ [Hprofile [Hclient _]]]].
  destruct Hprofile as [Henabled Hprofile].
  unfold tmr_start_owned, tmr_start_type_rest, tmr_start_raw_rep.
  destruct pooled.
  - destruct Hclient as [Hp [Hnonzero [Hinitialized Himage]]].
    Intros image; destruct H as [Hvalid [Hlookup Hty]].
    rewrite Hp, Hty.
    sep_apply_l_atomic (timer_configured_rep_merge_type sg (TimerState before) i image
      Henabled Hinitialized Hlookup).
    rewrite UCOS2_inv_split_timer; entailer!.
    rewrite <- Hp, <- Hty; exact PreH3.
  - destruct (Z.eq_dec p 0); [contradiction|].
    entailer!.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_3 : OSTmrStart_which_implies_wit_3.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range (&((p) # "os_tmr" ->ₛ "OSTmrType")) ty).
  Intros.
  destruct proof_of_OSTmrStart_which_implies_wit_2 as [Hmerge|Hmerge];
    specialize (Hmerge X before raw_state ty i p pooled mask context sg critical
      platform external PreH2 PreH3 PreH4);
    sep_apply Hmerge;
    unfold tmr_start_owned, tmr_start_int_rest;
    rewrite UCOS2_inv_split_interrupt;
    unfold interrupt_inv, store_int_state, os_sched_lock_ints;
    Intros;
    prop_apply_p (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState before)));
    rewrite PreH1; entailer!.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_4 : OSTmrStart_which_implies_wit_4.
Proof.
  left; intros.
  unfold tmr_start_owned, tmr_start_int_rest.
  rewrite UCOS2_inv_split_interrupt.
  unfold interrupt_inv, store_int_state, interrupt_in_range, os_sched_lock_ints.
  rewrite PreH1.
  prop_apply_p (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState before))).
  prop_apply_p (store_uchar_range (g_OSLockNesting sg) (lockNesting (IntrState before))).
  entailer!.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_5 : OSTmrStart_which_implies_wit_5.
Proof.
  left; intros.
  destruct proof_of_OSTmrStart_which_implies_wit_4 as [Hmerge|Hmerge];
    specialize (Hmerge before raw_state ty p pooled mask context sg platform external PreH1 PreH2);
    sep_apply Hmerge;
    rewrite os_sched_lock_pre_closed_equiv, tmr_start_closed_raw_equiv;
    unfold tmr_start_owned, tmr_start_execution_frame, UCOS2_inv;
    entailer!.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_6 : OSTmrStart_which_implies_wit_6.
Proof.
  left; intros.
  rewrite os_sched_lock_post_closed_equiv; Intros entry locked.
  destruct H as [Hcall Hvalid].
  pose proof (tmr_start_lock_preserves_public_storage critical sg context before entry locked Hcall)
    as Hstorage.
  unfold tmr_start_owned, tmr_start_execution_frame, UCOS2_inv.
  rewrite tmr_start_closed_raw_equiv.
  destruct pooled.
  - pose proof PreH4 as Hfacts.
    destruct Hfacts as [_ [_ [_ [Hclient _]]]].
    destruct Hclient as [Hp [Hnonzero [Hinitialized [image [Himage Hty]]]]].
    destruct (timer_public_storage_frame_has_image (TimerState before) (TimerState locked)
      i image Hstorage Himage) as [current Hcurrent].
    pose proof (timer_public_storage_frame_initialized _ _ Hstorage Hinitialized) as Hinit.
    Exists (timerImageState current) entry locked.
    unfold tmr_start_current; entailer!; exists current; auto.
  - Exists raw_state entry locked.
    unfold tmr_start_current; entailer!.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_7 : OSTmrStart_which_implies_wit_7.
Proof.
  left; intros.
  destruct PreH4 as [Htype Hstate]; rewrite Hstate.
  pose proof PreH5 as Hfacts.
  destruct Hfacts as [_ [_ [[Henabled [Hnames Hprofile]] _]]].
  unfold tmr_start_owned, tmr_start_state_rest, tmr_start_raw_rep.
  destruct pooled.
  - destruct PreH6 as [Hp [Hinitialized [image [Himage Hstatus]]]].
    rewrite UCOS2_inv_split_timer; Intros.
    rewrite (timer_initialized_configured_rep_eq sg (TimerState locked) Henabled Hinitialized).
    pose proof (timer_complete_split_state sg (TimerState locked) i image Himage) as Hsplit.
    unfold timer_option_offset in Hsplit; rewrite Hnames in Hsplit.
    replace (timer_pool_addr sg i + 36 + 1) with (timer_pool_addr sg i + 37) in Hsplit by lia.
    sep_apply_l_atomic Hsplit.
    Exists image; rewrite Hp, Hstatus; entailer!.
    + unfold tmr_start_current; split; [reflexivity|].
      split; [exact Hinitialized|]; exists image; auto.
    + rewrite <- Hp; exact PreH5.
    + unfold tmr_start_layout; split; [|reflexivity].
      rewrite <- Hp; exact Htype.
  - destruct (Z.eq_dec p 0); [contradiction|].
    unfold tmr_start_raw_state_rep.
    destruct (Z.eq_dec ty 100); [|contradiction].
    rewrite PreH3; destruct (Z.eq_dec 0 0); [|contradiction].
    unfold tmr_start_current in PreH6; rewrite PreH6.
    entailer!; unfold tmr_start_current, tmr_start_layout; auto.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_8 : OSTmrStart_which_implies_wit_8.
Proof.
  left; intros.
  pose proof PreH6 as Hfacts.
  destruct Hfacts as [Hlink_layout [Hunlink_layout [Hprofile [Hclient _]]]].
  assert (Hunlink_profile : tmr_unlink_profile sg) by exact Hprofile.
  destruct pooled.
  - pose proof PreH8 as Hcurrent.
    destruct PreH8 as [Hp [Hinit [v [Hv Hstatus]]]].
    unfold tmr_start_state_rest; Intros image.
    destruct H as [Hvalid [Himage Himage_state]].
    assert (Hconfig : valid_timer_configuration sg (TimerState locked)).
    { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
    assert (Henabled : cfgTimerEnabled (osKernelConfig sg) = true) by (destruct Hprofile; assumption).
    pose proof (proj1 (timer_initialized_configuration_iff sg (TimerState locked) Henabled Hinit) Hconfig) as Htimers.
    destruct (valid_timer_state_nonunused_image sg (TimerState locked) i image Htimers Himage ltac:(lia)) as [node [Hnode Hencoded]].
    assert (Hrunning : timerState node = TimerRunning).
    { destruct (timerState node); simpl in Hencoded; try reflexivity; lia. }
    assert (Heligible : tmr_unlink_running (TimerState locked) i) by (exists node; auto).
    pose proof (timer_complete_rep_merge_current_state__timer_updates sg (TimerState locked) i image Himage) as Hmerge.
    assert (Hoffset : timer_option_offset (osKernelConfig sg) = 36).
    { unfold timer_option_offset; destruct Hprofile as [_ [Hnames _]]; rewrite Hnames; reflexivity. }
    rewrite Hoffset in Hmerge.
    replace (timer_pool_addr sg i + 36 + 1) with (p + 37) in Hmerge by lia.
    rewrite <- Himage_state, <- (proj2 PreH5) in Hmerge.
    sep_apply_l_atomic Hmerge.
    unfold tmr_start_timer_frame, timer_inv.
    rewrite (timer_initialized_configured_rep_eq sg (TimerState locked) Henabled Hinit).
    entailer!.
  - cbn [tmr_start_client] in Hclient.
    specialize (Hclient PreH1 PreH2 PreH3).
    cbn [tmr_start_current] in PreH8; exfalso; lia.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_9 : OSTmrStart_which_implies_wit_9.
Proof.
  left; intros.
  unfold tmr_unlink_configured_post; Intros stopped.
  destruct H as [Hstep Hinit].
  pose proof (tmr_start_unlinked_eligible sg (TimerState locked) i stopped PreH4 Hstep) as Heligible.
  destruct PreH4 as [node [Hnode Hrunning]].
  assert (Hvalid : UCOS2_state_inv sg (replace_TimerS stopped locked)).
  { eapply UCOS2_timer_unlink_preserves_validity; eauto.
    unfold tmr_link_profile in PreH3; tauto. }
  Exists stopped; entailer!.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_10 : OSTmrStart_which_implies_wit_10.
Proof.
  left; intros; subst pooled.
  unfold tmr_link_configured_post; Intros started.
  destruct H as [Hlink Hinit].
  change (timer_link sg stopped i false = Some started) in Hlink.
  assert (Hprofile : tmr_link_profile sg) by (unfold tmr_start_pre_facts in PreH4; tauto).
  assert (Henabled : cfgTimerEnabled (osKernelConfig sg) = true) by (destruct Hprofile; assumption).
  destruct PreH10 as [node [Hnode Hnonrunning]].
  pose proof (UCOS2_timer_link_preserves_validity sg (replace_TimerS stopped locked)
    i node false started PreH11 Henabled PreH12 Hnode Hnonrunning Hlink) as Hvalid.
  assert (Hprefix : tmr_start_prefix critical sg context true p i ty raw_state 1 0
    before lock_entry locked (replace_TimerS started locked)).
  { unfold tmr_start_prefix.
    refine (conj PreH1 (conj PreH2 (conj PreH3 (conj PreH5 _)))).
    unfold tmr_start_locked_step; exists true, OS_ERR_NONE, started; split.
    - destruct PreH6 as [Hp [Hinitold [v [Hv Hstatus]]]].
      unfold timer_start_locked; rewrite Hv, <- Hstatus, PreH8; cbn [Z.eqb].
      unfold tmr_start_unlinked in PreH9; rewrite PreH9, Hlink; reflexivity.
    - repeat split; reflexivity. }
  Exists started.
  unfold tmr_start_owned, tmr_start_timer_frame, tmr_start_raw_rep, timer_inv.
  Intros.
  pose proof (UCOS2_inv_merge_updated_timer sg locked (replace_TimerS started locked)
    Hvalid ltac:(symmetry; apply UCOS2_raw_rep_missing_timer_replace_eq)) as Hmerge.
  change (timer_configured_rep sg started ** UCOS2_raw_rep_missing_timer sg locked
    |-- UCOS2_inv sg (replace_TimerS started locked)) in Hmerge.
  sep_apply Hmerge.
  entailer!.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_11 : OSTmrStart_which_implies_wit_11.
Proof.
  left; intros; entailer!.
  eapply tmr_start_owned_unlock_pre__unlock_returns; eassumption.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_12 : OSTmrStart_which_implies_wit_12.
Proof.
  left; intros; apply tmr_start_unlock_post_return.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_13 : OSTmrStart_which_implies_wit_13.
Proof.
  left; intros.
  pose proof PreH6 as Hfacts.
  destruct Hfacts as [Hlink_layout [Hunlink_layout [Hprofile [Hclient _]]]].
  assert (Hunlink_profile : tmr_unlink_profile sg) by exact Hprofile.
  destruct pooled.
  - pose proof PreH8 as Hcurrent.
    destruct PreH8 as [Hp [Hinit [v [Hv Hstatus]]]].
    unfold tmr_start_state_rest; Intros image.
    destruct H as [Hvalid [Himage Himage_state]].
    assert (Hconfig : valid_timer_configuration sg (TimerState locked)).
    { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
    assert (Henabled : cfgTimerEnabled (osKernelConfig sg) = true) by (destruct Hprofile; assumption).
    pose proof (proj1 (timer_initialized_configuration_iff sg (TimerState locked) Henabled Hinit) Hconfig) as Htimers.
    assert (Hnonzero : timerImageState image <> 0) by (unfold tmr_start_nonrunning_status in PreH4; lia).
    destruct (valid_timer_state_nonunused_image sg (TimerState locked) i image Htimers Himage Hnonzero) as [node [Hnode Hencoded]].
    assert (Hnonrunning : timerState node <> TimerRunning).
    { intro Hr; rewrite Hr in Hencoded; simpl in Hencoded.
      unfold tmr_start_nonrunning_status in PreH4; lia. }
    assert (Heligible : tmr_link_eligible (TimerState locked) i) by (exists node; auto).
    pose proof (timer_complete_rep_merge_current_state__timer_updates sg (TimerState locked) i image Himage) as Hmerge.
    assert (Hoffset : timer_option_offset (osKernelConfig sg) = 36).
    { unfold timer_option_offset; destruct Hprofile as [_ [Hnames _]]; rewrite Hnames; reflexivity. }
    rewrite Hoffset in Hmerge.
    replace (timer_pool_addr sg i + 36 + 1) with (p + 37) in Hmerge by lia.
    rewrite <- Himage_state, <- (proj2 PreH5) in Hmerge.
    sep_apply_l_atomic Hmerge.
    unfold tmr_start_timer_frame, timer_inv.
    rewrite (timer_initialized_configured_rep_eq sg (TimerState locked) Henabled Hinit).
    entailer!.
  - cbn [tmr_start_client] in Hclient.
    specialize (Hclient PreH1 PreH2 PreH3).
    cbn [tmr_start_current] in PreH8.
    unfold tmr_start_nonrunning_status in PreH4; exfalso; lia.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_14 : OSTmrStart_which_implies_wit_14.
Proof.
  left; intros; subst pooled.
  unfold tmr_link_configured_post; Intros started.
  destruct H as [Hlink Hinit].
  change (timer_link sg (TimerState locked) i false = Some started) in Hlink.
  assert (Hprofile : tmr_link_profile sg) by (unfold tmr_start_pre_facts in PreH4; tauto).
  assert (Henabled : cfgTimerEnabled (osKernelConfig sg) = true) by (destruct Hprofile; assumption).
  destruct PreH9 as [node [Hnode Hnonrunning]].
  pose proof (UCOS2_timer_link_preserves_validity sg locked i node false started
    PreH10 Henabled PreH11 Hnode Hnonrunning Hlink) as Hvalid.
  assert (Hprefix : tmr_start_prefix critical sg context true p i ty raw_state 1 0
    before lock_entry locked (replace_TimerS started locked)).
  { unfold tmr_start_prefix.
    refine (conj PreH1 (conj PreH2 (conj PreH3 (conj PreH5 _)))).
    unfold tmr_start_locked_step; exists true, OS_ERR_NONE, started; split.
    - destruct PreH6 as [Hp [Hinitold [v [Hv Hstatus]]]].
      unfold timer_start_locked; rewrite Hv, <- Hstatus.
      destruct PreH8 as [Hs|Hs]; rewrite Hs; cbn [Z.eqb orb]; rewrite Hlink; reflexivity.
    - repeat split; reflexivity. }
  Exists started.
  unfold tmr_start_owned, tmr_start_timer_frame, tmr_start_raw_rep, timer_inv.
  Intros.
  pose proof (UCOS2_inv_merge_updated_timer sg locked (replace_TimerS started locked)
    Hvalid ltac:(symmetry; apply UCOS2_raw_rep_missing_timer_replace_eq)) as Hmerge.
  change (timer_configured_rep sg started ** UCOS2_raw_rep_missing_timer sg locked
    |-- UCOS2_inv sg (replace_TimerS started locked)) in Hmerge.
  sep_apply Hmerge.
  entailer!.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_15 : OSTmrStart_which_implies_wit_15.
Proof.
  left; intros; entailer!.
  eapply tmr_start_owned_unlock_pre__unlock_returns; eassumption.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_16 : OSTmrStart_which_implies_wit_16.
Proof.
  left; intros; apply tmr_start_unlock_post_return.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_17 : OSTmrStart_which_implies_wit_17.
Proof.
  left; intros.
  assert (Hstep : tmr_start_locked_step sg pooled i raw_state locked (0, 135) locked).
  { unfold tmr_start_locked_step.
    destruct pooled.
    - destruct PreH8 as [Hp [Hinit [image [Hlookup Hstatus]]]].
      exists false, OS_ERR_TMR_INACTIVE, (TimerState locked).
      split; [eapply timer_start_locked_unused; eauto; lia|].
      split; [reflexivity|]. split; [reflexivity|symmetry; apply replace_TimerS_put_back].
    - simpl in PreH8; subst status; simpl; auto. }
  assert (Hprefix : tmr_start_prefix critical sg context pooled p i ty raw_state
    0 135 before lock_entry locked locked) by (unfold tmr_start_prefix; tauto).
  destruct PreH5 as [_ Hstate]; rewrite Hstate.
  sep_apply (tmr_start_state_rest_merge__unlock_returns external platform sg context mask
    pooled p i ty raw_state status before locked PreH1 PreH2 PreH3
    ltac:(unfold tmr_start_pre_facts in PreH6; tauto) PreH8).
  entailer!.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_18 : OSTmrStart_which_implies_wit_18.
Proof.
  left; intros; entailer!.
  eapply tmr_start_owned_unlock_pre__unlock_returns; eassumption.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_19 : OSTmrStart_which_implies_wit_19.
Proof.
  left; intros; apply tmr_start_unlock_post_return.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_20 : OSTmrStart_which_implies_wit_20.
Proof.
  left; intros; apply tmr_start_unlock_post_return.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_21 : OSTmrStart_which_implies_wit_21.
Proof.
  left; intros; entailer!.
  eapply tmr_start_owned_unlock_pre__unlock_returns; eassumption.
Qed.

Lemma proof_of_OSTmrStart_which_implies_wit_22 : OSTmrStart_which_implies_wit_22.
Proof.
  left; intros.
  assert (Hstep : tmr_start_locked_step sg pooled i raw_state locked (0, 141) locked).
  { unfold tmr_start_locked_step.
    destruct pooled.
    - destruct PreH11 as [Hp [Hinit [image [Hlookup Hstatus]]]].
      exists false, OS_ERR_TMR_INVALID_STATE, (TimerState locked).
      split; [eapply timer_start_locked_invalid_state; eauto; lia|].
      split; [reflexivity|]. split; [reflexivity|symmetry; apply replace_TimerS_put_back].
    - simpl in PreH11; subst status; simpl; tauto. }
  assert (Hprefix : tmr_start_prefix critical sg context pooled p i ty raw_state
    0 141 before lock_entry locked locked) by (unfold tmr_start_prefix; tauto).
  destruct PreH8 as [_ Hstate]; rewrite Hstate.
  sep_apply (tmr_start_state_rest_merge__unlock_returns external platform sg context mask
    pooled p i ty raw_state status before locked PreH1 PreH2 PreH3
    ltac:(unfold tmr_start_pre_facts in PreH9; tauto) PreH11).
  entailer!.
Qed.

