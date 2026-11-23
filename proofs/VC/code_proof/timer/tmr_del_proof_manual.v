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
From Ucos2Verify.VC.code.timer Require Import tmr_del_goal.
From Ucos2Verify.VC.code.timer Require Import tmr_del_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_del_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.timer_execution.
Import UCOS2_C_Rules.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTmrDel_return_wit_1 : OSTmrDel_return_wit_1.
Proof.
  unfold OSTmrDel_return_wit_1; left; intros.
  subst ptmr_pre perr0.
  lazymatch goal with
  | Hresult : tmr_del_result_prop ?crit ?globals ?inv ?ptr ?name ?initial ?completion ?result,
    Hsafe : safeExec (tmr_del_at_state ?initial)
      (tmr_del_call_program ?resources ?crit ?globals ?caller ?ptr ?name) ?continuation |- _ =>
      pose proof (tmr_del_api_post_after_unlock resources platform crit globals caller mask
        initial ptr name perr_pre completion result continuation Hresult eq_refl Hsafe) as Hpost;
      cbn [tmr_del_return tmr_del_result_ret tmr_del_result_err tmr_del_success_result
        tmr_del_inactive_result tmr_del_invalid_state_result encode_os_err_code] in Hpost;
      sep_apply_l_atomic Hpost; entailer!
  end.
Qed.

Lemma proof_of_OSTmrDel_return_wit_2 : OSTmrDel_return_wit_2.
Proof.
  unfold OSTmrDel_return_wit_2; left; intros.
  subst ptmr_pre perr0.
  lazymatch goal with
  | Hresult : tmr_del_result_prop ?crit ?globals ?inv ?ptr ?name ?initial ?completion ?result,
    Hsafe : safeExec (tmr_del_at_state ?initial)
      (tmr_del_call_program ?resources ?crit ?globals ?caller ?ptr ?name) ?continuation |- _ =>
      pose proof (tmr_del_api_post_after_unlock resources platform crit globals caller mask
        initial ptr name perr_pre completion result continuation Hresult eq_refl Hsafe) as Hpost;
      cbn [tmr_del_return tmr_del_result_ret tmr_del_result_err tmr_del_success_result
        tmr_del_inactive_result tmr_del_invalid_state_result encode_os_err_code] in Hpost;
      sep_apply_l_atomic Hpost; entailer!
  end.
Qed.

Lemma proof_of_OSTmrDel_return_wit_3 : OSTmrDel_return_wit_3.
Proof.
  unfold OSTmrDel_return_wit_3; left; intros.
  subst ptmr_pre perr0.
  lazymatch goal with
  | Hresult : tmr_del_result_prop ?crit ?globals ?inv ?ptr ?name ?initial ?completion ?result,
    Hsafe : safeExec (tmr_del_at_state ?initial)
      (tmr_del_call_program ?resources ?crit ?globals ?caller ?ptr ?name) ?continuation |- _ =>
      pose proof (tmr_del_api_post_after_unlock resources platform crit globals caller mask
        initial ptr name perr_pre completion result continuation Hresult eq_refl Hsafe) as Hpost;
      cbn [tmr_del_return tmr_del_result_ret tmr_del_result_err tmr_del_success_result
        tmr_del_inactive_result tmr_del_invalid_state_result encode_os_err_code] in Hpost;
      sep_apply_l_atomic Hpost; entailer!
  end.
Qed.

Lemma proof_of_OSTmrDel_return_wit_4 : OSTmrDel_return_wit_4.
Proof.
  unfold OSTmrDel_return_wit_4; left; intros.
  subst ptmr_pre perr0.
  lazymatch goal with
  | Hresult : tmr_del_result_prop ?crit ?globals ?inv ?ptr ?name ?initial ?completion ?result,
    Hsafe : safeExec (tmr_del_at_state ?initial)
      (tmr_del_call_program ?resources ?crit ?globals ?caller ?ptr ?name) ?continuation |- _ =>
      pose proof (tmr_del_api_post_after_unlock resources platform crit globals caller mask
        initial ptr name perr_pre completion result continuation Hresult eq_refl Hsafe) as Hpost;
      cbn [tmr_del_return tmr_del_result_ret tmr_del_result_err tmr_del_success_result
        tmr_del_inactive_result tmr_del_invalid_state_result encode_os_err_code] in Hpost;
      sep_apply_l_atomic Hpost; entailer!
  end.
Qed.

Lemma proof_of_OSTmrDel_return_wit_5 : OSTmrDel_return_wit_5.
Proof.
  unfold OSTmrDel_return_wit_5; left; intros.
  subst ptmr_pre perr0.
  lazymatch goal with
  | Hresult : tmr_del_result_prop ?crit ?globals ?inv ?ptr ?name ?initial ?completion ?result,
    Hsafe : safeExec (tmr_del_at_state ?initial)
      (tmr_del_call_program ?resources ?crit ?globals ?caller ?ptr ?name) ?continuation |- _ =>
      pose proof (tmr_del_api_post_after_unlock resources platform crit globals caller mask
        initial ptr name perr_pre completion result continuation Hresult eq_refl Hsafe) as Hpost;
      cbn [tmr_del_return tmr_del_result_ret tmr_del_result_err tmr_del_success_result
        tmr_del_inactive_result tmr_del_invalid_state_result encode_os_err_code] in Hpost;
      sep_apply_l_atomic Hpost; entailer!
  end.
Qed.

Lemma proof_of_OSTmrDel_return_wit_6 : OSTmrDel_return_wit_6.
Proof.
  unfold OSTmrDel_return_wit_6; left; intros.
  subst ptmr_pre perr0.
  prop_apply (store_uchar_range &(ptmr0 # "os_tmr" ->ₛ "OSTmrType")
    (tmr_del_image_type image)); Intros.
  prop_apply (store_uchar_range &("OSIntNesting")
    (tmr_del_int_nesting before)); Intros.
  rewrite IntLib.unsigned_last_nbits_eq in PreH1 by
    (change (0 <= tmr_del_int_nesting before < 4294967296);
     assert (Hrange : 0 <= tmr_del_int_nesting before <= 255) by assumption; lia).
  rewrite IntLib.unsigned_last_nbits_eq in PreH2 by
    (change (0 <= tmr_del_image_type image < 4294967296);
     assert (Hrange : 0 <= tmr_del_image_type image <= 255) by assumption; lia).
  assert (Hresult : tmr_del_result_prop critical sg
    (os_sched_call_invocation context) ptmr0 (LitMap "?") before before
    (TmrDelResultValue false OS_ERR_TMR_ISR)).
  { unfold tmr_del_result_prop; right; right; left; split; [exact PreH8|].
    exists i, image.
    destruct PreH3 as [_ [_ [Hpointer Himage]]].
    unfold tmr_del_image_type, tmr_del_int_nesting in *; repeat split; auto. }
  pose proof (tmr_del_api_post_early external platform critical sg context mask before
    ptmr0 (LitMap "?") perr_pre (TmrDelResultValue false OS_ERR_TMR_ISR) X
    Hresult eq_refl PreH14) as Hpost.
  sep_apply_l_atomic (tmr_del_merge_observed_cells sg before ptmr0 i image PreH5 PreH3 PreH6).
  unfold tmr_del_early_post in Hpost.
  cbn [tmr_del_return tmr_del_result_ret tmr_del_result_err encode_os_err_code] in Hpost.
  sep_apply_l_atomic Hpost; entailer!.
Qed.

Lemma proof_of_OSTmrDel_return_wit_7 : OSTmrDel_return_wit_7.
Proof.
  unfold OSTmrDel_return_wit_7; left; intros.
  subst ptmr_pre perr0.
  assert (Htype : tmr_del_image_type image <> 100).
  { intro Heq; rewrite Heq in PreH1; vm_compute in PreH1; tauto. }
  assert (Hresult : tmr_del_result_prop critical sg
    (os_sched_call_invocation context) ptmr0 (LitMap "?") before before
    (TmrDelResultValue false OS_ERR_TMR_INVALID_TYPE)).
  { unfold tmr_del_result_prop; right; left; split; [exact PreH7|].
    exists i, image.
    destruct PreH2 as [_ [_ [Hpointer Himage]]].
    unfold tmr_del_image_type in Htype; auto. }
  pose proof (tmr_del_api_post_early external platform critical sg context mask before
    ptmr0 (LitMap "?") perr_pre (TmrDelResultValue false OS_ERR_TMR_INVALID_TYPE) X
    Hresult eq_refl PreH13) as Hpost.
  cbn [tmr_del_return tmr_del_result_ret tmr_del_result_err encode_os_err_code] in Hpost.
  rewrite <- Hpost.
  unfold tmr_del_early_post.
  rewrite <- (tmr_del_merge_observed_cells sg before ptmr0 i image PreH4 PreH2 PreH5).
  entailer!.
Qed.

Lemma proof_of_OSTmrDel_return_wit_8 : OSTmrDel_return_wit_8.
Proof.
  unfold OSTmrDel_return_wit_8; left; intros.
  subst ptmr_pre ptmr0 perr0.
  assert (Hresult : tmr_del_result_prop critical sg
    (os_sched_call_invocation context) 0 (LitMap "?") before before
    (TmrDelResultValue false OS_ERR_TMR_INVALID)).
  { unfold tmr_del_result_prop; left; auto. }
  pose proof (tmr_del_api_post_early external platform critical sg context mask before
    0 (LitMap "?") perr_pre (TmrDelResultValue false OS_ERR_TMR_INVALID) X
    Hresult eq_refl PreH7) as Hpost.
  unfold tmr_del_pre; Intros.
  unfold tmr_del_early_post in Hpost.
  cbn [tmr_del_return tmr_del_result_ret tmr_del_result_err encode_os_err_code] in Hpost.
  sep_apply_l_atomic Hpost; entailer!.
Qed.

Lemma proof_of_OSTmrDel_partial_solve_wit_3_pure : OSTmrDel_partial_solve_wit_3_pure.
Proof.
  unfold OSTmrDel_partial_solve_wit_3_pure; left; intros; subst ptmr_pre.
  prop_apply (store_uchar_range &(ptmr0 # "os_tmr" ->ₛ "OSTmrType")
    (tmr_del_image_type image)); Intros.
  prop_apply (store_uchar_range &("OSIntNesting")
    (tmr_del_int_nesting before)); Intros.
  rewrite IntLib.unsigned_last_nbits_eq in PreH1 by
    (change (0 <= tmr_del_int_nesting before < 4294967296);
     assert (Hrange : 0 <= tmr_del_int_nesting before <= 255) by assumption; lia).
  rewrite IntLib.unsigned_last_nbits_eq in PreH2 by
    (change (0 <= tmr_del_image_type image < 4294967296);
     assert (Hrange : 0 <= tmr_del_image_type image <= 255) by assumption; lia).
  assert (Haddresses : os_sched_lock_global_addresses sg &("OSRunning")
    &("OSIntNesting") &("OSLockNesting")).
  { unfold tmr_del_c_bindings, os_sched_unlock_global_addresses,
      os_sched_global_addresses, os_sched_lock_global_addresses in *; tauto. }
  entailer!.
Qed. 

Lemma proof_of_OSTmrDel_partial_solve_wit_14_pure : OSTmrDel_partial_solve_wit_14_pure.
Proof.
  unfold OSTmrDel_partial_solve_wit_14_pure; left; intros.
  assert (Hstopped : tmr_del_image_stopped current_image).
  { unfold tmr_del_image_stopped; right; symmetry; exact PreH23. }
  entailer!.
Qed. 

Lemma proof_of_OSTmrDel_partial_solve_wit_15_pure : OSTmrDel_partial_solve_wit_15_pure.
Proof.
  unfold OSTmrDel_partial_solve_wit_15_pure; left; intros.
  assert (Hstopped : tmr_del_image_stopped current_image).
  { unfold tmr_del_image_stopped; left; symmetry; exact PreH22. }
  entailer!.
Qed. 

Lemma proof_of_OSTmrDel_which_implies_wit_1 : OSTmrDel_which_implies_wit_1.
Proof.
  unfold OSTmrDel_which_implies_wit_1; left; intros.
  destruct PreH3 as [Hzero|Hobs]; [contradiction|].
  unfold tmr_del_pre; Intros.
  assert (Hbindings : tmr_del_c_bindings sg ptmr0) by tauto.
  assert (Htype : &(ptmr0 # "os_tmr" ->ₛ "OSTmrType") = ptmr0).
  { unfold tmr_del_c_bindings, tmr_free_bindings, tmr_free_layout in Hbindings; tauto. }
  assert (Hints : &("OSIntNesting") = g_OSIntNesting sg).
  { unfold tmr_del_c_bindings, os_sched_unlock_global_addresses,
      os_sched_global_addresses in Hbindings; tauto. }
  pose proof Hobs as [Henabled [Hinit [Hpointer Himage]]].
  sep_apply_l_atomic (tmr_del_split_observations sg before i image Henabled Hinit Himage).
  rewrite Htype, Hints; subst ptmr0.
  unfold tmr_del_image_type, tmr_del_int_nesting.
  entailer!.
Qed. 

Lemma proof_of_OSTmrDel_which_implies_wit_2 : OSTmrDel_which_implies_wit_2.
Proof.
  unfold OSTmrDel_which_implies_wit_2; left; intros.
  assert (Hchecks : tmr_del_checks_passed ptmr0 image before).
  { apply tmr_del_early_result_continue_iff; auto. }
  apply _derivable1_andp_intros; [entailer!|].
  sep_apply (tmr_del_merge_observed_cells sg before ptmr0 i image PreH2 PreH1 PreH7).
  rewrite <- (tmr_del_lock_pre_from_inv platform critical sg
    (os_sched_call_invocation context) (os_sched_call_origin context) mask before).
  entailer!.
Qed. 

Lemma proof_of_OSTmrDel_which_implies_wit_3 : OSTmrDel_which_implies_wit_3.
Proof.
  unfold OSTmrDel_which_implies_wit_3; left; intros.
  rewrite tmr_del_lock_post_to_inv.
  Intros acquired locked.
  assert (Hlock : os_sched_lock_call_relation critical sg
    (os_sched_call_invocation context) before acquired locked) by assumption.
  pose proof (timer_public_trace_public_storage_frame sg (TimerState before)
    (TimerState locked) (os_sched_lock_call_timer_public_trace critical sg
      (os_sched_call_invocation context) before acquired locked Hlock)) as Hstorage.
  pose proof PreH4 as [Henabled [Hinit [Hpointer Himage]]].
  pose proof (timer_public_storage_frame_initialized _ _ Hstorage Hinit) as Hlockedinit.
  destruct (timer_public_storage_frame_has_image _ _ i image Hstorage Himage)
    as [current Hcurrent].
  assert (Hhistory : tmr_del_call_history critical sg (os_sched_call_invocation context)
    before ptmr0 i image locked).
  { split; [exact PreH4|]; split; [exact PreH3|]; exists acquired; exact Hlock. }
  assert (Hcfg : osKernelConfig sg = selected_kernel_configuration).
  { unfold tmr_del_c_bindings, tmr_free_bindings in PreH2; tauto. }
  assert (Htype : &(ptmr0 # "os_tmr" ->ₛ "OSTmrType") = ptmr0).
  { unfold tmr_del_c_bindings, tmr_free_bindings, tmr_free_layout in PreH2; tauto. }
  assert (Hstate : &(ptmr0 # "os_tmr" ->ₛ "OSTmrState") = ptmr0 + 37).
  { unfold tmr_del_c_bindings, tmr_free_bindings, tmr_free_layout in PreH2; tauto. }
  assert (Hoffset : timer_option_offset (osKernelConfig sg) = 36).
  { rewrite Hcfg; reflexivity. }
  sep_apply_l_atomic (tmr_del_split_locked_state sg locked i current
    Henabled Hlockedinit Hcurrent).
  Exists current locked.
  rewrite Htype, Hstate; subst ptmr0.
  unfold tmr_del_image_type, tmr_del_image_state, tmr_del_timer_state,
    tmr_del_locked_image.
  rewrite Hoffset.
  replace (timer_pool_addr sg i + 36 + 1) with (timer_pool_addr sg i + 37) by lia.
  entailer!.
Qed.

Lemma proof_of_OSTmrDel_which_implies_wit_4 : OSTmrDel_which_implies_wit_4.
Proof.
  unfold OSTmrDel_which_implies_wit_4; left; intros.
  pose proof (tmr_del_bindings_unlink_profile sg ptmr0 locked PreH1 PreH3) as Hprofile.
  pose proof (tmr_del_initialized_timer_valid sg ptmr0 locked PreH1 PreH3 PreH4) as Htimer.
  destruct PreH2 as [[_ [_ [Hpointer _]]] _].
  assert (Hnonzero : timerImageState current_image <> 0) by
    (unfold tmr_del_image_state in PreH6; lia).
  destruct (valid_timer_state_nonunused_image sg (TimerState locked) i current_image
    Htimer PreH5 Hnonzero) as [node [Hnode Hencode]].
  assert (Hrunning : tmr_unlink_running (tmr_del_timer_state locked) i).
  { exists node; split; [exact Hnode|].
    unfold tmr_del_image_state in PreH6.
    destruct (timerState node); cbn in Hencode; congruence. }
  assert (Hlayout : tmr_unlink_layout) by (unfold tmr_del_c_bindings in PreH1; tauto).
  assert (Hwheel : &("OSTmrWheelTbl") = g_OSTmrWheelTbl sg).
  { unfold tmr_del_c_bindings in PreH1; tauto. }
  assert (Hconfiguration : valid_timer_configuration sg (TimerState locked)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in PreH3; tauto. }
  apply _derivable1_andp_intros; [entailer!|].
  rewrite (tmr_del_merge_locked_cells sg locked ptmr0 i current_image
    PreH1 Hpointer PreH3 PreH4 PreH5).
  rewrite UCOS2_inv_split_timer.
  unfold timer_inv, tmr_del_timer_state; entailer!.
Qed. 

Lemma proof_of_OSTmrDel_which_implies_wit_6 : OSTmrDel_which_implies_wit_6.
Proof.
  unfold OSTmrDel_which_implies_wit_6; left; intros.
  pose proof (tmr_del_initialized_timer_valid sg ptmr0 locked PreH1 PreH4 PreH3) as Htimer.
  assert (Hfree_bindings : tmr_free_bindings sg ptmr0).
  { unfold tmr_del_c_bindings in PreH1; tauto. }
  destruct PreH5 as [node [Hnode Hrunning]].
  destruct Htimer as [_ [_ [_ [_ [_ [_ [_ [Hused _]]]]]]]].
  destruct (Hused i node Hnode) as [_ [_ [_ [original [Horiginal Hrepr]]]]].
  assert (Hstate : timerImageState original = 3).
  { rewrite Hrepr; change (encode_timer_status (timerState node) = 3).
    rewrite Hrunning; reflexivity. }
  unfold tmr_unlink_configured_post; Intros post.
  assert (Hunlink : timer_unlink sg (tmr_del_timer_state locked) i = Some post) by tauto.
  destruct (tmr_del_unlink_produces_free_input sg (tmr_del_timer_state locked)
    i ptmr0 post Hfree_bindings PreH2 PreH3 Hunlink) as [after_node [old Hinput]].
  assert (Hold : timerImages post i = Some old).
  { unfold tmr_free_valid_input in Hinput; tauto. }
  assert (Hfree : tmr_del_free_input sg post i old (timer_pool_addr sg i)).
  { exists after_node; rewrite <- PreH2; exact Hinput. }
  assert (Hrelease : tmr_del_release_step sg locked post i old (LitMap "?")).
  { exists (timer_release sg post i old (LitMap "?")); split; [|reflexivity].
    eapply TmrDelRunning; eassumption. }
  Exists post old; entailer!.
Qed. 

Lemma proof_of_OSTmrDel_which_implies_wit_7 : OSTmrDel_which_implies_wit_7.
Proof.
  unfold OSTmrDel_which_implies_wit_7; left; intros.
  sep_apply_l_atomic (tmr_del_released_unlock_pre external platform critical sg context mask
      before ptmr0 i image locked s old (LitMap "?")
      PreH1 PreH2 PreH3 PreH4 PreH5 PreH6).
  entailer!.
Qed. 

Lemma proof_of_OSTmrDel_which_implies_wit_8 : OSTmrDel_which_implies_wit_8.
Proof.
  unfold OSTmrDel_which_implies_wit_8; left; intros.
  pose proof (tmr_del_initialized_timer_valid sg ptmr0 locked PreH1 PreH3 PreH4) as Htimer.
  destruct PreH2 as [[_ [_ [Hpointer _]]] _].
  assert (Hfree_bindings : tmr_free_bindings sg ptmr0).
  { unfold tmr_del_c_bindings in PreH1; tauto. }
  destruct (tmr_del_stopped_produces_free_input sg (tmr_del_timer_state locked) i ptmr0
    current_image Hfree_bindings Hpointer Htimer PreH4 PreH5 PreH6) as [node Hinput].
  assert (Hfree : tmr_del_free_input sg (tmr_del_timer_state locked) i current_image ptmr0).
  { exists node; exact Hinput. }
  assert (Hrelease : tmr_del_release_step sg locked (tmr_del_timer_state locked)
    i current_image (LitMap "?")).
  { exists (timer_release sg (tmr_del_timer_state locked) i current_image (LitMap "?"));
      split; [|reflexivity].
    eapply TmrDelStopped; eassumption. }
  assert (Hconfiguration : valid_timer_configuration sg (TimerState locked)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in PreH3; tauto. }
  apply _derivable1_andp_intros; [entailer!|].
  sep_apply (tmr_del_merge_locked_cells sg locked ptmr0 i current_image
    PreH1 Hpointer PreH3 PreH4 PreH5).
  rewrite UCOS2_inv_split_timer.
  unfold timer_inv, tmr_del_timer_state; entailer!.
Qed. 

Lemma proof_of_OSTmrDel_which_implies_wit_9 : OSTmrDel_which_implies_wit_9.
Proof.
  unfold OSTmrDel_which_implies_wit_9; left; intros.
  sep_apply_l_atomic (tmr_del_released_unlock_pre external platform critical sg context mask
      before ptmr0 i image locked (tmr_del_timer_state locked) current_image (LitMap "?")
      PreH1 PreH2 PreH3 PreH4 PreH5 PreH6).
  entailer!.
Qed. 

Lemma proof_of_OSTmrDel_which_implies_wit_10 : OSTmrDel_which_implies_wit_10.
Proof.
  unfold OSTmrDel_which_implies_wit_10; left; intros.
  assert (Hstep : tmr_del_locked_state_step sg locked i (LitMap "?") false OS_ERR_TMR_INACTIVE locked).
  { exists (TimerState locked); split.
    - eapply TmrDelUnused; eassumption.
    - rewrite replace_TimerS_put_back; reflexivity. }
  sep_apply_l_atomic (tmr_del_unchanged_unlock_pre external platform critical sg context mask
      before ptmr0 i image locked current_image (LitMap "?") tmr_del_inactive_result
      PreH1 PreH2 PreH3 PreH4 PreH5 Hstep PreH7).
  entailer!.
Qed. 

Lemma proof_of_OSTmrDel_which_implies_wit_11 : OSTmrDel_which_implies_wit_11.
Proof.
  unfold OSTmrDel_which_implies_wit_11; left; intros.
  assert (Hstep : tmr_del_locked_state_step sg locked i (LitMap "?") false OS_ERR_TMR_INVALID_STATE locked).
  { exists (TimerState locked); split.
    - eapply TmrDelInvalidState; eassumption.
    - rewrite replace_TimerS_put_back; reflexivity. }
  sep_apply_l_atomic (tmr_del_unchanged_unlock_pre external platform critical sg context mask
      before ptmr0 i image locked current_image (LitMap "?") tmr_del_invalid_state_result
      PreH1 PreH2 PreH3 PreH4 PreH5 Hstep PreH10).
  entailer!.
Qed. 

