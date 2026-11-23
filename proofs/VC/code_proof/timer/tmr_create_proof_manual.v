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
From Ucos2Verify.VC.code.timer Require Import tmr_create_goal.
From Ucos2Verify.VC.code.timer Require Import tmr_create_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_create_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Import UCOS2_C_Rules.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTmrCreate_entail_wit_1_1 : OSTmrCreate_entail_wit_1_1.
Proof.
  left; intros; unfold store_uint; entailer!.
  apply tmr_create_argument_error_none_iff; left; split; congruence.
Qed. 

Lemma proof_of_OSTmrCreate_entail_wit_1_2 : OSTmrCreate_entail_wit_1_2.
Proof.
  left; intros; unfold store_uint; entailer!.
  apply tmr_create_argument_error_none_iff; right; split; congruence.
Qed. 

Lemma proof_of_OSTmrCreate_entail_wit_2_1 : OSTmrCreate_entail_wit_2_1.
Proof.
  left; intros; unfold store_uchar; entailer!.
  unfold tmr_create_first_error, tmr_create_early_error.
  rewrite PreH3.
  destruct H as [_ [Hnest_nonnegative Hnest_upper]].
  change (tmr_create_nesting before <= 255) in Hnest_upper.
  rewrite unsigned_last_nbits_eq in PreH1 by
    (change (0 <= tmr_create_nesting before < 4294967296); lia).
  unfold tmr_create_nesting in PreH1.
  rewrite (proj2 (Z.ltb_ge _ _) PreH1); reflexivity.
Qed. 

Lemma proof_of_OSTmrCreate_entail_wit_2_2 : OSTmrCreate_entail_wit_2_2.
Proof.
  left; intros; unfold store_uchar; entailer!.
  unfold tmr_create_first_error, tmr_create_early_error.
  rewrite PreH3.
  destruct H as [_ [Hnest_nonnegative Hnest_upper]].
  change (tmr_create_nesting before <= 255) in Hnest_upper.
  rewrite unsigned_last_nbits_eq in PreH1 by
    (change (0 <= tmr_create_nesting before < 4294967296); lia).
  unfold tmr_create_nesting in PreH1.
  rewrite (proj2 (Z.ltb_ge _ _) PreH1); reflexivity.
Qed. 

Lemma proof_of_OSTmrCreate_return_wit_1 : OSTmrCreate_return_wit_1.
Proof.
  left; intros.
  unfold tmr_create_output_binding in PreH31; subst perr_pre.
  rewrite (proj1 (proj2 (proj2 PreH1))).
  pose proof (tmr_create_api_post_after_unlock env args before
    (TmrCreateStored i private) completion perr0 X PreH2 eq_refl PreH24) as Hpost.
  cbn [tmr_create_result_pointer tmr_create_result_error error_codes.encode_os_err_code]
    in Hpost.
  sep_apply_r_atomic Hpost; entailer!.
Qed.

Lemma proof_of_OSTmrCreate_return_wit_2 : OSTmrCreate_return_wit_2.
Proof.
  left; intros.
  unfold tmr_create_output_binding in PreH31; subst perr_pre.
  rewrite (proj1 (proj2 (proj2 PreH1))).
  pose proof (tmr_create_api_post_after_unlock env args before
    (TmrCreateStored i private) completion perr0 X PreH2 eq_refl PreH24) as Hpost.
  cbn [tmr_create_result_pointer tmr_create_result_error error_codes.encode_os_err_code]
    in Hpost.
  sep_apply_r_atomic Hpost; entailer!.
Qed.

Lemma proof_of_OSTmrCreate_return_wit_3 : OSTmrCreate_return_wit_3.
Proof.
  left; intros.
  unfold tmr_create_output_binding in PreH29; subst perr_pre.
  rewrite (proj1 (proj2 (proj2 PreH1))).
  pose proof (tmr_create_api_post_after_unlock env args before
    (TmrCreateStored i private) completion perr0 X PreH2 eq_refl PreH22) as Hpost.
  cbn [tmr_create_result_pointer tmr_create_result_error error_codes.encode_os_err_code]
    in Hpost.
  sep_apply_r_atomic Hpost; entailer!.
Qed.

Lemma proof_of_OSTmrCreate_return_wit_4 : OSTmrCreate_return_wit_4.
Proof.
  left; intros.
  unfold tmr_create_output_binding in PreH29; subst perr_pre.
  rewrite (proj1 (proj2 (proj2 PreH1))).
  pose proof (tmr_create_api_post_after_unlock env args before
    (TmrCreateStored i private) completion perr0 X PreH2 eq_refl PreH22) as Hpost.
  cbn [tmr_create_result_pointer tmr_create_result_error error_codes.encode_os_err_code]
    in Hpost.
  sep_apply_r_atomic Hpost; entailer!.
Qed.

Lemma proof_of_OSTmrCreate_return_wit_5 : OSTmrCreate_return_wit_5.
Proof.
  left; intros.
  unfold tmr_create_output_binding in PreH26; subst perr_pre.
  pose proof (tmr_create_api_post_after_unlock env args before
    TmrCreateExhausted locked perr0 X PreH2 eq_refl PreH19) as Hpost.
  cbn [tmr_create_result_pointer tmr_create_result_error tmr_create_result_storage
    error_codes.encode_os_err_code] in Hpost.
  sep_apply_r_atomic Hpost; entailer!.
Qed.

Lemma proof_of_OSTmrCreate_return_wit_6 : OSTmrCreate_return_wit_6.
Proof.
  left; intros.
  unfold tmr_create_output_binding in PreH26; subst perr_pre.
  pose proof (tmr_create_api_post_after_unlock env args before
    TmrCreateExhausted locked perr0 X PreH2 eq_refl PreH19) as Hpost.
  cbn [tmr_create_result_pointer tmr_create_result_error tmr_create_result_storage
    error_codes.encode_os_err_code] in Hpost.
  sep_apply_r_atomic Hpost; entailer!.
Qed.

Lemma proof_of_OSTmrCreate_return_wit_7 : OSTmrCreate_return_wit_7.
Proof.
  left; intros.
  unfold tmr_create_output_binding in PreH17; subst perr_pre.
  assert (Haddress : &("OSIntNesting") = (tmr_create_globals env).(g_OSIntNesting)).
  { destruct PreH2 as [_ [[_ [Haddresses _]] _]].
    exact (proj1 (proj2 Haddresses)). }
  rewrite Haddress.
  prop_apply_p (store_uchar_range (tmr_create_globals env).(g_OSIntNesting)
    (tmr_create_nesting before)); Intros.
  assert (Hnest : 0 < tmr_create_nesting before).
  { rewrite unsigned_last_nbits_eq in PreH1.
    - lia.
    - change (0 <= tmr_create_nesting before < 4294967296).
      replace Byte.max_unsigned with 255 in * by reflexivity; lia. }
  assert (Herror : tmr_create_first_error args before = Some error_codes.OS_ERR_TMR_ISR).
  { apply tmr_create_early_error_isr; assumption. }
  pose proof (tmr_create_api_post_early__return_refinement env args before
    error_codes.OS_ERR_TMR_ISR perr0 X Herror PreH10) as Hpost.
  cbn [error_codes.encode_os_err_code] in Hpost.
  sep_apply_r_atomic Hpost.
  sepcon_assoc_change.
  sep_apply_r_atomic (tmr_create_observation_merge__return_refinement env before).
  entailer!.
Qed.

Lemma proof_of_OSTmrCreate_return_wit_8 : OSTmrCreate_return_wit_8.
Proof.
  left; intros.
  unfold tmr_create_output_binding in PreH17; subst perr_pre.
  assert (Haddress : &("OSIntNesting") = (tmr_create_globals env).(g_OSIntNesting)).
  { destruct PreH2 as [_ [[_ [Haddresses _]] _]].
    exact (proj1 (proj2 Haddresses)). }
  rewrite Haddress.
  prop_apply_p (store_uchar_range (tmr_create_globals env).(g_OSIntNesting)
    (tmr_create_nesting before)); Intros.
  assert (Hnest : 0 < tmr_create_nesting before).
  { rewrite unsigned_last_nbits_eq in PreH1.
    - lia.
    - change (0 <= tmr_create_nesting before < 4294967296).
      replace Byte.max_unsigned with 255 in * by reflexivity; lia. }
  assert (Herror : tmr_create_first_error args before = Some error_codes.OS_ERR_TMR_ISR).
  { apply tmr_create_early_error_isr; assumption. }
  pose proof (tmr_create_api_post_early__return_refinement env args before
    error_codes.OS_ERR_TMR_ISR perr0 X Herror PreH10) as Hpost.
  cbn [error_codes.encode_os_err_code] in Hpost.
  sep_apply_r_atomic Hpost.
  sepcon_assoc_change.
  sep_apply_r_atomic (tmr_create_observation_merge__return_refinement env before).
  entailer!.
Qed.

Lemma proof_of_OSTmrCreate_return_wit_9 : OSTmrCreate_return_wit_9.
Proof.
  left; intros.
  unfold tmr_create_output_binding in PreH9; subst perr_pre.
  assert (Herror : tmr_create_first_error args before =
    Some error_codes.OS_ERR_TMR_INVALID_OPT).
  { apply tmr_create_argument_error_precedes_isr.
    apply tmr_create_argument_error_invalid; congruence. }
  pose proof (tmr_create_api_post_early__return_refinement env args before
    error_codes.OS_ERR_TMR_INVALID_OPT perr0 X Herror PreH2) as Hpost.
  cbn [error_codes.encode_os_err_code] in Hpost.
  sep_apply_r_atomic Hpost; entailer!.
Qed.

Lemma proof_of_OSTmrCreate_return_wit_10 : OSTmrCreate_return_wit_10.
Proof.
  left; intros.
  unfold tmr_create_output_binding in PreH10; subst perr_pre.
  assert (Herror : tmr_create_first_error args before =
    Some error_codes.OS_ERR_TMR_INVALID_DLY).
  { apply tmr_create_argument_error_precedes_isr.
    rewrite <- PreH6, <- PreH4, <- PreH13, PreH1; reflexivity. }
  pose proof (tmr_create_api_post_early__return_refinement env args before
    error_codes.OS_ERR_TMR_INVALID_DLY perr0 X Herror PreH3) as Hpost.
  cbn [error_codes.encode_os_err_code] in Hpost.
  sep_apply_r_atomic Hpost; entailer!.
Qed.

Lemma proof_of_OSTmrCreate_return_wit_11 : OSTmrCreate_return_wit_11.
Proof.
  left; intros.
  unfold tmr_create_output_binding in PreH10; subst perr_pre.
  assert (Herror : tmr_create_first_error args before =
    Some error_codes.OS_ERR_TMR_INVALID_PERIOD).
  { apply tmr_create_argument_error_precedes_isr.
    rewrite <- PreH6, <- PreH5, <- PreH12, PreH1; reflexivity. }
  pose proof (tmr_create_api_post_early__return_refinement env args before
    error_codes.OS_ERR_TMR_INVALID_PERIOD perr0 X Herror PreH3) as Hpost.
  cbn [error_codes.encode_os_err_code] in Hpost.
  sep_apply_r_atomic Hpost; entailer!.
Qed.

Lemma proof_of_OSTmrCreate_partial_solve_wit_14_pure : OSTmrCreate_partial_solve_wit_14_pure.
Proof. left; intros; unfold tmr_create_pointer_null; entailer!. Qed. 

Lemma proof_of_OSTmrCreate_partial_solve_wit_15_pure : OSTmrCreate_partial_solve_wit_15_pure.
Proof. left; intros; unfold tmr_create_pointer_null; entailer!. Qed. 

Lemma proof_of_OSTmrCreate_partial_solve_wit_26_pure : OSTmrCreate_partial_solve_wit_26_pure.
Proof.
  left; intros; unfold tmr_create_chosen_name.
  rewrite tmr_create_name_nonnull by congruence; entailer!.
Qed. 

Lemma proof_of_OSTmrCreate_partial_solve_wit_27_pure : OSTmrCreate_partial_solve_wit_27_pure.
Proof.
  left; intros; unfold tmr_create_chosen_name.
  rewrite tmr_create_name_nonnull by congruence; entailer!.
Qed. 

Lemma proof_of_OSTmrCreate_partial_solve_wit_28_pure : OSTmrCreate_partial_solve_wit_28_pure.
Proof.
  left; intros; unfold tmr_create_chosen_name.
  assert (Hname : tmr_create_name_argument args = 0) by congruence.
  rewrite Hname, tmr_create_name_null; entailer!.
Qed. 

Lemma proof_of_OSTmrCreate_partial_solve_wit_29_pure : OSTmrCreate_partial_solve_wit_29_pure.
Proof.
  left; intros; unfold tmr_create_chosen_name.
  assert (Hname : tmr_create_name_argument args = 0) by congruence.
  rewrite Hname, tmr_create_name_null; entailer!.
Qed. 

Lemma proof_of_OSTmrCreate_which_implies_wit_1 : OSTmrCreate_which_implies_wit_1.
Proof. left; intros; unfold tmr_create_api_pre; entailer!. Qed. 

Lemma proof_of_OSTmrCreate_which_implies_wit_2 : OSTmrCreate_which_implies_wit_2.
Proof.
  right; intros before args env Hentry.
  destruct Hentry as [_ [[_ [Haddresses _]] _]].
  unfold os_sched_unlock_global_addresses in Haddresses.
  destruct Haddresses as [_ [Hnest _]].
  unfold tmr_create_return_frame, critical_region_outside.
  rewrite critical_region_outside_without_running_rep.
  rewrite <- UCOS2_raw_rep_split_running.
  rewrite (UCOS2_raw_rep_split_module _ _ InterruptModule).
  cbn [UCOS2_module_rep].
  unfold interrupt_inv, store_int_state, tmr_create_observation_rest, tmr_create_nesting.
  rewrite Hnest; entailer!.
Qed.

Lemma proof_of_OSTmrCreate_which_implies_wit_3 : OSTmrCreate_which_implies_wit_3.
Proof.
  right; intros before args env Hentry.
  destruct Hentry as [_ [[_ [Haddresses _]] [Hvalid _]]].
  unfold os_sched_unlock_global_addresses in Haddresses.
  destruct Haddresses as [Hrun [Hnest [Hlock Hrest]]].
  unfold tmr_create_observation_rest, tmr_create_nesting.
  rewrite Hnest.
  prop_apply_p (store_uchar_range (g_OSIntNesting (tmr_create_globals env))
    (intNesting (IntrState before))).
  prop_apply_p (store_uchar_range (g_OSLockNesting (tmr_create_globals env))
    (lockNesting (IntrState before))).
  rewrite os_sched_lock_pre_closed_equiv.
  unfold critical_region_outside.
  rewrite critical_region_outside_without_running_rep.
  rewrite <- UCOS2_raw_rep_split_running.
  rewrite (UCOS2_raw_rep_split_module _ _ InterruptModule).
  cbn [UCOS2_module_rep].
  unfold interrupt_inv, store_int_state, interrupt_in_range.
  entailer!; try (unfold os_sched_lock_global_addresses; auto); lia.
Qed.

Lemma proof_of_OSTmrCreate_which_implies_wit_4 : OSTmrCreate_which_implies_wit_4.
Proof.
  left; intros before args env Hentry Herror.
  rewrite os_sched_lock_post_closed_equiv; Intros acquired locked.
  destruct H as [Hrelation Hvalid].
  assert (Hbinding : tmr_alloc_source_binding env.(tmr_create_globals))
    by (unfold tmr_create_entry_facts, tmr_create_c_bindings in Hentry; tauto).
  assert (Hinitial : timer_api_initialized before.(TimerState))
    by (unfold tmr_create_entry_facts in Hentry; tauto).
  assert (Hinitialized : timer_api_initialized locked.(TimerState)).
  { eapply timer_execution.timer_public_storage_frame_initialized; [|exact Hinitial].
    apply timer_execution.timer_public_trace_public_storage_frame with (sg := env.(tmr_create_globals)).
    eapply os_sched_lock_call_timer_public_trace; exact Hrelation. }
  assert (Htimers : valid_timer_configuration env.(tmr_create_globals) locked.(TimerState))
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto).
  assert (Hlocked : tmr_create_locked_facts env args before locked).
  { unfold tmr_create_locked_facts; split; [exact Hentry|].
    split; [exact Herror|]. split; [exists acquired; exact Hrelation|auto]. }
  destruct (tmr_create_alloc_consequence_exists _ _ Hbinding Htimers Hinitialized)
    as [head [next [prev [used [free [frame Hconsequence]]]]]].
  pose proof (proj1 (proj2 (proj2 (proj2 Hconsequence)))) as Hpre.
  Exists head next prev used free frame locked.
  unfold critical_region_outside.
  rewrite critical_region_outside_without_running_rep.
  rewrite <- UCOS2_raw_rep_split_running.
  rewrite (UCOS2_raw_rep_split_module _ _ TimerModule).
  cbn [UCOS2_module_rep].
  assert (Hinv : timer_configured_rep env.(tmr_create_globals) locked.(TimerState) |--
    timer_inv env.(tmr_create_globals) locked.(TimerState)) by (unfold timer_inv; entailer!).
  sep_apply_l_atomic Hinv.
  sep_apply_l_atomic Hpre.
  unfold tmr_create_kernel_frame, tmr_create_timers; entailer!.
Qed.

Lemma proof_of_OSTmrCreate_which_implies_wit_5 : OSTmrCreate_which_implies_wit_5.
Proof.
  left; intros env locked head next prev used free alloc_frame ptmr Hconsequence.
  exact (proj2 (proj2 (proj2 (proj2 Hconsequence))) ptmr).
Qed.

Lemma proof_of_OSTmrCreate_which_implies_wit_6 : OSTmrCreate_which_implies_wit_6.
Proof.
  left; intros before args env locked ptmr Hlocked Hnull.
  destruct Hlocked as [Hentry [Herror [[acquired Hrelation] [Hvalid Hinitialized]]]].
  assert (Hbinding : tmr_alloc_source_binding env.(tmr_create_globals))
    by (unfold tmr_create_entry_facts, tmr_create_c_bindings in Hentry; tauto).
  assert (Haddresses : os_sched_unlock_global_addresses env.(tmr_create_globals)
    &("OSRunning") &("OSIntNesting") &("OSLockNesting") &("OSPrioHighRdy")
    &("OSPrioCur") &("OSTCBHighRdy") &("OSTCBPrioTbl") &("OSCtxSwCtr")
    &("OSUnMapTbl") &("OSRdyGrp") &("OSRdyTbl"))
    by (unfold tmr_create_entry_facts, tmr_create_c_bindings in Hentry; tauto).
  unfold tmr_alloc_configured_result, tmr_create_timers; Split; Intros.
  - destruct H as [Hempty Hret].
    assert (Hprefix : tmr_create_prefix env args before TmrCreateExhausted locked).
    { unfold tmr_create_prefix; rewrite Herror; exists acquired, locked; auto. }
    assert (Hsafety : os_sched_unlock_acquire_safety env.(tmr_create_external)
      env.(tmr_create_critical) env.(tmr_create_globals) env.(tmr_create_caller) locked).
    { unfold tmr_create_entry_facts, tmr_create_scheduler_safety in Hentry.
      apply (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hentry))))))
        with (result := TmrCreateExhausted); [exact Hprefix|reflexivity]. }
    rewrite os_sched_unlock_pre_closed_equiv.
    unfold os_sched_unlock_outside_frame, critical_region_outside.
    rewrite critical_region_outside_without_running_rep.
    rewrite <- UCOS2_raw_rep_split_running.
    rewrite (UCOS2_raw_rep_split_module _ _ TimerModule).
    cbn [UCOS2_module_rep].
    unfold tmr_create_kernel_frame, timer_inv; Intros; entailer!.
  - Intros i private allocated; destruct H as [Hallocate [Hpointer Hpostinit]].
    destruct Hbinding as [Hconfig [_ [_ [_ [_ [Hregion _]]]]]].
    assert (Henabled : cfgTimerEnabled (osKernelConfig (tmr_create_globals env)) = true)
      by (rewrite Hconfig; reflexivity).
    assert (Htimers : valid_timer_configuration env.(tmr_create_globals) locked.(TimerState))
      by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto).
    pose proof (proj1 (timer_initialized_configuration_iff _ _ Henabled Hinitialized) Htimers) as Htimer.
    assert (Hrange : 0 <= i < cfgMaxTimers (osKernelConfig (tmr_create_globals env))).
    { pose proof Hallocate as Ha; unfold timer_allocate in Ha.
      destruct (timerFree (TimerState locked)) as [|j rest] eqn:Hfree; [discriminate|].
      destruct (timerImages (TimerState locked) j); [|discriminate].
      inversion Ha; subst j.
      exact (proj1 (tmr_alloc_nonempty_facts _ _ _ _ Htimer Hfree)). }
    pose proof (timer_pool_addr_in_range _ _ Hregion Hrange) as Hpositive.
    unfold tmr_create_pointer_null in Hnull; exfalso; lia.
Qed.

Lemma proof_of_OSTmrCreate_which_implies_wit_7 : OSTmrCreate_which_implies_wit_7.
Proof.
  left; intros before args env locked ptmr Hlocked Hnonnull.
  pose proof Hlocked as [Hentry [Herror [[acquired Hrelation] [Hvalid Hinitialized]]]].
  assert (Hconfig : osKernelConfig (tmr_create_globals env) = selected_kernel_configuration)
    by (unfold tmr_create_entry_facts, tmr_create_c_bindings, tmr_alloc_source_binding in Hentry; tauto).
  assert (Henabled : cfgTimerEnabled (osKernelConfig (tmr_create_globals env)) = true)
    by (rewrite Hconfig; reflexivity).
  assert (Htimers : valid_timer_configuration env.(tmr_create_globals) locked.(TimerState))
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto).
  pose proof (proj1 (timer_initialized_configuration_iff _ _ Henabled Hinitialized) Htimers) as Htimer.
  unfold tmr_alloc_configured_result, tmr_create_timers; Split; Intros.
  - destruct H; contradiction.
  - Intros i private allocated; destruct H as [Hallocate [Hpointer Hpostinit]].
    assert (Hrange : 0 <= i < cfgMaxTimers (osKernelConfig (tmr_create_globals env))).
    { pose proof Hallocate as Ha; unfold timer_allocate in Ha.
      destruct (timerFree (TimerState locked)) as [|j rest] eqn:Hfree; [discriminate|].
      destruct (timerImages (TimerState locked) j); [|discriminate].
      inversion Ha; subst j.
      exact (proj1 (tmr_alloc_nonempty_facts _ _ _ _ Htimer Hfree)). }
    pose proof (tmr_create_allocated_image_facts _ _ _ _ _ Htimer Hallocate) as Himage.
    assert (Hadmission : tmr_create_name_admission env args before)
      by (unfold tmr_create_entry_facts in Hentry; tauto).
    specialize (Hadmission acquired locked i private allocated Herror Hrelation Hallocate).
    sep_apply_l_atomic (tmr_create_private_match_in_range env.(tmr_create_globals) i private).
    Intros.
    Exists i private allocated; entailer!.
    unfold tmr_create_allocated_facts; tauto.
Qed.

Lemma proof_of_OSTmrCreate_which_implies_wit_8 : OSTmrCreate_which_implies_wit_8.
Proof.
  right; intros before args env locked i private allocated ptmr Hfacts.
  destruct Hfacts as [Hlocked [_ [Hpointer [_ [Hrange _]]]]].
  destruct Hlocked as [Hentry _].
  destruct Hentry as [_ [[[Hconfig Halloc] [Haddresses Hfields]] _]].
  subst ptmr; specialize (Hfields i Hrange).
  destruct Hfields as [Hs [Hd [Hp [Ho [Hcb [Harg Hname]]]]]].
  rewrite Hs, Hd, Hp, Ho, Hcb, Harg, Hname.
  exact (tmr_create_split_private_fields _ _ _ Hconfig).
Qed.

Lemma proof_of_OSTmrCreate_which_implies_wit_9 : OSTmrCreate_which_implies_wit_9.
Proof.
  left; intros LitMap before args env locked i private allocated ptmr Hfacts Hnull Hname.
  assert (Hliteral : tmr_create_literal_condition env args locked.(NameState))
    by (unfold tmr_create_allocated_facts in Hfacts; tauto).
  sep_apply_l_atomic (tmr_create_literal_resources_split env args locked LitMap Hnull Hname Hliteral).
  Intros rest; Exists rest; entailer!.
Qed.

Lemma proof_of_OSTmrCreate_which_implies_wit_10 : OSTmrCreate_which_implies_wit_10.
Proof.
  left; intros LitMap env locked literal_rest Hrejoin; exact Hrejoin.
Qed.

Lemma proof_of_OSTmrCreate_which_implies_wit_11 : OSTmrCreate_which_implies_wit_11.
Proof.
  left; intros before args env locked i private allocated ptmr Hfacts.
  pose proof Hfacts as (Hlocked & Hallocate & Hpointer & Hnonnull & Hrange &
    Hmatch & Htype & Hnext & Hprev & Hgeneration & Hpadding & Hname & Hliteral).
  destruct Hlocked as [Hentry [Herror [[acquired Hrelation] [Hvalid Hinitialized]]]].
  assert (Hbinding : tmr_alloc_source_binding env.(tmr_create_globals))
    by (unfold tmr_create_entry_facts, tmr_create_c_bindings in Hentry; tauto).
  pose proof Hbinding as [Hconfig Hotherbinding].
  assert (Henabled : cfgTimerEnabled (osKernelConfig (tmr_create_globals env)) = true)
    by (rewrite Hconfig; reflexivity).
  assert (Hcapacity : cfgMaxTimers (osKernelConfig (tmr_create_globals env)) < 65536)
    by (rewrite Hconfig; cbn; lia).
  assert (Haddresses : os_sched_unlock_global_addresses env.(tmr_create_globals)
    &("OSRunning") &("OSIntNesting") &("OSLockNesting") &("OSPrioHighRdy")
    &("OSPrioCur") &("OSTCBHighRdy") &("OSTCBPrioTbl") &("OSCtxSwCtr")
    &("OSUnMapTbl") &("OSRdyGrp") &("OSRdyTbl"))
    by (unfold tmr_create_entry_facts, tmr_create_c_bindings in Hentry; tauto).
  assert (Hfields : forall j, 0 <= j < cfgMaxTimers (osKernelConfig (tmr_create_globals env)) ->
    let p := timer_pool_addr env.(tmr_create_globals) j in
    &((p) # "os_tmr" ->ₛ "OSTmrState") = p + 37 /\
    &((p) # "os_tmr" ->ₛ "OSTmrDly") = p + 24 /\
    &((p) # "os_tmr" ->ₛ "OSTmrPeriod") = p + 28 /\
    &((p) # "os_tmr" ->ₛ "OSTmrOpt") = p + 36 /\
    &((p) # "os_tmr" ->ₛ "OSTmrCallback") = p + 4 /\
    &((p) # "os_tmr" ->ₛ "OSTmrCallbackArg") = p + 8 /\
    &((p) # "os_tmr" ->ₛ "OSTmrName") = p + 32)
    by (unfold tmr_create_entry_facts, tmr_create_c_bindings in Hentry; tauto).
  assert (Harguments : tmr_create_arguments_in_range args)
    by (unfold tmr_create_entry_facts in Hentry; tauto).
  destruct Harguments as [Hdelay [Hperiod Hoptionrange]].
  assert (Hargument_error : tmr_create_argument_error args.(tmr_create_delay)
    args.(tmr_create_period) args.(tmr_create_option) = None).
  { unfold tmr_create_first_error, tmr_create_early_error in Herror.
    destruct (tmr_create_argument_error (tmr_create_delay args)
      (tmr_create_period args) (tmr_create_option args)); [discriminate|reflexivity]. }
  assert (Hmode : args.(tmr_create_option) = encode_timer_mode (tmr_create_mode args)).
  { pose proof (proj1 (tmr_create_argument_error_none_iff _ _ _) Hargument_error) as Hcases.
    unfold tmr_create_mode; destruct (tmr_create_option args =? 2) eqn:Htwo;
      cbn; [apply Z.eqb_eq in Htwo|apply Z.eqb_neq in Htwo]; tauto. }
  assert (Hallocated_valid : UCOS2_state_inv env.(tmr_create_globals) (replace_TimerS allocated locked)).
  { eapply tmr_create_allocate_global_validity; eassumption. }
  assert (Hallocated_init : timer_api_initialized allocated).
  { unfold timer_api_initialized; rewrite (timer_allocate_preserves_initialization_phase _ _ _ _ Hallocate).
    exact Hinitialized. }
  set (completion := tmr_create_completion env args locked i private allocated).
  assert (Hprefix : tmr_create_prefix env args before (TmrCreateStored i private) completion).
  { unfold tmr_create_prefix; rewrite Herror; exists acquired, locked.
    split; [exact Hrelation|exists allocated; auto]. }
  assert (Hsafety : os_sched_unlock_acquire_safety env.(tmr_create_external)
    env.(tmr_create_critical) env.(tmr_create_globals) env.(tmr_create_caller) completion).
  { unfold tmr_create_entry_facts, tmr_create_scheduler_safety in Hentry.
    apply (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hentry))))))
      with (result := TmrCreateStored i private); [exact Hprefix|reflexivity]. }
  Exists completion.
  subst ptmr; specialize (Hfields i Hrange).
  destruct Hfields as [Hs [Hd [Hp [Ho [Hcb [Harg Hnm]]]]]].
  rewrite Hs, Hd, Hp, Ho, Hcb, Harg, Hnm.
  pose proof (tmr_create_merge_initialized_fields
    (timer_pool_addr env.(tmr_create_globals) i) private.(timerPrivateImage)
    args.(tmr_create_delay) args.(tmr_create_period) args.(tmr_create_option)
    args.(tmr_create_callback) args.(tmr_create_callback_arg) (tmr_create_chosen_name args)) as Hmerge.
  unfold tmr_create_fields in Hmerge.
  sep_apply_l_atomic Hmerge.
  unfold tmr_create_kernel_frame, timer_inv; Intros.
  pose proof (UCOS2_inv_merge_updated_timer env.(tmr_create_globals) locked
    (replace_TimerS allocated locked) Hallocated_valid eq_refl) as Hallocated_merge.
  cbn [replace_TimerS TimerState] in Hallocated_merge.
  sep_apply_l_atomic Hallocated_merge.
  destruct (tmr_create_is_public (tmr_create_name_plan env)) eqn:Hpublic.
  - assert (Hnamed_valid : UCOS2_state_inv env.(tmr_create_globals)
      (replace_NameS (tmr_create_name_state env.(tmr_create_name_plan) locked.(NameState)) locked)).
    { eapply tmr_create_name_plan_preserves_validity; eassumption. }
    destruct (tmr_create_name_plan_readable _ _ _ Hpublic Hname) as [chars Hreadable].
    assert (Hcompleted_valid : UCOS2_state_inv env.(tmr_create_globals) completion).
    { unfold completion, tmr_create_completion; rewrite Hpublic.
      eapply tmr_create_publish_preserves_global_validity with (chars := chars);
        cbn [replace_NameS TimerState NameState]; try eassumption.
      rewrite <- Hmode; exact Hargument_error. }
    sep_apply_l_atomic (tmr_create_name_storage_to_global env.(tmr_create_globals)
      (replace_TimerS allocated locked) env.(tmr_create_name_plan)
      (tmr_create_chosen_name args) Hname).
    rewrite UCOS2_inv_split_timer; Intros.
    cbn [replace_NameS replace_TimerS TimerState NameState].
    rewrite (timer_initialized_configured_rep_eq _ _ Henabled Hallocated_init).
    assert (Himage : tmr_create_image private.(timerPrivateImage)
      args.(tmr_create_delay) args.(tmr_create_period) args.(tmr_create_option)
      args.(tmr_create_callback) args.(tmr_create_callback_arg) (tmr_create_chosen_name args) =
      timer_object_image (timer_create_object private args.(tmr_create_delay)
        args.(tmr_create_period) (tmr_create_mode args) args.(tmr_create_callback)
        args.(tmr_create_callback_arg) (tmr_create_chosen_name args))
        0 0 private.(timerPrivateImage).(timerImagePadding)).
    { rewrite Hmode; apply tmr_create_image_object_eq; auto. }
    rewrite Himage, <- Hconfig.
    pose proof (proj1 (timer_allocate_excludes_global_image _ _ _ _ Hallocate)) as Hmissing.
    sep_apply_l_atomic (tmr_create_publish_rep env.(tmr_create_globals) allocated i private
      args.(tmr_create_delay) args.(tmr_create_period) (tmr_create_mode args)
      args.(tmr_create_callback) args.(tmr_create_callback_arg) (tmr_create_chosen_name args) Hmissing).
    rewrite os_sched_unlock_pre_closed_equiv.
    unfold os_sched_unlock_outside_frame, critical_region_outside.
    rewrite critical_region_outside_without_running_rep.
    rewrite <- UCOS2_raw_rep_split_running.
    rewrite (UCOS2_raw_rep_split_module _ completion TimerModule).
    cbn [UCOS2_module_rep].
    unfold tmr_create_result_storage; rewrite Hpublic.
    unfold completion, tmr_create_completion; rewrite Hpublic.
    cbn [TimerState replace_TimerS replace_NameS NameState].
    rewrite (timer_initialized_configured_rep_eq env.(tmr_create_globals)
      (timer_publish allocated i private args.(tmr_create_delay) args.(tmr_create_period)
        (tmr_create_mode args) args.(tmr_create_callback) args.(tmr_create_callback_arg)
        (tmr_create_chosen_name args)) Henabled Hallocated_init).
    unfold completion, tmr_create_completion in Hcompleted_valid, Hsafety, Hprefix.
    rewrite Hpublic in Hcompleted_valid, Hsafety, Hprefix.
    entailer!.
  - assert (Hraw : env.(tmr_create_name_plan) = TmrCreateRawName).
    { destruct (tmr_create_name_plan env); cbn in Hpublic; congruence. }
    assert (Hcompleted_valid : UCOS2_state_inv env.(tmr_create_globals) completion).
    { unfold completion, tmr_create_completion; rewrite Hpublic; exact Hallocated_valid. }
    rewrite os_sched_unlock_pre_closed_equiv.
    unfold os_sched_unlock_outside_frame, critical_region_outside.
    rewrite critical_region_outside_without_running_rep.
    rewrite <- UCOS2_raw_rep_split_running.
    unfold tmr_create_result_storage; rewrite Hpublic.
    unfold completion, tmr_create_completion; rewrite Hpublic.
    unfold UCOS2_inv, tmr_create_name_storage; rewrite Hraw; Intros.
    unfold completion, tmr_create_completion in Hcompleted_valid, Hsafety, Hprefix.
    rewrite Hpublic in Hcompleted_valid, Hsafety, Hprefix.
    rewrite Hconfig; entailer!.
Qed.

