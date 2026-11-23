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
From Ucos2Verify.VC.code.timer Require Import tmr_state_get_goal.
From Ucos2Verify.VC.code.timer Require Import tmr_state_get_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_state_get_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTmrStateGet_entail_wit_1_1 : OSTmrStateGet_entail_wit_1_1.
Proof.
  left; intros; subst ptmr_pre perr_pre observed.
  Exists 0; unfold tmr_state_get_state_error; entailer!.
Qed.

Lemma proof_of_OSTmrStateGet_entail_wit_1_2 : OSTmrStateGet_entail_wit_1_2.
Proof.
  left; intros; subst ptmr_pre perr_pre observed.
  Exists 0; unfold tmr_state_get_state_error; entailer!.
Qed.

Lemma proof_of_OSTmrStateGet_entail_wit_1_3 : OSTmrStateGet_entail_wit_1_3.
Proof.
  left; intros; subst ptmr_pre perr_pre observed.
  Exists 0; unfold tmr_state_get_state_error; entailer!.
Qed.

Lemma proof_of_OSTmrStateGet_entail_wit_1_4 : OSTmrStateGet_entail_wit_1_4.
Proof.
  left; intros; subst ptmr_pre perr_pre observed.
  Exists 0; unfold tmr_state_get_state_error; entailer!.
Qed.

Lemma proof_of_OSTmrStateGet_entail_wit_1_5 : OSTmrStateGet_entail_wit_1_5.
Proof.
  left; intros; subst ptmr_pre perr_pre.
  assert (Hhigh : Z.leb observed 3 = false) by (apply Z.leb_gt; lia).
  Exists 141; unfold tmr_state_get_state_error.
  rewrite Hhigh, Bool.andb_false_r; entailer!.
Qed.

Lemma proof_of_OSTmrStateGet_return_wit_1 : OSTmrStateGet_return_wit_1.
Proof.
  left; intros.
  destruct PreH5 as [Hvalid [Hinput [Hprotocol Hsafe]]].
  assert (Hp : Z.eqb p 0 = false) by (apply Z.eqb_neq; exact PreH1).
  assert (Hunlock : os_sched_unlock_acquire_safety external critical sg context locked).
  { eapply Hprotocol; eauto. }
  sep_apply (tmr_state_get_unlock_post external platform critical sg context mask locked).
  Intros final returned.
  pose proof (tmr_state_get_unlock_return_preserves_validity external critical sg context
    locked returned final PreH17 Hunlock H) as Hfinal.
  assert (Hprogram : tmr_state_get_program external critical sg context p raw i ty raw_state
    before ((observed,error),returned) final).
  { unfold tmr_state_get_program; rewrite Hp, PreH2, PreH3; simpl.
    exists entry, locked, observed, returned.
    split; [exact PreH6|].
    split; [exact PreH7|].
    split; [exact H|now rewrite PreH14]. }
  pose proof (tmr_state_get_program_safe_return external critical sg context p raw i ty
    raw_state before observed error returned final X Hsafe Hprogram) as Hreturn.
  unfold tmr_state_get_post; Exists final returned error.
  unfold tmr_state_get_resources, tmr_state_get_public_resources, tmr_state_get_calls.
  rewrite Hp, PreH2, PreH3; simpl.
  rewrite (tmr_state_get_closed_rep critical sg (os_sched_call_invocation context) final).
  entailer!.
  rewrite <- PreH2; exact Hprogram.
Qed.

Lemma proof_of_OSTmrStateGet_return_wit_2 : OSTmrStateGet_return_wit_2.
Proof.
  left; intros; subst ptmr_pre perr_pre.
  destruct PreH9 as [Hvalid [Hinput [Hprotocol Hsafe]]].
  assert (Hp : Z.eqb p 0 = false) by (apply Z.eqb_neq; exact PreH3).
  assert (Hnesting : Z.ltb 0 (os_sched_ints before) = true) by (apply Z.ltb_lt; lia).
  assert (Hprogram : tmr_state_get_program external critical sg context p raw i ty raw_state
    before ((0,139),context) before).
  { unfold tmr_state_get_program; rewrite Hp, PreH2, Hnesting; simpl; auto. }
  pose proof (tmr_state_get_program_safe_return external critical sg context p raw i ty
    raw_state before 0 139 context before X Hsafe Hprogram) as Hreturn.
  sep_apply (tmr_state_get_observation_merge__branch_returns external platform sg context
    mask before p raw i ty raw_state _ _ _ PreH8 Hinput PreH3).
  unfold tmr_state_get_post; Exists before context 139; entailer!.
Qed.

Lemma proof_of_OSTmrStateGet_return_wit_3 : OSTmrStateGet_return_wit_3.
Proof.
  left; intros; subst ptmr_pre perr_pre.
  destruct PreH8 as [Hvalid [Hinput [Hprotocol Hsafe]]].
  assert (Hp : Z.eqb p 0 = false) by (apply Z.eqb_neq; exact PreH2).
  assert (Htype : Z.eqb ty 100 = false) by (apply Z.eqb_neq; exact PreH1).
  assert (Hprogram : tmr_state_get_program external critical sg context p raw i ty raw_state
    before ((0,137),context) before).
  { unfold tmr_state_get_program; rewrite Hp, Htype; simpl; auto. }
  pose proof (tmr_state_get_program_safe_return external critical sg context p raw i ty
    raw_state before 0 137 context before X Hsafe Hprogram) as Hreturn.
  sep_apply (tmr_state_get_observation_merge__branch_returns external platform sg context
    mask before p raw i ty raw_state _ _ _ PreH7 Hinput PreH2).
  unfold tmr_state_get_post; Exists before context 137; entailer!.
Qed.

Lemma proof_of_OSTmrStateGet_return_wit_4 : OSTmrStateGet_return_wit_4.
Proof.
  left; intros; subst ptmr_pre p perr_pre.
  unfold tmr_state_get_pre; Intros.
  destruct H as [Hvalid [Hinput [Hprotocol Hsafe]]].
  assert (Hprogram : tmr_state_get_program external critical sg context 0 raw i ty raw_state
    before ((0,138),context) before).
  { unfold tmr_state_get_program; simpl; auto. }
  pose proof (tmr_state_get_program_safe_return external critical sg context 0 raw i ty
    raw_state before 0 138 context before X Hsafe Hprogram) as Hreturn.
  unfold tmr_state_get_post; Exists before context 138; entailer!.
Qed.

Lemma proof_of_OSTmrStateGet_partial_solve_wit_3_pure : OSTmrStateGet_partial_solve_wit_3_pure.
Proof.
  left; intros.
  unfold os_sched_unlock_global_addresses, os_sched_global_addresses in PreH19.
  unfold os_sched_lock_global_addresses; entailer!; tauto.
Qed.

Lemma proof_of_OSTmrStateGet_which_implies_wit_1 : OSTmrStateGet_which_implies_wit_1.
Proof.
  left; intros X raw_state ty i raw before mask context sg critical platform external ptmr Hnonzero Hlayout.
  pose proof Hlayout as [Henabled [Hoffset [Htype [Hstate Hints]]]].
  assert (Hnonnull : (ptmr =? 0) = false) by (apply Z.eqb_neq; assumption).
  unfold tmr_state_get_pre; Intros.
  pose proof H as [Hvalid [Hinput Hrest]].
  unfold tmr_state_get_public_resources, tmr_state_get_raw_storage,
    tmr_state_get_observation_frame, tmr_state_get_entry_context_frame,
    tmr_state_get_context_frame, UCOS2_raw_rep_missing_interrupt.
  rewrite Hnonnull, Htype, Hints.
  rewrite Htype, Hints in Hlayout.
  destruct raw.
  - rewrite (UCOS2_raw_rep_split_module sg before InterruptModule).
    cbn [UCOS2_module_rep].
    unfold interrupt_inv, store_int_state, interrupt_inv_no_int_nesting, os_sched_ints.
    Intros.
    prop_apply_p (store_uchar_range ptmr ty); Intros.
    prop_apply_p (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState before))); Intros.
    entailer!.
  - unfold tmr_state_get_input in Hinput.
    destruct Hinput as [Hzero|[_ [_ [_ [Hinit [Hp [image [Himage Hty]]]]]]]]; [contradiction|].
    rewrite (UCOS2_raw_rep_split_two sg before TimerModule InterruptModule ltac:(discriminate)).
    cbn [UCOS2_module_rep].
    sep_apply (timer_configured_rep_split_type sg (TimerState before) i image Henabled Hinit Himage).
    rewrite Hty, <- Hp.
    unfold interrupt_inv, store_int_state, interrupt_inv_no_int_nesting, os_sched_ints.
    Intros.
    prop_apply_p (store_uchar_range ptmr ty); Intros.
    prop_apply_p (store_uchar_range (g_OSIntNesting sg) (intNesting (IntrState before))); Intros.
    Exists image; entailer!.
Qed.

Lemma proof_of_OSTmrStateGet_which_implies_wit_2 : OSTmrStateGet_which_implies_wit_2.
Proof.
  left; intros X raw_state ty i raw before mask context sg critical platform external ptmr
    Hnonzero Hty Hzero Hlayout Hfacts.
  pose proof Hlayout as [Henabled [Hoffset [Htype [Hstate Hints]]]].
  pose proof Hfacts as [Hvalid [Hinput Hrest]].
  assert (Hnonnull : (ptmr =? 0) = false) by (apply Z.eqb_neq; assumption).
  rewrite os_sched_lock_pre_closed_equiv, tmr_state_get_closed_rep.
  unfold tmr_state_get_observation_frame, tmr_state_get_entry_context_frame,
    tmr_state_get_context_frame, tmr_state_get_calls, tmr_state_get_raw_storage.
  rewrite Hnonnull, Hty, Hzero, !Z.eqb_refl; cbn [negb andb].
  rewrite Htype, Hints.
  rewrite Htype, Hints in Hlayout.
  rewrite Hty in Hfacts.
  destruct raw.
  - rewrite (UCOS2_raw_rep_split_module sg before InterruptModule).
    cbn [UCOS2_module_rep].
    unfold interrupt_inv, store_int_state, interrupt_inv_no_int_nesting, os_sched_ints,
      UCOS2_raw_rep_missing_interrupt.
    unfold os_sched_ints in Hzero; rewrite Hzero.
    entailer!.
  - unfold tmr_state_get_input in Hinput.
    destruct Hinput as [Hz|[_ [_ [_ [Hinit [Hp Hexists]]]]]]; [contradiction|].
    Intros image.
    destruct H as [Himage Himage_type].
    pose proof (timer_configured_rep_merge_type sg (TimerState before) i image
      Henabled Hinit Himage) as Hmerge.
    rewrite Himage_type, <- Hp in Hmerge.
    sep_apply Hmerge.
    rewrite (UCOS2_raw_rep_split_two sg before TimerModule InterruptModule ltac:(discriminate)).
    cbn [UCOS2_module_rep].
    unfold interrupt_inv, store_int_state, interrupt_inv_no_int_nesting, os_sched_ints.
    unfold os_sched_ints in Hzero; rewrite Hzero.
    entailer!.
Qed.

Lemma proof_of_OSTmrStateGet_which_implies_wit_3 : OSTmrStateGet_which_implies_wit_3.
Proof.
  left; intros X raw_state ty i raw before mask context sg critical platform external ptmr
    Hnonzero Hty Hzero Hlayout Hfacts.
  pose proof Hlayout as [Henabled [Hoffset [Htype [Hstate Hints]]]].
  pose proof Hfacts as [Hvalid_before [Hinput Hrest]].
  assert (Hnonnull : (ptmr =? 0) = false) by (apply Z.eqb_neq; assumption).
  rewrite os_sched_lock_post_closed_equiv.
  Intros entry locked.
  destruct H as [Hcall Hvalid].
  unfold tmr_state_get_raw_storage.
  rewrite Hnonnull, Hty, Hzero, !Z.eqb_refl; cbn [andb].
  rewrite Hty in Hfacts.
  rewrite Hstate in Hlayout.
  destruct raw.
  - Exists entry locked raw_state.
    unfold tmr_state_get_state_frame, tmr_state_get_resources, tmr_state_get_observation.
    rewrite Hstate.
    prop_apply_p (store_uchar_range (ptmr + 37) raw_state); Intros.
    entailer!.
  - unfold tmr_state_get_input in Hinput.
    destruct Hinput as [Hz|[_ [_ [_ [Hinit [Hp [old [Hold Hold_type]]]]]]]]; [contradiction|].
    pose proof (tmr_state_get_lock_has_current_image critical sg context before entry locked
      i old Hcall Hinit Hold) as [Hinitialized [current Hcurrent]].
    rewrite tmr_state_get_closed_rep.
    rewrite (UCOS2_raw_rep_split_module sg locked TimerModule).
    cbn [UCOS2_module_rep].
    rewrite (timer_initialized_configured_rep_eq sg (TimerState locked) Henabled Hinitialized).
    sep_apply (timer_raw_rep_split_type_state sg (TimerState locked) i current Hcurrent).
    assert (Haddr : timer_pool_addr sg i + timer_option_offset (osKernelConfig sg) + 1 = ptmr + 37)
      by (rewrite <- Hp, Hoffset; lia).
    rewrite Haddr.
    prop_apply_p (store_uchar_range (ptmr + 37) (timerImageState current)); Intros.
    assert (Hobservation : tmr_state_get_observation false i raw_state locked (timerImageState current))
      by (exists current; auto).
    Exists entry locked (timerImageState current).
    unfold tmr_state_get_state_frame, tmr_state_get_context_frame.
    rewrite Hstate.
    Exists current; entailer!.
Qed.

Lemma proof_of_OSTmrStateGet_which_implies_wit_4 : OSTmrStateGet_which_implies_wit_4.
Proof.
  left; intros X raw_state ty i raw before mask context sg critical platform external entry locked
    observed ptmr Hnonzero Hty Hzero Hlayout Hfacts Hcall Hvalid Hobservation.
  pose proof Hlayout as [Henabled [Hoffset [Htype [Hstate Hints]]]].
  pose proof Hfacts as [Hvalid_before [Hinput [Hprotocol Hsafe]]].
  pose proof (Hprotocol Hnonzero Hty Hzero entry locked Hcall) as Hcall_safe.
  assert (Hnonnull : (ptmr =? 0) = false) by (apply Z.eqb_neq; assumption).
  rewrite os_sched_unlock_pre_closed_equiv.
  unfold os_sched_unlock_outside_frame, tmr_state_get_raw_storage, tmr_state_get_state_frame.
  rewrite Hnonnull, Hty, Hzero, !Z.eqb_refl; cbn [andb].
  rewrite Hstate.
  rewrite Hty in Hfacts.
  rewrite Hstate in Hlayout.
  destruct raw.
  - unfold tmr_state_get_observation in Hobservation; subst observed.
    unfold tmr_state_get_resources; entailer!.
  - unfold tmr_state_get_input in Hinput.
    destruct Hinput as [Hz|[_ [_ [_ [Hinit [Hp [old [Hold Hold_type]]]]]]]]; [contradiction|].
    pose proof (tmr_state_get_lock_has_current_image critical sg context before entry locked
      i old Hcall Hinit Hold) as [Hinitialized Hexists].
    Intros image.
    destruct H as [Himage Himage_state].
    pose proof (timer_raw_rep_merge_type_state sg (TimerState locked) i image Himage) as Hmerge.
    assert (Haddr : timer_pool_addr sg i + timer_option_offset (osKernelConfig sg) + 1 = ptmr + 37)
      by (rewrite <- Hp, Hoffset; lia).
    rewrite Haddr, Himage_state in Hmerge.
    sep_apply Hmerge.
    rewrite tmr_state_get_closed_rep.
    rewrite (UCOS2_raw_rep_split_module sg locked TimerModule).
    cbn [UCOS2_module_rep].
    rewrite (timer_initialized_configured_rep_eq sg (TimerState locked) Henabled Hinitialized).
    unfold tmr_state_get_context_frame; entailer!.
Qed.

