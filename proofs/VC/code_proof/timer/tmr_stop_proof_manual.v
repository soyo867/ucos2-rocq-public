From SimpleC.Verification Require Import VCPrelude.
From Ucos2Verify.VC.code.timer Require Import tmr_stop_goal.
From Ucos2Verify.VC.code.timer Require Import tmr_stop_proof_auto.
From SimpleC.CoreLang Require Import CTypes.
Import SimpleCtypeNotations.
Require Import Ucos2Verify.VC.code.timer.spec.timer_callback_semantics.
Import TimerCallback_C_Rules.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_unlink_spec.
Require Import Ucos2Verify.VC.code.timer.spec.timer_callee_lift_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_stop_fields_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_stop_call_resources_spec.
Import TimerCallback_C_Rules TimerCallback_C_Rules.Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTmrStop_entail_wit_1 : OSTmrStop_entail_wit_1.
Proof.
  left; intros.
  subst AppRep_timer_stop_public_spec effects_timer_stop_public_spec
    raw_type_timer_stop_public_spec raw_state_timer_stop_public_spec.
  unfold tmr_stop_call_post.
  intros heap Hresources.
  eapply tmr_stop_null_return_post.
  - exact PreH14.
  - exact (proj2 PreH13).
  - eapply tmr_stop_call_callback_resources_forget. exact Hresources.
Qed.

Lemma proof_of_OSTmrStop_entail_wit_2 : OSTmrStop_entail_wit_2.
Proof.
  left; intros.
  subst AppRep_timer_stop_public_spec effects_timer_stop_public_spec
    raw_type_timer_stop_public_spec raw_state_timer_stop_public_spec.
  unfold tmr_stop_call_post.
  intros heap Hresources.
  eapply tmr_stop_type_return_post with
    (observed := before_timer_stop_public_spec) (ty := ty).
  - exact PreH14.
  - exact PreH15.
  - exact PreH16.
  - exact (proj2 PreH13).
  - eapply tmr_stop_call_callback_resources_forget. exact Hresources.
Qed.

Lemma proof_of_OSTmrStop_entail_wit_3 : OSTmrStop_entail_wit_3.
Proof.
  left; intros.
  subst AppRep_timer_stop_public_spec effects_timer_stop_public_spec
    raw_type_timer_stop_public_spec raw_state_timer_stop_public_spec.
  unfold tmr_stop_call_post.
  intros heap Hresources.
  subst ty.
  eapply tmr_stop_isr_return_post with (observed := before_timer_stop_public_spec).
  - exact PreH14.
  - exact PreH16.
  - exact PreH17.
  - exact (proj2 PreH13).
  - eapply tmr_stop_call_callback_resources_forget. exact Hresources.
Qed.

Lemma proof_of_OSTmrStop_entail_wit_4_1 : OSTmrStop_entail_wit_4_1.
Proof.
  unfold OSTmrStop_entail_wit_4_1; left; intros.
  subst AppRep_timer_stop_public_spec effects_timer_stop_public_spec
    raw_type_timer_stop_public_spec raw_state_timer_stop_public_spec.
  unfold tmr_stop_call_post.
  intros heap Hresources.
  apply tmr_stop_call_callback_resources_forget in Hresources.
  destruct PreH14 as [observed [source_locked
    [Hpointer [Htype [Hinterrupts [Hlock Hstate]]]]]].
  eapply tmr_stop_nonrunning_return_post with
    (observed := observed) (locked := source_locked) (state_read := locked)
    (status := status) (returned := returned) (error := 142);
    try eassumption.
  - unfold tmr_stop_call_stopped_status in PreH15; lia.
  - apply tmr_stop_nonrunning_output_stopped_completed; exact PreH15.
  - exact (proj2 PreH13).
Qed.

Lemma proof_of_OSTmrStop_entail_wit_4_2 : OSTmrStop_entail_wit_4_2.
Proof.
  unfold OSTmrStop_entail_wit_4_2; left; intros.
  subst AppRep_timer_stop_public_spec effects_timer_stop_public_spec
    raw_type_timer_stop_public_spec raw_state_timer_stop_public_spec.
  unfold tmr_stop_call_post.
  intros heap Hresources.
  apply tmr_stop_call_callback_resources_forget in Hresources.
  destruct PreH14 as [observed [source_locked
    [Hpointer [Htype [Hinterrupts [Hlock Hstate]]]]]].
  eapply tmr_stop_nonrunning_return_post with
    (observed := observed) (locked := source_locked) (state_read := locked)
    (status := status) (returned := returned) (error := 142);
    try eassumption.
  - unfold tmr_stop_call_stopped_status in PreH15; lia.
  - apply tmr_stop_nonrunning_output_stopped_completed; exact PreH15.
  - exact (proj2 PreH13).
Qed.

Lemma proof_of_OSTmrStop_entail_wit_5 : OSTmrStop_entail_wit_5.
Proof.
  unfold OSTmrStop_entail_wit_5; left; intros.
  subst AppRep_timer_stop_public_spec effects_timer_stop_public_spec
    raw_type_timer_stop_public_spec raw_state_timer_stop_public_spec.
  unfold tmr_stop_call_post.
  intros heap Hresources.
  apply tmr_stop_call_callback_resources_forget in Hresources.
  destruct PreH14 as [observed [source_locked
    [Hpointer [Htype [Hinterrupts [Hlock Hstate]]]]]].
  eapply tmr_stop_nonrunning_return_post with
    (observed := observed) (locked := source_locked) (state_read := locked)
    (status := status) (returned := returned) (error := 135);
    try eassumption.
  - lia.
  - rewrite PreH15; reflexivity.
  - exact (proj2 PreH13).
Qed.

Lemma proof_of_OSTmrStop_entail_wit_6 : OSTmrStop_entail_wit_6.
Proof.
  unfold OSTmrStop_entail_wit_6; left; intros.
  subst AppRep_timer_stop_public_spec effects_timer_stop_public_spec
    raw_type_timer_stop_public_spec raw_state_timer_stop_public_spec.
  unfold tmr_stop_call_post.
  intros heap Hresources.
  apply tmr_stop_call_callback_resources_forget in Hresources.
  destruct PreH14 as [observed [source_locked
    [Hpointer [Htype [Hinterrupts [Hlock Hstate]]]]]].
  eapply tmr_stop_nonrunning_return_post with
    (observed := observed) (locked := source_locked) (state_read := locked)
    (status := status) (returned := returned) (error := 141);
    try eassumption.
  - apply tmr_stop_nonrunning_output_invalid; assumption.
  - exact (proj2 PreH13).
Qed.

Lemma proof_of_OSTmrStop_partial_solve_wit_5_pure : OSTmrStop_partial_solve_wit_5_pure.
Proof.
  unfold OSTmrStop_partial_solve_wit_5_pure; left; intros.
  assert (Htype : ty <> 100).
  { intro Hequal; apply PreH1; rewrite Hequal; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_partial_solve_wit_8_pure : OSTmrStop_partial_solve_wit_8_pure.
Proof.
  unfold OSTmrStop_partial_solve_wit_8_pure; left; intros.
  assert (Hrange : forall address value,
    (address # UChar |-> value) |-- coq_prop (0 <= value <= Byte.max_unsigned)).
  { intros address value heap Hcell.
    destruct (proj1 Hcell) as [_ [Hlower Hupper]]. split; lia. }
  prop_apply_p (Hrange (&((p_timer_stop_public_spec) # "os_tmr" ->ₛ "OSTmrType")) ty).
  Intros.
  assert (Htype : ty = 100).
  { rewrite unsigned_last_nbits_eq in PreH1; [exact PreH1|].
    change (0 <= ty < 4294967296); change (0 <= ty <= 255) in H; lia. }
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_partial_solve_wit_15_pure : OSTmrStop_partial_solve_wit_15_pure.
Proof.
  unfold OSTmrStop_partial_solve_wit_15_pure; left; intros.
  destruct PreH4 as [Hrunning [Hinterrupts [Hlocks Hremaining]]].
  unfold os_sched_lock_global_addresses.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_partial_solve_wit_29_pure : OSTmrStop_partial_solve_wit_29_pure.
Proof.
  left. intros. entailer!.
Qed.

Lemma proof_of_OSTmrStop_partial_solve_wit_38_pure : OSTmrStop_partial_solve_wit_38_pure.
Proof.
  left. intros. entailer!.
Qed.

Lemma proof_of_OSTmrStop_partial_solve_wit_72_pure : OSTmrStop_partial_solve_wit_72_pure.
Proof.
  unfold OSTmrStop_partial_solve_wit_72_pure; left; intros.
  entailer!; unfold tmr_stop_call_stopped_status; lia.
Qed.

Lemma proof_of_OSTmrStop_partial_solve_wit_73_pure : OSTmrStop_partial_solve_wit_73_pure.
Proof.
  unfold OSTmrStop_partial_solve_wit_73_pure; left; intros.
  entailer!; unfold tmr_stop_call_stopped_status; lia.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_1 : OSTmrStop_which_implies_wit_1.
Proof.
  left.
  intros Client X before context pooled perr arg opt i p nesting mask domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep Happ Heffects Hraw_type Hraw_state Hdomain Hlayout Hunlink Hprofile Haddrs Hints Hwheel.
  subst AppRep effects raw_type raw_state domain.
  intros heap [Hfacts Hresources].
  pose proof (tmr_stop_call_callback_capabilities_split_resources
    (tmr_stop_call_application_rep ClientRep pooled p nesting) external platform critical sg
    (tmr_stop_call_effects callback) mask perr
    (tmr_stop_call_callback_domain critical sg (tmr_stop_call_effects callback)
      pooled p i opt arg tmr_stop_call_raw_type tmr_stop_call_raw_state context before)
    pooled p i opt arg tmr_stop_call_raw_type tmr_stop_call_raw_state context before
    (tmr_stop_entry_owned (tmr_stop_call_application_rep ClientRep pooled p nesting)
      external platform critical sg mask perr context before) heap Hresources) as Hsplit.
  destruct Hfacts as [Hbinding [Hrequirements Hsafe]].
  unfold tmr_stop_call_source_facts.
  repeat (first [assumption | reflexivity | apply conj]).
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_2 : OSTmrStop_which_implies_wit_2.
Proof.
  left; intros.
  unfold tmr_stop_entry_owned, tmr_stop_entry_client_rep, tmr_stop_call_output_frame.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_3 : OSTmrStop_which_implies_wit_3.
Proof.
  left; intros.
  unfold tmr_stop_owned, tmr_stop_client_rep, tmr_stop_call_output_frame.
  cbn [tmr_stop_set_error tmr_stop_error tmr_stop_kernel tmr_stop_application].
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_4 : OSTmrStop_which_implies_wit_4.
Proof.
  left.
  intros Client X before context pooled perr arg opt i p nesting mask domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep Hlayout Hunlink Hprofile Haddrs Hints Hwheel Happ Heffects Hraw_type Hraw_state Hdomain Hbinding Hsource Hnonnull.
  assert (Hborrow : forall P Q R : Assertion,
    (P |-- Q ** R) -> (Q ** R |-- P) -> P |-- Q ** (Q -* P)).
  { intros P Q R Hsplit Hmerge heap HP.
    destruct (Hsplit heap HP) as [cell [rest [Hjoin [Hcell Hrest]]]].
    exists cell, rest. split; [exact Hjoin|]. split; [exact Hcell|].
    intros other whole Hjoined Hother.
    apply (Hmerge whole). exists other, rest. split.
    - exact (TmrStopRules.join_comm rest other whole Hjoined).
    - split; assumption. }
  destruct pooled.
  - pose proof Hbinding as Hcurrent.
    change (tmr_stop_pooled_binding sg p i (TimerState (tmr_stop_kernel before))) in Hcurrent.
    destruct Hcurrent as [Hpointer [_ [_ [Hinit [image Himage]]]]].
    pose proof Hprofile as [Henabled [Hnames Hprofile_rest]].
    assert (Hread_value : tmr_stop_call_field_read true i raw_type raw_state StopTypeField before (timerImageType image)).
    { split; [reflexivity|]. exists image. split; [exact Himage|reflexivity]. }
    pose (rest :=
      TmrStopRules.lift (TmrStopOldFields.context_without_field external platform sg context mask
        (tmr_stop_kernel before) i image StopTypeField) **
      tmr_stop_entry_client_rep AppRep perr before).
    assert (Hsplit : tmr_stop_entry_owned AppRep external platform critical sg mask perr context before
      |-- tmr_stop_call_read_cell p StopTypeField (timerImageType image) ** rest).
    { pose proof (tmr_stop_call_entry_split_field AppRep external platform critical sg mask perr
        context before i image StopTypeField Hlayout Hnames Henabled Hinit Himage) as Hfield.
      unfold tmr_stop_call_entry_field_view in Hfield.
      cbn [tmr_stop_field_cell tmr_stop_field_name tmr_stop_field_value] in Hfield.
      rewrite Hpointer. unfold rest. cbn [tmr_stop_call_read_cell].
      sep_apply_l_atomic Hfield. entailer!. }
    assert (Hmerge : tmr_stop_call_read_cell p StopTypeField (timerImageType image) ** rest
      |-- tmr_stop_entry_owned AppRep external platform critical sg mask perr context before).
    { pose proof (tmr_stop_call_entry_merge_field AppRep external platform critical sg mask perr
        context before i image StopTypeField Hlayout Hnames Henabled Hinit Himage) as Hfield.
      unfold tmr_stop_call_entry_field_view in Hfield.
      cbn [tmr_stop_field_cell tmr_stop_field_name tmr_stop_field_value] in Hfield.
      rewrite Hpointer. unfold rest. cbn [tmr_stop_call_read_cell].
      sep_apply_l_atomic Hfield. entailer!. }
    pose proof (Hborrow _ _ _ Hsplit Hmerge) as Hview.
    change (tmr_stop_entry_owned AppRep external platform critical sg mask perr context before |--
      tmr_stop_call_read_cell p StopTypeField (timerImageType image) **
      tmr_stop_call_read_rest AppRep external platform critical sg mask perr false context before p StopTypeField (timerImageType image)) in Hview.
    cbn [tmr_stop_call_read_cell] in Hview.
    unfold tmr_unlink_timer_field in Hview.
    Exists (timerImageType image).
    sep_apply_l_atomic Hview.
    entailer!.
  - 
    assert (Hread_value : tmr_stop_call_field_read false i raw_type raw_state StopTypeField before (tmr_stop_call_raw_type before)).
    { rewrite Hraw_type. split; reflexivity. }
    pose (rest :=
      tmr_stop_context_rep external platform critical sg mask context (tmr_stop_kernel before) **
      (TmrStopRules.undef_store_uchar perr **
       (tmr_stop_raw_state_rep p (tmr_stop_call_raw_type before) nesting (tmr_stop_call_raw_state before) **
        ClientRep (tmr_stop_call_client (tmr_stop_application before))))).
    assert (Hsplit : tmr_stop_entry_owned AppRep external platform critical sg mask perr context before
      |-- tmr_stop_call_read_cell p StopTypeField (tmr_stop_call_raw_type before) ** rest).
    { unfold tmr_stop_entry_owned, tmr_stop_entry_client_rep, rest.
      rewrite Happ.
      rewrite tmr_stop_call_application_raw_type by assumption.
      cbn [tmr_stop_call_read_cell tmr_stop_call_raw_type tmr_stop_call_raw_state].
      entailer!. }
    assert (Hmerge : tmr_stop_call_read_cell p StopTypeField (tmr_stop_call_raw_type before) ** rest
      |-- tmr_stop_entry_owned AppRep external platform critical sg mask perr context before).
    { unfold tmr_stop_entry_owned, tmr_stop_entry_client_rep, rest.
      rewrite Happ.
      rewrite tmr_stop_call_application_raw_type by assumption.
      cbn [tmr_stop_call_read_cell tmr_stop_call_raw_type tmr_stop_call_raw_state].
      entailer!. }
    pose proof (Hborrow _ _ _ Hsplit Hmerge) as Hview.
    change (tmr_stop_entry_owned AppRep external platform critical sg mask perr context before |--
      tmr_stop_call_read_cell p StopTypeField (tmr_stop_call_raw_type before) **
      tmr_stop_call_read_rest AppRep external platform critical sg mask perr false context before p StopTypeField (tmr_stop_call_raw_type before)) in Hview.
    cbn [tmr_stop_call_read_cell] in Hview.
    unfold tmr_unlink_timer_field in Hview.
    Exists (tmr_stop_call_raw_type before).
    sep_apply_l_atomic Hview.
    entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_5 : OSTmrStop_which_implies_wit_5.
Proof.
  left.
  intros Client X before context pooled perr arg opt i p nesting mask domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep ty Hlayout Hunlink Hprofile Haddrs Hints Hwheel Happ Heffects Hraw_type Hraw_state Hdomain Hbinding Hsource Hnonnull Hty Hread.
  assert (Hrestore :
    tmr_stop_call_read_cell p StopTypeField ty **
    tmr_stop_call_read_rest AppRep external platform critical sg mask perr false context before p StopTypeField ty
    |-- tmr_stop_entry_owned AppRep external platform critical sg mask perr context before).
  { intros heap [field_heap [rest_heap [Hjoin [Hfield Hrest]]]].
    apply (Hrest field_heap heap).
    - exact (TmrStopRules.join_comm field_heap rest_heap heap Hjoin).
    - exact Hfield. }
  cbn [tmr_stop_call_read_cell] in Hrestore.
  unfold tmr_unlink_timer_field in Hrestore.
  sep_apply_l_atomic Hrestore.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_6 : OSTmrStop_which_implies_wit_6.
Proof.
  left; intros.
  unfold tmr_stop_entry_owned, tmr_stop_entry_client_rep, tmr_stop_call_output_frame.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_7 : OSTmrStop_which_implies_wit_7.
Proof.
  left; intros.
  unfold tmr_stop_owned, tmr_stop_client_rep, tmr_stop_call_output_frame.
  cbn [tmr_stop_set_error tmr_stop_error tmr_stop_kernel tmr_stop_application].
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_8 : OSTmrStop_which_implies_wit_8.
Proof.
  left.
  intros Client X before context pooled perr arg opt i p nesting mask domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep ty Hlayout Hunlink Hprofile Haddrs Hints Hwheel Happ Heffects Hraw_type Hraw_state Hdomain Hbinding Hsource Hnonnull Hty Hread.
  assert (Hrestore :
    tmr_stop_call_read_cell p StopTypeField ty **
    tmr_stop_call_read_rest AppRep external platform critical sg mask perr false context before p StopTypeField ty
    |-- tmr_stop_entry_owned AppRep external platform critical sg mask perr context before).
  { intros heap [field_heap [rest_heap [Hjoin [Hfield Hrest]]]].
    apply (Hrest field_heap heap).
    - exact (TmrStopRules.join_comm field_heap rest_heap heap Hjoin).
    - exact Hfield. }
  cbn [tmr_stop_call_read_cell] in Hrestore.
  unfold tmr_unlink_timer_field in Hrestore.
  sep_apply_l_atomic Hrestore.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_9 : OSTmrStop_which_implies_wit_9.
Proof.
  left.
  intros Client X before context pooled perr arg opt i p nesting mask domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep ty Hlayout Hunlink Hprofile Haddrs Hints Hwheel Happ Heffects Hraw_type Hraw_state Hdomain Hbinding Hsource Hnonnull Hty Hread.
  pose proof (tmr_stop_context_rep_split_interrupt_with_frame external platform critical sg mask context
    (tmr_stop_kernel before) (tmr_stop_entry_client_rep AppRep perr before)) as Hsplit.
  rewrite <- Hints in Hsplit.
  unfold tmr_stop_entry_owned.
  sep_apply_l_atomic Hsplit.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_10 : OSTmrStop_which_implies_wit_10.
Proof.
  left.
  intros Client X before context pooled perr arg opt i p nesting mask domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep ty Hlayout Hunlink Hprofile Haddrs Hints Hwheel Happ Heffects Hraw_type Hraw_state Hdomain Hbinding Hsource Hnonnull Hty Hread.
  pose proof (tmr_stop_context_rep_merge_interrupt_with_frame external platform critical sg mask context
    (tmr_stop_kernel before) (tmr_stop_entry_client_rep AppRep perr before)) as Hmerge.
  rewrite <- Hints in Hmerge.
  unfold tmr_stop_entry_owned.
  sep_apply_l_atomic Hmerge.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_11 : OSTmrStop_which_implies_wit_11.
Proof.
  left; intros.
  unfold tmr_stop_entry_owned, tmr_stop_entry_client_rep, tmr_stop_call_output_frame.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_12 : OSTmrStop_which_implies_wit_12.
Proof.
  left; intros.
  unfold tmr_stop_owned, tmr_stop_client_rep, tmr_stop_call_output_frame.
  cbn [tmr_stop_set_error tmr_stop_error tmr_stop_kernel tmr_stop_application].
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_13 : OSTmrStop_which_implies_wit_13.
Proof.
  left.
  intros Client X before context pooled perr arg opt i p nesting mask domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep ty Hlayout Hunlink Hprofile Haddrs Hints Hwheel Happ Heffects Hraw_type Hraw_state Hdomain Hbinding Hsource Hnonnull Hty Hread.
  pose proof (tmr_stop_context_rep_merge_interrupt_with_frame external platform critical sg mask context
    (tmr_stop_kernel before) (tmr_stop_entry_client_rep AppRep perr before)) as Hmerge.
  rewrite <- Hints in Hmerge.
  unfold tmr_stop_entry_owned.
  sep_apply_l_atomic Hmerge.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_14 : OSTmrStop_which_implies_wit_14.
Proof.
  left. intros Client X before context pooled perr argument opt i p nesting mask
    domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep.
  intros.
  sep_apply (tmr_stop_call_lock_pre_open AppRep external platform critical sg mask perr context before).
  unfold tmr_stop_call_lock_pre, tmr_stop_call_kernel_any.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_15 : OSTmrStop_which_implies_wit_15.
Proof.
  left. intros Client X before context pooled perr argument opt i p nesting mask
    domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep.
  intros.
  sep_apply (TimerCalleeLift.os_sched_lock_program_post_closed_return platform critical sg
    (os_sched_call_invocation context) (os_sched_call_origin context) mask
    (tmr_stop_kernel before) tmr_stop_call_kernel_any).
  Intros entry kernel.
  assert (Hstep : tmr_stop_call_lock_step critical sg effects context before
    (tmr_stop_set_kernel kernel before)).
  { split.
    - split; [reflexivity|]. exists entry; tauto.
    - rewrite PreH8. apply tmr_stop_call_lock_application. }
  Exists (tmr_stop_set_kernel kernel before).
  unfold tmr_stop_entry_owned, tmr_stop_context_rep.
  cbn [tmr_stop_set_kernel tmr_stop_kernel tmr_stop_entry_client_rep tmr_stop_application].
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_16 : OSTmrStop_which_implies_wit_16.
Proof.
  left.
  intros Client X before context pooled perr arg opt i p nesting mask domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep ty locked Hlayout Hunlink Hprofile Haddrs Hints Hwheel Happ Heffects Hraw_type Hraw_state Hdomain Hbinding Hsource Hnonnull Hty Hread Hzero Hlock.
  assert (Hborrow : forall P Q R : Assertion,
    (P |-- Q ** R) -> (Q ** R |-- P) -> P |-- Q ** (Q -* P)).
  { intros P Q R Hsplit Hmerge heap HP.
    destruct (Hsplit heap HP) as [cell [rest [Hjoin [Hcell Hrest]]]].
    exists cell, rest. split; [exact Hjoin|]. split; [exact Hcell|].
    intros other whole Hjoined Hother.
    apply (Hmerge whole). exists other, rest. split.
    - exact (TmrStopRules.join_comm rest other whole Hjoined).
    - split; assumption. }
  destruct pooled.
  - assert (Hcurrent : tmr_stop_pooled_binding sg p i (TimerState (tmr_stop_kernel locked))).
    { eapply tmr_stop_call_lock_pooled_binding; [exact Hlock|exact Hbinding]. }
    destruct Hcurrent as [Hpointer [_ [_ [Hinit [image Himage]]]]].
    pose proof Hprofile as [Henabled [Hnames Hprofile_rest]].
    assert (Hread_value : tmr_stop_call_field_read true i raw_type raw_state StopStateField locked (timerImageState image)).
    { split; [reflexivity|]. exists image. split; [exact Himage|reflexivity]. }
    pose (rest :=
      TmrStopRules.lift (TmrStopOldFields.context_without_field external platform sg context mask
        (tmr_stop_kernel locked) i image StopStateField) **
      tmr_stop_entry_client_rep AppRep perr locked).
    assert (Hsplit : tmr_stop_entry_owned AppRep external platform critical sg mask perr context locked
      |-- tmr_stop_call_read_cell p StopStateField (timerImageState image) ** rest).
    { pose proof (tmr_stop_call_entry_split_field AppRep external platform critical sg mask perr
        context locked i image StopStateField Hlayout Hnames Henabled Hinit Himage) as Hfield.
      unfold tmr_stop_call_entry_field_view in Hfield.
      cbn [tmr_stop_field_cell tmr_stop_field_name tmr_stop_field_value] in Hfield.
      rewrite Hpointer. unfold rest. cbn [tmr_stop_call_read_cell].
      sep_apply_l_atomic Hfield. entailer!. }
    assert (Hmerge : tmr_stop_call_read_cell p StopStateField (timerImageState image) ** rest
      |-- tmr_stop_entry_owned AppRep external platform critical sg mask perr context locked).
    { pose proof (tmr_stop_call_entry_merge_field AppRep external platform critical sg mask perr
        context locked i image StopStateField Hlayout Hnames Henabled Hinit Himage) as Hfield.
      unfold tmr_stop_call_entry_field_view in Hfield.
      cbn [tmr_stop_field_cell tmr_stop_field_name tmr_stop_field_value] in Hfield.
      rewrite Hpointer. unfold rest. cbn [tmr_stop_call_read_cell].
      sep_apply_l_atomic Hfield. entailer!. }
    pose proof (Hborrow _ _ _ Hsplit Hmerge) as Hview.
    change (tmr_stop_entry_owned AppRep external platform critical sg mask perr context locked |--
      tmr_stop_call_read_cell p StopStateField (timerImageState image) **
      tmr_stop_call_read_rest AppRep external platform critical sg mask perr false context locked p StopStateField (timerImageState image)) in Hview.
    cbn [tmr_stop_call_read_cell] in Hview.
    unfold tmr_unlink_timer_field in Hview.
    Exists (timerImageState image).
    sep_apply_l_atomic Hview.
    entailer!.
  - assert (Hnesting : nesting <= 0).
    { change (nesting = os_sched_lock_ints (tmr_stop_kernel before)) in Hbinding. lia. }
    pose proof (proj2 Hlock) as Hframe.
    rewrite Heffects in Hframe.
    cbn [tmr_stop_call_effects] in Hframe.
    destruct Hframe as [Herror Happlication].
    assert (Hcurrent_type : tmr_stop_call_type_byte (tmr_stop_application locked) = 100).
    { rewrite Happlication.
      rewrite Hraw_type in Hread.
      change (ty = tmr_stop_call_raw_type before /\ before = before) in Hread.
      destruct Hread as [Hread_type Hstate].
      unfold tmr_stop_call_raw_type in Hread_type.
      congruence. }
    assert (Hread_value : tmr_stop_call_field_read false i raw_type raw_state StopStateField locked (tmr_stop_call_raw_state locked)).
    { rewrite Hraw_state. split; reflexivity. }
    pose (rest :=
      tmr_stop_context_rep external platform critical sg mask context (tmr_stop_kernel locked) **
      (TmrStopRules.undef_store_uchar perr **
       (tmr_stop_call_read_cell p StopTypeField 100 **
        ClientRep (tmr_stop_call_client (tmr_stop_application locked))))).
    assert (Hsplit : tmr_stop_entry_owned AppRep external platform critical sg mask perr context locked
      |-- tmr_stop_call_read_cell p StopStateField (tmr_stop_call_raw_state locked) ** rest).
    { unfold tmr_stop_entry_owned, tmr_stop_entry_client_rep, rest.
      rewrite Happ.
      rewrite tmr_stop_call_application_raw_state by assumption.
      cbn [tmr_stop_call_read_cell tmr_stop_call_raw_type tmr_stop_call_raw_state].
      entailer!. }
    assert (Hmerge : tmr_stop_call_read_cell p StopStateField (tmr_stop_call_raw_state locked) ** rest
      |-- tmr_stop_entry_owned AppRep external platform critical sg mask perr context locked).
    { unfold tmr_stop_entry_owned, tmr_stop_entry_client_rep, rest.
      rewrite Happ.
      rewrite tmr_stop_call_application_raw_state by assumption.
      cbn [tmr_stop_call_read_cell tmr_stop_call_raw_type tmr_stop_call_raw_state].
      entailer!. }
    pose proof (Hborrow _ _ _ Hsplit Hmerge) as Hview.
    change (tmr_stop_entry_owned AppRep external platform critical sg mask perr context locked |--
      tmr_stop_call_read_cell p StopStateField (tmr_stop_call_raw_state locked) **
      tmr_stop_call_read_rest AppRep external platform critical sg mask perr false context locked p StopStateField (tmr_stop_call_raw_state locked)) in Hview.
    cbn [tmr_stop_call_read_cell] in Hview.
    unfold tmr_unlink_timer_field in Hview.
    Exists (tmr_stop_call_raw_state locked).
    sep_apply_l_atomic Hview.
    entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_17 : OSTmrStop_which_implies_wit_17.
Proof.
  left. intros Client X before context pooled perr argument opt i p nesting mask
    domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep.
  intros.
  assert (Hprefix : tmr_stop_call_state_prefix critical sg effects pooled p i
    raw_type raw_state context before status locked).
  { exists before, locked.
    split; [exact PreH14|].
    split; [rewrite <- PreH15; exact PreH16|].
    split; [lia|].
    split; [exact PreH18|exact PreH19]. }
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_18 : OSTmrStop_which_implies_wit_18.
Proof.
  left.
  intros Client X before context pooled perr arg opt i p nesting mask domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep locked status Hlayout Hunlink Hprofile Haddrs Hints Hwheel Happ Heffects Hraw_type Hraw_state Hdomain Hbinding Hsource Hstatus Hprefix.
  assert (Hrestore :
    tmr_stop_call_read_cell p StopStateField status **
    tmr_stop_call_read_rest AppRep external platform critical sg mask perr false context locked p StopStateField status
    |-- tmr_stop_entry_owned AppRep external platform critical sg mask perr context locked).
  { intros heap [field_heap [rest_heap [Hjoin [Hfield Hrest]]]].
    apply (Hrest field_heap heap).
    - exact (TmrStopRules.join_comm field_heap rest_heap heap Hjoin).
    - exact Hfield. }
  cbn [tmr_stop_call_read_cell] in Hrestore.
  unfold tmr_unlink_timer_field in Hrestore.
  sep_apply_l_atomic Hrestore.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_19 : OSTmrStop_which_implies_wit_19.
Proof.
  left. intros Client X before context pooled perr argument opt i p nesting mask
    domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep.
  intros.
  destruct (tmr_stop_call_requirements_unlink external critical sg effects pooled p i opt
    argument raw_type raw_state context before locked (proj1 PreH13) PreH14)
    as [Hpointer [Hinit Hrunning]].
  sep_apply (tmr_stop_call_entry_split_timer AppRep external platform critical sg mask perr context locked).
  unfold tmr_stop_call_unlink_client_frame.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_20 : OSTmrStop_which_implies_wit_20.
Proof.
  left. intros Client X before context pooled perr argument opt i p nesting mask
    domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep.
  intros.
  destruct PreH17 as [node [Hnode Hrunning]].
  assert (Henabled : cfgTimerEnabled (osKernelConfig sg) = true) by exact (proj1 PreH3).
  assert (Hmerge :
    (TimerCalleeLift.tmr_unlink_configured_post sg (TimerState (tmr_stop_kernel locked)) i **
     tmr_stop_unlink_frame external platform sg mask context locked) |--
    EX timers, coq_prop (timer_unlink sg (TimerState (tmr_stop_kernel locked)) i = Some timers) &&
      tmr_stop_context_rep external platform critical sg mask context
        (replace_TimerS timers (tmr_stop_kernel locked))).
  { intros heap Hparts.
    pose proof (proj2 (TmrStopRules.lift_sepcon _ _ heap) Hparts) as Hlifted.
    pose proof (TmrStopRules.lift_entailment _ _
      (TmrStopOldFields.unlink_post_merge_context external platform critical sg context mask
        (tmr_stop_kernel locked) i node Henabled PreH16 Hnode Hrunning) heap Hlifted) as Hmerged.
    destruct Hmerged as [timers [Hstep Hcontext]].
    exists timers. split; [exact Hstep|].
    exact (proj2 (TimerCalleeLift.os_sched_closed_resources_lift external platform critical sg
      context mask (replace_TimerS timers (tmr_stop_kernel locked))) heap Hcontext). }
  unfold tmr_stop_call_unlink_client_frame.
  assert (Hreassociate :
    TimerCalleeLift.tmr_unlink_configured_post sg (TimerState (tmr_stop_kernel locked)) i **
      (tmr_stop_unlink_frame external platform sg mask context locked **
       tmr_stop_entry_client_rep AppRep perr locked) |--
    (TimerCalleeLift.tmr_unlink_configured_post sg (TimerState (tmr_stop_kernel locked)) i **
     tmr_stop_unlink_frame external platform sg mask context locked) **
      tmr_stop_entry_client_rep AppRep perr locked).
  { entailer!. }
  sepcon_assoc_change.
  rewrite Hreassociate.
  rewrite Hmerge.
  Intros timers.
  assert (Hstep : tmr_stop_call_unlink_step sg i locked
    (tmr_stop_set_kernel (replace_TimerS timers (tmr_stop_kernel locked)) locked)).
  { apply tmr_stop_unlink_step. assumption. }
  Exists (tmr_stop_set_kernel (replace_TimerS timers (tmr_stop_kernel locked)) locked).
  unfold tmr_stop_entry_owned.
  cbn [tmr_stop_set_kernel tmr_stop_kernel tmr_stop_entry_client_rep tmr_stop_application].
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_21 : OSTmrStop_which_implies_wit_21.
Proof.
  left; intros.
  unfold tmr_stop_entry_owned, tmr_stop_entry_client_rep, tmr_stop_call_output_frame.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_22 : OSTmrStop_which_implies_wit_22.
Proof.
  left; intros.
  unfold tmr_stop_owned, tmr_stop_client_rep, tmr_stop_call_output_frame.
  cbn [tmr_stop_set_error tmr_stop_error tmr_stop_kernel tmr_stop_application].
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_23 : OSTmrStop_which_implies_wit_23.
Proof.
  left.
  intros Client X before context pooled error_addr argument opt i p nesting mask
    domain raw_state raw_type effects AppRep callback sg critical platform external
    ClientRep locked stopped Hlayout Hunlink_layout Hprofile Haddresses Hints Hwheel
    Happ Heffects Htype Hstate Hdomain Hbinding Hsource Hprefix Hunlink Hopt.
  destruct (proj1 (proj1 Hsource) locked Hprefix) as [Hpointer [Hinit Hrunning]].
  pose proof Hunlink as Hstep.
  destruct Hstep as [_ [timers [Hstep Hstopped]]].
  destruct (timer_unlink_clears_links_and_stops _ _ _ _ Hstep)
    as [node [image [_ [Himage Himage_fields]]]].
  assert (Hcurrent_image :
    timerImages (TimerState (tmr_stop_kernel (tmr_stop_set_error 0 stopped))) i = Some image).
  { rewrite Hstopped. exact Himage. }
  assert (Hcurrent_init : timer_api_initialized
    (TimerState (tmr_stop_kernel (tmr_stop_set_error 0 stopped)))).
  { rewrite Hstopped. change (timer_api_initialized timers).
    unfold timer_api_initialized.
    rewrite (timer_unlink_preserves_initialization_phase _ _ _ _ Hstep).
    exact Hinit. }
  assert (Hread : tmr_stop_call_field_read pooled i raw_type raw_state
    StopCallbackField (tmr_stop_set_error 0 stopped) (timerImageCallback image)).
  { apply tmr_stop_image_field_read. exact Hcurrent_image. }
  pose proof Hprofile as Hconfig.
  destruct Hconfig as [Henabled [Hnames Hconfiguration]].
  assert (Hborrow :
    tmr_stop_owned AppRep external platform critical sg mask error_addr context
      (tmr_stop_set_error 0 stopped) |--
    tmr_stop_call_read_cell p StopCallbackField (timerImageCallback image) **
    tmr_stop_call_read_rest AppRep external platform critical sg mask error_addr
      true context (tmr_stop_set_error 0 stopped) p StopCallbackField (timerImageCallback image)).
  { pose proof (tmr_stop_owned_split_field AppRep external platform critical sg mask
      error_addr context (tmr_stop_set_error 0 stopped) i image StopCallbackField
      Hlayout Hnames Henabled Hcurrent_init Hcurrent_image) as Hsplit.
    pose proof (tmr_stop_owned_merge_field AppRep external platform critical sg mask
      error_addr context (tmr_stop_set_error 0 stopped) i image StopCallbackField
      Hlayout Hnames Henabled Hcurrent_init Hcurrent_image) as Hmerge.
    rewrite Hpointer.
    unfold tmr_stop_call_read_rest.
    cbn [tmr_stop_call_read_cell].
    rewrite Hsplit at 1.
    unfold tmr_stop_owned_field_view in Hmerge |- *.
    cbn [tmr_stop_field_cell tmr_stop_field_name tmr_stop_field_value] in Hmerge |- *.
    sepcon_assoc_change.
    sepcon_cancel.
    apply_sepcon_adjoint.
    sep_apply_r_atomic Hmerge.
    entailer!. }
  Exists (timerImageCallback image).
  sep_apply Hborrow.
  unfold tmr_stop_call_read_cell.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_24 : OSTmrStop_which_implies_wit_24.
Proof.
  left. intros.
  assert (Hrestore : forall P Q : Assertion, P ** (P -* Q) |-- Q).
  { intros P Q heap [cell [rest [Hjoin [Hcell Hrest]]]].
    exact (Hrest cell heap (TmrStopRules.join_comm cell rest heap Hjoin) Hcell). }
  unfold tmr_stop_call_read_rest.
  cbn [tmr_stop_call_read_cell].
  unfold tmr_unlink_timer_field.
  match goal with
  | |- context [TmrStopRules.wand ?P ?Q] => sep_apply (Hrestore P Q)
  end.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_25 : OSTmrStop_which_implies_wit_25.
Proof.
  left.
  intros Client X before context pooled error_addr argument opt i p nesting mask
    domain raw_state raw_type effects AppRep callback sg critical platform external
    ClientRep locked stopped callback_ptr Hlayout Hunlink_layout Hprofile Haddresses Hints Hwheel
    Happ Heffects Htype Hstate Hdomain Hbinding Hsource Hprefix Hunlink Hopt Hfn Hcallback_read.
  destruct (proj1 (proj1 Hsource) locked Hprefix) as [Hpointer [Hinit Hrunning]].
  pose proof Hunlink as Hstep.
  destruct Hstep as [_ [timers [Hstep Hstopped]]].
  destruct (timer_unlink_clears_links_and_stops _ _ _ _ Hstep)
    as [node [image [_ [Himage Himage_fields]]]].
  assert (Hcurrent_image :
    timerImages (TimerState (tmr_stop_kernel (tmr_stop_set_error 0 stopped))) i = Some image).
  { rewrite Hstopped. exact Himage. }
  assert (Hcurrent_init : timer_api_initialized
    (TimerState (tmr_stop_kernel (tmr_stop_set_error 0 stopped)))).
  { rewrite Hstopped. change (timer_api_initialized timers).
    unfold timer_api_initialized.
    rewrite (timer_unlink_preserves_initialization_phase _ _ _ _ Hstep).
    exact Hinit. }
  assert (Hread : tmr_stop_call_field_read pooled i raw_type raw_state
    StopArgumentField (tmr_stop_set_error 0 stopped) (timerImageArg image)).
  { apply tmr_stop_image_field_read. exact Hcurrent_image. }
  pose proof Hprofile as Hconfig.
  destruct Hconfig as [Henabled [Hnames Hconfiguration]].
  assert (Hborrow :
    tmr_stop_owned AppRep external platform critical sg mask error_addr context
      (tmr_stop_set_error 0 stopped) |--
    tmr_stop_call_read_cell p StopArgumentField (timerImageArg image) **
    tmr_stop_call_read_rest AppRep external platform critical sg mask error_addr
      true context (tmr_stop_set_error 0 stopped) p StopArgumentField (timerImageArg image)).
  { pose proof (tmr_stop_owned_split_field AppRep external platform critical sg mask
      error_addr context (tmr_stop_set_error 0 stopped) i image StopArgumentField
      Hlayout Hnames Henabled Hcurrent_init Hcurrent_image) as Hsplit.
    pose proof (tmr_stop_owned_merge_field AppRep external platform critical sg mask
      error_addr context (tmr_stop_set_error 0 stopped) i image StopArgumentField
      Hlayout Hnames Henabled Hcurrent_init Hcurrent_image) as Hmerge.
    rewrite Hpointer.
    unfold tmr_stop_call_read_rest.
    cbn [tmr_stop_call_read_cell].
    rewrite Hsplit at 1.
    unfold tmr_stop_owned_field_view in Hmerge |- *.
    cbn [tmr_stop_field_cell tmr_stop_field_name tmr_stop_field_value] in Hmerge |- *.
    sepcon_assoc_change.
    sepcon_cancel.
    apply_sepcon_adjoint.
    sep_apply_r_atomic Hmerge.
    entailer!. }
  Exists (timerImageArg image).
  sep_apply Hborrow.
  unfold tmr_stop_call_read_cell.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_26 : OSTmrStop_which_implies_wit_26.
Proof.
  left.
  intros Client X before context pooled error_addr argument opt i p nesting mask
    domain raw_state raw_type effects AppRep callback sg critical platform external
    ClientRep locked stopped callback_ptr stored_arg Hlayout Hunlink_layout Hprofile Haddresses Hints Hwheel
    Happ Heffects Htype Hstate Hdomain Hbinding Hsource Hprefix Hunlink Hopt Hfn Hcallback_read Hargument_read.
  assert (Hselect : tmr_stop_select_callback_program p i opt argument
    (tmr_stop_set_error 0 stopped) (Some (callback_ptr, p, stored_arg)) (tmr_stop_set_error 0 stopped)).
  { eapply tmr_stop_select_stored_argument; eassumption. }
  assert (Hcallback_prefix : tmr_stop_call_callback_prefix critical sg effects pooled p i opt argument
    raw_type raw_state context before callback_ptr p stored_arg (tmr_stop_set_error 0 stopped)).
  { destruct Hprefix as [observed [entry_locked [Hp [Htype_read [Hnest [Hlock Hstate_read]]]]]].
    exists observed, entry_locked, locked, stopped.
    repeat first [assumption | apply conj]. }
  assert (Hcallback_domain : domain callback_ptr p stored_arg context (tmr_stop_set_error 0 stopped)).
  { rewrite Hdomain. apply tmr_stop_call_callback_prefix_domain. exact Hcallback_prefix. }
  sepcon_assoc_change.
  intros heap Hheap. split.
  - repeat first [assumption | apply conj].
  - pose proof (tmr_stop_call_callback_resources_merge AppRep external platform critical sg
      effects mask error_addr domain pooled p i opt argument raw_type raw_state context before
      _ heap Hheap) as Hmerged.
    pose proof (proj1 Hmerged callback_ptr p stored_arg (tmr_stop_set_error 0 stopped) Hcallback_prefix) as Hcap.
  pose proof (tmr_stop_call_callback_argument_consequence AppRep external platform critical
    sg effects mask error_addr domain callback_ptr p stored_arg heap Hcap) as Hargument_cap.
    eapply TimerCallback_C_Rules.func_ptr_spec_mono; [|exact Hargument_cap].
    intros body current Hfull call_context call_before.
    eapply TimerCallback_C_Rules.HoareFun_conseq; [| |exact (Hfull call_context call_before)].
    + intros [actual_self actual_argument] current_heap [[Hcall_domain Hargs] Howned].
      exact (conj Hcall_domain (conj Hargs Howned)).
    + intros [actual_self actual_argument] [] current_heap Hpost. exact Hpost.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_27 : OSTmrStop_which_implies_wit_27.
Proof.
  unfold OSTmrStop_which_implies_wit_27; left.
  intros Client X before context pooled perr argument opt i p nesting mask domain
    raw_state raw_type effects AppRep callback sg critical platform external ClientRep
    stopped fn_ stored_arg Hlayout Hunlink_layout Hprofile Haddresses Hints_addr
    Hwheel_addr HAppRep Heffects Hraw_type Hraw_state Hdomain Hbinding Hsource Hprefix.
  assert (Hresume :
    tmr_stop_callback_post AppRep external platform critical sg effects mask perr
      fn_ p stored_arg context (tmr_stop_set_error 0 stopped) (p, stored_arg) tt |--
    tmr_stop_call_running_ready AppRep external platform critical sg effects mask perr
      pooled p i opt argument raw_type raw_state context before).
  { intros heap [returned [after [Hargs [Hcallback [Hready Howned]]]]].
    exists returned, after; split.
    - destruct Hprefix as [observed [locked [state_read [unlinked
        [Hpointer [Htype [Hints [Hlock [Hstate [Hunlink Hselect]]]]]]]]]].
      exists state_read, unlinked, (Some (fn_, p, stored_arg)), (tmr_stop_set_error 0 stopped).
      split.
      + exists observed, locked; split; [exact Hpointer|].
        split; [exact Htype|]. split; [exact Hints|]. split; assumption.
      + split; [exact Hunlink|]. split; [exact Hselect|].
        apply tmr_stop_optional_callback_some; exact Hcallback.
    - split; assumption. }
  sep_apply Hresume.
  assert (Hforget : forall pointer value,
    TimerCallback_C_Rules.Rules.derivable1
      (TimerCallback_C_Rules.Rules.store_ptr pointer value)
      (TimerCallback_C_Rules.Rules.undef_store_ptr pointer)).
  { intros pointer value [state environment] Hstore.
    apply (proj2 (TimerCallback_C_Rules.Rules.undef_store_ptr_slice environment pointer state)).
    apply (UCOS2_C_Rules.store_ptr_undef_store_ptr pointer value).
    exact (proj1 (TimerCallback_C_Rules.Rules.store_ptr_slice environment pointer value state) Hstore). }
  sep_apply Hforget.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_28 : OSTmrStop_which_implies_wit_28.
Proof.
  left. intros.
  assert (Hrestore : forall P Q : Assertion, P ** (P -* Q) |-- Q).
  { intros P Q heap [cell [rest [Hjoin [Hcell Hrest]]]].
    exact (Hrest cell heap (TmrStopRules.join_comm cell rest heap Hjoin) Hcell). }
  unfold tmr_stop_call_read_rest.
  cbn [tmr_stop_call_read_cell].
  unfold tmr_unlink_timer_field.
  match goal with
  | |- context [TmrStopRules.wand ?P ?Q] => sep_apply (Hrestore P Q)
  end.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_29 : OSTmrStop_which_implies_wit_29.
Proof.
  left; intros.
  unfold tmr_stop_owned, tmr_stop_client_rep, tmr_stop_call_output_frame.
  cbn [tmr_stop_set_error tmr_stop_kernel tmr_stop_error tmr_stop_application].
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_30 : OSTmrStop_which_implies_wit_30.
Proof.
  left; intros.
  unfold tmr_stop_owned, tmr_stop_client_rep, tmr_stop_call_output_frame.
  cbn [tmr_stop_set_error tmr_stop_kernel tmr_stop_error tmr_stop_application].
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_31 : OSTmrStop_which_implies_wit_31.
Proof.
  unfold OSTmrStop_which_implies_wit_31; left.
  intros Client X before context pooled perr argument opt i p nesting mask domain
    raw_state raw_type effects AppRep callback sg critical platform external ClientRep
    locked stopped fn_ Hlayout Hunlink_layout Hprofile Haddresses Hints_addr
    Hwheel_addr HAppRep Heffects Hraw_type Hraw_state Hdomain Hbinding Hsource Hstateprefix Hunlink Hopt Hfn Hread.
  assert (Hselect : tmr_stop_select_callback_program p i opt argument
    (tmr_stop_set_error 0 stopped) None (tmr_stop_set_error 143 (tmr_stop_set_error 0 stopped))).
  {
    apply tmr_stop_select_null_callback.
    - left; exact Hopt.
    - rewrite Hfn in Hread; exact Hread.
  }
  assert (Hready : tmr_stop_unlock_ready external critical sg context (tmr_stop_set_error 143 (tmr_stop_set_error 0 stopped))).
  { eapply tmr_stop_call_requirements_no_callback;
      [exact (proj1 Hsource)|exact Hstateprefix|exact Hunlink|exact Hselect]. }
  assert (Hresume :
    tmr_stop_owned AppRep external platform critical sg mask perr context (tmr_stop_set_error 143 (tmr_stop_set_error 0 stopped)) |--
    tmr_stop_call_running_ready AppRep external platform critical sg effects mask perr
      pooled p i opt argument raw_type raw_state context before).
  { intros heap Howned. exists context, (tmr_stop_set_error 143 (tmr_stop_set_error 0 stopped)); split.
    - exists locked, stopped, None, (tmr_stop_set_error 143 (tmr_stop_set_error 0 stopped)).
      split; [exact Hstateprefix|]. split; [exact Hunlink|].
      split; [exact Hselect|apply tmr_stop_optional_callback_none].
    - split; assumption. }
  sep_apply Hresume.
  assert (Hforget : forall pointer value,
    TimerCallback_C_Rules.Rules.derivable1
      (TimerCallback_C_Rules.Rules.store_ptr pointer value)
      (TimerCallback_C_Rules.Rules.undef_store_ptr pointer)).
  { intros pointer value [state environment] Hstore.
    apply (proj2 (TimerCallback_C_Rules.Rules.undef_store_ptr_slice environment pointer state)).
    apply (UCOS2_C_Rules.store_ptr_undef_store_ptr pointer value).
    exact (proj1 (TimerCallback_C_Rules.Rules.store_ptr_slice environment pointer value state) Hstore). }
  sep_apply Hforget.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_32 : OSTmrStop_which_implies_wit_32.
Proof.
  left.
  intros Client X before context pooled error_addr argument opt i p nesting mask
    domain raw_state raw_type effects AppRep callback sg critical platform external
    ClientRep locked stopped Hlayout Hunlink_layout Hprofile Haddresses Hints Hwheel
    Happ Heffects Htype Hstate Hdomain Hbinding Hsource Hprefix Hunlink Hopt.
  destruct (proj1 (proj1 Hsource) locked Hprefix) as [Hpointer [Hinit Hrunning]].
  pose proof Hunlink as Hstep.
  destruct Hstep as [_ [timers [Hstep Hstopped]]].
  destruct (timer_unlink_clears_links_and_stops _ _ _ _ Hstep)
    as [node [image [_ [Himage Himage_fields]]]].
  assert (Hcurrent_image :
    timerImages (TimerState (tmr_stop_kernel (tmr_stop_set_error 0 stopped))) i = Some image).
  { rewrite Hstopped. exact Himage. }
  assert (Hcurrent_init : timer_api_initialized
    (TimerState (tmr_stop_kernel (tmr_stop_set_error 0 stopped)))).
  { rewrite Hstopped. change (timer_api_initialized timers).
    unfold timer_api_initialized.
    rewrite (timer_unlink_preserves_initialization_phase _ _ _ _ Hstep).
    exact Hinit. }
  assert (Hread : tmr_stop_call_field_read pooled i raw_type raw_state
    StopCallbackField (tmr_stop_set_error 0 stopped) (timerImageCallback image)).
  { apply tmr_stop_image_field_read. exact Hcurrent_image. }
  pose proof Hprofile as Hconfig.
  destruct Hconfig as [Henabled [Hnames Hconfiguration]].
  assert (Hborrow :
    tmr_stop_owned AppRep external platform critical sg mask error_addr context
      (tmr_stop_set_error 0 stopped) |--
    tmr_stop_call_read_cell p StopCallbackField (timerImageCallback image) **
    tmr_stop_call_read_rest AppRep external platform critical sg mask error_addr
      true context (tmr_stop_set_error 0 stopped) p StopCallbackField (timerImageCallback image)).
  { pose proof (tmr_stop_owned_split_field AppRep external platform critical sg mask
      error_addr context (tmr_stop_set_error 0 stopped) i image StopCallbackField
      Hlayout Hnames Henabled Hcurrent_init Hcurrent_image) as Hsplit.
    pose proof (tmr_stop_owned_merge_field AppRep external platform critical sg mask
      error_addr context (tmr_stop_set_error 0 stopped) i image StopCallbackField
      Hlayout Hnames Henabled Hcurrent_init Hcurrent_image) as Hmerge.
    rewrite Hpointer.
    unfold tmr_stop_call_read_rest.
    cbn [tmr_stop_call_read_cell].
    rewrite Hsplit at 1.
    unfold tmr_stop_owned_field_view in Hmerge |- *.
    cbn [tmr_stop_field_cell tmr_stop_field_name tmr_stop_field_value] in Hmerge |- *.
    sepcon_assoc_change.
    sepcon_cancel.
    apply_sepcon_adjoint.
    sep_apply_r_atomic Hmerge.
    entailer!. }
  Exists (timerImageCallback image).
  sep_apply Hborrow.
  unfold tmr_stop_call_read_cell.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_33 : OSTmrStop_which_implies_wit_33.
Proof.
  left. intros.
  assert (Hrestore : forall P Q : Assertion, P ** (P -* Q) |-- Q).
  { intros P Q heap [cell [rest [Hjoin [Hcell Hrest]]]].
    exact (Hrest cell heap (TmrStopRules.join_comm cell rest heap Hjoin) Hcell). }
  unfold tmr_stop_call_read_rest.
  cbn [tmr_stop_call_read_cell].
  unfold tmr_unlink_timer_field.
  match goal with
  | |- context [TmrStopRules.wand ?P ?Q] => sep_apply (Hrestore P Q)
  end.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_34 : OSTmrStop_which_implies_wit_34.
Proof.
  left.
  intros Client X before context pooled error_addr argument opt i p nesting mask
    domain raw_state raw_type effects AppRep callback sg critical platform external
    ClientRep locked stopped callback_ptr Hlayout Hunlink_layout Hprofile Haddresses Hints Hwheel
    Happ Heffects Htype Hstate Hdomain Hbinding Hsource Hprefix Hunlink Hopt Hfn Hcallback_read.
  assert (Hselect : tmr_stop_select_callback_program p i opt argument
    (tmr_stop_set_error 0 stopped) (Some (callback_ptr, p, argument)) (tmr_stop_set_error 0 stopped)).
  { eapply tmr_stop_select_api_argument; eassumption. }
  assert (Hcallback_prefix : tmr_stop_call_callback_prefix critical sg effects pooled p i opt argument
    raw_type raw_state context before callback_ptr p argument (tmr_stop_set_error 0 stopped)).
  { destruct Hprefix as [observed [entry_locked [Hp [Htype_read [Hnest [Hlock Hstate_read]]]]]].
    exists observed, entry_locked, locked, stopped.
    repeat first [assumption | apply conj]. }
  assert (Hcallback_domain : domain callback_ptr p argument context (tmr_stop_set_error 0 stopped)).
  { rewrite Hdomain. apply tmr_stop_call_callback_prefix_domain. exact Hcallback_prefix. }
  sepcon_assoc_change.
  intros heap Hheap. split.
  - repeat first [assumption | apply conj].
  - pose proof (tmr_stop_call_callback_resources_merge AppRep external platform critical sg
      effects mask error_addr domain pooled p i opt argument raw_type raw_state context before
      _ heap Hheap) as Hmerged.
    pose proof (proj1 Hmerged callback_ptr p argument (tmr_stop_set_error 0 stopped) Hcallback_prefix) as Hcap.
    eapply TimerCallback_C_Rules.func_ptr_spec_mono; [|exact Hcap].
    intros body current Hfull call_context call_before.
    eapply TimerCallback_C_Rules.HoareFun_conseq; [| |exact (Hfull call_context call_before)].
    + intros [actual_self actual_argument] current_heap [[Hcall_domain Hargs] Howned].
      exact (conj Hcall_domain (conj Hargs Howned)).
    + intros [actual_self actual_argument] [] current_heap Hpost. exact Hpost.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_35 : OSTmrStop_which_implies_wit_35.
Proof.
  unfold OSTmrStop_which_implies_wit_35; left.
  intros Client X before context pooled perr argument opt i p nesting mask domain
    raw_state raw_type effects AppRep callback sg critical platform external ClientRep
    stopped fn_ Hlayout Hunlink_layout Hprofile Haddresses Hints_addr
    Hwheel_addr HAppRep Heffects Hraw_type Hraw_state Hdomain Hbinding Hsource Hprefix.
  assert (Hresume :
    tmr_stop_callback_post AppRep external platform critical sg effects mask perr
      fn_ p argument context (tmr_stop_set_error 0 stopped) (p, argument) tt |--
    tmr_stop_call_running_ready AppRep external platform critical sg effects mask perr
      pooled p i opt argument raw_type raw_state context before).
  { intros heap [returned [after [Hargs [Hcallback [Hready Howned]]]]].
    exists returned, after; split.
    - destruct Hprefix as [observed [locked [state_read [unlinked
        [Hpointer [Htype [Hints [Hlock [Hstate [Hunlink Hselect]]]]]]]]]].
      exists state_read, unlinked, (Some (fn_, p, argument)), (tmr_stop_set_error 0 stopped).
      split.
      + exists observed, locked; split; [exact Hpointer|].
        split; [exact Htype|]. split; [exact Hints|]. split; assumption.
      + split; [exact Hunlink|]. split; [exact Hselect|].
        apply tmr_stop_optional_callback_some; exact Hcallback.
    - split; assumption. }
  sep_apply Hresume.
  assert (Hforget : forall pointer value,
    TimerCallback_C_Rules.Rules.derivable1
      (TimerCallback_C_Rules.Rules.store_ptr pointer value)
      (TimerCallback_C_Rules.Rules.undef_store_ptr pointer)).
  { intros pointer value [state environment] Hstore.
    apply (proj2 (TimerCallback_C_Rules.Rules.undef_store_ptr_slice environment pointer state)).
    apply (UCOS2_C_Rules.store_ptr_undef_store_ptr pointer value).
    exact (proj1 (TimerCallback_C_Rules.Rules.store_ptr_slice environment pointer value state) Hstore). }
  sep_apply Hforget.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_36 : OSTmrStop_which_implies_wit_36.
Proof.
  left. intros.
  assert (Hrestore : forall P Q : Assertion, P ** (P -* Q) |-- Q).
  { intros P Q heap [cell [rest [Hjoin [Hcell Hrest]]]].
    exact (Hrest cell heap (TmrStopRules.join_comm cell rest heap Hjoin) Hcell). }
  unfold tmr_stop_call_read_rest.
  cbn [tmr_stop_call_read_cell].
  unfold tmr_unlink_timer_field.
  match goal with
  | |- context [TmrStopRules.wand ?P ?Q] => sep_apply (Hrestore P Q)
  end.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_37 : OSTmrStop_which_implies_wit_37.
Proof.
  left; intros.
  unfold tmr_stop_owned, tmr_stop_client_rep, tmr_stop_call_output_frame.
  cbn [tmr_stop_set_error tmr_stop_kernel tmr_stop_error tmr_stop_application].
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_38 : OSTmrStop_which_implies_wit_38.
Proof.
  left; intros.
  unfold tmr_stop_owned, tmr_stop_client_rep, tmr_stop_call_output_frame.
  cbn [tmr_stop_set_error tmr_stop_kernel tmr_stop_error tmr_stop_application].
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_39 : OSTmrStop_which_implies_wit_39.
Proof.
  unfold OSTmrStop_which_implies_wit_39; left.
  intros Client X before context pooled perr argument opt i p nesting mask domain
    raw_state raw_type effects AppRep callback sg critical platform external ClientRep
    locked stopped fn_ Hlayout Hunlink_layout Hprofile Haddresses Hints_addr
    Hwheel_addr HAppRep Heffects Hraw_type Hraw_state Hdomain Hbinding Hsource Hstateprefix Hunlink Hopt Hfn Hread.
  assert (Hselect : tmr_stop_select_callback_program p i opt argument
    (tmr_stop_set_error 0 stopped) None (tmr_stop_set_error 143 (tmr_stop_set_error 0 stopped))).
  {
    apply tmr_stop_select_null_callback.
    - right; exact Hopt.
    - rewrite Hfn in Hread; exact Hread.
  }
  assert (Hready : tmr_stop_unlock_ready external critical sg context (tmr_stop_set_error 143 (tmr_stop_set_error 0 stopped))).
  { eapply tmr_stop_call_requirements_no_callback;
      [exact (proj1 Hsource)|exact Hstateprefix|exact Hunlink|exact Hselect]. }
  assert (Hresume :
    tmr_stop_owned AppRep external platform critical sg mask perr context (tmr_stop_set_error 143 (tmr_stop_set_error 0 stopped)) |--
    tmr_stop_call_running_ready AppRep external platform critical sg effects mask perr
      pooled p i opt argument raw_type raw_state context before).
  { intros heap Howned. exists context, (tmr_stop_set_error 143 (tmr_stop_set_error 0 stopped)); split.
    - exists locked, stopped, None, (tmr_stop_set_error 143 (tmr_stop_set_error 0 stopped)).
      split; [exact Hstateprefix|]. split; [exact Hunlink|].
      split; [exact Hselect|apply tmr_stop_optional_callback_none].
    - split; assumption. }
  sep_apply Hresume.
  assert (Hforget : forall pointer value,
    TimerCallback_C_Rules.Rules.derivable1
      (TimerCallback_C_Rules.Rules.store_ptr pointer value)
      (TimerCallback_C_Rules.Rules.undef_store_ptr pointer)).
  { intros pointer value [state environment] Hstore.
    apply (proj2 (TimerCallback_C_Rules.Rules.undef_store_ptr_slice environment pointer state)).
    apply (UCOS2_C_Rules.store_ptr_undef_store_ptr pointer value).
    exact (proj1 (TimerCallback_C_Rules.Rules.store_ptr_slice environment pointer value state) Hstore). }
  sep_apply Hforget.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_40 : OSTmrStop_which_implies_wit_40.
Proof.
  unfold OSTmrStop_which_implies_wit_40; left.
  intros Client X before context pooled perr argument opt i p nesting mask domain
    raw_state raw_type effects AppRep callback sg critical platform external ClientRep
    locked stopped Hlayout Hunlink_layout Hprofile Haddresses Hints_addr
    Hwheel_addr HAppRep Heffects Hraw_type Hraw_state Hdomain Hbinding Hsource Hstateprefix Hunlink Hopt.
  assert (Hselect : tmr_stop_select_callback_program p i opt argument
    (tmr_stop_set_error 0 stopped) None (tmr_stop_set_error 0 stopped)).
  {
    apply tmr_stop_select_none; exact Hopt.
  }
  assert (Hready : tmr_stop_unlock_ready external critical sg context (tmr_stop_set_error 0 stopped)).
  { eapply tmr_stop_call_requirements_no_callback;
      [exact (proj1 Hsource)|exact Hstateprefix|exact Hunlink|exact Hselect]. }
  assert (Hresume :
    tmr_stop_owned AppRep external platform critical sg mask perr context (tmr_stop_set_error 0 stopped) |--
    tmr_stop_call_running_ready AppRep external platform critical sg effects mask perr
      pooled p i opt argument raw_type raw_state context before).
  { intros heap Howned. exists context, (tmr_stop_set_error 0 stopped); split.
    - exists locked, stopped, None, (tmr_stop_set_error 0 stopped).
      split; [exact Hstateprefix|]. split; [exact Hunlink|].
      split; [exact Hselect|apply tmr_stop_optional_callback_none].
    - split; assumption. }
  sep_apply Hresume.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_41 : OSTmrStop_which_implies_wit_41.
Proof.
  unfold OSTmrStop_which_implies_wit_41; left.
  intros Client X before context pooled perr argument opt i p nesting mask domain
    raw_state raw_type effects AppRep callback sg critical platform external ClientRep
    locked stopped Hlayout Hunlink_layout Hprofile Haddresses Hints_addr
    Hwheel_addr HAppRep Heffects Hraw_type Hraw_state Hdomain Hbinding Hsource Hstateprefix Hunlink Hzero Hthree Hfour.
  assert (Hselect : tmr_stop_select_callback_program p i opt argument
    (tmr_stop_set_error 0 stopped) None (tmr_stop_set_error 132 (tmr_stop_set_error 0 stopped))).
  {
    apply tmr_stop_select_invalid_option; assumption.
  }
  assert (Hready : tmr_stop_unlock_ready external critical sg context (tmr_stop_set_error 132 (tmr_stop_set_error 0 stopped))).
  { eapply tmr_stop_call_requirements_no_callback;
      [exact (proj1 Hsource)|exact Hstateprefix|exact Hunlink|exact Hselect]. }
  assert (Hresume :
    tmr_stop_owned AppRep external platform critical sg mask perr context (tmr_stop_set_error 132 (tmr_stop_set_error 0 stopped)) |--
    tmr_stop_call_running_ready AppRep external platform critical sg effects mask perr
      pooled p i opt argument raw_type raw_state context before).
  { intros heap Howned. exists context, (tmr_stop_set_error 132 (tmr_stop_set_error 0 stopped)); split.
    - exists locked, stopped, None, (tmr_stop_set_error 132 (tmr_stop_set_error 0 stopped)).
      split; [exact Hstateprefix|]. split; [exact Hunlink|].
      split; [exact Hselect|apply tmr_stop_optional_callback_none].
    - split; assumption. }
  sep_apply Hresume.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_42 : OSTmrStop_which_implies_wit_42.
Proof.
  left; intros.
  unfold tmr_stop_owned, tmr_stop_client_rep, tmr_stop_call_output_frame.
  cbn [tmr_stop_set_error tmr_stop_kernel tmr_stop_error tmr_stop_application].
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_43 : OSTmrStop_which_implies_wit_43.
Proof.
  left; intros.
  unfold tmr_stop_owned, tmr_stop_client_rep, tmr_stop_call_output_frame.
  cbn [tmr_stop_set_error tmr_stop_kernel tmr_stop_error tmr_stop_application].
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_44 : OSTmrStop_which_implies_wit_44.
Proof.
  unfold OSTmrStop_which_implies_wit_44; left.
  intros Client X before context pooled perr argument opt i p nesting mask domain
    raw_state raw_type effects AppRep callback sg critical platform external ClientRep
    Hlayout Hunlink_layout Hprofile Haddresses Hints_addr Hwheel_addr
    HAppRep Heffects Hraw_type Hraw_state Hdomain Hbinding Hsource.
  intros heap [resources_heap [owned_heap [Hjoin [Hresources
    [calling [current [Hprefix [Hready Howned]]]]]]]].
  exists calling, current.
  repeat first [assumption | split].
  exists resources_heap, owned_heap; split; [exact Hjoin|].
  split; assumption.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_45 : OSTmrStop_which_implies_wit_45.
Proof.
  left. intros Client X before context pooled perr argument opt i p nesting mask
    domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep.
  intros.
  unfold tmr_stop_owned.
  sep_apply (tmr_stop_call_context_unlock_pre external platform critical sg mask
    unlock_context (tmr_stop_kernel unlock_before) PreH15).
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_46 : OSTmrStop_which_implies_wit_46.
Proof.
  unfold OSTmrStop_which_implies_wit_46; left.
  intros Client X before context pooled perr argument opt i p nesting mask domain
    raw_state raw_type effects AppRep callback sg critical platform external ClientRep
    unlock_context unlock_before Hlayout Hunlink_layout Hprofile Haddresses Hints_addr
    Hwheel_addr HAppRep Heffects Hraw_type Hraw_state Hdomain Hbinding Hsource Hprefix Hready.
  subst AppRep effects raw_type raw_state domain.
  unfold tmr_stop_call_post.
  assert (Hreturn :
    TimerCalleeLift.os_sched_unlock_program_post external platform critical sg
      unlock_context mask (tmr_stop_kernel unlock_before) tmr_stop_call_kernel_any **
    tmr_stop_client_rep (tmr_stop_call_application_rep ClientRep pooled p nesting)
      perr unlock_before |--
    tmr_stop_post (tmr_stop_call_application_rep ClientRep pooled p nesting)
      external platform critical sg (tmr_stop_call_effects callback) mask perr
      pooled p i opt argument tmr_stop_call_raw_type tmr_stop_call_raw_state
      context before 1 X).
  { intros heap [kernel_heap [client_heap [Hjoin [Hpost Hclient]]]].
    destruct (TimerCalleeLift.os_sched_unlock_program_post_closed_return
      external platform critical sg unlock_context mask (tmr_stop_kernel unlock_before)
      tmr_stop_call_kernel_any Hready kernel_heap Hpost)
      as [returned [kernel [[Hcall Hany] Hcontext]]].
    assert (Hunlock : tmr_stop_unlock_program external critical sg
      (tmr_stop_call_effects callback) unlock_context unlock_before returned
      (tmr_stop_set_kernel kernel unlock_before)).
    { split; [exact Hcall|apply tmr_stop_call_unlock_application]. }
    assert (Howned : tmr_stop_owned
      (tmr_stop_call_application_rep ClientRep pooled p nesting)
      external platform critical sg mask perr returned
      (tmr_stop_set_kernel kernel unlock_before) heap).
    { exists kernel_heap, client_heap; split; [exact Hjoin|].
      split; [exact Hcontext|exact Hclient]. }
    destruct Hprefix as [state_read [stopped [request [selected
      [Hstateprefix [Hunlink [Hselect Hcallback]]]]]]].
    destruct Hstateprefix as [observed [locked
      [Hpointer [Htype [Hints [Hlock Hstate]]]]]].
    eapply tmr_stop_running_return_post;
      [exact Hpointer|exact Htype|exact Hints|exact Hlock|exact Hstate|
       exact Hunlink|exact Hselect|exact Hcallback|exact Hunlock|
       exact (proj2 Hsource)|exact Howned]. }
  sep_apply (tmr_stop_call_callback_resources_emp
    (tmr_stop_call_application_rep ClientRep pooled p nesting)
    external platform critical sg (tmr_stop_call_effects callback) mask perr
    (tmr_stop_call_callback_domain critical sg (tmr_stop_call_effects callback)
      pooled p i opt argument tmr_stop_call_raw_type tmr_stop_call_raw_state context before)
    pooled p i opt argument tmr_stop_call_raw_type tmr_stop_call_raw_state context before).
  sep_apply Hreturn.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_47 : OSTmrStop_which_implies_wit_47.
Proof.
  left.
  intros Client X before context pooled perr arg opt i p nesting mask domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep locked status Hlayout Hunlink Hprofile Haddrs Hints Hwheel Happ Heffects Hraw_type Hraw_state Hdomain Hbinding Hsource Hprefix Hstatus.
  assert (Hrestore :
    tmr_stop_call_read_cell p StopStateField status **
    tmr_stop_call_read_rest AppRep external platform critical sg mask perr false context locked p StopStateField status
    |-- tmr_stop_entry_owned AppRep external platform critical sg mask perr context locked).
  { intros heap [field_heap [rest_heap [Hjoin [Hfield Hrest]]]].
    apply (Hrest field_heap heap).
    - exact (TmrStopRules.join_comm field_heap rest_heap heap Hjoin).
    - exact Hfield. }
  cbn [tmr_stop_call_read_cell] in Hrestore.
  unfold tmr_unlink_timer_field in Hrestore.
  sep_apply_l_atomic Hrestore.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_48 : OSTmrStop_which_implies_wit_48.
Proof.
  left. intros Client X before context pooled perr argument opt i p nesting mask
    domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep.
  intros.
  assert (Hready : tmr_stop_unlock_ready external critical sg context locked).
  { eapply (tmr_stop_call_requirements_nonrunning external critical sg effects
      pooled p i opt argument raw_type raw_state context before status locked).
    - exact (proj1 PreH13).
    - exact PreH14.
    - unfold tmr_stop_call_stopped_status in PreH15. lia. }
  sep_apply (tmr_stop_call_unlock_pre_open AppRep external platform critical sg mask perr context locked Hready).
  unfold tmr_stop_call_unlock_pre, tmr_stop_call_kernel_any.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_49 : OSTmrStop_which_implies_wit_49.
Proof.
  left. intros Client X before context pooled perr argument opt i p nesting mask
    domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep.
  intros.
  assert (Hready : tmr_stop_unlock_ready external critical sg context locked).
  { eapply (tmr_stop_call_requirements_nonrunning external critical sg effects
      pooled p i opt argument raw_type raw_state context before status locked).
    - exact (proj1 PreH13).
    - exact PreH14.
    - unfold tmr_stop_call_stopped_status in PreH15. lia. }
  sep_apply (TimerCalleeLift.os_sched_unlock_program_post_closed_return external platform
    critical sg context mask (tmr_stop_kernel locked) tmr_stop_call_kernel_any Hready).
  Intros returned kernel.
  assert (Hstep : tmr_stop_call_unlock_step external critical sg effects context locked
    returned (tmr_stop_set_kernel kernel locked)).
  { split; [tauto|]. rewrite PreH8. apply tmr_stop_call_unlock_application. }
  Exists returned (tmr_stop_set_kernel kernel locked).
  unfold tmr_stop_entry_owned, tmr_stop_context_rep.
  cbn [tmr_stop_set_kernel tmr_stop_kernel tmr_stop_entry_client_rep tmr_stop_application].
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_50 : OSTmrStop_which_implies_wit_50.
Proof.
  left; intros.
  unfold tmr_stop_entry_owned, tmr_stop_entry_client_rep, tmr_stop_call_output_frame.
  cbn [tmr_stop_set_error tmr_stop_kernel tmr_stop_error tmr_stop_application].
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_51 : OSTmrStop_which_implies_wit_51.
Proof.
  left; intros.
  unfold tmr_stop_owned, tmr_stop_client_rep, tmr_stop_call_output_frame.
  cbn [tmr_stop_set_error tmr_stop_kernel tmr_stop_error tmr_stop_application].
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_52 : OSTmrStop_which_implies_wit_52.
Proof.
  left.
  intros Client X before context pooled perr arg opt i p nesting mask domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep locked status Hlayout Hunlink Hprofile Haddrs Hints Hwheel Happ Heffects Hraw_type Hraw_state Hdomain Hbinding Hsource Hprefix Hstatus.
  assert (Hrestore :
    tmr_stop_call_read_cell p StopStateField status **
    tmr_stop_call_read_rest AppRep external platform critical sg mask perr false context locked p StopStateField status
    |-- tmr_stop_entry_owned AppRep external platform critical sg mask perr context locked).
  { intros heap [field_heap [rest_heap [Hjoin [Hfield Hrest]]]].
    apply (Hrest field_heap heap).
    - exact (TmrStopRules.join_comm field_heap rest_heap heap Hjoin).
    - exact Hfield. }
  cbn [tmr_stop_call_read_cell] in Hrestore.
  unfold tmr_unlink_timer_field in Hrestore.
  sep_apply_l_atomic Hrestore.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_53 : OSTmrStop_which_implies_wit_53.
Proof.
  left. intros Client X before context pooled perr argument opt i p nesting mask
    domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep.
  intros.
  assert (Hready : tmr_stop_unlock_ready external critical sg context locked).
  { eapply (tmr_stop_call_requirements_nonrunning external critical sg effects
      pooled p i opt argument raw_type raw_state context before status locked).
    - exact (proj1 PreH13).
    - exact PreH14.
    - lia. }
  sep_apply (tmr_stop_call_unlock_pre_open AppRep external platform critical sg mask perr context locked Hready).
  unfold tmr_stop_call_unlock_pre, tmr_stop_call_kernel_any.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_54 : OSTmrStop_which_implies_wit_54.
Proof.
  left. intros Client X before context pooled perr argument opt i p nesting mask
    domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep.
  intros.
  assert (Hready : tmr_stop_unlock_ready external critical sg context locked).
  { eapply (tmr_stop_call_requirements_nonrunning external critical sg effects
      pooled p i opt argument raw_type raw_state context before status locked).
    - exact (proj1 PreH13).
    - exact PreH14.
    - lia. }
  sep_apply (TimerCalleeLift.os_sched_unlock_program_post_closed_return external platform
    critical sg context mask (tmr_stop_kernel locked) tmr_stop_call_kernel_any Hready).
  Intros returned kernel.
  assert (Hstep : tmr_stop_call_unlock_step external critical sg effects context locked
    returned (tmr_stop_set_kernel kernel locked)).
  { split; [tauto|]. rewrite PreH8. apply tmr_stop_call_unlock_application. }
  Exists returned (tmr_stop_set_kernel kernel locked).
  unfold tmr_stop_entry_owned, tmr_stop_context_rep.
  cbn [tmr_stop_set_kernel tmr_stop_kernel tmr_stop_entry_client_rep tmr_stop_application].
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_55 : OSTmrStop_which_implies_wit_55.
Proof.
  left; intros.
  unfold tmr_stop_entry_owned, tmr_stop_entry_client_rep, tmr_stop_call_output_frame.
  cbn [tmr_stop_set_error tmr_stop_kernel tmr_stop_error tmr_stop_application].
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_56 : OSTmrStop_which_implies_wit_56.
Proof.
  left; intros.
  unfold tmr_stop_owned, tmr_stop_client_rep, tmr_stop_call_output_frame.
  cbn [tmr_stop_set_error tmr_stop_kernel tmr_stop_error tmr_stop_application].
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_57 : OSTmrStop_which_implies_wit_57.
Proof.
  left; intros.
  unfold tmr_stop_owned, tmr_stop_client_rep, tmr_stop_call_output_frame.
  cbn [tmr_stop_set_error tmr_stop_kernel tmr_stop_error tmr_stop_application].
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_58 : OSTmrStop_which_implies_wit_58.
Proof.
  left; intros.
  unfold tmr_stop_entry_owned, tmr_stop_entry_client_rep, tmr_stop_call_output_frame.
  cbn [tmr_stop_set_error tmr_stop_kernel tmr_stop_error tmr_stop_application].
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_59 : OSTmrStop_which_implies_wit_59.
Proof.
  left. intros Client X before context pooled perr argument opt i p nesting mask
    domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep.
  intros.
  assert (Hready : tmr_stop_unlock_ready external critical sg context locked).
  { eapply (tmr_stop_call_requirements_nonrunning external critical sg effects
      pooled p i opt argument raw_type raw_state context before status locked).
    - exact (proj1 PreH13).
    - exact PreH14.
    - exact PreH18. }
  sep_apply (TimerCalleeLift.os_sched_unlock_program_post_closed_return external platform
    critical sg context mask (tmr_stop_kernel locked) tmr_stop_call_kernel_any Hready).
  Intros returned kernel.
  assert (Hstep : tmr_stop_call_unlock_step external critical sg effects context locked
    returned (tmr_stop_set_kernel kernel locked)).
  { split; [tauto|]. rewrite PreH8. apply tmr_stop_call_unlock_application. }
  Exists returned (tmr_stop_set_kernel kernel locked).
  unfold tmr_stop_entry_owned, tmr_stop_context_rep.
  cbn [tmr_stop_set_kernel tmr_stop_kernel tmr_stop_entry_client_rep tmr_stop_application].
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_60 : OSTmrStop_which_implies_wit_60.
Proof.
  left. intros Client X before context pooled perr argument opt i p nesting mask
    domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep.
  intros.
  assert (Hready : tmr_stop_unlock_ready external critical sg context locked).
  { eapply (tmr_stop_call_requirements_nonrunning external critical sg effects
      pooled p i opt argument raw_type raw_state context before status locked).
    - exact (proj1 PreH13).
    - exact PreH14.
    - exact PreH18. }
  sep_apply (tmr_stop_call_unlock_pre_open AppRep external platform critical sg mask perr context locked Hready).
  unfold tmr_stop_call_unlock_pre, tmr_stop_call_kernel_any.
  entailer!.
Qed.

Lemma proof_of_OSTmrStop_which_implies_wit_61 : OSTmrStop_which_implies_wit_61.
Proof.
  left.
  intros Client X before context pooled perr arg opt i p nesting mask domain raw_state raw_type effects AppRep callback sg critical platform external ClientRep locked status Hlayout Hunlink Hprofile Haddrs Hints Hwheel Happ Heffects Hraw_type Hraw_state Hdomain Hbinding Hsource Hprefix Hzero Hone Htwo Hthree.
  assert (Hrestore :
    tmr_stop_call_read_cell p StopStateField status **
    tmr_stop_call_read_rest AppRep external platform critical sg mask perr false context locked p StopStateField status
    |-- tmr_stop_entry_owned AppRep external platform critical sg mask perr context locked).
  { intros heap [field_heap [rest_heap [Hjoin [Hfield Hrest]]]].
    apply (Hrest field_heap heap).
    - exact (TmrStopRules.join_comm field_heap rest_heap heap Hjoin).
    - exact Hfield. }
  cbn [tmr_stop_call_read_cell] in Hrestore.
  unfold tmr_unlink_timer_field in Hrestore.
  sep_apply_l_atomic Hrestore.
  entailer!.
Qed.

