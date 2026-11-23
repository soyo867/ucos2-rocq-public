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
From Ucos2Verify.VC.code.timer Require Import tmr_remain_get_goal.
From Ucos2Verify.VC.code.timer Require Import tmr_remain_get_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_remain_get_spec.
               Import UCOS2_C_Rules.
               Local Open Scope sac_scope.
Local Open Scope sac.

Lemma proof_of_OSTmrRemainGet_entail_wit_1 : OSTmrRemainGet_entail_wit_1.
Proof.
  left; intros.
  pose proof PreH1 as (Htype & Hstate & Hoption & Hdelay & Hperiod & Hmatch).
  unfold tmr_remain_get_ready, tmr_remain_get_payload,
    tmr_remain_get_payload_fields, tmr_remain_get_observe.
  unfold tmr_remain_get_state, tmr_remain_get_match,
    tmr_remain_get_time_address in *.
  rewrite Hstate, Hmatch, PreH24, PreH21, PreH2.
  cbn [Z.eqb Pos.eqb].
  unfold kernel_u32, unsigned_last_nbits.
  entailer!.
Qed.

Lemma proof_of_OSTmrRemainGet_entail_wit_2_1 : OSTmrRemainGet_entail_wit_2_1.
Proof.
  left; intros.
  pose proof PreH1 as (Htype & Hstate & Hoption & Hdelay & Hperiod & Hmatch).
  unfold tmr_remain_get_ready, tmr_remain_get_payload,
    tmr_remain_get_payload_fields, tmr_remain_get_observe.
  unfold tmr_remain_get_state, tmr_remain_get_option,
    tmr_remain_get_delay, tmr_remain_get_period in *.
  rewrite Hstate, Hoption, Hdelay, Hperiod, PreH25, PreH6, PreH2, PreH3.
  cbn [Z.eqb Pos.eqb andb].
  entailer!.
Qed.

Lemma proof_of_OSTmrRemainGet_entail_wit_2_2 : OSTmrRemainGet_entail_wit_2_2.
Proof.
  left; intros.
  pose proof PreH2 as (Htype & Hstate & Hoption & Hdelay & Hperiod & Hmatch).
  unfold tmr_remain_get_ready, tmr_remain_get_payload,
    tmr_remain_get_payload_fields, tmr_remain_get_period_storage,
    tmr_remain_get_observe.
  unfold tmr_remain_get_state, tmr_remain_get_option, tmr_remain_get_delay in *.
  rewrite Hstate, Hoption, Hdelay, PreH22, PreH3, <- PreH30,
    (proj2 (Z.eqb_neq _ _) PreH1).
  cbn [Z.eqb Pos.eqb andb].
  entailer!.
Qed.

Lemma proof_of_OSTmrRemainGet_entail_wit_3_1 : OSTmrRemainGet_entail_wit_3_1.
Proof.
  left; intros.
  pose proof PreH1 as (Htype & Hstate & Hoption & Hdelay & Hperiod & Hmatch).
  unfold tmr_remain_get_ready, tmr_remain_get_payload,
    tmr_remain_get_payload_fields, tmr_remain_get_period_storage,
    tmr_remain_get_observe.
  unfold tmr_remain_get_state, tmr_remain_get_option, tmr_remain_get_delay in *.
  rewrite Hstate, Hoption, Hdelay, PreH21, PreH2, <- PreH30.
  cbn [Z.eqb Pos.eqb andb].
  entailer!.
Qed.

Lemma proof_of_OSTmrRemainGet_entail_wit_3_2 : OSTmrRemainGet_entail_wit_3_2.
Proof.
  left; intros.
  pose proof PreH1 as (Htype & Hstate & Hoption & Hdelay & Hperiod & Hmatch).
  unfold tmr_remain_get_ready, tmr_remain_get_payload,
    tmr_remain_get_payload_fields, tmr_remain_get_period_storage,
    tmr_remain_get_observe.
  unfold tmr_remain_get_state, tmr_remain_get_option, tmr_remain_get_delay in *.
  assert (Hnotperiodic : Z.eqb (timerImageOption current) 2 = false)
    by (apply Z.eqb_neq; lia).
  rewrite Hstate, Hoption, Hdelay, PreH21, PreH2, Hnotperiodic.
  cbn [Z.eqb Pos.eqb andb].
  entailer!.
Qed.

Lemma proof_of_OSTmrRemainGet_entail_wit_4_1 : OSTmrRemainGet_entail_wit_4_1.
Proof.
  left; intros; eapply tmr_remain_get_post_after_unlock; eassumption.
Qed.

Lemma proof_of_OSTmrRemainGet_entail_wit_4_2 : OSTmrRemainGet_entail_wit_4_2.
Proof.
  left; intros; eapply tmr_remain_get_post_after_unlock; eassumption.
Qed.

Lemma proof_of_OSTmrRemainGet_entail_wit_5 : OSTmrRemainGet_entail_wit_5.
Proof.
  left; intros.
  pose proof PreH1 as (Htype & Hstate & Hoption & Hdelay & Hperiod & Hmatch).
  unfold tmr_remain_get_ready, tmr_remain_get_observe.
  unfold tmr_remain_get_state in *.
  rewrite Hstate, PreH19, <- PreH27.
  cbn [Z.eqb Pos.eqb]; entailer!.
Qed.

Lemma proof_of_OSTmrRemainGet_entail_wit_6 : OSTmrRemainGet_entail_wit_6.
Proof.
  left; intros.
  pose proof PreH1 as (Htype & Hstate & Hoption & Hdelay & Hperiod & Hmatch).
  unfold tmr_remain_get_ready, tmr_remain_get_observe.
  unfold tmr_remain_get_state in *.
  rewrite Hstate, PreH19, <- PreH28.
  cbn [Z.eqb Pos.eqb]; entailer!.
Qed.

Lemma proof_of_OSTmrRemainGet_entail_wit_7 : OSTmrRemainGet_entail_wit_7.
Proof.
  left; intros.
  pose proof PreH1 as (Htype & Hstate & Hoption & Hdelay & Hperiod & Hmatch).
  unfold tmr_remain_get_ready, tmr_remain_get_observe.
  unfold tmr_remain_get_state in *.
  assert (Hr : Z.eqb (timerImageState current) 3 = false) by (apply Z.eqb_neq; lia).
  assert (Hs : Z.eqb (timerImageState current) 1 = false) by (apply Z.eqb_neq; lia).
  assert (Hc : Z.eqb (timerImageState current) 2 = false) by (apply Z.eqb_neq; lia).
  assert (Hu : Z.eqb (timerImageState current) 0 = false) by (apply Z.eqb_neq; lia).
  rewrite Hstate, PreH19, Hr, Hs, Hc, Hu; entailer!.
Qed.

Lemma proof_of_OSTmrRemainGet_return_wit_1 : OSTmrRemainGet_return_wit_1.
Proof.
  left; intros; eapply tmr_remain_get_post_after_unlock; eassumption.
Qed.

Lemma proof_of_OSTmrRemainGet_return_wit_2 : OSTmrRemainGet_return_wit_2.
Proof.
  left; intros; eapply tmr_remain_get_post_after_unlock; eassumption.
Qed.

Lemma proof_of_OSTmrRemainGet_return_wit_3 : OSTmrRemainGet_return_wit_3.
Proof.
  left; intros; eapply tmr_remain_get_post_after_unlock; eassumption.
Qed.

Lemma proof_of_OSTmrRemainGet_return_wit_5 : OSTmrRemainGet_return_wit_5.
Proof.
  left; intros; eapply tmr_remain_get_post_after_unlock; eassumption.
Qed.

Lemma proof_of_OSTmrRemainGet_return_wit_6 : OSTmrRemainGet_return_wit_6.
Proof.
  unfold OSTmrRemainGet_return_wit_6; left; intros.
  pose proof PreH8 as (Htype & Hlayout).
  rewrite Htype, PreH14, PreH12; unfold tmr_remain_get_int_address.
  sep_apply (proj2 (tmr_remain_get_entry_rep_equiv__entry_refresh
    external critical sg context raw p ty original i before PreH9 PreH3)).
  assert (Hcalls : tmr_remain_get_calls p ty (tmr_remain_get_ints before) = false).
  { unfold tmr_remain_get_calls; rewrite PreH2,
      (proj2 (Z.eqb_neq p 0) PreH3),
      (proj2 (Z.ltb_lt 0 (tmr_remain_get_ints before)) ltac:(lia)); reflexivity. }
  assert (Heffect : tmr_remain_get_effect external critical sg context raw p ty original i
    before (0, 139) context before).
  { unfold tmr_remain_get_effect; rewrite (proj2 (Z.eqb_neq p 0) PreH3), PreH2,
      (proj2 (Z.ltb_lt 0 (tmr_remain_get_ints before)) ltac:(lia)); simpl; auto. }
  pose proof (tmr_remain_get_program_safe_return external critical sg context raw p ty original i
    before (0, 139) context before X Heffect PreH17) as Hsafe.
  unfold tmr_remain_get_post; Exists (0, 139) context before.
  unfold tmr_remain_get_call_resources; rewrite Hcalls; simpl; entailer!.
Qed.

Lemma proof_of_OSTmrRemainGet_return_wit_7 : OSTmrRemainGet_return_wit_7.
Proof.
  unfold OSTmrRemainGet_return_wit_7; left; intros.
  pose proof PreH7 as (Htype & Hlayout).
  rewrite Htype, PreH13, PreH11; unfold tmr_remain_get_int_address.
  sep_apply (proj2 (tmr_remain_get_entry_rep_equiv__entry_refresh
    external critical sg context raw p ty original i before PreH8 PreH2)).
  assert (Hcalls : tmr_remain_get_calls p ty (tmr_remain_get_ints before) = false).
  { unfold tmr_remain_get_calls; rewrite (proj2 (Z.eqb_neq p 0) PreH2),
      (proj2 (Z.eqb_neq ty 100) PreH1); reflexivity. }
  assert (Heffect : tmr_remain_get_effect external critical sg context raw p ty original i
    before (0, 137) context before).
  { unfold tmr_remain_get_effect; rewrite (proj2 (Z.eqb_neq p 0) PreH2),
      (proj2 (Z.eqb_neq ty 100) PreH1); simpl; auto. }
  pose proof (tmr_remain_get_program_safe_return external critical sg context raw p ty original i
    before (0, 137) context before X Heffect PreH16) as Hsafe.
  unfold tmr_remain_get_post; Exists (0, 137) context before.
  unfold tmr_remain_get_call_resources; rewrite Hcalls; simpl; entailer!.
Qed.

Lemma proof_of_OSTmrRemainGet_return_wit_8 : OSTmrRemainGet_return_wit_8.
Proof.
  unfold OSTmrRemainGet_return_wit_8; left; intros.
  subst ptmr_pre error_addr; subst p.
  assert (Heffect : tmr_remain_get_effect external critical sg context raw 0 ty original i
    before (0, 138) context before).
  { unfold tmr_remain_get_effect; simpl; auto. }
  pose proof (tmr_remain_get_program_safe_return external critical sg context raw 0 ty original i
    before (0, 138) context before X Heffect PreH8) as Hsafe.
  unfold tmr_remain_get_input; Intros.
  unfold tmr_remain_get_post; Exists (0, 138) context before.
  unfold tmr_remain_get_call_resources, tmr_remain_get_calls; simpl; entailer!.
Qed.

Lemma proof_of_OSTmrRemainGet_partial_solve_wit_3_pure : OSTmrRemainGet_partial_solve_wit_3_pure.
Proof.
  unfold OSTmrRemainGet_partial_solve_wit_3_pure; left; intros.
  unfold os_sched_unlock_global_addresses, os_sched_global_addresses in PreH21.
  unfold os_sched_lock_global_addresses; entailer!; tauto.
Qed.

Lemma proof_of_OSTmrRemainGet_which_implies_wit_1 : OSTmrRemainGet_which_implies_wit_1.
Proof.
  unfold OSTmrRemainGet_which_implies_wit_1; left; intros.
  pose proof PreH2 as (Htype & Hlayout).
  unfold tmr_remain_get_input; Intros.
  sep_apply (proj1 (tmr_remain_get_entry_rep_equiv__entry_refresh
    external critical sg context raw p ty original i before H PreH1)).
  prop_apply_p (store_uchar_range p ty).
  prop_apply_p (store_uchar_range sg.(g_OSIntNesting) (tmr_remain_get_ints before)).
  rewrite Htype in PreH2 |- *.
  rewrite PreH3; unfold tmr_remain_get_int_address; entailer!.
Qed.

Lemma proof_of_OSTmrRemainGet_which_implies_wit_2 : OSTmrRemainGet_which_implies_wit_2.
Proof.
  unfold OSTmrRemainGet_which_implies_wit_2; left; intros.
  pose proof PreH5 as (Htype & Hlayout).
  rewrite Htype in PreH5 |- *.
  rewrite PreH4; unfold tmr_remain_get_int_address.
  sep_apply (proj2 (tmr_remain_get_entry_rep_equiv__entry_refresh
    external critical sg context raw p ty original i before PreH6 PreH1)).
  unfold tmr_remain_get_call_resources.
  rewrite (tmr_remain_get_calls_passed p ty (tmr_remain_get_ints before) PreH1 PreH2 PreH3).
  rewrite os_sched_lock_pre_closed_equiv, tmr_remain_get_closed_rep.
  pose proof (proj1 PreH6) as Hinv; entailer!.
Qed.

Lemma proof_of_OSTmrRemainGet_which_implies_wit_3 : OSTmrRemainGet_which_implies_wit_3.
Proof.
  unfold OSTmrRemainGet_which_implies_wit_3; left; intros.
  pose proof PreH4 as (Htype & Hstate & Hlayout).
  pose proof PreH5 as (Hbefore & Henabled & Hnames & Hconfigured & Hprotocol).
  pose proof (tmr_remain_get_calls_passed p ty (tmr_remain_get_ints before)
    PreH1 PreH2 PreH3) as Hcalls.
  rewrite os_sched_lock_post_closed_equiv.
  Intros acquired locked.
  destruct H as (Hcall & Hlocked).
  rewrite tmr_remain_get_closed_rep.
  assert (Hcurrent : exists current,
    tmr_remain_get_image_binding raw original i locked current /\
    (raw = false -> timer_api_initialized locked.(TimerState) /\ p = timer_pool_addr sg i)).
  { destruct raw.
    - exists original; split; [reflexivity|discriminate].
    - specialize (Hconfigured PreH1 eq_refl).
      destruct Hconfigured as (Hinit & Haddr & Himage & Hty).
      destruct (tmr_remain_get_lock_has_current_image critical sg
        context.(os_sched_call_invocation) before acquired locked i original Hinit Himage Hcall)
        as (Hinit_locked & current & Himage_locked).
      exists current; split; [exact Himage_locked|auto]. }
  destruct Hcurrent as (current & Himage & Hpool).
  sep_apply (tmr_remain_get_current_rep__entry_refresh sg raw p ty (tmr_remain_get_ints before)
    original i locked current PreH1 Hcalls Henabled Hnames Hlocked Himage Hpool).
  sep_apply (tmr_remain_get_payload_ranges__entry_refresh sg p current locked).
  Intros.
  Exists acquired locked current.
  assert (Hfacts : tmr_remain_get_locked_facts external critical sg context raw p ty
    original i before acquired locked current).
  { unfold tmr_remain_get_locked_facts.
    split; [exact PreH5|]. split; [exact PreH1|]. split; [exact PreH2|].
    split; [exact PreH3|]. split; [exact Hcall|]. split; [exact Hlocked|].
    split; [exact Himage|]. split; [intros Hraw; exact (proj1 (Hpool Hraw))|exact H]. }
  rewrite Hstate in PreH4 |- *.
  unfold tmr_remain_get_state; entailer!.
Qed.

Lemma proof_of_OSTmrRemainGet_which_implies_wit_4 : OSTmrRemainGet_which_implies_wit_4.
Proof.
  left; intros.
  unfold tmr_remain_get_layout in *.
  pose proof PreH1 as (Htype & Hstate & Hoption & Hdelay & Hperiod & Hmatch).
  unfold tmr_remain_get_payload, tmr_remain_get_payload_fields,
    tmr_remain_get_state, tmr_remain_get_match, tmr_remain_get_time_address in *.
  rewrite Hmatch, PreH2, PreH3; cbn [Z.eqb Pos.eqb]; entailer!.
Qed.

Lemma proof_of_OSTmrRemainGet_which_implies_wit_5 : OSTmrRemainGet_which_implies_wit_5.
Proof.
  left; intros; apply tmr_remain_get_ready_unlock_pre__unlock_return.
Qed.

Lemma proof_of_OSTmrRemainGet_which_implies_wit_6 : OSTmrRemainGet_which_implies_wit_6.
Proof.
  left; intros.
  unfold tmr_remain_get_layout in *.
  pose proof PreH1 as (Htype & Hstate & Hoption & Hdelay & Hperiod & Hmatch).
  unfold tmr_remain_get_payload, tmr_remain_get_payload_fields,
    tmr_remain_get_period_storage, tmr_remain_get_state,
    tmr_remain_get_option, tmr_remain_get_delay in *.
  rewrite Hoption, Hdelay, PreH2; cbn [Z.eqb Pos.eqb]; entailer!.
Qed.

Lemma proof_of_OSTmrRemainGet_which_implies_wit_7 : OSTmrRemainGet_which_implies_wit_7.
Proof.
  left; intros.
  unfold tmr_remain_get_layout in *.
  pose proof PreH1 as (Htype & Hstate & Hoption & Hdelay & Hperiod & Hmatch).
  unfold tmr_remain_get_period_storage, tmr_remain_get_option,
    tmr_remain_get_delay, tmr_remain_get_period in *.
  rewrite Hperiod, PreH2, PreH3; cbn [Z.eqb Pos.eqb andb]; entailer!.
Qed.

Lemma proof_of_OSTmrRemainGet_which_implies_wit_8 : OSTmrRemainGet_which_implies_wit_8.
Proof.
  left; intros; apply tmr_remain_get_ready_unlock_pre__unlock_return.
Qed.

Lemma proof_of_OSTmrRemainGet_which_implies_wit_9 : OSTmrRemainGet_which_implies_wit_9.
Proof.
  left; intros; apply tmr_remain_get_ready_unlock_pre__unlock_return.
Qed.

Lemma proof_of_OSTmrRemainGet_which_implies_wit_10 : OSTmrRemainGet_which_implies_wit_10.
Proof.
  left; intros; apply tmr_remain_get_ready_unlock_pre__unlock_return.
Qed.

Lemma proof_of_OSTmrRemainGet_which_implies_wit_11 : OSTmrRemainGet_which_implies_wit_11.
Proof.
  left; intros; apply tmr_remain_get_ready_unlock_pre__unlock_return.
Qed.

Lemma proof_of_OSTmrRemainGet_which_implies_wit_12 : OSTmrRemainGet_which_implies_wit_12.
Proof.
  left; intros; apply tmr_remain_get_ready_unlock_pre__unlock_return.
Qed.

