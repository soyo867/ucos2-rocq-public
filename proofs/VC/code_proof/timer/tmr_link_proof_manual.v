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
From Ucos2Verify.VC.code.timer Require Import tmr_link_goal.
From Ucos2Verify.VC.code.timer Require Import tmr_link_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_link_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTmr_Link_entail_wit_1_1 : OSTmr_Link_entail_wit_1_1.
Proof.
  right; intros.
  unfold tmr_link_match, kernel_resources.kernel_u32, unsigned_last_nbits.
  cbn [Z.eqb]; entailer!.
Qed.

Lemma proof_of_OSTmr_Link_entail_wit_1_2 : OSTmr_Link_entail_wit_1_2.
Proof.
  right; intros.
  unfold tmr_link_match.
  destruct (Z.eqb type_pre 1);
    unfold kernel_resources.kernel_u32, unsigned_last_nbits;
    cbn [Z.eqb]; entailer!.
Qed.

Lemma proof_of_OSTmr_Link_entail_wit_1_3 : OSTmr_Link_entail_wit_1_3.
Proof.
  right; intros.
  assert (Hkind : Z.eqb type_pre 1 = false) by (apply Z.eqb_neq; lia).
  assert (Hdelay : Z.eqb delay_raw_spec 0 = false) by (apply Z.eqb_neq; assumption).
  unfold tmr_link_match; rewrite Hkind, Hdelay.
  unfold kernel_resources.kernel_u32, unsigned_last_nbits; entailer!.
Qed.

Lemma proof_of_OSTmr_Link_entail_wit_2_1 : OSTmr_Link_entail_wit_2_1.
Proof.
  right; intros; entailer!.
  apply unsigned_last_nbits_eq.
  rewrite Z.rem_mod_nonneg by (pose proof (tmr_link_match_in_range 1 delay_raw_spec period_raw_spec time_raw_spec); lia).
  pose proof (Z.mod_pos_bound (tmr_link_match 1 delay_raw_spec period_raw_spec time_raw_spec) 7 ltac:(lia)).
  change (0 <= (tmr_link_match 1 delay_raw_spec period_raw_spec time_raw_spec) mod 7 < 65536).
  lia.
Qed.

Lemma proof_of_OSTmr_Link_entail_wit_2_2 : OSTmr_Link_entail_wit_2_2.
Proof.
  right; intros; entailer!.
  apply unsigned_last_nbits_eq.
  rewrite Z.rem_mod_nonneg by (pose proof (tmr_link_match_in_range type_pre 0 period_raw_spec time_raw_spec); lia).
  pose proof (Z.mod_pos_bound (tmr_link_match type_pre 0 period_raw_spec time_raw_spec) 7 ltac:(lia)).
  change (0 <= (tmr_link_match type_pre 0 period_raw_spec time_raw_spec) mod 7 < 65536).
  lia.
Qed.

Lemma proof_of_OSTmr_Link_entail_wit_2_3 : OSTmr_Link_entail_wit_2_3.
Proof.
  right; intros; entailer!.
  apply unsigned_last_nbits_eq.
  rewrite Z.rem_mod_nonneg by (pose proof (tmr_link_match_in_range type_pre delay_raw_spec period_raw_spec time_raw_spec); lia).
  pose proof (Z.mod_pos_bound (tmr_link_match type_pre delay_raw_spec period_raw_spec time_raw_spec) 7 ltac:(lia)).
  change (0 <= (tmr_link_match type_pre delay_raw_spec period_raw_spec time_raw_spec) mod 7 < 65536).
  lia.
Qed.

Lemma proof_of_OSTmr_Link_entail_wit_3_1 : OSTmr_Link_entail_wit_3_1.
Proof.
  left; intros.
  unfold tmr_link_wheel_size in *.
  cbn [sizeof_front_end_type sizeof_front_end_type_of_ptr_size].
  rewrite PreH30, PreH12.
  rewrite (Z.mul_comm _ 8).
  entailer!.
Qed.

Lemma proof_of_OSTmr_Link_entail_wit_3_2 : OSTmr_Link_entail_wit_3_2.
Proof.
  left; intros.
  unfold tmr_link_wheel_size in *.
  cbn [sizeof_front_end_type sizeof_front_end_type_of_ptr_size].
  rewrite PreH31, PreH13.
  rewrite (Z.mul_comm _ 8).
  entailer!.
Qed.

Lemma proof_of_OSTmr_Link_entail_wit_3_3 : OSTmr_Link_entail_wit_3_3.
Proof.
  left; intros.
  unfold tmr_link_wheel_size in *.
  cbn [sizeof_front_end_type sizeof_front_end_type_of_ptr_size].
  rewrite PreH31, PreH13.
  rewrite (Z.mul_comm _ 8).
  entailer!.
Qed.

Lemma proof_of_OSTmr_Link_return_wit_1 : OSTmr_Link_return_wit_1.
Proof.
  left; intros; subst first_raw_spec clock_raw_spec.
  unfold tmr_link_raw_post, tmr_link_neighbor_pre, tmr_link_neighbor_post,
    tmr_link_entries, tmr_link_spoke_addr, tmr_link_timer_field, tmr_link_wheel_field.
  destruct (Z.eq_dec 0 0); [|contradiction].
  rewrite Z.rem_mod_nonneg by lia.
  entailer!.
Qed.

Lemma proof_of_OSTmr_Link_return_wit_2 : OSTmr_Link_return_wit_2.
Proof.
  left; intros; subst first_raw_spec clock_raw_spec.
  unfold tmr_link_raw_post, tmr_link_neighbor_pre, tmr_link_neighbor_post,
    tmr_link_entries, tmr_link_spoke_addr, tmr_link_timer_field, tmr_link_wheel_field.
  destruct (Z.eq_dec 0 0); [|contradiction].
  rewrite Z.rem_mod_nonneg by lia.
  entailer!.
Qed.

Lemma proof_of_OSTmr_Link_return_wit_3 : OSTmr_Link_return_wit_3.
Proof.
  left; intros; subst first_raw_spec clock_raw_spec.
  unfold tmr_link_raw_post, tmr_link_neighbor_pre, tmr_link_neighbor_post,
    tmr_link_entries, tmr_link_spoke_addr, tmr_link_timer_field, tmr_link_wheel_field.
  destruct (Z.eq_dec 0 0); [|contradiction].
  rewrite Z.rem_mod_nonneg by lia.
  entailer!.
Qed.

Lemma proof_of_OSTmr_Link_return_wit_4 : OSTmr_Link_return_wit_4.
Proof.
  left; intros; subst clock_raw_spec.
  unfold tmr_link_raw_post, tmr_link_neighbor_post, tmr_link_entries,
    tmr_link_spoke_addr, tmr_link_timer_field, tmr_link_wheel_field.
  destruct (Z.eq_dec first_raw_spec 0); [contradiction|].
  rewrite Z.rem_mod_nonneg by lia.
  unfold unsigned_last_nbits, Ucos2Verify.lib.kernel_resources.kernel_u16.
  entailer!.
Qed.

Lemma proof_of_OSTmr_Link_return_wit_5 : OSTmr_Link_return_wit_5.
Proof.
  left; intros; subst clock_raw_spec.
  unfold tmr_link_raw_post, tmr_link_neighbor_post, tmr_link_entries,
    tmr_link_spoke_addr, tmr_link_timer_field, tmr_link_wheel_field.
  destruct (Z.eq_dec first_raw_spec 0); [contradiction|].
  rewrite Z.rem_mod_nonneg by lia.
  unfold unsigned_last_nbits, Ucos2Verify.lib.kernel_resources.kernel_u16.
  entailer!.
Qed.

Lemma proof_of_OSTmr_Link_return_wit_6 : OSTmr_Link_return_wit_6.
Proof.
  left; intros; subst clock_raw_spec.
  unfold tmr_link_raw_post, tmr_link_neighbor_post, tmr_link_entries,
    tmr_link_spoke_addr, tmr_link_timer_field, tmr_link_wheel_field.
  destruct (Z.eq_dec first_raw_spec 0); [contradiction|].
  rewrite Z.rem_mod_nonneg by lia.
  unfold unsigned_last_nbits, Ucos2Verify.lib.kernel_resources.kernel_u16.
  entailer!.
Qed.

Lemma proof_of_OSTmr_Link_which_implies_wit_1 : OSTmr_Link_which_implies_wit_1.
Proof.
  left; intros; subst clock_raw_spec.
  unfold tmr_link_raw_pre, tmr_link_spoke_addr,
    tmr_link_timer_field, tmr_link_wheel_field.
  rewrite Z.rem_mod_nonneg by
    (pose proof (tmr_link_match_in_range kind_raw_spec delay_raw_spec period_raw_spec time_raw_spec); lia).
  entailer!.
Qed.

Lemma proof_of_OSTmr_Link_which_implies_wit_2 : OSTmr_Link_which_implies_wit_2.
Proof.
  left; intros; unfold tmr_link_neighbor_pre, tmr_link_timer_field.
  destruct (Z.eq_dec first_raw_spec 0); [contradiction|].
  entailer!.
Qed.

Lemma proof_of_OSTmr_Link_derive_configured_spec_by_raw_spec : OSTmr_Link_derive_configured_spec_by_raw_spec.
Proof.
  intros ty p R kind i s sg.
  Intros.
  match goal with H : tmr_link_layout |- _ => rename H into Hlayout end.
  match goal with H : tmr_link_profile sg |- _ => rename H into Hprofile end.
  match goal with H : timer_api_initialized s |- _ => rename H into Hinit end.
  match goal with H : tmr_link_eligible s i |- _ => rename H into Heligible end.
  unfold timer_inv; Intros.
  match goal with H : valid_timer_configuration sg s |- _ => rename H into Hconfig end.
  pose proof Hprofile as [Hen [Hnames [Hcap [Hsize [Hpool Hwheel_region]]]]].
  pose proof (proj1 (timer_initialized_configuration_iff sg s Hen Hinit) Hconfig) as Hvalid.
  rewrite (timer_initialized_configured_rep_eq sg s Hen Hinit).
  destruct Heligible as [t [Ht Hnotrunning]].
  pose proof Hvalid as [_ [Hwheel [Htime [_ [_ [_ [_ [Hused _]]]]]]]].
  destruct (Hused i t Ht) as [Htvalid [_ [_ [old [Hold Himage]]]]].
  assert (Hdelay : timerImageDelay old = timerDelay t) by (rewrite Himage; reflexivity).
  assert (Hperiod : timerImagePeriod old = timerPeriod t) by (rewrite Himage; reflexivity).
  set (m := tmr_link_match kind (timerImageDelay old) (timerImagePeriod old) (timerTime s)).
  assert (Hmatch : m = timerMatch (timer_link_object (timerTime s) (Z.eqb kind 1) t)).
  { unfold m; rewrite Hdelay, Hperiod; reflexivity. }
  assert (Hspoke : timer_spoke (osKernelConfig sg) m = m mod 7).
  { unfold timer_spoke, Ucos2Verify.lib.kernel_resources.kernel_u16; rewrite Hsize.
    apply Z.mod_small; pose proof (Z.mod_pos_bound m 7 ltac:(lia)); lia. }
  set (n := Z.to_nat (m mod 7)).
  set (row := nth n (timerWheel s) nil).
  assert (Hn : (n < List.length (timerWheel s))%nat).
  { unfold n; rewrite <- Hspoke; apply timer_wheel_spoke_index_in_range; [lia|exact Hwheel]. }
  assert (Hrow : nth_error (timerWheel s) n = Some row).
  { unfold row; apply nth_error_nth'; exact Hn. }
  assert (Hnot : ~ In i row).
  { intro Hin; apply (tmr_link_eligible_not_in_wheel sg s i Hvalid).
    - exists t; tauto.
    - unfold timer_wheel_member; eapply timer_wheel_row_member; eauto. }
  pose proof (tmr_link_profile_pool_region sg Hprofile) as Hpool_valid.
  pose proof (timer_wheel_row_pointer_null_iff sg s n row Hpool_valid Hvalid Hrow) as Hnull.
  assert (Hrowimages : forall j, In j row -> exists v, timerImages s j = Some v).
  { intros j Hj.
    destruct (timer_wheel_member_spoke sg s n row j Hwheel Hrow Hj) as [u [Hu _]].
    destruct (Hused j u Hu) as [_ [_ [_ [v [Hv _]]]]]; eauto. }
  destruct (tmr_link_images_fields_split_merge sg (timerImages s) i old m row
    Hlayout Hnames Hold Hnot Hnull Hrowimages) as [F [Hsplit_images Hmerge_images]].
  assert (Hp : 0 < timer_pool_addr sg i /\ timer_pool_addr sg i + 40 <= 4294967296).
  { pose proof (timer_pool_addr_in_range sg i Hpool_valid
      (timer_used_id_in_range sg s i t Hvalid Ht)) as Hr.
    rewrite (tmr_link_profile_object_size sg Hprofile) in Hr; exact Hr. }
  assert (Hneighbor : tmr_link_neighbor_bounds (timer_id_pointer sg row)).
  { unfold tmr_link_neighbor_bounds; intros Hnz.
    destruct row as [|j rest]; [contradiction|].
    pose proof (timer_wheel_row_ids_in_range sg s n (j :: rest) j Hvalid Hrow (or_introl eq_refl)) as Hj.
    pose proof (timer_pool_addr_in_range sg j Hpool_valid Hj) as Hr.
    rewrite (tmr_link_profile_object_size sg Hprofile) in Hr; exact Hr. }
  pose proof (timer_wheel_row_entries_in_range sg s n row ltac:(lia) Hvalid Hrow) as Hentries.
  pose proof (tmr_link_row_entries_increase sg s n row i Hprofile Hvalid Hrow) as Hentries_update.
  assert (Haddr : tmr_link_spoke_addr (g_OSTmrWheelTbl sg) m =
      g_OSTmrWheelTbl sg + 8 * Z.of_nat n).
  { unfold tmr_link_spoke_addr, n; rewrite Z2Nat.id; [reflexivity|apply Z.mod_pos_bound; lia]. }
  pose proof Hlayout as [_ [_ [_ [_ [_ [_ [Hfirst [Hcount Hsizeof]]]]]]]].
  set (Fg := g_OSTmrFreeList sg # Ptr |-> timer_id_pointer sg (timerFree s) **
    g_OSTmrFree sg # UShort |-> timerFreeCount s **
    g_OSTmrUsed sg # UShort |-> timerUsedCount s **
    g_OSTmrSem sg # Ptr |-> timerSem s **
    g_OSTmrSemSignal sg # Ptr |-> timerSignalSem s).
  set (Fw := tmr_link_wheel_without_spoke sg (g_OSTmrWheelTbl sg) (timerWheel s) n).
  set (Rraw := F ** Fw ** Fg ** R).
  set (post := timer_replace_wheel_objects s
    (Ucos2Verify.lib.kernel_resources.kernel_map_set (timerUsed s) i (Some (timer_link_object (timerTime s) (Z.eqb kind 1) t)))
    (timer_wheel_prepend_images sg (timerImages s) i
      (timer_link_image old m (timer_id_pointer sg row)) row)
    (timer_wheel_update (timerWheel s) n (i :: row))).
  assert (Hstep : timer_link sg s i (Z.eqb kind 1) = Some post).
  { unfold timer_link, post; rewrite Ht, Hold; cbn zeta.
    rewrite <- Hmatch, Hspoke; reflexivity. }
  destruct (timer_link_preserves_configuration sg s i t (Z.eqb kind 1) post
    Hen ltac:(lia) Hconfig Hinit Ht Hnotrunning Hstep) as [Hpostvalid Hpostinit].
  assert (Hpost : tmr_link_raw_post (timer_pool_addr sg i) (g_OSTmrWheelTbl sg)
    (g_OSTmrTime sg) kind (timerTime s) (timerImageDelay old) (timerImagePeriod old)
    (timer_id_pointer sg row) (Z.of_nat (List.length row)) Rraw |--
    tmr_link_configured_post sg s i kind ** R).
  { unfold tmr_link_configured_post; Exists post.
    unfold timer_inv; rewrite (timer_initialized_configured_rep_eq sg post Hen Hpostinit).
    entailer!.
    unfold tmr_link_raw_post; fold m.
    rewrite Haddr, Hfirst, Hcount, Hentries_update.
    unfold Rraw, Fw, Fg, post.
    unfold timer_raw_rep, timer_images_rep, timer_globals_rep.
    cbn [timer_replace_wheel_objects timerImages timerWheel timerFree timerFreeCount
      timerUsedCount timerTime timerSem timerSignalSem].
    sepcon_right_assoc.
    sep_apply_l_atomic Hmerge_images.
    pose proof (tmr_link_wheel_merge_updated_spoke sg (timerWheel s) n row (i :: row)
      (g_OSTmrWheelTbl sg) Hrow) as Hmerge_wheel.
    cbn [timer_id_pointer] in Hmerge_wheel.
    sepcon_right_assoc.
    sep_apply_r_atomic Hmerge_wheel.
    entailer!. }
  assert (Hwand : emp |--
    tmr_link_raw_post (timer_pool_addr sg i) (g_OSTmrWheelTbl sg)
      (g_OSTmrTime sg) kind (timerTime s) (timerImageDelay old) (timerImagePeriod old)
      (timer_id_pointer sg row) (Z.of_nat (List.length row)) Rraw -*
      (tmr_link_configured_post sg s i kind ** R)).
  { apply_sepcon_adjoint; sep_apply_r_atomic Hpost; entailer!. }
  Exists (timer_pool_addr sg i) (g_OSTmrWheelTbl sg) (g_OSTmrTime sg) kind
    (timerTime s) (timerImageDelay old) (timerImagePeriod old)
    (timer_id_pointer sg row) (Z.of_nat (List.length row)) Rraw.
  entailer!.
  sep_apply_r_atomic Hwand.
  unfold tmr_link_raw_pre; fold m.
  rewrite Haddr, Hfirst, Hcount.
  unfold timer_raw_rep, timer_images_rep, timer_globals_rep, Rraw, Fw, Fg.
  sep_apply_l_atomic Hsplit_images.
  sep_apply_l_atomic (tmr_link_wheel_split_spoke sg (timerWheel s) n row (g_OSTmrWheelTbl sg) Hrow).
  destruct Htvalid as [Hd [Hper _]].
  rewrite <- Hdelay in Hd; rewrite <- Hperiod in Hper.
  unfold kernel_region_valid in Hwheel_region; cbn in Hwheel_region.
  entailer!.
Qed.
