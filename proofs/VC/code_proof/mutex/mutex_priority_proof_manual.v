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
From Ucos2Verify.VC.code.mutex Require Import mutex_priority_goal.
From Ucos2Verify.VC.code.mutex Require Import mutex_priority_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Import UCOS2_C_Rules.
Import ucos2_rules_lib.
Local Open Scope sac_scope.
Local Open Scope sac.

Lemma proof_of_OSMutex_BasePrio_entail_wit_1 : OSMutex_BasePrio_entail_wit_1.
Proof.
  right; intros; entailer!.
  left; split; [unfold mutex_priority_no_match; intros; lia | reflexivity].
Qed.

Lemma proof_of_OSMutex_BasePrio_entail_wit_2_1 : OSMutex_BasePrio_entail_wit_2_1.
Proof.
  right; intros; entailer!.
  right; split; [lia |].
  split; [assumption | intros; lia].
Qed.

Lemma proof_of_OSMutex_BasePrio_entail_wit_2_2 : OSMutex_BasePrio_entail_wit_2_2.
Proof.
  right; intros; entailer!.
  destruct PreH11 as [[Hnone Hfallback] | [Hrange [Hmatch Hmax]]].
  - left; split; [| exact Hfallback].
    intros index Hindex.
    destruct (Z.eq_dec index i) as [-> | Hneq]; [exact PreH1 |].
    apply Hnone; lia.
  - right; split; [lia |].
    split; [exact Hmatch |].
    intros index Hindex Hpointer.
    destruct (Z.eq_dec index i) as [-> | Hneq]; [contradiction |].
    apply Hmax; [lia | exact Hpointer].
Qed.

Lemma proof_of_OSMutex_BasePrio_return_wit_1 : OSMutex_BasePrio_return_wit_1.
Proof.
  right; intros.
  assert (i = 64) by lia; subst i.
  unfold mutex_base_priority_result; entailer!.
Qed.

Lemma proof_of_OSMutex_BasePrio_which_implies_wit_1 : OSMutex_BasePrio_which_implies_wit_1.
Proof.
  left; intros.
  pose proof (tcb64_storage_split ptcb image TCBPrio) as Hsplit.
  unfold mutex_priority_fallback in PreH1.
  rewrite PreH1 in Hsplit; exact Hsplit.
Qed.

Lemma proof_of_OSMutex_BasePrio_which_implies_wit_2 : OSMutex_BasePrio_which_implies_wit_2.
Proof.
  left; intros.
  pose proof (tcb64_storage_merge ptcb image TCBPrio) as Hmerge.
  unfold mutex_priority_fallback in PreH1.
  rewrite PreH1 in Hmerge; exact Hmerge.
Qed.

Lemma proof_of_OSMutex_EffectivePrio_entail_wit_1 : OSMutex_EffectivePrio_entail_wit_1.
Proof.
  right; intros; entailer!.
  unfold mutex_priority_no_match; intros; lia.
Qed.

Lemma proof_of_OSMutex_EffectivePrio_entail_wit_2 : OSMutex_EffectivePrio_entail_wit_2.
Proof.
  right; intros; entailer!.
  intros index Hindex.
  destruct (Z.eq_dec index i) as [-> | Hneq]; [exact PreH1 |].
  apply PreH9; lia.
Qed.

Lemma proof_of_OSMutex_EffectivePrio_return_wit_1 : OSMutex_EffectivePrio_return_wit_1.
Proof.
  left; intros.
  assert (i = 64) by lia; subst i.
  pose proof (tcb64_storage_merge ptcb_pre image TCBPrio) as Hmerge.
  unfold mutex_priority_fallback in PreH7.
  rewrite PreH7 in Hmerge.
  cbn [tcb_cell tcb_field_address remove TCBField_eq_dec mutex_priority_unchanged_fields] in Hmerge.
  sep_apply Hmerge; entailer!.
  apply mutex_effective_priority_no_alias; exact PreH8.
Qed.

Lemma proof_of_OSMutex_EffectivePrio_return_wit_2 : OSMutex_EffectivePrio_return_wit_2.
Proof.
  right; intros; entailer!.
  right; split; [lia |].
  split; [exact PreH1 |].
  intros index Hindex Hpointer.
  destruct (Z_le_gt_dec i index) as [Hle | Hlt]; [exact Hle |].
  exfalso; apply (PreH9 index); [lia | exact Hpointer].
Qed.

Lemma proof_of_OSMutex_EffectivePrio_which_implies_wit_1 : OSMutex_EffectivePrio_which_implies_wit_1.
Proof.
  left; intros.
  pose proof (tcb64_storage_split ptcb image TCBPrio) as Hsplit.
  unfold mutex_priority_fallback in PreH1.
  rewrite PreH1 in Hsplit; exact Hsplit.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_safety_wit_3 : OSMutex_RdyAtPrio_safety_wit_3.
Proof.
  left; intros; rewrite !land_seven_eq_mod_eight__priority_encoding.
  pose proof (Z.mod_pos_bound (Z.shiftr prio_pre 3) 8 ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_safety_wit_4 : OSMutex_RdyAtPrio_safety_wit_4.
Proof.
  left; intros; rewrite !land_seven_eq_mod_eight__priority_encoding.
  pose proof (Z.mod_pos_bound (Z.shiftr prio_pre 3) 8 ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_safety_wit_5 : OSMutex_RdyAtPrio_safety_wit_5.
Proof.
  left; intros; rewrite !land_seven_eq_mod_eight__priority_encoding.
  pose proof (Z.mod_pos_bound prio_pre 8 ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_safety_wit_6 : OSMutex_RdyAtPrio_safety_wit_6.
Proof.
  left; intros; rewrite !land_seven_eq_mod_eight__priority_encoding.
  pose proof (Z.mod_pos_bound prio_pre 8 ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_entail_wit_1_1 : OSMutex_RdyAtPrio_entail_wit_1_1.
Proof.
  right; intros.
  assert (Hready : mutex_priority_was_ready rows old_y old_bitx = true).
  { unfold mutex_priority_was_ready.
    apply Z.eqb_neq in PreH2; rewrite PreH2; reflexivity. }
  pose proof (mutex_priority_cleared_row_in_range__ready_bitmap_stages
    rows old_y old_bitx (PreH10 old_y ltac:(lia))) as Hrange.
  rewrite Znth_replace_Znth_Same in PreH1 by lia.
  fold (mutex_priority_cleared_row rows old_y old_bitx) in PreH1.
  rewrite unsigned_last_nbits_eq in PreH1 by lia.
  unfold mutex_priority_removed_rows, mutex_priority_removed_group.
  rewrite Hready, PreH1; cbn [Z.eqb encode_bool].
  rewrite <- byte_land_mask_eq__ready_bitmap_stages by lia.
  unfold mutex_priority_cleared_row in PreH1; rewrite PreH1.
  entailer!.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_entail_wit_1_2 : OSMutex_RdyAtPrio_entail_wit_1_2.
Proof.
  right; intros.
  assert (Hready : mutex_priority_was_ready rows old_y old_bitx = true).
  { unfold mutex_priority_was_ready.
    apply Z.eqb_neq in PreH2; rewrite PreH2; reflexivity. }
  pose proof (mutex_priority_cleared_row_in_range__ready_bitmap_stages
    rows old_y old_bitx (PreH10 old_y ltac:(lia))) as Hrange.
  rewrite Znth_replace_Znth_Same in PreH1 by lia.
  fold (mutex_priority_cleared_row rows old_y old_bitx) in PreH1.
  rewrite unsigned_last_nbits_eq in PreH1 by lia.
  apply Z.eqb_neq in PreH1.
  unfold mutex_priority_removed_rows, mutex_priority_removed_group.
  rewrite Hready, PreH1; cbn [encode_bool].
  entailer!.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_entail_wit_1_3 : OSMutex_RdyAtPrio_entail_wit_1_3.
Proof.
  right; intros.
  assert (Hready : mutex_priority_was_ready rows old_y old_bitx = false).
  { unfold mutex_priority_was_ready; rewrite PreH1; reflexivity. }
  unfold mutex_priority_removed_rows, mutex_priority_removed_group.
  rewrite Hready; cbn [encode_bool].
  entailer!.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_entail_wit_2_1 : OSMutex_RdyAtPrio_entail_wit_2_1.
Proof.
  right; intros.
  destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding
    prio_pre ltac:(lia)) as (Hx & Hy & Hex & Hey).
  rewrite Hex, Hey.
  rewrite !shift_one_unsigned_byte_eq__priority_encoding by assumption.
  unfold tcb_bit_x_of_prio, tcb_bit_y_of_prio, mutex_priority_current.
  destruct (Z.eq_dec ptcb_pre ptcb_pre); [|contradiction].
  entailer!.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_entail_wit_2_2 : OSMutex_RdyAtPrio_entail_wit_2_2.
Proof.
  right; intros.
  destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding
    prio_pre ltac:(lia)) as (Hx & Hy & Hex & Hey).
  rewrite Hex, Hey.
  rewrite !shift_one_unsigned_byte_eq__priority_encoding by assumption.
  unfold tcb_bit_x_of_prio, tcb_bit_y_of_prio, mutex_priority_current.
  destruct (Z.eq_dec ptcb_pre current); [contradiction|].
  entailer!.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_return_wit_1 : OSMutex_RdyAtPrio_return_wit_1.
Proof.
  right; intros.
  assert (Hready : mutex_priority_was_ready rows old_y old_bitx = true).
  { destruct (mutex_priority_was_ready rows old_y old_bitx) eqn:Hready; [reflexivity|].
    rewrite PreH20 in PreH1; discriminate. }
  assert (Hrow : unsigned_last_nbits
    (Znth (tcb_y_of_prio prio_pre) (mutex_priority_removed_rows rows old_y old_bitx) 0) 8 =
    Znth (tcb_y_of_prio prio_pre) (mutex_priority_removed_rows rows old_y old_bitx) 0).
  { apply byte_unsigned_eq__ready_bitmap_stages.
    apply mutex_priority_removed_rows_in_range__ready_bitmap_stages; assumption || lia. }
  assert (Hgroup : unsigned_last_nbits
    (mutex_priority_removed_group rows group old_y old_bitx old_bity) 8 =
    mutex_priority_removed_group rows group old_y old_bitx old_bity).
  { apply byte_unsigned_eq__ready_bitmap_stages,
      mutex_priority_removed_group_in_range__ready_bitmap_stages; lia. }
  assert (Hx : unsigned_last_nbits (tcb_bit_x_of_prio prio_pre) 8 =
    tcb_bit_x_of_prio prio_pre).
  { apply byte_unsigned_eq__ready_bitmap_stages.
    unfold tcb_bit_x_of_prio; apply single_bit_in_byte_range__ready_bitmap_stages; lia. }
  assert (Hy : unsigned_last_nbits (tcb_bit_y_of_prio prio_pre) 8 =
    tcb_bit_y_of_prio prio_pre).
  { apply byte_unsigned_eq__ready_bitmap_stages.
    unfold tcb_bit_y_of_prio; apply single_bit_in_byte_range__ready_bitmap_stages; lia. }
  rewrite Hrow, Hgroup, Hx, Hy.
  unfold mutex_priority_rows, mutex_priority_group.
  rewrite Hready.
  unfold mutex_priority_removed_group, ready_group_after_relocation.
  rewrite Hready.
  entailer!.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_return_wit_2 : OSMutex_RdyAtPrio_return_wit_2.
Proof.
  right; intros.
  assert (Hready : mutex_priority_was_ready rows old_y old_bitx = false).
  { destruct (mutex_priority_was_ready rows old_y old_bitx) eqn:Hready; [|reflexivity].
    rewrite PreH20 in PreH1; contradiction. }
  unfold mutex_priority_removed_rows, mutex_priority_removed_group,
    mutex_priority_rows, mutex_priority_group.
  rewrite Hready.
  entailer!.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_which_implies_wit_1 : OSMutex_RdyAtPrio_which_implies_wit_1.
Proof.
  left; intros.
  destruct PreH1 as (Hp & Hx & Hy & Hbx & Hby).
  unfold tcb64_storage_rep, mutex_priority_tcb_rest,
    tcb_fields, mutex_priority_unchanged_fields.
  cbn [tcb64_fields_rep].
  sep_apply_l_atomic (tcb64_fields_rep_split tcb_fields ptcb image TCBPrio
    ltac:(cbn; repeat constructor; simpl; intuition discriminate)
    ltac:(cbn; tauto)).
  sep_apply_l_atomic (tcb64_fields_rep_split
    (remove TCBField_eq_dec TCBPrio tcb_fields) ptcb image TCBX
    ltac:(cbn; repeat constructor; simpl; intuition discriminate)
    ltac:(cbn; tauto)).
  sep_apply_l_atomic (tcb64_fields_rep_split
    (remove TCBField_eq_dec TCBX (remove TCBField_eq_dec TCBPrio tcb_fields))
    ptcb image TCBY
    ltac:(cbn; repeat constructor; simpl; intuition discriminate)
    ltac:(cbn; tauto)).
  sep_apply_l_atomic (tcb64_fields_rep_split
    (remove TCBField_eq_dec TCBY
      (remove TCBField_eq_dec TCBX (remove TCBField_eq_dec TCBPrio tcb_fields)))
    ptcb image TCBBitX
    ltac:(cbn; repeat constructor; simpl; intuition discriminate)
    ltac:(cbn; tauto)).
  sep_apply_l_atomic (tcb64_fields_rep_split
    (remove TCBField_eq_dec TCBBitX
      (remove TCBField_eq_dec TCBY
        (remove TCBField_eq_dec TCBX (remove TCBField_eq_dec TCBPrio tcb_fields))))
    ptcb image TCBBitY
    ltac:(cbn; repeat constructor; simpl; intuition discriminate)
    ltac:(cbn; tauto)).
  rewrite Hp, Hx, Hy, Hbx, Hby.
  sepcon_assoc_change.
  sepcon_lift (tcb64_fields_rep ptcb
    (remove TCBField_eq_dec TCBBitY
      (remove TCBField_eq_dec TCBBitX
        (remove TCBField_eq_dec TCBY
          (remove TCBField_eq_dec TCBX
            (remove TCBField_eq_dec TCBPrio tcb_fields))))) image).
  sepcon_lift (&(ptcb # "os_tcb" ->ₛ "OSTCBPrio") # UChar |-> old_prio).
  sepcon_lift (&(ptcb # "os_tcb" ->ₛ "OSTCBX") # UChar |-> old_x).
  sepcon_lift (&(ptcb # "os_tcb" ->ₛ "OSTCBY") # UChar |-> old_y).
  sepcon_lift (&(ptcb # "os_tcb" ->ₛ "OSTCBBitX") # UChar |-> old_bitx).
  sepcon_lift (&(ptcb # "os_tcb" ->ₛ "OSTCBBitY") # UChar |-> old_bity).
  sepcon_assoc_change.
  cbn [tcb_cell tcb_field_address].
  entailer!.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_which_implies_wit_2 : OSMutex_RdyAtPrio_which_implies_wit_2.
Proof.
  left; intros.
  prop_apply (store_uchar_range (&("OSRdyGrp")) group).
  Intros.
  prop_apply (store_uchar_range (&(ptcb # "os_tcb" ->ₛ "OSTCBBitX")) old_bitx).
  Intros.
  prop_apply (store_uchar_range (&(ptcb # "os_tcb" ->ₛ "OSTCBBitY")) old_bity).
  Intros.
  unfold UCharArray.full, store_array.
  prop_apply uchar_array_rep_implies_forall_byte_range__priority_encoding.
  Intros.
  entailer!.
  all: try (change Byte.max_unsigned with 255 in *; lia).
  intros index Hi.
  match goal with Hall : Forall _ rows |- _ =>
    apply Forall_forall with (x := Znth index rows 0) in Hall; [exact Hall|]
  end.
  unfold Znth; apply nth_In.
  rewrite Zlength_correct in PreH1; lia.
Qed.

Lemma proof_of_OSMutex_RdyAtPrio_which_implies_wit_3 : OSMutex_RdyAtPrio_which_implies_wit_3.
Proof.
  left; intros.
  rewrite <- mutex_priority_reordered_fields.
  assert (Hcons : forall f fields image,
    NoDup (f :: fields) ->
    tcb64_fields_rep ptcb (f :: fields) image --||--
      tcb_cell ptcb f (image f) ** tcb64_fields_rep ptcb fields image).
  { intros; apply TaskFieldStorage.store_fields_cons; assumption. }
  pose proof mutex_priority_reordered_nodup as Hnd.
  pose proof Hnd as Hnd4.
  apply NoDup_cons_iff in Hnd4; destruct Hnd4 as [_ Hnd4].
  pose proof Hnd4 as Hnd3.
  apply NoDup_cons_iff in Hnd3; destruct Hnd3 as [_ Hnd3].
  pose proof Hnd3 as Hnd2.
  apply NoDup_cons_iff in Hnd2; destruct Hnd2 as [_ Hnd2].
  pose proof Hnd2 as Hnd1.
  apply NoDup_cons_iff in Hnd1; destruct Hnd1 as [_ Hnd1].
  rewrite (Hcons _ _ _ Hnd), (Hcons _ _ _ Hnd4),
    (Hcons _ _ _ Hnd3), (Hcons _ _ _ Hnd2), (Hcons _ _ _ Hnd1).
  fold (mutex_priority_tcb_rest ptcb (mutex_priority_image image prio)).
  rewrite mutex_priority_rest_updated.
  change (mutex_priority_image image prio TCBPrio) with (Some prio).
  change (mutex_priority_image image prio TCBX) with (Some (tcb_x_of_prio prio)).
  change (mutex_priority_image image prio TCBY) with (Some (tcb_y_of_prio prio)).
  change (mutex_priority_image image prio TCBBitX) with (Some (tcb_bit_x_of_prio prio)).
  change (mutex_priority_image image prio TCBBitY) with (Some (tcb_bit_y_of_prio prio)).
  cbn [mutex_priority_image tcb_write tcb_cell tcb_field_address].
  entailer!.
Qed.
