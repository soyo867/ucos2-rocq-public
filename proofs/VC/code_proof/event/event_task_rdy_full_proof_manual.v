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
From Ucos2Verify.VC.code.event Require Import event_task_rdy_full_goal.
From Ucos2Verify.VC.code.event Require Import event_task_rdy_full_proof_auto_checked.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_full_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
Local Open Scope sac_scope.
Require Import Ucos2Verify.VC.code.event.spec.event_task_remove_spec.
Import Ucos2Verify.lib.ucos2_rules_lib.UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OS_EventTaskRdy_safety_wit_1 : OS_EventTaskRdy_safety_wit_1.
Proof.
left; intros.
  rewrite PreH16, PreH17, Z.shiftl_mul_pow2 by lia.
  rewrite signed_last_nbits_eq by (cbn; lia).
  entailer!.
Qed.

Lemma proof_of_OS_EventTaskRdy_safety_wit_2 : OS_EventTaskRdy_safety_wit_2.
Proof.
left; intros.
  rewrite PreH16.
  rewrite signed_last_nbits_eq by (cbn; lia).
  entailer!.
Qed.

Lemma proof_of_OS_EventTaskRdy_entail_wit_1 : OS_EventTaskRdy_entail_wit_1.
Proof.
right; intros.
  rewrite PreH16, PreH17, Z.shiftl_mul_pow2 by lia.
  rewrite signed_last_nbits_eq by (cbn; lia).
  rewrite unsigned_last_nbits_eq by (cbn; lia).
  pose proof (Z.div_mod (curPrio t) 8 ltac:(lia)) as Hdecode.
  unfold tcb_y_of_prio, tcb_x_of_prio.
  entailer!.
Qed.

Lemma proof_of_OS_EventTaskRdy_entail_wit_3 : OS_EventTaskRdy_entail_wit_3.
Proof.
left; intros.
  prop_apply_p (store_uchar_range (&("OSRdyGrp")) group).
  pureIntros.
  prop_apply_p (store_uchar_range
    ((&("OSRdyTbl")) + tcb_y_of_prio (curPrio t) * sizeof(UCHAR))
    (Znth (tcb_y_of_prio (curPrio t)) rows 0)).
  pureIntros.
  pose proof (store_uint_range (tcb_field_address (task_slot_addr sg tid) TCBDly)
    (dly t)) as Hd.
  cbn [tcb_field_address] in Hd; prop_apply_p Hd; pureIntros.
  change (0 <= group <= 255) in H.
  change (0 <= Znth (tcb_y_of_prio (curPrio t)) rows 0 <= 255) in H0.
  entailer!; lia.
Qed.

Lemma proof_of_OS_EventTaskRdy_entail_wit_4_1 : OS_EventTaskRdy_entail_wit_4_1.
Proof.
left; intros.
  assert (Hbyte : forall shift, 0 <= shift < 8 ->
    unsigned_last_nbits (Z.shiftl 1 shift) 8 = Z.shiftl 1 shift).
  { intros shift Hrange.
    assert (Hcases : shift = 0 \/ shift = 1 \/ shift = 2 \/ shift = 3 \/
      shift = 4 \/ shift = 5 \/ shift = 6 \/ shift = 7) by lia.
    repeat destruct Hcases as [Hcases|Hcases]; subst shift; reflexivity. }
  pose proof (task_status_clear_wait_byte_complement
    (encode_task_status (stat t)) msk_pre ltac:(lia)) as Hstatus.
  rewrite <- Hstatus in PreH3 |- *.
  assert (Hbx : unsigned_last_nbits (tcb_bit_x_of_prio (curPrio t)) 8 =
    tcb_bit_x_of_prio (curPrio t)).
  { unfold tcb_bit_x_of_prio; apply Hbyte; lia. }
  assert (Hby : unsigned_last_nbits (tcb_bit_y_of_prio (curPrio t)) 8 =
    tcb_bit_y_of_prio (curPrio t)).
  { unfold tcb_bit_y_of_prio; apply Hbyte; lia. }
  rewrite Hbx, Hby, PreH10, PreH21.
  unfold event_task_rdy_full_after_single, event_task_rdy_full_ready, event_task_rdy_ready_group, event_task_rdy_ready_rows,
    task_status_is_suspended, task_suspend_mask.
  rewrite PreH3; cbn [Z.eqb negb].
  apply _derivable1_andp_intros; [entailer!; congruence|].
  pose proof (event_task_rdy_full_tcb_merge_updated sg t (task_slot_addr sg tid)
    pmsg_pre msk_pre pend_stat_pre) as Htcb.
  cbn [tcb_cell tcb_field_address] in Htcb.
  rewrite <- Htcb.
  rewrite <- (UCharArray.missing_i_merge_to_full
    (g_OSRdyTbl sg) (tcb_y_of_prio (curPrio t)) 8
    (Z.lor (Znth (tcb_y_of_prio (curPrio t)) rows 0) (tcb_bit_x_of_prio (curPrio t)))
    rows ltac:(lia)).

  destruct (event_task_rdy_full_selection sg tasks events eid e tid t pointers instances PreH16)
    as [_ [_ [Hprio _]]].
  pose proof PreH14 as [Hprofile [Htasks [He [Hlayout [Hcanonical [Hhead [Ht Hmulti]]]]]]].
  pose proof (proj1 Hprofile) as Hsg.
  destruct Htasks as [_ [_ [_ [_ [_ [_ [Hunique _]]]]]]].
  pose proof (event_task_remove_multi_merge_event sg tasks events eid e tid t
    Hsg Hunique Hcanonical Hprio Ht Hlayout ltac:(unfold tcb_y_of_prio in *; lia)) as Hmerge.
  unfold event_task_rdy_full_after_remove.
  rewrite <- Hmerge.
  unfold tcb_y_of_prio.
  rewrite !sizeof_uchar, !Z.mul_1_r; entailer!.
Qed.

Lemma proof_of_OS_EventTaskRdy_entail_wit_4_2 : OS_EventTaskRdy_entail_wit_4_2.
Proof.
left; intros.
  pose proof (task_status_clear_wait_byte_complement
    (encode_task_status (stat t)) msk_pre ltac:(lia)) as Hstatus.
  rewrite <- Hstatus in PreH3 |- *.
  rewrite PreH10, PreH21.
  unfold event_task_rdy_full_after_single, event_task_rdy_full_ready, event_task_rdy_ready_group, event_task_rdy_ready_rows,
    task_status_is_suspended, task_suspend_mask.
  assert (Hguard : Z.eqb (Z.land
    (task_status_clear_wait (encode_task_status (stat t)) msk_pre) 8) 0 = false)
    by (apply Z.eqb_neq; exact PreH3).
  rewrite Hguard; cbn [negb].
  apply _derivable1_andp_intros; [entailer!; congruence|].
  pose proof (event_task_rdy_full_tcb_merge_updated sg t (task_slot_addr sg tid)
    pmsg_pre msk_pre pend_stat_pre) as Htcb.
  cbn [tcb_cell tcb_field_address] in Htcb; rewrite <- Htcb.
  pose proof (UCharArray.missing_i_merge_to_full
    (g_OSRdyTbl sg) (tcb_y_of_prio (curPrio t)) 8
    (Znth (tcb_y_of_prio (curPrio t)) rows 0) rows ltac:(lia)) as Hready.
  rewrite replace_Znth_Znth in Hready; rewrite <- Hready.

  destruct (event_task_rdy_full_selection sg tasks events eid e tid t pointers instances PreH16)
    as [_ [_ [Hprio _]]].
  pose proof PreH14 as [Hprofile [Htasks [He [Hlayout [Hcanonical [Hhead [Ht Hmulti]]]]]]].
  pose proof (proj1 Hprofile) as Hsg.
  destruct Htasks as [_ [_ [_ [_ [_ [_ [Hunique _]]]]]]].
  pose proof (event_task_remove_multi_merge_event sg tasks events eid e tid t
    Hsg Hunique Hcanonical Hprio Ht Hlayout ltac:(unfold tcb_y_of_prio in *; lia)) as Hmerge.
  unfold event_task_rdy_full_after_remove.
  rewrite <- Hmerge.
  unfold tcb_y_of_prio.
  rewrite !sizeof_uchar, !Z.mul_1_r; entailer!.
Qed.

Lemma proof_of_OS_EventTaskRdy_entail_wit_5_1 : OS_EventTaskRdy_entail_wit_5_1.
Proof.
left; intros; unfold event_task_rdy_full_post, event_task_rdy_full_task_image,
    event_task_rdy_full_events, event_task_rdy_full_array; cbn zeta.
  destruct (Z.eq_dec (tcbEventMultiPtr t) 0); [contradiction|].
  apply _derivable1_andp_intros; [entailer!; congruence|].
  pose proof (event_task_rdy_full_multi_merge_updated (task_slot_addr sg tid)
    (event_task_rdy_full_after_remove_image sg t pmsg_pre msk_pre pend_stat_pre)
    0 (event_addr sg eid)) as Hmerge.
  cbn [tcb_layout_cell tcb_cell tcb_field_address event_task_rdy_full_after_remove_image
    event_task_rdy_full_before_remove_image tcb_layout_write field_update
    task_layout_image tcb_layout_image task_tcb64_image] in Hmerge.
  unfold task_multi_fields_rep in Hmerge.
  rewrite <- Hmerge; entailer!.
Qed.

Lemma proof_of_OS_EventTaskRdy_entail_wit_5_2 : OS_EventTaskRdy_entail_wit_5_2.
Proof.
left; intros; unfold event_task_rdy_full_post, event_task_rdy_full_task_image,
    event_task_rdy_full_events; cbn zeta.
  destruct (Z.eq_dec (tcbEventMultiPtr t) 0); [|contradiction].
  apply _derivable1_andp_intros; [entailer!; congruence|].
  pose proof (event_task_rdy_full_multi_merge (task_slot_addr sg tid)
    (event_task_rdy_full_after_remove_image sg t pmsg_pre msk_pre pend_stat_pre)) as Hmerge.
  cbn [tcb_layout_cell tcb_cell tcb_field_address event_task_rdy_full_after_remove_image
    event_task_rdy_full_before_remove_image tcb_layout_write field_update
    task_layout_image tcb_layout_image task_tcb64_image] in Hmerge.
  rewrite <- Hmerge; entailer!.
Qed.

Lemma proof_of_OS_EventTaskRdy_which_implies_wit_1 : OS_EventTaskRdy_which_implies_wit_1.
Proof.
left; intros; unfold event_task_rdy_full_pre.
  Intros_p Hpre; destruct Hpre as [Hentry [Hmask [Hresult Hrows]]].
  destruct (event_task_rdy_full_selection sg tasks events eid e tid t pointers instances Hentry)
    as [Hprio [Howner [Hvalid [Hp [Hy Hx]]]]].
  pose proof (unmap_in_range (encode_event_wait_grp (waitList e) tasks)) as Hyrange.
  pose proof (unmap_in_range (encode_event_wait_tbl_at_or (waitList e) tasks
    (tcb_y_of_prio (curPrio t)))) as Hxrange.
  rewrite Hy in Hyrange; rewrite Hx in Hxrange.
  pose proof Hentry as [_ [_ [He [Hlayout _]]]].
  rewrite PreH1, PreH2.
  sep_apply_l_atomic (event_task_remove_multi_split_event sg tasks events eid e
    (tcb_y_of_prio (curPrio t)) He Hlayout Hyrange).
  entailer!.
Qed.

Lemma proof_of_OS_EventTaskRdy_which_implies_wit_2 : OS_EventTaskRdy_which_implies_wit_2.
Proof.
left; intros; rewrite PreH1.
  prop_apply_p (unmap_index_from_byte
    (&(pevent # "os_event" ->ₛ "OSEventGrp"))
    (encode_event_wait_grp (waitList e) tasks)).
  Intros_p Hbits.
  sep_apply_l_atomic (unmap_table_split_cell sg
    (encode_event_wait_grp (waitList e) tasks) Hbits).
  entailer!.
Qed.

Lemma proof_of_OS_EventTaskRdy_which_implies_wit_3 : OS_EventTaskRdy_which_implies_wit_3.
Proof.
left; intros; rewrite PreH1.
  prop_apply_p (unmap_index_from_byte
    (&(pevent # "os_event" ->ₛ "OSEventGrp"))
    (encode_event_wait_grp (waitList e) tasks)).
  Intros_p Hbits.
  sep_apply_l_atomic (unmap_table_merge_cell sg
    (encode_event_wait_grp (waitList e) tasks) Hbits).
  entailer!.
Qed.

Lemma proof_of_OS_EventTaskRdy_which_implies_wit_4 : OS_EventTaskRdy_which_implies_wit_4.
Proof.
left; intros; rewrite PreH1.
  prop_apply_p (unmap_index_from_byte
    (&(pevent # "os_event" ->ₛ "OSEventTbl") + tcb_y_of_prio (curPrio t) * sizeof(UCHAR))
    (encode_event_wait_tbl_at_or (waitList e) tasks (tcb_y_of_prio (curPrio t)))).
  Intros_p Hbits.
  sep_apply_l_atomic (unmap_table_split_cell sg
    (encode_event_wait_tbl_at_or (waitList e) tasks (tcb_y_of_prio (curPrio t))) Hbits).
  entailer!.
Qed.

Lemma proof_of_OS_EventTaskRdy_which_implies_wit_5 : OS_EventTaskRdy_which_implies_wit_5.
Proof.
left; intros; rewrite PreH1.
  prop_apply_p (unmap_index_from_byte
    (&(pevent # "os_event" ->ₛ "OSEventTbl") + tcb_y_of_prio (curPrio t) * sizeof(UCHAR))
    (encode_event_wait_tbl_at_or (waitList e) tasks (tcb_y_of_prio (curPrio t)))).
  Intros_p Hbits.
  sep_apply_l_atomic (unmap_table_merge_cell sg
    (encode_event_wait_tbl_at_or (waitList e) tasks (tcb_y_of_prio (curPrio t))) Hbits).
  entailer!.
Qed.

Lemma proof_of_OS_EventTaskRdy_which_implies_wit_6 : OS_EventTaskRdy_which_implies_wit_6.
Proof.
right; intros; rewrite PreH1.
  destruct (event_task_rdy_full_selection sg tasks events eid e tid t pointers instances PreH2)
    as [Hprio [Howner [Hvalid [Hp Hcoords]]]].
  apply event_task_rdy_prio_split; assumption.
Qed.

Lemma proof_of_OS_EventTaskRdy_which_implies_wit_7 : OS_EventTaskRdy_which_implies_wit_7.
Proof.
right; intros; rewrite PreH1.
  destruct (event_task_rdy_full_selection sg tasks events eid e tid t pointers instances PreH2)
    as [Hprio [Howner [Hvalid [Hp Hcoords]]]].
  apply event_task_rdy_prio_merge; assumption.
Qed.

Lemma proof_of_OS_EventTaskRdy_which_implies_wit_8 : OS_EventTaskRdy_which_implies_wit_8.
Proof.
left; intros t sg ptcb.
  exact (event_task_rdy_full_tcb_split ptcb (task_layout_image sg t)).
Qed.

Lemma proof_of_OS_EventTaskRdy_which_implies_wit_9 : OS_EventTaskRdy_which_implies_wit_9.
Proof.
right; intros rows t sg Hbase Hy0 Hy8; rewrite Hbase.
  apply UCharArray.full_split_to_missing_i; lia.
Qed.

Lemma proof_of_OS_EventTaskRdy_which_implies_wit_10 : OS_EventTaskRdy_which_implies_wit_10.
Proof.
left; intros.
  unfold event_task_remove_pre.
  sep_apply_l_atomic (store_ptr_undef_store_ptr
    (tcb_field_address ptcb TCBEventPtr) (encode_event_link sg (eventPtr t))).
  rewrite sizeof_uchar, Z.mul_1_r.
  cbn [tcb_field_address]; entailer!; lia.
Qed.

Lemma proof_of_OS_EventTaskRdy_which_implies_wit_11 : OS_EventTaskRdy_which_implies_wit_11.
Proof.
left; intros; unfold event_task_remove_post.
  rewrite sizeof_uchar, Z.mul_1_r.
  cbn [tcb_field_address]; entailer!; lia.
Qed.

Lemma proof_of_OS_EventTaskRdy_which_implies_wit_12 : OS_EventTaskRdy_which_implies_wit_12.
Proof.
left; intros; unfold event_task_rdy_full_after_single; Intros_p Hentry.
  pose proof (proj1 (event_task_rdy_full_selection sg tasks events eid e tid t pointers instances Hentry)) as Hpriority.
  pose proof (event_task_rdy_full_multi_split (task_slot_addr sg tid)
    (event_task_rdy_full_after_remove_image sg t pmsg_pre msk_pre pend_stat_pre)) as Hsplit.
  sep_apply_l_atomic Hsplit.
  cbn [tcb_layout_cell tcb_cell tcb_field_address event_task_rdy_full_after_remove_image
    event_task_rdy_full_before_remove_image tcb_layout_write field_update
    task_layout_image tcb_layout_image task_tcb64_image].
  entailer!.
Qed.

Lemma proof_of_OS_EventTaskRdy_which_implies_wit_13 : OS_EventTaskRdy_which_implies_wit_13.
Proof.
left; intros; unfold event_task_rdy_full_array.
  destruct (Z.eq_dec (tcbEventMultiPtr t) 0); [contradiction|].
  pose proof (event_task_rdy_full_remove_multi_input sg tasks events eid e tid t pointers instances PreH1 PreH2).
  entailer!.
Qed.

Lemma proof_of_OS_EventTaskRdy_which_implies_wit_14 : OS_EventTaskRdy_which_implies_wit_14.
Proof.
left; intros; unfold event_task_remove_multi_post, event_task_remove_multi_tcb_reads,
    tcb_y_of_prio; entailer!.
Qed.

Lemma proof_of_OS_EventTaskRemove_return_wit_1 : OS_EventTaskRemove_return_wit_1.
Proof.
unfold OS_EventTaskRemove_return_wit_1; left.
  intros pevent ptcb group_value row_value bit_y bit_x row Hzero Hlo Hhi.
  unfold event_task_remove_post, event_task_remove_group,
    event_task_remove_cleared.
  cbn [Ucos2Verify.lib.task_storage.tcb_field_address].
  rewrite Hzero, Z.eqb_refl.
  rewrite sizeof_uchar, Z.mul_1_r.
  entailer!.
Qed.

Lemma proof_of_OS_EventTaskRemove_return_wit_2 : OS_EventTaskRemove_return_wit_2.
Proof.
unfold OS_EventTaskRemove_return_wit_2; left.
  intros pevent ptcb group_value row_value bit_y bit_x row Hnonzero Hlo Hhi.
  unfold event_task_remove_post, event_task_remove_group,
    event_task_remove_cleared.
  cbn [Ucos2Verify.lib.task_storage.tcb_field_address].
  assert (Hguard : Z.eqb
    (Z.land row_value (unsigned_last_nbits (Z.lnot bit_x) 8)) 0 = false)
    by (apply Z.eqb_neq; exact Hnonzero).
  rewrite Hguard, sizeof_uchar, Z.mul_1_r.
  entailer!.
Qed.

Lemma proof_of_OS_EventTaskRemove_which_implies_wit_1 : OS_EventTaskRemove_which_implies_wit_1.
Proof.
unfold OS_EventTaskRemove_which_implies_wit_1; left.
  intros group_value row_value bit_y bit_x row pevent ptcb.
  unfold event_task_remove_pre.
  cbn [Ucos2Verify.lib.task_storage.tcb_field_address].
  rewrite sizeof_uchar, Z.mul_1_r.
  entailer!.
Qed.
