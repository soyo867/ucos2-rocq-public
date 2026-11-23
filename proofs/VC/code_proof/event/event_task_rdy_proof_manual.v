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
From Ucos2Verify.VC.code.event Require Import event_task_rdy_goal.
From Ucos2Verify.VC.code.event Require Import event_task_rdy_proof_auto_checked.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
Local Open Scope sac_scope.
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
  unfold event_task_rdy_post, event_task_rdy_ready_group, event_task_rdy_ready_rows,
    task_status_is_suspended, task_suspend_mask.
  rewrite PreH3; cbn [Z.eqb negb].
  apply _derivable1_andp_intros; [entailer!; congruence|].
  pose proof (event_task_rdy_tcb_merge_updated sg t (task_slot_addr sg tid)
    pmsg_pre msk_pre pend_stat_pre) as Htcb.
  cbn [tcb_cell tcb_field_address] in Htcb.
  rewrite <- Htcb.
  rewrite <- (UCharArray.missing_i_merge_to_full
    (g_OSRdyTbl sg) (tcb_y_of_prio (curPrio t)) 8
    (Z.lor (Znth (tcb_y_of_prio (curPrio t)) rows 0) (tcb_bit_x_of_prio (curPrio t)))
    rows ltac:(lia)).
  destruct (event_task_rdy_selection sg tasks eid e tid t PreH16)
    as [_ [_ [Hprio _]]].
  destruct PreH14 as [Hsg [Hlayout [Hmulti [Htasks [Hentry [Hhead Hlookup]]]]]].
  destruct Htasks as [_ [_ [_ [_ [_ [_ [Hunique _]]]]]]].
  pose proof (event_remove_waiter_image_eq sg tasks e tid t Hsg Hunique
    (proj1 Hentry) Hprio Hlookup) as Himage.
  destruct Hlayout as [_ [Hgrp Htbl]].
  unfold OSEventGrp_off, OSEventTbl_off in Hgrp, Htbl.
  rewrite Hgrp, Htbl, Himage.
  rewrite <- (event_task_remove_ecb_merge_updated
    sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg tasks e) (tcb_y_of_prio (curPrio t))
    (encode_event_wait_tbl_at_or (waitList e) tasks (tcb_y_of_prio (curPrio t)))
    (encode_event_wait_grp (waitList e) tasks)
    (tcb_bit_x_of_prio (curPrio t)) (tcb_bit_y_of_prio (curPrio t))
    ltac:(lia) ltac:(reflexivity)).
  rewrite !sizeof_uchar, !Z.mul_1_r; entailer!.
Qed.

Lemma proof_of_OS_EventTaskRdy_entail_wit_4_2 : OS_EventTaskRdy_entail_wit_4_2.
Proof.
  left; intros.
  pose proof (task_status_clear_wait_byte_complement
    (encode_task_status (stat t)) msk_pre ltac:(lia)) as Hstatus.
  rewrite <- Hstatus in PreH3 |- *.
  rewrite PreH10, PreH21.
  unfold event_task_rdy_post, event_task_rdy_ready_group, event_task_rdy_ready_rows,
    task_status_is_suspended, task_suspend_mask.
  assert (Hguard : Z.eqb (Z.land
    (task_status_clear_wait (encode_task_status (stat t)) msk_pre) 8) 0 = false)
    by (apply Z.eqb_neq; exact PreH3).
  rewrite Hguard; cbn [negb].
  apply _derivable1_andp_intros; [entailer!; congruence|].
  pose proof (event_task_rdy_tcb_merge_updated sg t (task_slot_addr sg tid)
    pmsg_pre msk_pre pend_stat_pre) as Htcb.
  cbn [tcb_cell tcb_field_address] in Htcb; rewrite <- Htcb.
  pose proof (UCharArray.missing_i_merge_to_full
    (g_OSRdyTbl sg) (tcb_y_of_prio (curPrio t)) 8
    (Znth (tcb_y_of_prio (curPrio t)) rows 0) rows ltac:(lia)) as Hready.
  rewrite replace_Znth_Znth in Hready; rewrite <- Hready.
  destruct (event_task_rdy_selection sg tasks eid e tid t PreH16)
    as [_ [_ [Hprio _]]].
  destruct PreH14 as [Hsg [Hlayout [Hmulti [Htasks [Hentry [Hhead Hlookup]]]]]].
  destruct Htasks as [_ [_ [_ [_ [_ [_ [Hunique _]]]]]]].
  pose proof (event_remove_waiter_image_eq sg tasks e tid t Hsg Hunique
    (proj1 Hentry) Hprio Hlookup) as Himage.
  destruct Hlayout as [_ [Hgrp Htbl]].
  unfold OSEventGrp_off, OSEventTbl_off in Hgrp, Htbl.
  rewrite Hgrp, Htbl, Himage.
  rewrite <- (event_task_remove_ecb_merge_updated
    sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg tasks e) (tcb_y_of_prio (curPrio t))
    (encode_event_wait_tbl_at_or (waitList e) tasks (tcb_y_of_prio (curPrio t)))
    (encode_event_wait_grp (waitList e) tasks)
    (tcb_bit_x_of_prio (curPrio t)) (tcb_bit_y_of_prio (curPrio t))
    ltac:(lia) ltac:(reflexivity)).
  rewrite !sizeof_uchar, !Z.mul_1_r; entailer!.
Qed.

Lemma proof_of_OS_EventTaskRdy_which_implies_wit_1 : OS_EventTaskRdy_which_implies_wit_1.
Proof.
  left; intros.
  unfold event_task_rdy_pre.
  Intros_p Hpre.
  destruct Hpre as [Hentry [Hmask [Hresult Hrows]]].
  destruct (event_task_rdy_selection sg tasks eid e tid t Hentry)
    as [Hprio [Howner [Hvalid [Hp [Hy Hx]]]]].
  pose proof (unmap_in_range (encode_event_wait_grp (waitList e) tasks)) as Hyrange.
  pose proof (unmap_in_range (encode_event_wait_tbl_at_or (waitList e) tasks
    (tcb_y_of_prio (curPrio t)))) as Hxrange.
  rewrite Hy in Hyrange; rewrite Hx in Hxrange.
  pose proof Hentry as [_ [[_ [Hgroup Htable]] _]].
  unfold event_wait_fields_layout_prop, OSEventGrp_off, OSEventTbl_off in Hgroup, Htable.
  rewrite PreH1, PreH2, Hgroup, Htable.
  change (sizeof(UCHAR)) with 1.
  replace (tcb_y_of_prio (curPrio t) * 1) with (tcb_y_of_prio (curPrio t)) by lia.
  sep_apply_l_atomic (event_task_remove_ecb_split sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_image sg tasks e) (tcb_y_of_prio (curPrio t))
    (encode_event_wait_tbl_at_or (waitList e) tasks (tcb_y_of_prio (curPrio t)))
    (encode_event_wait_grp (waitList e) tasks) Hyrange
    (event_table_image_eq sg tasks e (tcb_y_of_prio (curPrio t)) Hyrange) eq_refl).
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
  destruct (event_task_rdy_selection sg tasks eid e tid t PreH2)
    as [Hprio [Howner [Hvalid [Hp Hcoords]]]].
  apply event_task_rdy_prio_split; assumption.
Qed. 

Lemma proof_of_OS_EventTaskRdy_which_implies_wit_7 : OS_EventTaskRdy_which_implies_wit_7.
Proof.
  right; intros; rewrite PreH1.
  destruct (event_task_rdy_selection sg tasks eid e tid t PreH2)
    as [Hprio [Howner [Hvalid [Hp Hcoords]]]].
  apply event_task_rdy_prio_merge; assumption.
Qed. 

Lemma proof_of_OS_EventTaskRdy_which_implies_wit_8 : OS_EventTaskRdy_which_implies_wit_8.
Proof.
  left; intros t sg ptcb.
  exact (event_task_rdy_tcb_split ptcb (task_tcb64_image sg t)).
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
