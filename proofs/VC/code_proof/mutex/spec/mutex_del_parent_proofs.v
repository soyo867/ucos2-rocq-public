Require Import Coq.ZArith.ZArith Coq.micromega.Lia Coq.Lists.List.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.lib.field_storage.
Require Export Ucos2Verify.lib.mutex.
Require Export Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.event_wait.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma mutex_del_parent_packed_count : forall ceiling low,
  0 <= ceiling < 256 -> 0 <= low < 256 ->
  0 <= ceiling * 256 + low <= 65535 /\
  Z.shiftr (ceiling * 256 + low) 8 = ceiling.
Proof.
  intros ceiling low Hceiling Hlow; split; [lia|].
  rewrite Z.shiftr_div_pow2 by lia.
  change ((ceiling * 256 + low) / 256 = ceiling).
  rewrite Z.add_comm, Z.div_add by lia.
  rewrite Z.div_small by lia; lia.
Qed.

Lemma mutex_del_parent_event_core_split : forall sg state eid event,
  mutex_query_lookup state eid event ->
  UCOS2_raw_rep sg state |--
    (event_pool_addr sg eid + 0) # UChar |-> encode_event_type event.(eventType) **
    (event_pool_addr sg eid + 4) # Ptr |-> encode_event_ptr_value sg event **
    (event_pool_addr sg eid + 8) # UShort |-> encode_event_cnt_value event **
    (event_pool_addr sg eid + 10) # UChar |-> encode_event_wait_grp event.(waitList) state.(TskState) **
    sg.(g_OSEventFreeList) # Ptr |-> event_encode_pool_link sg (hd_error state.(EventState).(unUsedEventStates)) **
    mutex_del_parent_event_rest sg state eid event.
Proof.
  intros sg state eid event He.
  sep_apply_l_atomic (mutex_del_raw_split_event sg state eid event He).
  unfold event_storage_rep, mutex_del_parent_event_rest.
  pose proof (EventFieldStorage.store_fields_split_field EventField (option Z) EventField_eq_dec
    (event_cell (event_pool_addr sg eid)) (event_fields sg.(osKernelConfig).(cfgEventNames))
    (event_image sg state.(TskState) event) EventTypeField
    (event_fields_nodup _) ltac:(unfold event_fields; simpl; tauto)) as Htype.
  sep_apply_l_atomic Htype.
  pose proof (EventFieldStorage.store_fields_split_field EventField (option Z) EventField_eq_dec
    (event_cell (event_pool_addr sg eid))
    (remove EventField_eq_dec EventTypeField (event_fields sg.(osKernelConfig).(cfgEventNames)))
    (event_image sg state.(TskState) event) EventPtrField
    ltac:(destruct sg.(osKernelConfig).(cfgEventNames); simpl; repeat constructor; simpl; intuition discriminate)
    ltac:(unfold event_fields; simpl; tauto)) as Hptr.
  sep_apply_l_atomic Hptr.
  pose proof (EventFieldStorage.store_fields_split_field EventField (option Z) EventField_eq_dec
    (event_cell (event_pool_addr sg eid))
    (remove EventField_eq_dec EventPtrField (remove EventField_eq_dec EventTypeField
      (event_fields sg.(osKernelConfig).(cfgEventNames))))
    (event_image sg state.(TskState) event) EventCntField
    ltac:(destruct sg.(osKernelConfig).(cfgEventNames); simpl; repeat constructor; simpl; intuition discriminate)
    ltac:(unfold event_fields; simpl; tauto)) as Hcnt.
  sep_apply_l_atomic Hcnt.
  pose proof (EventFieldStorage.store_fields_split_field EventField (option Z) EventField_eq_dec
    (event_cell (event_pool_addr sg eid))
    (remove EventField_eq_dec EventCntField (remove EventField_eq_dec EventPtrField
      (remove EventField_eq_dec EventTypeField (event_fields sg.(osKernelConfig).(cfgEventNames)))))
    (event_image sg state.(TskState) event) EventGrpField
    ltac:(destruct sg.(osKernelConfig).(cfgEventNames); simpl; repeat constructor; simpl; intuition discriminate)
    ltac:(unfold event_fields; simpl; tauto)) as Hgrp.
  sep_apply_l_atomic Hgrp.
  cbn [event_cell event_image event_field_offset]; entailer!.
Qed.

Lemma mutex_del_parent_event_core_merge : forall sg state eid event,
  mutex_query_lookup state eid event ->
    (event_pool_addr sg eid + 0) # UChar |-> encode_event_type event.(eventType) **
    (event_pool_addr sg eid + 4) # Ptr |-> encode_event_ptr_value sg event **
    (event_pool_addr sg eid + 8) # UShort |-> encode_event_cnt_value event **
    (event_pool_addr sg eid + 10) # UChar |-> encode_event_wait_grp event.(waitList) state.(TskState) **
    sg.(g_OSEventFreeList) # Ptr |-> event_encode_pool_link sg (hd_error state.(EventState).(unUsedEventStates)) **
    mutex_del_parent_event_rest sg state eid event |-- UCOS2_raw_rep sg state.
Proof.
  intros sg state eid event He.
  unfold mutex_del_parent_event_rest.
  pose proof (EventFieldStorage.store_fields_merge_field EventField (option Z) EventField_eq_dec
    (event_cell (event_pool_addr sg eid))
    (remove EventField_eq_dec EventCntField (remove EventField_eq_dec EventPtrField
      (remove EventField_eq_dec EventTypeField (event_fields sg.(osKernelConfig).(cfgEventNames)))))
    (event_image sg state.(TskState) event) EventGrpField
    ltac:(destruct sg.(osKernelConfig).(cfgEventNames); simpl; repeat constructor; simpl; intuition discriminate)
    ltac:(unfold event_fields; simpl; tauto)) as Hgrp.
  cbn [event_cell event_image event_field_offset] in Hgrp.
  sepcon_right_assoc.
  sep_apply Hgrp.
  pose proof (EventFieldStorage.store_fields_merge_field EventField (option Z) EventField_eq_dec
    (event_cell (event_pool_addr sg eid))
    (remove EventField_eq_dec EventPtrField (remove EventField_eq_dec EventTypeField
      (event_fields sg.(osKernelConfig).(cfgEventNames))))
    (event_image sg state.(TskState) event) EventCntField
    ltac:(destruct sg.(osKernelConfig).(cfgEventNames); simpl; repeat constructor; simpl; intuition discriminate)
    ltac:(unfold event_fields; simpl; tauto)) as Hcnt.
  cbn [event_cell event_image event_field_offset] in Hcnt; sep_apply Hcnt.
  pose proof (EventFieldStorage.store_fields_merge_field EventField (option Z) EventField_eq_dec
    (event_cell (event_pool_addr sg eid))
    (remove EventField_eq_dec EventTypeField (event_fields sg.(osKernelConfig).(cfgEventNames)))
    (event_image sg state.(TskState) event) EventPtrField
    ltac:(destruct sg.(osKernelConfig).(cfgEventNames); simpl; repeat constructor; simpl; intuition discriminate)
    ltac:(unfold event_fields; simpl; tauto)) as Hptr.
  cbn [event_cell event_image event_field_offset] in Hptr; sep_apply Hptr.
  pose proof (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
    (event_pool_addr sg eid) (event_image sg state.(TskState) event) EventTypeField
    ltac:(unfold event_fields; simpl; tauto)) as Htype.
  cbn [event_cell event_image event_field_offset] in Htype.
  unfold event_storage_without_field in Htype; sep_apply Htype.
  sep_apply_l_atomic (mutex_del_raw_merge_event sg state eid event He); entailer!.
Qed.

Lemma mutex_del_parent_count_decode : forall sg eid entry event mutex,
  mutex_del_parent_entry sg eid entry event mutex ->
  0 <= mutex.(mfPCP) < 256 /\
  0 <= encode_event_cnt_value event <= 65535 /\
  Z.shiftr (encode_event_cnt_value event) 8 = mutex.(mfPCP).
Proof.
  intros sg eid entry event mutex [Hvalid [He [Ht [Hm Hu]]]].
  pose proof Hvalid as [Hprofile [_ [_ [_ [Hcross _]]]]].
  destruct Hcross as [_ [_ [_ [Hprotocol _]]]].
  destruct (Hprotocol eid event mutex He Ht Hm) as [Hpcp [Hshape Hslot]].
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  assert (Hrange : 0 <= mutex.(mfPCP) < 256).
  { unfold valid_mutex_pcp, task_priority_in_range in Hpcp.
    rewrite Hlowest, Hdisabled in Hpcp; lia. }
  split; [exact Hrange|].
  unfold encode_event_cnt_value; rewrite Ht, Hm.
  destruct mutex.(mfOwner) as [owner|] eqn:Ho;
    destruct mutex.(mfOwnerOrigPrio) as [original|] eqn:Horig;
    simpl in Hshape |- *; try contradiction.
  - destruct Hshape as [Horig_range _].
    apply mutex_del_parent_packed_count; [exact Hrange|].
    unfold task_priority_in_range in Horig_range; rewrite Hlowest in Horig_range; lia.
  - apply mutex_del_parent_packed_count; [exact Hrange|lia].
Qed.

Lemma mutex_del_parent_cast_count : forall sg eid entry event mutex,
  mutex_del_parent_entry sg eid entry event mutex ->
  unsigned_last_nbits (Z.shiftr (encode_event_cnt_value event) 8) 8 =
    Z.shiftr (encode_event_cnt_value event) 8.
Proof.
  intros sg eid entry event mutex Hentry.
  destruct (mutex_del_parent_count_decode sg eid entry event mutex Hentry) as [Hr [_ Heq]].
  apply unsigned_last_nbits_eq; rewrite Heq; change (0 <= mutex.(mfPCP) < 256); exact Hr.
Qed.

Lemma mutex_del_parent_enabled_ceiling_in_range : forall sg eid entry ceiling,
  mutex_del_parent_ceiling_at sg eid entry ceiling -> ceiling <> 255 ->
  0 <= ceiling < 64.
Proof.
  intros sg eid entry ceiling [event [mutex [Hentry Hceiling]]] Hdisabled.
  destruct (mutex_del_parent_count_decode sg eid entry event mutex Hentry)
    as [_ [_ Hdecode]].
  rewrite Hdecode in Hceiling; subst ceiling.
  destruct Hentry as [Hvalid [He [Ht [Hm _]]]].
  pose proof Hvalid as [Hprofile [_ [_ [_ [Hcross _]]]]].
  destruct Hcross as [_ [_ [_ [Hprotocol _]]]].
  destruct (Hprotocol eid event mutex He Ht Hm) as [Hpcp _].
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  assert (Hdis : sg.(osPrioMutexCeilDis) = 255)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  unfold valid_mutex_pcp, task_priority_in_range in Hpcp;
    rewrite Hlowest, Hdis in Hpcp; lia.
Qed.

Lemma mutex_del_parent_loop_count_decode : forall sg eid entry prepared state original event mutex priorities,
  mutex_del_parent_loop_facts sg eid entry prepared state original event mutex priorities ->
  0 <= encode_event_cnt_value event <= 65535 /\
  Z.shiftr (encode_event_cnt_value event) 8 = mutex.(mfPCP) /\
  unsigned_last_nbits (Z.shiftr (encode_event_cnt_value event) 8) 8 =
    Z.shiftr (encode_event_cnt_value event) 8.
Proof.
  intros sg eid entry prepared state original event mutex priorities
    [Hentry [Hprepare [Hprefix [Hphase He]]]].
  destruct (mutex_del_parent_count_decode sg eid entry original mutex Hentry)
    as [Hpcp [Hrange Hdecode]].
  pose proof (mutex_del_parent_cast_count sg eid entry original mutex Hentry) as Hcast.
  destruct Hentry as [_ [_ [Ht [Hm _]]]].
  destruct Hphase as [phase_event [Hp [Hpt [Hpm _]]]].
  unfold mutex_query_lookup in He; rewrite He in Hp; injection Hp as Hp; subst phase_event.
  assert (Hcount : encode_event_cnt_value event = encode_event_cnt_value original).
  { unfold encode_event_cnt_value; rewrite Hpt, Hpm, Ht, Hm; reflexivity. }
  rewrite Hcount; auto.
Qed.

Lemma mutex_del_parent_loop_enabled_ceiling : forall sg eid entry prepared state original event mutex priorities ceiling,
  mutex_del_parent_loop_facts sg eid entry prepared state original event mutex priorities ->
  mutex_del_parent_ceiling mutex ceiling -> ceiling <> 255 ->
  0 <= ceiling < 64 /\ state.(TskState).(prioTbl) ceiling = PTFree.
Proof.
  intros sg eid entry prepared state original event mutex priorities ceiling
    [Hentry [_ [_ [Hphase _]]]] Hceiling Hneq.
  unfold mutex_del_parent_ceiling in Hceiling; subst ceiling.
  assert (Hca : mutex_del_parent_ceiling_at sg eid entry mutex.(mfPCP)).
  { exists original, mutex; split; [exact Hentry|].
    destruct (mutex_del_parent_count_decode sg eid entry original mutex Hentry) as [_ [_ Hdecode]];
      symmetry; exact Hdecode. }
  split; [eapply mutex_del_parent_enabled_ceiling_in_range; eauto|].
  pose proof Hentry as [[Hprofile _] _].
  assert (Hdis : sg.(osPrioMutexCeilDis) = 255)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  destruct Hphase as [phase_event [_ [_ [_ [[Hdisabled _]|[_ [Hclear _]]]]]]];
    [congruence|exact Hclear].
Qed.

Lemma mutex_del_parent_group_cast : forall sg state waiters,
  UCOS2_state_inv sg state ->
  unsigned_last_nbits (encode_event_wait_grp waiters state.(TskState)) 32 =
    encode_event_wait_grp waiters state.(TskState).
Proof.
  intros sg state waiters [Hprofile [Htasks _]].
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  assert (Hrange : 0 <= encode_ready_grp waiters state.(TskState) < 2 ^ 8).
  { apply encode_ready_grp_in_range; intros tid node Hin Hnode.
    assert (Hp : task_priority_in_range sg node.(curPrio))
      by (unfold task_in_range in Htasks; intuition eauto).
    unfold task_priority_in_range in Hp; rewrite Hlowest in Hp.
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  apply unsigned_last_nbits_eq.
  change (0 <= encode_ready_grp waiters state.(TskState) < 4294967296).
  change (0 <= encode_ready_grp waiters state.(TskState) < 256) in Hrange; lia.
Qed.

Lemma mutex_del_parent_prepare_disabled : forall sg eid entry event mutex,
  mutex_del_parent_entry sg eid entry event mutex -> mutex.(mfPCP) = 255 ->
  UCOS2_raw_rep sg entry |-- mutex_del_parent_prepared sg eid entry entry event mutex.
Proof.
  intros sg eid entry event mutex Hentry Hpcp.
  pose proof Hentry as [Hvalid [He [Ht [Hm _]]]].
  pose proof Hvalid as [Hprofile _].
  assert (Hdisabled : mutex.(mfPCP) = sg.(osPrioMutexCeilDis)).
  { unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; intuition congruence. }
  assert (Hprepare : mutex_del_prepare sg mutex entry entry).
  { unfold mutex_del_prepare; destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis));
      [reflexivity|contradiction]. }
  pose proof (mutex_del_disabled_state_implies_wake_state sg eid mutex entry event
    Hvalid He Ht Hm Hdisabled) as Hphase.
  unfold mutex_del_parent_prepared, mutex_del_wake_rep; entailer!.
Qed.

Lemma mutex_del_parent_prepare_unowned : forall sg eid entry event mutex,
  mutex_del_parent_entry sg eid entry event mutex -> mutex.(mfPCP) <> 255 ->
  encode_event_ptr_value sg event = 0 ->
  mutex_del_released_resources sg entry mutex.(mfPCP) |--
    mutex_del_parent_prepared sg eid entry (mutex_del_released_state entry mutex.(mfPCP)) event mutex.
Proof.
  intros sg eid entry event mutex Hentry Hpcp Hptr.
  pose proof Hentry as [Hvalid [He [Ht [Hm _]]]].
  pose proof Hvalid as [Hprofile [_ [_ [_ [Hcross _]]]]].
  assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  assert (Hnone : mutex.(mfOwner) = None).
  { unfold encode_event_ptr_value in Hptr; rewrite Ht, Hm in Hptr.
    destruct mutex.(mfOwner) as [owner|] eqn:Ho; [|reflexivity].
    destruct Hcross as [_ [Hsnap _]].
    destruct (Hsnap eid event mutex owner He Ht Hm Ho) as [node [base [snapshot [Hnode _]]]].
    pose proof (mutex_del_live_task_pointer_nonzero sg entry owner node Hvalid Hnode); contradiction. }
  assert (Hprepare : mutex_del_prepare sg mutex entry (mutex_del_released_state entry mutex.(mfPCP))).
  { unfold mutex_del_prepare; rewrite Hdisabled, Hnone.
    destruct (Z.eq_dec mutex.(mfPCP) 255); [contradiction|reflexivity]. }
  pose proof (mutex_del_unowned_enabled_establishes_released_state sg entry eid event mutex
    Hvalid He Ht Hm Hnone ltac:(change (mutex.(mfPCP) <> sg.(osPrioMutexCeilDis)); congruence)) as Hreleased.
  pose proof (mutex_del_released_state_implies_wake_state sg eid mutex _ Hreleased) as Hphase.
  rewrite mutex_del_released_resources_raw_equiv.
  unfold mutex_del_parent_prepared, mutex_del_wake_rep; entailer!.
Qed.

Lemma mutex_del_parent_storage_pointer_not_reserved : forall base image value,
  tcb_field_address base TCBStkPtr = base ->
  image TCBStkPtr = Some value ->
  tcb64_storage_rep base image |--
    coq_prop (base <> 1) && tcb64_storage_rep base image.
Proof.
  intros base image value Haddress Himage.
  pose proof (tcb64_storage_split base image TCBStkPtr) as Hsplit.
  pose proof (tcb64_storage_merge base image TCBStkPtr) as Hmerge.
  cbn [tcb_cell] in Hsplit, Hmerge; rewrite Haddress, Himage in Hsplit, Hmerge.
  match goal with |- _ |-- ?Post =>
    match type of Hsplit with _ |-- ?Opened => assert (Hfinish : Opened |-- Post) end
  end.
  { sep_apply_l_atomic (mutex_del_pointer_cell_not_reserved base value).
    Intros; sep_apply_l_atomic Hmerge; entailer!. }
  intros heap Howned; apply (Hfinish heap); exact (Hsplit heap Howned).
Qed.

Lemma mutex_del_parent_owner_from_pointer : forall sg eid entry event mutex owner,
  mutex_del_parent_entry sg eid entry event mutex ->
  task_slot_addr sg owner <> 0 ->
  encode_event_ptr_value sg event = task_slot_addr sg owner ->
  mutex.(mfOwner) = Some owner.
Proof.
  intros sg eid entry event mutex owner [_ [_ [Ht [Hm _]]]] Hnonzero Hpointer.
  unfold encode_event_ptr_value in Hpointer; rewrite Ht, Hm in Hpointer.
  destruct mutex.(mfOwner) as [actual|] eqn:Howner;
    cbn [encode_task_link] in Hpointer; [|congruence].
  apply task_slot_addr_injective in Hpointer; subst actual; reflexivity.
Qed.

Lemma mutex_del_parent_recycle_fields_merge : forall sg state eid event,
  (event_pool_addr sg eid + 0) # UChar |-> 0 **
  (event_pool_addr sg eid + 4) # Ptr |-> event_encode_pool_link sg (hd_error state.(EventState).(unUsedEventStates)) **
  (event_pool_addr sg eid + 8) # UShort |-> 0 **
  (event_pool_addr sg eid + 10) # UChar |-> encode_event_wait_grp event.(waitList) state.(TskState) **
  sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid **
  mutex_del_parent_event_rest sg state eid event |--
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    (event_recycle_image sg state.(EventState).(unUsedEventStates) (event_image sg state.(TskState) event)) **
  sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid ** mutex_del_event_frame sg state eid.
Proof.
  intros sg state eid event; unfold mutex_del_parent_event_rest.
  set (image := event_recycle_image sg state.(EventState).(unUsedEventStates)
    (event_image sg state.(TskState) event)).
  assert (Hrest : EventFieldStorage.store_fields EventField_eq_dec (event_cell (event_pool_addr sg eid))
    (remove EventField_eq_dec EventGrpField (remove EventField_eq_dec EventCntField
      (remove EventField_eq_dec EventPtrField (remove EventField_eq_dec EventTypeField (event_fields sg.(osKernelConfig).(cfgEventNames)))))) image =
    EventFieldStorage.store_fields EventField_eq_dec (event_cell (event_pool_addr sg eid))
    (remove EventField_eq_dec EventGrpField (remove EventField_eq_dec EventCntField
      (remove EventField_eq_dec EventPtrField (remove EventField_eq_dec EventTypeField (event_fields sg.(osKernelConfig).(cfgEventNames))))))
      (event_image sg state.(TskState) event)).
  { unfold image, event_recycle_image, event_write.
    repeat rewrite EventFieldStorage.store_fields_update_unlisted
      by (destruct sg.(osKernelConfig).(cfgEventNames); simpl; intuition discriminate).
    reflexivity. }
  rewrite <- Hrest; sepcon_right_assoc.
  pose proof (EventFieldStorage.store_fields_merge_field EventField (option Z) EventField_eq_dec
    (event_cell (event_pool_addr sg eid))
    (remove EventField_eq_dec EventCntField (remove EventField_eq_dec EventPtrField
      (remove EventField_eq_dec EventTypeField (event_fields sg.(osKernelConfig).(cfgEventNames))))) image EventGrpField
    ltac:(destruct sg.(osKernelConfig).(cfgEventNames); simpl; repeat constructor; simpl; intuition discriminate)
    ltac:(unfold event_fields; simpl; tauto)) as Hgrp.
  change (event_cell (event_pool_addr sg eid) EventGrpField (image EventGrpField)) with
    ((event_pool_addr sg eid + 10) # UChar |-> encode_event_wait_grp event.(waitList) state.(TskState)) in Hgrp.
  sep_apply Hgrp.
  pose proof (EventFieldStorage.store_fields_merge_field EventField (option Z) EventField_eq_dec
    (event_cell (event_pool_addr sg eid))
    (remove EventField_eq_dec EventPtrField (remove EventField_eq_dec EventTypeField (event_fields sg.(osKernelConfig).(cfgEventNames)))) image EventCntField
    ltac:(destruct sg.(osKernelConfig).(cfgEventNames); simpl; repeat constructor; simpl; intuition discriminate)
    ltac:(unfold event_fields; simpl; tauto)) as Hcnt.
  change (event_cell (event_pool_addr sg eid) EventCntField (image EventCntField)) with
    ((event_pool_addr sg eid + 8) # UShort |-> 0) in Hcnt; sep_apply Hcnt.
  pose proof (EventFieldStorage.store_fields_merge_field EventField (option Z) EventField_eq_dec
    (event_cell (event_pool_addr sg eid))
    (remove EventField_eq_dec EventTypeField (event_fields sg.(osKernelConfig).(cfgEventNames))) image EventPtrField
    ltac:(destruct sg.(osKernelConfig).(cfgEventNames); simpl; repeat constructor; simpl; intuition discriminate)
    ltac:(unfold event_fields; simpl; tauto)) as Hptr.
  change (event_cell (event_pool_addr sg eid) EventPtrField (image EventPtrField)) with
    ((event_pool_addr sg eid + 4) # Ptr |-> event_encode_pool_link sg (hd_error state.(EventState).(unUsedEventStates))) in Hptr; sep_apply Hptr.
  pose proof (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
    (event_pool_addr sg eid) image EventTypeField ltac:(unfold event_fields; simpl; tauto)) as Htype.
  change (event_cell (event_pool_addr sg eid) EventTypeField (image EventTypeField)) with
    ((event_pool_addr sg eid + 0) # UChar |-> 0) in Htype.
  unfold event_storage_without_field in Htype; sep_apply Htype; entailer!.
Qed.

Lemma mutex_del_parent_prefix_event_fields : forall sg eid initial priorities final,
  mutex_del_wake_prefix sg eid initial priorities final ->
  forall original current,
  initial.(EventState).(inUsedEventStates) eid = Some original ->
  final.(EventState).(inUsedEventStates) eid = Some current ->
  event_set_wait_list current [] = event_set_wait_list original [].
Proof.
  intros sg eid initial priorities final Hprefix.
  induction Hprefix as [state|state event priority mid priorities after He Hgroup Hstep Htail IH];
    intros original current Horiginal Hcurrent.
  - rewrite Horiginal in Hcurrent; injection Hcurrent as E; subst current; reflexivity.
  - rewrite He in Horiginal; injection Horiginal as E; subst original.
    unfold event_task_rdy in Hstep; rewrite He in Hstep.
    destruct (state.(TskState).(prioTbl) (event_wait_priority state.(TskState) event)) as [| |tid]; try discriminate.
    destruct (state.(TskState).(inUsedTaskStates) tid) as [old|] eqn:Hold; [|discriminate].
    injection Hstep as Ep Em; subst mid.
    assert (Hmid : (event_wake_state sg state eid event tid old PendMutex 0 PendAbort).(EventState).(inUsedEventStates) eid =
      Some (event_set_wait_list event (remove_Z_eqb tid event.(waitList)))).
    { cbn [event_wake_state replace_SchedS replace_EventS replace_TskS EventState update_event_field_raw inUsedEventStates].
      rewrite Z.eqb_refl; reflexivity. }
    specialize (IH _ current Hmid Hcurrent).
    rewrite event_set_wait_list_last_write in IH; exact IH.
Qed.

Lemma mutex_del_parent_recheck_live_fields : forall sg entry eid observed,
  UCOS2_state_inv sg entry -> sem_query_public_slot entry eid observed ->
  event_slot_type_value entry.(EventState) eid = 4 ->
  exists mutex, mutex_query_lookup entry eid observed /\
    observed.(eventType) = OS_EVENT_TYPE_MUTEX /\ observed.(mutexFields) = Some mutex.
Proof.
  intros sg entry eid observed Hvalid [Hlive|[Hnone Hfree]] Htype.
  - unfold event_slot_type_value in Htype.
    pose proof Hlive as Hlookup; unfold mutex_query_lookup in Hlookup; rewrite Hlookup in Htype.
    assert (Hkind : observed.(eventType) = OS_EVENT_TYPE_MUTEX).
    { destruct observed.(eventType); simpl in Htype; try discriminate; reflexivity. }
    destruct Hvalid as [_ [_ [_ [Hevents _]]]].
    destruct Hevents as [_ [_ [_ [Hfields _]]]].
    specialize (Hfields eid observed Hlookup).
    unfold event_fields_consistency in Hfields; rewrite Hkind in Hfields.
    destruct Hfields as [Hsome _]; destruct observed.(mutexFields) as [mutex|] eqn:Hmutex;
      [exists mutex; auto|contradiction].
  - unfold event_slot_type_value in Htype; rewrite Hnone in Htype; discriminate.
Qed.

Lemma mutex_del_parent_program_type_split : forall sg entry eid observed,
  sem_query_public_slot entry eid observed ->
  kernel_program_inv sg entry |--
    coq_prop (UCOS2_state_inv sg entry) &&
    ((event_addr sg eid + OSEventType_off) # UChar |->
      event_slot_type_value entry.(EventState) eid **
     sem_query_type_frame sg entry eid ** unmap_table_rep sg).
Proof.
  intros; rewrite kernel_program_inv_split_unmap.
  sep_apply_l_atomic (sem_query_type_split_full sg entry eid observed H); entailer!.
Qed.

Lemma mutex_del_parent_program_type_merge : forall sg entry eid,
  UCOS2_state_inv sg entry ->
  (event_addr sg eid + OSEventType_off) # UChar |->
    event_slot_type_value entry.(EventState) eid **
  sem_query_type_frame sg entry eid ** unmap_table_rep sg |--
  kernel_program_inv sg entry.
Proof.
  intros; sep_apply_l_atomic (sem_query_type_merge_full sg entry eid H).
  rewrite kernel_program_inv_split_unmap; entailer!.
Qed.

Lemma mutex_del_parent_recheck_error_return : forall external platform critical sg context
  mask saved before entry pe option eid observed,
  mutex_del_parent_prefix_ok pe before eid ->
  mutex_del_parent_save_facts critical sg context.(os_sched_call_invocation)
    mask saved before entry ->
  mutex_del_recheck_observation sg eid entry observed -> observed <> 4 ->
  mutex_del_callsite_unscheduled_post external platform critical sg context mask entry |--
  mutex_del_parent_post external platform critical sg context mask before pe option eid
    pe (encode_os_err_code OS_ERR_EVENT_TYPE).
Proof.
  intros external platform critical sg context mask saved before entry pe option eid observed
    Hprefix [Hinterval _] Hobservation Htype heap Hclosed.
  right; exists entry; split; [|exact Hclosed].
  split; [exact Hprefix|]. split; [exact Hinterval|].
  exists observed; exact (conj Hobservation (conj Htype (conj eq_refl (conj eq_refl eq_refl)))).
Qed.
