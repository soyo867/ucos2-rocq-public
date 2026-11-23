Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.VC.code.event.spec.event_pend_multi_join_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

Lemma event_pend_multi_task_fields_remove_nodup : forall fields field,
  NoDup fields -> NoDup (remove TCBLayoutField_eq_dec field fields).
Proof.
  intros fields field Hnodup.
  induction Hnodup as [|head rest Hnot Hnodup IH]; cbn [remove].
  - constructor.
  - destruct (TCBLayoutField_eq_dec field head); [exact IH|].
    constructor; [|exact IH].
    intro Hin; apply in_remove in Hin; tauto.
Qed.

(** Exact configured-cell split. Common image encodings are reused, but the
    owned object is the full Multi/Profile TCB, with its entire residual. *)
Lemma event_pend_multi_task_storage_resume_equiv : forall sg tid task,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = true ->
  sg.(osKernelConfig).(cfgTaskProfile) = true ->
  let tcb := task_slot_addr sg tid in
  used_task_rep sg tid task --||--
  &(tcb # "os_tcb" ->ₛ "OSTCBStatPend") # UChar |->
    event_pend_multi_task_pend_status task **
  event_pend_multi_resume_deferred_cells sg tid task **
  event_pend_multi_tcb_rest sg tid task event_pend_multi_resume_fields.
Proof.
  intros sg tid task Hmulti Hprofile.
  cbn zeta.
  unfold used_task_rep, task_slot_storage_rep, tcb_configured_storage_rep.
  rewrite Hmulti, Hprofile.
  unfold event_pend_multi_tcb_rest, event_pend_multi_resume_fields;
    cbn [fold_right].
  split.
  -
    sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
      (tcb_layout_cell true (task_slot_addr sg tid)) (tcb_configured_fields true true) (task_layout_image sg task) (TCBCommonField TCBBitY)
      ltac:(repeat apply event_pend_multi_task_fields_remove_nodup; apply tcb_configured_fields_nodup) ltac:(simpl; tauto)).
    sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
      (tcb_layout_cell true (task_slot_addr sg tid)) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (tcb_configured_fields true true)) (task_layout_image sg task) (TCBCommonField TCBBitX)
      ltac:(repeat apply event_pend_multi_task_fields_remove_nodup; apply tcb_configured_fields_nodup) ltac:(simpl; tauto)).
    sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
      (tcb_layout_cell true (task_slot_addr sg tid)) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (tcb_configured_fields true true))) (task_layout_image sg task) (TCBCommonField TCBY)
      ltac:(repeat apply event_pend_multi_task_fields_remove_nodup; apply tcb_configured_fields_nodup) ltac:(simpl; tauto)).
    sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
      (tcb_layout_cell true (task_slot_addr sg tid)) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (tcb_configured_fields true true)))) (task_layout_image sg task) (TCBCommonField TCBMsg)
      ltac:(repeat apply event_pend_multi_task_fields_remove_nodup; apply tcb_configured_fields_nodup) ltac:(simpl; tauto)).
    sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
      (tcb_layout_cell true (task_slot_addr sg tid)) (remove TCBLayoutField_eq_dec (TCBCommonField TCBMsg) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (tcb_configured_fields true true))))) (task_layout_image sg task) (TCBEventMultiRdy)
      ltac:(repeat apply event_pend_multi_task_fields_remove_nodup; apply tcb_configured_fields_nodup) ltac:(simpl; tauto)).
    sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
      (tcb_layout_cell true (task_slot_addr sg tid)) (remove TCBLayoutField_eq_dec (TCBEventMultiRdy) (remove TCBLayoutField_eq_dec (TCBCommonField TCBMsg) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (tcb_configured_fields true true)))))) (task_layout_image sg task) (TCBEventMultiPtr)
      ltac:(repeat apply event_pend_multi_task_fields_remove_nodup; apply tcb_configured_fields_nodup) ltac:(simpl; tauto)).
    sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
      (tcb_layout_cell true (task_slot_addr sg tid)) (remove TCBLayoutField_eq_dec (TCBEventMultiPtr) (remove TCBLayoutField_eq_dec (TCBEventMultiRdy) (remove TCBLayoutField_eq_dec (TCBCommonField TCBMsg) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (tcb_configured_fields true true))))))) (task_layout_image sg task) (TCBCommonField TCBStatPend)
      ltac:(repeat apply event_pend_multi_task_fields_remove_nodup; apply tcb_configured_fields_nodup) ltac:(simpl; tauto)).
    sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
      (tcb_layout_cell true (task_slot_addr sg tid)) (remove TCBLayoutField_eq_dec (TCBCommonField TCBStatPend) (remove TCBLayoutField_eq_dec (TCBEventMultiPtr) (remove TCBLayoutField_eq_dec (TCBEventMultiRdy) (remove TCBLayoutField_eq_dec (TCBCommonField TCBMsg) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (tcb_configured_fields true true)))))))) (task_layout_image sg task) (TCBCommonField TCBStat)
      ltac:(repeat apply event_pend_multi_task_fields_remove_nodup; apply tcb_configured_fields_nodup) ltac:(simpl; tauto)).
    unfold event_pend_multi_resume_deferred_cells, event_pend_multi_resume_deferred_without_message,
      event_task_remove_multi_tcb_reads, event_pend_multi_task_pend_status,
      event_pend_multi_task_status, event_pend_multi_task_multi_pointer,
      event_pend_multi_task_ready_pointer, event_pend_multi_task_message.
    cbn [tcb_layout_cell tcb_cell tcb_field_address task_layout_image tcb_layout_image task_tcb64_image tcb_y_of_prio]
; entailer!.
  - unfold event_pend_multi_resume_deferred_cells, event_pend_multi_resume_deferred_without_message,
      event_task_remove_multi_tcb_reads, event_pend_multi_task_pend_status,
      event_pend_multi_task_status, event_pend_multi_task_multi_pointer,
      event_pend_multi_task_ready_pointer, event_pend_multi_task_message.
    sepcon_right_assoc.
    pose proof (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec
      (tcb_layout_cell true (task_slot_addr sg tid)) (remove TCBLayoutField_eq_dec (TCBCommonField TCBStatPend) (remove TCBLayoutField_eq_dec (TCBEventMultiPtr) (remove TCBLayoutField_eq_dec (TCBEventMultiRdy) (remove TCBLayoutField_eq_dec (TCBCommonField TCBMsg) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (tcb_configured_fields true true)))))))) (task_layout_image sg task) (TCBCommonField TCBStat)
      ltac:(repeat apply event_pend_multi_task_fields_remove_nodup; apply tcb_configured_fields_nodup) ltac:(simpl; tauto)) as Hmerge0.
    cbn [tcb_layout_cell tcb_cell tcb_field_address task_layout_image tcb_layout_image task_tcb64_image tcb_y_of_prio] in Hmerge0; unfold tcb_y_of_prio in Hmerge0; sep_apply_l_atomic Hmerge0.
    pose proof (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec
      (tcb_layout_cell true (task_slot_addr sg tid)) (remove TCBLayoutField_eq_dec (TCBEventMultiPtr) (remove TCBLayoutField_eq_dec (TCBEventMultiRdy) (remove TCBLayoutField_eq_dec (TCBCommonField TCBMsg) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (tcb_configured_fields true true))))))) (task_layout_image sg task) (TCBCommonField TCBStatPend)
      ltac:(repeat apply event_pend_multi_task_fields_remove_nodup; apply tcb_configured_fields_nodup) ltac:(simpl; tauto)) as Hmerge1.
    cbn [tcb_layout_cell tcb_cell tcb_field_address task_layout_image tcb_layout_image task_tcb64_image tcb_y_of_prio] in Hmerge1; unfold tcb_y_of_prio in Hmerge1; sep_apply_l_atomic Hmerge1.
    pose proof (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec
      (tcb_layout_cell true (task_slot_addr sg tid)) (remove TCBLayoutField_eq_dec (TCBEventMultiRdy) (remove TCBLayoutField_eq_dec (TCBCommonField TCBMsg) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (tcb_configured_fields true true)))))) (task_layout_image sg task) (TCBEventMultiPtr)
      ltac:(repeat apply event_pend_multi_task_fields_remove_nodup; apply tcb_configured_fields_nodup) ltac:(simpl; tauto)) as Hmerge2.
    cbn [tcb_layout_cell tcb_cell tcb_field_address task_layout_image tcb_layout_image task_tcb64_image tcb_y_of_prio] in Hmerge2; unfold tcb_y_of_prio in Hmerge2; sep_apply_l_atomic Hmerge2.
    pose proof (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec
      (tcb_layout_cell true (task_slot_addr sg tid)) (remove TCBLayoutField_eq_dec (TCBCommonField TCBMsg) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (tcb_configured_fields true true))))) (task_layout_image sg task) (TCBEventMultiRdy)
      ltac:(repeat apply event_pend_multi_task_fields_remove_nodup; apply tcb_configured_fields_nodup) ltac:(simpl; tauto)) as Hmerge3.
    cbn [tcb_layout_cell tcb_cell tcb_field_address task_layout_image tcb_layout_image task_tcb64_image tcb_y_of_prio] in Hmerge3; unfold tcb_y_of_prio in Hmerge3; sep_apply_l_atomic Hmerge3.
    pose proof (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec
      (tcb_layout_cell true (task_slot_addr sg tid)) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (tcb_configured_fields true true)))) (task_layout_image sg task) (TCBCommonField TCBMsg)
      ltac:(repeat apply event_pend_multi_task_fields_remove_nodup; apply tcb_configured_fields_nodup) ltac:(simpl; tauto)) as Hmerge4.
    cbn [tcb_layout_cell tcb_cell tcb_field_address task_layout_image tcb_layout_image task_tcb64_image tcb_y_of_prio] in Hmerge4; unfold tcb_y_of_prio in Hmerge4; sep_apply_l_atomic Hmerge4.
    pose proof (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec
      (tcb_layout_cell true (task_slot_addr sg tid)) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (tcb_configured_fields true true))) (task_layout_image sg task) (TCBCommonField TCBY)
      ltac:(repeat apply event_pend_multi_task_fields_remove_nodup; apply tcb_configured_fields_nodup) ltac:(simpl; tauto)) as Hmerge5.
    cbn [tcb_layout_cell tcb_cell tcb_field_address task_layout_image tcb_layout_image task_tcb64_image tcb_y_of_prio] in Hmerge5; unfold tcb_y_of_prio in Hmerge5; sep_apply_l_atomic Hmerge5.
    pose proof (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec
      (tcb_layout_cell true (task_slot_addr sg tid)) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (tcb_configured_fields true true)) (task_layout_image sg task) (TCBCommonField TCBBitX)
      ltac:(repeat apply event_pend_multi_task_fields_remove_nodup; apply tcb_configured_fields_nodup) ltac:(simpl; tauto)) as Hmerge6.
    cbn [tcb_layout_cell tcb_cell tcb_field_address task_layout_image tcb_layout_image task_tcb64_image tcb_y_of_prio] in Hmerge6; unfold tcb_y_of_prio in Hmerge6; sep_apply_l_atomic Hmerge6.
    pose proof (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec
      (tcb_layout_cell true (task_slot_addr sg tid)) (tcb_configured_fields true true) (task_layout_image sg task) (TCBCommonField TCBBitY)
      ltac:(repeat apply event_pend_multi_task_fields_remove_nodup; apply tcb_configured_fields_nodup) ltac:(simpl; tauto)) as Hmerge7.
    cbn [tcb_layout_cell tcb_cell tcb_field_address task_layout_image tcb_layout_image task_tcb64_image tcb_y_of_prio] in Hmerge7; unfold tcb_y_of_prio in Hmerge7; sep_apply_l_atomic Hmerge7.
    entailer!.
Qed.

Lemma event_pend_multi_task_heap_resume_equiv : forall sg state tid task,
  UCOS2_full_state_inv sg state ->
  event_pend_multi_task_selected sg state tid task ->
  let tcb := task_slot_addr sg tid in
  UCOS2_full_inv sg state --||--
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  &(tcb # "os_tcb" ->ₛ "OSTCBStatPend") # UChar |->
    event_pend_multi_task_pend_status task **
  event_pend_multi_resume_deferred_cells sg tid task **
  event_pend_multi_task_frame sg state tid task event_pend_multi_resume_fields **
  event_raw_rep sg state.(TskState) state.(EventState).
Proof.
  intros sg state tid task Hvalid [Hcurrent [Htask Hrow]].
  cbn zeta.
  pose proof Hvalid as [Hprofile _].
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = true)
    by (unfold full_features_kernel_profile in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = true)
    by (unfold full_features_kernel_profile in Hprofile; tauto).
  unfold event_pend_multi_task_frame; split.
  - unfold UCOS2_full_inv, UCOS2_raw_rep, task_shared_rep; Intros.
    sep_apply_l_atomic (task_public_storage_split_task sg state.(TskState) tid task Htask).
    rewrite (event_pend_multi_task_storage_resume_equiv sg tid task Hmulti Hprofiling).
    unfold event_pend_multi_sched_without_current, sched_raw_rep, sched_physical_rep,
      UCOS2_raw_rep_missing_task_storage_sched_event.
    rewrite Hcurrent; cbn [encode_task_link]; entailer!.
  - sepcon_right_assoc.
    sep_apply_l_atomic (proj2 (event_pend_multi_task_storage_resume_equiv sg tid task Hmulti Hprofiling)).
    sep_apply_l_atomic (task_public_storage_merge_task sg state.(TskState) tid task Htask).
    unfold UCOS2_full_inv, UCOS2_raw_rep, task_shared_rep,
      event_pend_multi_sched_without_current, sched_raw_rep, sched_physical_rep,
      UCOS2_raw_rep_missing_task_storage_sched_event.
    rewrite Hcurrent; cbn [encode_task_link]; entailer!.
Qed.

Lemma event_pend_multi_type_frame_valid_id : forall sg state eid,
  UCOS2_full_state_inv sg state ->
  sem_query_type_frame sg state eid |--
    “ valid_event_id sg eid ” && sem_query_type_frame sg state eid.
Proof.
  intros sg state eid Hvalid.
  pose proof Hvalid as [_ [_ [_ [[Hpool [Hstorage _]] _]]]].
  destruct Hpool as [[Hdistinct [Hfree Hallocated]] Hprivate].
  unfold sem_query_type_frame.
  destruct (state.(EventState).(inUsedEventStates) eid) as [node|] eqn:Hslot.
  - assert (Hpresent : exists value, event_allocated_slots state.(EventState) eid = Some value).
    { unfold event_allocated_slots.
      destruct (state.(EventState).(eventLifecycle).(eventPrivate) eid) as [allocation|];
        [eauto|rewrite Hslot; cbn; eauto]. }
    pose proof (proj1 (Hallocated eid) Hpresent) as Hrange.
    unfold valid_event_id; entailer!; tauto.
  - Intros image.
    assert (Himage : state.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image)
      by assumption.
    assert (Hfreeid : In eid state.(EventState).(unUsedEventStates)).
    { apply (proj1 (proj1 Hstorage eid)); eauto. }
    pose proof (Hfree eid Hfreeid) as Hrange.
    Exists image; unfold valid_event_id; entailer!.
Qed.

Lemma event_pend_multi_type_arrow_merge : forall sg state eid pointer,
  UCOS2_full_state_inv sg state -> event_pend_multi_abi sg ->
  event_pend_multi_event_pointer sg eid pointer ->
  &(pointer # "os_event" ->ₛ "OSEventType") # UChar |->
    event_slot_type_value state.(EventState) eid ** sem_query_type_frame sg state eid |--
  UCOS2_full_inv sg state.
Proof.
  intros sg state eid pointer Hvalid [Htable _] Hpointer.
  sep_apply_l_atomic (event_pend_multi_type_frame_valid_id sg state eid Hvalid); Intros.
  assert (Hid : valid_event_id sg eid) by assumption.
  destruct (Htable eid Hid) as [[Htype _] _].
  unfold event_pend_multi_event_pointer in Hpointer; rewrite Hpointer, Htype.
  sep_apply_l_atomic (event_pend_multi_type_merge sg state eid Hvalid); entailer!.
Qed.
