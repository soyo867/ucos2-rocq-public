Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_pool Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.sem Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The first actual C read must cover used AND free public ECB storage.
    Only the existing non-Event residual is changed to its fields owner. *)
Definition sem_pend_fields_type_frame sg state eid : Assertion :=
  match state.(EventState).(inUsedEventStates) eid with
  | Some observed =>
      event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
        (event_image sg state.(TskState) observed) EventTypeField **
      event_raw_rep_no_eid sg state.(TskState) state.(EventState) eid **
      UCOS2_fields_raw_rep_missing_module sg state EventModule
  | None => EX image : EventStorage,
      coq_prop (state.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image) &&
      (event_storage_without_field sg.(osKernelConfig).(cfgEventNames)
        (event_addr sg eid) image EventTypeField **
       event_free_storage_without_eid sg state.(EventState) eid **
       @UCOS2_C_Rules.store_map EventID OSEventAbstractState
         (used_event_rep sg state.(TskState)) state.(EventState).(inUsedEventStates) **
       event_free_root_rep sg state.(EventState) **
       UCOS2_fields_raw_rep_missing_module sg state EventModule)
  end.

Lemma sem_pend_fields_type_split : forall sg state eid observed,
  sem_query_public_slot state eid observed ->
  UCOS2_fields_inv sg state |-- coq_prop (UCOS2_state_inv sg state) &&
    ((event_addr sg eid + OSEventType_off) # UChar |->
      event_slot_type_value state.(EventState) eid ** sem_pend_fields_type_frame sg state eid).
Proof.
  intros sg state eid observed [Hused|[Hnone Hfree]].
  - unfold sem_pend_fields_type_frame, event_slot_type_value.
    unfold mutex_query_lookup in Hused; rewrite Hused.
    rewrite (UCOS2_fields_inv_split_module sg state EventModule ltac:(discriminate)); Intros.
    cbn [UCOS2_module_rep].
    sep_apply_l_atomic (event_raw_rep_split_eid sg state.(TskState) state.(EventState) eid observed Hused).
    unfold used_event_rep.
    sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
      (event_addr sg eid) (event_image sg state.(TskState) observed) EventTypeField ltac:(simpl; tauto)).
    cbn [event_image event_cell event_field_offset]; unfold OSEventType_off; entailer!;
    unfold derivable1, andp, coq_prop; intros heap Hheap; exact (conj H Hheap).
  - unfold sem_pend_fields_type_frame, event_slot_type_value; rewrite Hnone.
    rewrite (UCOS2_fields_inv_split_module sg state EventModule ltac:(discriminate)); Intros.
    match goal with H : UCOS2_state_inv sg state |- _ =>
      pose proof H as [_ [_ [_ [[_ [Hstorage _]] _]]]] end.
    destruct Hstorage as [Hdomain [_ Htype]].
    destruct (proj2 (Hdomain eid) Hfree) as [image Himage].
    cbn [UCOS2_module_rep]; unfold event_raw_rep.
    sep_apply_l_atomic (event_free_storage_split_eid sg state.(EventState) eid image Himage).
    sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
      (event_pool_addr sg eid) image EventTypeField ltac:(simpl; tauto)).
    rewrite (Htype eid image Himage).
    cbn [event_cell event_field_offset]; Exists image.
    unfold OSEventType_off, event_addr.
    rewrite logic_equiv_coq_prop_andp_sepcon.
    repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_fields_type_merge : forall sg state eid,
  UCOS2_state_inv sg state ->
  (event_addr sg eid + OSEventType_off) # UChar |-> event_slot_type_value state.(EventState) eid **
    sem_pend_fields_type_frame sg state eid |-- UCOS2_fields_inv sg state.
Proof.
  intros sg state eid Hvalid; unfold sem_pend_fields_type_frame, event_slot_type_value.
  destruct (state.(EventState).(inUsedEventStates) eid) as [observed|] eqn:Hslot.
  - change ((event_addr sg eid + OSEventType_off) # UChar |-> encode_event_type observed.(eventType)) with
      (event_cell (event_addr sg eid) EventTypeField ((event_image sg state.(TskState) observed) EventTypeField)).
    sep_apply_l_atomic (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
      (event_addr sg eid) (event_image sg state.(TskState) observed) EventTypeField ltac:(simpl; tauto)).
    fold (used_event_rep sg state.(TskState) eid observed).
    sep_apply_l_atomic (event_raw_rep_merge_eid sg state.(TskState) state.(EventState) eid observed Hslot).
    rewrite (UCOS2_fields_inv_split_module sg state EventModule ltac:(discriminate)).
    cbn [UCOS2_module_rep]; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
  - Intros image.
    repeat rewrite logic_equiv_coq_prop_andp_sepcon.
    repeat rewrite logic_equiv_sepcon_coq_prop_andp.
    repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end).
    assert (Himage : state.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image)
      by assumption.
    pose proof Hvalid as [_ [_ [_ [[_ [Hstorage _]] _]]]].
    assert (Htype : image EventTypeField = Some 0) by (apply (proj2 (proj2 Hstorage) eid image Himage)).
    assert (Hcell : ((event_addr sg eid + OSEventType_off) # UChar |-> 0) =
      event_cell (event_pool_addr sg eid) EventTypeField (image EventTypeField)).
    { rewrite Htype; reflexivity. }
    rewrite Hcell.
    sep_apply_l_atomic (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
      (event_pool_addr sg eid) image EventTypeField ltac:(simpl; tauto)).
    sep_apply_l_atomic (event_free_storage_merge_eid sg state.(EventState) eid image Himage).
    rewrite (UCOS2_fields_inv_split_module sg state EventModule ltac:(discriminate)).
    cbn [UCOS2_module_rep]; unfold event_raw_rep; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Definition sem_pend_fields_event_queue_frame sg state : Assertion :=
  flag_fields_configured_rep sg state.(FlagState) **
  UCOS2_selected_rep sg state
    (fun module => match module with EventModule | QueueModule | FlagModule => false | _ => true end).

Lemma sem_pend_fields_inv_split_event_queue : forall sg state,
  UCOS2_fields_inv sg state --||-- coq_prop (UCOS2_state_inv sg state) &&
    (event_raw_rep sg state.(TskState) state.(EventState) ** queue_storage_rep sg state.(EventState) **
     sem_pend_fields_event_queue_frame sg state).
Proof.
  intros; unfold UCOS2_fields_inv, UCOS2_fields_raw_rep, UCOS2_raw_rep_missing_flag,
    UCOS2_raw_rep_missing_module, sem_pend_fields_event_queue_frame, UCOS2_selected_rep.
  cbn [UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect UCOS2_module_rep];
    split; apply coq_prop_andp_left; intro Hvalid; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_fields_event_queue_frame_replace_event_eq : forall sg state events,
  sem_pend_fields_event_queue_frame sg (replace_EventS events state) =
  sem_pend_fields_event_queue_frame sg state.
Proof. reflexivity. Qed.

Lemma sem_pend_fields_inv_merge_event_queue : forall sg state events,
  UCOS2_state_inv sg (replace_EventS events state) ->
  event_raw_rep sg state.(TskState) events ** queue_storage_rep sg events **
    sem_pend_fields_event_queue_frame sg state |-- UCOS2_fields_inv sg (replace_EventS events state).
Proof.
  intros sg state events Hvalid.
  rewrite sem_pend_fields_inv_split_event_queue, sem_pend_fields_event_queue_frame_replace_event_eq.
  cbn [replace_EventS]; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Definition sem_pend_fields_count_frame sg state eid current : Assertion :=
  sem_rep_no_count sg state.(TskState) eid current **
  event_raw_rep_no_eid sg state.(TskState) state.(EventState) eid **
  queue_storage_rep sg state.(EventState) ** sem_pend_fields_event_queue_frame sg state.

Lemma sem_pend_fields_count_split : forall sg state eid current,
  mutex_query_lookup state eid current -> current.(eventType) = OS_EVENT_TYPE_SEM ->
  UCOS2_fields_inv sg state |--
  coq_prop (UCOS2_state_inv sg state /\ 0 <= encode_event_cnt_value current <= 65535) &&
  ((event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value current **
   sem_pend_fields_count_frame sg state eid current).
Proof.
  intros sg state eid current Hlookup Htype.
  rewrite sem_pend_fields_inv_split_event_queue.
  apply coq_prop_andp_left; intro Hvalid.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  specialize (Hpayload eid current Hlookup); unfold event_payload_consistency in Hpayload.
  rewrite Htype in Hpayload; destruct current.(semFields) as [fields|] eqn:Hfields; [|contradiction].
  assert (Hcount : encode_event_cnt_value current = fields.(semCount)).
  { unfold encode_event_cnt_value; rewrite Htype, Hfields; reflexivity. }
  sep_apply_l_atomic (event_raw_rep_split_eid sg state.(TskState) state.(EventState) eid current Hlookup).
  sep_apply_l_atomic (sem_rep_split_count sg state.(TskState) eid current fields Htype Hfields).
  rewrite Hcount; unfold sem_pend_fields_count_frame; destruct Hpayload as [Hrange Hwait]; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_fields_count_merge_updated : forall sg state eid current count,
  UCOS2_state_inv sg state -> mutex_query_lookup state eid current ->
  current.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_fields_consistency current.(waitList) {| semCount := count |} ->
  (event_addr sg eid + OSEventCnt_off) # UShort |-> count **
    sem_pend_fields_count_frame sg state eid current |--
  UCOS2_fields_inv sg (sem_count_update_state state eid current count).
Proof.
  intros sg state eid current count Hvalid Hlookup Htype Hcount.
  pose proof (UCOS2_sem_count_update_preserves_validity sg state eid current count
    Hvalid Hlookup Htype Hcount) as Hafter.
  unfold sem_pend_fields_count_frame.
  sep_apply_l_atomic (sem_rep_merge_updated_count sg state.(TskState) eid current count Htype).
  sep_apply_l_atomic (event_raw_rep_merge_updated_eid sg state.(TskState) state.(EventState)
    eid (sem_set_count current count)).
  sep_apply_l_atomic (queue_event_update_preserves_storage sg state.(EventState) eid current
    (sem_set_count current count) Hlookup eq_refl eq_refl).
  unfold sem_count_update_state in Hafter |- *.
  sep_apply_l_atomic (sem_pend_fields_inv_merge_event_queue sg state
    (update_event_field_raw state.(EventState) eid (sem_set_count current count)) Hafter).
  repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_fields_count_merge_decrement : forall sg state eid current,
  UCOS2_state_inv sg state -> mutex_query_lookup state eid current ->
  current.(eventType) = OS_EVENT_TYPE_SEM -> 0 < encode_event_cnt_value current ->
  (event_addr sg eid + OSEventCnt_off) # UShort |-> (encode_event_cnt_value current - 1) **
    sem_pend_fields_count_frame sg state eid current |--
  UCOS2_fields_inv sg (sem_count_update_state state eid current (encode_event_cnt_value current - 1)).
Proof.
  intros sg state eid current Hvalid Hlookup Htype Hpositive.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  specialize (Hpayload eid current Hlookup); unfold event_payload_consistency in Hpayload.
  rewrite Htype in Hpayload; destruct current.(semFields) as [fields|] eqn:Hfields; [|contradiction].
  assert (Hcount : encode_event_cnt_value current = fields.(semCount)).
  { unfold encode_event_cnt_value; rewrite Htype, Hfields; reflexivity. }
  apply sem_pend_fields_count_merge_updated; try assumption.
  rewrite Hcount; apply sem_decrement_preserves_consistency; [exact Hpayload|lia].
Qed.
