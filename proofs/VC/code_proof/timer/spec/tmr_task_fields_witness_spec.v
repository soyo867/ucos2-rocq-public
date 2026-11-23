Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_fields_call_adapter_spec.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Strings.String Coq.micromega.Lia.
Require Import SetsClass.SetsClass.
From SimpleC.SL Require Import CNotation.
Require Import Ucos2Verify.lib.event.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(** Concrete cell views of the existing fields owner.  The local family,
    application frame, and callback environment are the ones in that owner. *)
Lemma tmr_task_fields_profile_enabled : forall sg,
  tmr_task_profile sg -> sg.(osKernelConfig).(cfgTimerEnabled) = true.
Proof. intros sg H; unfold tmr_task_profile, tmr_link_profile in H; tauto. Qed.

Lemma tmr_task_fields_wheel_head_address : forall sg base spoke,
  tmr_task_profile sg -> base = sg.(g_OSTmrWheelTbl) ->
  tmr_unlink_wheel_field
    (base + Z.of_nat spoke * sizeof_alias_type "os_tmr_wheel") "OSTmrFirst" =
  sg.(g_OSTmrWheelTbl) + 8 * Z.of_nat spoke.
Proof.
  intros sg base spoke Hprofile Hbase.
  assert (Hlayout : tmr_unlink_layout) by (unfold tmr_task_profile in Hprofile; tauto).
  destruct Hlayout as [_ [_ [_ [_ [Hfirst [_ Hsize]]]]]].
  unfold tmr_unlink_wheel_size in Hsize.
  rewrite Hfirst, Hsize, Hbase; lia.
Qed.

Section TaskFieldsWitnessCells.
Context {Application : Type} (AppRep : Application -> TmrTaskFieldsRules.expr).
Context (environment : TaskStackCallEnvironment) (sg : StableGlobVars) (mask perr : Z).

Lemma tmr_task_fields_owned_split_time_cell : forall call before,
  tmr_task_profile sg -> timer_api_initialized (tmr_task_timers before) ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before)
    (TmrTaskFieldsRules.sepcon
      (TmrTaskFieldsRules.store_uint sg.(g_OSTmrTime) (timerTime (tmr_task_timers before)))
      (tmr_task_fields_time_rest AppRep environment sg mask perr call before)).
Proof.
  intros call before Hprofile Hinit heap Howned.
  apply (proj1 (tmr_task_fields_heap_view_cell AppRep environment sg mask perr
    call before TaskUIntCell sg.(g_OSTmrTime) (timerTime (tmr_task_timers before))
    (TmrTaskFieldsHeap.timer_without_time sg (tmr_task_timers before))) heap).
  exact (tmr_task_current_fields_split_time AppRep environment sg mask perr call before
    (tmr_task_fields_profile_enabled sg Hprofile) Hinit heap Howned).
Qed.

Lemma tmr_task_fields_owned_merge_time_cell : forall call before,
  tmr_task_profile sg -> timer_api_initialized (tmr_task_timers before) ->
  TmrTaskFieldsRules.derivable1
    (TmrTaskFieldsRules.sepcon
      (TmrTaskFieldsRules.store_uint sg.(g_OSTmrTime) (timerTime (tmr_task_timers before)))
      (tmr_task_fields_time_rest AppRep environment sg mask perr call before))
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before).
Proof.
  intros call before Hprofile Hinit heap Hcells.
  apply (tmr_task_current_fields_merge_time AppRep environment sg mask perr call before
    (tmr_task_fields_profile_enabled sg Hprofile) Hinit heap).
  exact (proj2 (tmr_task_fields_heap_view_cell AppRep environment sg mask perr
    call before TaskUIntCell sg.(g_OSTmrTime) (timerTime (tmr_task_timers before))
    (TmrTaskFieldsHeap.timer_without_time sg (tmr_task_timers before))) heap Hcells).
Qed.

Lemma tmr_task_fields_time_rest_advance : forall call before,
  tmr_task_profile sg -> timer_api_initialized (tmr_task_timers before) ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_fields_time_rest AppRep environment sg mask perr call before)
    (tmr_task_fields_time_rest AppRep environment sg mask perr call
      (tmr_task_set_timers (timer_service_advance (tmr_task_timers before)) before)).
Proof.
  intros call before Hprofile Hinit heap
    [local [kernel [client [Hjoin [[Hvalid Hfields] Hclient]]]]].
  exists local, kernel, client; split; [exact Hjoin|].
  split; [|exact Hclient]. split.
  - apply UCOS2_timer_service_advance_preserves_validity.
    + exact (tmr_task_fields_profile_enabled sg Hprofile).
    + exact Hvalid.
    + exact Hinit.
  - exact Hfields.
Qed.

Lemma tmr_task_fields_pool_image_cell_view : forall call before index image field,
  tmr_task_profile sg -> tmr_create_c_bindings sg ->
  timer_api_initialized (tmr_task_timers before) ->
  tmr_task_fields_index_valid sg index -> tmr_task_fields_image_at before index image ->
  TmrTaskFieldsRules.logic_equiv
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before)
    (TmrTaskFieldsRules.sepcon
      (tmr_task_cell (tmr_task_image_kind field)
        (tmr_unlink_timer_field (timer_pool_addr sg index) (tmr_task_image_name field))
        (tmr_task_image_value field image))
      (tmr_task_fields_image_rest AppRep environment sg mask perr call before index image field)).
Proof.
  intros call before index image field Hprofile Hbinding Hinit Hindex Himage.
  assert (Hlayout : tmr_unlink_layout) by (unfold tmr_task_profile in Hprofile; tauto).
  pose proof (tmr_task_fields_pool_image_view AppRep environment sg mask perr
    call before index image field Hbinding Hlayout
    (tmr_task_fields_profile_enabled sg Hprofile) Hinit Hindex Himage) as Hview.
  pose proof (tmr_task_fields_heap_view_cell AppRep environment sg mask perr
    call before (tmr_task_image_kind field)
    (tmr_unlink_timer_field (timer_pool_addr sg index) (tmr_task_image_name field))
    (tmr_task_image_value field image)
    (TmrTaskFieldsHeap.timer_without_field sg (tmr_task_timers before) index image field)) as Hcell.
  split; intros heap Hheap.
  - exact (proj1 Hcell heap (proj1 Hview heap Hheap)).
  - exact (proj2 Hview heap (proj2 Hcell heap Hheap)).
Qed.

Lemma tmr_task_fields_heap_view_two_cells : forall call before
  first_kind first_address first_value second_kind second_address second_value rest,
  TmrTaskFieldsRules.logic_equiv
    (tmr_task_fields_heap_view AppRep environment sg mask perr call before
      (UCOS2_C_Rules.sepcon (TmrTaskFieldsHeap.cell first_kind first_address first_value)
        (TmrTaskFieldsHeap.cell second_kind second_address second_value)) rest)
    (TmrTaskFieldsRules.sepcon
      (TmrTaskFieldsRules.sepcon (tmr_task_cell first_kind first_address first_value)
        (tmr_task_cell second_kind second_address second_value))
      (tmr_task_fields_cell_rest AppRep environment sg mask perr call before rest)).
Proof.
  intros call before first_kind first_address first_value second_kind second_address second_value rest.
  split.
  - intros heap [local [kernel [client [Hwhole
      [[parts [remaining [Hparts [Hcells Hremaining]]]] Hclient]]]]].
    destruct (TmrTaskFieldsRules.join_assoc parts remaining client kernel heap Hparts Hwhole)
      as [tail [Htail Hjoin]].
    exists parts, tail; split; [exact Hjoin|]. split.
    + destruct (proj1 (TmrTaskFieldsRules.lift_sepcon _ _ parts) Hcells)
        as [first [second [Hpair [Hfirst Hsecond]]]].
      exists first, second; split; [exact Hpair|]. split.
      * exact (proj2 (tmr_task_fields_cell_lift first_kind first_address first_value) first Hfirst).
      * exact (proj2 (tmr_task_fields_cell_lift second_kind second_address second_value) second Hsecond).
    + exists local, remaining, client; split; [exact Htail|]. split; assumption.
  - intros heap [parts [tail [Hwhole [Hcells
      [local [remaining [client [Htail [Hremaining Hclient]]]]]]]]].
    destruct (TmrTaskFieldsRules.join_assoc client remaining parts tail heap
      (TmrTaskFieldsRules.join_comm _ _ _ Htail)
      (TmrTaskFieldsRules.join_comm _ _ _ Hwhole)) as [kernel [Hparts Hjoin]].
    exists local, kernel, client; split.
    + apply TmrTaskFieldsRules.join_comm; exact Hjoin.
    + split; [|exact Hclient]. exists parts, remaining; split.
      * apply TmrTaskFieldsRules.join_comm; exact Hparts.
      * split; [|exact Hremaining].
        apply (proj2 (TmrTaskFieldsRules.lift_sepcon _ _ parts)).
        destruct Hcells as [first [second [Hpair [Hfirst Hsecond]]]].
        exists first, second; split; [exact Hpair|]. split.
        -- exact (proj1 (tmr_task_fields_cell_lift first_kind first_address first_value) first Hfirst).
        -- exact (proj1 (tmr_task_fields_cell_lift second_kind second_address second_value) second Hsecond).
Qed.

Lemma tmr_task_fields_pool_match_cell_view : forall call before index image,
  tmr_task_profile sg -> tmr_create_c_bindings sg ->
  timer_api_initialized (tmr_task_timers before) ->
  tmr_task_fields_index_valid sg index -> tmr_task_fields_image_at before index image ->
  TmrTaskFieldsRules.logic_equiv
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before)
    (TmrTaskFieldsRules.sepcon
      (TmrTaskFieldsRules.sepcon
        (TmrTaskFieldsRules.store_uint sg.(g_OSTmrTime) (timerTime (tmr_task_timers before)))
        (TmrTaskFieldsRules.store_uint
          (tmr_unlink_timer_field (timer_pool_addr sg index) "OSTmrMatch") image.(timerImageMatch)))
      (tmr_task_fields_match_rest AppRep environment sg mask perr call before index image)).
Proof.
  intros call before index image Hprofile Hbinding Hinit Hindex Himage.
  assert (Hlayout : tmr_unlink_layout) by (unfold tmr_task_profile in Hprofile; tauto).
  pose proof (tmr_task_fields_pool_match_view AppRep environment sg mask perr call before
    index image Hbinding Hlayout (tmr_task_fields_profile_enabled sg Hprofile)
    Hinit Hindex Himage) as Hview.
  pose proof (tmr_task_fields_heap_view_two_cells call before
    TaskUIntCell sg.(g_OSTmrTime) (timerTime (tmr_task_timers before))
    TaskUIntCell (tmr_unlink_timer_field (timer_pool_addr sg index) "OSTmrMatch")
    image.(timerImageMatch)
    (TmrTaskFieldsHeap.timer_without_time_field sg (tmr_task_timers before)
      index image TaskMatchField)) as Hcells.
  split; intros heap Hheap.
  - exact (proj1 Hcells heap (proj1 Hview heap Hheap)).
  - exact (proj2 Hview heap (proj2 Hcells heap Hheap)).
Qed.

Lemma tmr_task_fields_head_cell_view : forall call before spoke,
  tmr_task_profile sg -> timer_api_initialized (tmr_task_timers before) ->
  tmr_task_spoke_in_range sg spoke ->
  TmrTaskFieldsRules.logic_equiv
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before)
    (TmrTaskFieldsRules.sepcon
      (TmrTaskFieldsRules.store_ptr (sg.(g_OSTmrWheelTbl) + 8 * Z.of_nat spoke)
        (tmr_task_head sg spoke (tmr_task_timers before)))
      (tmr_task_fields_head_rest AppRep environment sg mask perr call before spoke)).
Proof.
  intros call before spoke Hprofile Hinit Hspoke.
  pose proof (tmr_task_fields_profile_enabled sg Hprofile) as Hen.
  pose proof (tmr_task_fields_heap_view_cell AppRep environment sg mask perr call before
    TaskPointerCell (sg.(g_OSTmrWheelTbl) + 8 * Z.of_nat spoke)
    (tmr_task_head sg spoke (tmr_task_timers before))
    (TmrTaskFieldsHeap.timer_without_head sg (tmr_task_timers before) spoke
      (nth spoke (timerWheel (tmr_task_timers before)) []))) as Hcell.
  split; intros heap Hheap.
  - apply (proj1 Hcell heap).
    exact (tmr_task_current_fields_reload_head AppRep environment sg mask perr
      call before spoke Hen Hinit Hspoke heap Hheap).
  - pose proof Hheap as [part [tail [Hjoin [Hpart
      [local [kernel [client [Htail [Hkernel Hclient]]]]]]]]].
    pose proof (proj1 Hkernel) as Hvalid.
    change (UCOS2_state_inv sg (fst before)) in Hvalid.
    assert (Htimer : valid_timer_state sg (tmr_task_timers before)).
    { apply (proj1 (timer_initialized_configuration_iff sg (tmr_task_timers before) Hen Hinit)).
      change (valid_timer_configuration sg (fst before).(TimerState)).
      unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
    destruct Htimer as [_ [[Hlength _] _]].
    assert (Hrow : nth_error (timerWheel (tmr_task_timers before)) spoke =
      Some (nth spoke (timerWheel (tmr_task_timers before)) [])).
    { apply nth_error_nth'; unfold tmr_task_spoke_in_range in Hspoke; lia. }
    apply (proj2 (tmr_task_current_fields_split_merge_head AppRep environment sg mask perr
      call before spoke _ Hen Hinit Hrow) heap).
    exact (proj2 Hcell heap Hheap).
Qed.

Lemma tmr_task_fields_eligible_image : forall call before index,
  tmr_task_profile sg -> timer_api_initialized (tmr_task_timers before) ->
  tmr_link_eligible (tmr_task_timers before) index ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before)
    (fun heap => exists image, tmr_task_fields_image_at before index image /\
      tmr_task_current_fields_owned AppRep environment sg mask perr call before heap).
Proof.
  intros call before index Hprofile Hinit [node [Hnode Hinactive]] heap Howned.
  pose proof (proj1 (tmr_task_current_fields_timer_valid AppRep environment sg mask perr
    call before (tmr_task_fields_profile_enabled sg Hprofile) Hinit heap Howned)) as Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ [Hused _]]]]]]]].
  destruct (Hused index node Hnode) as [_ [_ [_ [image [Himage _]]]]].
  exists image; split; [exact Himage|exact Howned].
Qed.

Lemma tmr_task_fields_owned_split_completed_state_cell : forall call before index image,
  tmr_task_profile sg -> tmr_create_c_bindings sg ->
  timer_api_initialized (tmr_task_timers before) ->
  tmr_task_fields_index_valid sg index -> tmr_task_fields_image_at before index image ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before)
    (TmrTaskFieldsRules.sepcon
      (TmrTaskFieldsRules.store_uchar
        (tmr_unlink_timer_field (timer_pool_addr sg index) "OSTmrState") image.(timerImageState))
      (tmr_task_fields_complete_rest AppRep environment sg mask perr call before index image)).
Proof.
  intros call before index image Hprofile Hbinding Hinit Hindex Himage heap Howned.
  assert (Hlayout : tmr_unlink_layout) by (unfold tmr_task_profile in Hprofile; tauto).
  pose proof (tmr_task_pool_field_addresses_from_create_binding sg index TaskStateField
    Hbinding Hlayout Hindex) as Haddress.
  cbn [tmr_task_image_name tmr_task_image_offset] in Haddress.
  replace (timer_pool_addr sg index + (timer_option_offset sg.(osKernelConfig) + 1))
    with (timer_pool_addr sg index + timer_option_offset sg.(osKernelConfig) + 1)
    in Haddress by lia.
  rewrite Haddress.
  apply (proj1 (tmr_task_fields_heap_view_cell AppRep environment sg mask perr call before
    TaskByteCell (timer_pool_addr sg index + timer_option_offset sg.(osKernelConfig) + 1)
    image.(timerImageState)
    (timer_complete_rep_without_state sg (tmr_task_timers before) index image)) heap).
  exact (tmr_task_current_fields_split_completed_state AppRep environment sg mask perr
    call before index image (tmr_task_fields_profile_enabled sg Hprofile) Hinit Himage heap Howned).
Qed.

Lemma tmr_task_fields_completed_state_cell_merge : forall call before index image,
  tmr_task_profile sg -> tmr_create_c_bindings sg ->
  timer_api_initialized (tmr_task_timers before) ->
  tmr_task_fields_index_valid sg index -> tmr_task_fields_image_at before index image ->
  tmr_link_eligible (tmr_task_timers before) index ->
  TmrTaskFieldsRules.derivable1
    (TmrTaskFieldsRules.sepcon
      (TmrTaskFieldsRules.store_uchar
        (tmr_unlink_timer_field (timer_pool_addr sg index) "OSTmrState") 2)
      (tmr_task_fields_complete_rest AppRep environment sg mask perr call before index image))
    (fun heap => exists after, tmr_task_complete_world before index after /\
      tmr_task_current_fields_owned AppRep environment sg mask perr call after heap).
Proof.
  intros call before index image Hprofile Hbinding Hinit Hindex Himage
    [node [Hnode Hinactive]] heap Hcells.
  assert (Hlayout : tmr_unlink_layout) by (unfold tmr_task_profile in Hprofile; tauto).
  pose proof (tmr_task_pool_field_addresses_from_create_binding sg index TaskStateField
    Hbinding Hlayout Hindex) as Haddress.
  cbn [tmr_task_image_name tmr_task_image_offset] in Haddress.
  replace (timer_pool_addr sg index + (timer_option_offset sg.(osKernelConfig) + 1))
    with (timer_pool_addr sg index + timer_option_offset sg.(osKernelConfig) + 1)
    in Haddress by lia.
  rewrite Haddress in Hcells.
  destruct (timer_complete_result_exists (tmr_task_timers before) index node image Hnode Himage)
    as [timers Hstep].
  exists (tmr_task_set_timers timers before); split.
  - exists timers; split; [exact Hstep|reflexivity].
  - apply (tmr_task_current_fields_merge_completed_state AppRep environment sg mask perr
      call before index node image timers (tmr_task_fields_profile_enabled sg Hprofile)
      Hinit Hnode Hinactive Himage Hstep heap).
    apply (proj2 (tmr_task_fields_heap_view_cell AppRep environment sg mask perr call before
      TaskByteCell (timer_pool_addr sg index + timer_option_offset sg.(osKernelConfig) + 1) 2
      (timer_complete_rep_without_state sg (tmr_task_timers before) index image)) heap).
    exact Hcells.
Qed.

End TaskFieldsWitnessCells.

Lemma tmr_task_unlink_world_initialized_eligible : forall Application sg
  (before after : tmr_task_scan_world Application) index,
  timer_api_initialized (tmr_task_timers before) ->
  tmr_task_unlink_world sg before index after ->
  timer_api_initialized (tmr_task_timers after) /\
  tmr_link_eligible (tmr_task_timers after) index.
Proof.
  intros Application sg before after index Hinit [timers [Hstep ->]].
  change (timer_api_initialized timers /\ tmr_link_eligible timers index).
  split.
  - unfold timer_api_initialized in *.
    rewrite (timer_unlink_preserves_initialization_phase sg (tmr_task_timers before)
      index timers Hstep); exact Hinit.
  - destruct (timer_unlink_clears_links_and_stops sg (tmr_task_timers before) index timers Hstep)
      as [node [image [Hnode [_ [Hstate _]]]]].
    exists node; split; [exact Hnode|]. rewrite Hstate; discriminate.
Qed.

Section TaskFieldsWitnessRawCalls.
Context {Application : Type} (AppRep : Application -> TmrTaskFieldsRules.expr).
Context (environment : TaskStackCallEnvironment) (sg : StableGlobVars) (mask perr : Z).

Lemma tmr_task_fields_owned_split_unlink : forall call before index,
  tmr_task_profile sg -> timer_api_initialized (tmr_task_timers before) ->
  tmr_unlink_running (tmr_task_timers before) index ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before)
    (fun heap => exists local match_time next previous first entries frame,
      TmrTaskFieldsRules.sepcon
        (TmrTaskFieldsCallee.unlink_pre (timer_pool_addr sg index) sg.(g_OSTmrWheelTbl)
          match_time next previous first entries frame)
        (tmr_task_fields_unlink_rest AppRep environment sg mask perr local call before
          index match_time next previous first entries frame) heap).
Proof.
  intros call before index Hprofile Hinit Hrunning heap Howned.
  assert (Hlayout : tmr_unlink_layout) by (unfold tmr_task_profile in Hprofile; tauto).
  assert (Hunlink : tmr_unlink_profile sg) by (unfold tmr_task_profile in Hprofile; tauto).
  destruct (tmr_task_current_fields_split_unlink_call AppRep environment sg mask perr
    call before index Hlayout Hunlink Hinit Hrunning heap Howned)
    as [local [kernel [client [Hwhole [Hkernel Hclient]]]]].
  destruct Hkernel as [match_time [next [previous [first [entries [frame Hpair]]]]]].
  destruct (proj1 (TmrTaskFieldsRules.lift_sepcon _ _ kernel) Hpair)
    as [raw [rest [Hpairjoin [Hraw Hrest]]]].
  destruct (TmrTaskFieldsRules.join_assoc raw rest client kernel heap Hpairjoin Hwhole)
    as [tail [Htail Hjoin]].
  exists local, match_time, next, previous, first, entries, frame, raw, tail.
  split; [exact Hjoin|]. split; [exact Hraw|].
  exists rest, client; split; [exact Htail|]. split; assumption.
Qed.

Lemma tmr_task_fields_unlink_post_merge : forall local call before index
  match_time next previous first entries frame,
  TmrTaskFieldsRules.derivable1
    (TmrTaskFieldsRules.sepcon
      (TmrTaskFieldsCallee.unlink_post (timer_pool_addr sg index) sg.(g_OSTmrWheelTbl)
        match_time next previous first entries frame)
      (tmr_task_fields_unlink_rest AppRep environment sg mask perr local call before
        index match_time next previous first entries frame))
    (fun heap => exists after, tmr_task_unlink_world sg before index after /\
      tmr_task_current_fields_owned AppRep environment sg mask perr call after heap).
Proof.
  intros local call before index match_time next previous first entries frame heap
    [raw [tail [Hwhole [Hraw [rest [client [Htail [Hrest Hclient]]]]]]]].
  destruct (TmrTaskFieldsRules.join_assoc client rest raw tail heap
    (TmrTaskFieldsRules.join_comm _ _ _ Htail)
    (TmrTaskFieldsRules.join_comm _ _ _ Hwhole)) as [kernel [Hparts Hjoin]].
  pose proof (proj1 (TmrTaskFieldsRules.lift_wand _ _ rest) Hrest) as Hrestore.
  destruct (Hrestore raw kernel Hparts Hraw) as [timers [Hstep Hcontext]].
  exists (tmr_task_set_timers timers before); split.
  - exists timers; split; [exact Hstep|reflexivity].
  - exists local, kernel, client; split.
    + apply TmrTaskFieldsRules.join_comm; exact Hjoin.
    + split; assumption.
Qed.

Lemma tmr_task_fields_owned_split_link : forall call before index,
  tmr_task_profile sg -> timer_api_initialized (tmr_task_timers before) ->
  tmr_link_eligible (tmr_task_timers before) index ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before)
    (fun heap => exists local delay period first entries frame,
      TmrTaskFieldsRules.sepcon
        (TmrTaskFieldsCallee.link_pre (timer_pool_addr sg index) sg.(g_OSTmrWheelTbl)
          sg.(g_OSTmrTime) 1 (timerTime (tmr_task_timers before)) delay period first entries frame)
        (tmr_task_fields_link_rest AppRep environment sg mask perr local call before
          index delay period first entries frame) heap).
Proof.
  intros call before index Hprofile Hinit Heligible heap Howned.
  assert (Hlayout : tmr_link_layout) by (unfold tmr_task_profile in Hprofile; tauto).
  assert (Hlink : tmr_link_profile sg) by (unfold tmr_task_profile in Hprofile; tauto).
  destruct (tmr_task_current_fields_split_link_call AppRep environment sg mask perr
    call before index Hlayout Hlink Hinit Heligible heap Howned)
    as [local [kernel [client [Hwhole [Hkernel Hclient]]]]].
  destruct Hkernel as [delay [period [first [entries [frame Hpair]]]]].
  destruct (proj1 (TmrTaskFieldsRules.lift_sepcon _ _ kernel) Hpair)
    as [raw [rest [Hpairjoin [Hraw Hrest]]]].
  destruct (TmrTaskFieldsRules.join_assoc raw rest client kernel heap Hpairjoin Hwhole)
    as [tail [Htail Hjoin]].
  exists local, delay, period, first, entries, frame, raw, tail.
  split; [exact Hjoin|]. split; [exact Hraw|].
  exists rest, client; split; [exact Htail|]. split; assumption.
Qed.

Lemma tmr_task_fields_link_post_merge : forall local call before index
  delay period first entries frame,
  TmrTaskFieldsRules.derivable1
    (TmrTaskFieldsRules.sepcon
      (TmrTaskFieldsCallee.link_post (timer_pool_addr sg index) sg.(g_OSTmrWheelTbl)
        sg.(g_OSTmrTime) 1 (timerTime (tmr_task_timers before)) delay period first entries frame)
      (tmr_task_fields_link_rest AppRep environment sg mask perr local call before
        index delay period first entries frame))
    (fun heap => exists after, tmr_task_link_world sg before index after /\
      tmr_task_current_fields_owned AppRep environment sg mask perr call after heap).
Proof.
  intros local call before index delay period first entries frame heap
    [raw [tail [Hwhole [Hraw [rest [client [Htail [Hrest Hclient]]]]]]]].
  destruct (TmrTaskFieldsRules.join_assoc client rest raw tail heap
    (TmrTaskFieldsRules.join_comm _ _ _ Htail)
    (TmrTaskFieldsRules.join_comm _ _ _ Hwhole)) as [kernel [Hparts Hjoin]].
  pose proof (proj1 (TmrTaskFieldsRules.lift_wand _ _ rest) Hrest) as Hrestore.
  destruct (Hrestore raw kernel Hparts Hraw) as [timers [Hstep Hcontext]].
  exists (tmr_task_set_timers timers before); split.
  - exists timers; split; [exact Hstep|reflexivity].
  - exists local, kernel, client; split.
    + apply TmrTaskFieldsRules.join_comm; exact Hjoin.
    + split; assumption.
Qed.

End TaskFieldsWitnessRawCalls.

Section TaskFieldsWitnessSchedulerCalls.
Context {Application : Type} (AppRep : Application -> TmrTaskFieldsRules.expr).
Context (environment : TaskStackCallEnvironment) (sg : StableGlobVars) (mask perr : Z).

Lemma tmr_task_fields_owned_lock_pre : forall critical local call world,
  TmrTaskFieldsRules.derivable1
    (tmr_task_fields_owned AppRep environment sg mask perr local call world)
    (TmrTaskFieldsRules.sepcon
      (TmrTaskFieldsCallee.lock_pre environment critical local sg call mask
        (tmr_task_kernel world) tmr_task_fields_kernel_any)
      (tmr_task_fields_client AppRep perr world)).
Proof.
  intros critical local call world heap [kernel [client [Hjoin [Hkernel Hclient]]]].
  exists kernel, client; split; [exact Hjoin|]. split; [|exact Hclient].
  split; [|exact Hkernel].
  unfold os_sched_lock_continuation_safe, safeExec, safe, StateRelHoare.weakestpre,
    tmr_task_fields_kernel_any.
  exists (tmr_task_kernel world); split; [reflexivity|]. sets_unfold; intros; exact I.
Qed.

Lemma tmr_task_current_fields_unlock_pre : forall critical call world,
  kernel_sched_ready_clients critical -> kernel_tcb_stack_field_layout sg ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_current_fields_owned AppRep environment sg mask perr call world)
    (fun heap => exists local,
      TmrTaskFieldsRules.sepcon
        (TmrTaskFieldsCallee.unlock_pre environment critical local sg call mask
          (tmr_task_kernel world) tmr_task_fields_kernel_any)
        (tmr_task_fields_client AppRep perr world) heap).
Proof.
  intros critical call world Hclients Hlayout heap
    [local [kernel [client [Hjoin [Hkernel Hclient]]]]].
  exists local, kernel, client; split; [exact Hjoin|]. split; [|exact Hclient].
  split; [|exact Hkernel]. split; [|split; assumption].
  unfold os_sched_unlock_continuation_safe, safeExec, safe, StateRelHoare.weakestpre,
    tmr_task_fields_kernel_any.
  exists (tmr_task_kernel world); split; [reflexivity|]. sets_unfold; intros; exact I.
Qed.

End TaskFieldsWitnessSchedulerCalls.

(** The ECB alias interpretation is an input binding.  The call domain
    supplies the actual eid and ordered early-error/blocking branches. *)
Lemma tmr_task_fields_pend_address_guard_from_layout : forall environment critical sg call
  before eid observed pe ints locks current group rows,
  sem_pend_fields_call_domain environment critical sg call pe before eid observed ->
  event_table_layout_prop sg ->
  ints = sg.(g_OSIntNesting) -> locks = sg.(g_OSLockNesting) ->
  current = sg.(g_OSTCBCur) -> group = sg.(g_OSRdyGrp) -> rows = sg.(g_OSRdyTbl) ->
  tmr_task_pend_address_guard sg before (Some environment) critical call pe eid
    (&((pe) # "os_event" ->ₛ "OSEventType"))
    (&((pe) # "os_event" ->ₛ "OSEventCnt")) ints locks current group rows.
Proof.
  intros environment critical sg call before eid observed pe ints locks current group rows
    [_ [_ [Hinput [_ [_ Hblocking]]]]] Hlayout Hints Hlocks Hcurrent Hgroup Hrows.
  destruct Hinput as [Hzero|[Hnonzero [Haddress [Hid [Hslot Hprotocol]]]]].
  - left; exact Hzero.
  - pose proof (event_object_layout_core_proj sg eid (Hlayout eid Hid))
      as [Htype_address [_ Hcount_address]].
    right; split; [exact Hnonzero|]. split.
    + rewrite Haddress; exact Htype_address.
    + destruct (Z.eq_dec (event_slot_type_value before.(EventState) eid) 3) as [Htype|Htype].
      2: { left; exact Htype. }
      right; split; [exact Htype|]. split; [exact Hints|].
      destruct (Z_lt_ge_dec 0 before.(IntrState).(intNesting)) as [Hinside|Houtside].
      * left; lia.
      * right; split; [lia|]. split; [exact Hlocks|].
        destruct (Z_lt_ge_dec 0 before.(IntrState).(lockNesting)) as [Hlocked|Hunlocked].
        -- left; lia.
        -- right; split; [lia|]. split.
           ++ rewrite Haddress; exact Hcount_address.
           ++ rewrite Hcurrent, Hgroup, Hrows.
              apply Hblocking; [exact Hnonzero|].
              unfold sem_pend_context_error; rewrite Htype.
              cbn [encode_event_type Z.eqb negb].
              rewrite (proj2 (Z.ltb_ge 0 before.(IntrState).(intNesting)) ltac:(lia)),
                (proj2 (Z.ltb_ge 0 before.(IntrState).(lockNesting)) ltac:(lia)); reflexivity.
Qed.

Module TmrTaskFieldsWitnessHeap.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.

Definition timer_without_signal sg timers : Assertion :=
  timer_images_rep sg timers **
  timer_wheel_rep_from sg sg.(g_OSTmrWheelTbl) timers.(timerWheel) **
  sg.(g_OSTmrFreeList) # Ptr |-> timer_id_pointer sg timers.(timerFree) **
  sg.(g_OSTmrFree) # UShort |-> timers.(timerFreeCount) **
  sg.(g_OSTmrUsed) # UShort |-> timers.(timerUsedCount) **
  sg.(g_OSTmrTime) # UInt |-> timers.(timerTime) **
  sg.(g_OSTmrSem) # Ptr |-> timers.(timerSem).

Lemma timer_split_merge_signal : forall sg timers,
  timer_raw_rep sg timers --||--
  sg.(g_OSTmrSemSignal) # Ptr |-> timers.(timerSignalSem) ** timer_without_signal sg timers.
Proof.
  intros; unfold timer_raw_rep, timer_globals_rep, timer_without_signal; split; entailer!.
Qed.

Definition signal_rest environment local sg call mask perr before : Assertion :=
  TmrTaskFieldsHeap.context_rest environment local sg call mask before
    (timer_without_signal sg before.(TimerState)) ** sem_pend_error_cell perr.

Lemma signal_rest_closes_pend : forall environment local critical sg call mask perr before
  eid observed,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized before.(TimerState) ->
  sem_pend_fields_call_domain environment critical sg call before.(TimerState).(timerSignalSem)
    before eid observed ->
  signal_rest environment local sg call mask perr before |--
  (sg.(g_OSTmrSemSignal) # Ptr |-> before.(TimerState).(timerSignalSem) -*
    sem_pend_source_fields_call_pre environment local critical sg call mask
      before.(TimerState).(timerSignalSem) 0 perr before eid observed tmr_task_legacy_any).
Proof.
  intros environment local critical sg call mask perr before eid observed Hen Hinit Hdomain.
  apply_sepcon_adjoint.
  assert (Hmerge :
    signal_rest environment local sg call mask perr before **
      sg.(g_OSTmrSemSignal) # Ptr |-> before.(TimerState).(timerSignalSem) |--
    sem_pend_error_cell perr ** TmrTaskFields.tmr_task_fields_context environment local sg call mask before).
  { sep_apply_r_atomic (TmrTaskFieldsHeap.context_merge_read_part environment local sg call mask before
      (TmrTaskFieldsHeap.cell TaskPointerCell sg.(g_OSTmrSemSignal) before.(TimerState).(timerSignalSem))
      (timer_without_signal sg before.(TimerState)) Hen Hinit
      (proj2 (timer_split_merge_signal sg before.(TimerState)))).
    unfold signal_rest, TmrTaskFieldsHeap.cell; entailer!. }
  intros heap Hheap; split.
  - split; [exact Hdomain|].
    unfold sem_pend_source_fields_call_safe, safeExec, safe, StateRelHoare.weakestpre, tmr_task_legacy_any.
    exists (RTrans_Abs before); split.
    + unfold LastSeen; intro state; split; trivial.
    + sets_unfold; intros; exact I.
  - exact (Hmerge heap Hheap).
Qed.

Lemma context_split_pend_argument : forall environment local critical sg call mask perr before
  eid observed,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized before.(TimerState) ->
  sem_pend_fields_call_domain environment critical sg call before.(TimerState).(timerSignalSem)
    before eid observed ->
  TmrTaskFields.tmr_task_fields_context environment local sg call mask before ** sem_pend_error_cell perr |--
  sg.(g_OSTmrSemSignal) # Ptr |-> before.(TimerState).(timerSignalSem) **
    (sg.(g_OSTmrSemSignal) # Ptr |-> before.(TimerState).(timerSignalSem) -*
      sem_pend_source_fields_call_pre environment local critical sg call mask
        before.(TimerState).(timerSignalSem) 0 perr before eid observed tmr_task_legacy_any).
Proof.
  intros environment local critical sg call mask perr before eid observed Hen Hinit Hdomain.
  sep_apply_l_atomic (TmrTaskFieldsHeap.context_split_part environment local sg call mask before
    (TmrTaskFieldsHeap.cell TaskPointerCell sg.(g_OSTmrSemSignal) before.(TimerState).(timerSignalSem))
    (timer_without_signal sg before.(TimerState)) Hen Hinit
    (proj1 (timer_split_merge_signal sg before.(TimerState)))).
  sep_apply_r_atomic (signal_rest_closes_pend environment local critical sg call mask perr before
    eid observed Hen Hinit Hdomain).
  unfold signal_rest, TmrTaskFieldsHeap.cell; entailer!.
Qed.

End TmrTaskFieldsWitnessHeap.

Lemma tmr_task_current_fields_pend_argument : forall Application
  (AppRep : Application -> TmrTaskFieldsRules.expr) environment critical sg call mask perr
  (world : tmr_task_scan_world Application) eid observed,
  tmr_task_profile sg -> timer_api_initialized (tmr_task_timers world) ->
  sem_pend_fields_call_domain environment critical sg call
    (tmr_task_timers world).(timerSignalSem) (tmr_task_kernel world) eid observed ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_current_fields_owned AppRep environment sg mask perr call world)
    (fun heap => exists local,
      TmrTaskFieldsRules.sepcon
        (tmr_task_fields_pend_argument_pre environment local critical sg call mask
          (tmr_task_timers world).(timerSignalSem) 0 perr (tmr_task_kernel world)
          eid observed tmr_task_legacy_any sg.(g_OSTmrSemSignal))
        (AppRep (tmr_task_application world)) heap).
Proof.
  intros Application AppRep environment critical sg call mask perr world eid observed
    Hprofile Hinit Hdomain heap
    [local [kernel [client [Hwhole [Hkernel
      [error [application [Hclient [Herror Happlication]]]]]]]]].
  destruct (TmrTaskFieldsRules.join_assoc application error kernel client heap
    (TmrTaskFieldsRules.join_comm _ _ _ Hclient)
    (TmrTaskFieldsRules.join_comm _ _ _ Hwhole)) as [owned [Hparts Hjoin]].
  assert (Hraw : TmrTaskFieldsRules.lift
    (UCOS2_C_Rules.sepcon
      (TmrTaskFields.tmr_task_fields_context environment local sg call mask (tmr_task_kernel world))
      (sem_pend_error_cell perr)) owned).
  { apply (proj2 (TmrTaskFieldsRules.lift_sepcon _ _ owned)).
    exists kernel, error; split.
    - apply TmrTaskFieldsRules.join_comm; exact Hparts.
    - split; assumption. }
  pose proof (TmrTaskFieldsWitnessHeap.context_split_pend_argument environment local critical sg call
    mask perr (tmr_task_kernel world) eid observed (tmr_task_fields_profile_enabled sg Hprofile)
    Hinit Hdomain (fst owned) Hraw) as Hargument.
  destruct (proj1 (TmrTaskFieldsRules.lift_sepcon _ _ owned) Hargument)
    as [cell [rest [Hargumentjoin [Hcell Hrest]]]].
  exists local, owned, application; split.
  - apply TmrTaskFieldsRules.join_comm; exact Hjoin.
  - split; [|exact Happlication]. exists cell, rest; split; [exact Hargumentjoin|]. split.
    + exact (proj2 (tmr_task_fields_cell_lift TaskPointerCell sg.(g_OSTmrSemSignal)
        (tmr_task_timers world).(timerSignalSem)) cell Hcell).
    + intros supplied combined Hcombined Hsupplied.
      apply (proj1 (TmrTaskFieldsRules.lift_wand _ _ rest) Hrest supplied combined Hcombined).
      exact (proj1 (tmr_task_fields_cell_lift TaskPointerCell sg.(g_OSTmrSemSignal)
        (tmr_task_timers world).(timerSignalSem)) supplied Hsupplied).
Qed.
