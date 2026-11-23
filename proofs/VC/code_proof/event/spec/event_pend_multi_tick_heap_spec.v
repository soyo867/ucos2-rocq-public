Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Strings.String Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.VC.code.event.spec.event_pend_multi_tick_full_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_profile_heap_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_storage
  Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.task_storage
  Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.task Ucos2Verify.lib.tick
  Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def
  Ucos2Verify.lib.task_status Ucos2Verify.lib.field_storage Ucos2Verify.lib.sched
  Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.ucos2_spatial
  Ucos2Verify.lib.task_stack.
From AUXLib Require Import ListLib.
Import UCOS2_C_Rules KernelHeapStorage KernelHeapObservation ListNotations TaskStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** These are the actual full-layout TCB cells used by one protected tick
    body. Other fields, including Names/Profile/Multi pointers, stay in
    the same physical frame. No endpoint kernel invariant is a premise of
    the memory execution relation. *)
Definition event_pend_multi_tick_byte_field (field : TCBField) : Prop :=
  field = TCBStat \/ field = TCBStatPend \/ field = TCBY \/
  field = TCBBitX \/ field = TCBBitY.

Lemma event_pend_multi_tick_common_write_image : forall image field value,
  tcb_layout_write image (TCBCommonField field) value =
  tcb_layout_update_common (fun common => tcb_write common field value) image.
Proof.
  intros; apply functional_extensionality; intros [other| | | | | | |];
    try reflexivity.
  unfold tcb_layout_write, tcb_layout_update_common, tcb_layout_image,
    tcb_layout_common_image, tcb_write, field_update.
  destruct (TCBField_eq_dec other field) as [Heq|Hne];
    destruct (TCBLayoutField_eq_dec (TCBCommonField other) (TCBCommonField field));
    congruence.
Qed.

Lemma event_pend_multi_tick_byte_load : forall pointer image field value frame heap,
  event_pend_multi_tick_byte_field field ->
  image (TCBCommonField field) = Some value ->
  (tcb_configured_storage_rep true true pointer image ** frame) heap ->
  uchar_load (tcb_field_address pointer field) value heap.
Proof.
  intros pointer image field value frame heap Hfield Hvalue Hheap.
  assert (Hsplit : tcb_configured_storage_rep true true pointer image ** frame |--
    tcb_field_address pointer field # UChar |-> value **
    (tcb_configured_storage_without_field true true pointer image (TCBCommonField field) ** frame)).
  { sep_apply_l_atomic (tcb_configured_storage_split_field true true pointer image
      (TCBCommonField field) (tcb_configured_common_field_in true true field)).
    rewrite Hvalue; unfold event_pend_multi_tick_byte_field in Hfield;
      destruct Hfield as [-> | [-> | [-> | [-> | ->]]]]; cbn [tcb_layout_cell tcb_cell]; entailer!. }
  eapply framed_uchar_store_load; exact (Hsplit heap Hheap).
Qed.

Lemma event_pend_multi_tick_delay_load : forall pointer image delay frame heap,
  image (TCBCommonField TCBDly) = Some delay ->
  (tcb_configured_storage_rep true true pointer image ** frame) heap ->
  pointer_load (tcb_field_address pointer TCBDly) delay heap.
Proof.
  intros pointer image delay frame heap Hdelay Hheap.
  assert (Hsplit : tcb_configured_storage_rep true true pointer image ** frame |--
    tcb_field_address pointer TCBDly # UInt |-> delay **
    (tcb_configured_storage_without_field true true pointer image (TCBCommonField TCBDly) ** frame)).
  { sep_apply_l_atomic (tcb_configured_storage_split_field true true pointer image
      (TCBCommonField TCBDly) (tcb_configured_common_field_in true true TCBDly)).
    rewrite Hdelay; cbn [tcb_layout_cell tcb_cell]; entailer!. }
  destruct (Hsplit heap Hheap) as [cell [rest [Hjoin [Hcell Hrest]]]].
  eapply pointer_load_frame; [apply sched_profile_uint_load; exact Hcell|exact Hjoin].
Qed.

Lemma event_pend_multi_tick_delay_write : forall pointer image old stored frame heap,
  image (TCBCommonField TCBDly) = Some old -> 0 <= stored < 4294967296 ->
  (tcb_configured_storage_rep true true pointer image ** frame) heap ->
  exists final,
    kernel_heap_execution (pointer_store_writes (tcb_field_address pointer TCBDly) stored) heap final /\
    (tcb_configured_storage_rep true true pointer
      (tcb_layout_write image (TCBCommonField TCBDly) (Some stored)) ** frame) final.
Proof.
  intros pointer image old stored frame heap Hold Hstored Hheap.
  assert (Hsplit : tcb_configured_storage_rep true true pointer image ** frame |--
    tcb_field_address pointer TCBDly # UInt |->_ **
    (tcb_configured_storage_without_field true true pointer image (TCBCommonField TCBDly) ** frame)).
  { sep_apply_l_atomic (tcb_configured_storage_split_field true true pointer image
      (TCBCommonField TCBDly) (tcb_configured_common_field_in true true TCBDly)).
    rewrite Hold; cbn [tcb_layout_cell tcb_cell].
    sep_apply_l_atomic (store_uint_undef_store_uint (tcb_field_address pointer TCBDly) old); entailer!. }
  destruct (sched_profile_uint_store_frame_post _ stored _ heap Hstored (Hsplit heap Hheap))
    as [final [Hrun Hpost]].
  exists final; split; [exact Hrun|].
  assert (Hmerge : tcb_field_address pointer TCBDly # UInt |-> stored **
    (tcb_configured_storage_without_field true true pointer image (TCBCommonField TCBDly) ** frame) |--
    tcb_configured_storage_rep true true pointer
      (tcb_layout_write image (TCBCommonField TCBDly) (Some stored)) ** frame).
  { pose proof (tcb_configured_storage_merge_updated_field true true pointer image
      (TCBCommonField TCBDly) (Some stored) (tcb_configured_common_field_in true true TCBDly)) as Hfield.
    cbn [tcb_layout_cell tcb_cell] in Hfield; sep_apply_l_atomic Hfield; entailer!. }
  exact (Hmerge final Hpost).
Qed.

Lemma event_pend_multi_tick_byte_write : forall pointer image field old stored frame heap,
  event_pend_multi_tick_byte_field field ->
  image (TCBCommonField field) = Some old -> 0 <= stored < 256 ->
  (tcb_configured_storage_rep true true pointer image ** frame) heap ->
  exists final, kernel_heap_execution [(tcb_field_address pointer field, stored)] heap final /\
    (tcb_configured_storage_rep true true pointer
      (tcb_layout_write image (TCBCommonField field) (Some stored)) ** frame) final.
Proof.
  intros pointer image field old stored frame heap Hfield Hold Hstored Hheap.
  assert (Hsplit : tcb_configured_storage_rep true true pointer image ** frame |--
    tcb_field_address pointer field # UChar |-> old **
    (tcb_configured_storage_without_field true true pointer image (TCBCommonField field) ** frame)).
  { sep_apply_l_atomic (tcb_configured_storage_split_field true true pointer image
      (TCBCommonField field) (tcb_configured_common_field_in true true field)).
    rewrite Hold; unfold event_pend_multi_tick_byte_field in Hfield;
      destruct Hfield as [-> | [-> | [-> | [-> | ->]]]]; cbn [tcb_layout_cell tcb_cell]; entailer!. }
  destruct (kernel_heap_framed_uchar_store _ old stored _ heap Hstored (Hsplit heap Hheap))
    as [final [Hrun Hpost]].
  exists final; split; [exact Hrun|].
  assert (Hmerge : tcb_field_address pointer field # UChar |-> stored **
    (tcb_configured_storage_without_field true true pointer image (TCBCommonField field) ** frame) |--
    tcb_configured_storage_rep true true pointer
      (tcb_layout_write image (TCBCommonField field) (Some stored)) ** frame).
  { pose proof (tcb_configured_storage_merge_updated_field true true pointer image
      (TCBCommonField field) (Some stored) (tcb_configured_common_field_in true true field)) as Hmerge.
    unfold event_pend_multi_tick_byte_field in Hfield;
      destruct Hfield as [-> | [-> | [-> | [-> | ->]]]];
      cbn [tcb_layout_cell tcb_cell] in Hmerge; sep_apply_l_atomic Hmerge; entailer!. }
  exact (Hmerge final Hpost).
Qed.

Definition event_pend_multi_tick_expire_fragment (pointer : addr)
  (before after : model) : Prop :=
  exists bits, uchar_load (tcb_field_address pointer TCBStat) bits before /\
    if task_status_has_pending bits then
      exists cleared,
        kernel_heap_execution [(tcb_field_address pointer TCBStat,
          task_status_clear_wait bits task_pend_any_mask)] before cleared /\
        kernel_heap_execution [(tcb_field_address pointer TCBStatPend,
          encode_pend_status PendTimeout)] cleared after
    else kernel_heap_execution [(tcb_field_address pointer TCBStatPend,
      encode_pend_status PendOK)] before after.

Lemma event_pend_multi_tick_expire_storage_post :
  forall pointer image bits old_result frame heap,
  image (TCBCommonField TCBStat) = Some bits ->
  image (TCBCommonField TCBStatPend) = Some old_result ->
  (tcb_configured_storage_rep true true pointer image ** frame) heap ->
  exists final, event_pend_multi_tick_expire_fragment pointer heap final /\
    (tcb_configured_storage_rep true true pointer (tcb_multi_timeout_image image bits) ** frame) final.
Proof.
  intros pointer image bits old_result frame heap Hbits Hresult Hheap.
  pose proof (event_pend_multi_tick_byte_load pointer image TCBStat bits frame heap
    (or_introl eq_refl) Hbits Hheap) as Hread.
  destruct (task_status_has_pending bits) eqn:Hpending.
  - destruct (event_pend_multi_tick_byte_write pointer image TCBStat bits
      (task_status_clear_wait bits task_pend_any_mask) frame heap
      (or_introl eq_refl) Hbits (task_status_clear_wait_in_range _ _ (proj1 Hread)) Hheap)
      as [cleared [Hclear Hcleared]].
    destruct (event_pend_multi_tick_byte_write pointer
      (tcb_layout_write image (TCBCommonField TCBStat)
        (Some (task_status_clear_wait bits task_pend_any_mask))) TCBStatPend old_result
      (encode_pend_status PendTimeout) frame cleared
      (or_intror (or_introl eq_refl)) Hresult ltac:(cbn; lia) Hcleared)
      as [final [Hpend Hfinal]].
    exists final; split.
    + exists bits; split; [exact Hread|rewrite Hpending; exists cleared; split; assumption].
    + assert (Himage : tcb_layout_write
        (tcb_layout_write image (TCBCommonField TCBStat)
          (Some (task_status_clear_wait bits task_pend_any_mask)))
        (TCBCommonField TCBStatPend) (Some (encode_pend_status PendTimeout)) =
        tcb_multi_timeout_image image bits).
      { apply functional_extensionality; intros [field| | | | | | |];
          try reflexivity; destruct field; unfold tcb_multi_timeout_image,
          tcb_layout_update_common, tcb_expire_status_image; rewrite Hpending; reflexivity. }
      rewrite <- Himage; exact Hfinal.
  - destruct (event_pend_multi_tick_byte_write pointer image TCBStatPend old_result
      (encode_pend_status PendOK) frame heap (or_intror (or_introl eq_refl))
      Hresult ltac:(cbn; lia) Hheap) as [final [Hpend Hfinal]].
    exists final; split.
    + exists bits; split; [exact Hread|rewrite Hpending; exact Hpend].
    + assert (Himage : tcb_layout_write image (TCBCommonField TCBStatPend)
        (Some (encode_pend_status PendOK)) = tcb_multi_timeout_image image bits).
      { apply functional_extensionality; intros [field| | | | | | |];
          try reflexivity; destruct field; unfold tcb_multi_timeout_image,
          tcb_layout_update_common, tcb_expire_status_image; rewrite Hpending; reflexivity. }
      rewrite <- Himage; exact Hfinal.
Qed.

(** Source/os_core.c's Dly test/decrement and expiration fields. The
    bitmap stores below are deliberately a separate following fragment;
    the TCB fragment alone does not assert that the task is ready. *)
Definition event_pend_multi_tick_tcb_fragment (pointer : addr)
  (before after : model) : Prop :=
  exists delay, pointer_load (tcb_field_address pointer TCBDly) delay before /\
    if Z.eqb delay 0 then after = before else
      exists decremented,
        kernel_heap_execution (pointer_store_writes (tcb_field_address pointer TCBDly) (delay - 1))
          before decremented /\
        pointer_load (tcb_field_address pointer TCBDly) (delay - 1) decremented /\
        if Z.eqb (delay - 1) 0 then
          event_pend_multi_tick_expire_fragment pointer decremented after
        else after = decremented.

Lemma event_pend_multi_tick_tcb_storage_post : forall sg pointer task frame heap,
  (tcb_configured_storage_rep true true pointer (task_layout_image sg task) ** frame) heap ->
  exists final, event_pend_multi_tick_tcb_fragment pointer heap final /\
    (tcb_configured_storage_rep true true pointer (task_layout_image sg (tick_task_update task)) ** frame) final.
Proof.
  intros sg pointer task frame heap Hheap.
  pose proof (event_pend_multi_tick_delay_load pointer (task_layout_image sg task)
    task.(dly) frame heap eq_refl Hheap) as Hread.
  destruct (Z.eqb task.(dly) 0) eqn:Hzero.
  - exists heap; split.
    + exists task.(dly); split; [exact Hread|rewrite Hzero; reflexivity].
    + apply Z.eqb_eq in Hzero; rewrite tick_task_zero_delay_eq by exact Hzero; exact Hheap.
  - assert (Hrange : 0 < task.(dly) < 4294967296)
      by (apply Z.eqb_neq in Hzero; destruct Hread as [Hrange _]; lia).
    destruct (event_pend_multi_tick_delay_write pointer (task_layout_image sg task)
      task.(dly) (task.(dly) - 1) frame heap eq_refl ltac:(lia) Hheap)
      as [decremented [Hwrite Hdecremented]].
    pose proof (event_pend_multi_tick_delay_load pointer
      (tcb_layout_write (task_layout_image sg task) (TCBCommonField TCBDly) (Some (task.(dly) - 1)))
      (task.(dly) - 1) frame decremented eq_refl Hdecremented) as HnewRead.
    destruct (Z.eqb (task.(dly) - 1) 0) eqn:Hexpired.
    + destruct (event_pend_multi_tick_expire_storage_post pointer
        (tcb_layout_write (task_layout_image sg task) (TCBCommonField TCBDly) (Some (task.(dly) - 1)))
        (encode_task_status task.(stat)) (encode_pend_status task.(statPend))
        frame decremented eq_refl eq_refl Hdecremented) as [final [Hexecution Hfinal]].
      exists final; split.
      * exists task.(dly); split; [exact Hread|rewrite Hzero; exists decremented].
        split; [exact Hwrite|]. split; [exact HnewRead|rewrite Hexpired; exact Hexecution].
      * rewrite (tick_task_update_layout_image_eq sg task Hrange), Hexpired.
        rewrite event_pend_multi_tick_common_write_image in Hfinal; exact Hfinal.
    + exists decremented; split.
      * exists task.(dly); split; [exact Hread|rewrite Hzero; exists decremented].
        split; [exact Hwrite|]. split; [exact HnewRead|rewrite Hexpired; reflexivity].
      * rewrite (tick_task_update_layout_image_eq sg task Hrange), Hexpired.
        rewrite event_pend_multi_tick_common_write_image in Hdecremented; exact Hdecremented.
Qed.

Lemma event_pend_multi_tick_expire_fragment_deterministic : forall pointer before first second,
  event_pend_multi_tick_expire_fragment pointer before first ->
  event_pend_multi_tick_expire_fragment pointer before second -> first = second.
Proof.
  intros pointer before first second [bits [Hread Hrun]] [bits' [Hread' Hrun']].
  assert (bits = bits') by (eapply uchar_load_deterministic; eassumption); subst bits'.
  destruct (task_status_has_pending bits).
  - destruct Hrun as [cleared [Hclear Hpend]], Hrun' as [cleared' [Hclear' Hpend']].
    assert (cleared = cleared') by (eapply kernel_heap_execution_deterministic; eassumption).
    subst cleared'; eapply kernel_heap_execution_deterministic; eassumption.
  - eapply kernel_heap_execution_deterministic; eassumption.
Qed.

Lemma event_pend_multi_tick_tcb_fragment_deterministic : forall pointer before first second,
  event_pend_multi_tick_tcb_fragment pointer before first ->
  event_pend_multi_tick_tcb_fragment pointer before second -> first = second.
Proof.
  intros pointer before first second [delay [Hread Hrun]] [delay' [Hread' Hrun']].
  assert (delay = delay') by (eapply pointer_load_deterministic; eassumption); subst delay'.
  destruct (Z.eqb delay 0); [congruence|].
  destruct Hrun as [decremented [Hwrite [_ Hrun]]],
    Hrun' as [decremented' [Hwrite' [_ Hrun']]].
  assert (decremented = decremented') by (eapply kernel_heap_execution_deterministic; eassumption).
  subst decremented'; destruct (Z.eqb (delay - 1) 0); [|congruence].
  eapply event_pend_multi_tick_expire_fragment_deterministic; eassumption.
Qed.

(** The source executes these stores only after the delay reached zero.
    It tests the actual new Stat byte, not whether every event pending bit
    is absent. Group is written before the selected row. *)
Definition event_pend_multi_tick_ready_fragment (sg : StableGlobVars) (pointer : addr)
  (before after : model) : Prop :=
  exists bits, uchar_load (tcb_field_address pointer TCBStat) bits before /\
    if task_status_is_suspended bits then after = before else
      exists bit_y group grouped y bit_x row,
        uchar_load (tcb_field_address pointer TCBBitY) bit_y before /\
        uchar_load sg.(g_OSRdyGrp) group before /\
        kernel_heap_execution [(sg.(g_OSRdyGrp), Z.lor group bit_y)] before grouped /\
        uchar_load (tcb_field_address pointer TCBY) y grouped /\
        uchar_load (tcb_field_address pointer TCBBitX) bit_x grouped /\
        uchar_load (sg.(g_OSRdyTbl) + y * sizeof(UCHAR)) row grouped /\
        kernel_heap_execution [(sg.(g_OSRdyTbl) + y * sizeof(UCHAR), Z.lor row bit_x)] grouped after.

Lemma event_pend_multi_tick_ready_storage_post :
  forall sg pointer image bits y bit_x bit_y group rows frame heap,
  image (TCBCommonField TCBStat) = Some bits ->
  image (TCBCommonField TCBY) = Some y ->
  image (TCBCommonField TCBBitX) = Some bit_x ->
  image (TCBCommonField TCBBitY) = Some bit_y -> 0 <= y < 8 ->
  (tcb_configured_storage_rep true true pointer image **
    sg.(g_OSRdyGrp) # UChar |-> group ** UCharArray.full sg.(g_OSRdyTbl) 8 rows ** frame) heap ->
  exists final, event_pend_multi_tick_ready_fragment sg pointer heap final /\
    (tcb_configured_storage_rep true true pointer image **
      sg.(g_OSRdyGrp) # UChar |-> (if task_status_is_suspended bits then group else Z.lor group bit_y) **
      UCharArray.full sg.(g_OSRdyTbl) 8
        (if task_status_is_suspended bits then rows
         else replace_Znth y (Z.lor (Znth y rows 0) bit_x) rows) ** frame) final.
Proof.
  intros sg pointer image bits y bit_x bit_y group rows frame heap
    Hbits Hy HbitX HbitY Hrow Hheap.
  assert (Hordered : tcb_configured_storage_rep true true pointer image **
      sg.(g_OSRdyGrp) # UChar |-> group ** UCharArray.full sg.(g_OSRdyTbl) 8 rows ** frame |--
    tcb_configured_storage_rep true true pointer image **
      (sg.(g_OSRdyGrp) # UChar |-> group ** UCharArray.full sg.(g_OSRdyTbl) 8 rows ** frame)) by entailer!.
  pose proof (event_pend_multi_tick_byte_load pointer image TCBStat bits _ heap
    (or_introl eq_refl) Hbits (Hordered heap Hheap)) as HreadBits.
  destruct (task_status_is_suspended bits) eqn:Hsuspended.
  - exists heap; split; [exists bits; split; [exact HreadBits|rewrite Hsuspended; reflexivity]|exact Hheap].
  - pose proof (event_pend_multi_tick_byte_load pointer image TCBBitY bit_y _ heap
      (or_intror (or_intror (or_intror (or_intror eq_refl)))) HbitY (Hordered heap Hheap)) as HreadBitY.
    assert (HgroupSplit : tcb_configured_storage_rep true true pointer image **
        sg.(g_OSRdyGrp) # UChar |-> group ** UCharArray.full sg.(g_OSRdyTbl) 8 rows ** frame |--
      sg.(g_OSRdyGrp) # UChar |-> group **
        (tcb_configured_storage_rep true true pointer image ** UCharArray.full sg.(g_OSRdyTbl) 8 rows ** frame))
      by entailer!.
    pose proof (framed_uchar_store_load _ _ _ _ (HgroupSplit heap Hheap)) as HreadGroup.
    assert (HgroupRange : 0 <= Z.lor group bit_y < 256).
    { change 256 with (2^8); apply bitmap_lor_in_range; [lia|exact (proj1 HreadGroup)|exact (proj1 HreadBitY)]. }
    destruct (kernel_heap_framed_uchar_store _ group (Z.lor group bit_y) _ heap
      HgroupRange (HgroupSplit heap Hheap)) as [grouped [HgroupWrite Hgrouped]].
    assert (HgroupOrder : sg.(g_OSRdyGrp) # UChar |-> Z.lor group bit_y **
        (tcb_configured_storage_rep true true pointer image ** UCharArray.full sg.(g_OSRdyTbl) 8 rows ** frame) |--
      tcb_configured_storage_rep true true pointer image **
        (sg.(g_OSRdyGrp) # UChar |-> Z.lor group bit_y ** UCharArray.full sg.(g_OSRdyTbl) 8 rows ** frame))
      by entailer!.
    pose proof (event_pend_multi_tick_byte_load pointer image TCBY y _ grouped
      (or_intror (or_intror (or_introl eq_refl))) Hy (HgroupOrder grouped Hgrouped)) as HreadY.
    pose proof (event_pend_multi_tick_byte_load pointer image TCBBitX bit_x _ grouped
      (or_intror (or_intror (or_intror (or_introl eq_refl)))) HbitX (HgroupOrder grouped Hgrouped)) as HreadBitX.
    assert (HrowSplit : sg.(g_OSRdyGrp) # UChar |-> Z.lor group bit_y **
        (tcb_configured_storage_rep true true pointer image ** UCharArray.full sg.(g_OSRdyTbl) 8 rows ** frame) |--
      (sg.(g_OSRdyTbl) + y * sizeof(UCHAR)) # UChar |-> Znth y rows 0 **
        (UCharArray.missing_i sg.(g_OSRdyTbl) y 0 8 rows **
         tcb_configured_storage_rep true true pointer image **
         sg.(g_OSRdyGrp) # UChar |-> Z.lor group bit_y ** frame)).
    { sep_apply_l_atomic (UCharArray.full_split_to_missing_i sg.(g_OSRdyTbl) y 8 rows 0 Hrow); entailer!. }
    pose proof (framed_uchar_store_load _ _ _ _ (HrowSplit grouped Hgrouped)) as HreadRow.
    assert (HrowRange : 0 <= Z.lor (Znth y rows 0) bit_x < 256).
    { change 256 with (2^8); apply bitmap_lor_in_range; [lia|exact (proj1 HreadRow)|exact (proj1 HreadBitX)]. }
    destruct (kernel_heap_framed_uchar_store _ (Znth y rows 0) (Z.lor (Znth y rows 0) bit_x) _ grouped
      HrowRange (HrowSplit grouped Hgrouped)) as [final [HrowWrite Hfinal]].
    exists final; split.
    + exists bits; split; [exact HreadBits|rewrite Hsuspended].
      exists bit_y, group, grouped, y, bit_x, (Znth y rows 0).
      split; [exact HreadBitY|]. split; [exact HreadGroup|].
      split; [exact HgroupWrite|]. split; [exact HreadY|].
      split; [exact HreadBitX|]. split; [exact HreadRow|exact HrowWrite].
    + assert (Hmerge : (sg.(g_OSRdyTbl) + y * sizeof(UCHAR)) # UChar |-> Z.lor (Znth y rows 0) bit_x **
          (UCharArray.missing_i sg.(g_OSRdyTbl) y 0 8 rows **
           tcb_configured_storage_rep true true pointer image **
           sg.(g_OSRdyGrp) # UChar |-> Z.lor group bit_y ** frame) |--
        tcb_configured_storage_rep true true pointer image **
          sg.(g_OSRdyGrp) # UChar |-> Z.lor group bit_y **
          UCharArray.full sg.(g_OSRdyTbl) 8 (replace_Znth y (Z.lor (Znth y rows 0) bit_x) rows) ** frame).
      { sep_apply_l_atomic (UCharArray.missing_i_merge_to_full sg.(g_OSRdyTbl) y 8
          (Z.lor (Znth y rows 0) bit_x) rows Hrow); entailer!. }
      exact (Hmerge final Hfinal).
Qed.

Definition event_pend_multi_tick_body_frame sg state tid : Assertion :=
  task_public_storage_without_task sg state.(TskState) tid **
  sched_physical_rep sg state.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg state.

Lemma event_pend_multi_tick_body_split : forall sg state tid task,
  full_features_kernel_profile sg -> state.(TskState).(inUsedTaskStates) tid = Some task ->
  UCOS2_raw_rep sg state |--
  tcb_configured_storage_rep true true (task_slot_addr sg tid) (task_layout_image sg task) **
    (sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
     UCharArray.full sg.(g_OSRdyTbl) 8 (sched_row_values state.(TskState) state.(SchedState).(readyList)) **
     event_pend_multi_tick_body_frame sg state tid).
Proof.
  intros sg state tid task Hprofile Htask.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = true)
    by (unfold full_features_kernel_profile in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = true)
    by (unfold full_features_kernel_profile in Hprofile; tauto).
  unfold UCOS2_raw_rep, task_shared_rep.
  sep_apply_l_atomic (task_public_storage_split_task sg state.(TskState) tid task Htask).
  unfold used_task_rep, task_slot_storage_rep; rewrite Hmulti, Hprofiling.
  unfold sched_raw_rep; rewrite sched_rows_array_equiv.
  unfold event_pend_multi_tick_body_frame, UCOS2_raw_rep_missing_task_storage_sched; entailer!.
Qed.

Lemma event_pend_multi_tick_body_merge : forall sg state tid task,
  UCOS2_full_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some task ->
  let after := tick_task_step sg tid task state in
  tcb_configured_storage_rep true true (task_slot_addr sg tid) (task_layout_image sg (tick_task_update task)) **
    sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp after.(SchedState).(readyList) after.(TskState) **
    UCharArray.full sg.(g_OSRdyTbl) 8 (sched_row_values after.(TskState) after.(SchedState).(readyList)) **
    event_pend_multi_tick_body_frame sg state tid |-- UCOS2_full_inv sg after.
Proof.
  intros sg state tid task Hvalid Htask after.
  pose proof (event_pend_multi_tick_step_preserves_full_state sg state tid task Hvalid Htask) as Hafter.
  fold after in Hafter.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = true)
    by (destruct Hvalid as [Hprofile _]; unfold full_features_kernel_profile in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = true)
    by (destruct Hvalid as [Hprofile _]; unfold full_features_kernel_profile in Hprofile; tauto).
  assert (Hstorage : tcb_configured_storage_rep true true (task_slot_addr sg tid)
    (task_layout_image sg (tick_task_update task)) = used_task_rep sg tid (tick_task_update task)).
  { unfold used_task_rep, task_slot_storage_rep; rewrite Hmulti, Hprofiling; reflexivity. }
  rewrite Hstorage; unfold event_pend_multi_tick_body_frame.
  assert (HmergeTask : forall group rows,
    used_task_rep sg tid (tick_task_update task) ** sg.(g_OSRdyGrp) # UChar |-> group **
      UCharArray.full sg.(g_OSRdyTbl) 8 rows **
      (task_public_storage_without_task sg state.(TskState) tid **
       sched_physical_rep sg state.(SchedState) ** UCOS2_raw_rep_missing_task_storage_sched sg state) |--
    task_public_storage sg (glob_task_set_usedtask state.(TskState) tid (tick_task_update task)) **
      sg.(g_OSRdyGrp) # UChar |-> group ** UCharArray.full sg.(g_OSRdyTbl) 8 rows **
      sched_physical_rep sg state.(SchedState) ** UCOS2_raw_rep_missing_task_storage_sched sg state).
  { intros; sepcon_assoc_change.
    sep_apply_r_atomic (task_public_storage_merge_updated_task sg state.(TskState) tid (tick_task_update task));
      entailer!. }
  assert (Hfinish :
    task_public_storage sg (glob_task_set_usedtask state.(TskState) tid (tick_task_update task)) **
      sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp after.(SchedState).(readyList) after.(TskState) **
      UCharArray.full sg.(g_OSRdyTbl) 8 (sched_row_values after.(TskState) after.(SchedState).(readyList)) **
      sched_physical_rep sg state.(SchedState) ** UCOS2_raw_rep_missing_task_storage_sched sg state |--
    UCOS2_full_inv sg after).
  { rewrite <- (tick_task_step_task_state_eq sg tid task state Htask); fold after.
    assert (Hphysical : sched_physical_rep sg after.(SchedState) = sched_physical_rep sg state.(SchedState)).
    { unfold after, tick_task_step; destruct (Z.eqb task.(dly) 0); [reflexivity|].
      destruct (Z.eqb (tick_task_update task).(dly) 0); [|reflexivity].
      apply sched_wake_by_status_physical_rep_eq. }
    rewrite <- Hphysical.
    rewrite (time_tick_task_step_preserves_residual sg state tid task Htask); fold after.
    unfold UCOS2_full_inv, UCOS2_raw_rep, task_shared_rep,
      UCOS2_raw_rep_missing_task_storage_sched, sched_raw_rep.
    rewrite sched_rows_array_equiv; entailer!. }
  intros physical Howned; apply (Hfinish physical).
  exact (HmergeTask _ _ physical Howned).
Qed.

(** One masked task body from the original OSTimeTick. The surrounding
    hook, global time/step, list/idle reads and next-pointer/Restore remain
    separate source cuts. The local pointer is supplied by that caller. *)
Definition event_pend_multi_tick_body_fragment (sg : StableGlobVars) (pointer : addr)
  (before after : model) : Prop :=
  exists delay, pointer_load (tcb_field_address pointer TCBDly) delay before /\
    if Z.eqb delay 0 then after = before else
      exists decremented,
        kernel_heap_execution (pointer_store_writes (tcb_field_address pointer TCBDly) (delay - 1))
          before decremented /\
        pointer_load (tcb_field_address pointer TCBDly) (delay - 1) decremented /\
        if Z.eqb (delay - 1) 0 then
          exists expired, event_pend_multi_tick_expire_fragment pointer decremented expired /\
            event_pend_multi_tick_ready_fragment sg pointer expired after
        else after = decremented.

Lemma event_pend_multi_tick_body_full_post : forall sg state tid task heap,
  state.(TskState).(inUsedTaskStates) tid = Some task -> UCOS2_full_inv sg state heap ->
  exists final, event_pend_multi_tick_body_fragment sg (task_slot_addr sg tid) heap final /\
    UCOS2_full_inv sg (tick_task_step sg tid task state) final.
Proof.
  intros sg state tid task heap Htask Hheap; pose proof Hheap as [Hvalid Hraw].
  pose proof (event_pend_multi_tick_body_split sg state tid task (proj1 Hvalid) Htask heap Hraw) as Hsplit.
  pose proof (event_pend_multi_tick_delay_load (task_slot_addr sg tid) (task_layout_image sg task)
    task.(dly) _ heap eq_refl Hsplit) as HdelayRead.
  destruct (Z.eqb task.(dly) 0) eqn:Hzero.
  - exists heap; split.
    + exists task.(dly); split; [exact HdelayRead|rewrite Hzero; reflexivity].
    + unfold tick_task_step; rewrite Hzero; exact Hheap.
  - assert (Hy : 0 <= time_tick_y task < 8).
    { pose proof (proj1 Hvalid) as Hprofile; pose proof (proj1 (proj2 Hvalid)) as Htasks.
      destruct Htasks as [_ [_ [_ [_ [_ [_ [_ [Hpriority _]]]]]]]].
      specialize (Hpriority tid task Htask); unfold task_priority_in_range in Hpriority.
      assert (Hprio : 0 <= task.(curPrio) < 64)
        by (unfold full_features_kernel_profile, valid_stable_glob_vars in Hprofile; intuition lia).
      unfold time_tick_y, tcb_y_of_prio; split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
    assert (HnewPriority : (tick_task_update task).(curPrio) = task.(curPrio))
      by (unfold tick_task_update; rewrite Hzero; reflexivity).
    assert (HnewDelay : (tick_task_update task).(dly) = task.(dly) - 1)
      by (unfold tick_task_update; rewrite Hzero; reflexivity).
    destruct (time_tick_task_step_ready_encoding__task_update_backedges sg state tid task Htask Hy)
      as [Hgroup Hrows].
    cbn zeta in Hgroup, Hrows; rewrite Hzero, HnewDelay in Hgroup, Hrows.
    destruct (event_pend_multi_tick_tcb_storage_post sg (task_slot_addr sg tid) task _ heap Hsplit)
      as [middle [[delay [Hread Hrun]] Hmiddle]].
    assert (delay = task.(dly)) by (eapply pointer_load_deterministic; eassumption); subst delay.
    rewrite Hzero in Hrun; destruct Hrun as [decremented [Hwrite [HnewRead Hrun]]].
    assert (Horder : forall image group rows,
      tcb_configured_storage_rep true true (task_slot_addr sg tid) image **
        (sg.(g_OSRdyGrp) # UChar |-> group ** UCharArray.full sg.(g_OSRdyTbl) 8 rows **
         event_pend_multi_tick_body_frame sg state tid) |--
      tcb_configured_storage_rep true true (task_slot_addr sg tid) image **
        sg.(g_OSRdyGrp) # UChar |-> group ** UCharArray.full sg.(g_OSRdyTbl) 8 rows **
        event_pend_multi_tick_body_frame sg state tid) by (intros; entailer!).
    pose proof (event_pend_multi_tick_body_merge sg state tid task Hvalid Htask) as Hmerge; cbn zeta in Hmerge.
    destruct (Z.eqb (task.(dly) - 1) 0) eqn:Hexpired.
    + destruct (event_pend_multi_tick_ready_storage_post sg (task_slot_addr sg tid)
        (task_layout_image sg (tick_task_update task))
        (encode_task_status (tick_task_update task).(stat))
        (tcb_y_of_prio (tick_task_update task).(curPrio))
        (tcb_bit_x_of_prio (tick_task_update task).(curPrio))
        (tcb_bit_y_of_prio (tick_task_update task).(curPrio))
        (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
        (sched_row_values state.(TskState) state.(SchedState).(readyList))
        (event_pend_multi_tick_body_frame sg state tid) middle eq_refl eq_refl eq_refl eq_refl
        ltac:(rewrite HnewPriority; exact Hy) (Horder _ _ _ middle Hmiddle))
        as [final [Hready Hfinal]].
      exists final; split.
      * exists task.(dly); split; [exact HdelayRead|rewrite Hzero; exists decremented].
        split; [exact Hwrite|]. split; [exact HnewRead|rewrite Hexpired; exists middle; split; assumption].
      * unfold time_tick_ready_group, time_tick_ready_rows, time_tick_y,
          time_tick_bit_y, time_tick_bit_x in Hgroup, Hrows.
        rewrite Hgroup, Hrows in Hmerge; rewrite HnewPriority in Hfinal.
        exact (Hmerge final Hfinal).
    + subst middle.
      exists decremented; split.
      * exists task.(dly); split; [exact HdelayRead|rewrite Hzero; exists decremented].
        split; [exact Hwrite|]. split; [exact HnewRead|rewrite Hexpired; reflexivity].
      * unfold time_tick_ready_group, time_tick_ready_rows in Hgroup, Hrows.
        rewrite Hgroup, Hrows in Hmerge; exact (Hmerge decremented (Horder _ _ _ decremented Hmiddle)).
Qed.

Lemma event_pend_multi_tick_ready_fragment_deterministic : forall sg pointer before first second,
  event_pend_multi_tick_ready_fragment sg pointer before first ->
  event_pend_multi_tick_ready_fragment sg pointer before second -> first = second.
Proof.
  intros sg pointer before first second [bits [Hbits Hrun]] [bits' [Hbits' Hrun']].
  assert (bits = bits') by (eapply uchar_load_deterministic; eassumption); subst bits'.
  destruct (task_status_is_suspended bits); [congruence|].
  destruct Hrun as [bit_y [group [grouped [y [bit_x [row
    [HbitY [Hgroup [HwriteGroup [Hy [HbitX [Hrow HwriteRow]]]]]]]]]]]],
    Hrun' as [bit_y' [group' [grouped' [y' [bit_x' [row'
    [HbitY' [Hgroup' [HwriteGroup' [Hy' [HbitX' [Hrow' HwriteRow']]]]]]]]]]]].
  assert (bit_y = bit_y') by (eapply uchar_load_deterministic; eassumption); subst bit_y'.
  assert (group = group') by (eapply uchar_load_deterministic; eassumption); subst group'.
  assert (grouped = grouped') by (eapply kernel_heap_execution_deterministic; eassumption); subst grouped'.
  assert (y = y') by (eapply uchar_load_deterministic; eassumption); subst y'.
  assert (bit_x = bit_x') by (eapply uchar_load_deterministic; eassumption); subst bit_x'.
  assert (row = row') by (eapply uchar_load_deterministic; eassumption); subst row'.
  eapply kernel_heap_execution_deterministic; eassumption.
Qed.

Lemma event_pend_multi_tick_body_fragment_deterministic : forall sg pointer before first second,
  event_pend_multi_tick_body_fragment sg pointer before first ->
  event_pend_multi_tick_body_fragment sg pointer before second -> first = second.
Proof.
  intros sg pointer before first second [delay [Hread Hrun]] [delay' [Hread' Hrun']].
  assert (delay = delay') by (eapply pointer_load_deterministic; eassumption); subst delay'.
  destruct (Z.eqb delay 0); [congruence|].
  destruct Hrun as [decremented [Hwrite [_ Hrun]]],
    Hrun' as [decremented' [Hwrite' [_ Hrun']]].
  assert (decremented = decremented') by (eapply kernel_heap_execution_deterministic; eassumption).
  subst decremented'; destruct (Z.eqb (delay - 1) 0); [|congruence].
  destruct Hrun as [expired [Hexpire Hready]], Hrun' as [expired' [Hexpire' Hready']].
  assert (expired = expired') by (eapply event_pend_multi_tick_expire_fragment_deterministic; eassumption).
  subst expired'; eapply event_pend_multi_tick_ready_fragment_deterministic; eassumption.
Qed.

Lemma event_pend_multi_tick_expire_fragment_frame : forall pointer before after frame whole,
  event_pend_multi_tick_expire_fragment pointer before after -> join before frame whole ->
  exists final, event_pend_multi_tick_expire_fragment pointer whole final /\ join after frame final.
Proof.
  intros pointer before after frame whole [bits [Hread Hrun]] Hjoin.
  pose proof (uchar_load_frame _ _ _ _ _ Hread Hjoin) as HwholeRead.
  destruct (task_status_has_pending bits) eqn:Hpending.
  - destruct Hrun as [cleared [Hclear Hpend]].
    destruct (kernel_heap_execution_frame _ _ _ _ _ Hclear Hjoin) as [clearedWhole [HclearWhole HclearedJoin]].
    destruct (kernel_heap_execution_frame _ _ _ _ _ Hpend HclearedJoin) as [final [HpendWhole Hfinal]].
    exists final; split; [|exact Hfinal].
    exists bits; split; [exact HwholeRead|rewrite Hpending; exists clearedWhole; split; assumption].
  - destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin) as [final [Hwhole Hfinal]].
    exists final; split; [|exact Hfinal].
    exists bits; split; [exact HwholeRead|rewrite Hpending; exact Hwhole].
Qed.

Lemma event_pend_multi_tick_ready_fragment_frame : forall sg pointer before after frame whole,
  event_pend_multi_tick_ready_fragment sg pointer before after -> join before frame whole ->
  exists final, event_pend_multi_tick_ready_fragment sg pointer whole final /\ join after frame final.
Proof.
  intros sg pointer before after frame whole [bits [Hread Hrun]] Hjoin.
  pose proof (uchar_load_frame _ _ _ _ _ Hread Hjoin) as HwholeRead.
  destruct (task_status_is_suspended bits) eqn:Hsuspended.
  - subst after; exists whole; split; [|exact Hjoin].
    exists bits; split; [exact HwholeRead|rewrite Hsuspended; reflexivity].
  - destruct Hrun as [bit_y [group [grouped [y [bit_x [row
      [HbitY [Hgroup [HwriteGroup [Hy [HbitX [Hrow HwriteRow]]]]]]]]]]]].
    destruct (kernel_heap_execution_frame _ _ _ _ _ HwriteGroup Hjoin)
      as [groupedWhole [HwriteGroupWhole HgroupedJoin]].
    destruct (kernel_heap_execution_frame _ _ _ _ _ HwriteRow HgroupedJoin)
      as [final [HwriteRowWhole Hfinal]].
    exists final; split; [|exact Hfinal].
    exists bits; split; [exact HwholeRead|rewrite Hsuspended].
    exists bit_y, group, groupedWhole, y, bit_x, row.
    split; [eapply uchar_load_frame; eassumption|].
    split; [eapply uchar_load_frame; eassumption|].
    split; [exact HwriteGroupWhole|].
    split; [eapply uchar_load_frame; eassumption|].
    split; [eapply uchar_load_frame; eassumption|].
    split; [eapply uchar_load_frame; eassumption|exact HwriteRowWhole].
Qed.

Lemma event_pend_multi_tick_body_fragment_frame : forall sg pointer before after frame whole,
  event_pend_multi_tick_body_fragment sg pointer before after -> join before frame whole ->
  exists final, event_pend_multi_tick_body_fragment sg pointer whole final /\ join after frame final.
Proof.
  intros sg pointer before after frame whole [delay [Hread Hrun]] Hjoin.
  pose proof (pointer_load_frame _ _ _ _ _ Hread Hjoin) as HwholeRead.
  destruct (Z.eqb delay 0) eqn:Hzero.
  - subst after; exists whole; split; [|exact Hjoin].
    exists delay; split; [exact HwholeRead|rewrite Hzero; reflexivity].
  - destruct Hrun as [decremented [Hwrite [HnewRead Hrun]]].
    destruct (kernel_heap_execution_frame _ _ _ _ _ Hwrite Hjoin)
      as [decrementedWhole [HwriteWhole HdecrementedJoin]].
    pose proof (pointer_load_frame _ _ _ _ _ HnewRead HdecrementedJoin) as HwholeNewRead.
    destruct (Z.eqb (delay - 1) 0) eqn:Hexpired.
    + destruct Hrun as [expired [Hexpire Hready]].
      destruct (event_pend_multi_tick_expire_fragment_frame _ _ _ _ _ Hexpire HdecrementedJoin)
        as [expiredWhole [HexpireWhole HexpiredJoin]].
      destruct (event_pend_multi_tick_ready_fragment_frame _ _ _ _ _ _ Hready HexpiredJoin)
        as [final [HreadyWhole Hfinal]].
      exists final; split; [|exact Hfinal].
      exists delay; split; [exact HwholeRead|rewrite Hzero; exists decrementedWhole].
      split; [exact HwriteWhole|]. split; [exact HwholeNewRead|rewrite Hexpired].
      exists expiredWhole; split; assumption.
    + subst after; exists decrementedWhole; split; [|exact HdecrementedJoin].
      exists delay; split; [exact HwholeRead|rewrite Hzero; exists decrementedWhole].
      split; [exact HwriteWhole|]. split; [exact HwholeNewRead|rewrite Hexpired; reflexivity].
Qed.

Lemma event_pend_multi_tick_body_full_frame_post : forall sg state tid task frame whole,
  state.(TskState).(inUsedTaskStates) tid = Some task ->
  (UCOS2_full_inv sg state ** frame) whole ->
  exists final, event_pend_multi_tick_body_fragment sg (task_slot_addr sg tid) whole final /\
    (UCOS2_full_inv sg (tick_task_step sg tid task state) ** frame) final.
Proof.
  intros sg state tid task frame whole Htask [owned [rest [Hjoin [Howned Hrest]]]].
  destruct (event_pend_multi_tick_body_full_post sg state tid task owned Htask Howned)
    as [after [Hrun Hafter]].
  destruct (event_pend_multi_tick_body_fragment_frame _ _ _ _ _ _ Hrun Hjoin)
    as [final [Hwhole Hfinal]].
  exists final; split; [exact Hwhole|].
  exists after, rest; split; [exact Hfinal|]; split; assumption.
Qed.

(** A consumer of the actual execution endpoint. The constructed proof
    heap is identified with it by determinism, not granted as an unrelated
    matching snapshot. The caller's private array/continuation resources
    can be the frame and are returned from the very same physical run. *)
Lemma event_pend_multi_tick_body_preserves_full_inv : forall sg state tid task frame before after,
  state.(TskState).(inUsedTaskStates) tid = Some task ->
  (UCOS2_full_inv sg state ** frame) before ->
  event_pend_multi_tick_body_fragment sg (task_slot_addr sg tid) before after ->
  (UCOS2_full_inv sg (tick_task_step sg tid task state) ** frame) after.
Proof.
  intros sg state tid task frame before after Htask Hbefore Hrun.
  destruct (event_pend_multi_tick_body_full_frame_post sg state tid task frame before Htask Hbefore)
    as [constructed [Hconstructed Hpost]].
  assert (constructed = after)
    by (eapply event_pend_multi_tick_body_fragment_deterministic; eassumption).
  subst constructed; exact Hpost.
Qed.

