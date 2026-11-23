Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_recycle_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_owner_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_proofs.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations KernelHeapObservation KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Only the fields written by the selected single-Event OS_EventTaskRdy
    and its OS_EventTaskRemove callee. Multi-byte effects are one typed
    source store, using the existing ARM32 little-endian storage rules. *)
Definition mutex_del_wake_tcb_writable (field : TCBField) : Prop :=
  In field [TCBDly; TCBMsg; TCBStat; TCBStatPend; TCBEventPtr].

Definition mutex_del_wake_tcb_writes (pointer : Z) (field : TCBField) (stored : Z)
  : list (addr * Mem.byte) :=
  match field with
  | TCBDly | TCBMsg | TCBEventPtr => pointer_store_writes (tcb_field_address pointer field) stored
  | _ => [(tcb_field_address pointer field, stored)]
  end.

Definition mutex_del_wake_tcb_value_in_range (field : TCBField) (stored : Z) : Prop :=
  0 <= stored < match field with TCBDly | TCBMsg | TCBEventPtr => 4294967296 | _ => 256 end.

Lemma mutex_del_wake_tcb_cell_store : forall pointer field old stored before (frame : Assertion),
  mutex_del_wake_tcb_writable field -> mutex_del_wake_tcb_value_in_range field stored ->
  (tcb_cell pointer field old ** frame) before ->
  exists after, kernel_heap_execution (mutex_del_wake_tcb_writes pointer field stored) before after /\
    (tcb_cell pointer field (Some stored) ** frame) after.
Proof.
  intros pointer field old stored before frame Hfield Hrange Hpre.
  assert (Hforget : tcb_cell pointer field old |-- tcb_cell pointer field None).
  { unfold mutex_del_wake_tcb_writable in Hfield.
    destruct field; simpl in Hfield; try solve [intuition discriminate]; destruct old; cbn [tcb_cell];
      first [apply store_uchar_undef_store_uchar | apply store_ptr_undef_store_ptr |
        apply store_uint_undef_store_uint | apply store_ushort_undef_store_ushort | reflexivity]. }
  assert (Hopen : tcb_cell pointer field old ** frame |-- tcb_cell pointer field None ** frame).
  { sep_apply_l_atomic Hforget; entailer!. }
  pose proof (Hopen before Hpre) as Howned.
  unfold mutex_del_wake_tcb_writable in Hfield.
  destruct field; simpl in Hfield; try solve [intuition discriminate];
    cbn [mutex_del_wake_tcb_value_in_range] in Hrange;
    cbn [tcb_cell mutex_del_wake_tcb_writes] in Howned |- *;
    first [eapply framed_uchar_noninit_store_execution | eapply framed_pointer_store_execution |
      eapply task_stack_uint_store_execution]; eassumption.
Qed.

Lemma mutex_del_wake_tcb_store : forall pointer image field stored before after (frame : Assertion),
  mutex_del_wake_tcb_writable field -> mutex_del_wake_tcb_value_in_range field stored ->
  (tcb64_storage_rep pointer image ** frame) before ->
  kernel_heap_execution (mutex_del_wake_tcb_writes pointer field stored) before after ->
  (tcb64_storage_rep pointer (tcb_write image field (Some stored)) ** frame) after.
Proof.
  intros pointer image field stored before after frame Hfield Hrange Hpre Hrun.
  assert (Hopen : tcb64_storage_rep pointer image ** frame |--
    tcb_cell pointer field (image field) ** (tcb64_storage_without pointer field image ** frame)).
  { sep_apply_l_atomic (tcb64_storage_split pointer image field); entailer!. }
  destruct (mutex_del_wake_tcb_cell_store pointer field (image field) stored before
    (tcb64_storage_without pointer field image ** frame) Hfield Hrange (Hopen before Hpre))
    as [produced [Hwrite Hproduced]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hclose : tcb_cell pointer field (Some stored) ** (tcb64_storage_without pointer field image ** frame) |--
    tcb64_storage_rep pointer (tcb_write image field (Some stored)) ** frame).
  { sep_apply_l_atomic (tcb64_storage_merge_updated pointer image field (Some stored)); entailer!. }
  exact (Hclose after Hproduced).
Qed.

Lemma mutex_del_wake_tcb_byte_load : forall pointer image field observed before (frame : Assertion),
  In field [TCBStat; TCBY; TCBBitX; TCBBitY] -> image field = Some observed ->
  (tcb64_storage_rep pointer image ** frame) before ->
  uchar_load (tcb_field_address pointer field) observed before.
Proof.
  intros pointer image field observed before frame Hfield Himage Hpre.
  assert (Hopen : tcb64_storage_rep pointer image ** frame |--
    tcb_field_address pointer field # UChar |-> observed ** TT).
  { sep_apply_l_atomic (tcb64_storage_split pointer image field); rewrite Himage.
    destruct field; simpl in Hfield; try solve [intuition discriminate];
      cbn [tcb_cell]; entailer!; intros ? ?; exact I. }
  eapply framed_uchar_store_load; exact (Hopen before Hpre).
Qed.

Lemma mutex_del_wake_array_load : forall address length values index before (frame : Assertion),
  0 <= index < length -> (UCharArray.full address length values ** frame) before ->
  uchar_load (address + index) (Znth index values 0) before.
Proof.
  intros address length values index before frame Hindex Hpre.
  assert (Hopen : UCharArray.full address length values ** frame |--
    (address + index) # UChar |-> Znth index values 0 ** TT).
  { sep_apply_l_atomic (UCharArray.full_split_to_missing_i address index length values 0 Hindex).
    unfold StoreUCharAsElement.storeA; replace (address + index * sizeof(UCHAR)) with (address + index) by (cbn; lia).
    entailer!; intros ? ?; exact I. }
  eapply framed_uchar_store_load; exact (Hopen before Hpre).
Qed.

Lemma mutex_del_wake_array_store : forall address length values index stored before after (frame : Assertion),
  0 <= index < length -> 0 <= stored < 256 ->
  (UCharArray.full address length values ** frame) before ->
  kernel_heap_execution [(address + index, stored)] before after ->
  (UCharArray.full address length (replace_Znth index stored values) ** frame) after.
Proof.
  intros address length values index stored before after frame Hindex Hrange Hpre Hrun.
  set (residual := UCharArray.missing_i address index 0 length values ** frame).
  assert (Hopen : UCharArray.full address length values ** frame |--
    (address + index) # UChar |-> Znth index values 0 ** residual).
  { unfold residual; sep_apply_l_atomic (UCharArray.full_split_to_missing_i address index length values 0 Hindex).
    unfold StoreUCharAsElement.storeA; replace (address + index * sizeof(UCHAR)) with (address + index) by (cbn; lia).
    entailer!. }
  destruct (kernel_heap_framed_uchar_store _ _ stored residual before Hrange (Hopen before Hpre))
    as [produced [Hwrite Hproduced]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hclose : (address + index) # UChar |-> stored ** residual |--
    UCharArray.full address length (replace_Znth index stored values) ** frame).
  { unfold residual; replace (address + index) with (address + index * sizeof(UCHAR)) by (cbn; lia).
    sep_apply_l_atomic (UCharArray.missing_i_merge_to_full address index length stored values Hindex); entailer!. }
  exact (Hclose after Hproduced).
Qed.

(** The read-only selector uses the current physical ECB bitmap and both
    actual lookup tables. It has no assumed canonical waiter identity. *)
Definition mutex_del_wake_selection_execution (sg : StableGlobVars) (pe pointer row priority : Z)
  (heap : model) : Prop :=
  exists group bits column,
    uchar_load (pe + OSEventGrp_off) group heap /\
    uchar_load (sg.(g_OSUnMapTbl) + group) row heap /\
    uchar_load (pe + OSEventTbl_off + row) bits heap /\
    uchar_load (sg.(g_OSUnMapTbl) + bits) column heap /\
    priority = row * 8 + column /\
    pointer_load (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) pointer heap.

Lemma mutex_del_wake_selection_resources : forall sg tasks eid event tid task group rows pointer row priority
  before (frame : Assertion),
  (event_task_rdy_pre sg tasks eid event tid task 16 2 group rows ** frame) before ->
  mutex_del_wake_selection_execution sg (event_addr sg eid) pointer row priority before ->
  pointer = task_slot_addr sg tid /\ row = tcb_y_of_prio task.(curPrio) /\ priority = task.(curPrio).
Proof.
  intros sg tasks eid event tid task group rows pointer row priority before frame Hpre
    (observed_group & bits & column & Hgroup & Hy & Hrow & Hx & Hpriority & Hpointer).
  assert (Hopen : event_task_rdy_pre sg tasks eid event tid task 16 2 group rows ** frame |--
    coq_prop (event_task_rdy_entry sg tasks eid event tid task) &&
    (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid) (event_image sg tasks event) **
     unmap_table_rep sg ** store_prio_tbl sg tasks.(prioTbl) ** TT)).
  { unfold event_task_rdy_pre; entailer!; try tauto; intros ? ?; exact I. }
  destruct (Hopen before Hpre) as [Hentry Howned].
  destruct (event_task_rdy_selection sg tasks eid event tid task Hentry)
    as [Hprio [Hslot [Hvalid [Hrange [Huy Hux]]]]].
  destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding task.(curPrio) Hrange)
    as [Hxr [Hyr Hencoding]].
  assert (Hcells : event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid) (event_image sg tasks event) **
      unmap_table_rep sg ** store_prio_tbl sg tasks.(prioTbl) ** (TT) |--
    (event_addr sg eid + 10) # UChar |-> encode_event_wait_grp event.(waitList) tasks **
    (event_addr sg eid + 11 + tcb_y_of_prio task.(curPrio)) # UChar |->
      encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)) **
    unmap_table_rep sg ** store_prio_tbl sg tasks.(prioTbl) ** TT).
  { sep_apply_l_atomic (event_task_remove_ecb_split sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
      (event_image sg tasks event) (tcb_y_of_prio task.(curPrio))
      (encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)))
      (encode_event_wait_grp event.(waitList) tasks) Hyr
      (event_table_image_eq sg tasks event _ Hyr) eq_refl).
    entailer!; intros ? ?; exact I. }
  pose proof (Hcells before Howned) as Hphysical.
  assert (Hg : uchar_load (event_addr sg eid + 10) (encode_event_wait_grp event.(waitList) tasks) before).
  { match type of Hphysical with ?P before => assert (Horder : P |--
      (event_addr sg eid + 10) # UChar |-> encode_event_wait_grp event.(waitList) tasks ** TT) end.
    { entailer!; intros ? ?; exact I. }
    eapply framed_uchar_store_load; exact (Horder before Hphysical). }
  assert (Eg : observed_group = encode_event_wait_grp event.(waitList) tasks)
    by (eapply uchar_load_deterministic; eassumption); subst observed_group.
  assert (Hunmap : (unmap_table_rep sg ** TT) before).
  { match type of Hphysical with ?P before => assert (Horder : P |-- unmap_table_rep sg ** TT) end.
    { entailer!; intros ? ?; exact I. } exact (Horder before Hphysical). }
  pose proof (mutex_del_wake_array_load sg.(g_OSUnMapTbl) 256 unmap_table
    (encode_event_wait_grp event.(waitList) tasks) before (TT) (proj1 Hg) Hunmap) as Hactual_y.
  rewrite unmap_table_Znth, Huy in Hactual_y by exact (proj1 Hg).
  assert (Ey : row = tcb_y_of_prio task.(curPrio))
    by (eapply uchar_load_deterministic; eassumption); subst row.
  assert (Hb : uchar_load (event_addr sg eid + 11 + tcb_y_of_prio task.(curPrio))
    (encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio))) before).
  { match type of Hphysical with ?P before => assert (Horder : P |--
      (event_addr sg eid + 11 + tcb_y_of_prio task.(curPrio)) # UChar |->
        encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)) ** TT) end.
    { entailer!; intros ? ?; exact I. }
    eapply framed_uchar_store_load; exact (Horder before Hphysical). }
  assert (Eb : bits = encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)))
    by (eapply uchar_load_deterministic; eassumption); subst bits.
  pose proof (mutex_del_wake_array_load sg.(g_OSUnMapTbl) 256 unmap_table
    (encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)))
    before (TT) (proj1 Hb) Hunmap) as Hactual_x.
  rewrite unmap_table_Znth, Hux in Hactual_x by exact (proj1 Hb).
  assert (Ex : column = tcb_x_of_prio task.(curPrio))
    by (eapply uchar_load_deterministic; eassumption); subst column.
  assert (Ep : priority = task.(curPrio)).
  { unfold tcb_y_of_prio, tcb_x_of_prio in Hpriority.
    pose proof (Z.div_mod task.(curPrio) 8 ltac:(lia)); lia. }
  rewrite Ep in Hpointer.
  assert (Htable : (store_prio_tbl sg tasks.(prioTbl) ** TT) before).
  { match type of Howned with ?P before => assert (Horder : P |-- store_prio_tbl sg tasks.(prioTbl) ** TT) end.
    { entailer!; intros ? ?; exact I. } exact (Horder before Howned). }
  assert (Htable_cell : store_prio_tbl sg tasks.(prioTbl) ** (TT) |--
    (sg.(g_OSTCBPrioTbl) + task.(curPrio) * sizeof(PTR)) # Ptr |-> task_slot_addr sg tid ** TT).
  { sep_apply_l_atomic (event_task_rdy_prio_split sg tasks tid task.(curPrio) Hrange Hslot).
    entailer!; intros ? ?; exact I. }
  pose proof (framed_pointer_store_load _ _ _ _ (Htable_cell before Htable)) as Hactual_pointer.
  assert (Epointer : pointer = task_slot_addr sg tid) by (eapply pointer_load_deterministic; eassumption).
  auto.
Qed.

Definition mutex_del_waiter_remove_execution (pointer group table : Z) (before after : model) : Prop :=
  exists row bitx value cleared removed,
    uchar_load (tcb_field_address pointer TCBY) row before /\
    uchar_load (tcb_field_address pointer TCBBitX) bitx before /\
    uchar_load (table + row) value before /\
    kernel_heap_execution [(table + row, event_task_remove_cleared value bitx)] before cleared /\
    uchar_load (table + row) (event_task_remove_cleared value bitx) cleared /\
    (if Z.eqb (event_task_remove_cleared value bitx) 0
     then exists bity group_value,
       uchar_load (tcb_field_address pointer TCBBitY) bity cleared /\
       uchar_load group group_value cleared /\
       kernel_heap_execution [(group, event_task_remove_cleared group_value bity)] cleared removed
     else removed = cleared) /\
    kernel_heap_execution (pointer_store_writes (tcb_field_address pointer TCBEventPtr) 0) removed after.

Lemma mutex_del_waiter_remove_resources : forall pointer group table row bitx bity value group_value
  before after (frame : Assertion),
  (event_task_remove_pre pointer group table row bitx bity value group_value ** frame) before ->
  mutex_del_waiter_remove_execution pointer group table before after ->
  (event_task_remove_post pointer group table row bitx bity value group_value ** frame) after.
Proof.
  intros pointer group table row bitx bity value group_value before after frame Hpre
    (actual_row & actual_bitx & actual_value & cleared & removed &
      Hrow & Hbitx & Hvalue & Hclear & Hcheck & Hgroup & Hpointer).
  set (cells := fun (v g : Z) =>
    tcb_field_address pointer TCBY # UChar |-> row **
    tcb_field_address pointer TCBBitX # UChar |-> bitx **
    tcb_field_address pointer TCBBitY # UChar |-> bity **
    tcb_field_address pointer TCBEventPtr # Ptr |->_ **
    group # UChar |-> g ** (table + row) # UChar |-> v ** frame).
  assert (Hopen : event_task_remove_pre pointer group table row bitx bity value group_value ** frame |--
    coq_prop (0 <= row < 8) && cells value group_value).
  { unfold event_task_remove_pre, cells; entailer!; lia. }
  destruct (Hopen before Hpre) as [Hrange Hcells].
  assert (Hy : uchar_load (tcb_field_address pointer TCBY) row before).
  { assert (Horder : cells value group_value |-- tcb_field_address pointer TCBY # UChar |-> row ** TT)
      by (unfold cells; entailer!; intros ? ?; exact I).
    eapply framed_uchar_store_load; exact (Horder before Hcells). }
  assert (actual_row = row) by (eapply uchar_load_deterministic; eassumption); subst actual_row.
  assert (Hx : uchar_load (tcb_field_address pointer TCBBitX) bitx before).
  { assert (Horder : cells value group_value |-- tcb_field_address pointer TCBBitX # UChar |-> bitx ** TT)
      by (unfold cells; entailer!; intros ? ?; exact I).
    eapply framed_uchar_store_load; exact (Horder before Hcells). }
  assert (actual_bitx = bitx) by (eapply uchar_load_deterministic; eassumption); subst actual_bitx.
  assert (Hv : uchar_load (table + row) value before).
  { assert (Horder : cells value group_value |-- (table + row) # UChar |-> value ** TT)
      by (unfold cells; entailer!; intros ? ?; exact I).
    eapply framed_uchar_store_load; exact (Horder before Hcells). }
  assert (actual_value = value) by (eapply uchar_load_deterministic; eassumption); subst actual_value.
  set (residual := tcb_field_address pointer TCBY # UChar |-> row **
    tcb_field_address pointer TCBBitX # UChar |-> bitx **
    tcb_field_address pointer TCBBitY # UChar |-> bity **
    tcb_field_address pointer TCBEventPtr # Ptr |->_ ** group # UChar |-> group_value ** frame).
  assert (Hwrite_order : cells value group_value |-- (table + row) # UChar |-> value ** residual)
    by (unfold cells, residual; entailer!).
  destruct (kernel_heap_framed_uchar_store (table + row) value (event_task_remove_cleared value bitx)
    residual before (byte_land_in_range__ready_bitmap_stages value _ (proj1 Hv))
    (Hwrite_order before Hcells)) as [produced [Hwrite Hproduced]].
  assert (produced = cleared) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hclear_order : (table + row) # UChar |-> event_task_remove_cleared value bitx ** residual |--
    cells (event_task_remove_cleared value bitx) group_value) by (unfold cells, residual; entailer!).
  pose proof (Hclear_order cleared Hproduced) as Hcleared.
  assert (Hremoved : cells (event_task_remove_cleared value bitx)
    (event_task_remove_group value group_value bitx bity) removed).
  { unfold event_task_remove_group.
    destruct (Z.eqb (event_task_remove_cleared value bitx) 0); [|subst removed; exact Hcleared].
    destruct Hgroup as (actual_bity & actual_group & Hby & Hg & Hwrite_group).
    assert (Hactual_by : uchar_load (tcb_field_address pointer TCBBitY) bity cleared).
    { assert (Horder : cells (event_task_remove_cleared value bitx) group_value |--
        tcb_field_address pointer TCBBitY # UChar |-> bity ** TT)
        by (unfold cells; entailer!; intros ? ?; exact I).
      eapply framed_uchar_store_load; exact (Horder cleared Hcleared). }
    assert (actual_bity = bity) by (eapply uchar_load_deterministic; eassumption); subst actual_bity.
    set (rest := tcb_field_address pointer TCBY # UChar |-> row **
      tcb_field_address pointer TCBBitX # UChar |-> bitx **
      tcb_field_address pointer TCBBitY # UChar |-> bity **
      tcb_field_address pointer TCBEventPtr # Ptr |->_ **
      (table + row) # UChar |-> event_task_remove_cleared value bitx ** frame).
    assert (Horder : cells (event_task_remove_cleared value bitx) group_value |--
      group # UChar |-> group_value ** rest) by (unfold cells, rest; entailer!).
    pose proof (framed_uchar_store_load _ _ _ _ (Horder cleared Hcleared)) as Hactual_g.
    assert (actual_group = group_value) by (eapply uchar_load_deterministic; eassumption); subst actual_group.
    destruct (kernel_heap_framed_uchar_store group group_value (event_task_remove_cleared group_value bity)
      rest cleared (byte_land_in_range__ready_bitmap_stages group_value _ (proj1 Hactual_g))
      (Horder cleared Hcleared)) as [produced [Hgroup_exec Hwritten]].
    assert (produced = removed) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
    assert (Hclose : group # UChar |-> event_task_remove_cleared group_value bity ** rest |--
      cells (event_task_remove_cleared value bitx) (event_task_remove_cleared group_value bity))
      by (unfold cells, rest; entailer!).
    exact (Hclose removed Hwritten). }
  set (final_frame := tcb_field_address pointer TCBY # UChar |-> row **
    tcb_field_address pointer TCBBitX # UChar |-> bitx **
    tcb_field_address pointer TCBBitY # UChar |-> bity **
    group # UChar |-> event_task_remove_group value group_value bitx bity **
    (table + row) # UChar |-> event_task_remove_cleared value bitx ** frame).
  assert (Hptr_order : cells (event_task_remove_cleared value bitx)
      (event_task_remove_group value group_value bitx bity) |--
    tcb_field_address pointer TCBEventPtr # Ptr |->_ ** final_frame)
    by (unfold cells, final_frame; entailer!).
  destruct (framed_pointer_store_execution _ 0 final_frame removed ltac:(lia) (Hptr_order removed Hremoved))
    as [produced [Hpointer_exec Hwritten]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hclose : tcb_field_address pointer TCBEventPtr # Ptr |-> 0 ** final_frame |--
    event_task_remove_post pointer group table row bitx bity value group_value ** frame).
  { unfold final_frame, event_task_remove_post; entailer!; lia. }
  exact (Hclose after Hwritten).
Qed.

Definition mutex_del_waiter_prefix_execution (pointer : Z) (before after : model) : Prop :=
  exists delayed messaged status_written bits,
    kernel_heap_execution (pointer_store_writes (tcb_field_address pointer TCBDly) 0) before delayed /\
    kernel_heap_execution (pointer_store_writes (tcb_field_address pointer TCBMsg) 0) delayed messaged /\
    uchar_load (tcb_field_address pointer TCBStat) bits messaged /\
    kernel_heap_execution [(tcb_field_address pointer TCBStat, event_task_remove_cleared bits 16)]
      messaged status_written /\
    kernel_heap_execution [(tcb_field_address pointer TCBStatPend, 2)] status_written after.

Lemma mutex_del_waiter_prefix_resources : forall sg task pointer before after (frame : Assertion),
  (tcb64_storage_rep pointer (task_tcb64_image sg task) ** frame) before ->
  mutex_del_waiter_prefix_execution pointer before after ->
  (tcb64_storage_rep pointer (event_task_rdy_before_remove_image sg task 0 16 2) ** frame) after.
Proof.
  intros sg task pointer before after frame Hpre
    (delayed & messaged & status_written & bits & Hdly & Hmsg & Hbits & Hstat & Hpend).
  pose proof (mutex_del_wake_tcb_store pointer (task_tcb64_image sg task) TCBDly 0 before delayed frame
    ltac:(unfold mutex_del_wake_tcb_writable; cbn; auto)
    ltac:(unfold mutex_del_wake_tcb_value_in_range; cbn; lia) Hpre Hdly) as Hd.
  pose proof (mutex_del_wake_tcb_store pointer (tcb_write (task_tcb64_image sg task) TCBDly (Some 0))
    TCBMsg 0 delayed messaged frame ltac:(unfold mutex_del_wake_tcb_writable; cbn; auto)
    ltac:(unfold mutex_del_wake_tcb_value_in_range; cbn; lia) Hd Hmsg) as Hm.
  pose proof (mutex_del_wake_tcb_byte_load pointer
    (tcb_write (tcb_write (task_tcb64_image sg task) TCBDly (Some 0)) TCBMsg (Some 0))
    TCBStat (encode_task_status task.(stat)) messaged frame ltac:(cbn; auto) eq_refl Hm) as Hactual.
  assert (bits = encode_task_status task.(stat)) by (eapply uchar_load_deterministic; eassumption); subst bits.
  assert (Eclear : event_task_remove_cleared (encode_task_status task.(stat)) 16 =
    task_status_clear_wait (encode_task_status task.(stat)) 16).
  { symmetry; apply task_status_clear_wait_byte_complement; lia. }
  rewrite Eclear in Hstat.
  pose proof (mutex_del_wake_tcb_store pointer
    (tcb_write (tcb_write (task_tcb64_image sg task) TCBDly (Some 0)) TCBMsg (Some 0))
    TCBStat (task_status_clear_wait (encode_task_status task.(stat)) 16) messaged status_written frame
    ltac:(unfold mutex_del_wake_tcb_writable; cbn; auto)
    (task_status_clear_wait_in_range _ _ (proj1 Hactual)) Hm Hstat) as Hs.
  exact (mutex_del_wake_tcb_store pointer _ TCBStatPend 2 status_written after frame
    ltac:(unfold mutex_del_wake_tcb_writable; cbn; auto)
    ltac:(unfold mutex_del_wake_tcb_value_in_range; cbn; lia) Hs Hpend).
Qed.

(** This relation follows the C suspension test and reads the current TCB
    masks and scheduler bytes. The selector's row is the source local [y]. *)
Definition mutex_del_waiter_ready_execution (pointer group table row : Z)
  (before after : model) : Prop :=
  exists bits,
    uchar_load (tcb_field_address pointer TCBStat) bits before /\
    if Z.eqb (Z.land bits 8) 0 then
      exists bity group_value grouped bitx row_value,
        uchar_load (tcb_field_address pointer TCBBitY) bity before /\
        uchar_load group group_value before /\
        kernel_heap_execution [(group, Z.lor group_value bity)] before grouped /\
        uchar_load (tcb_field_address pointer TCBBitX) bitx grouped /\
        uchar_load (table + row) row_value grouped /\
        kernel_heap_execution [(table + row, Z.lor row_value bitx)] grouped after
    else after = before.

Lemma mutex_del_waiter_ready_resources : forall pointer image group table row bitx bity bits group_value rows
  before after (frame : Assertion),
  0 <= row < 8 -> image TCBStat = Some bits -> image TCBBitX = Some bitx -> image TCBBitY = Some bity ->
  (tcb64_storage_rep pointer image ** group # UChar |-> group_value ** UCharArray.full table 8 rows ** frame) before ->
  mutex_del_waiter_ready_execution pointer group table row before after ->
  (tcb64_storage_rep pointer image **
   group # UChar |-> event_task_rdy_ready_group bits group_value bity **
   UCharArray.full table 8 (event_task_rdy_ready_rows bits row bitx rows) ** frame) after.
Proof.
  intros pointer image group table row bitx bity bits group_value rows before after frame
    Hrow Hbits Hbitx Hbity Hpre (observed & Hread & Hbranch).
  set (resources := fun (g : Z) (rs : list Z) =>
    tcb64_storage_rep pointer image ** group # UChar |-> g ** UCharArray.full table 8 rs ** frame).
  assert (Htask : resources group_value rows |-- tcb64_storage_rep pointer image ** TT)
    by (unfold resources; entailer!; intros ? ?; exact I).
  pose proof (mutex_del_wake_tcb_byte_load pointer image TCBStat bits before (TT)
    ltac:(cbn; auto) Hbits (Htask before Hpre)) as Hactual.
  assert (observed = bits) by (eapply uchar_load_deterministic; eassumption); subst observed.
  unfold event_task_rdy_ready_group, event_task_rdy_ready_rows, task_status_is_suspended, task_suspend_mask.
  destruct (Z.eqb (Z.land bits 8) 0) eqn:Htest; cbn; [|subst after; exact Hpre].
  destruct Hbranch as (actual_bity & actual_group & grouped & actual_bitx & actual_row &
    Hby & Hg & Hgroup_write & Hbx & Hrows & Hrow_write).
  pose proof (mutex_del_wake_tcb_byte_load pointer image TCBBitY bity before (TT)
    ltac:(cbn; auto) Hbity (Htask before Hpre)) as Hactual_by.
  assert (actual_bity = bity) by (eapply uchar_load_deterministic; eassumption); subst actual_bity.
  set (group_frame := tcb64_storage_rep pointer image ** UCharArray.full table 8 rows ** frame).
  assert (Hgroup_order : resources group_value rows |-- group # UChar |-> group_value ** group_frame)
    by (unfold resources, group_frame; entailer!).
  pose proof (framed_uchar_store_load _ _ _ _ (Hgroup_order before Hpre)) as Hactual_group.
  assert (actual_group = group_value) by (eapply uchar_load_deterministic; eassumption); subst actual_group.
  destruct (kernel_heap_framed_uchar_store group group_value (Z.lor group_value bity)
    group_frame before (bitmap_lor_in_range 8 _ _ ltac:(lia) (proj1 Hactual_group) (proj1 Hactual_by))
    (Hgroup_order before Hpre)) as [produced [Hwrite Hproduced]].
  assert (produced = grouped) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hgrouped_order : group # UChar |-> Z.lor group_value bity ** group_frame |--
    resources (Z.lor group_value bity) rows) by (unfold group_frame, resources; entailer!).
  pose proof (Hgrouped_order grouped Hproduced) as Hgrouped.
  assert (Htask_grouped : resources (Z.lor group_value bity) rows |-- tcb64_storage_rep pointer image ** TT)
    by (unfold resources; entailer!; intros ? ?; exact I).
  pose proof (mutex_del_wake_tcb_byte_load pointer image TCBBitX bitx grouped (TT)
    ltac:(cbn; auto) Hbitx (Htask_grouped grouped Hgrouped)) as Hactual_bx.
  assert (actual_bitx = bitx) by (eapply uchar_load_deterministic; eassumption); subst actual_bitx.
  set (rows_frame := tcb64_storage_rep pointer image ** group # UChar |-> Z.lor group_value bity ** frame).
  assert (Hrows_order : resources (Z.lor group_value bity) rows |-- UCharArray.full table 8 rows ** rows_frame)
    by (unfold resources, rows_frame; entailer!).
  pose proof (mutex_del_wake_array_load table 8 rows row grouped rows_frame Hrow
    (Hrows_order grouped Hgrouped)) as Hactual_row.
  assert (actual_row = Znth row rows 0) by (eapply uchar_load_deterministic; eassumption); subst actual_row.
  pose proof (mutex_del_wake_array_store table 8 rows row (Z.lor (Znth row rows 0) bitx)
    grouped after rows_frame Hrow
    (bitmap_lor_in_range 8 _ _ ltac:(lia) (proj1 Hactual_row) (proj1 Hactual_bx))
    (Hrows_order grouped Hgrouped) Hrow_write) as Hstored.
  assert (Hclose : UCharArray.full table 8 (replace_Znth row (Z.lor (Znth row rows 0) bitx) rows) ** rows_frame |--
    resources (Z.lor group_value bity) (replace_Znth row (Z.lor (Znth row rows 0) bitx) rows))
    by (unfold rows_frame, resources; entailer!).
  exact (Hclose after Hstored).
Qed.

(** Selected OS_EventTaskRdy(pe, NULL, OS_STAT_MUTEX, OS_STAT_PEND_ABORT):
    lookup, four TCB stores, conditional ready insertion, then the concrete
    OS_EventTaskRemove body. All operands are read from the executing heap. *)
Definition mutex_del_waiter_execution (sg : StableGlobVars) (pe returned : Z)
  (before after : model) : Prop :=
  exists pointer row prefixed readied,
    mutex_del_wake_selection_execution sg pe pointer row returned before /\
    mutex_del_waiter_prefix_execution pointer before prefixed /\
    mutex_del_waiter_ready_execution pointer sg.(g_OSRdyGrp) sg.(g_OSRdyTbl) row prefixed readied /\
    mutex_del_waiter_remove_execution pointer (pe + OSEventGrp_off) (pe + OSEventTbl_off) readied after.

Lemma mutex_del_waiter_source_post : forall sg tasks eid event tid task group rows returned
  before after (frame : Assertion),
  (event_task_rdy_pre sg tasks eid event tid task 16 2 group rows ** frame) before ->
  mutex_del_waiter_execution sg (event_addr sg eid) returned before after ->
  (event_task_rdy_post sg tasks eid event tid task 0 16 2 group rows returned ** frame) after.
Proof.
  intros sg tasks eid event tid task group rows returned before after frame Hpre
    (pointer & row & prefixed & readied & Hselection & Hprefix & Hready & Hremove).
  destruct (mutex_del_wake_selection_resources sg tasks eid event tid task group rows pointer row returned
    before frame Hpre Hselection) as [Epointer [Erow Ereturned]].
  subst pointer row returned.
  set (image := event_task_rdy_before_remove_image sg task 0 16 2).
  set (bits := task_status_clear_wait (encode_task_status task.(stat)) 16).
  set (ready_group := event_task_rdy_ready_group bits group (tcb_bit_y_of_prio task.(curPrio))).
  set (ready_rows := event_task_rdy_ready_rows bits (tcb_y_of_prio task.(curPrio))
    (tcb_bit_x_of_prio task.(curPrio)) rows).
  set (prefix_frame := event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
      (event_image sg tasks event) ** unmap_table_rep sg ** store_prio_tbl sg tasks.(prioTbl) **
    sg.(g_OSRdyGrp) # UChar |-> group ** UCharArray.full sg.(g_OSRdyTbl) 8 rows ** frame).
  assert (Hopen : event_task_rdy_pre sg tasks eid event tid task 16 2 group rows ** frame |--
    coq_prop (event_task_rdy_entry sg tasks eid event tid task) &&
    (tcb64_storage_rep (task_slot_addr sg tid) (task_tcb64_image sg task) ** prefix_frame)).
  { unfold event_task_rdy_pre, prefix_frame; entailer!; tauto. }
  destruct (Hopen before Hpre) as [Hentry Howned].
  pose proof (mutex_del_waiter_prefix_resources sg task (task_slot_addr sg tid) before prefixed
    prefix_frame Howned Hprefix) as Hprefixed.
  destruct (event_task_rdy_selection sg tasks eid event tid task Hentry)
    as [Hpriority [Htable [Hvalid [Hrange _]]]].
  pose proof (proj1 (proj2 (priority_coordinates_in_range_and_encoding_eq__priority_encoding
    task.(curPrio) Hrange))) as Hrow.
  set (ready_frame := event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
      (event_image sg tasks event) ** unmap_table_rep sg ** store_prio_tbl sg tasks.(prioTbl) ** frame).
  assert (Hready_order : tcb64_storage_rep (task_slot_addr sg tid) image ** prefix_frame |--
    tcb64_storage_rep (task_slot_addr sg tid) image ** sg.(g_OSRdyGrp) # UChar |-> group **
    UCharArray.full sg.(g_OSRdyTbl) 8 rows ** ready_frame)
    by (unfold prefix_frame, ready_frame; entailer!).
  pose proof (mutex_del_waiter_ready_resources (task_slot_addr sg tid) image sg.(g_OSRdyGrp) sg.(g_OSRdyTbl)
    (tcb_y_of_prio task.(curPrio)) (tcb_bit_x_of_prio task.(curPrio)) (tcb_bit_y_of_prio task.(curPrio))
    bits group rows prefixed readied ready_frame Hrow eq_refl eq_refl eq_refl
    (Hready_order prefixed Hprefixed) Hready) as Hreadied.
  set (remove_frame := unmap_table_rep sg ** store_prio_tbl sg tasks.(prioTbl) **
    sg.(g_OSRdyGrp) # UChar |-> ready_group ** UCharArray.full sg.(g_OSRdyTbl) 8 ready_rows ** frame).
  set (remove_rest :=
    event_task_remove_tcb_frame (task_slot_addr sg tid) image **
    event_task_remove_ecb_frame sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
      (event_image sg tasks event) (tcb_y_of_prio task.(curPrio)) ** remove_frame).
  set (remove_pre := event_task_remove_pre (task_slot_addr sg tid) (event_addr sg eid + 10)
    (event_addr sg eid + 11) (tcb_y_of_prio task.(curPrio)) (tcb_bit_x_of_prio task.(curPrio))
    (tcb_bit_y_of_prio task.(curPrio))
    (encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)))
    (encode_event_wait_grp event.(waitList) tasks)).
  assert (Hremove_open : tcb64_storage_rep (task_slot_addr sg tid) image **
      sg.(g_OSRdyGrp) # UChar |-> ready_group ** UCharArray.full sg.(g_OSRdyTbl) 8 ready_rows ** ready_frame |--
    remove_pre ** remove_rest).
  { eapply derivable1_trans with (y :=
      (tcb64_storage_rep (task_slot_addr sg tid) image **
       event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid) (event_image sg tasks event)) **
      remove_frame).
    { unfold ready_frame, remove_frame; entailer!. }
    unfold remove_pre, remove_rest.
    sep_apply_l_atomic (event_task_remove_storage_split sg.(osKernelConfig).(cfgEventNames)
      (task_slot_addr sg tid) (event_addr sg eid) image (event_image sg tasks event)
      (tcb_y_of_prio task.(curPrio)) (tcb_bit_x_of_prio task.(curPrio)) (tcb_bit_y_of_prio task.(curPrio))
      (encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)))
      (encode_event_wait_grp event.(waitList) tasks) Hrow eq_refl eq_refl eq_refl
      (event_table_image_eq sg tasks event _ Hrow) eq_refl); entailer!. }
  pose proof (mutex_del_waiter_remove_resources (task_slot_addr sg tid) (event_addr sg eid + 10)
    (event_addr sg eid + 11) (tcb_y_of_prio task.(curPrio)) (tcb_bit_x_of_prio task.(curPrio))
    (tcb_bit_y_of_prio task.(curPrio))
    (encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)))
    (encode_event_wait_grp event.(waitList) tasks) readied after remove_rest
    (Hremove_open readied Hreadied) Hremove) as Hremoved.
  destruct Hentry as [Hsg [Hlayout [Hmulti [Htasks [Hconsistency [Hhead Hlookup]]]]]].
  assert (Hunique : task_priority_unique tasks) by (unfold task_in_range in Htasks; tauto).
  assert (Hcanonical : event_waitList_canonical sg tasks event.(waitList)) by (exact (proj1 Hconsistency)).
  assert (Hclose : event_task_remove_post (task_slot_addr sg tid) (event_addr sg eid + 10)
      (event_addr sg eid + 11) (tcb_y_of_prio task.(curPrio)) (tcb_bit_x_of_prio task.(curPrio))
      (tcb_bit_y_of_prio task.(curPrio))
      (encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)))
      (encode_event_wait_grp event.(waitList) tasks) ** remove_rest |--
    event_task_rdy_post sg tasks eid event tid task 0 16 2 group rows task.(curPrio) ** frame).
  { unfold remove_rest.
    eapply derivable1_trans with (y :=
      (event_task_remove_post (task_slot_addr sg tid) (event_addr sg eid + 10)
        (event_addr sg eid + 11) (tcb_y_of_prio task.(curPrio)) (tcb_bit_x_of_prio task.(curPrio))
        (tcb_bit_y_of_prio task.(curPrio))
        (encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)))
        (encode_event_wait_grp event.(waitList) tasks) **
       event_task_remove_tcb_frame (task_slot_addr sg tid) image **
       event_task_remove_ecb_frame sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
         (event_image sg tasks event) (tcb_y_of_prio task.(curPrio))) ** remove_frame).
    { entailer!. }
    unfold remove_frame, event_task_rdy_post.
    sep_apply_l_atomic (event_task_remove_storage_merge_updated sg.(osKernelConfig).(cfgEventNames)
      (task_slot_addr sg tid) (event_addr sg eid) image (event_image sg tasks event)
      (tcb_y_of_prio task.(curPrio)) (tcb_bit_x_of_prio task.(curPrio)) (tcb_bit_y_of_prio task.(curPrio))
      (encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)))
      (encode_event_wait_grp event.(waitList) tasks) eq_refl eq_refl eq_refl eq_refl).
    unfold tcb_bit_x_of_prio, tcb_bit_y_of_prio, tcb_x_of_prio, tcb_y_of_prio.
    rewrite <- (event_remove_waiter_image_eq sg tasks event tid task Hsg Hunique Hcanonical Hvalid Hlookup).
    unfold image, ready_group, ready_rows, bits, event_task_rdy_task_image; entailer!; lia. }
  exact (Hclose after Hremoved).
Qed.

Lemma mutex_del_wake_group_load : forall sg state eid event heap (frame : Assertion),
  state.(EventState).(inUsedEventStates) eid = Some event ->
  (kernel_program_rep sg state ** frame) heap ->
  uchar_load (event_addr sg eid + OSEventGrp_off)
    (encode_event_wait_grp event.(waitList) state.(TskState)) heap.
Proof.
  intros sg state eid event heap frame Hlookup Hpre.
  assert (Hsplit : kernel_program_rep sg state ** frame |--
    (event_pool_addr sg eid + 10) # UChar |-> encode_event_wait_grp event.(waitList) state.(TskState) ** TT).
  { unfold kernel_program_rep.
    sep_apply_l_atomic (mutex_del_parent_event_core_split sg state eid event Hlookup).
    entailer!; intros ? ?; exact I. }
  eapply framed_uchar_store_load; exact (Hsplit heap Hpre).
Qed.

Lemma mutex_del_waiter_state_resources : forall sg eid mutex state event priority before after (frame : Assertion),
  mutex_del_wake_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  encode_event_wait_grp event.(waitList) state.(TskState) <> 0 ->
  event_object_layout_prop sg eid -> (kernel_program_rep sg state ** frame) before ->
  mutex_del_waiter_execution sg (event_addr sg eid) priority before after ->
  exists updated,
    event_task_rdy sg state eid PendMutex 0 PendAbort = Some (priority, updated) /\
    mutex_del_wake_state_inv sg eid mutex updated /\ (kernel_program_rep sg updated ** frame) after.
Proof.
  intros sg eid mutex state event priority before after frame Hphase Hlookup Hnonzero Hlayout Hpre Hrun.
  assert (Hopen : kernel_program_rep sg state ** frame |-- EX tid old,
    coq_prop (event_task_rdy_entry sg state.(TskState) eid event tid old) &&
    (event_task_rdy_pre sg state.(TskState) eid event tid old 16 2
       (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
       (sched_row_values state.(TskState) state.(SchedState).(readyList)) **
     (mutex_del_wake_frame sg state eid tid ** frame))).
  { eapply derivable1_trans with (y := (mutex_del_wake_rep sg eid mutex state ** unmap_table_rep sg) ** frame).
    { unfold kernel_program_rep, mutex_del_wake_rep; entailer!. }
    sep_apply_l_atomic (mutex_del_wake_split sg eid mutex state event Hphase Hlookup Hnonzero Hlayout).
    Intros tid old; Exists tid old; entailer!. }
  destruct (Hopen before Hpre) as [tid [old [Hentry Howned]]].
  pose proof (mutex_del_waiter_source_post sg state.(TskState) eid event tid old
    (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
    (sched_row_values state.(TskState) state.(SchedState).(readyList)) priority before after
    (mutex_del_wake_frame sg state eid tid ** frame) Howned Hrun) as Hreturned.
  set (updated := event_wake_state sg state eid event tid old PendMutex 0 PendAbort).
  assert (Hclose : event_task_rdy_post sg state.(TskState) eid event tid old 0 16 2
      (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
      (sched_row_values state.(TskState) state.(SchedState).(readyList)) priority **
      (mutex_del_wake_frame sg state eid tid ** frame) |--
    coq_prop (event_task_rdy sg state eid PendMutex 0 PendAbort = Some (priority, updated) /\
      mutex_del_wake_state_inv sg eid mutex updated) && (kernel_program_rep sg updated ** frame)).
  { eapply derivable1_trans with (y :=
      (event_task_rdy_post sg state.(TskState) eid event tid old 0 16 2
        (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
        (sched_row_values state.(TskState) state.(SchedState).(readyList)) priority **
        mutex_del_wake_frame sg state eid tid) ** frame); [entailer!|].
    sep_apply_l_atomic (mutex_del_wake_merge sg eid mutex state event tid old priority Hphase Hlookup Hentry).
    unfold updated, kernel_program_rep, mutex_del_wake_rep; entailer!. }
  destruct (Hclose after Hreturned) as [[Hstep Hvalid] Hheap]; exists updated; auto.
Qed.

(** Finite executions of the literal EventGrp-tested C while loop. The
    source relation mentions heaps and loads/calls only; the abstract
    broadcast relation is established by the theorem below. *)
Inductive mutex_del_wake_loop_execution (sg : StableGlobVars) (pe : Z)
  : model -> model -> Prop :=
| mutex_del_wake_loop_done : forall heap,
    uchar_load (pe + OSEventGrp_off) 0 heap ->
    mutex_del_wake_loop_execution sg pe heap heap
| mutex_del_wake_loop_next : forall before middle after group priority,
    uchar_load (pe + OSEventGrp_off) group before -> group <> 0 ->
    mutex_del_waiter_execution sg pe priority before middle ->
    mutex_del_wake_loop_execution sg pe middle after ->
    mutex_del_wake_loop_execution sg pe before after.

Lemma mutex_del_wake_loop_resources : forall sg eid mutex before after (frame : Assertion),
  event_object_layout_prop sg eid -> mutex_del_wake_loop_execution sg (event_addr sg eid) before after ->
  forall state event,
    mutex_del_wake_state_inv sg eid mutex state ->
    state.(EventState).(inUsedEventStates) eid = Some event ->
    (kernel_program_rep sg state ** frame) before ->
    exists priorities updated,
      event_broadcast sg eid PendMutex 0 PendAbort state priorities updated /\
      (kernel_program_rep sg updated ** frame) after.
Proof.
  intros sg eid mutex before after frame Hlayout Hrun.
  induction Hrun as [heap Hzero|before middle after group priority Hgroup Hnonzero Hstep Hloop IH];
    intros state event Hphase Hlookup Hpre.
  - pose proof (mutex_del_wake_group_load sg state eid event heap frame Hlookup Hpre) as Hactual.
    assert (Hempty : encode_event_wait_grp event.(waitList) state.(TskState) = 0)
      by (eapply uchar_load_deterministic; eassumption).
    exists [], state; split; [eapply event_broadcast_done; eassumption|exact Hpre].
  - pose proof (mutex_del_wake_group_load sg state eid event before frame Hlookup Hpre) as Hactual.
    assert (Egroup : group = encode_event_wait_grp event.(waitList) state.(TskState))
      by (eapply uchar_load_deterministic; eassumption).
    rewrite Egroup in Hnonzero.
    destruct (mutex_del_waiter_state_resources sg eid mutex state event priority before middle frame
      Hphase Hlookup Hnonzero Hlayout Hpre Hstep) as [mid [Habstract [Hphase_mid Hheap_mid]]].
    destruct Hphase_mid as [current [Hcurrent Hrest]].
    assert (Hphase_mid : mutex_del_wake_state_inv sg eid mutex mid) by (exists current; auto).
    destruct (IH mid current Hphase_mid Hcurrent Hheap_mid) as [priorities [updated [Hbroadcast Hheap]]].
    exists (priority :: priorities), updated; split; [eapply event_broadcast_next; eassumption|exact Hheap].
Qed.

Lemma mutex_del_wake_count_load : forall sg state eid event heap (frame : Assertion),
  state.(EventState).(inUsedEventStates) eid = Some event ->
  (kernel_program_rep sg state ** frame) heap ->
  mutex_del_count_load (event_addr sg eid + OSEventCnt_off) (encode_event_cnt_value event) heap.
Proof.
  intros sg state eid event heap frame Hlookup Hpre.
  assert (Hsplit : kernel_program_rep sg state ** frame |--
    (event_pool_addr sg eid + 8) # UShort |-> encode_event_cnt_value event ** TT).
  { unfold kernel_program_rep; sep_apply_l_atomic (mutex_del_parent_event_core_split sg state eid event Hlookup).
    entailer!; intros ? ?; exact I. }
  eapply mutex_del_count_store_load; exact (Hsplit heap Hpre).
Qed.

Lemma mutex_del_wake_repeated_ceiling_store : forall sg eid mutex state before after (frame : Assertion),
  mutex_del_wake_state_inv sg eid mutex state -> mutex.(mfPCP) <> sg.(osPrioMutexCeilDis) ->
  (kernel_program_rep sg state ** frame) before ->
  kernel_heap_execution (pointer_store_writes (sg.(g_OSTCBPrioTbl) + mutex.(mfPCP) * sizeof(PTR)) 0)
    before after -> (kernel_program_rep sg state ** frame) after.
Proof.
  intros sg eid mutex state before after frame Hphase Henabled Hpre Hrun.
  destruct Hphase as [event [Hlookup [Htype [Hfields [[Hdisabled Hvalid]|Hreleased]]]]];
    [contradiction|].
  pose proof (mutex_del_released_ceiling_in_range sg eid mutex state Hreleased) as Hrange.
  pose proof (proj1 (proj2 Hreleased)) as Hclear.
  pose proof (mutex_del_ceiling_store_resources sg state mutex.(mfPCP) before after frame Hrange Hpre Hrun) as Hafter.
  assert (Htable : mutex_del_released_table state mutex.(mfPCP) = state.(TskState).(prioTbl)).
  { unfold mutex_del_released_table; rewrite <- Hclear; apply update_prio_tbl_put_back. }
  assert (Hclose : mutex_del_released_resources sg state mutex.(mfPCP) ** unmap_table_rep sg ** frame |--
    kernel_program_rep sg state ** frame).
  { unfold mutex_del_released_resources, kernel_program_rep; rewrite Htable, UCOS2_raw_rep_priority_table_equiv.
    entailer!. }
  exact (Hclose after Hafter).
Qed.

Definition mutex_del_always_after_prepare_execution (sg : StableGlobVars) (pe : Z)
  (before after : model) : Prop :=
  exists drained count ceiling released,
    mutex_del_wake_loop_execution sg pe before drained /\
    mutex_del_count_load (pe + OSEventCnt_off) count drained /\
    ceiling = unsigned_last_nbits (Z.shiftr count 8) 8 /\
    (if Z.eq_dec ceiling 255 then released = drained
     else kernel_heap_execution (pointer_store_writes (sg.(g_OSTCBPrioTbl) + ceiling * sizeof(PTR)) 0)
       drained released) /\
    mutex_del_recycle_stores sg pe released after.

(** Pure evaluation of the already existing wake operation. The bound is
    the initial canonical wait-list length; it is proof data and does not
    add a counter or ghost ownership to the C loop. *)
Fixpoint mutex_del_broadcast_state (sg : StableGlobVars) (eid : EventID)
  (remaining : nat) (state : UCOS2_Verify_State) : UCOS2_Verify_State :=
  match remaining with
  | O => state
  | S rest => match event_task_rdy sg state eid PendMutex 0 PendAbort with
      | Some (_, next) => mutex_del_broadcast_state sg eid rest next
      | None => state
      end
  end.

Lemma mutex_del_broadcast_state_of_execution : forall sg eid before priorities after,
  event_broadcast sg eid PendMutex 0 PendAbort before priorities after ->
  mutex_del_broadcast_state sg eid (length priorities) before = after.
Proof.
  intros sg eid before priorities after Hrun; induction Hrun; cbn; [reflexivity|].
  rewrite H1; exact IHHrun.
Qed.

Definition mutex_del_always_checkpoint sg eid event prepared : UCOS2_Verify_State :=
  mutex_del_recycle_state sg eid (event_set_wait_list event [])
    (mutex_del_broadcast_state sg eid (length event.(waitList)) prepared).

(** A concrete consumer of the complete loop: the second ceiling store
    and all four recycle writes produce the ordinary program invariant
    and the existing public critical observation for OS_DEL_ALWAYS. *)
Lemma mutex_del_always_after_prepare_resources : forall sg eid entry prepared event mutex before after
  (frame : Assertion),
  event_object_layout_prop sg eid ->
  (mutex_del_parent_prepared sg eid entry prepared event mutex ** unmap_table_rep sg ** frame) before ->
  mutex_del_always_after_prepare_execution sg (event_addr sg eid) before after ->
  mutex_del_critical sg eid 1 entry
    (0, (OS_ERR_NONE, negb (Z.eqb (encode_event_wait_grp event.(waitList) entry.(TskState)) 0)))
    (mutex_del_always_checkpoint sg eid event prepared) /\
  (kernel_program_inv sg (mutex_del_always_checkpoint sg eid event prepared) ** frame) after.
Proof.
  intros sg eid entry prepared event mutex before after frame Hlayout Hpre
    (drained_heap & count & ceiling & released & Hloop & Hcount & Hceiling & Hclear & Hrecycle).
  assert (Hopen : mutex_del_parent_prepared sg eid entry prepared event mutex ** unmap_table_rep sg ** frame |--
    coq_prop (mutex_del_parent_entry sg eid entry event mutex /\ mutex_del_prepare sg mutex entry prepared /\
      mutex_del_wake_state_inv sg eid mutex prepared) && (kernel_program_rep sg prepared ** frame)).
  { unfold mutex_del_parent_prepared, mutex_del_wake_rep, kernel_program_rep; entailer!. }
  destruct (Hopen before Hpre) as [[Hparent [Hprepare Hphase]] Hheap].
  pose proof Hparent as [Hvalid [Hlookup [Htype [Hfields Huse]]]].
  assert (Hprepared_lookup : prepared.(EventState).(inUsedEventStates) eid = Some event).
  { rewrite (mutex_del_prepare_event_state_eq sg mutex entry prepared Hprepare); exact Hlookup. }
  destruct (mutex_del_wake_loop_resources sg eid mutex before drained_heap frame Hlayout Hloop
    prepared event Hphase Hprepared_lookup Hheap) as [priorities [drained [Hbroadcast Hdrained]]].
  destruct (mutex_del_wake_broadcast_result sg eid mutex prepared event priorities drained
    Hphase Hprepared_lookup Hbroadcast) as [Hphase_after [Hdrained_lookup Hlength]].
  pose proof (mutex_del_wake_count_load sg drained eid (event_set_wait_list event []) drained_heap frame
    Hdrained_lookup Hdrained) as Hactual_count.
  assert (Ecount : count = encode_event_cnt_value (event_set_wait_list event []))
    by (eapply mutex_del_count_load_deterministic; eassumption).
  change (count = encode_event_cnt_value event) in Ecount; rewrite Ecount in Hceiling.
  rewrite (mutex_del_parent_cast_count sg eid entry event mutex Hparent),
    (proj2 (proj2 (mutex_del_parent_count_decode sg eid entry event mutex Hparent))) in Hceiling.
  subst ceiling.
  assert (Hreleased : (kernel_program_rep sg drained ** frame) released).
  { destruct (Z.eq_dec mutex.(mfPCP) 255) as [Hdisabled|Henabled]; [subst released; exact Hdrained|].
    assert (Hsentinel : sg.(osPrioMutexCeilDis) = 255)
      by (destruct Hvalid as [Hprofile _]; unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
    eapply mutex_del_wake_repeated_ceiling_store; try eassumption; congruence. }
  pose proof (mutex_del_recycle_stores_resources sg eid mutex drained (event_set_wait_list event [])
    released after frame Hphase_after Hdrained_lookup eq_refl Hreleased Hrecycle) as Hfinished.
  assert (Edrained : mutex_del_broadcast_state sg eid (length event.(waitList)) prepared = drained).
  { rewrite <- Hlength; apply mutex_del_broadcast_state_of_execution; exact Hbroadcast. }
  unfold mutex_del_always_checkpoint; rewrite Edrained; split; [|exact Hfinished].
  exists event, mutex; split; [exact Hlookup|]. split; [exact Htype|]. split; [exact Hfields|].
  cbn; exists prepared, priorities, drained; repeat split; assumption.
Qed.
