Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
From compcert.lib Require Import Integers.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_entry_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_public_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_irq_register_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_repeated_irq_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_save_irq_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_clients_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_owner_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_program_storage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_readonly_error_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_readonly_irq_save_source_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations KernelHeapObservation KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The selected source reads OSEventCnt as one little-endian unsigned
    short. This observation describes the two owned bytes, not a new
    machine transition or a permission supplied by an abstract event. *)
Definition mutex_del_count_load (address observed : Z) (heap : model) : Prop :=
  0 <= observed < 65536 /\ exists low high,
    heap.(ConAssertion.s_mem) address = value low /\
    heap.(ConAssertion.s_mem) (address + 1) = value high /\
    merge_short low high observed.

Lemma mutex_del_count_load_deterministic : forall address first second heap,
  mutex_del_count_load address first heap -> mutex_del_count_load address second heap -> first = second.
Proof.
  intros address first second heap [Hfirst [a [b [Ha [Hb Hmerge]]]]]
    [Hsecond [a' [b' [Ha' [Hb' Hmerge']]]]].
  assert (a = a') by congruence; assert (b = b') by congruence; subst a' b'.
  change (first mod 65536 = a mod 256 + b mod 256 * 256) in Hmerge.
  change (second mod 65536 = a mod 256 + b mod 256 * 256) in Hmerge'.
  rewrite (Z.mod_small first _ Hfirst) in Hmerge.
  rewrite (Z.mod_small second _ Hsecond) in Hmerge'; congruence.
Qed.

Lemma mutex_del_count_store_load : forall address observed (frame : Assertion) heap,
  (address # UShort |-> observed ** frame) heap -> mutex_del_count_load address observed heap.
Proof.
  intros address observed frame heap Howned.
  assert (Hsplit : address # UShort |-> observed ** frame |--
    coq_prop (0 <= observed < 65536) &&
    EX low high, coq_prop (merge_short low high observed) &&
      (store_byte address low ** (store_byte (address + 1) high ** frame))).
  { unfold store_ushort, store_2byte; Intros low high; Exists low high; entailer!; lia. }
  destruct (Hsplit heap Howned) as [Hrange [low [high [Hmerge Hcells]]]].
  assert (Hlow : exists encoded, heap.(ConAssertion.s_mem) address = value encoded /\ Byte.eqm low encoded).
  { eapply framed_byte_store_observation; exact Hcells. }
  assert (Hhigh : exists encoded, heap.(ConAssertion.s_mem) (address + 1) = value encoded /\ Byte.eqm high encoded).
  { assert (Horder : store_byte address low ** (store_byte (address + 1) high ** frame) |--
      store_byte (address + 1) high ** (store_byte address low ** frame)) by entailer!.
    eapply framed_byte_store_observation; exact (Horder heap Hcells). }
  destruct Hlow as [a [Ha Heqa]], Hhigh as [b [Hb Heqb]].
  split; [exact Hrange|]. exists a, b; split; [exact Ha|]. split; [exact Hb|].
  eapply merge_short_eqm; eassumption.
Qed.

(** Literal source order under the already acquired mask:
      Type=UNUSED; Ptr=OSEventFreeList; Cnt=0; OSEventFreeList=pe.
    Each multi-byte list is the physical effect of ONE typed C store.
    The free-list RHS is read from the actual heap after the Type store. *)
Definition mutex_del_recycle_stores (sg : StableGlobVars) (pe : Z)
  (before after : model) : Prop :=
  exists typed pointed counted free,
    kernel_heap_execution [(pe + OSEventType_off, 0)] before typed /\
    pointer_load sg.(g_OSEventFreeList) free typed /\
    kernel_heap_execution (pointer_store_writes (pe + OSEventPtr_off) free) typed pointed /\
    kernel_heap_execution (byte_list_writes (pe + OSEventCnt_off) [0; 0]) pointed counted /\
    kernel_heap_execution (pointer_store_writes sg.(g_OSEventFreeList) pe) counted after.

(** The old fields-merge theorem is reached only after these actual writes.
    This physical producer is shared by the no-wait branch below and by
    later prepare/wake sources once their own concrete calls are connected. *)
Lemma mutex_del_recycle_stores_resources : forall sg eid mutex state event before after (frame : Assertion),
  mutex_del_wake_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  encode_event_wait_grp event.(waitList) state.(TskState) = 0 ->
  (kernel_program_rep sg state ** frame) before ->
  mutex_del_recycle_stores sg (event_pool_addr sg eid) before after ->
  (kernel_program_inv sg (mutex_del_recycle_state sg eid event state) ** frame) after.
Proof.
  intros sg eid mutex state event before after frame Hphase He Hempty Hpre
    [typed [pointed [counted [free [Htype [Hread [Hptr [Hcount Hroot]]]]]]]].
  set (pe := event_pool_addr sg eid) in *.
  set (old_free := event_encode_pool_link sg (hd_error state.(EventState).(unUsedEventStates))).
  set (residual := (pe + 10) # UChar |-> encode_event_wait_grp event.(waitList) state.(TskState) **
    mutex_del_parent_event_rest sg state eid event ** unmap_table_rep sg ** frame).
  assert (Hopen : kernel_program_rep sg state ** frame |--
    (pe + 0) # UChar |-> encode_event_type event.(eventType) **
    ((pe + 4) # Ptr |-> encode_event_ptr_value sg event **
     (pe + 8) # UShort |-> encode_event_cnt_value event **
     sg.(g_OSEventFreeList) # Ptr |-> old_free ** residual)).
  { unfold kernel_program_rep, residual, pe, old_free.
    sep_apply_l_atomic (mutex_del_parent_event_core_split sg state eid event He); entailer!. }
  pose proof (Hopen before Hpre) as Hcells.
  assert (Hpe : 0 <= pe < 4294967296).
  { destruct Hcells as [cell [rest [Hjoin [[[Haddress Hvalue] Hbytes] Hrest]]]].
    unfold isvalidptr_char, addr_max_unsigned in Haddress; cbn in Haddress; lia. }
  destruct (kernel_heap_framed_uchar_store (pe + 0) (encode_event_type event.(eventType)) 0 _ before
    ltac:(lia) Hcells) as [produced [Hwrite Htyped]].
  assert (produced = typed) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hread_order : (pe + 0) # UChar |-> 0 **
      ((pe + 4) # Ptr |-> encode_event_ptr_value sg event **
       (pe + 8) # UShort |-> encode_event_cnt_value event **
       sg.(g_OSEventFreeList) # Ptr |-> old_free ** residual) |--
    sg.(g_OSEventFreeList) # Ptr |-> old_free **
      ((pe + 0) # UChar |-> 0 ** (pe + 4) # Ptr |-> encode_event_ptr_value sg event **
       (pe + 8) # UShort |-> encode_event_cnt_value event ** residual)) by entailer!.
  pose proof (framed_pointer_store_load _ _ _ _ (Hread_order typed Htyped)) as Hactual_free.
  assert (free = old_free) by (eapply pointer_load_deterministic; eassumption); subst free.
  assert (Hptr_order : (pe + 0) # UChar |-> 0 **
      ((pe + 4) # Ptr |-> encode_event_ptr_value sg event **
       (pe + 8) # UShort |-> encode_event_cnt_value event **
       sg.(g_OSEventFreeList) # Ptr |-> old_free ** residual) |--
    (pe + 4) # Ptr |->_ ** ((pe + 0) # UChar |-> 0 **
      (pe + 8) # UShort |-> encode_event_cnt_value event **
      sg.(g_OSEventFreeList) # Ptr |-> old_free ** residual)).
  { sep_apply_l_atomic (store_ptr_undef_store_ptr (pe + 4) (encode_event_ptr_value sg event)); entailer!. }
  destruct (framed_pointer_store_execution (pe + 4) old_free _ typed (proj1 Hactual_free)
    (Hptr_order typed Htyped)) as [produced [Hwrite_ptr Hpointed]].
  assert (produced = pointed) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hcount_order : (pe + 4) # Ptr |-> old_free ** ((pe + 0) # UChar |-> 0 **
      (pe + 8) # UShort |-> encode_event_cnt_value event **
      sg.(g_OSEventFreeList) # Ptr |-> old_free ** residual) |--
    (pe + 8) # UShort |->_ ** ((pe + 0) # UChar |-> 0 ** (pe + 4) # Ptr |-> old_free **
      sg.(g_OSEventFreeList) # Ptr |-> old_free ** residual)).
  { sep_apply_l_atomic (store_ushort_undef_store_ushort (pe + 8) (encode_event_cnt_value event)); entailer!. }
  destruct (event_create_count_store_execution (pe + 8) 0 _ pointed ltac:(lia)
    (Hcount_order pointed Hpointed)) as [produced [Hwrite_count Hcounted]].
  assert (produced = counted) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hroot_order : (pe + 8) # UShort |-> 0 ** ((pe + 0) # UChar |-> 0 **
      (pe + 4) # Ptr |-> old_free ** sg.(g_OSEventFreeList) # Ptr |-> old_free ** residual) |--
    sg.(g_OSEventFreeList) # Ptr |->_ ** ((pe + 0) # UChar |-> 0 **
      (pe + 4) # Ptr |-> old_free ** (pe + 8) # UShort |-> 0 ** residual)).
  { sep_apply_l_atomic (store_ptr_undef_store_ptr sg.(g_OSEventFreeList) old_free); entailer!. }
  destruct (framed_pointer_store_execution sg.(g_OSEventFreeList) pe _ counted Hpe
    (Hroot_order counted Hcounted)) as [produced [Hwrite_root Hfinished]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hclose : sg.(g_OSEventFreeList) # Ptr |-> pe ** ((pe + 0) # UChar |-> 0 **
      (pe + 4) # Ptr |-> old_free ** (pe + 8) # UShort |-> 0 ** residual) |--
    kernel_program_inv sg (mutex_del_recycle_state sg eid event state) ** frame).
  { unfold residual, pe, old_free.
    assert (Horder :
      sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid **
      ((event_pool_addr sg eid + 0) # UChar |-> 0 **
       (event_pool_addr sg eid + 4) # Ptr |->
         event_encode_pool_link sg (hd_error state.(EventState).(unUsedEventStates)) **
       (event_pool_addr sg eid + 8) # UShort |-> 0 **
       ((event_pool_addr sg eid + 10) # UChar |->
          encode_event_wait_grp event.(waitList) state.(TskState) **
        mutex_del_parent_event_rest sg state eid event ** unmap_table_rep sg ** frame)) |--
      (((event_pool_addr sg eid + 0) # UChar |-> 0 **
        (event_pool_addr sg eid + 4) # Ptr |->
          event_encode_pool_link sg (hd_error state.(EventState).(unUsedEventStates)) **
        (event_pool_addr sg eid + 8) # UShort |-> 0 **
        (event_pool_addr sg eid + 10) # UChar |->
          encode_event_wait_grp event.(waitList) state.(TskState) **
        sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid **
        mutex_del_parent_event_rest sg state eid event) ** unmap_table_rep sg) ** frame)
      by entailer!.
    eapply derivable1_trans; [exact Horder|].
    sep_apply_l_atomic (mutex_del_program_recycle_fields_merge sg eid mutex state event Hphase He Hempty).
    entailer!. }
  exact (Hclose after Hfinished).
Qed.

Lemma mutex_del_program_count_load : forall sg state pe eid event heap (frame : Assertion),
  pe = event_addr sg eid -> mutex_query_lookup state eid event ->
  (kernel_program_inv sg state ** frame) heap ->
  mutex_del_count_load (pe + OSEventCnt_off) (encode_event_cnt_value event) heap.
Proof.
  intros sg state pe eid event heap frame -> Hlookup Hpre.
  assert (Hsplit : kernel_program_inv sg state ** frame |--
    (event_pool_addr sg eid + 8) # UShort |-> encode_event_cnt_value event ** TT).
  { unfold kernel_program_inv, kernel_program_rep; Intros_p Hvalid.
    sep_apply_l_atomic (mutex_del_parent_event_core_split sg state eid event Hlookup).
    entailer!; intros ? ?; exact I. }
  eapply mutex_del_count_store_load; exact (Hsplit heap Hpre).
Qed.

(** The owner-pointer guard is read before the ceiling slot is released.
    This observation borrows the actual ECB bytes from the acquired heap. *)
Lemma mutex_del_program_pointer_load : forall sg state eid event heap (frame : Assertion),
  mutex_query_lookup state eid event ->
  (kernel_program_inv sg state ** frame) heap ->
  pointer_load (event_pool_addr sg eid + OSEventPtr_off) (encode_event_ptr_value sg event) heap.
Proof.
  intros sg state eid event heap frame Hlookup Hpre.
  assert (Hsplit : kernel_program_inv sg state ** frame |--
    (event_pool_addr sg eid + 4) # Ptr |-> encode_event_ptr_value sg event ** TT).
  { unfold kernel_program_inv, kernel_program_rep; Intros_p Hvalid.
    sep_apply_l_atomic (mutex_del_parent_event_core_split sg state eid event Hlookup).
    entailer!; intros ? ?; exact I. }
  eapply framed_pointer_store_load; exact (Hsplit heap Hpre).
Qed.

(** The literal OSTCBPrioTbl[pcp]=NULL store reaches the already proved
    released-state owner. Its domain is obtained from the actual count and
    pointer guards below. No invariant is asserted between this store and
    the later ECB recycle while the published mutex still owns its PCP. *)
Lemma mutex_del_unowned_ceiling_store_resources : forall sg eid state event mutex before after
  (frame : Assertion),
  mutex_del_parent_entry sg eid state event mutex -> mutex.(mfPCP) <> 255 ->
  (kernel_program_inv sg state ** frame) before ->
  pointer_load (event_pool_addr sg eid + OSEventPtr_off) 0 before ->
  kernel_heap_execution
    (pointer_store_writes (sg.(g_OSTCBPrioTbl) + mutex.(mfPCP) * sizeof(PTR)) 0) before after ->
  (mutex_del_parent_prepared sg eid state (mutex_del_released_state state mutex.(mfPCP)) event mutex **
    unmap_table_rep sg ** frame) after.
Proof.
  intros sg eid state event mutex before after frame Hparent Hpcp Hpre Hread Hstore.
  pose proof (proj1 (proj2 Hparent)) as Hlookup.
  pose proof (mutex_del_program_pointer_load sg state eid event before frame Hlookup Hpre) as Hactual.
  assert (Hptr : encode_event_ptr_value sg event = 0)
    by (eapply pointer_load_deterministic; eassumption).
  assert (Hceiling : mutex_del_parent_ceiling_at sg eid state mutex.(mfPCP)).
  { exists event, mutex; split; [exact Hparent|].
    symmetry; exact (proj2 (proj2 (mutex_del_parent_count_decode sg eid state event mutex Hparent))). }
  pose proof (mutex_del_parent_enabled_ceiling_in_range sg eid state mutex.(mfPCP) Hceiling Hpcp)
    as Hrange.
  set (slot := sg.(g_OSTCBPrioTbl) + mutex.(mfPCP) * sizeof(PTR)).
  set (residual := store_prio_tbl_missing_i sg state.(TskState).(prioTbl) mutex.(mfPCP) **
    UCOS2_raw_rep_missing_priority_table sg state ** unmap_table_rep sg ** frame).
  assert (Hopen : kernel_program_inv sg state ** frame |-- slot # Ptr |->_ ** residual).
  { unfold kernel_program_inv, kernel_program_rep, residual, slot; Intros_p Hvalid.
    rewrite UCOS2_raw_rep_priority_table_equiv.
    sep_apply_l_atomic (store_prio_tbl_split_cell sg state.(TskState).(prioTbl) mutex.(mfPCP) Hrange).
    sep_apply_l_atomic (store_ptr_undef_store_ptr
      (sg.(g_OSTCBPrioTbl) + mutex.(mfPCP) * sizeof(PTR))
      (prio_tbl_entry_to_addr sg (state.(TskState).(prioTbl) mutex.(mfPCP)))); entailer!. }
  destruct (framed_pointer_store_execution slot 0 residual before ltac:(lia) (Hopen before Hpre))
    as [produced [Hwrite Hreleased]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hclose : slot # Ptr |-> 0 ** residual |--
    mutex_del_parent_prepared sg eid state (mutex_del_released_state state mutex.(mfPCP)) event mutex **
      unmap_table_rep sg ** frame).
  { unfold slot, residual.
    sep_apply_l_atomic (mutex_del_released_resources_merge_cell sg state mutex.(mfPCP) Hrange).
    sep_apply_l_atomic (mutex_del_parent_prepare_unowned sg eid state event mutex Hparent Hpcp Hptr).
    entailer!. }
  exact (Hclose after Hreleased).
Qed.

(** Consume the actual EffectivePrio call and the outer current-priority
    read in the source branch where RdyAtPrio is skipped. The layout premise
    is the existing public Del layout, not a new pointer/safety assumption. *)
Lemma mutex_del_owned_ceiling_skip_resources : forall sg eid state event mutex pointer priority
  before after (frame : Assertion),
  mutex_del_parent_layout sg -> mutex_del_parent_entry sg eid state event mutex ->
  mutex.(mfPCP) <> 255 -> pointer <> 0 ->
  (kernel_program_inv sg state ** frame) before ->
  pointer_load (event_pool_addr sg eid + OSEventPtr_off) pointer before ->
  kernel_heap_execution
    (pointer_store_writes (sg.(g_OSTCBPrioTbl) + mutex.(mfPCP) * sizeof(PTR)) 0) before after ->
  mutex_del_effective_priority_reads sg pointer after 0 priority ->
  uchar_load (tcb_field_address pointer TCBPrio) priority after ->
  (mutex_del_parent_prepared sg eid state (mutex_del_released_state state mutex.(mfPCP)) event mutex **
    unmap_table_rep sg ** frame) after.
Proof.
  intros sg eid state event mutex pointer priority before after frame Hlayout Hparent Hpcp Hnonzero
    Hpre Hread Hstore Hreads Hcompare.
  pose proof Hparent as [Hvalid [Hlookup [Htype [Hfields Huse]]]].
  pose proof Hvalid as [Hprofile [_ [_ [_ [Hcross _]]]]].
  pose proof (mutex_del_program_pointer_load sg state eid event before frame Hlookup Hpre) as Hactual.
  assert (Hptr : encode_event_ptr_value sg event = pointer)
    by (eapply pointer_load_deterministic; eassumption).
  assert (Howner_pointer : exists owner, mutex.(mfOwner) = Some owner /\ pointer = task_slot_addr sg owner).
  { unfold encode_event_ptr_value in Hptr; rewrite Htype, Hfields in Hptr.
    destruct mutex.(mfOwner) as [owner|] eqn:Howner; cbn [encode_task_link] in Hptr;
      [exists owner; split; congruence|congruence]. }
  destruct Howner_pointer as [owner [Howner ->]].
  destruct Hcross as [_ [Hsnap _]].
  destruct (Hsnap eid event mutex owner Hlookup Htype Hfields Howner)
    as [node [base [snapshot [Hnode Hrest]]]].
  assert (Hceiling : mutex_del_parent_ceiling_at sg eid state mutex.(mfPCP)).
  { exists event, mutex; split; [exact Hparent|].
    symmetry; exact (proj2 (proj2 (mutex_del_parent_count_decode sg eid state event mutex Hparent))). }
  pose proof (mutex_del_parent_enabled_ceiling_in_range sg eid state mutex.(mfPCP) Hceiling Hpcp) as Hrange.
  assert (Hforget : kernel_program_inv sg state ** frame |-- kernel_program_rep sg state ** frame)
    by (unfold kernel_program_inv; entailer!).
  pose proof (mutex_del_ceiling_store_resources sg state mutex.(mfPCP) before after frame Hrange
    (Hforget before Hpre) Hstore) as Hreleased.
  assert (Hfocus : mutex_del_released_resources sg state mutex.(mfPCP) ** unmap_table_rep sg ** frame |--
    mutex_del_priority_input sg state mutex.(mfPCP) owner node **
      mutex_del_priority_frame sg state owner ** unmap_table_rep sg ** frame).
  { sep_apply_l_atomic (mutex_del_released_resources_split_priority sg state mutex.(mfPCP) owner node Hprofile Hnode).
    entailer!. }
  pose proof (Hfocus after Hreleased) as Hfocused.
  assert (Hscan_order : mutex_del_priority_input sg state mutex.(mfPCP) owner node **
      mutex_del_priority_frame sg state owner ** unmap_table_rep sg ** frame |--
    tcb64_storage_rep (task_slot_addr sg owner) (task_tcb64_image sg node) **
      PtrArray.full sg.(g_OSTCBPrioTbl) 64 (mutex_del_priority_values sg (mutex_del_released_table state mutex.(mfPCP))) ** TT).
  { unfold mutex_del_priority_input; entailer!; intros ? ?; exact I. }
  pose proof (mutex_del_effective_priority_reads_result sg (task_slot_addr sg owner)
    (task_tcb64_image sg node) (mutex_del_priority_values sg (mutex_del_released_table state mutex.(mfPCP)))
    node.(curPrio) after (TT) priority eq_refl (Hscan_order after Hfocused) Hreads) as Hscan.
  assert (Hfield_order : mutex_del_priority_input sg state mutex.(mfPCP) owner node **
      mutex_del_priority_frame sg state owner ** unmap_table_rep sg ** frame |--
    tcb64_storage_rep (task_slot_addr sg owner) (task_tcb64_image sg node) ** TT).
  { unfold mutex_del_priority_input; entailer!; intros ? ?; exact I. }
  assert (Hnotreserved : task_slot_addr sg owner <> 1).
  { assert (Haddresses : forall base, tcb_field_address base TCBStkPtr = base)
      by (unfold mutex_del_parent_layout in Hlayout; tauto).
    destruct (Hfield_order after Hfocused) as [owned [rest [Hjoin [Howned Hrest_owned]]]].
    exact (proj1 (mutex_del_parent_storage_pointer_not_reserved
      (task_slot_addr sg owner) (task_tcb64_image sg node) node.(tcbStkPtr)
      (Haddresses _) eq_refl owned Howned)). }
  pose proof (mutex_del_priority_field_load (task_slot_addr sg owner) (task_tcb64_image sg node)
    node.(curPrio) after (TT) eq_refl (Hfield_order after Hfocused)) as Hactual_priority.
  assert (Hsame : node.(curPrio) = priority) by (eapply uchar_load_deterministic; eassumption).
  assert (Henabled : mutex_pcp_enabled sg mutex).
  { assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255)
      by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
    unfold mutex_pcp_enabled; congruence. }
  pose proof (mutex_del_program_prepare_owner sg state eid event mutex owner node priority
    Hparent Howner Henabled Hnode Hnotreserved Hscan) as Hmerge.
  assert (Hprepared_state : mutex_del_owner_priority_state sg state mutex.(mfPCP) owner node priority =
    mutex_del_released_state state mutex.(mfPCP)).
  { unfold mutex_del_owner_priority_state; destruct Z.eq_dec; [reflexivity|contradiction]. }
  rewrite Hprepared_state in Hmerge.
  destruct (Z.eq_dec node.(curPrio) priority); [|contradiction].
  assert (Hclose : mutex_del_priority_input sg state mutex.(mfPCP) owner node **
      mutex_del_priority_frame sg state owner ** unmap_table_rep sg ** frame |--
    mutex_del_parent_prepared sg eid state (mutex_del_released_state state mutex.(mfPCP)) event mutex **
      unmap_table_rep sg ** frame).
  { sep_apply_l_atomic Hmerge; entailer!. }
  exact (Hclose after Hfocused).
Qed.

(** The RdyAtPrio source borrows exactly the existing helper's physical
    input.  Its three source segments below contain reads and ordered stores,
    not an assumed helper postcondition or an InsideCritical conversion. *)
Definition mutex_del_priority_heap (sg : StableGlobVars) (pointer : Z)
  (image : TCBCommonImage) (table rows : list Z) (group current current_prio : Z) : Assertion :=
  tcb64_storage_rep pointer image ** PtrArray.full sg.(g_OSTCBPrioTbl) 64 table **
  UCharArray.full sg.(g_OSRdyTbl) 8 rows ** sg.(g_OSRdyGrp) # UChar |-> group **
  sg.(g_OSTCBCur) # Ptr |-> current ** sg.(g_OSPrioCur) # UChar |-> current_prio.

Definition mutex_del_priority_byte_field (field : TCBField) : Prop :=
  In field [TCBPrio; TCBX; TCBY; TCBBitX; TCBBitY].

Lemma mutex_del_priority_byte_load : forall sg pointer image table rows group current current_prio
  field observed heap (frame : Assertion),
  mutex_del_priority_byte_field field -> image field = Some observed ->
  (mutex_del_priority_heap sg pointer image table rows group current current_prio ** frame) heap ->
  uchar_load (tcb_field_address pointer field) observed heap.
Proof.
  intros sg pointer image table rows group current current_prio field observed heap frame Hfield Himage Hpre.
  assert (Hopen : mutex_del_priority_heap sg pointer image table rows group current current_prio ** frame |--
    (tcb_field_address pointer field) # UChar |-> observed ** TT).
  { unfold mutex_del_priority_heap; sep_apply_l_atomic (tcb64_storage_split pointer image field).
    rewrite Himage; destruct field; unfold mutex_del_priority_byte_field in Hfield; simpl in Hfield;
      try solve [intuition discriminate]; cbn [tcb_cell]; entailer!; intros ? ?; exact I. }
  eapply framed_uchar_store_load; exact (Hopen heap Hpre).
Qed.

Lemma mutex_del_priority_byte_store : forall sg pointer image table rows group current current_prio
  field stored before after (frame : Assertion),
  mutex_del_priority_byte_field field -> 0 <= stored < 256 ->
  (mutex_del_priority_heap sg pointer image table rows group current current_prio ** frame) before ->
  kernel_heap_execution [(tcb_field_address pointer field, stored)] before after ->
  (mutex_del_priority_heap sg pointer (tcb_write image field (Some stored))
    table rows group current current_prio ** frame) after.
Proof.
  intros sg pointer image table rows group current current_prio field stored before after frame
    Hfield Hrange Hpre Hrun.
  set (residual := tcb64_storage_without pointer field image **
    PtrArray.full sg.(g_OSTCBPrioTbl) 64 table ** UCharArray.full sg.(g_OSRdyTbl) 8 rows **
    sg.(g_OSRdyGrp) # UChar |-> group ** sg.(g_OSTCBCur) # Ptr |-> current **
    sg.(g_OSPrioCur) # UChar |-> current_prio ** frame).
  assert (Hopen : mutex_del_priority_heap sg pointer image table rows group current current_prio ** frame |--
    (tcb_field_address pointer field) # UChar |->_ ** residual).
  { unfold mutex_del_priority_heap, residual; sep_apply_l_atomic (tcb64_storage_split pointer image field).
    destruct field; unfold mutex_del_priority_byte_field in Hfield; simpl in Hfield; try solve [intuition discriminate];
      cbn [tcb_cell]; destruct (image _) as [old|];
      entailer!; apply store_uchar_undef_store_uchar. }
  destruct (framed_uchar_noninit_store_execution _ stored residual before Hrange (Hopen before Hpre))
    as [produced [Hwrite Hproduced]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hclose : (tcb_field_address pointer field) # UChar |-> stored ** residual |--
    mutex_del_priority_heap sg pointer (tcb_write image field (Some stored)) table rows group current current_prio ** frame).
  { unfold mutex_del_priority_heap, residual.
    assert (Hcell : (tcb_field_address pointer field) # UChar |-> stored = tcb_cell pointer field (Some stored)).
    { destruct field; unfold mutex_del_priority_byte_field in Hfield; simpl in Hfield;
        try solve [intuition discriminate]; reflexivity. }
    rewrite Hcell; sep_apply_l_atomic (tcb64_storage_merge_updated pointer image field (Some stored)); entailer!. }
  exact (Hclose after Hproduced).
Qed.

Lemma mutex_del_priority_row_load : forall sg pointer image table rows group current current_prio
  index heap (frame : Assertion),
  0 <= index < 8 ->
  (mutex_del_priority_heap sg pointer image table rows group current current_prio ** frame) heap ->
  uchar_load (sg.(g_OSRdyTbl) + index) (Znth index rows 0) heap.
Proof.
  intros sg pointer image table rows group current current_prio index heap frame Hindex Hpre.
  assert (Hopen : mutex_del_priority_heap sg pointer image table rows group current current_prio ** frame |--
    (sg.(g_OSRdyTbl) + index) # UChar |-> Znth index rows 0 ** TT).
  { unfold mutex_del_priority_heap.
    sep_apply_l_atomic (UCharArray.full_split_to_missing_i sg.(g_OSRdyTbl) index 8 rows 0 Hindex).
    unfold StoreUCharAsElement.storeA; replace (sg.(g_OSRdyTbl) + index * sizeof(UCHAR))
      with (sg.(g_OSRdyTbl) + index) by (cbn; lia).
    entailer!; intros ? ?; exact I. }
  eapply framed_uchar_store_load; exact (Hopen heap Hpre).
Qed.

Lemma mutex_del_priority_row_store : forall sg pointer image table rows group current current_prio
  index stored before after (frame : Assertion),
  0 <= index < 8 -> 0 <= stored < 256 ->
  (mutex_del_priority_heap sg pointer image table rows group current current_prio ** frame) before ->
  kernel_heap_execution [(sg.(g_OSRdyTbl) + index, stored)] before after ->
  (mutex_del_priority_heap sg pointer image table (replace_Znth index stored rows)
    group current current_prio ** frame) after.
Proof.
  intros sg pointer image table rows group current current_prio index stored before after frame
    Hindex Hrange Hpre Hrun.
  set (residual := UCharArray.missing_i sg.(g_OSRdyTbl) index 0 8 rows **
    tcb64_storage_rep pointer image ** PtrArray.full sg.(g_OSTCBPrioTbl) 64 table **
    sg.(g_OSRdyGrp) # UChar |-> group ** sg.(g_OSTCBCur) # Ptr |-> current **
    sg.(g_OSPrioCur) # UChar |-> current_prio ** frame).
  assert (Hopen : mutex_del_priority_heap sg pointer image table rows group current current_prio ** frame |--
    (sg.(g_OSRdyTbl) + index) # UChar |-> Znth index rows 0 ** residual).
  { unfold mutex_del_priority_heap, residual.
    sep_apply_l_atomic (UCharArray.full_split_to_missing_i sg.(g_OSRdyTbl) index 8 rows 0 Hindex).
    unfold StoreUCharAsElement.storeA; replace (sg.(g_OSRdyTbl) + index * sizeof(UCHAR))
      with (sg.(g_OSRdyTbl) + index) by (cbn; lia); entailer!. }
  destruct (kernel_heap_framed_uchar_store _ _ stored residual before Hrange (Hopen before Hpre))
    as [produced [Hwrite Hproduced]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hclose : (sg.(g_OSRdyTbl) + index) # UChar |-> stored ** residual |--
    mutex_del_priority_heap sg pointer image table (replace_Znth index stored rows) group current current_prio ** frame).
  { unfold mutex_del_priority_heap, residual.
    replace (sg.(g_OSRdyTbl) + index) with (sg.(g_OSRdyTbl) + index * sizeof(UCHAR)) by (cbn; lia).
    sep_apply_l_atomic (UCharArray.missing_i_merge_to_full sg.(g_OSRdyTbl) index 8 stored rows Hindex); entailer!. }
  exact (Hclose after Hproduced).
Qed.

Lemma mutex_del_priority_globals_load : forall sg pointer image table rows group current current_prio
  heap (frame : Assertion),
  (mutex_del_priority_heap sg pointer image table rows group current current_prio ** frame) heap ->
  uchar_load sg.(g_OSRdyGrp) group heap /\ pointer_load sg.(g_OSTCBCur) current heap.
Proof.
  intros sg pointer image table rows group current current_prio heap frame Hpre; split.
  - assert (Hopen : mutex_del_priority_heap sg pointer image table rows group current current_prio ** frame |--
      sg.(g_OSRdyGrp) # UChar |-> group ** TT)
      by (unfold mutex_del_priority_heap; entailer!; intros ? ?; exact I).
    eapply framed_uchar_store_load; exact (Hopen heap Hpre).
  - assert (Hopen : mutex_del_priority_heap sg pointer image table rows group current current_prio ** frame |--
      sg.(g_OSTCBCur) # Ptr |-> current ** TT)
      by (unfold mutex_del_priority_heap; entailer!; intros ? ?; exact I).
    eapply framed_pointer_store_load; exact (Hopen heap Hpre).
Qed.

Lemma mutex_del_priority_group_store : forall sg pointer image table rows group current current_prio
  stored before after (frame : Assertion),
  0 <= stored < 256 ->
  (mutex_del_priority_heap sg pointer image table rows group current current_prio ** frame) before ->
  kernel_heap_execution [(sg.(g_OSRdyGrp), stored)] before after ->
  (mutex_del_priority_heap sg pointer image table rows stored current current_prio ** frame) after.
Proof.
  intros sg pointer image table rows group current current_prio stored before after frame Hrange Hpre Hrun.
  set (residual := tcb64_storage_rep pointer image ** PtrArray.full sg.(g_OSTCBPrioTbl) 64 table **
    UCharArray.full sg.(g_OSRdyTbl) 8 rows ** sg.(g_OSTCBCur) # Ptr |-> current **
    sg.(g_OSPrioCur) # UChar |-> current_prio ** frame).
  assert (Hopen : mutex_del_priority_heap sg pointer image table rows group current current_prio ** frame |--
    sg.(g_OSRdyGrp) # UChar |-> group ** residual)
    by (unfold mutex_del_priority_heap, residual; entailer!).
  destruct (kernel_heap_framed_uchar_store _ group stored residual before Hrange (Hopen before Hpre))
    as [produced [Hwrite Hproduced]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hclose : sg.(g_OSRdyGrp) # UChar |-> stored ** residual |--
    mutex_del_priority_heap sg pointer image table rows stored current current_prio ** frame)
    by (unfold mutex_del_priority_heap, residual; entailer!).
  exact (Hclose after Hproduced).
Qed.

Lemma mutex_del_priority_current_store : forall sg pointer image table rows group current current_prio
  stored before after (frame : Assertion),
  0 <= stored < 256 ->
  (mutex_del_priority_heap sg pointer image table rows group current current_prio ** frame) before ->
  kernel_heap_execution [(sg.(g_OSPrioCur), stored)] before after ->
  (mutex_del_priority_heap sg pointer image table rows group current stored ** frame) after.
Proof.
  intros sg pointer image table rows group current current_prio stored before after frame Hrange Hpre Hrun.
  set (residual := tcb64_storage_rep pointer image ** PtrArray.full sg.(g_OSTCBPrioTbl) 64 table **
    UCharArray.full sg.(g_OSRdyTbl) 8 rows ** sg.(g_OSRdyGrp) # UChar |-> group **
    sg.(g_OSTCBCur) # Ptr |-> current ** frame).
  assert (Hopen : mutex_del_priority_heap sg pointer image table rows group current current_prio ** frame |--
    sg.(g_OSPrioCur) # UChar |-> current_prio ** residual)
    by (unfold mutex_del_priority_heap, residual; entailer!).
  destruct (kernel_heap_framed_uchar_store _ current_prio stored residual before Hrange (Hopen before Hpre))
    as [produced [Hwrite Hproduced]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hclose : sg.(g_OSPrioCur) # UChar |-> stored ** residual |--
    mutex_del_priority_heap sg pointer image table rows group current stored ** frame)
    by (unfold mutex_del_priority_heap, residual; entailer!).
  exact (Hclose after Hproduced).
Qed.

Lemma mutex_del_priority_table_store : forall sg pointer image table rows group current current_prio
  priority before after (frame : Assertion),
  0 <= priority < 64 -> 0 <= pointer < 4294967296 ->
  (mutex_del_priority_heap sg pointer image table rows group current current_prio ** frame) before ->
  kernel_heap_execution (pointer_store_writes (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) pointer) before after ->
  (mutex_del_priority_heap sg pointer image (replace_Znth priority pointer table) rows
    group current current_prio ** frame) after.
Proof.
  intros sg pointer image table rows group current current_prio priority before after frame
    Hpriority Hpointer Hpre Hrun.
  set (residual := PtrArray.missing_i sg.(g_OSTCBPrioTbl) priority 0 64 table **
    tcb64_storage_rep pointer image ** UCharArray.full sg.(g_OSRdyTbl) 8 rows **
    sg.(g_OSRdyGrp) # UChar |-> group ** sg.(g_OSTCBCur) # Ptr |-> current **
    sg.(g_OSPrioCur) # UChar |-> current_prio ** frame).
  assert (Hopen : mutex_del_priority_heap sg pointer image table rows group current current_prio ** frame |--
    (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |->_ ** residual).
  { unfold mutex_del_priority_heap, residual.
    sep_apply_l_atomic (PtrArray.full_split_to_missing_i sg.(g_OSTCBPrioTbl) priority 64 table 0 Hpriority).
    unfold StorePtrAsElement.storeA.
    sep_apply_l_atomic (store_ptr_undef_store_ptr
      (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) (Znth priority table 0)); entailer!. }
  destruct (framed_pointer_store_execution _ pointer residual before Hpointer (Hopen before Hpre))
    as [produced [Hwrite Hproduced]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hclose : (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |-> pointer ** residual |--
    mutex_del_priority_heap sg pointer image (replace_Znth priority pointer table) rows group current current_prio ** frame).
  { unfold mutex_del_priority_heap, residual.
    sep_apply_l_atomic (PtrArray.missing_i_merge_to_full sg.(g_OSTCBPrioTbl) priority 64 pointer table Hpriority); entailer!. }
  exact (Hclose after Hproduced).
Qed.

Definition mutex_del_priority_remove_execution (sg : StableGlobVars) (pointer : Z)
  (ready : bool) (before after : model) : Prop :=
  exists y bitx row,
    uchar_load (tcb_field_address pointer TCBY) y before /\
    uchar_load (tcb_field_address pointer TCBBitX) bitx before /\
    uchar_load (sg.(g_OSRdyTbl) + y) row before /\
    ready = negb (Z.eqb (Z.land row bitx) 0) /\
    if ready then exists cleared,
      let value := Z.land row (unsigned_last_nbits (Z.lnot bitx) 8) in
      kernel_heap_execution [(sg.(g_OSRdyTbl) + y, value)] before cleared /\
      uchar_load (sg.(g_OSRdyTbl) + y) value cleared /\
      if Z.eqb value 0 then exists bity group,
        uchar_load (tcb_field_address pointer TCBBitY) bity cleared /\
        uchar_load sg.(g_OSRdyGrp) group cleared /\
        kernel_heap_execution [(sg.(g_OSRdyGrp), Z.land group (unsigned_last_nbits (Z.lnot bity) 8))] cleared after
      else after = cleared
    else after = before.

Definition mutex_del_priority_assign_execution (sg : StableGlobVars) (pointer priority : Z)
  (before after : model) : Prop :=
  exists prio_stored current_stored y_stored x_stored bity_stored current y x,
    kernel_heap_execution [(tcb_field_address pointer TCBPrio, priority)] before prio_stored /\
    pointer_load sg.(g_OSTCBCur) current prio_stored /\
    (if Z.eq_dec pointer current
     then kernel_heap_execution [(sg.(g_OSPrioCur), priority)] prio_stored current_stored
     else current_stored = prio_stored) /\
    kernel_heap_execution [(tcb_field_address pointer TCBY, tcb_y_of_prio priority)] current_stored y_stored /\
    kernel_heap_execution [(tcb_field_address pointer TCBX, tcb_x_of_prio priority)] y_stored x_stored /\
    uchar_load (tcb_field_address pointer TCBY) y x_stored /\
    kernel_heap_execution [(tcb_field_address pointer TCBBitY, Z.shiftl 1 y)] x_stored bity_stored /\
    uchar_load (tcb_field_address pointer TCBX) x bity_stored /\
    kernel_heap_execution [(tcb_field_address pointer TCBBitX, Z.shiftl 1 x)] bity_stored after.

Definition mutex_del_priority_insert_execution (sg : StableGlobVars) (pointer : Z)
  (ready : bool) (before after : model) : Prop :=
  if ready then exists group_stored group bity y bitx row,
    uchar_load sg.(g_OSRdyGrp) group before /\
    uchar_load (tcb_field_address pointer TCBBitY) bity before /\
    kernel_heap_execution [(sg.(g_OSRdyGrp), Z.lor group bity)] before group_stored /\
    uchar_load (tcb_field_address pointer TCBY) y group_stored /\
    uchar_load (tcb_field_address pointer TCBBitX) bitx group_stored /\
    uchar_load (sg.(g_OSRdyTbl) + y) row group_stored /\
    kernel_heap_execution [(sg.(g_OSRdyTbl) + y, Z.lor row bitx)] group_stored after
  else after = before.

Definition mutex_del_rdy_at_priority_execution (sg : StableGlobVars) (pointer priority : Z)
  (before after : model) : Prop :=
  exists ready removed assigned inserted,
    mutex_del_priority_remove_execution sg pointer ready before removed /\
    mutex_del_priority_assign_execution sg pointer priority removed assigned /\
    mutex_del_priority_insert_execution sg pointer ready assigned inserted /\
    kernel_heap_execution (pointer_store_writes (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) pointer) inserted after.

Lemma mutex_del_priority_remove_resources : forall sg pointer image table rows group current current_prio
  old_y old_bitx old_bity ready before after (frame : Assertion),
  0 <= old_y < 8 -> image TCBY = Some old_y -> image TCBBitX = Some old_bitx ->
  image TCBBitY = Some old_bity ->
  (mutex_del_priority_heap sg pointer image table rows group current current_prio ** frame) before ->
  mutex_del_priority_remove_execution sg pointer ready before after ->
  ready = mutex_priority_was_ready rows old_y old_bitx /\
  (mutex_del_priority_heap sg pointer image table (mutex_priority_removed_rows rows old_y old_bitx)
    (mutex_priority_removed_group rows group old_y old_bitx old_bity) current current_prio ** frame) after.
Proof.
  intros sg pointer image table rows group current current_prio old_y old_bitx old_bity ready before after
    frame Hy Hiy Hibx Hiby Hpre (y & bitx & row & Hread_y & Hread_x & Hread_row & Hready & Hrun).
  pose proof (mutex_del_priority_byte_load sg pointer image table rows group current current_prio TCBY old_y
    before frame ltac:(unfold mutex_del_priority_byte_field; simpl; tauto) Hiy Hpre) as Hactual_y.
  assert (y = old_y) by (eapply uchar_load_deterministic; eassumption); subst y.
  pose proof (mutex_del_priority_byte_load sg pointer image table rows group current current_prio TCBBitX old_bitx
    before frame ltac:(unfold mutex_del_priority_byte_field; simpl; tauto) Hibx Hpre) as Hactual_x.
  assert (bitx = old_bitx) by (eapply uchar_load_deterministic; eassumption); subst bitx.
  pose proof (mutex_del_priority_row_load sg pointer image table rows group current current_prio old_y
    before frame Hy Hpre) as Hactual_row.
  assert (row = Znth old_y rows 0) by (eapply uchar_load_deterministic; eassumption); subst row.
  change (ready = mutex_priority_was_ready rows old_y old_bitx) in Hready; split; [exact Hready|].
  unfold mutex_priority_removed_rows, mutex_priority_removed_group; rewrite <- Hready.
  destruct ready; [|subst after; exact Hpre].
  destruct Hrun as [cleared [Hwrite [Hcheck Hclear]]].
  fold (mutex_priority_cleared_row rows old_y old_bitx) in Hwrite, Hcheck, Hclear.
  pose proof (mutex_del_priority_row_store sg pointer image table rows group current current_prio old_y
    (mutex_priority_cleared_row rows old_y old_bitx) before cleared frame Hy
    (mutex_priority_cleared_row_in_range__ready_bitmap_stages rows old_y old_bitx (proj1 Hactual_row))
    Hpre Hwrite) as Hcleared.
  destruct (Z.eqb (mutex_priority_cleared_row rows old_y old_bitx) 0); [|subst after; exact Hcleared].
  destruct Hclear as (bity & observed_group & Hread_bity & Hread_group & Hwrite_group).
  pose proof (mutex_del_priority_byte_load sg pointer image table _ group current current_prio TCBBitY old_bity
    cleared frame ltac:(unfold mutex_del_priority_byte_field; simpl; tauto) Hiby Hcleared) as Hactual_bity.
  assert (bity = old_bity) by (eapply uchar_load_deterministic; eassumption); subst bity.
  pose proof (proj1 (mutex_del_priority_globals_load sg pointer image table _ group current current_prio
    cleared frame Hcleared)) as Hactual_group.
  assert (observed_group = group) by (eapply uchar_load_deterministic; eassumption); subst observed_group.
  eapply mutex_del_priority_group_store; [|exact Hcleared|exact Hwrite_group].
  apply byte_land_in_range__ready_bitmap_stages; exact (proj1 Hactual_group).
Qed.

Lemma mutex_del_priority_assign_resources : forall sg pointer image table rows group current current_prio
  priority before after (frame : Assertion),
  0 <= priority < 64 ->
  (mutex_del_priority_heap sg pointer image table rows group current current_prio ** frame) before ->
  mutex_del_priority_assign_execution sg pointer priority before after ->
  (mutex_del_priority_heap sg pointer (mutex_priority_image image priority) table rows group current
    (mutex_priority_current pointer current current_prio priority) ** frame) after.
Proof.
  intros sg pointer image table rows group current current_prio priority before after frame Hp Hpre
    (prio_stored & current_stored & y_stored & x_stored & bity_stored & observed_current & y & x &
     Hprio & Hread_current & Hcurrent & Hy & Hx & Hread_y & Hbity & Hread_x & Hbitx).
  destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding priority Hp)
    as [Hxr [Hyr Hencoding]].
  pose proof (mutex_del_priority_byte_store sg pointer image table rows group current current_prio
    TCBPrio priority before prio_stored frame ltac:(unfold mutex_del_priority_byte_field; simpl; tauto)
    ltac:(lia) Hpre Hprio) as Hprio_owned.
  pose proof (proj2 (mutex_del_priority_globals_load sg pointer _ table rows group current current_prio
    prio_stored frame Hprio_owned)) as Hactual_current.
  assert (observed_current = current) by (eapply pointer_load_deterministic; eassumption); subst observed_current.
  assert (Hcurrent_owned :
    (mutex_del_priority_heap sg pointer (tcb_write image TCBPrio (Some priority)) table rows group current
      (mutex_priority_current pointer current current_prio priority) ** frame) current_stored).
  { unfold mutex_priority_current; destruct Z.eq_dec.
    - eapply mutex_del_priority_current_store; [lia|exact Hprio_owned|exact Hcurrent].
    - subst current_stored; exact Hprio_owned. }
  pose proof (mutex_del_priority_byte_store sg pointer _ table rows group current _ TCBY (tcb_y_of_prio priority)
    current_stored y_stored frame ltac:(unfold mutex_del_priority_byte_field; simpl; tauto) ltac:(lia)
    Hcurrent_owned Hy) as Hy_owned.
  pose proof (mutex_del_priority_byte_store sg pointer _ table rows group current _ TCBX (tcb_x_of_prio priority)
    y_stored x_stored frame ltac:(unfold mutex_del_priority_byte_field; simpl; tauto) ltac:(lia)
    Hy_owned Hx) as Hx_owned.
  pose proof (mutex_del_priority_byte_load sg pointer _ table rows group current _ TCBY (tcb_y_of_prio priority)
    x_stored frame ltac:(unfold mutex_del_priority_byte_field; simpl; tauto) eq_refl Hx_owned) as Hactual_y.
  assert (y = tcb_y_of_prio priority) by (eapply uchar_load_deterministic; eassumption); subst y.
  pose proof (mutex_del_priority_byte_store sg pointer _ table rows group current _ TCBBitY
    (tcb_bit_y_of_prio priority) x_stored bity_stored frame
    ltac:(unfold mutex_del_priority_byte_field; simpl; tauto)
    (single_bit_in_byte_range__ready_bitmap_stages _ Hyr) Hx_owned Hbity) as Hbity_owned.
  pose proof (mutex_del_priority_byte_load sg pointer _ table rows group current _ TCBX (tcb_x_of_prio priority)
    bity_stored frame ltac:(unfold mutex_del_priority_byte_field; simpl; tauto) eq_refl Hbity_owned) as Hactual_x.
  assert (x = tcb_x_of_prio priority) by (eapply uchar_load_deterministic; eassumption); subst x.
  eapply mutex_del_priority_byte_store; [unfold mutex_del_priority_byte_field; simpl; tauto| |exact Hbity_owned|exact Hbitx].
  exact (single_bit_in_byte_range__ready_bitmap_stages _ Hxr).
Qed.

Lemma mutex_del_priority_insert_resources : forall sg pointer image table rows group current current_prio
  priority ready before after (frame : Assertion),
  0 <= priority < 64 ->
  (mutex_del_priority_heap sg pointer (mutex_priority_image image priority) table rows group current current_prio ** frame) before ->
  mutex_del_priority_insert_execution sg pointer ready before after ->
  (mutex_del_priority_heap sg pointer (mutex_priority_image image priority) table
    (if ready then replace_Znth (tcb_y_of_prio priority)
      (Z.lor (Znth (tcb_y_of_prio priority) rows 0) (tcb_bit_x_of_prio priority)) rows else rows)
    (if ready then Z.lor group (tcb_bit_y_of_prio priority) else group) current current_prio ** frame) after.
Proof.
  intros sg pointer image table rows group current current_prio priority ready before after frame Hp Hpre Hrun.
  unfold mutex_del_priority_insert_execution in Hrun.
  destruct ready; [|subst after; exact Hpre].
  destruct Hrun as (group_stored & observed_group & bity & y & bitx & row &
    Hread_group & Hread_bity & Hgroup & Hread_y & Hread_bitx & Hread_row & Hrow).
  destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding priority Hp)
    as [Hxr [Hyr Hencoding]].
  pose proof (proj1 (mutex_del_priority_globals_load sg pointer _ table rows group current current_prio
    before frame Hpre)) as Hactual_group.
  assert (observed_group = group) by (eapply uchar_load_deterministic; eassumption); subst observed_group.
  pose proof (mutex_del_priority_byte_load sg pointer _ table rows group current current_prio TCBBitY
    (tcb_bit_y_of_prio priority) before frame ltac:(unfold mutex_del_priority_byte_field; simpl; tauto)
    eq_refl Hpre) as Hactual_bity.
  assert (bity = tcb_bit_y_of_prio priority) by (eapply uchar_load_deterministic; eassumption); subst bity.
  pose proof (mutex_del_priority_group_store sg pointer _ table rows group current current_prio
    (Z.lor group (tcb_bit_y_of_prio priority)) before group_stored frame
    (bitmap_lor_in_range 8 _ _ ltac:(lia) (proj1 Hactual_group) (proj1 Hactual_bity)) Hpre Hgroup) as Hgroup_owned.
  pose proof (mutex_del_priority_byte_load sg pointer _ table rows _ current current_prio TCBY
    (tcb_y_of_prio priority) group_stored frame ltac:(unfold mutex_del_priority_byte_field; simpl; tauto)
    eq_refl Hgroup_owned) as Hactual_y.
  assert (y = tcb_y_of_prio priority) by (eapply uchar_load_deterministic; eassumption); subst y.
  pose proof (mutex_del_priority_byte_load sg pointer _ table rows _ current current_prio TCBBitX
    (tcb_bit_x_of_prio priority) group_stored frame ltac:(unfold mutex_del_priority_byte_field; simpl; tauto)
    eq_refl Hgroup_owned) as Hactual_bitx.
  assert (bitx = tcb_bit_x_of_prio priority) by (eapply uchar_load_deterministic; eassumption); subst bitx.
  pose proof (mutex_del_priority_row_load sg pointer _ table rows _ current current_prio
    (tcb_y_of_prio priority) group_stored frame Hyr Hgroup_owned) as Hactual_row.
  assert (row = Znth (tcb_y_of_prio priority) rows 0) by (eapply uchar_load_deterministic; eassumption); subst row.
  eapply mutex_del_priority_row_store; [exact Hyr| |exact Hgroup_owned|exact Hrow].
  exact (bitmap_lor_in_range 8 _ _ ltac:(lia) (proj1 Hactual_row) (proj1 Hactual_bitx)).
Qed.

Lemma mutex_del_rdy_at_priority_resources : forall sg pointer image table rows group current current_prio
  old_y old_bitx old_bity priority before after (frame : Assertion),
  0 <= priority < 64 -> 0 <= pointer < 4294967296 -> 0 <= old_y < 8 ->
  image TCBY = Some old_y -> image TCBBitX = Some old_bitx -> image TCBBitY = Some old_bity ->
  (mutex_del_priority_heap sg pointer image table rows group current current_prio ** frame) before ->
  mutex_del_rdy_at_priority_execution sg pointer priority before after ->
  (mutex_del_priority_heap sg pointer (mutex_priority_image image priority)
    (replace_Znth priority pointer table) (mutex_priority_rows rows old_y old_bitx priority)
    (mutex_priority_group rows group old_y old_bitx old_bity priority) current
    (mutex_priority_current pointer current current_prio priority) ** frame) after.
Proof.
  intros sg pointer image table rows group current current_prio old_y old_bitx old_bity priority before after frame
    Hp Hpointer Hy Hiy Hibx Hiby Hpre (ready & removed & assigned & inserted & Hremove & Hassign & Hinsert & Htable).
  destruct (mutex_del_priority_remove_resources sg pointer image table rows group current current_prio
    old_y old_bitx old_bity ready before removed frame Hy Hiy Hibx Hiby Hpre Hremove) as [Hready Hremoved].
  pose proof (mutex_del_priority_assign_resources sg pointer image table _ _ current current_prio
    priority removed assigned frame Hp Hremoved Hassign) as Hassigned.
  pose proof (mutex_del_priority_insert_resources sg pointer image table _ _ current _
    priority ready assigned inserted frame Hp Hassigned Hinsert) as Hinserted.
  pose proof (mutex_del_priority_table_store sg pointer _ table _ _ current _ priority inserted after frame
    Hp Hpointer Hinserted Htable) as Hfinal.
  rewrite Hready in Hfinal.
  unfold mutex_priority_rows, mutex_priority_group, mutex_priority_removed_group, ready_group_after_relocation in *.
  destruct (mutex_priority_was_ready rows old_y old_bitx) eqn:Hr; [exact Hfinal|].
  unfold mutex_priority_removed_rows in Hfinal; rewrite Hr in Hfinal; exact Hfinal.
Qed.

(** A total name for the already-defined owner-priority transformer at the
    acquired lookup.  The following source theorem derives the live lookup,
    owner and node from the actual pointer read; none is a caller premise. *)
Definition mutex_del_owner_adjusted_state (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (eid : EventID) (priority : Z) : UCOS2_Verify_State :=
  match state.(EventState).(inUsedEventStates) eid with
  | Some event =>
      match event.(mutexFields) with
      | Some mutex =>
          match mutex.(mfOwner) with
          | Some owner =>
              match state.(TskState).(inUsedTaskStates) owner with
              | Some node => mutex_del_owner_priority_state sg state mutex.(mfPCP) owner node priority
              | None => state
              end
          | None => state
          end
      | None => state
      end
  | None => state
  end.

Lemma mutex_del_owned_ceiling_adjust_resources : forall sg eid state event mutex pointer old_priority priority
  before released after (frame : Assertion),
  mutex_del_parent_layout sg -> mutex_del_parent_entry sg eid state event mutex ->
  mutex.(mfPCP) <> 255 -> pointer <> 0 -> old_priority <> priority ->
  (kernel_program_inv sg state ** frame) before ->
  pointer_load (event_pool_addr sg eid + OSEventPtr_off) pointer before ->
  kernel_heap_execution
    (pointer_store_writes (sg.(g_OSTCBPrioTbl) + mutex.(mfPCP) * sizeof(PTR)) 0) before released ->
  mutex_del_effective_priority_reads sg pointer released 0 priority ->
  uchar_load (tcb_field_address pointer TCBPrio) old_priority released ->
  mutex_del_rdy_at_priority_execution sg pointer priority released after ->
  (mutex_del_parent_prepared sg eid state (mutex_del_owner_adjusted_state sg state eid priority) event mutex **
    unmap_table_rep sg ** frame) after.
Proof.
  intros sg eid state event mutex pointer old_priority priority before released after frame
    Hlayout Hparent Hpcp Hnonzero Hdifferent Hpre Hread Hstore Hreads Hcompare Hrdy.
  pose proof Hparent as [Hvalid [Hlookup [Htype [Hfields Huse]]]].
  pose proof Hvalid as [Hprofile [Htasks [_ [_ [Hcross _]]]]].
  pose proof (mutex_del_program_pointer_load sg state eid event before frame Hlookup Hpre) as Hactual.
  assert (Hptr : encode_event_ptr_value sg event = pointer)
    by (eapply pointer_load_deterministic; eassumption).
  assert (Howner_pointer : exists owner, mutex.(mfOwner) = Some owner /\ pointer = task_slot_addr sg owner).
  { unfold encode_event_ptr_value in Hptr; rewrite Htype, Hfields in Hptr.
    destruct mutex.(mfOwner) as [owner|] eqn:Howner; cbn [encode_task_link] in Hptr;
      [exists owner; split; congruence|congruence]. }
  destruct Howner_pointer as [owner [Howner ->]].
  destruct Hcross as [_ [Hsnap _]].
  destruct (Hsnap eid event mutex owner Hlookup Htype Hfields Howner)
    as [node [base [snapshot [Hnode Hrest]]]].
  assert (Hceiling : mutex_del_parent_ceiling_at sg eid state mutex.(mfPCP)).
  { exists event, mutex; split; [exact Hparent|].
    symmetry; exact (proj2 (proj2 (mutex_del_parent_count_decode sg eid state event mutex Hparent))). }
  pose proof (mutex_del_parent_enabled_ceiling_in_range sg eid state mutex.(mfPCP) Hceiling Hpcp) as Hrange.
  assert (Hforget : kernel_program_inv sg state ** frame |-- kernel_program_rep sg state ** frame)
    by (unfold kernel_program_inv; entailer!).
  pose proof (mutex_del_ceiling_store_resources sg state mutex.(mfPCP) before released frame Hrange
    (Hforget before Hpre) Hstore) as Hreleased.
  assert (Hfocus : mutex_del_released_resources sg state mutex.(mfPCP) ** unmap_table_rep sg ** frame |--
    mutex_del_priority_input sg state mutex.(mfPCP) owner node **
      mutex_del_priority_frame sg state owner ** unmap_table_rep sg ** frame).
  { sep_apply_l_atomic (mutex_del_released_resources_split_priority sg state mutex.(mfPCP) owner node Hprofile Hnode).
    entailer!. }
  pose proof (Hfocus released Hreleased) as Hfocused.
  assert (Hscan_order : mutex_del_priority_input sg state mutex.(mfPCP) owner node **
      mutex_del_priority_frame sg state owner ** unmap_table_rep sg ** frame |--
    tcb64_storage_rep (task_slot_addr sg owner) (task_tcb64_image sg node) **
      PtrArray.full sg.(g_OSTCBPrioTbl) 64 (mutex_del_priority_values sg (mutex_del_released_table state mutex.(mfPCP))) ** TT).
  { unfold mutex_del_priority_input; entailer!; intros ? ?; exact I. }
  pose proof (mutex_del_effective_priority_reads_result sg (task_slot_addr sg owner)
    (task_tcb64_image sg node) (mutex_del_priority_values sg (mutex_del_released_table state mutex.(mfPCP)))
    node.(curPrio) released (TT) priority eq_refl (Hscan_order released Hfocused) Hreads) as Hscan.
  assert (Hfield_order : mutex_del_priority_input sg state mutex.(mfPCP) owner node **
      mutex_del_priority_frame sg state owner ** unmap_table_rep sg ** frame |--
    tcb64_storage_rep (task_slot_addr sg owner) (task_tcb64_image sg node) ** TT).
  { unfold mutex_del_priority_input; entailer!; intros ? ?; exact I. }
  assert (Hnotreserved : task_slot_addr sg owner <> 1).
  { assert (Haddresses : forall address, tcb_field_address address TCBStkPtr = address)
      by (unfold mutex_del_parent_layout in Hlayout; tauto).
    destruct (Hfield_order released Hfocused) as [owned [rest [Hjoin [Howned Hrest_owned]]]].
    exact (proj1 (mutex_del_parent_storage_pointer_not_reserved
      (task_slot_addr sg owner) (task_tcb64_image sg node) node.(tcbStkPtr)
      (Haddresses _) eq_refl owned Howned)). }
  pose proof (mutex_del_priority_field_load (task_slot_addr sg owner) (task_tcb64_image sg node)
    node.(curPrio) released (TT) eq_refl (Hfield_order released Hfocused)) as Hactual_priority.
  assert (Hold : node.(curPrio) = old_priority) by (eapply uchar_load_deterministic; eassumption).
  assert (Henabled : mutex_pcp_enabled sg mutex).
  { assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255)
      by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
    unfold mutex_pcp_enabled; congruence. }
  destruct (mutex_del_owner_scan_properties sg state eid event mutex owner priority
    Hvalid Hlookup Htype Hfields Howner Henabled Hnotreserved ltac:(intros other Hother;
      rewrite Hnode in Hother; injection Hother as E; subst other; exact Hscan))
    as [other [other_base [Hother [Hbase [Heffective Hproperties]]]]].
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  assert (Hpriority : 0 <= priority < 64).
  { pose proof (proj1 (proj1 Heffective)) as Hbound; unfold task_priority_in_range in Hbound; lia. }
  assert (Hold_range : task_priority_in_range sg node.(curPrio)).
  { unfold task_in_range in Htasks; intuition eauto. }
  assert (Hy : 0 <= tcb_y_of_prio node.(curPrio) < 8).
  { unfold tcb_y_of_prio, task_priority_in_range in *.
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  assert (Hheap_order : mutex_del_priority_input sg state mutex.(mfPCP) owner node **
      mutex_del_priority_frame sg state owner ** unmap_table_rep sg ** frame |--
    mutex_del_priority_input sg state mutex.(mfPCP) owner node **
      (mutex_del_priority_frame sg state owner ** unmap_table_rep sg ** frame)) by entailer!.
  pose proof (mutex_del_rdy_at_priority_resources sg (task_slot_addr sg owner) (task_tcb64_image sg node)
    (mutex_del_priority_values sg (mutex_del_released_table state mutex.(mfPCP)))
    (sched_row_values state.(TskState) state.(SchedState).(readyList))
    (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
    (encode_task_link sg state.(SchedState).(curTaskID)) (sched_priority_byte state.(SchedState).(curSchedPrio))
    (tcb_y_of_prio node.(curPrio)) (tcb_bit_x_of_prio node.(curPrio)) (tcb_bit_y_of_prio node.(curPrio))
    priority released after (mutex_del_priority_frame sg state owner ** unmap_table_rep sg ** frame)
    Hpriority (proj1 Hread) Hy eq_refl eq_refl eq_refl (Hheap_order released Hfocused) Hrdy) as Hadjusted.
  change ((mutex_del_priority_output sg state mutex.(mfPCP) owner node priority **
    (mutex_del_priority_frame sg state owner ** unmap_table_rep sg ** frame)) after) in Hadjusted.
  pose proof (mutex_del_program_prepare_owner sg state eid event mutex owner node priority
    Hparent Howner Henabled Hnode Hnotreserved Hscan) as Hmerge.
  destruct (Z.eq_dec node.(curPrio) priority); [congruence|].
  unfold mutex_del_owner_adjusted_state; unfold mutex_query_lookup in Hlookup.
  rewrite Hlookup, Hfields, Howner, Hnode.
  assert (Hclose : mutex_del_priority_output sg state mutex.(mfPCP) owner node priority **
      (mutex_del_priority_frame sg state owner ** unmap_table_rep sg ** frame) |--
    mutex_del_parent_prepared sg eid state
      (mutex_del_owner_priority_state sg state mutex.(mfPCP) owner node priority) event mutex **
      unmap_table_rep sg ** frame).
  { sep_apply_l_atomic Hmerge; entailer!. }
  exact (Hclose after Hadjusted).
Qed.

Section NoPendRecycleSource.
Context (environment : MutexDelCallEnvironment) (critical : CriticalRegionResources)
  (arch : A32InterruptContext) (sg : StableGlobVars) (Local : Type).
Variable save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
  environment.(mutex_del_call_platform) critical arch.
Variable restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
  environment.(mutex_del_call_platform) critical arch.
Variable registers_source : Armv7aIRQRegisterSave environment.(mutex_del_call_external)
  environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
  environment.(mutex_del_call_continuations).
Variable local_step : OsIntExitCallContext ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable normal_return : OsIntExitCallContext -> StableGlobVars ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable handler_contract : forall handler,
  RestoreHandlerContract
    (fun (_ : RestoreHandlerCall) (_ : Local) =>
      mutex_del_restore_handler_owner environment.(mutex_del_call_platform)
        environment.(mutex_del_call_port) handler)
    (local_step handler) (normal_return handler).
Variable handler_stack : TaskStackRegion.
Variable handler_fragments : TaskStackFragments.

(** One actual branch of OSMutexDel with opt=OS_DEL_NO_PEND. The branch
    guards are physical reads, not additional public-entry requirements.
    The ghost recycle endpoint is validated against the four stores below;
    it is not a premise asserting a completed abstract Del operation. *)
Definition mutex_del_no_pend_recycle_execution
  restore_entry call state mask registers pe eid observed perr cpu_sr saved_word
  before entered acquired returned final after : Prop :=
  let checkpoint := mutex_del_recycle_state sg eid observed acquired in
  exists initialized prefix_heap returned_registers resumed final_registers final_state
    saved_heap body_heap recycled middle restored returned_heap cursor written final_cursor count,
    kernel_heap_execution (pointer_store_writes cpu_sr 0) before initialized /\
    mutex_del_call_prefix_execution sg pe perr initialized None prefix_heap /\
    registers.(kernel_save_return_word) = None /\
    valid_os_cpu_sr registers.(kernel_save_cpsr) /\
    armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask /\
    mutex_del_irq_registers_execution environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
      environment.(mutex_del_call_continuations) registers_source sg Local local_step normal_return
      handler_stack handler_fragments (armv7a_save_entry_address save + 4)
      (kernel_save_read_cpsr registers) call state prefix_heap returned_registers entered acquired resumed /\
    armv7a_save_suffix_transition save returned_registers acquired resumed
      final_registers final_state saved_heap /\
    saved_word = final_registers.(kernel_save_r0) /\
    kernel_heap_execution (pointer_store_writes cpu_sr saved_word) saved_heap body_heap /\
    uchar_load (pe + OSEventType_off) 4 body_heap /\
    uchar_load (pe + OSEventGrp_off) 0 body_heap /\
    mutex_del_count_load (pe + OSEventCnt_off) count body_heap /\
    unsigned_last_nbits (Z.shiftr count 8) 8 = 255 /\
    mutex_del_recycle_stores sg pe body_heap recycled /\
    cursor.(kernel_restore_r0) = saved_word /\
    armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 /\
    armv7a_restore_prefix_transition restore cursor recycled written middle /\
    mutex_del_restore_irqs_execution environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
      environment.(mutex_del_call_continuations) sg Local local_step normal_return
      handler_stack handler_fragments (armv7a_irq_fiq_mask saved_word)
      (restore_entry + 8) cursor.(kernel_restore_lr) entered checkpoint middle returned final restored /\
    armv7a_restore_suffix_transition restore written restored final_cursor returned_heap /\
    kernel_heap_execution [(perr, 0)] returned_heap after.

Lemma mutex_del_runtime_no_pend_recycle_source_post : forall restore_entry call state mask registers
  pe eid observed perr old_error cpu_sr saved_word before entered acquired returned final after (frame : Assertion),
  mutex_del_parent_input sg pe state eid observed ->
  (mutex_del_runtime_entry environment environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) sg call mask state **
    (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
    task_stack_fragments_rep handler_stack handler_fragments ** frame) before ->
  mutex_del_no_pend_recycle_execution restore_entry call state mask registers pe eid observed perr cpu_sr
    saved_word before entered acquired returned final after ->
  saved_word = registers.(kernel_save_cpsr) /\
  mutex_del_parent_critical_observation sg eid 0 0 0 0 acquired
    (mutex_del_recycle_state sg eid observed acquired) /\
  (mutex_del_runtime_post environment environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) sg call mask state pe 0 eid 0 0 **
    (perr # UChar |-> 0) ** (cpu_sr # UInt |-> saved_word) **
    task_stack_fragments_rep handler_stack handler_fragments ** frame) after.
Proof.
  intros restore_entry call state mask registers pe eid observed perr old_error cpu_sr saved_word
    before entered acquired returned final after frame Hdomain Hentry Hsource.
  set (abi := environment.(mutex_del_call_continuations)) in *.
  set (active := task_stack_call_active_key call).
  assert (Hopen : mutex_del_runtime_entry environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask state |--
    kernel_stack_call_closed abi mutex_del_stack_resources sg active call mask state).
  { unfold mutex_del_runtime_entry; Intros same_environment.
    destruct H as [Henv ->]; reflexivity. }
  assert (Hpre : (kernel_stack_call_closed abi mutex_del_stack_resources sg active call mask state **
      (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
      task_stack_fragments_rep handler_stack handler_fragments ** frame) before).
  { match type of Hentry with ?P before => match goal with |- ?Q before => assert (Horder : P |-- Q) end end.
    { sep_apply_l_atomic Hopen; entailer!. } exact (Horder before Hentry). }
  destruct Hsource as (initialized & prefix_heap & returned_registers & resumed & final_registers & final_state &
    saved_heap & body_heap & recycled & middle & restored & returned_heap & cursor & written & final_cursor & count &
    Hinit & Hprefix & Hnone & Hvalid & Hmask & Hsave_irqs & Hsave_suffix & Hsaved & Hstore &
    Htype_read & Hgroup_read & Hcount_read & Hpcp & Hstores & Hr0 & Hmasked & Hrestore_prefix &
    Hrestore_irqs & Hrestore_suffix & Herror).
  subst saved_word.
  set (entry_residual := mutex_del_stack_critical_frame abi sg active state **
    task_stack_fragments_rep handler_stack handler_fragments ** frame).
  assert (Hinitialize_order : kernel_stack_call_closed abi mutex_del_stack_resources sg active call mask state **
      (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
      task_stack_fragments_rep handler_stack handler_fragments ** frame |--
    (cpu_sr # UInt |->_) **
      (kernel_program_inv sg state ** (perr # UChar |-> old_error) **
       (kernel_call_execution_owned environment.(mutex_del_call_external)
          environment.(mutex_del_call_platform) call mask ** entry_residual))).
  { unfold kernel_stack_call_closed, entry_residual.
    rewrite mutex_del_stack_world_split_critical_frame; entailer!. }
  destruct (task_stack_uint_store_execution cpu_sr 0 _ before ltac:(lia)
    (Hinitialize_order before Hpre)) as [produced [Hinitialize Hinitialized]].
  assert (produced = initialized) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hprefix_order : (cpu_sr # UInt |-> 0) **
      (kernel_program_inv sg state ** (perr # UChar |-> old_error) **
       (kernel_call_execution_owned environment.(mutex_del_call_external)
          environment.(mutex_del_call_platform) call mask ** entry_residual)) |--
    kernel_program_inv sg state ** (perr # UChar |-> old_error) **
      (kernel_call_execution_owned environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) call mask ** (cpu_sr # UInt |->_) ** entry_residual)).
  { sep_apply_l_atomic (store_uint_undef_store_uint cpu_sr 0); entailer!. }
  destruct (mutex_del_call_prefix_resources sg state pe eid observed perr old_error initialized None prefix_heap _
    Hdomain (Hprefix_order initialized Hinitialized) Hprefix)
    as [[Hnonnull [Hentry_type Hnest]] Hprefix_owned].
  assert (Hprefix_ok : mutex_del_parent_prefix_ok pe state eid).
  { unfold mutex_del_parent_prefix_ok; apply mutex_del_before_save_continues_iff;
    [rewrite Hnest; lia|auto]. }
  assert (Hsave_order : kernel_program_inv sg state ** (perr # UChar |-> old_error) **
      (kernel_call_execution_owned environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) call mask ** (cpu_sr # UInt |->_) ** entry_residual) |--
    kernel_stack_call_closed abi mutex_del_stack_resources sg active call
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state **
      (task_stack_fragments_rep handler_stack handler_fragments **
       ((cpu_sr # UInt |->_) ** (perr # UChar |-> old_error) ** frame))).
  { unfold kernel_stack_call_closed, entry_residual; rewrite Hmask.
    rewrite mutex_del_stack_world_split_critical_frame; entailer!. }
  destruct (mutex_del_stack_irq_save_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi registers_source sg Local
    local_step normal_return handler_contract handler_stack handler_fragments critical arch save active call state
    registers prefix_heap returned_registers entered acquired resumed final_registers final_state saved_heap _
    Hnone Hvalid (Hsave_order prefix_heap Hprefix_owned) Hsave_irqs Hsave_suffix)
    as [Hmrs [Hsuffix_source [Hstate [Hsaved_value [Hfinal_cpsr [Hreturn [Hsame_entered [Hevents Hsaved_heap]]]]]]]].
  destruct (mutex_del_irq_registers_execution_refinement environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi registers_source sg Local
    local_step normal_return handler_stack handler_fragments _ _ _ _ _ _ _ _ _ Hsave_irqs)
    as [_ [_ [_ Hcounter]]].
  pose proof (mutex_del_counter_irqs_owner_history environment sg Local local_step normal_return
    handler_stack handler_fragments _ _ _ _ _ _ _ _ _ Hcounter) as Hhistory.
  assert (Hstore_order : kernel_stack_call_masked abi mutex_del_stack_resources critical sg active entered
      final_registers.(kernel_save_r0) acquired acquired **
      (task_stack_fragments_rep handler_stack handler_fragments **
       ((cpu_sr # UInt |->_) ** (perr # UChar |-> old_error) ** frame)) |--
    (cpu_sr # UInt |->_) **
      (kernel_stack_call_masked abi mutex_del_stack_resources critical sg active entered
         final_registers.(kernel_save_r0) acquired acquired ** (perr # UChar |-> old_error) **
       task_stack_fragments_rep handler_stack handler_fragments ** frame)) by entailer!.
  destruct (task_stack_uint_store_execution cpu_sr final_registers.(kernel_save_r0) _ saved_heap
    ltac:(rewrite Hsaved_value; exact Hvalid) (Hstore_order saved_heap Hsaved_heap))
    as [produced [Hwrite Hbody_owned]].
  assert (produced = body_heap) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  set (body_frame := critical_region_masked environment.(mutex_del_call_platform) critical sg
      entered.(os_sched_call_invocation) entered.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
    os_sched_context_resources environment.(mutex_del_call_external) entered **
    mutex_del_stack_critical_frame abi sg active acquired **
    task_stack_fragments_rep handler_stack handler_fragments **
    (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** (perr # UChar |-> old_error) ** frame).
  assert (Hbody_order : (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
      (kernel_stack_call_masked abi mutex_del_stack_resources critical sg active entered
         final_registers.(kernel_save_r0) acquired acquired ** (perr # UChar |-> old_error) **
       task_stack_fragments_rep handler_stack handler_fragments ** frame) |--
    coq_prop (UCOS2_state_inv sg acquired /\ mutex_program_selected_reachable sg acquired) &&
      (kernel_program_inv sg acquired ** body_frame)).
  { unfold kernel_stack_call_masked, body_frame.
    rewrite mutex_del_stack_world_split_critical_frame.
    unfold kernel_program_inv, mutex_del_stack_critical_frame; entailer!. }
  destruct (Hbody_order body_heap Hbody_owned) as [[Hacquired_valid Hreach] Hbody].
  destruct Hdomain as [Hzero|[_ [Haddress [Hid Hslot]]]]; [contradiction|].
  assert (Hacquired_slot : sem_query_public_slot acquired eid observed).
  { unfold sem_query_public_slot, mutex_query_lookup in *; rewrite Hevents; exact Hslot. }
  pose proof (mutex_del_call_program_type_load sg acquired pe eid observed body_heap _ Haddress Hacquired_slot Hbody)
    as Hactual_type.
  assert (Htype : event_slot_type_value acquired.(EventState) eid = 4)
    by (eapply uchar_load_deterministic; eassumption).
  destruct (mutex_del_parent_recheck_live_fields sg acquired eid observed Hacquired_valid Hacquired_slot Htype)
    as [mutex [Hlookup [Hkind Hfields]]].
  assert (Howner_use : mutex_owner_event_unlinked acquired.(TskState) acquired.(EventState)).
  { eapply mutex_program_reachable_owner_use; [|exact Hreach].
    intros; eapply mutex_program_selected_initial_empty; eassumption. }
  assert (Hparent : mutex_del_parent_entry sg eid acquired observed mutex)
    by (exact (conj Hacquired_valid (conj Hlookup (conj Hkind (conj Hfields Howner_use))))).
  pose proof (mutex_del_call_program_group_load sg acquired pe eid observed body_heap _ Haddress Hlookup Hbody)
    as Hactual_group.
  assert (Hempty : encode_event_wait_grp observed.(waitList) acquired.(TskState) = 0)
    by (eapply uchar_load_deterministic; eassumption).
  pose proof (mutex_del_program_count_load sg acquired pe eid observed body_heap _ Haddress Hlookup Hbody)
    as Hactual_count.
  assert (Hcount : count = encode_event_cnt_value observed)
    by (eapply mutex_del_count_load_deterministic; eassumption).
  rewrite Hcount, (mutex_del_parent_cast_count sg eid acquired observed mutex Hparent) in Hpcp.
  pose proof (proj2 (proj2 (mutex_del_parent_count_decode sg eid acquired observed mutex Hparent))) as Hdecode.
  rewrite Hdecode in Hpcp.
  assert (Hdisabled : mutex.(mfPCP) = sg.(osPrioMutexCeilDis)).
  { assert (Hprofile : sg.(osPrioMutexCeilDis) = 255).
    { destruct Hacquired_valid as [Hprofile _].
      unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto. }
    congruence. }
  assert (Hphase : mutex_del_wake_state_inv sg eid mutex acquired).
  { eapply mutex_del_disabled_state_implies_wake_state; eassumption. }
  set (checkpoint := mutex_del_recycle_state sg eid observed acquired) in *.
  assert (Hcritical : mutex_del_critical sg eid 0 acquired (0, (OS_ERR_NONE, false)) checkpoint).
  { exists observed, mutex; split; [exact Hlookup|]. split; [exact Hkind|]. split; [exact Hfields|].
    destruct (Z.eq_dec 0 0); [|contradiction].
    destruct (Z.eq_dec (encode_event_wait_grp observed.(waitList) acquired.(TskState)) 0); [|contradiction].
    exists acquired; split.
    - unfold mutex_del_prepare; destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis));
        [reflexivity|contradiction].
    - split; reflexivity. }
  assert (Hobservation : mutex_del_parent_critical_observation sg eid 0 0 0 0 acquired checkpoint).
  { exists OS_ERR_NONE, false; split; [exact Hcritical|split; reflexivity]. }
  assert (Hforget : kernel_program_inv sg acquired ** body_frame |-- kernel_program_rep sg acquired ** body_frame).
  { unfold kernel_program_inv; entailer!. }
  rewrite Haddress in Hstores.
  pose proof (mutex_del_recycle_stores_resources sg eid mutex acquired observed body_heap recycled body_frame
    Hphase Hlookup Hempty (Hforget body_heap Hbody) Hstores) as Hrecycled.
  fold checkpoint in Hrecycled.
  assert (Hcheckpoint : mutex_del_stack_checkpoint sg acquired checkpoint).
  { right; exists eid, 0, (0, (OS_ERR_NONE, false)); exact Hcritical. }
  assert (Hrestore_order : kernel_program_inv sg checkpoint ** body_frame |--
    mutex_del_stack_restore_input abi critical sg active entered final_registers.(kernel_save_r0) acquired checkpoint **
      (task_stack_fragments_rep handler_stack handler_fragments **
       ((cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** (perr # UChar |-> old_error) ** frame))).
  { unfold body_frame, mutex_del_stack_restore_input; entailer!. }
  destruct (mutex_del_stack_repeated_restore_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi sg Local local_step normal_return
    handler_contract handler_stack handler_fragments critical arch restore active entered
    final_registers.(kernel_save_r0) acquired checkpoint restore_entry cursor recycled written middle
    returned final restored final_cursor returned_heap _ Hr0 Hmasked (Hrestore_order recycled Hrecycled)
    Hrestore_prefix Hrestore_irqs Hrestore_suffix) as [Hi [Ho [Hs [Hrestore_return Hreturned]]]].
  rewrite Hsaved_value, Hmask in Hreturned.
  assert (Hsame : kernel_stack_call_same_call returned call).
  { destruct Hsame_entered as [Hi' [Ho' Hs']]; unfold kernel_stack_call_same_call; repeat split; congruence. }
  assert (Hreturned_order : kernel_stack_call_closed abi mutex_del_stack_resources sg active returned mask final **
      (task_stack_fragments_rep handler_stack handler_fragments **
        ((cpu_sr # UInt |-> registers.(kernel_save_cpsr)) ** (perr # UChar |-> old_error) ** frame)) |--
    (perr # UChar |-> old_error) **
      (kernel_stack_call_closed abi mutex_del_stack_resources sg active returned mask final **
       (cpu_sr # UInt |-> registers.(kernel_save_cpsr)) **
       task_stack_fragments_rep handler_stack handler_fragments ** frame)) by entailer!.
  destruct (kernel_heap_framed_uchar_store perr old_error 0 _ returned_heap ltac:(lia)
    (Hreturned_order returned_heap Hreturned)) as [finished [Hwrite_error Hfinished]].
  assert (finished = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst finished.
  assert (Hpublic : kernel_stack_call_closed abi mutex_del_stack_resources sg active returned mask final |--
    mutex_del_runtime_post environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask state pe 0 eid 0 0).
  { unfold mutex_del_runtime_post; Left; Right; Exists acquired checkpoint 0.
    apply _derivable1_andp_intros; [entailer!|].
    unfold mutex_del_runtime_return, mutex_del_runtime_return_at; Exists returned final environment.
    unfold mutex_del_callsite_environment; entailer!. }
  split; [exact Hsaved_value|]. split; [exact Hobservation|].
  match type of Hfinished with ?P after => match goal with |- ?Q after => assert (Hfinish : P |-- Q) end end.
  { rewrite Hsaved_value; sep_apply_l_atomic Hpublic; entailer!. }
  exact (Hfinish after Hfinished).
Qed.

(** The enabled-PCP/no-owner branch adds the source's physical owner read
    and priority-table store before exactly the same four recycle stores.
    The observed count binds [ceiling]; neither its range nor owner absence
    is supplied as a public-entry premise. *)
Definition mutex_del_no_pend_unowned_recycle_execution
  restore_entry call state mask registers pe eid observed ceiling perr cpu_sr saved_word
  before entered acquired returned final after : Prop :=
  let checkpoint := mutex_del_recycle_state sg eid observed (mutex_del_released_state acquired ceiling) in
  exists initialized prefix_heap returned_registers resumed final_registers final_state
    saved_heap body_heap released_heap recycled middle restored returned_heap cursor written final_cursor count,
    kernel_heap_execution (pointer_store_writes cpu_sr 0) before initialized /\
    mutex_del_call_prefix_execution sg pe perr initialized None prefix_heap /\
    registers.(kernel_save_return_word) = None /\
    valid_os_cpu_sr registers.(kernel_save_cpsr) /\
    armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask /\
    mutex_del_irq_registers_execution environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
      environment.(mutex_del_call_continuations) registers_source sg Local local_step normal_return
      handler_stack handler_fragments (armv7a_save_entry_address save + 4)
      (kernel_save_read_cpsr registers) call state prefix_heap returned_registers entered acquired resumed /\
    armv7a_save_suffix_transition save returned_registers acquired resumed
      final_registers final_state saved_heap /\
    saved_word = final_registers.(kernel_save_r0) /\
    kernel_heap_execution (pointer_store_writes cpu_sr saved_word) saved_heap body_heap /\
    uchar_load (pe + OSEventType_off) 4 body_heap /\
    uchar_load (pe + OSEventGrp_off) 0 body_heap /\
    mutex_del_count_load (pe + OSEventCnt_off) count body_heap /\
    unsigned_last_nbits (Z.shiftr count 8) 8 = ceiling /\
    ceiling <> 255 /\
    pointer_load (pe + OSEventPtr_off) 0 body_heap /\
    kernel_heap_execution
      (pointer_store_writes (sg.(g_OSTCBPrioTbl) + ceiling * sizeof(PTR)) 0) body_heap released_heap /\
    mutex_del_recycle_stores sg pe released_heap recycled /\
    cursor.(kernel_restore_r0) = saved_word /\
    armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 /\
    armv7a_restore_prefix_transition restore cursor recycled written middle /\
    mutex_del_restore_irqs_execution environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
      environment.(mutex_del_call_continuations) sg Local local_step normal_return
      handler_stack handler_fragments (armv7a_irq_fiq_mask saved_word)
      (restore_entry + 8) cursor.(kernel_restore_lr) entered checkpoint middle returned final restored /\
    armv7a_restore_suffix_transition restore written restored final_cursor returned_heap /\
    kernel_heap_execution [(perr, 0)] returned_heap after.

Lemma mutex_del_runtime_no_pend_unowned_recycle_source_post : forall restore_entry call state mask registers
  pe eid observed ceiling perr old_error cpu_sr saved_word before entered acquired returned final after (frame : Assertion),
  mutex_del_parent_input sg pe state eid observed ->
  (mutex_del_runtime_entry environment environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) sg call mask state **
    (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
    task_stack_fragments_rep handler_stack handler_fragments ** frame) before ->
  mutex_del_no_pend_unowned_recycle_execution restore_entry call state mask registers pe eid observed ceiling perr cpu_sr
    saved_word before entered acquired returned final after ->
  saved_word = registers.(kernel_save_cpsr) /\
  mutex_del_parent_critical_observation sg eid 0 0 0 0 acquired
    (mutex_del_recycle_state sg eid observed (mutex_del_released_state acquired ceiling)) /\
  (mutex_del_runtime_post environment environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) sg call mask state pe 0 eid 0 0 **
    (perr # UChar |-> 0) ** (cpu_sr # UInt |-> saved_word) **
    task_stack_fragments_rep handler_stack handler_fragments ** frame) after.
Proof.
  intros restore_entry call state mask registers pe eid observed ceiling perr old_error cpu_sr saved_word
    before entered acquired returned final after frame Hdomain Hentry Hsource.
  set (abi := environment.(mutex_del_call_continuations)) in *.
  set (active := task_stack_call_active_key call).
  assert (Hopen : mutex_del_runtime_entry environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask state |--
    kernel_stack_call_closed abi mutex_del_stack_resources sg active call mask state).
  { unfold mutex_del_runtime_entry; Intros same_environment.
    destruct H as [Henv ->]; reflexivity. }
  assert (Hpre : (kernel_stack_call_closed abi mutex_del_stack_resources sg active call mask state **
      (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
      task_stack_fragments_rep handler_stack handler_fragments ** frame) before).
  { match type of Hentry with ?P before => match goal with |- ?Q before => assert (Horder : P |-- Q) end end.
    { sep_apply_l_atomic Hopen; entailer!. } exact (Horder before Hentry). }
  destruct Hsource as (initialized & prefix_heap & returned_registers & resumed & final_registers & final_state &
    saved_heap & body_heap & released_heap & recycled & middle & restored & returned_heap & cursor & written & final_cursor & count &
    Hinit & Hprefix & Hnone & Hvalid & Hmask & Hsave_irqs & Hsave_suffix & Hsaved & Hstore &
    Htype_read & Hgroup_read & Hcount_read & Hceiling & Hpcp & Hptr_read & Hrelease & Hstores & Hr0 & Hmasked & Hrestore_prefix &
    Hrestore_irqs & Hrestore_suffix & Herror).
  subst saved_word.
  set (entry_residual := mutex_del_stack_critical_frame abi sg active state **
    task_stack_fragments_rep handler_stack handler_fragments ** frame).
  assert (Hinitialize_order : kernel_stack_call_closed abi mutex_del_stack_resources sg active call mask state **
      (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
      task_stack_fragments_rep handler_stack handler_fragments ** frame |--
    (cpu_sr # UInt |->_) **
      (kernel_program_inv sg state ** (perr # UChar |-> old_error) **
       (kernel_call_execution_owned environment.(mutex_del_call_external)
          environment.(mutex_del_call_platform) call mask ** entry_residual))).
  { unfold kernel_stack_call_closed, entry_residual.
    rewrite mutex_del_stack_world_split_critical_frame; entailer!. }
  destruct (task_stack_uint_store_execution cpu_sr 0 _ before ltac:(lia)
    (Hinitialize_order before Hpre)) as [produced [Hinitialize Hinitialized]].
  assert (produced = initialized) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hprefix_order : (cpu_sr # UInt |-> 0) **
      (kernel_program_inv sg state ** (perr # UChar |-> old_error) **
       (kernel_call_execution_owned environment.(mutex_del_call_external)
          environment.(mutex_del_call_platform) call mask ** entry_residual)) |--
    kernel_program_inv sg state ** (perr # UChar |-> old_error) **
      (kernel_call_execution_owned environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) call mask ** (cpu_sr # UInt |->_) ** entry_residual)).
  { sep_apply_l_atomic (store_uint_undef_store_uint cpu_sr 0); entailer!. }
  destruct (mutex_del_call_prefix_resources sg state pe eid observed perr old_error initialized None prefix_heap _
    Hdomain (Hprefix_order initialized Hinitialized) Hprefix)
    as [[Hnonnull [Hentry_type Hnest]] Hprefix_owned].
  assert (Hprefix_ok : mutex_del_parent_prefix_ok pe state eid).
  { unfold mutex_del_parent_prefix_ok; apply mutex_del_before_save_continues_iff;
    [rewrite Hnest; lia|auto]. }
  assert (Hsave_order : kernel_program_inv sg state ** (perr # UChar |-> old_error) **
      (kernel_call_execution_owned environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) call mask ** (cpu_sr # UInt |->_) ** entry_residual) |--
    kernel_stack_call_closed abi mutex_del_stack_resources sg active call
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state **
      (task_stack_fragments_rep handler_stack handler_fragments **
       ((cpu_sr # UInt |->_) ** (perr # UChar |-> old_error) ** frame))).
  { unfold kernel_stack_call_closed, entry_residual; rewrite Hmask.
    rewrite mutex_del_stack_world_split_critical_frame; entailer!. }
  destruct (mutex_del_stack_irq_save_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi registers_source sg Local
    local_step normal_return handler_contract handler_stack handler_fragments critical arch save active call state
    registers prefix_heap returned_registers entered acquired resumed final_registers final_state saved_heap _
    Hnone Hvalid (Hsave_order prefix_heap Hprefix_owned) Hsave_irqs Hsave_suffix)
    as [Hmrs [Hsuffix_source [Hstate [Hsaved_value [Hfinal_cpsr [Hreturn [Hsame_entered [Hevents Hsaved_heap]]]]]]]].
  destruct (mutex_del_irq_registers_execution_refinement environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi registers_source sg Local
    local_step normal_return handler_stack handler_fragments _ _ _ _ _ _ _ _ _ Hsave_irqs)
    as [_ [_ [_ Hcounter]]].
  pose proof (mutex_del_counter_irqs_owner_history environment sg Local local_step normal_return
    handler_stack handler_fragments _ _ _ _ _ _ _ _ _ Hcounter) as Hhistory.
  assert (Hstore_order : kernel_stack_call_masked abi mutex_del_stack_resources critical sg active entered
      final_registers.(kernel_save_r0) acquired acquired **
      (task_stack_fragments_rep handler_stack handler_fragments **
       ((cpu_sr # UInt |->_) ** (perr # UChar |-> old_error) ** frame)) |--
    (cpu_sr # UInt |->_) **
      (kernel_stack_call_masked abi mutex_del_stack_resources critical sg active entered
         final_registers.(kernel_save_r0) acquired acquired ** (perr # UChar |-> old_error) **
       task_stack_fragments_rep handler_stack handler_fragments ** frame)) by entailer!.
  destruct (task_stack_uint_store_execution cpu_sr final_registers.(kernel_save_r0) _ saved_heap
    ltac:(rewrite Hsaved_value; exact Hvalid) (Hstore_order saved_heap Hsaved_heap))
    as [produced [Hwrite Hbody_owned]].
  assert (produced = body_heap) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  set (body_frame := critical_region_masked environment.(mutex_del_call_platform) critical sg
      entered.(os_sched_call_invocation) entered.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
    os_sched_context_resources environment.(mutex_del_call_external) entered **
    mutex_del_stack_critical_frame abi sg active acquired **
    task_stack_fragments_rep handler_stack handler_fragments **
    (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** (perr # UChar |-> old_error) ** frame).
  assert (Hbody_order : (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
      (kernel_stack_call_masked abi mutex_del_stack_resources critical sg active entered
         final_registers.(kernel_save_r0) acquired acquired ** (perr # UChar |-> old_error) **
       task_stack_fragments_rep handler_stack handler_fragments ** frame) |--
    coq_prop (UCOS2_state_inv sg acquired /\ mutex_program_selected_reachable sg acquired) &&
      (kernel_program_inv sg acquired ** body_frame)).
  { unfold kernel_stack_call_masked, body_frame.
    rewrite mutex_del_stack_world_split_critical_frame.
    unfold kernel_program_inv, mutex_del_stack_critical_frame; entailer!. }
  destruct (Hbody_order body_heap Hbody_owned) as [[Hacquired_valid Hreach] Hbody].
  destruct Hdomain as [Hzero|[_ [Haddress [Hid Hslot]]]]; [contradiction|].
  assert (Hacquired_slot : sem_query_public_slot acquired eid observed).
  { unfold sem_query_public_slot, mutex_query_lookup in *; rewrite Hevents; exact Hslot. }
  pose proof (mutex_del_call_program_type_load sg acquired pe eid observed body_heap _ Haddress Hacquired_slot Hbody)
    as Hactual_type.
  assert (Htype : event_slot_type_value acquired.(EventState) eid = 4)
    by (eapply uchar_load_deterministic; eassumption).
  destruct (mutex_del_parent_recheck_live_fields sg acquired eid observed Hacquired_valid Hacquired_slot Htype)
    as [mutex [Hlookup [Hkind Hfields]]].
  assert (Howner_use : mutex_owner_event_unlinked acquired.(TskState) acquired.(EventState)).
  { eapply mutex_program_reachable_owner_use; [|exact Hreach].
    intros; eapply mutex_program_selected_initial_empty; eassumption. }
  assert (Hparent : mutex_del_parent_entry sg eid acquired observed mutex)
    by (exact (conj Hacquired_valid (conj Hlookup (conj Hkind (conj Hfields Howner_use))))).
  pose proof (mutex_del_call_program_group_load sg acquired pe eid observed body_heap _ Haddress Hlookup Hbody)
    as Hactual_group.
  assert (Hempty : encode_event_wait_grp observed.(waitList) acquired.(TskState) = 0)
    by (eapply uchar_load_deterministic; eassumption).
  pose proof (mutex_del_program_count_load sg acquired pe eid observed body_heap _ Haddress Hlookup Hbody)
    as Hactual_count.
  assert (Hcount : count = encode_event_cnt_value observed)
    by (eapply mutex_del_count_load_deterministic; eassumption).
  rewrite Hcount, (mutex_del_parent_cast_count sg eid acquired observed mutex Hparent) in Hceiling.
  pose proof (proj2 (proj2 (mutex_del_parent_count_decode sg eid acquired observed mutex Hparent))) as Hdecode.
  rewrite Hdecode in Hceiling; subst ceiling.
  rewrite Haddress in Hptr_read.
  pose proof (mutex_del_unowned_ceiling_store_resources sg eid acquired observed mutex body_heap released_heap
    body_frame Hparent Hpcp Hbody Hptr_read Hrelease) as Hprepared.
  set (prepared := mutex_del_released_state acquired mutex.(mfPCP)) in *.
  assert (Hprepare_open :
    mutex_del_parent_prepared sg eid acquired prepared observed mutex ** unmap_table_rep sg ** body_frame |--
    coq_prop (mutex_del_prepare sg mutex acquired prepared /\
      mutex_del_wake_state_inv sg eid mutex prepared) &&
      (kernel_program_rep sg prepared ** body_frame)).
  { unfold mutex_del_parent_prepared, mutex_del_wake_rep, kernel_program_rep; entailer!. }
  destruct (Hprepare_open released_heap Hprepared) as [[Hprepare Hphase] Hreleased].
  set (checkpoint := mutex_del_recycle_state sg eid observed prepared) in *.
  assert (Hcritical : mutex_del_critical sg eid 0 acquired (0, (OS_ERR_NONE, false)) checkpoint).
  { exists observed, mutex; split; [exact Hlookup|]. split; [exact Hkind|]. split; [exact Hfields|].
    destruct (Z.eq_dec 0 0); [|contradiction].
    destruct (Z.eq_dec (encode_event_wait_grp observed.(waitList) acquired.(TskState)) 0); [|contradiction].
    exists prepared; split; [exact Hprepare|]. split; reflexivity. }
  assert (Hobservation : mutex_del_parent_critical_observation sg eid 0 0 0 0 acquired checkpoint).
  { exists OS_ERR_NONE, false; split; [exact Hcritical|split; reflexivity]. }
  assert (Hwaiters : observed.(waitList) = [])
    by (eapply mutex_del_event_group_zero_implies_empty; eassumption).
  assert (Hprepared_empty : encode_event_wait_grp observed.(waitList) prepared.(TskState) = 0)
    by (rewrite Hwaiters; reflexivity).
  rewrite Haddress in Hstores.
  pose proof (mutex_del_recycle_stores_resources sg eid mutex prepared observed released_heap recycled body_frame
    Hphase Hlookup Hprepared_empty Hreleased Hstores) as Hrecycled.
  fold checkpoint in Hrecycled.
  assert (Hcheckpoint : mutex_del_stack_checkpoint sg acquired checkpoint).
  { right; exists eid, 0, (0, (OS_ERR_NONE, false)); exact Hcritical. }
  assert (Hrestore_order : kernel_program_inv sg checkpoint ** body_frame |--
    mutex_del_stack_restore_input abi critical sg active entered final_registers.(kernel_save_r0) acquired checkpoint **
      (task_stack_fragments_rep handler_stack handler_fragments **
       ((cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** (perr # UChar |-> old_error) ** frame))).
  { unfold body_frame, mutex_del_stack_restore_input; entailer!. }
  destruct (mutex_del_stack_repeated_restore_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi sg Local local_step normal_return
    handler_contract handler_stack handler_fragments critical arch restore active entered
    final_registers.(kernel_save_r0) acquired checkpoint restore_entry cursor recycled written middle
    returned final restored final_cursor returned_heap _ Hr0 Hmasked (Hrestore_order recycled Hrecycled)
    Hrestore_prefix Hrestore_irqs Hrestore_suffix) as [Hi [Ho [Hs [Hrestore_return Hreturned]]]].
  rewrite Hsaved_value, Hmask in Hreturned.
  assert (Hsame : kernel_stack_call_same_call returned call).
  { destruct Hsame_entered as [Hi' [Ho' Hs']]; unfold kernel_stack_call_same_call; repeat split; congruence. }
  assert (Hreturned_order : kernel_stack_call_closed abi mutex_del_stack_resources sg active returned mask final **
      (task_stack_fragments_rep handler_stack handler_fragments **
        ((cpu_sr # UInt |-> registers.(kernel_save_cpsr)) ** (perr # UChar |-> old_error) ** frame)) |--
    (perr # UChar |-> old_error) **
      (kernel_stack_call_closed abi mutex_del_stack_resources sg active returned mask final **
       (cpu_sr # UInt |-> registers.(kernel_save_cpsr)) **
       task_stack_fragments_rep handler_stack handler_fragments ** frame)) by entailer!.
  destruct (kernel_heap_framed_uchar_store perr old_error 0 _ returned_heap ltac:(lia)
    (Hreturned_order returned_heap Hreturned)) as [finished [Hwrite_error Hfinished]].
  assert (finished = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst finished.
  assert (Hpublic : kernel_stack_call_closed abi mutex_del_stack_resources sg active returned mask final |--
    mutex_del_runtime_post environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask state pe 0 eid 0 0).
  { unfold mutex_del_runtime_post; Left; Right; Exists acquired checkpoint 0.
    apply _derivable1_andp_intros; [entailer!|].
    unfold mutex_del_runtime_return, mutex_del_runtime_return_at; Exists returned final environment.
    unfold mutex_del_callsite_environment; entailer!. }
  split; [exact Hsaved_value|]. split; [exact Hobservation|].
  match type of Hfinished with ?P after => match goal with |- ?Q after => assert (Hfinish : P |-- Q) end end.
  { rewrite Hsaved_value; sep_apply_l_atomic Hpublic; entailer!. }
  exact (Hfinish after Hfinished).
Qed.

(** Real held-owner path where EffectivePrio's returned priority equals
    the TCB priority read by Del, so the source skips RdyAtPrio. This is
    separate from the still-required priority-changing source branch. *)
Definition mutex_del_no_pend_owner_skip_execution
  restore_entry call state mask registers pe eid observed ceiling pointer priority perr cpu_sr saved_word
  before entered acquired returned final after : Prop :=
  let checkpoint := mutex_del_recycle_state sg eid observed (mutex_del_released_state acquired ceiling) in
  exists initialized prefix_heap returned_registers resumed final_registers final_state
    saved_heap body_heap released_heap recycled middle restored returned_heap cursor written final_cursor count,
    kernel_heap_execution (pointer_store_writes cpu_sr 0) before initialized /\
    mutex_del_call_prefix_execution sg pe perr initialized None prefix_heap /\
    registers.(kernel_save_return_word) = None /\
    valid_os_cpu_sr registers.(kernel_save_cpsr) /\
    armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask /\
    mutex_del_irq_registers_execution environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
      environment.(mutex_del_call_continuations) registers_source sg Local local_step normal_return
      handler_stack handler_fragments (armv7a_save_entry_address save + 4)
      (kernel_save_read_cpsr registers) call state prefix_heap returned_registers entered acquired resumed /\
    armv7a_save_suffix_transition save returned_registers acquired resumed
      final_registers final_state saved_heap /\
    saved_word = final_registers.(kernel_save_r0) /\
    kernel_heap_execution (pointer_store_writes cpu_sr saved_word) saved_heap body_heap /\
    uchar_load (pe + OSEventType_off) 4 body_heap /\
    uchar_load (pe + OSEventGrp_off) 0 body_heap /\
    mutex_del_count_load (pe + OSEventCnt_off) count body_heap /\
    unsigned_last_nbits (Z.shiftr count 8) 8 = ceiling /\
    ceiling <> 255 /\
    pointer <> 0 /\
    pointer_load (pe + OSEventPtr_off) pointer body_heap /\
    kernel_heap_execution
      (pointer_store_writes (sg.(g_OSTCBPrioTbl) + ceiling * sizeof(PTR)) 0) body_heap released_heap /\
    mutex_del_effective_priority_reads sg pointer released_heap 0 priority /\
    uchar_load (tcb_field_address pointer TCBPrio) priority released_heap /\
    mutex_del_recycle_stores sg pe released_heap recycled /\
    cursor.(kernel_restore_r0) = saved_word /\
    armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 /\
    armv7a_restore_prefix_transition restore cursor recycled written middle /\
    mutex_del_restore_irqs_execution environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
      environment.(mutex_del_call_continuations) sg Local local_step normal_return
      handler_stack handler_fragments (armv7a_irq_fiq_mask saved_word)
      (restore_entry + 8) cursor.(kernel_restore_lr) entered checkpoint middle returned final restored /\
    armv7a_restore_suffix_transition restore written restored final_cursor returned_heap /\
    kernel_heap_execution [(perr, 0)] returned_heap after.

Lemma mutex_del_runtime_no_pend_owner_skip_source_post : forall restore_entry call state mask registers
  pe eid observed ceiling pointer priority perr old_error cpu_sr saved_word before entered acquired returned final after (frame : Assertion),
  mutex_del_parent_layout sg -> mutex_del_parent_input sg pe state eid observed ->
  (mutex_del_runtime_entry environment environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) sg call mask state **
    (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
    task_stack_fragments_rep handler_stack handler_fragments ** frame) before ->
  mutex_del_no_pend_owner_skip_execution restore_entry call state mask registers pe eid observed ceiling pointer priority perr cpu_sr
    saved_word before entered acquired returned final after ->
  saved_word = registers.(kernel_save_cpsr) /\
  mutex_del_parent_critical_observation sg eid 0 0 0 0 acquired
    (mutex_del_recycle_state sg eid observed (mutex_del_released_state acquired ceiling)) /\
  (mutex_del_runtime_post environment environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) sg call mask state pe 0 eid 0 0 **
    (perr # UChar |-> 0) ** (cpu_sr # UInt |-> saved_word) **
    task_stack_fragments_rep handler_stack handler_fragments ** frame) after.
Proof.
  intros restore_entry call state mask registers pe eid observed ceiling pointer priority perr old_error cpu_sr saved_word
    before entered acquired returned final after frame Hlayout Hdomain Hentry Hsource.
  set (abi := environment.(mutex_del_call_continuations)) in *.
  set (active := task_stack_call_active_key call).
  assert (Hopen : mutex_del_runtime_entry environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask state |--
    kernel_stack_call_closed abi mutex_del_stack_resources sg active call mask state).
  { unfold mutex_del_runtime_entry; Intros same_environment.
    destruct H as [Henv ->]; reflexivity. }
  assert (Hpre : (kernel_stack_call_closed abi mutex_del_stack_resources sg active call mask state **
      (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
      task_stack_fragments_rep handler_stack handler_fragments ** frame) before).
  { match type of Hentry with ?P before => match goal with |- ?Q before => assert (Horder : P |-- Q) end end.
    { sep_apply_l_atomic Hopen; entailer!. } exact (Horder before Hentry). }
  destruct Hsource as (initialized & prefix_heap & returned_registers & resumed & final_registers & final_state &
    saved_heap & body_heap & released_heap & recycled & middle & restored & returned_heap & cursor & written & final_cursor & count &
    Hinit & Hprefix & Hnone & Hvalid & Hmask & Hsave_irqs & Hsave_suffix & Hsaved & Hstore &
    Htype_read & Hgroup_read & Hcount_read & Hceiling & Hpcp & Hpointer_nonzero & Hptr_read & Hrelease & Hreads & Hcompare & Hstores & Hr0 & Hmasked & Hrestore_prefix &
    Hrestore_irqs & Hrestore_suffix & Herror).
  subst saved_word.
  set (entry_residual := mutex_del_stack_critical_frame abi sg active state **
    task_stack_fragments_rep handler_stack handler_fragments ** frame).
  assert (Hinitialize_order : kernel_stack_call_closed abi mutex_del_stack_resources sg active call mask state **
      (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
      task_stack_fragments_rep handler_stack handler_fragments ** frame |--
    (cpu_sr # UInt |->_) **
      (kernel_program_inv sg state ** (perr # UChar |-> old_error) **
       (kernel_call_execution_owned environment.(mutex_del_call_external)
          environment.(mutex_del_call_platform) call mask ** entry_residual))).
  { unfold kernel_stack_call_closed, entry_residual.
    rewrite mutex_del_stack_world_split_critical_frame; entailer!. }
  destruct (task_stack_uint_store_execution cpu_sr 0 _ before ltac:(lia)
    (Hinitialize_order before Hpre)) as [produced [Hinitialize Hinitialized]].
  assert (produced = initialized) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hprefix_order : (cpu_sr # UInt |-> 0) **
      (kernel_program_inv sg state ** (perr # UChar |-> old_error) **
       (kernel_call_execution_owned environment.(mutex_del_call_external)
          environment.(mutex_del_call_platform) call mask ** entry_residual)) |--
    kernel_program_inv sg state ** (perr # UChar |-> old_error) **
      (kernel_call_execution_owned environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) call mask ** (cpu_sr # UInt |->_) ** entry_residual)).
  { sep_apply_l_atomic (store_uint_undef_store_uint cpu_sr 0); entailer!. }
  destruct (mutex_del_call_prefix_resources sg state pe eid observed perr old_error initialized None prefix_heap _
    Hdomain (Hprefix_order initialized Hinitialized) Hprefix)
    as [[Hnonnull [Hentry_type Hnest]] Hprefix_owned].
  assert (Hprefix_ok : mutex_del_parent_prefix_ok pe state eid).
  { unfold mutex_del_parent_prefix_ok; apply mutex_del_before_save_continues_iff;
    [rewrite Hnest; lia|auto]. }
  assert (Hsave_order : kernel_program_inv sg state ** (perr # UChar |-> old_error) **
      (kernel_call_execution_owned environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) call mask ** (cpu_sr # UInt |->_) ** entry_residual) |--
    kernel_stack_call_closed abi mutex_del_stack_resources sg active call
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state **
      (task_stack_fragments_rep handler_stack handler_fragments **
       ((cpu_sr # UInt |->_) ** (perr # UChar |-> old_error) ** frame))).
  { unfold kernel_stack_call_closed, entry_residual; rewrite Hmask.
    rewrite mutex_del_stack_world_split_critical_frame; entailer!. }
  destruct (mutex_del_stack_irq_save_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi registers_source sg Local
    local_step normal_return handler_contract handler_stack handler_fragments critical arch save active call state
    registers prefix_heap returned_registers entered acquired resumed final_registers final_state saved_heap _
    Hnone Hvalid (Hsave_order prefix_heap Hprefix_owned) Hsave_irqs Hsave_suffix)
    as [Hmrs [Hsuffix_source [Hstate [Hsaved_value [Hfinal_cpsr [Hreturn [Hsame_entered [Hevents Hsaved_heap]]]]]]]].
  destruct (mutex_del_irq_registers_execution_refinement environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi registers_source sg Local
    local_step normal_return handler_stack handler_fragments _ _ _ _ _ _ _ _ _ Hsave_irqs)
    as [_ [_ [_ Hcounter]]].
  pose proof (mutex_del_counter_irqs_owner_history environment sg Local local_step normal_return
    handler_stack handler_fragments _ _ _ _ _ _ _ _ _ Hcounter) as Hhistory.
  assert (Hstore_order : kernel_stack_call_masked abi mutex_del_stack_resources critical sg active entered
      final_registers.(kernel_save_r0) acquired acquired **
      (task_stack_fragments_rep handler_stack handler_fragments **
       ((cpu_sr # UInt |->_) ** (perr # UChar |-> old_error) ** frame)) |--
    (cpu_sr # UInt |->_) **
      (kernel_stack_call_masked abi mutex_del_stack_resources critical sg active entered
         final_registers.(kernel_save_r0) acquired acquired ** (perr # UChar |-> old_error) **
       task_stack_fragments_rep handler_stack handler_fragments ** frame)) by entailer!.
  destruct (task_stack_uint_store_execution cpu_sr final_registers.(kernel_save_r0) _ saved_heap
    ltac:(rewrite Hsaved_value; exact Hvalid) (Hstore_order saved_heap Hsaved_heap))
    as [produced [Hwrite Hbody_owned]].
  assert (produced = body_heap) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  set (body_frame := critical_region_masked environment.(mutex_del_call_platform) critical sg
      entered.(os_sched_call_invocation) entered.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
    os_sched_context_resources environment.(mutex_del_call_external) entered **
    mutex_del_stack_critical_frame abi sg active acquired **
    task_stack_fragments_rep handler_stack handler_fragments **
    (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** (perr # UChar |-> old_error) ** frame).
  assert (Hbody_order : (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
      (kernel_stack_call_masked abi mutex_del_stack_resources critical sg active entered
         final_registers.(kernel_save_r0) acquired acquired ** (perr # UChar |-> old_error) **
       task_stack_fragments_rep handler_stack handler_fragments ** frame) |--
    coq_prop (UCOS2_state_inv sg acquired /\ mutex_program_selected_reachable sg acquired) &&
      (kernel_program_inv sg acquired ** body_frame)).
  { unfold kernel_stack_call_masked, body_frame.
    rewrite mutex_del_stack_world_split_critical_frame.
    unfold kernel_program_inv, mutex_del_stack_critical_frame; entailer!. }
  destruct (Hbody_order body_heap Hbody_owned) as [[Hacquired_valid Hreach] Hbody].
  destruct Hdomain as [Hzero|[_ [Haddress [Hid Hslot]]]]; [contradiction|].
  assert (Hacquired_slot : sem_query_public_slot acquired eid observed).
  { unfold sem_query_public_slot, mutex_query_lookup in *; rewrite Hevents; exact Hslot. }
  pose proof (mutex_del_call_program_type_load sg acquired pe eid observed body_heap _ Haddress Hacquired_slot Hbody)
    as Hactual_type.
  assert (Htype : event_slot_type_value acquired.(EventState) eid = 4)
    by (eapply uchar_load_deterministic; eassumption).
  destruct (mutex_del_parent_recheck_live_fields sg acquired eid observed Hacquired_valid Hacquired_slot Htype)
    as [mutex [Hlookup [Hkind Hfields]]].
  assert (Howner_use : mutex_owner_event_unlinked acquired.(TskState) acquired.(EventState)).
  { eapply mutex_program_reachable_owner_use; [|exact Hreach].
    intros; eapply mutex_program_selected_initial_empty; eassumption. }
  assert (Hparent : mutex_del_parent_entry sg eid acquired observed mutex)
    by (exact (conj Hacquired_valid (conj Hlookup (conj Hkind (conj Hfields Howner_use))))).
  pose proof (mutex_del_call_program_group_load sg acquired pe eid observed body_heap _ Haddress Hlookup Hbody)
    as Hactual_group.
  assert (Hempty : encode_event_wait_grp observed.(waitList) acquired.(TskState) = 0)
    by (eapply uchar_load_deterministic; eassumption).
  pose proof (mutex_del_program_count_load sg acquired pe eid observed body_heap _ Haddress Hlookup Hbody)
    as Hactual_count.
  assert (Hcount : count = encode_event_cnt_value observed)
    by (eapply mutex_del_count_load_deterministic; eassumption).
  rewrite Hcount, (mutex_del_parent_cast_count sg eid acquired observed mutex Hparent) in Hceiling.
  pose proof (proj2 (proj2 (mutex_del_parent_count_decode sg eid acquired observed mutex Hparent))) as Hdecode.
  rewrite Hdecode in Hceiling; subst ceiling.
  rewrite Haddress in Hptr_read.
  pose proof (mutex_del_owned_ceiling_skip_resources sg eid acquired observed mutex pointer priority
    body_heap released_heap body_frame Hlayout Hparent Hpcp Hpointer_nonzero
    Hbody Hptr_read Hrelease Hreads Hcompare) as Hprepared.
  set (prepared := mutex_del_released_state acquired mutex.(mfPCP)) in *.
  assert (Hprepare_open :
    mutex_del_parent_prepared sg eid acquired prepared observed mutex ** unmap_table_rep sg ** body_frame |--
    coq_prop (mutex_del_prepare sg mutex acquired prepared /\
      mutex_del_wake_state_inv sg eid mutex prepared) &&
      (kernel_program_rep sg prepared ** body_frame)).
  { unfold mutex_del_parent_prepared, mutex_del_wake_rep, kernel_program_rep; entailer!. }
  destruct (Hprepare_open released_heap Hprepared) as [[Hprepare Hphase] Hreleased].
  set (checkpoint := mutex_del_recycle_state sg eid observed prepared) in *.
  assert (Hcritical : mutex_del_critical sg eid 0 acquired (0, (OS_ERR_NONE, false)) checkpoint).
  { exists observed, mutex; split; [exact Hlookup|]. split; [exact Hkind|]. split; [exact Hfields|].
    destruct (Z.eq_dec 0 0); [|contradiction].
    destruct (Z.eq_dec (encode_event_wait_grp observed.(waitList) acquired.(TskState)) 0); [|contradiction].
    exists prepared; split; [exact Hprepare|]. split; reflexivity. }
  assert (Hobservation : mutex_del_parent_critical_observation sg eid 0 0 0 0 acquired checkpoint).
  { exists OS_ERR_NONE, false; split; [exact Hcritical|split; reflexivity]. }
  assert (Hwaiters : observed.(waitList) = [])
    by (eapply mutex_del_event_group_zero_implies_empty; eassumption).
  assert (Hprepared_empty : encode_event_wait_grp observed.(waitList) prepared.(TskState) = 0)
    by (rewrite Hwaiters; reflexivity).
  rewrite Haddress in Hstores.
  pose proof (mutex_del_recycle_stores_resources sg eid mutex prepared observed released_heap recycled body_frame
    Hphase Hlookup Hprepared_empty Hreleased Hstores) as Hrecycled.
  fold checkpoint in Hrecycled.
  assert (Hcheckpoint : mutex_del_stack_checkpoint sg acquired checkpoint).
  { right; exists eid, 0, (0, (OS_ERR_NONE, false)); exact Hcritical. }
  assert (Hrestore_order : kernel_program_inv sg checkpoint ** body_frame |--
    mutex_del_stack_restore_input abi critical sg active entered final_registers.(kernel_save_r0) acquired checkpoint **
      (task_stack_fragments_rep handler_stack handler_fragments **
       ((cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** (perr # UChar |-> old_error) ** frame))).
  { unfold body_frame, mutex_del_stack_restore_input; entailer!. }
  destruct (mutex_del_stack_repeated_restore_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi sg Local local_step normal_return
    handler_contract handler_stack handler_fragments critical arch restore active entered
    final_registers.(kernel_save_r0) acquired checkpoint restore_entry cursor recycled written middle
    returned final restored final_cursor returned_heap _ Hr0 Hmasked (Hrestore_order recycled Hrecycled)
    Hrestore_prefix Hrestore_irqs Hrestore_suffix) as [Hi [Ho [Hs [Hrestore_return Hreturned]]]].
  rewrite Hsaved_value, Hmask in Hreturned.
  assert (Hsame : kernel_stack_call_same_call returned call).
  { destruct Hsame_entered as [Hi' [Ho' Hs']]; unfold kernel_stack_call_same_call; repeat split; congruence. }
  assert (Hreturned_order : kernel_stack_call_closed abi mutex_del_stack_resources sg active returned mask final **
      (task_stack_fragments_rep handler_stack handler_fragments **
        ((cpu_sr # UInt |-> registers.(kernel_save_cpsr)) ** (perr # UChar |-> old_error) ** frame)) |--
    (perr # UChar |-> old_error) **
      (kernel_stack_call_closed abi mutex_del_stack_resources sg active returned mask final **
       (cpu_sr # UInt |-> registers.(kernel_save_cpsr)) **
       task_stack_fragments_rep handler_stack handler_fragments ** frame)) by entailer!.
  destruct (kernel_heap_framed_uchar_store perr old_error 0 _ returned_heap ltac:(lia)
    (Hreturned_order returned_heap Hreturned)) as [finished [Hwrite_error Hfinished]].
  assert (finished = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst finished.
  assert (Hpublic : kernel_stack_call_closed abi mutex_del_stack_resources sg active returned mask final |--
    mutex_del_runtime_post environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask state pe 0 eid 0 0).
  { unfold mutex_del_runtime_post; Left; Right; Exists acquired checkpoint 0.
    apply _derivable1_andp_intros; [entailer!|].
    unfold mutex_del_runtime_return, mutex_del_runtime_return_at; Exists returned final environment.
    unfold mutex_del_callsite_environment; entailer!. }
  split; [exact Hsaved_value|]. split; [exact Hobservation|].
  match type of Hfinished with ?P after => match goal with |- ?Q after => assert (Hfinish : P |-- Q) end end.
  { rewrite Hsaved_value; sep_apply_l_atomic Hpublic; entailer!. }
  exact (Hfinish after Hfinished).
Qed.
(** Actual NO_PEND held-owner branch with unequal old and scanned priorities.
    The helper writes are followed by the same four recycling stores and
    the current stack-aware Restore producer.  Ready and current-task
    choices remain the source's physical reads, without new entry guards. *)
Definition mutex_del_no_pend_owner_adjust_execution
  restore_entry call state mask registers pe eid observed ceiling pointer old_priority priority perr cpu_sr saved_word
  before entered acquired returned final after : Prop :=
  let checkpoint := mutex_del_recycle_state sg eid observed (mutex_del_owner_adjusted_state sg acquired eid priority) in
  exists initialized prefix_heap returned_registers resumed final_registers final_state
    saved_heap body_heap released_heap adjusted_heap recycled middle restored returned_heap cursor written final_cursor count,
    kernel_heap_execution (pointer_store_writes cpu_sr 0) before initialized /\
    mutex_del_call_prefix_execution sg pe perr initialized None prefix_heap /\
    registers.(kernel_save_return_word) = None /\
    valid_os_cpu_sr registers.(kernel_save_cpsr) /\
    armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask /\
    mutex_del_irq_registers_execution environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
      environment.(mutex_del_call_continuations) registers_source sg Local local_step normal_return
      handler_stack handler_fragments (armv7a_save_entry_address save + 4)
      (kernel_save_read_cpsr registers) call state prefix_heap returned_registers entered acquired resumed /\
    armv7a_save_suffix_transition save returned_registers acquired resumed
      final_registers final_state saved_heap /\
    saved_word = final_registers.(kernel_save_r0) /\
    kernel_heap_execution (pointer_store_writes cpu_sr saved_word) saved_heap body_heap /\
    uchar_load (pe + OSEventType_off) 4 body_heap /\
    uchar_load (pe + OSEventGrp_off) 0 body_heap /\
    mutex_del_count_load (pe + OSEventCnt_off) count body_heap /\
    unsigned_last_nbits (Z.shiftr count 8) 8 = ceiling /\
    ceiling <> 255 /\
    pointer <> 0 /\
    pointer_load (pe + OSEventPtr_off) pointer body_heap /\
    kernel_heap_execution
      (pointer_store_writes (sg.(g_OSTCBPrioTbl) + ceiling * sizeof(PTR)) 0) body_heap released_heap /\
    mutex_del_effective_priority_reads sg pointer released_heap 0 priority /\
    uchar_load (tcb_field_address pointer TCBPrio) old_priority released_heap /\
    old_priority <> priority /\
    mutex_del_rdy_at_priority_execution sg pointer priority released_heap adjusted_heap /\
    mutex_del_recycle_stores sg pe adjusted_heap recycled /\
    cursor.(kernel_restore_r0) = saved_word /\
    armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 /\
    armv7a_restore_prefix_transition restore cursor recycled written middle /\
    mutex_del_restore_irqs_execution environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
      environment.(mutex_del_call_continuations) sg Local local_step normal_return
      handler_stack handler_fragments (armv7a_irq_fiq_mask saved_word)
      (restore_entry + 8) cursor.(kernel_restore_lr) entered checkpoint middle returned final restored /\
    armv7a_restore_suffix_transition restore written restored final_cursor returned_heap /\
    kernel_heap_execution [(perr, 0)] returned_heap after.

Lemma mutex_del_runtime_no_pend_owner_adjust_source_post : forall restore_entry call state mask registers
  pe eid observed ceiling pointer old_priority priority perr old_error cpu_sr saved_word before entered acquired returned final after (frame : Assertion),
  mutex_del_parent_layout sg -> mutex_del_parent_input sg pe state eid observed ->
  (mutex_del_runtime_entry environment environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) sg call mask state **
    (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
    task_stack_fragments_rep handler_stack handler_fragments ** frame) before ->
  mutex_del_no_pend_owner_adjust_execution restore_entry call state mask registers pe eid observed ceiling pointer old_priority priority perr cpu_sr
    saved_word before entered acquired returned final after ->
  saved_word = registers.(kernel_save_cpsr) /\
  mutex_del_parent_critical_observation sg eid 0 0 0 0 acquired
    (mutex_del_recycle_state sg eid observed (mutex_del_owner_adjusted_state sg acquired eid priority)) /\
  (mutex_del_runtime_post environment environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) sg call mask state pe 0 eid 0 0 **
    (perr # UChar |-> 0) ** (cpu_sr # UInt |-> saved_word) **
    task_stack_fragments_rep handler_stack handler_fragments ** frame) after.
Proof.
  intros restore_entry call state mask registers pe eid observed ceiling pointer old_priority priority perr old_error cpu_sr saved_word
    before entered acquired returned final after frame Hlayout Hdomain Hentry Hsource.
  set (abi := environment.(mutex_del_call_continuations)) in *.
  set (active := task_stack_call_active_key call).
  assert (Hopen : mutex_del_runtime_entry environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask state |--
    kernel_stack_call_closed abi mutex_del_stack_resources sg active call mask state).
  { unfold mutex_del_runtime_entry; Intros same_environment.
    destruct H as [Henv ->]; reflexivity. }
  assert (Hpre : (kernel_stack_call_closed abi mutex_del_stack_resources sg active call mask state **
      (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
      task_stack_fragments_rep handler_stack handler_fragments ** frame) before).
  { match type of Hentry with ?P before => match goal with |- ?Q before => assert (Horder : P |-- Q) end end.
    { sep_apply_l_atomic Hopen; entailer!. } exact (Horder before Hentry). }
  destruct Hsource as (initialized & prefix_heap & returned_registers & resumed & final_registers & final_state &
    saved_heap & body_heap & released_heap & adjusted_heap & recycled & middle & restored & returned_heap & cursor & written & final_cursor & count &
    Hinit & Hprefix & Hnone & Hvalid & Hmask & Hsave_irqs & Hsave_suffix & Hsaved & Hstore &
    Htype_read & Hgroup_read & Hcount_read & Hceiling & Hpcp & Hpointer_nonzero & Hptr_read & Hrelease & Hreads & Hcompare & Hdifferent & Hrdy & Hstores & Hr0 & Hmasked & Hrestore_prefix &
    Hrestore_irqs & Hrestore_suffix & Herror).
  subst saved_word.
  set (entry_residual := mutex_del_stack_critical_frame abi sg active state **
    task_stack_fragments_rep handler_stack handler_fragments ** frame).
  assert (Hinitialize_order : kernel_stack_call_closed abi mutex_del_stack_resources sg active call mask state **
      (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
      task_stack_fragments_rep handler_stack handler_fragments ** frame |--
    (cpu_sr # UInt |->_) **
      (kernel_program_inv sg state ** (perr # UChar |-> old_error) **
       (kernel_call_execution_owned environment.(mutex_del_call_external)
          environment.(mutex_del_call_platform) call mask ** entry_residual))).
  { unfold kernel_stack_call_closed, entry_residual.
    rewrite mutex_del_stack_world_split_critical_frame; entailer!. }
  destruct (task_stack_uint_store_execution cpu_sr 0 _ before ltac:(lia)
    (Hinitialize_order before Hpre)) as [produced [Hinitialize Hinitialized]].
  assert (produced = initialized) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hprefix_order : (cpu_sr # UInt |-> 0) **
      (kernel_program_inv sg state ** (perr # UChar |-> old_error) **
       (kernel_call_execution_owned environment.(mutex_del_call_external)
          environment.(mutex_del_call_platform) call mask ** entry_residual)) |--
    kernel_program_inv sg state ** (perr # UChar |-> old_error) **
      (kernel_call_execution_owned environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) call mask ** (cpu_sr # UInt |->_) ** entry_residual)).
  { sep_apply_l_atomic (store_uint_undef_store_uint cpu_sr 0); entailer!. }
  destruct (mutex_del_call_prefix_resources sg state pe eid observed perr old_error initialized None prefix_heap _
    Hdomain (Hprefix_order initialized Hinitialized) Hprefix)
    as [[Hnonnull [Hentry_type Hnest]] Hprefix_owned].
  assert (Hprefix_ok : mutex_del_parent_prefix_ok pe state eid).
  { unfold mutex_del_parent_prefix_ok; apply mutex_del_before_save_continues_iff;
    [rewrite Hnest; lia|auto]. }
  assert (Hsave_order : kernel_program_inv sg state ** (perr # UChar |-> old_error) **
      (kernel_call_execution_owned environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) call mask ** (cpu_sr # UInt |->_) ** entry_residual) |--
    kernel_stack_call_closed abi mutex_del_stack_resources sg active call
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state **
      (task_stack_fragments_rep handler_stack handler_fragments **
       ((cpu_sr # UInt |->_) ** (perr # UChar |-> old_error) ** frame))).
  { unfold kernel_stack_call_closed, entry_residual; rewrite Hmask.
    rewrite mutex_del_stack_world_split_critical_frame; entailer!. }
  destruct (mutex_del_stack_irq_save_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi registers_source sg Local
    local_step normal_return handler_contract handler_stack handler_fragments critical arch save active call state
    registers prefix_heap returned_registers entered acquired resumed final_registers final_state saved_heap _
    Hnone Hvalid (Hsave_order prefix_heap Hprefix_owned) Hsave_irqs Hsave_suffix)
    as [Hmrs [Hsuffix_source [Hstate [Hsaved_value [Hfinal_cpsr [Hreturn [Hsame_entered [Hevents Hsaved_heap]]]]]]]].
  destruct (mutex_del_irq_registers_execution_refinement environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi registers_source sg Local
    local_step normal_return handler_stack handler_fragments _ _ _ _ _ _ _ _ _ Hsave_irqs)
    as [_ [_ [_ Hcounter]]].
  pose proof (mutex_del_counter_irqs_owner_history environment sg Local local_step normal_return
    handler_stack handler_fragments _ _ _ _ _ _ _ _ _ Hcounter) as Hhistory.
  assert (Hstore_order : kernel_stack_call_masked abi mutex_del_stack_resources critical sg active entered
      final_registers.(kernel_save_r0) acquired acquired **
      (task_stack_fragments_rep handler_stack handler_fragments **
       ((cpu_sr # UInt |->_) ** (perr # UChar |-> old_error) ** frame)) |--
    (cpu_sr # UInt |->_) **
      (kernel_stack_call_masked abi mutex_del_stack_resources critical sg active entered
         final_registers.(kernel_save_r0) acquired acquired ** (perr # UChar |-> old_error) **
       task_stack_fragments_rep handler_stack handler_fragments ** frame)) by entailer!.
  destruct (task_stack_uint_store_execution cpu_sr final_registers.(kernel_save_r0) _ saved_heap
    ltac:(rewrite Hsaved_value; exact Hvalid) (Hstore_order saved_heap Hsaved_heap))
    as [produced [Hwrite Hbody_owned]].
  assert (produced = body_heap) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  set (body_frame := critical_region_masked environment.(mutex_del_call_platform) critical sg
      entered.(os_sched_call_invocation) entered.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
    os_sched_context_resources environment.(mutex_del_call_external) entered **
    mutex_del_stack_critical_frame abi sg active acquired **
    task_stack_fragments_rep handler_stack handler_fragments **
    (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** (perr # UChar |-> old_error) ** frame).
  assert (Hbody_order : (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
      (kernel_stack_call_masked abi mutex_del_stack_resources critical sg active entered
         final_registers.(kernel_save_r0) acquired acquired ** (perr # UChar |-> old_error) **
       task_stack_fragments_rep handler_stack handler_fragments ** frame) |--
    coq_prop (UCOS2_state_inv sg acquired /\ mutex_program_selected_reachable sg acquired) &&
      (kernel_program_inv sg acquired ** body_frame)).
  { unfold kernel_stack_call_masked, body_frame.
    rewrite mutex_del_stack_world_split_critical_frame.
    unfold kernel_program_inv, mutex_del_stack_critical_frame; entailer!. }
  destruct (Hbody_order body_heap Hbody_owned) as [[Hacquired_valid Hreach] Hbody].
  destruct Hdomain as [Hzero|[_ [Haddress [Hid Hslot]]]]; [contradiction|].
  assert (Hacquired_slot : sem_query_public_slot acquired eid observed).
  { unfold sem_query_public_slot, mutex_query_lookup in *; rewrite Hevents; exact Hslot. }
  pose proof (mutex_del_call_program_type_load sg acquired pe eid observed body_heap _ Haddress Hacquired_slot Hbody)
    as Hactual_type.
  assert (Htype : event_slot_type_value acquired.(EventState) eid = 4)
    by (eapply uchar_load_deterministic; eassumption).
  destruct (mutex_del_parent_recheck_live_fields sg acquired eid observed Hacquired_valid Hacquired_slot Htype)
    as [mutex [Hlookup [Hkind Hfields]]].
  assert (Howner_use : mutex_owner_event_unlinked acquired.(TskState) acquired.(EventState)).
  { eapply mutex_program_reachable_owner_use; [|exact Hreach].
    intros; eapply mutex_program_selected_initial_empty; eassumption. }
  assert (Hparent : mutex_del_parent_entry sg eid acquired observed mutex)
    by (exact (conj Hacquired_valid (conj Hlookup (conj Hkind (conj Hfields Howner_use))))).
  pose proof (mutex_del_call_program_group_load sg acquired pe eid observed body_heap _ Haddress Hlookup Hbody)
    as Hactual_group.
  assert (Hempty : encode_event_wait_grp observed.(waitList) acquired.(TskState) = 0)
    by (eapply uchar_load_deterministic; eassumption).
  pose proof (mutex_del_program_count_load sg acquired pe eid observed body_heap _ Haddress Hlookup Hbody)
    as Hactual_count.
  assert (Hcount : count = encode_event_cnt_value observed)
    by (eapply mutex_del_count_load_deterministic; eassumption).
  rewrite Hcount, (mutex_del_parent_cast_count sg eid acquired observed mutex Hparent) in Hceiling.
  pose proof (proj2 (proj2 (mutex_del_parent_count_decode sg eid acquired observed mutex Hparent))) as Hdecode.
  rewrite Hdecode in Hceiling; subst ceiling.
  rewrite Haddress in Hptr_read.
  pose proof (mutex_del_owned_ceiling_adjust_resources sg eid acquired observed mutex pointer old_priority priority
    body_heap released_heap adjusted_heap body_frame Hlayout Hparent Hpcp Hpointer_nonzero Hdifferent
    Hbody Hptr_read Hrelease Hreads Hcompare Hrdy) as Hprepared.
  set (prepared := mutex_del_owner_adjusted_state sg acquired eid priority) in *.
  assert (Hprepare_open :
    mutex_del_parent_prepared sg eid acquired prepared observed mutex ** unmap_table_rep sg ** body_frame |--
    coq_prop (mutex_del_prepare sg mutex acquired prepared /\
      mutex_del_wake_state_inv sg eid mutex prepared) &&
      (kernel_program_rep sg prepared ** body_frame)).
  { unfold mutex_del_parent_prepared, mutex_del_wake_rep, kernel_program_rep; entailer!. }
  destruct (Hprepare_open adjusted_heap Hprepared) as [[Hprepare Hphase] Hreleased].
  set (checkpoint := mutex_del_recycle_state sg eid observed prepared) in *.
  assert (Hcritical : mutex_del_critical sg eid 0 acquired (0, (OS_ERR_NONE, false)) checkpoint).
  { exists observed, mutex; split; [exact Hlookup|]. split; [exact Hkind|]. split; [exact Hfields|].
    destruct (Z.eq_dec 0 0); [|contradiction].
    destruct (Z.eq_dec (encode_event_wait_grp observed.(waitList) acquired.(TskState)) 0); [|contradiction].
    exists prepared; split; [exact Hprepare|]. split; reflexivity. }
  assert (Hobservation : mutex_del_parent_critical_observation sg eid 0 0 0 0 acquired checkpoint).
  { exists OS_ERR_NONE, false; split; [exact Hcritical|split; reflexivity]. }
  assert (Hwaiters : observed.(waitList) = [])
    by (eapply mutex_del_event_group_zero_implies_empty; eassumption).
  assert (Hprepared_empty : encode_event_wait_grp observed.(waitList) prepared.(TskState) = 0)
    by (rewrite Hwaiters; reflexivity).
  rewrite Haddress in Hstores.
  assert (Hprepared_lookup : prepared.(EventState).(inUsedEventStates) eid = Some observed).
  { rewrite (mutex_del_prepare_event_state_eq sg mutex acquired prepared Hprepare); exact Hlookup. }
  pose proof (mutex_del_recycle_stores_resources sg eid mutex prepared observed adjusted_heap recycled body_frame
    Hphase Hprepared_lookup Hprepared_empty Hreleased Hstores) as Hrecycled.
  fold checkpoint in Hrecycled.
  assert (Hcheckpoint : mutex_del_stack_checkpoint sg acquired checkpoint).
  { right; exists eid, 0, (0, (OS_ERR_NONE, false)); exact Hcritical. }
  assert (Hrestore_order : kernel_program_inv sg checkpoint ** body_frame |--
    mutex_del_stack_restore_input abi critical sg active entered final_registers.(kernel_save_r0) acquired checkpoint **
      (task_stack_fragments_rep handler_stack handler_fragments **
       ((cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** (perr # UChar |-> old_error) ** frame))).
  { unfold body_frame, mutex_del_stack_restore_input; entailer!. }
  destruct (mutex_del_stack_repeated_restore_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi sg Local local_step normal_return
    handler_contract handler_stack handler_fragments critical arch restore active entered
    final_registers.(kernel_save_r0) acquired checkpoint restore_entry cursor recycled written middle
    returned final restored final_cursor returned_heap _ Hr0 Hmasked (Hrestore_order recycled Hrecycled)
    Hrestore_prefix Hrestore_irqs Hrestore_suffix) as [Hi [Ho [Hs [Hrestore_return Hreturned]]]].
  rewrite Hsaved_value, Hmask in Hreturned.
  assert (Hsame : kernel_stack_call_same_call returned call).
  { destruct Hsame_entered as [Hi' [Ho' Hs']]; unfold kernel_stack_call_same_call; repeat split; congruence. }
  assert (Hreturned_order : kernel_stack_call_closed abi mutex_del_stack_resources sg active returned mask final **
      (task_stack_fragments_rep handler_stack handler_fragments **
        ((cpu_sr # UInt |-> registers.(kernel_save_cpsr)) ** (perr # UChar |-> old_error) ** frame)) |--
    (perr # UChar |-> old_error) **
      (kernel_stack_call_closed abi mutex_del_stack_resources sg active returned mask final **
       (cpu_sr # UInt |-> registers.(kernel_save_cpsr)) **
       task_stack_fragments_rep handler_stack handler_fragments ** frame)) by entailer!.
  destruct (kernel_heap_framed_uchar_store perr old_error 0 _ returned_heap ltac:(lia)
    (Hreturned_order returned_heap Hreturned)) as [finished [Hwrite_error Hfinished]].
  assert (finished = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst finished.
  assert (Hpublic : kernel_stack_call_closed abi mutex_del_stack_resources sg active returned mask final |--
    mutex_del_runtime_post environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask state pe 0 eid 0 0).
  { unfold mutex_del_runtime_post; Left; Right; Exists acquired checkpoint 0.
    apply _derivable1_andp_intros; [entailer!|].
    unfold mutex_del_runtime_return, mutex_del_runtime_return_at; Exists returned final environment.
    unfold mutex_del_callsite_environment; entailer!. }
  split; [exact Hsaved_value|]. split; [exact Hobservation|].
  match type of Hfinished with ?P after => match goal with |- ?Q after => assert (Hfinish : P |-- Q) end end.
  { rewrite Hsaved_value; sep_apply_l_atomic Hpublic; entailer!. }
  exact (Hfinish after Hfinished).
Qed.

End NoPendRecycleSource.
