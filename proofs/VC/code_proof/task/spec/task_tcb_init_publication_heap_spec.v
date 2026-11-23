Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Import UCOS2_C_Rules KernelHeapStorage KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The last five stores of the selected task-atomic-publication variant,
    after its conditional old-head Prev write and before final Restore.
    Each bitmap/count read is on the actual heap following the preceding
    store. The three TCB bytes are read, not re-created from a ready fact.
    This is the protected memory fragment, not an interrupt-free assumption
    about the earlier StackInit, allocation, hooks, or Save calls. *)
Definition task_tcb_init_publication_tail_fragment (sg : StableGlobVars)
  (priority pointer : Z) (before after : model) : Prop :=
  exists linked grouped readied counted group row count,
    kernel_heap_execution (pointer_store_writes sg.(g_OSTCBList) pointer) before linked /\
    uchar_load sg.(g_OSRdyGrp) group linked /\
    uchar_load (tcb_field_address pointer TCBBitY) (Z.shiftl 1 (priority / 8)) linked /\
    kernel_heap_execution [(sg.(g_OSRdyGrp), Z.lor group (Z.shiftl 1 (priority / 8)))]
      linked grouped /\
    uchar_load (tcb_field_address pointer TCBY) (priority / 8) grouped /\
    uchar_load (sg.(g_OSRdyTbl) + priority / 8 * sizeof(UCHAR)) row grouped /\
    uchar_load (tcb_field_address pointer TCBBitX) (Z.shiftl 1 (priority mod 8)) grouped /\
    kernel_heap_execution [(sg.(g_OSRdyTbl) + priority / 8 * sizeof(UCHAR),
      Z.lor row (Z.shiftl 1 (priority mod 8)))] grouped readied /\
    uchar_load sg.(g_OSTaskCtr) count readied /\
    kernel_heap_execution [(sg.(g_OSTaskCtr), count + 1)] readied counted /\
    kernel_heap_execution
      (pointer_store_writes (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) pointer) counted after.

Definition task_tcb_init_publication_cells (sg : StableGlobVars)
  (priority pointer head group row count entry : Z) : Assertion :=
  sg.(g_OSTCBList) # Ptr |-> head **
  sg.(g_OSRdyGrp) # UChar |-> group **
  (sg.(g_OSRdyTbl) + priority / 8 * sizeof(UCHAR)) # UChar |-> row **
  sg.(g_OSTaskCtr) # UChar |-> count **
  (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |-> entry **
  (tcb_field_address pointer TCBY) # UChar |-> (priority / 8) **
  (tcb_field_address pointer TCBBitY) # UChar |-> (Z.shiftl 1 (priority / 8)) **
  (tcb_field_address pointer TCBBitX) # UChar |-> (Z.shiftl 1 (priority mod 8)).

Lemma task_tcb_init_publication_cells_reads :
  forall sg priority pointer head group row count entry (frame : Assertion) heap,
  (task_tcb_init_publication_cells sg priority pointer head group row count entry ** frame) heap ->
  uchar_load sg.(g_OSRdyGrp) group heap /\
  uchar_load (sg.(g_OSRdyTbl) + priority / 8 * sizeof(UCHAR)) row heap /\
  uchar_load sg.(g_OSTaskCtr) count heap /\
  uchar_load (tcb_field_address pointer TCBY) (priority / 8) heap /\
  uchar_load (tcb_field_address pointer TCBBitY) (Z.shiftl 1 (priority / 8)) heap /\
  uchar_load (tcb_field_address pointer TCBBitX) (Z.shiftl 1 (priority mod 8)) heap.
Proof.
  intros sg priority pointer head group row count entry frame heap Hheap.
  assert (Hread : forall address value,
    (task_tcb_init_publication_cells sg priority pointer head group row count entry ** frame |--
      address # UChar |-> value ** TT) -> uchar_load address value heap).
  { intros address value Hfocus; eapply framed_uchar_store_load; exact (Hfocus heap Hheap). }
  repeat (apply conj; [apply Hread; unfold task_tcb_init_publication_cells;
    entailer!; intros ? ?; exact I|]).
  apply Hread; unfold task_tcb_init_publication_cells; entailer!; intros ? ?; exact I.
Qed.

Definition task_tcb_init_without_ready_fields (multi profile : bool)
  (base : Z) (image : TCBLayoutImage) : Assertion :=
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec (tcb_layout_cell multi base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX)
      (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY)
        (remove TCBLayoutField_eq_dec (TCBCommonField TCBY)
          (tcb_configured_fields multi profile)))) image.

Lemma task_tcb_init_storage_split_ready_fields : forall multi profile base image priority,
  image (TCBCommonField TCBY) = Some (priority / 8) ->
  image (TCBCommonField TCBBitY) = Some (Z.shiftl 1 (priority / 8)) ->
  image (TCBCommonField TCBBitX) = Some (Z.shiftl 1 (priority mod 8)) ->
  tcb_configured_storage_rep multi profile base image --||--
  (tcb_field_address base TCBY) # UChar |-> (priority / 8) **
  (tcb_field_address base TCBBitY) # UChar |-> (Z.shiftl 1 (priority / 8)) **
  (tcb_field_address base TCBBitX) # UChar |-> (Z.shiftl 1 (priority mod 8)) **
  task_tcb_init_without_ready_fields multi profile base image.
Proof.
  intros multi profile base image priority Hy Hbity Hbitx.
  set (fields := tcb_configured_fields multi profile).
  set (without_y := remove TCBLayoutField_eq_dec (TCBCommonField TCBY) fields).
  set (without_y_bity := remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) without_y).
  assert (Hnd : NoDup fields) by apply tcb_configured_fields_nodup.
  assert (Hremove : forall field list, NoDup list -> NoDup (remove TCBLayoutField_eq_dec field list)).
  { intros field list Hnodup; induction Hnodup as [|head tail Hnot Htail IH]; cbn; [constructor|].
    destruct (TCBLayoutField_eq_dec field head); [exact IH|].
    constructor; [|exact IH]. intro Hin; apply Hnot; apply in_remove in Hin; tauto. }
  assert (Hnd_y : NoDup without_y) by (apply Hremove; exact Hnd).
  assert (Hnd_y_bity : NoDup without_y_bity) by (apply Hremove; exact Hnd_y).
  assert (Hin_y : In (TCBCommonField TCBY) fields) by apply tcb_configured_common_field_in.
  assert (Hin_bity : In (TCBCommonField TCBBitY) without_y).
  { apply in_in_remove; [discriminate|apply tcb_configured_common_field_in]. }
  assert (Hin_bitx : In (TCBCommonField TCBBitX) without_y_bity).
  { apply in_in_remove; [discriminate|]. apply in_in_remove; [discriminate|apply tcb_configured_common_field_in]. }
  pose proof (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell multi base) fields image (TCBCommonField TCBY) Hnd Hin_y) as Hsplit_y.
  pose proof (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell multi base) without_y image (TCBCommonField TCBBitY) Hnd_y Hin_bity) as Hsplit_bity.
  pose proof (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell multi base) without_y_bity image (TCBCommonField TCBBitX) Hnd_y_bity Hin_bitx) as Hsplit_bitx.
  pose proof (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell multi base) fields image (TCBCommonField TCBY) Hnd Hin_y) as Hmerge_y.
  pose proof (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell multi base) without_y image (TCBCommonField TCBBitY) Hnd_y Hin_bity) as Hmerge_bity.
  pose proof (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell multi base) without_y_bity image (TCBCommonField TCBBitX) Hnd_y_bity Hin_bitx) as Hmerge_bitx.
  rewrite Hy in Hsplit_y, Hmerge_y; rewrite Hbity in Hsplit_bity, Hmerge_bity;
    rewrite Hbitx in Hsplit_bitx, Hmerge_bitx.
  cbn [tcb_layout_cell tcb_cell] in Hsplit_y, Hsplit_bity, Hsplit_bitx, Hmerge_y, Hmerge_bity, Hmerge_bitx.
  fold without_y in Hmerge_y; fold without_y_bity in Hmerge_bity.
  unfold tcb_configured_storage_rep, task_tcb_init_without_ready_fields; fold fields without_y without_y_bity.
  split.
  - sep_apply_l_atomic Hsplit_y; fold without_y.
    sep_apply_l_atomic Hsplit_bity; fold without_y_bity.
    sep_apply_l_atomic Hsplit_bitx; entailer!.
  - sep_apply_l_atomic Hmerge_bitx; sep_apply_l_atomic Hmerge_bity;
      sep_apply_l_atomic Hmerge_y; entailer!.
Qed.

(** Exact cut after the old-head Prev branch has finished.  The global
    cells still have their old values; the private node already contains
    the actual StackInit return SP, initialized bytes and new links. *)
Definition task_tcb_init_publication_tail_storage sg args current slot image : Assertion :=
  task_slot_storage_rep sg slot
    (task_tcb_init_linked_layout_image sg current.(TskState).(tcbListHead)
      (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
        sg.(osKernelConfig).(cfgTaskProfile) args image)) **
  task_tcb_init_used_with_head_prev sg current slot **
  sg.(g_OSTCBList) # Ptr |-> task_tcb_init_active_head sg current **
  sg.(g_OSTaskCtr) # UChar |-> task_tcb_init_count current **
  sg.(g_OSRdyGrp) # UChar |-> task_tcb_init_ready_group current **
  UCharArray.full sg.(g_OSRdyTbl) 8 (task_tcb_init_ready_rows current) **
  PtrArray.full sg.(g_OSTCBPrioTbl) 64 (task_tcb_init_priority_table sg current) **
  task_tcb_init_publication_other sg current.

Lemma task_tcb_init_publication_cells_store_execution :
  forall sg priority pointer head group row count entry (frame : Assertion) before,
  0 <= pointer < 4294967296 ->
  0 <= Z.lor group (Z.shiftl 1 (priority / 8)) < 256 ->
  0 <= Z.lor row (Z.shiftl 1 (priority mod 8)) < 256 ->
  0 <= count + 1 < 256 ->
  (task_tcb_init_publication_cells sg priority pointer head group row count entry ** frame) before ->
  exists after,
    task_tcb_init_publication_tail_fragment sg priority pointer before after /\
    (task_tcb_init_publication_cells sg priority pointer pointer
      (Z.lor group (Z.shiftl 1 (priority / 8)))
      (Z.lor row (Z.shiftl 1 (priority mod 8))) (count + 1) pointer ** frame) after.
Proof.
  intros sg priority pointer head group row count entry frame before Hpointer Hgroup Hrow Hcount Hbefore.
  assert (Hhead : task_tcb_init_publication_cells sg priority pointer head group row count entry ** frame |--
    sg.(g_OSTCBList) # Ptr |->_ **
    (sg.(g_OSRdyGrp) # UChar |-> group **
     (sg.(g_OSRdyTbl) + priority / 8 * sizeof(UCHAR)) # UChar |-> row **
     sg.(g_OSTaskCtr) # UChar |-> count **
     (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |-> entry **
     (tcb_field_address pointer TCBY) # UChar |-> (priority / 8) **
     (tcb_field_address pointer TCBBitY) # UChar |-> (Z.shiftl 1 (priority / 8)) **
     (tcb_field_address pointer TCBBitX) # UChar |-> (Z.shiftl 1 (priority mod 8)) ** frame)).
  { unfold task_tcb_init_publication_cells.
    sep_apply_l_atomic (store_ptr_undef_store_ptr sg.(g_OSTCBList) head); entailer!. }
  destruct (framed_pointer_store_execution _ _ _ before Hpointer (Hhead before Hbefore))
    as [linked [Hlink Hlinked]].
  assert (Hlinked_cells : (task_tcb_init_publication_cells sg priority pointer pointer group row count entry ** frame) linked).
  { match type of Hlinked with ?P linked =>
      assert (Hpack : P |-- task_tcb_init_publication_cells sg priority pointer pointer group row count entry ** frame)
        by (unfold task_tcb_init_publication_cells; entailer!) end.
    exact (Hpack linked Hlinked). }
  destruct (task_tcb_init_publication_cells_reads _ _ _ _ _ _ _ _ _ _ Hlinked_cells)
    as [Hgroup_load [_ [_ [_ [Hbity _]]]]].
  assert (Hgroup_focus : task_tcb_init_publication_cells sg priority pointer pointer group row count entry ** frame |--
    sg.(g_OSRdyGrp) # UChar |-> group **
    (sg.(g_OSTCBList) # Ptr |-> pointer **
     (sg.(g_OSRdyTbl) + priority / 8 * sizeof(UCHAR)) # UChar |-> row **
     sg.(g_OSTaskCtr) # UChar |-> count **
     (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |-> entry **
     (tcb_field_address pointer TCBY) # UChar |-> (priority / 8) **
     (tcb_field_address pointer TCBBitY) # UChar |-> (Z.shiftl 1 (priority / 8)) **
     (tcb_field_address pointer TCBBitX) # UChar |-> (Z.shiftl 1 (priority mod 8)) ** frame))
    by (unfold task_tcb_init_publication_cells; entailer!).
  destruct (kernel_heap_framed_uchar_store _ _ _ _ linked Hgroup (Hgroup_focus linked Hlinked_cells))
    as [grouped [Hgroup_store Hgrouped]].
  assert (Hgrouped_cells : (task_tcb_init_publication_cells sg priority pointer pointer
    (Z.lor group (Z.shiftl 1 (priority / 8))) row count entry ** frame) grouped).
  { match type of Hgrouped with ?P grouped =>
      assert (Hpack : P |-- task_tcb_init_publication_cells sg priority pointer pointer
        (Z.lor group (Z.shiftl 1 (priority / 8))) row count entry ** frame)
        by (unfold task_tcb_init_publication_cells; entailer!) end.
    exact (Hpack grouped Hgrouped). }
  destruct (task_tcb_init_publication_cells_reads _ _ _ _ _ _ _ _ _ _ Hgrouped_cells)
    as [_ [Hrow_load [_ [Hy [_ Hbitx]]]]].
  assert (Hrow_focus : task_tcb_init_publication_cells sg priority pointer pointer
      (Z.lor group (Z.shiftl 1 (priority / 8))) row count entry ** frame |--
    (sg.(g_OSRdyTbl) + priority / 8 * sizeof(UCHAR)) # UChar |-> row **
    (sg.(g_OSTCBList) # Ptr |-> pointer **
     sg.(g_OSRdyGrp) # UChar |-> (Z.lor group (Z.shiftl 1 (priority / 8))) **
     sg.(g_OSTaskCtr) # UChar |-> count **
     (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |-> entry **
     (tcb_field_address pointer TCBY) # UChar |-> (priority / 8) **
     (tcb_field_address pointer TCBBitY) # UChar |-> (Z.shiftl 1 (priority / 8)) **
     (tcb_field_address pointer TCBBitX) # UChar |-> (Z.shiftl 1 (priority mod 8)) ** frame))
    by (unfold task_tcb_init_publication_cells; entailer!).
  destruct (kernel_heap_framed_uchar_store _ _ _ _ grouped Hrow (Hrow_focus grouped Hgrouped_cells))
    as [readied [Hrow_store Hreadied]].
  assert (Hreadied_cells : (task_tcb_init_publication_cells sg priority pointer pointer
    (Z.lor group (Z.shiftl 1 (priority / 8)))
    (Z.lor row (Z.shiftl 1 (priority mod 8))) count entry ** frame) readied).
  { match type of Hreadied with ?P readied =>
      assert (Hpack : P |-- task_tcb_init_publication_cells sg priority pointer pointer
        (Z.lor group (Z.shiftl 1 (priority / 8)))
        (Z.lor row (Z.shiftl 1 (priority mod 8))) count entry ** frame)
        by (unfold task_tcb_init_publication_cells; entailer!) end.
    exact (Hpack readied Hreadied). }
  destruct (task_tcb_init_publication_cells_reads _ _ _ _ _ _ _ _ _ _ Hreadied_cells)
    as [_ [_ [Hcount_load _]]].
  assert (Hcount_focus : task_tcb_init_publication_cells sg priority pointer pointer
      (Z.lor group (Z.shiftl 1 (priority / 8)))
      (Z.lor row (Z.shiftl 1 (priority mod 8))) count entry ** frame |--
    sg.(g_OSTaskCtr) # UChar |-> count **
    (sg.(g_OSTCBList) # Ptr |-> pointer **
     sg.(g_OSRdyGrp) # UChar |-> (Z.lor group (Z.shiftl 1 (priority / 8))) **
     (sg.(g_OSRdyTbl) + priority / 8 * sizeof(UCHAR)) # UChar |->
       (Z.lor row (Z.shiftl 1 (priority mod 8))) **
     (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |-> entry **
     (tcb_field_address pointer TCBY) # UChar |-> (priority / 8) **
     (tcb_field_address pointer TCBBitY) # UChar |-> (Z.shiftl 1 (priority / 8)) **
     (tcb_field_address pointer TCBBitX) # UChar |-> (Z.shiftl 1 (priority mod 8)) ** frame))
    by (unfold task_tcb_init_publication_cells; entailer!).
  destruct (kernel_heap_framed_uchar_store _ _ _ _ readied Hcount (Hcount_focus readied Hreadied_cells))
    as [counted [Hcount_store Hcounted]].
  assert (Htable_focus :
    sg.(g_OSTaskCtr) # UChar |-> (count + 1) **
    (sg.(g_OSTCBList) # Ptr |-> pointer **
     sg.(g_OSRdyGrp) # UChar |-> (Z.lor group (Z.shiftl 1 (priority / 8))) **
     (sg.(g_OSRdyTbl) + priority / 8 * sizeof(UCHAR)) # UChar |->
       (Z.lor row (Z.shiftl 1 (priority mod 8))) **
     (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |-> entry **
     (tcb_field_address pointer TCBY) # UChar |-> (priority / 8) **
     (tcb_field_address pointer TCBBitY) # UChar |-> (Z.shiftl 1 (priority / 8)) **
     (tcb_field_address pointer TCBBitX) # UChar |-> (Z.shiftl 1 (priority mod 8)) ** frame) |--
    (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |->_ **
    (sg.(g_OSTCBList) # Ptr |-> pointer **
     sg.(g_OSRdyGrp) # UChar |-> (Z.lor group (Z.shiftl 1 (priority / 8))) **
     (sg.(g_OSRdyTbl) + priority / 8 * sizeof(UCHAR)) # UChar |->
       (Z.lor row (Z.shiftl 1 (priority mod 8))) **
     sg.(g_OSTaskCtr) # UChar |-> (count + 1) **
     (tcb_field_address pointer TCBY) # UChar |-> (priority / 8) **
     (tcb_field_address pointer TCBBitY) # UChar |-> (Z.shiftl 1 (priority / 8)) **
     (tcb_field_address pointer TCBBitX) # UChar |-> (Z.shiftl 1 (priority mod 8)) ** frame)).
  { sep_apply_l_atomic (store_ptr_undef_store_ptr
      (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) entry); entailer!. }
  destruct (framed_pointer_store_execution _ _ _ counted Hpointer (Htable_focus counted Hcounted))
    as [after [Htable_store Hafter]].
  exists after; split.
  - exists linked, grouped, readied, counted, group, row, count.
    split; [exact Hlink|]. split; [exact Hgroup_load|]. split; [exact Hbity|].
    split; [exact Hgroup_store|]. split; [exact Hy|]. split; [exact Hrow_load|].
    split; [exact Hbitx|]. split; [exact Hrow_store|]. split; [exact Hcount_load|].
    split; assumption.
  - match type of Hafter with ?P after =>
      assert (Hpack : P |-- task_tcb_init_publication_cells sg priority pointer pointer
        (Z.lor group (Z.shiftl 1 (priority / 8)))
        (Z.lor row (Z.shiftl 1 (priority mod 8))) (count + 1) pointer ** frame)
        by (unfold task_tcb_init_publication_cells; entailer!) end.
    exact (Hpack after Hafter).
Qed.

(** The pure allocation identity comes from TCBInit's earlier detach and
    re-acquire.  The pointer bound is the range of the pointer actually
    loaded from the free-list root, retained by that caller protocol.
    Neither premise asserts a destination frame or a future ready state. *)
Lemma task_tcb_init_publication_tail_store_execution :
  forall sg args invocation origin acquired current slot image (frame : Assertion) before,
  UCOS2_state_inv sg current ->
  task_tcb_init_commit_binding args invocation origin acquired current slot ->
  0 <= args.(initPrio) < 64 ->
  0 <= task_slot_addr sg slot < 4294967296 ->
  (task_tcb_init_publication_tail_storage sg args current slot image ** frame) before ->
  exists after,
    task_tcb_init_publication_tail_fragment sg args.(initPrio) (task_slot_addr sg slot) before after /\
    (task_create_publication_storage sg args invocation acquired current slot image ** frame) after.
Proof.
  intros sg args invocation origin acquired current slot image frame before
    Hvalid Hbinding Hpriority Hpointer Hbefore.
  assert (Hy : 0 <= args.(initPrio) / 8 < 8)
    by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]).
  assert (Hx : 0 <= args.(initPrio) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  set (initialized := task_tcb_init_linked_layout_image sg current.(TskState).(tcbListHead)
    (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
      sg.(osKernelConfig).(cfgTaskProfile) args image)).
  pose proof (task_tcb_init_storage_split_ready_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile) (task_slot_addr sg slot) initialized args.(initPrio)) as Hfields.
  assert (Hfield_values : initialized (TCBCommonField TCBY) = Some (args.(initPrio) / 8) /\
    initialized (TCBCommonField TCBBitY) = Some (Z.shiftl 1 (args.(initPrio) / 8)) /\
    initialized (TCBCommonField TCBBitX) = Some (Z.shiftl 1 (args.(initPrio) mod 8))).
  { unfold initialized; destruct sg.(osKernelConfig).(cfgEventMultiEnabled),
      sg.(osKernelConfig).(cfgTaskProfile); repeat split; reflexivity. }
  specialize (Hfields (proj1 Hfield_values) (proj1 (proj2 Hfield_values)) (proj2 (proj2 Hfield_values))).
  set (rest := task_tcb_init_without_ready_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile) (task_slot_addr sg slot) initialized **
    task_tcb_init_used_with_head_prev sg current slot **
    UCharArray.missing_i sg.(g_OSRdyTbl) (args.(initPrio) / 8) 0 8 (task_tcb_init_ready_rows current) **
    PtrArray.missing_i sg.(g_OSTCBPrioTbl) args.(initPrio) 0 64 (task_tcb_init_priority_table sg current) **
    task_tcb_init_publication_other sg current ** frame).
  assert (Hsplit : task_tcb_init_publication_tail_storage sg args current slot image ** frame |--
    task_tcb_init_publication_cells sg args.(initPrio) (task_slot_addr sg slot)
      (task_tcb_init_active_head sg current) (task_tcb_init_ready_group current)
      (Znth (args.(initPrio) / 8) (task_tcb_init_ready_rows current) 0)
      (task_tcb_init_count current)
      (Znth args.(initPrio) (task_tcb_init_priority_table sg current) 0) ** rest).
  { unfold task_tcb_init_publication_tail_storage, task_slot_storage_rep; fold initialized.
    rewrite Hfields.
    sep_apply_l_atomic (UCharArray.full_split_to_missing_i sg.(g_OSRdyTbl)
      (args.(initPrio) / 8) 8 (task_tcb_init_ready_rows current) 0 Hy).
    sep_apply_l_atomic (PtrArray.full_split_to_missing_i sg.(g_OSTCBPrioTbl)
      args.(initPrio) 64 (task_tcb_init_priority_table sg current) 0 Hpriority).
    unfold task_tcb_init_publication_cells, rest; entailer!. }
  pose proof (Hsplit before Hbefore) as Hcells.
  destruct (task_tcb_init_publication_cells_reads _ _ _ _ _ _ _ _ _ _ Hcells)
    as [Hgroup_load [Hrow_load _]].
  assert (Hgroup : 0 <= Z.lor (task_tcb_init_ready_group current)
    (Z.shiftl 1 (args.(initPrio) / 8)) < 256).
  { apply (bitmap_lor_in_range 8); [lia|exact (proj1 Hgroup_load)|].
    apply (bitmap_single_bit_in_range 8); exact Hy. }
  assert (Hrow : 0 <= Z.lor (Znth (args.(initPrio) / 8) (task_tcb_init_ready_rows current) 0)
    (Z.shiftl 1 (args.(initPrio) mod 8)) < 256).
  { apply (bitmap_lor_in_range 8); [lia|exact (proj1 Hrow_load)|].
    apply (bitmap_single_bit_in_range 8); exact Hx. }
  assert (Hcount : 0 <= task_tcb_init_count current + 1 < 256).
  { pose proof (task_count_in_pool_range sg current.(TskState)
      (proj1 Hvalid) (proj1 (proj2 Hvalid))); unfold task_tcb_init_count; lia. }
  destruct (task_tcb_init_publication_cells_store_execution _ _ _ _ _ _ _ _ _ before
    Hpointer Hgroup Hrow Hcount Hcells) as [after [Hrun Hafter]].
  pose proof (task_tcb_init_commit_binding_identity args invocation origin acquired current slot image Hbinding)
    as Hidentity.
  assert (Hnot : ~ In slot current.(SchedState).(readyList)).
  { pose proof (task_commit_identity_private _ _ _ _ Hidentity) as Hprivate.
    destruct (task_private_excludes_public sg current.(TskState) slot
      (proj1 (proj1 (proj2 Hvalid))) Hprivate) as [Hnone _].
    intro Hin.
    destruct (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid)))) slot Hin) as [t [Hget _]].
    congruence. }
  set (published := task_tcb_init_published_state sg args invocation acquired current slot image).
  assert (Hgroup_eq : task_tcb_init_ready_group published =
    Z.lor (task_tcb_init_ready_group current) (Z.shiftl 1 (args.(initPrio) / 8))).
  { exact (proj1 (sched_commit_ready_encodings__publication_and_returns sg current.(TskState)
      current.(SchedState) args.(initPrio) invocation
      (task_tcb_init_commit_node args acquired slot image) Hnot)). }
  assert (Hrows_eq : task_tcb_init_ready_rows published =
    replace_Znth (args.(initPrio) / 8)
      (Z.lor (Znth (args.(initPrio) / 8) (task_tcb_init_ready_rows current) 0)
        (Z.shiftl 1 (args.(initPrio) mod 8))) (task_tcb_init_ready_rows current)).
  { exact (sched_commit_rows_replace_eq__publication_and_returns sg current.(TskState)
      current.(SchedState) args.(initPrio) invocation
      (task_tcb_init_commit_node args acquired slot image) Hnot Hy). }
  assert (Htable_eq : task_tcb_init_priority_table sg published =
    replace_Znth args.(initPrio) (task_slot_addr sg slot) (task_tcb_init_priority_table sg current)).
  { exact (task_commit_priority_table_replace_eq__publication_and_returns sg current.(TskState)
      args.(initPrio) invocation (task_tcb_init_commit_node args acquired slot image) Hpriority). }
  exists after; split; [exact Hrun|].
  match type of Hafter with ?P after =>
    assert (Hmerge : P |-- task_create_publication_storage sg args invocation acquired current slot image ** frame)
  end.
  { unfold task_tcb_init_publication_cells, rest; sepcon_assoc_change.
    pose proof (UCharArray.missing_i_merge_to_full sg.(g_OSRdyTbl) (args.(initPrio) / 8) 8
      (Z.lor (Znth (args.(initPrio) / 8) (task_tcb_init_ready_rows current) 0)
        (Z.shiftl 1 (args.(initPrio) mod 8))) (task_tcb_init_ready_rows current) Hy) as Hrows_merge.
    cbv beta in Hrows_merge.
    sep_apply_l_atomic Hrows_merge.
    pose proof (PtrArray.missing_i_merge_to_full sg.(g_OSTCBPrioTbl) args.(initPrio) 64
      (task_slot_addr sg slot) (task_tcb_init_priority_table sg current) Hpriority) as Htable_merge.
    cbv beta in Htable_merge; rewrite sizeof_ptr.
    unfold ptr_size_Z in Htable_merge; sep_apply_l_atomic Htable_merge.
    unfold task_create_publication_storage; fold published; fold initialized.
    rewrite Hgroup_eq, Hrows_eq, Htable_eq.
    unfold task_slot_storage_rep; rewrite Hfields; entailer!. }
  exact (Hmerge after Hafter).
Qed.
