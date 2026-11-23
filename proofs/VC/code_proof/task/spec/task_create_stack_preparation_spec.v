Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapStorage KernelHeapObservation ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source stores are typed atomic stores.  Their little-endian byte lists
    describe the resulting memory, not additional C interruption points. *)
Definition task_tcb_init_ushort_writes (address value : Z) :=
  byte_list_writes address [value mod 256; (value / 256) mod 256].

Lemma task_tcb_init_ushort_store_execution : forall address value (frame : Assertion) before,
  0 <= value < 65536 -> (address # UShort |->_ ** frame) before ->
  exists after, kernel_heap_execution (task_tcb_init_ushort_writes address value) before after /\
    (address # UShort |-> value ** frame) after.
Proof.
  intros address value frame before Hrange [cell [rest [Hjoin [[Haddress Hcell] Hrest]]]].
  assert (Hsplit : store_2byte_noninit address |-- store_bytes_noninit address 2 ** emp).
  { unfold store_2byte_noninit; cbn [store_bytes_noninit]; entailer!. }
  assert (Hbytes : Forall (fun byte => 0 <= byte < 256)
    [value mod 256; (value / 256) mod 256]).
  { repeat constructor; apply Z.mod_pos_bound; lia. }
  destruct (byte_list_store_execution _ address emp cell Hbytes (Hsplit cell Hcell))
    as [written [Hrun Hwritten]].
  assert (Hvalue : (address # UShort |-> value) written).
  { split; [split; [exact Haddress|lia]|].
    exists (value mod 256), ((value / 256) mod 256); split.
    - change (value mod 65536 = (value mod 256) mod 256 +
        ((value / 256) mod 256) mod 256 * 256).
      rewrite !Z.mod_mod by lia; rewrite (Z.mod_small value 65536 Hrange).
      assert (Hq : 0 <= value / 256 < 256).
      { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
      rewrite (Z.mod_small (value / 256) 256 Hq).
      pose proof (Z.div_mod value 256 ltac:(lia)); lia.
    - assert (Hmerge : byte_list_rep address [value mod 256; (value / 256) mod 256] ** emp |--
        store_byte address (value mod 256) ** store_byte (address + 1) ((value / 256) mod 256)).
      { cbn [byte_list_rep]; entailer!. }
      exact (Hmerge written Hwritten). }
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin) as [after [Hwhole Hfinal]].
  exists after; split; [exact Hwhole|].
  exists written, rest; split; [exact Hfinal|]; split; assumption.
Qed.

Definition task_tcb_init_parameters_in_range (args : TaskTCBInitArgs) : Prop :=
  0 <= args.(initPrio) < 64 /\
  0 <= args.(initStkPtr) < 4294967296 /\ 0 <= args.(initStkBottom) < 4294967296 /\
  0 <= args.(initPublicId) < 65536 /\ 0 <= args.(initStkSize) < 4294967296 /\
  0 <= args.(initExtPtr) < 4294967296 /\ 0 <= args.(initOpt) < 65536 /\
  0 <= args.(initNamePointer) < 4294967296.

Definition task_tcb_init_field_address (multi : bool) (base : Z) (field : TCBLayoutField) : Z :=
  match field with
  | TCBCommonField TCBPadding42 => base + if multi then 50 else 42
  | TCBCommonField TCBPadding43 => base + if multi then 51 else 43
  | TCBCommonField common => tcb_field_address base common
  | TCBEventMultiPtr => &(base # "os_tcb" ->ₛ "OSTCBEventMultiPtr")
  | TCBEventMultiRdy => &(base # "os_tcb" ->ₛ "OSTCBEventMultiRdy")
  | TCBCtxSwCtr => &(base # "os_tcb" ->ₛ "OSTCBCtxSwCtr")
  | TCBCyclesTot => &(base # "os_tcb" ->ₛ "OSTCBCyclesTot")
  | TCBCyclesStart => &(base # "os_tcb" ->ₛ "OSTCBCyclesStart")
  | TCBStkBase => &(base # "os_tcb" ->ₛ "OSTCBStkBase")
  | TCBStkUsed => &(base # "os_tcb" ->ₛ "OSTCBStkUsed")
  end.

Definition task_tcb_init_field_bound field : Z :=
  match tcb_layout_field_width field with
  | 1%nat => 256 | 2%nat => 65536 | _ => 4294967296
  end.

Definition task_tcb_init_field_writes multi base field value :=
  let address := task_tcb_init_field_address multi base field in
  match tcb_layout_field_width field with
  | 1%nat => [(address, value)]
  | 2%nat => task_tcb_init_ushort_writes address value
  | _ => pointer_store_writes address value
  end.

Lemma task_tcb_init_layout_cell_to_undef : forall multi base field old,
  tcb_layout_cell multi base field old |-- tcb_layout_cell multi base field None.
Proof.
  intros multi base [field| | | | | | |] [value|]; try reflexivity;
    try (destruct field); cbn [tcb_layout_cell tcb_cell];
    first [apply store_ptr_undef_store_ptr | apply store_uint_undef_store_uint |
      apply store_ushort_undef_store_ushort | apply store_uchar_undef_store_uchar |
      apply tcb_padding_cell_forget |
      apply UIntArray.full_to_undef_full].
Qed.

Lemma task_tcb_init_uint_single_full : forall address value,
  address # UInt |-> value |-- UIntArray.full address 1 [value].
Proof.
  intros; unfold UIntArray.full, store_array; cbn [store_array_rec].
  unfold StoreUIntAsElement.storeA.
  replace (address + 0 * sizeof(UINT)) with address by lia; entailer!.
Qed.

Lemma task_tcb_init_layout_cell_store_execution :
  forall multi base field value (frame : Assertion) before,
  0 <= value < task_tcb_init_field_bound field ->
  (tcb_layout_cell multi base field None ** frame) before ->
  exists after, kernel_heap_execution (task_tcb_init_field_writes multi base field value) before after /\
    (tcb_layout_cell multi base field (Some value) ** frame) after.
Proof.
  intros multi base field value frame before Hrange Hbefore.
  assert (Hpadding : forall address,
    (tcb_padding_cell address None ** frame) before ->
    (address # UChar |->_ ** frame) before).
  { intros address Hinitialized.
    assert (Hforget : tcb_padding_cell address None ** frame |--
      address # UChar |->_ ** frame).
    { unfold tcb_padding_cell; Intros byte.
      sep_apply_l_atomic (store_uchar_undef_store_uchar address byte); entailer!. }
    exact (Hforget before Hinitialized). }
  destruct field as [field| | | | | | |];
    try (destruct field);
    cbn [tcb_layout_cell tcb_cell task_tcb_init_field_writes task_tcb_init_field_address
      task_tcb_init_field_bound tcb_layout_field_width tcb_field_width] in *;
    try (eapply framed_pointer_store_execution; eassumption);
    try (eapply task_stack_uint_store_execution; eassumption);
    try (eapply task_tcb_init_ushort_store_execution; eassumption);
    try (eapply framed_uchar_noninit_store_execution; eassumption);
    try (eapply framed_uchar_noninit_store_execution;
      [exact Hrange|apply Hpadding; exact Hbefore]).
  assert (Hsplit : UIntArray.undef_full (tcb_field_address base TCBReg0) 1 ** frame |--
    (tcb_field_address base TCBReg0) # UInt |->_ ** frame).
  { sep_apply_l_atomic (task_stack_undef_single_cell (tcb_field_address base TCBReg0)); entailer!. }
  destruct (task_stack_uint_store_execution _ value frame before Hrange (Hsplit before Hbefore))
    as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  assert (Hmerge : (tcb_field_address base TCBReg0) # UInt |-> value ** frame |--
    UIntArray.full (tcb_field_address base TCBReg0) 1 [value] ** frame).
  { sep_apply_l_atomic (task_tcb_init_uint_single_full (tcb_field_address base TCBReg0) value); entailer!. }
  exact (Hmerge after Hafter).
Qed.

Definition task_tcb_init_field_sequence_writes multi base (stores : list (TCBLayoutField * Z)) :=
  flat_map (fun store => task_tcb_init_field_writes multi base (fst store) (snd store)) stores.

Lemma task_tcb_init_field_sequence_execution :
  forall stores multi profile base image (frame : Assertion) before,
  Forall (fun store => In (fst store) (tcb_configured_fields multi profile) /\
    0 <= snd store < task_tcb_init_field_bound (fst store)) stores ->
  (tcb_configured_storage_rep multi profile base image ** frame) before ->
  exists after,
    kernel_heap_execution (task_tcb_init_field_sequence_writes multi base stores) before after /\
    (tcb_configured_storage_rep multi profile base
      (fold_left (fun current store => tcb_layout_write current (fst store) (Some (snd store))) stores image) ** frame) after.
Proof.
  induction stores as [|[field value] stores IH]; intros multi profile base image frame before Hstores Hbefore.
  - exists before; split; [split; [constructor|split; reflexivity]|exact Hbefore].
  - inversion Hstores as [|store tail [Hin Hrange] Htail]; subst; cbn [fst snd] in Hin, Hrange.
    assert (Hsplit : tcb_configured_storage_rep multi profile base image ** frame |--
      tcb_layout_cell multi base field None **
      (tcb_configured_storage_without_field multi profile base image field ** frame)).
    { sep_apply_l_atomic (tcb_configured_storage_split_field multi profile base image field Hin).
      sep_apply_l_atomic (task_tcb_init_layout_cell_to_undef multi base field (image field)); entailer!. }
    destruct (task_tcb_init_layout_cell_store_execution multi base field value _ before Hrange
      (Hsplit before Hbefore)) as [middle [Hwrite Hmiddle]].
    assert (Hmerge : tcb_layout_cell multi base field (Some value) **
      (tcb_configured_storage_without_field multi profile base image field ** frame) |--
      tcb_configured_storage_rep multi profile base (tcb_layout_write image field (Some value)) ** frame).
    { sep_apply_l_atomic (tcb_configured_storage_merge_updated_field multi profile base image field (Some value) Hin).
      entailer!. }
    destruct (IH multi profile base (tcb_layout_write image field (Some value)) frame middle Htail
      (Hmerge middle Hmiddle)) as [after [Hrest Hafter]].
    exists after; split; [|exact Hafter].
    cbn [task_tcb_init_field_sequence_writes flat_map fst snd].
    eapply heap_execution_append; eassumption.
Qed.

Lemma task_tcb_init_source_field_ranges : forall multi profile args,
  task_tcb_init_parameters_in_range args ->
  Forall (fun store => In (fst store) (tcb_configured_fields multi profile) /\
    0 <= snd store < task_tcb_init_field_bound (fst store))
    (task_tcb_init_source_layout_stores multi profile args).
Proof.
  intros multi profile args [Hp [Hsp [Hbottom [Hid [Hsize [Hext [Hopt Hname]]]]]]].
  assert (Hy : 0 <= args.(initPrio) / 8 < 8).
  { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
  pose proof (Z.mod_pos_bound args.(initPrio) 8 ltac:(lia)) as Hx.
  pose proof (shiftl_one_byte_in_range__private_initialization _ Hy) as Hby.
  pose proof (shiftl_one_byte_in_range__private_initialization _ Hx) as Hbx.
  apply Forall_forall; intros [field value] Hin.
  destruct multi, profile;
    cbn [task_tcb_init_source_layout_stores task_tcb_init_source_stores firstn skipn map app In fst snd] in Hin;
    repeat match type of Hin with _ \/ _ => destruct Hin as [Hin | Hin] end;
    try contradiction; inversion Hin; subst; clear Hin;
    cbn [fst snd task_tcb_init_field_bound tcb_layout_field_width tcb_field_width];
    (split; [unfold tcb_configured_fields, tcb_profile_fields, tcb_fields; simpl; tauto|lia]).
Qed.

Lemma task_tcb_init_private_initialization_execution :
  forall sg args slot image (frame : Assertion) before,
  task_tcb_init_parameters_in_range args ->
  (task_slot_storage_rep sg slot image ** frame) before ->
  exists after,
    kernel_heap_execution
      (task_tcb_init_field_sequence_writes sg.(osKernelConfig).(cfgEventMultiEnabled)
        (task_slot_addr sg slot)
        (task_tcb_init_source_layout_stores sg.(osKernelConfig).(cfgEventMultiEnabled)
          sg.(osKernelConfig).(cfgTaskProfile) args)) before after /\
    (task_slot_storage_rep sg slot
      (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
        sg.(osKernelConfig).(cfgTaskProfile) args image) ** frame) after.
Proof.
  intros sg args slot image frame before Hrange Hbefore.
  destruct (task_tcb_init_field_sequence_execution _ _ _ _ image frame before
    (task_tcb_init_source_field_ranges _ _ args Hrange) Hbefore) as [after [Hrun Hafter]].
  rewrite task_tcb_init_source_layout_stores_image_eq in Hafter.
  exists after; split; assumption.
Qed.

Definition task_tcb_init_free_pop_fragment (sg : StableGlobVars)
  (pointer next : Z) (before after : model) : Prop :=
  pointer_load sg.(g_OSTCBFreeList) pointer before /\ pointer <> 0 /\
  pointer_load (tcb_field_address pointer TCBNext) next before /\
  kernel_heap_execution (pointer_store_writes sg.(g_OSTCBFreeList) next) before after.

Lemma task_tcb_init_free_pop_execution :
  forall sg args invocation origin acquired slot rest (frame : Assertion) before,
  task_tcb_init_entry sg args invocation origin acquired ->
  acquired.(TskState).(unUsedTaskStates) = slot :: rest ->
  (UCOS2_inv sg acquired ** frame) before ->
  exists image after,
    task_tcb_init_detach_observation args invocation origin acquired slot rest image /\
    task_tcb_init_free_pop_fragment sg (task_slot_addr sg slot)
      (task_tcb_init_free_next sg rest) before after /\
    (UCOS2_inv sg (task_tcb_init_detached_state args invocation origin acquired slot rest image) **
      task_slot_storage_rep sg slot image ** frame) after.
Proof.
  intros sg args invocation origin acquired slot rest frame before Hentry Hhead Hbefore.
  pose proof (proj1 Hentry) as Hvalid.
  pose proof (proj1 (proj2 Hvalid)) as Htasks.
  assert (Hlinks : task_free_links sg acquired.(TskState).(taskLifecycle).(taskFreeStorage)
    acquired.(TskState).(unUsedTaskStates)) by (unfold task_in_range in Htasks; tauto).
  rewrite Hhead in Hlinks; destruct Hlinks as [image [Himage [Hnext Htail]]].
  assert (Hdetach : task_tcb_init_detach_observation args invocation origin acquired slot rest image).
  { unfold task_tcb_init_detach_observation, task_detach_guard.
    split; [exact Hhead|]; split; [exact (proj1 (proj2 (proj2 (proj2 Hentry))))|].
    split; [reflexivity|exact Himage]. }
  assert (Hslot : task_slot_in_range sg slot).
  { apply (proj2 (proj1 (proj1 Htasks) slot)); right; left; rewrite Hhead; left; reflexivity. }
  pose proof (task_slot_addr_positive__publication_and_returns sg slot (proj1 (proj1 Hvalid)) Hslot) as Hpositive.
  assert (Hsplit : UCOS2_inv sg acquired ** frame |--
    sg.(g_OSTCBFreeList) # Ptr |-> task_slot_addr sg slot **
    (task_slot_storage_rep sg slot image ** task_tcb_init_public_without_free_head sg acquired rest ** frame)).
  { unfold UCOS2_inv, UCOS2_raw_rep, task_shared_rep; Intros.
    sep_apply_l_atomic (task_public_storage_split_free_head sg acquired.(TskState) slot rest Hhead).
    Intros found. assert (found = image) by congruence; subst found.
    unfold task_tcb_init_public_without_free_head, UCOS2_raw_rep_missing_task_storage_sched; entailer!. }
  pose proof (Hsplit before Hbefore) as Howned.
  pose proof (framed_pointer_store_load _ _ _ before Howned) as Hroot_read.
  assert (Hnext_focus : sg.(g_OSTCBFreeList) # Ptr |-> task_slot_addr sg slot **
      (task_slot_storage_rep sg slot image ** task_tcb_init_public_without_free_head sg acquired rest ** frame) |--
    (tcb_field_address (task_slot_addr sg slot) TCBNext) # Ptr |-> task_tcb_init_free_next sg rest ** TT).
  { unfold task_slot_storage_rep.
    sep_apply_l_atomic (tcb_configured_storage_split_field
      sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
      (task_slot_addr sg slot) image (TCBCommonField TCBNext)
      (tcb_configured_common_field_in sg.(osKernelConfig).(cfgEventMultiEnabled)
        sg.(osKernelConfig).(cfgTaskProfile) TCBNext)).
    rewrite Hnext; cbn [tcb_layout_cell tcb_cell]; unfold task_tcb_init_free_next; entailer!; intros ? ?; exact I. }
  pose proof (framed_pointer_store_load _ _ _ before (Hnext_focus before Howned)) as Hnext_read.
  assert (Herase : sg.(g_OSTCBFreeList) # Ptr |-> task_slot_addr sg slot **
      (task_slot_storage_rep sg slot image ** task_tcb_init_public_without_free_head sg acquired rest ** frame) |--
    sg.(g_OSTCBFreeList) # Ptr |->_ **
      (task_slot_storage_rep sg slot image ** task_tcb_init_public_without_free_head sg acquired rest ** frame)).
  { sep_apply_l_atomic (store_ptr_undef_store_ptr sg.(g_OSTCBFreeList) (task_slot_addr sg slot)); entailer!. }
  destruct (framed_pointer_store_execution _ _ _ before (proj1 Hnext_read) (Herase before Howned))
    as [after [Hwrite Hafter]].
  exists image, after; split; [exact Hdetach|].
  split; [unfold task_tcb_init_free_pop_fragment; split; [exact Hroot_read|];
    split; [lia|]; split; assumption|].
  assert (Hmerge : sg.(g_OSTCBFreeList) # Ptr |-> task_tcb_init_free_next sg rest **
      (task_slot_storage_rep sg slot image ** task_tcb_init_public_without_free_head sg acquired rest ** frame) |--
    UCOS2_inv sg (task_tcb_init_detached_state args invocation origin acquired slot rest image) **
      task_slot_storage_rep sg slot image ** frame).
  { sep_apply_l_atomic (task_tcb_init_detach_merge_invariant sg args invocation origin acquired slot rest image Hentry Hdetach).
    entailer!. }
  exact (Hmerge after Hafter).
Qed.

Definition task_tcb_init_link_globals sg current : Assertion :=
  sg.(g_OSTCBList) # Ptr |-> task_tcb_init_active_head sg current **
  sg.(g_OSTaskCtr) # UChar |-> task_tcb_init_count current **
  sg.(g_OSRdyGrp) # UChar |-> task_tcb_init_ready_group current **
  UCharArray.full sg.(g_OSRdyTbl) 8 (task_tcb_init_ready_rows current) **
  PtrArray.full sg.(g_OSTCBPrioTbl) 64 (task_tcb_init_priority_table sg current) **
  task_tcb_init_publication_other sg current.

(** The head is loaded for Next, then read again for the conditional
    old-head Prev assignment. No memory operation lies between the guard
    and its repeated evaluation as the assignment's lvalue base. *)
Definition task_tcb_init_link_fragment sg pointer head (before after : model) : Prop :=
  exists linked,
    pointer_load sg.(g_OSTCBList) head before /\
    kernel_heap_execution
      (pointer_store_writes (tcb_field_address pointer TCBNext) head ++
       pointer_store_writes (tcb_field_address pointer TCBPrev) 0) before linked /\
    pointer_load sg.(g_OSTCBList) head linked /\
    ((head = 0 /\ after = linked) \/
     (head <> 0 /\ kernel_heap_execution
       (pointer_store_writes (tcb_field_address head TCBPrev) pointer) linked after)).

Lemma task_tcb_init_links_execution :
  forall sg args current slot image (frame : Assertion) before,
  UCOS2_state_inv sg current -> 0 <= task_slot_addr sg slot < 4294967296 ->
  (task_slot_storage_rep sg slot
      (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
        sg.(osKernelConfig).(cfgTaskProfile) args image) **
    UCOS2_inv sg current ** frame) before ->
  exists after,
    task_tcb_init_link_fragment sg (task_slot_addr sg slot)
      (task_tcb_init_active_head sg current) before after /\
    (task_tcb_init_publication_tail_storage sg args current slot image ** frame) after.
Proof.
  intros sg args current slot image frame before Hvalid Hpointer Hbefore.
  set (initialized := task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile) args image).
  set (head := task_tcb_init_active_head sg current).
  assert (Hsplit : task_slot_storage_rep sg slot initialized ** UCOS2_inv sg current ** frame |--
    task_slot_storage_rep sg slot initialized **
      (task_tcb_init_used_storage sg current ** task_tcb_init_link_globals sg current ** frame)).
  { unfold UCOS2_inv; Intros. rewrite task_tcb_init_raw_split_publication.
    unfold task_tcb_init_link_globals; entailer!. }
  pose proof (Hsplit before Hbefore) as Howned.
  assert (Hread_focus : forall contents,
    task_slot_storage_rep sg slot contents **
      (task_tcb_init_used_storage sg current ** task_tcb_init_link_globals sg current ** frame) |--
    sg.(g_OSTCBList) # Ptr |-> head ** TT).
  { intros; unfold task_tcb_init_link_globals, head; entailer!; intros ? ?; exact I. }
  pose proof (framed_pointer_store_load _ _ _ before (Hread_focus initialized before Howned)) as Hread.
  assert (Hstores : Forall (fun store =>
    In (fst store) (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)) /\
      0 <= snd store < task_tcb_init_field_bound (fst store))
    [(TCBCommonField TCBNext, head); (TCBCommonField TCBPrev, 0)]).
  { constructor; [split; [apply tcb_configured_common_field_in|exact (proj1 Hread)]|].
    constructor; [split; [apply tcb_configured_common_field_in|cbn; lia]|constructor]. }
  destruct (task_tcb_init_field_sequence_execution _ _ _ _ initialized _ before Hstores Howned)
    as [linked [Hlinks Hlinked]].
  assert (Hrun : kernel_heap_execution
    (pointer_store_writes (tcb_field_address (task_slot_addr sg slot) TCBNext) head ++
     pointer_store_writes (tcb_field_address (task_slot_addr sg slot) TCBPrev) 0) before linked).
  { cbn [task_tcb_init_field_sequence_writes flat_map task_tcb_init_field_writes
      task_tcb_init_field_address tcb_layout_field_width tcb_field_width fst snd] in Hlinks.
    rewrite app_nil_r in Hlinks; exact Hlinks. }
  change ((task_slot_storage_rep sg slot
      (task_tcb_init_linked_layout_image sg current.(TskState).(tcbListHead) initialized) **
      (task_tcb_init_used_storage sg current ** task_tcb_init_link_globals sg current ** frame)) linked) in Hlinked.
  pose proof (framed_pointer_store_load _ _ _ linked
    (Hread_focus _ linked Hlinked)) as Hguard.
  destruct (Z.eq_dec head 0) as [Hzero | Hnonzero].
  - exists linked; split.
    + exists linked; split; [exact Hread|]; split; [exact Hrun|]; split; [exact Hguard|].
      left; split; [exact Hzero|reflexivity].
    + assert (Hnone : current.(TskState).(tcbListHead) = None).
      { eapply task_tcb_init_active_head_zero__publication_and_returns; eassumption. }
      assert (Hmap : task_tcb_init_head_updated_map current slot = current.(TskState).(inUsedTaskStates)).
      { apply functional_extensionality; intro tid; unfold task_tcb_init_head_updated_map; rewrite Hnone.
        destruct (current.(TskState).(inUsedTaskStates) tid); reflexivity. }
      assert (Hmerge : task_slot_storage_rep sg slot
          (task_tcb_init_linked_layout_image sg current.(TskState).(tcbListHead) initialized) **
          (task_tcb_init_used_storage sg current ** task_tcb_init_link_globals sg current ** frame) |--
        task_tcb_init_publication_tail_storage sg args current slot image ** frame).
      { unfold task_tcb_init_publication_tail_storage, task_tcb_init_link_globals,
          task_tcb_init_used_with_head_prev, task_tcb_init_used_storage.
        rewrite Hmap; unfold initialized; entailer!. }
      exact (Hmerge linked Hlinked).
  - set (node := task_slot_storage_rep sg slot
      (task_tcb_init_linked_layout_image sg current.(TskState).(tcbListHead) initialized)).
    assert (Hfocus : node **
        (task_tcb_init_used_storage sg current ** task_tcb_init_link_globals sg current ** frame) |--
      (tcb_field_address head TCBPrev) # Ptr |->_ **
        (task_tcb_init_used_without_head_prev sg current ** node **
         task_tcb_init_link_globals sg current ** frame)).
    { sep_apply_l_atomic (task_tcb_init_used_split_head_prev__publication_and_returns sg current Hvalid Hnonzero).
      Intros previous; cbn [tcb_cell]. fold head.
      sep_apply_l_atomic (store_ptr_undef_store_ptr (tcb_field_address head TCBPrev) previous); entailer!. }
    destruct (framed_pointer_store_execution _ _ _ linked Hpointer (Hfocus linked Hlinked))
      as [after [Hwrite Hafter]].
    exists after; split.
    + exists linked; split; [exact Hread|]; split; [exact Hrun|]; split; [exact Hguard|].
      right; split; assumption.
    + assert (Hmerge : (tcb_field_address head TCBPrev) # Ptr |-> task_slot_addr sg slot **
          (task_tcb_init_used_without_head_prev sg current ** node **
           task_tcb_init_link_globals sg current ** frame) |--
        task_tcb_init_publication_tail_storage sg args current slot image ** frame).
      { change (tcb_cell (task_tcb_init_active_head sg current) TCBPrev (Some (task_slot_addr sg slot)) **
          (task_tcb_init_used_without_head_prev sg current ** node **
           task_tcb_init_link_globals sg current ** frame) |--
          task_tcb_init_publication_tail_storage sg args current slot image ** frame).
        sep_apply_l_atomic (task_tcb_init_used_merge_head_prev__publication_and_returns sg current slot).
        unfold task_tcb_init_publication_tail_storage, node, initialized, task_tcb_init_link_globals; entailer!. }
      exact (Hmerge after Hafter).
Qed.

(** Heap projection of the two enabled dispatches to the selected official
    [(void)ptcb] App bodies, in the branch with no intervening interrupt.
    This is NOT the semantics of a general enabled-IRQ call interval.
    Source tokens are bound by config/task-native-v2.93.01 and the current
    prepared-source diagnostic; neither wrapper dispatch is erased. *)
Definition task_tcb_init_empty_hooks_uninterrupted (before after : model) : Prop :=
  exists between,
    kernel_heap_execution [] before between /\ kernel_heap_execution [] between after.

Definition task_tcb_init_preparation_fragment sg args pointer next head (before after : model) : Prop :=
  exists detached initialized hooked,
    task_tcb_init_free_pop_fragment sg pointer next before detached /\
    kernel_heap_execution
      (task_tcb_init_field_sequence_writes sg.(osKernelConfig).(cfgEventMultiEnabled) pointer
        (task_tcb_init_source_layout_stores sg.(osKernelConfig).(cfgEventMultiEnabled)
          sg.(osKernelConfig).(cfgTaskProfile) args)) detached initialized /\
    task_tcb_init_empty_hooks_uninterrupted initialized hooked /\
    task_tcb_init_link_fragment sg pointer head hooked after.

Lemma task_tcb_init_preparation_execution :
  forall sg args invocation origin acquired slot rest (frame : Assertion) before,
  task_tcb_init_entry sg args invocation origin acquired ->
  task_tcb_init_parameters_in_range args ->
  acquired.(TskState).(unUsedTaskStates) = slot :: rest ->
  (UCOS2_inv sg acquired ** frame) before ->
  exists image after,
    task_tcb_init_detach_observation args invocation origin acquired slot rest image /\
    task_tcb_init_preparation_fragment sg args (task_slot_addr sg slot)
      (task_tcb_init_free_next sg rest) (task_tcb_init_active_head sg acquired) before after /\
    (task_tcb_init_publication_tail_storage sg args
       (task_tcb_init_detached_state args invocation origin acquired slot rest image) slot image ** frame) after.
Proof.
  intros sg args invocation origin acquired slot rest frame before Hentry Hrange Hhead Hbefore.
  destruct (task_tcb_init_free_pop_execution sg args invocation origin acquired slot rest frame before
    Hentry Hhead Hbefore) as [image [detached [Hdetach [Hpop Hdetached]]]].
  set (current := task_tcb_init_detached_state args invocation origin acquired slot rest image).
  assert (Hfocus : UCOS2_inv sg current ** task_slot_storage_rep sg slot image ** frame |--
    task_slot_storage_rep sg slot image ** (UCOS2_inv sg current ** frame)) by entailer!.
  destruct (task_tcb_init_private_initialization_execution sg args slot image _ detached Hrange
    (Hfocus detached Hdetached)) as [initialized [Hinit Hinitialized]].
  assert (Hlinks_input : task_slot_storage_rep sg slot
      (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
        sg.(osKernelConfig).(cfgTaskProfile) args image) ** (UCOS2_inv sg current ** frame) |--
    task_slot_storage_rep sg slot
      (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
        sg.(osKernelConfig).(cfgTaskProfile) args image) ** UCOS2_inv sg current ** frame) by entailer!.
  pose proof (task_tcb_init_detach_preserves_validity sg args invocation origin acquired slot rest image Hentry Hdetach)
    as Hvalid.
  destruct (task_tcb_init_links_execution sg args current slot image frame initialized Hvalid
    (proj1 (proj1 Hpop)) (Hlinks_input initialized Hinitialized)) as [after [Hlink Hafter]].
  exists image, after; split; [exact Hdetach|]; split; [|exact Hafter].
  exists detached, initialized, initialized.
  split; [exact Hpop|]; split; [exact Hinit|]; split; [|exact Hlink].
  exists initialized; split; (split; [constructor|split; reflexivity]).
Qed.

Definition task_create_stack_reserve_fragment sg priority (before after : model) : Prop :=
  uchar_load sg.(g_OSIntNesting) 0 before /\
  pointer_load (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) 0 before /\
  kernel_heap_execution
    (pointer_store_writes (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) 1) before after.

Lemma task_create_stack_reserved_entry : forall sg args name call initial,
  task_create_stack_entry sg args name call initial ->
  task_priority_in_range sg args.(createPriority) ->
  initial.(TskState).(prioTbl) args.(createPriority) = PTFree ->
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args name)
    call.(os_sched_call_invocation) call.(os_sched_call_origin)
    (task_create_stack_reserved args call initial).
Proof.
  intros sg args name call initial [Hvalid [Hactive [Hempty Hname]]] Hpriority Hfree.
  assert (Hguard : task_reserve_guard sg initial.(TskState) args.(createPriority)
    call.(os_sched_call_invocation) call.(os_sched_call_origin)).
  { unfold task_reserve_guard, task_invocation_active in *; tauto. }
  pose proof (UCOS2_task_reserve_preserves_validity sg initial args.(createPriority)
    call.(os_sched_call_invocation) call.(os_sched_call_origin) Hvalid Hguard) as Hvalid_after.
  unfold task_tcb_init_entry, task_tcb_init_pending.
  assert (Hprio : (task_tcb_init_stack_call_args args name).(initPrio) = args.(createPriority)).
  { unfold task_tcb_init_stack_call_args, task_create_tcb_args; destruct args.(createExtension); reflexivity. }
  rewrite Hprio; split; [exact Hvalid_after|]; split; [exact Hpriority|]; split; [exact Hactive|].
  split; [|exact Hname].
  cbn [task_create_stack_reserved replace_TskS TskState task_reserve
    task_lifecycle_set_reservation taskLifecycle taskReservations].
  destruct (Z.eq_dec args.(createPriority) args.(createPriority)); [reflexivity|contradiction].
Qed.

Lemma task_create_stack_reserve_execution :
  forall sg args name call initial (frame : Assertion) before,
  task_create_stack_entry sg args name call initial ->
  task_priority_in_range sg args.(createPriority) ->
  initial.(IntrState).(intNesting) = 0 ->
  initial.(TskState).(prioTbl) args.(createPriority) = PTFree ->
  (UCOS2_inv sg initial ** frame) before ->
  exists after,
    task_create_stack_reserve_fragment sg args.(createPriority) before after /\
    (UCOS2_inv sg (task_create_stack_reserved args call initial) ** frame) after.
Proof.
  intros sg args name call initial frame before Hentry Hpriority Hnest Hfree Hbefore.
  pose proof (proj1 Hentry) as Hvalid.
  assert (Hp : 0 <= args.(createPriority) < 64).
  { pose proof (proj1 (proj1 Hvalid)) as Hstable.
    unfold valid_stable_glob_vars in Hstable; unfold task_priority_in_range in Hpriority; intuition lia. }
  assert (Hnest_focus : UCOS2_inv sg initial ** frame |-- sg.(g_OSIntNesting) # UChar |-> 0 ** TT).
  { rewrite task_create_stack_inv_split_nesting. unfold task_create_stack_nesting; rewrite Hnest.
    entailer!; intros ? ?; exact I. }
  pose proof (framed_uchar_store_load _ _ _ before (Hnest_focus before Hbefore)) as Hnest_read.
  assert (Hsplit : UCOS2_inv sg initial ** frame |--
    (sg.(g_OSTCBPrioTbl) + args.(createPriority) * sizeof(PTR)) # Ptr |-> 0 **
    (store_prio_tbl_missing_i sg initial.(TskState).(prioTbl) args.(createPriority) **
     UCOS2_raw_rep_missing_priority_table sg initial ** frame)).
  { sep_apply_l_atomic (UCOS2_inv_split_priority_cell sg initial args.(createPriority) Hp).
    Intros; rewrite Hfree; cbn [prio_tbl_entry_to_addr]; entailer!. }
  pose proof (Hsplit before Hbefore) as Howned.
  pose proof (framed_pointer_store_load _ _ _ before Howned) as Hpriority_read.
  assert (Herase : (sg.(g_OSTCBPrioTbl) + args.(createPriority) * sizeof(PTR)) # Ptr |-> 0 **
      (store_prio_tbl_missing_i sg initial.(TskState).(prioTbl) args.(createPriority) **
       UCOS2_raw_rep_missing_priority_table sg initial ** frame) |--
    (sg.(g_OSTCBPrioTbl) + args.(createPriority) * sizeof(PTR)) # Ptr |->_ **
      (store_prio_tbl_missing_i sg initial.(TskState).(prioTbl) args.(createPriority) **
       UCOS2_raw_rep_missing_priority_table sg initial ** frame)).
  { sep_apply_l_atomic (store_ptr_undef_store_ptr
      (sg.(g_OSTCBPrioTbl) + args.(createPriority) * sizeof(PTR)) 0); entailer!. }
  destruct (framed_pointer_store_execution _ 1 _ before ltac:(lia) (Herase before Howned))
    as [after [Hwrite Hafter]].
  assert (Hguard : task_reserve_guard sg initial.(TskState) args.(createPriority)
    call.(os_sched_call_invocation) call.(os_sched_call_origin)).
  { destruct Hentry as [_ [Hactive [Hempty _]]].
    unfold task_reserve_guard, task_invocation_active in *; tauto. }
  assert (Hmerge : (sg.(g_OSTCBPrioTbl) + args.(createPriority) * sizeof(PTR)) # Ptr |-> 1 **
      (store_prio_tbl_missing_i sg initial.(TskState).(prioTbl) args.(createPriority) **
       UCOS2_raw_rep_missing_priority_table sg initial ** frame) |--
    UCOS2_inv sg (task_create_stack_reserved args call initial) ** frame).
  { sep_apply_l_atomic (UCOS2_inv_merge_reserved_priority sg initial args.(createPriority)
      call.(os_sched_call_invocation) call.(os_sched_call_origin) Hvalid Hguard).
    unfold task_create_stack_reserved; entailer!. }
  exists after; split; [unfold task_create_stack_reserve_fragment; split; [exact Hnest_read|]; split; assumption|].
  exact (Hmerge after Hafter).
Qed.

(** This input owns the unpublished caller buffer.  The snapshot is an
    index for the existing kernel world, not a new OS ledger or a promised
    poststate.  An external caller/allocator must actually supply these
    bytes; a bare Closed cut cannot manufacture them. *)
Record TaskCreateStackInput : Type := {
  stack_input_region : TaskStackRegion;
  stack_input_args : TaskCreateArgs;
  stack_input_return : Z;
  stack_input_lower : list (option Z);
  stack_input_old_frame : list (option Z);
  stack_input_upper : list (option Z);
  stack_input_name : Z;
  stack_input_call : OsSchedCallContext;
  stack_input_state : UCOS2_Verify_State
}.

Definition task_create_stack_input_args input :=
  task_tcb_init_stack_call_args input.(stack_input_args) input.(stack_input_name).

Definition task_create_stack_input_acquired input :=
  task_create_stack_reserved input.(stack_input_args) input.(stack_input_call) input.(stack_input_state).

Definition task_create_stack_input_detached input slot rest image :=
  task_tcb_init_detached_state (task_create_stack_input_args input)
    input.(stack_input_call).(os_sched_call_invocation) input.(stack_input_call).(os_sched_call_origin)
    (task_create_stack_input_acquired input) slot rest image.

Definition task_create_stack_input_facts sg input : Prop :=
  task_create_stack_entry sg input.(stack_input_args) input.(stack_input_name)
    input.(stack_input_call) input.(stack_input_state) /\
  input.(stack_input_args).(createExtension) = TaskCreateBasic /\
  task_priority_in_range sg input.(stack_input_args).(createPriority) /\
  task_create_stack_buffer_domain input.(stack_input_region) input.(stack_input_args)
    input.(stack_input_return) input.(stack_input_lower) input.(stack_input_old_frame) input.(stack_input_upper) /\
  task_tcb_init_parameters_in_range (task_create_stack_input_args input).

Definition task_create_stack_prepared_publication input slot image : TaskCreateStackPublication :=
  {| stack_publication_region := input.(stack_input_region);
     stack_publication_args := input.(stack_input_args);
     stack_publication_return := input.(stack_input_return);
     stack_publication_lower := input.(stack_input_lower);
     stack_publication_upper := input.(stack_input_upper);
     stack_publication_name := input.(stack_input_name);
     stack_publication_invocation := input.(stack_input_call).(os_sched_call_invocation);
     stack_publication_origin := input.(stack_input_call).(os_sched_call_origin);
     stack_publication_acquired := task_create_stack_input_acquired input;
     stack_publication_slot := slot;
     stack_publication_image := image;
     stack_publication_lease := {| stackLeaseRegion := input.(stack_input_region);
       stackLeaseSlot := slot;
       stackLeaseGeneration := (task_create_stack_input_acquired input).(TskState).(taskLifecycle).(taskNextGeneration) |} |}.

(** Successful basic-Create memory path: guard loads and reservation,
    actual StackInit pushes, then actual TCBInit preparation. Save/Restore
    instructions do not write this C heap in the selected uninterrupted
    branch. Their CPU ownership is not asserted by this heap projection. *)
Definition task_create_stack_preparation_fragment sg input slot rest (before after : model) : Prop :=
  exists reserved initialized,
    task_create_stack_reserve_fragment sg input.(stack_input_args).(createPriority) before reserved /\
    kernel_heap_execution
      (task_stack_init_no_vfp_writes input.(stack_input_args).(createStackTop)
        input.(stack_input_args).(createEntry) input.(stack_input_args).(createArgument)
        input.(stack_input_return)) reserved initialized /\
    task_tcb_init_preparation_fragment sg (task_create_stack_input_args input)
      (task_slot_addr sg slot) (task_tcb_init_free_next sg rest)
      (task_tcb_init_active_head sg (task_create_stack_input_acquired input)) initialized after.

Lemma task_create_stack_preparation_execution :
  forall sg input slot rest (frame : Assertion) before,
  task_create_stack_input_facts sg input ->
  input.(stack_input_state).(IntrState).(intNesting) = 0 ->
  input.(stack_input_state).(TskState).(prioTbl) input.(stack_input_args).(createPriority) = PTFree ->
  input.(stack_input_state).(TskState).(unUsedTaskStates) = slot :: rest ->
  (UCOS2_inv sg input.(stack_input_state) **
    task_stack_storage input.(stack_input_region)
      (input.(stack_input_lower) ++ input.(stack_input_old_frame) ++ input.(stack_input_upper)) ** frame) before ->
  exists image after,
    task_tcb_init_detach_observation (task_create_stack_input_args input)
      input.(stack_input_call).(os_sched_call_invocation) input.(stack_input_call).(os_sched_call_origin)
      (task_create_stack_input_acquired input) slot rest image /\
    task_create_stack_preparation_fragment sg input slot rest before after /\
    (task_tcb_init_publication_tail_storage sg (task_create_stack_input_args input)
       (task_create_stack_input_detached input slot rest image) slot image **
      task_stack_storage input.(stack_input_region)
        (task_create_stack_publication_words (task_create_stack_prepared_publication input slot image)) ** frame) after.
Proof.
  intros sg input slot rest frame before [Hentry [Hbasic [Hpriority [Hbuffer Hparameters]]]] Hnest Hfree Hhead Hbefore.
  destruct Hbuffer as [Hlayout [Hlength [Hentry_pc [Hargument Hreturn]]]].
  set (buffer := task_stack_storage input.(stack_input_region)
    (input.(stack_input_lower) ++ input.(stack_input_old_frame) ++ input.(stack_input_upper))).
  assert (Hfocus : UCOS2_inv sg input.(stack_input_state) ** buffer ** frame |--
    UCOS2_inv sg input.(stack_input_state) ** (buffer ** frame)) by entailer!.
  destruct (task_create_stack_reserve_execution sg input.(stack_input_args) input.(stack_input_name)
    input.(stack_input_call) input.(stack_input_state) _ before Hentry Hpriority Hnest Hfree
    (Hfocus before Hbefore)) as [reserved [Hreserve Hreserved]].
  set (acquired := task_create_stack_input_acquired input).
  assert (Hstack_focus : UCOS2_inv sg acquired ** (buffer ** frame) |--
    buffer ** (UCOS2_inv sg acquired ** frame)) by entailer!.
  destruct (task_create_stack_init_store_execution input.(stack_input_region) input.(stack_input_args)
    input.(stack_input_return) input.(stack_input_lower) input.(stack_input_old_frame) input.(stack_input_upper)
    _ reserved Hlayout Hlength Hentry_pc Hargument Hreturn (Hstack_focus reserved Hreserved))
    as [initialized [Hstack Hinitialized]].
  set (words := task_create_stack_image TaskStackNoVFP input.(stack_input_args) input.(stack_input_return)
    input.(stack_input_lower) input.(stack_input_upper)).
  assert (Hinit_focus : task_stack_storage input.(stack_input_region) words ** (UCOS2_inv sg acquired ** frame) |--
    UCOS2_inv sg acquired ** (task_stack_storage input.(stack_input_region) words ** frame)) by entailer!.
  pose proof (task_create_stack_reserved_entry sg input.(stack_input_args) input.(stack_input_name)
    input.(stack_input_call) input.(stack_input_state) Hentry Hpriority Hfree) as Hacquired.
  destruct (task_tcb_init_preparation_execution sg (task_create_stack_input_args input)
    input.(stack_input_call).(os_sched_call_invocation) input.(stack_input_call).(os_sched_call_origin)
    acquired slot rest _ initialized Hacquired Hparameters Hhead (Hinit_focus initialized Hinitialized))
    as [image [after [Hdetach [Hprepare Hafter]]]].
  exists image, after; split; [exact Hdetach|]; split.
  - exists reserved, initialized; split; [exact Hreserve|]; split; assumption.
  - assert (Hmerge : task_tcb_init_publication_tail_storage sg (task_create_stack_input_args input)
        (task_create_stack_input_detached input slot rest image) slot image **
        (task_stack_storage input.(stack_input_region) words ** frame) |--
      task_tcb_init_publication_tail_storage sg (task_create_stack_input_args input)
        (task_create_stack_input_detached input slot rest image) slot image **
        task_stack_storage input.(stack_input_region)
          (task_create_stack_publication_words (task_create_stack_prepared_publication input slot image)) ** frame).
    { unfold words, task_create_stack_publication_words, task_create_stack_prepared_publication; cbn; entailer!. }
    exact (Hmerge after Hafter).
Qed.

Lemma task_create_stack_prepared_publication_input : forall sg input slot rest image,
  task_create_stack_input_facts sg input ->
  input.(stack_input_state).(TskState).(prioTbl) input.(stack_input_args).(createPriority) = PTFree ->
  task_tcb_init_detach_observation (task_create_stack_input_args input)
    input.(stack_input_call).(os_sched_call_invocation) input.(stack_input_call).(os_sched_call_origin)
    (task_create_stack_input_acquired input) slot rest image ->
  UCOS2_state_inv sg (task_create_stack_input_detached input slot rest image) /\
  task_create_stack_publication_input sg (task_create_stack_prepared_publication input slot image)
    (task_create_stack_input_detached input slot rest image).
Proof.
  intros sg input slot rest image [Hentry [Hbasic [Hpriority [Hbuffer Hparameters]]]] Hfree Hdetach.
  pose proof (task_create_stack_reserved_entry sg input.(stack_input_args) input.(stack_input_name)
    input.(stack_input_call) input.(stack_input_state) Hentry Hpriority Hfree) as Hacquired.
  pose proof (task_tcb_init_detach_preserves_validity _ _ _ _ _ _ _ _ Hacquired Hdetach) as Hvalid.
  split; [exact Hvalid|].
  set (actual := task_create_stack_input_args input).
  set (acquired := task_create_stack_input_acquired input).
  set (current := task_create_stack_input_detached input slot rest image).
  set (allocation := {| privateSlot := slot;
    privateGeneration := acquired.(TskState).(taskLifecycle).(taskNextGeneration); privateStorage := image |}).
  set (entry := {| creationInvocation := input.(stack_input_call).(os_sched_call_invocation);
    creationOrigin := input.(stack_input_call).(os_sched_call_origin); creationAllocation := Some allocation |}).
  assert (Hlookup : current.(TskState).(taskLifecycle).(taskReservations) actual.(initPrio) = Some entry).
  { unfold current, task_create_stack_input_detached, task_tcb_init_detached_state.
    cbn [replace_TskS TskState task_detach_head taskLifecycle taskReservations].
    fold actual acquired. destruct (Z.eq_dec actual.(initPrio) actual.(initPrio)); [reflexivity|contradiction]. }
  assert (Hbinding : task_tcb_init_commit_binding actual input.(stack_input_call).(os_sched_call_invocation)
    input.(stack_input_call).(os_sched_call_origin) acquired current slot).
  { exists entry, allocation; split; [exact Hlookup|]; repeat split; reflexivity. }
  assert (Hcreation : task_stack_creation_binding current.(TskState) actual.(initPrio)
    input.(stack_input_call).(os_sched_call_invocation) input.(stack_input_call).(os_sched_call_origin)
    {| stackLeaseRegion := input.(stack_input_region); stackLeaseSlot := slot;
       stackLeaseGeneration := acquired.(TskState).(taskLifecycle).(taskNextGeneration) |}).
  { exists entry, allocation; split; [exact Hlookup|]; repeat split; reflexivity. }
  pose proof (task_tcb_init_detached_flags_defined _ _ _ _ _ _ _ _ Hacquired Hdetach) as Hflags.
  unfold task_create_stack_publication_input, task_create_stack_prepared_publication,
    task_create_stack_publication_args; cbn.
  fold actual acquired current.
  split; [exact (proj1 Hbuffer)|]; split; [reflexivity|]; split; [exact Hbinding|].
  split; [exact Hcreation|]; split; [exact Hflags|].
  intros Hnames.
  exact (proj2 (proj2 (proj2 (proj2 Hacquired))) Hnames).
Qed.

Definition task_create_stack_input_resources {external platform port}
  (abi : Armv7aContinuationABI external platform port) sg input state : Assertion :=
  coq_prop (state = input.(stack_input_state) /\ task_create_stack_input_facts sg input) &&
  (kernel_client_heap_world abi sg state **
    task_stack_storage input.(stack_input_region)
      (input.(stack_input_lower) ++ input.(stack_input_old_frame) ++ input.(stack_input_upper))).

(** Resource assignment at entry, not a Closed -> Extra transition with
    an arbitrary frame. The caller's actual buffer is visibly consumed. *)
Lemma task_create_stack_input_assign : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg input,
  task_create_stack_input_facts sg input ->
  kernel_client_heap_world abi sg input.(stack_input_state) **
    task_stack_storage input.(stack_input_region)
      (input.(stack_input_lower) ++ input.(stack_input_old_frame) ++ input.(stack_input_upper)) |--
  task_create_stack_input_resources abi sg input input.(stack_input_state).
Proof. intros; unfold task_create_stack_input_resources; entailer!. Qed.

Lemma task_create_stack_input_produces_publication : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg input slot rest (frame : Assertion) before,
  input.(stack_input_state).(IntrState).(intNesting) = 0 ->
  input.(stack_input_state).(TskState).(prioTbl) input.(stack_input_args).(createPriority) = PTFree ->
  input.(stack_input_state).(TskState).(unUsedTaskStates) = slot :: rest ->
  (task_create_stack_input_resources abi sg input input.(stack_input_state) ** frame) before ->
  exists image after,
    task_tcb_init_detach_observation (task_create_stack_input_args input)
      input.(stack_input_call).(os_sched_call_invocation) input.(stack_input_call).(os_sched_call_origin)
      (task_create_stack_input_acquired input) slot rest image /\
    task_create_stack_preparation_fragment sg input slot rest before after /\
    (kernel_client_heap_publication abi sg (task_create_stack_prepared_publication input slot image)
      (task_create_stack_input_detached input slot rest image) ** frame) after.
Proof.
  intros external platform port abi sg input slot rest frame before Hnest Hfree Hhead Hbefore.
  assert (Hsplit : task_create_stack_input_resources abi sg input input.(stack_input_state) ** frame |--
    coq_prop (task_create_stack_input_facts sg input) &&
    (UCOS2_inv sg input.(stack_input_state) **
      task_stack_storage input.(stack_input_region)
        (input.(stack_input_lower) ++ input.(stack_input_old_frame) ++ input.(stack_input_upper)) **
      (armv7a_task_continuations abi input.(stack_input_state).(TskState).(parkedTaskStacks) **
       unmap_table_rep sg ** frame))).
  { unfold task_create_stack_input_resources, kernel_client_heap_world; rewrite kernel_program_inv_split_unmap.
    entailer!. }
  destruct (Hsplit before Hbefore) as [Hfacts Howned].
  destruct (task_create_stack_preparation_execution sg input slot rest _ before Hfacts Hnest Hfree Hhead Howned)
    as [image [after [Hdetach [Hsource Hafter]]]].
  destruct (task_create_stack_prepared_publication_input sg input slot rest image Hfacts Hfree Hdetach)
    as [Hvalid Hinput].
  assert (Hpointer : 0 <= task_slot_addr sg slot < 4294967296).
  { destruct Hsource as [reserved [initialized [_ [_ [detached [ready [hooked [Hpop _]]]]]]]].
    exact (proj1 (proj1 Hpop)). }
  assert (Hpriority : 0 <= (task_create_stack_input_args input).(initPrio) < 64).
  { exact (proj1 (proj2 (proj2 (proj2 (proj2 Hfacts))))). }
  assert (Hmerge : task_tcb_init_publication_tail_storage sg (task_create_stack_input_args input)
      (task_create_stack_input_detached input slot rest image) slot image **
      task_stack_storage input.(stack_input_region)
        (task_create_stack_publication_words (task_create_stack_prepared_publication input slot image)) **
      (armv7a_task_continuations abi input.(stack_input_state).(TskState).(parkedTaskStacks) **
       unmap_table_rep sg ** frame) |--
    kernel_client_heap_publication abi sg (task_create_stack_prepared_publication input slot image)
      (task_create_stack_input_detached input slot rest image) ** frame).
  { unfold kernel_client_heap_publication; cbn [task_create_stack_prepared_publication].
    entailer!. }
  exists image, after; split; [exact Hdetach|]; split; [exact Hsource|exact (Hmerge after Hafter)].
Qed.

Lemma task_tcb_init_empty_hooks_final_eq : forall before first second,
  task_tcb_init_empty_hooks_uninterrupted before first ->
  task_tcb_init_empty_hooks_uninterrupted before second -> first = second.
Proof.
  intros before first second [m1 [H1 H2]] [m2 [H3 H4]].
  assert (m1 = m2) by (eapply kernel_heap_execution_deterministic; eassumption); subst m2.
  eapply kernel_heap_execution_deterministic; eassumption.
Qed.

Lemma task_tcb_init_links_final_eq : forall sg pointer head before first second,
  task_tcb_init_link_fragment sg pointer head before first ->
  task_tcb_init_link_fragment sg pointer head before second -> first = second.
Proof.
  intros sg pointer head before first second
    [m1 [_ [H1 [_ Htail1]]]] [m2 [_ [H2 [_ Htail2]]]].
  assert (m1 = m2) by (eapply kernel_heap_execution_deterministic; eassumption); subst m2.
  destruct Htail1 as [[Hz1 Heq1]|[Hnz1 Hw1]], Htail2 as [[Hz2 Heq2]|[Hnz2 Hw2]];
    try congruence.
  eapply kernel_heap_execution_deterministic; eassumption.
Qed.

Lemma task_tcb_init_preparation_final_eq : forall sg args pointer next head before first second,
  task_tcb_init_preparation_fragment sg args pointer next head before first ->
  task_tcb_init_preparation_fragment sg args pointer next head before second -> first = second.
Proof.
  intros sg args pointer next head before first second
    [d1 [i1 [h1 [[_ [_ [_ Hp1]]] [Hi1 [Hh1 Hl1]]]]]]
    [d2 [i2 [h2 [[_ [_ [_ Hp2]]] [Hi2 [Hh2 Hl2]]]]]].
  assert (d1 = d2) by (eapply kernel_heap_execution_deterministic; eassumption); subst d2.
  assert (i1 = i2) by (eapply kernel_heap_execution_deterministic; eassumption); subst i2.
  assert (h1 = h2) by (eapply task_tcb_init_empty_hooks_final_eq; eassumption); subst h2.
  eapply task_tcb_init_links_final_eq; eassumption.
Qed.

Lemma task_create_stack_preparation_final_eq : forall sg input slot rest before first second,
  task_create_stack_preparation_fragment sg input slot rest before first ->
  task_create_stack_preparation_fragment sg input slot rest before second -> first = second.
Proof.
  intros sg input slot rest before first second
    [r1 [i1 [[_ [_ Hr1]] [Hi1 Hp1]]]] [r2 [i2 [[_ [_ Hr2]] [Hi2 Hp2]]]].
  assert (r1 = r2) by (eapply kernel_heap_execution_deterministic; eassumption); subst r2.
  assert (i1 = i2) by (eapply kernel_heap_execution_deterministic; eassumption); subst i2.
  eapply task_tcb_init_preparation_final_eq; eassumption.
Qed.

(** Guards and allocation tags here describe the BEFORE snapshot of the
    input cut. The source relation contains actual heap operations, never
    the publication resource assertion or a future safety condition. *)
Inductive task_create_stack_heap_step (sg : StableGlobVars) :
  KernelClientHeapCut TaskCreateStackInput -> model -> KernelClientHeapCut TaskCreateStackInput -> model -> Prop :=
| TaskCreateStackHeapPrepare : forall input slot rest image before after,
    input.(stack_input_state).(IntrState).(intNesting) = 0 ->
    input.(stack_input_state).(TskState).(prioTbl) input.(stack_input_args).(createPriority) = PTFree ->
    input.(stack_input_state).(TskState).(unUsedTaskStates) = slot :: rest ->
    input.(stack_input_state).(TskState).(taskLifecycle).(taskFreeStorage) slot = Some image ->
    task_create_stack_preparation_fragment sg input slot rest before after ->
    task_create_stack_heap_step sg (KernelClientHeapExtra input) before
      (KernelClientHeapTaskPublication (task_create_stack_prepared_publication input slot image)) after.

Inductive task_create_stack_heap_effect (sg : StableGlobVars) :
  KernelClientHeapCut TaskCreateStackInput -> UCOS2_Verify_State ->
    KernelClientHeapCut TaskCreateStackInput -> UCOS2_Verify_State -> Prop :=
| TaskCreateStackHeapPrepared : forall input slot rest image,
    task_create_stack_heap_effect sg (KernelClientHeapExtra input) input.(stack_input_state)
      (KernelClientHeapTaskPublication (task_create_stack_prepared_publication input slot image))
      (task_create_stack_input_detached input slot rest image).

Lemma task_create_stack_heap_extension_valid : forall external platform port
  (abi : Armv7aContinuationABI external platform port),
  kernel_client_heap_extension_valid abi (task_create_stack_input_resources abi)
    task_create_stack_heap_step task_create_stack_heap_effect.
Proof.
  intros external platform port abi sg cut before next after state frame Hstep Hbefore.
  destruct Hstep as [input slot rest image before after Hnest Hfree Hhead Himage Hsource].
  change ((task_create_stack_input_resources abi sg input state ** frame) before) in Hbefore.
  assert (Hstate : state = input.(stack_input_state)).
  { destruct Hbefore as [owned [rest_heap [Hjoin [[[Hstate Hfacts] Howned] Hframe]]]]; exact Hstate. }
  subst state.
  destruct (task_create_stack_input_produces_publication external platform port abi sg input slot rest frame before
    Hnest Hfree Hhead Hbefore) as [observed [produced [Hdetach [Hrun Hproduced]]]].
  assert (Hlookup : input.(stack_input_state).(TskState).(taskLifecycle).(taskFreeStorage) slot = Some observed).
  { exact (proj2 (proj2 (proj2 Hdetach))). }
  assert (observed = image) by congruence; subst observed.
  assert (produced = after) by (eapply task_create_stack_preparation_final_eq; eassumption); subst produced.
  exists (task_create_stack_input_detached input slot rest image); split; [constructor|exact Hproduced].
Qed.

(** The registered preparation is actually followed by the existing
    publication source consumer. Both stages act on this same heap. *)
Lemma task_create_stack_input_publishes_world : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg input slot rest (frame : Assertion) before,
  input.(stack_input_state).(IntrState).(intNesting) = 0 ->
  input.(stack_input_state).(TskState).(prioTbl) input.(stack_input_args).(createPriority) = PTFree ->
  input.(stack_input_state).(TskState).(unUsedTaskStates) = slot :: rest ->
  (task_create_stack_input_resources abi sg input input.(stack_input_state) ** frame) before ->
  exists image after,
    kernel_client_heap_trace task_create_stack_heap_step sg
      (KernelClientHeapExtra input) before KernelClientHeapClosed after /\
    (kernel_client_heap_world abi sg
      (task_create_stack_publication_state sg (task_create_stack_prepared_publication input slot image)
        (task_create_stack_input_detached input slot rest image)) ** frame) after.
Proof.
  intros external platform port abi sg input slot rest frame before Hnest Hfree Hhead Hbefore.
  destruct (task_create_stack_input_produces_publication external platform port abi sg input slot rest frame before
    Hnest Hfree Hhead Hbefore) as [image [prepared [Hdetach [Hsource Hprepared]]]].
  destruct (kernel_client_publication_produces_world external platform port abi sg
    (task_create_stack_prepared_publication input slot image)
    (task_create_stack_input_detached input slot rest image) frame prepared Hprepared)
    as [after [Hpublish [Hstep Hafter]]].
  exists image, after; split; [|exact Hafter].
  econstructor.
  - apply KernelClientHeapRegistered.
    eapply TaskCreateStackHeapPrepare with (rest := rest); try eassumption.
    exact (proj2 (proj2 (proj2 Hdetach))).
  - econstructor; [apply KernelClientHeapPublish; exact Hpublish|constructor].
Qed.

(** Strong resource entry. This is not obtained from weak continuations:
    the caller supplies the SAME map's current SP/frame-indexed entries. *)
Definition task_create_stack_covered_input_resources {external platform port}
  (abi : Armv7aContinuationABI external platform port) sg input active : Assertion :=
  coq_prop (task_create_stack_input_facts sg input /\
    task_stack_live_coverage input.(stack_input_state).(TskState) active) &&
  (kernel_program_inv sg input.(stack_input_state) **
    armv7a_task_stack_continuations abi input.(stack_input_state).(TskState)
      input.(stack_input_state).(TskState).(parkedTaskStacks) **
    task_stack_storage input.(stack_input_region)
      (input.(stack_input_lower) ++ input.(stack_input_old_frame) ++ input.(stack_input_upper))).

Lemma task_create_stack_covered_input_assign : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg input active,
  task_create_stack_input_facts sg input ->
  task_stack_live_coverage input.(stack_input_state).(TskState) active ->
  kernel_program_inv sg input.(stack_input_state) **
    armv7a_task_stack_continuations abi input.(stack_input_state).(TskState)
      input.(stack_input_state).(TskState).(parkedTaskStacks) **
    task_stack_storage input.(stack_input_region)
      (input.(stack_input_lower) ++ input.(stack_input_old_frame) ++ input.(stack_input_upper)) |--
  task_create_stack_covered_input_resources abi sg input active.
Proof. intros; unfold task_create_stack_covered_input_resources; entailer!. Qed.

(** Actual preparation -> actual five publication stores -> the existing
    strong publication/initial-frame producer. No weak-map projection is
    used. Boot (active=None), no-scheduler, and running inputs all retain
    their own coverage index; this theorem stops before final Restore. *)
Lemma task_create_stack_input_publishes_covered : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg input active slot rest (frame : Assertion) before,
  input.(stack_input_state).(IntrState).(intNesting) = 0 ->
  input.(stack_input_state).(TskState).(prioTbl) input.(stack_input_args).(createPriority) = PTFree ->
  input.(stack_input_state).(TskState).(unUsedTaskStates) = slot :: rest ->
  (task_create_stack_covered_input_resources abi sg input active ** frame) before ->
  exists image prepared after,
    task_create_stack_preparation_fragment sg input slot rest before prepared /\
    task_tcb_init_publication_tail_fragment sg (task_create_stack_input_args input).(initPrio)
      (task_slot_addr sg slot) prepared after /\
    let publication := task_create_stack_prepared_publication input slot image in
    let current := task_create_stack_input_detached input slot rest image in
    let published := task_create_stack_publication_state sg publication current in
    kernel_client_step (task_create_stack_publication_client publication) sg current published /\
    task_stack_live_coverage published.(TskState) active /\
    (kernel_program_inv sg published **
      armv7a_task_stack_continuations abi published.(TskState) published.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi sg input active slot rest frame before Hnest Hfree Hhead Hbefore.
  assert (Hsplit : task_create_stack_covered_input_resources abi sg input active ** frame |--
    coq_prop (task_create_stack_input_facts sg input /\
      task_stack_live_coverage input.(stack_input_state).(TskState) active) &&
    (UCOS2_inv sg input.(stack_input_state) **
      task_stack_storage input.(stack_input_region)
        (input.(stack_input_lower) ++ input.(stack_input_old_frame) ++ input.(stack_input_upper)) **
      (armv7a_task_stack_continuations abi input.(stack_input_state).(TskState)
         input.(stack_input_state).(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame))).
  { unfold task_create_stack_covered_input_resources; rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hsplit before Hbefore) as [[Hfacts Hcoverage] Howned].
  destruct (task_create_stack_preparation_execution sg input slot rest _ before Hfacts Hnest Hfree Hhead Howned)
    as [image [prepared [Hdetach [Hsource Hprepared]]]].
  destruct (task_create_stack_prepared_publication_input sg input slot rest image Hfacts Hfree Hdetach)
    as [Hvalid Hinput].
  set (publication := task_create_stack_prepared_publication input slot image).
  set (current := task_create_stack_input_detached input slot rest image).
  set (actual := task_create_stack_input_args input).
  assert (Hcurrent_coverage : task_stack_live_coverage current.(TskState) active) by exact Hcoverage.
  assert (Hpointer : 0 <= task_slot_addr sg slot < 4294967296).
  { destruct Hsource as [reserved [initialized [_ [_ [detached [ready [hooked [Hpop _]]]]]]]].
    exact (proj1 (proj1 Hpop)). }
  assert (Hpriority : 0 <= actual.(initPrio) < 64).
  { exact (proj1 (proj2 (proj2 (proj2 (proj2 Hfacts))))). }
  assert (Hbinding : task_tcb_init_commit_binding actual
    input.(stack_input_call).(os_sched_call_invocation) input.(stack_input_call).(os_sched_call_origin)
    (task_create_stack_input_acquired input) current slot).
  { exact (proj1 (proj2 (proj2 Hinput))). }
  assert (Hfocus : task_tcb_init_publication_tail_storage sg actual current slot image **
      task_stack_storage input.(stack_input_region) (task_create_stack_publication_words publication) **
      (armv7a_task_stack_continuations abi input.(stack_input_state).(TskState)
         input.(stack_input_state).(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame) |--
    task_tcb_init_publication_tail_storage sg actual current slot image **
      (task_stack_storage input.(stack_input_region) (task_create_stack_publication_words publication) **
       armv7a_task_stack_continuations abi current.(TskState) current.(TskState).(parkedTaskStacks) **
       (unmap_table_rep sg ** frame))) by entailer!.
  destruct (task_tcb_init_publication_tail_store_execution sg actual
    input.(stack_input_call).(os_sched_call_invocation) input.(stack_input_call).(os_sched_call_origin)
    (task_create_stack_input_acquired input) current slot image _ prepared Hvalid Hbinding Hpriority Hpointer
    (Hfocus prepared Hprepared)) as [after [Htail Hafter]].
  pose proof (task_create_publication_covered_stack_merge external platform port abi sg publication current active
    Hvalid Hinput Hcurrent_coverage) as Hclose; cbv zeta in Hclose.
  set (published := task_create_stack_publication_state sg publication current).
  assert (Hmerge : task_create_publication_storage sg actual
      input.(stack_input_call).(os_sched_call_invocation) (task_create_stack_input_acquired input) current slot image **
      (task_stack_storage input.(stack_input_region) (task_create_stack_publication_words publication) **
       armv7a_task_stack_continuations abi current.(TskState) current.(TskState).(parkedTaskStacks) **
       (unmap_table_rep sg ** frame)) |--
    coq_prop (kernel_client_step (task_create_stack_publication_client publication) sg current published /\
      task_stack_live_coverage published.(TskState) active) &&
    (kernel_program_inv sg published **
      armv7a_task_stack_continuations abi published.(TskState) published.(TskState).(parkedTaskStacks) ** frame)).
  { unfold task_create_stack_publication_args, publication, task_create_stack_prepared_publication in Hclose.
    cbn [stack_publication_region stack_publication_args stack_publication_return
      stack_publication_lower stack_publication_upper stack_publication_name stack_publication_invocation
      stack_publication_origin stack_publication_acquired stack_publication_slot stack_publication_image
      stack_publication_lease] in Hclose.
    fold (task_tcb_init_stack_call_args input.(stack_input_args) input.(stack_input_name)) in Hclose.
    fold (task_create_stack_prepared_publication input slot image) in Hclose.
    fold (task_create_stack_input_args input) actual current publication published in Hclose.
    rewrite kernel_program_inv_split_unmap.
    sepcon_assoc_change; sep_apply_l_atomic Hclose; Intros; entailer!. }
  destruct (Hmerge after Hafter) as [[Hstep Hcovered] Hresources].
  exists image, prepared, after; split; [exact Hsource|]; split; [exact Htail|].
  cbv zeta; split; [exact Hstep|]; split; assumption.
Qed.
