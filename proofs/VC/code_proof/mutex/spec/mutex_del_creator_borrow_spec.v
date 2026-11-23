Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.sched Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_slot_spec.
Import UCOS2_C_Rules ListNotations EventStateDef KernelHeapObservation KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual nonempty shared free-pop fragment used by Sem/Mbox/Queue
    Create. The existing selected source/field binding is reused, not
    assumed for another profile. Reads precede the one global pointer
    store; pevent's local value is the observed head. This fragment stops
    BEFORE Restore. It neither implements task switching nor publishes
    the object, and it does not give Del ownership from a static address. *)
Lemma event_create_detach_heap_resources : forall sg state eid rest before (frame : Assertion),
  sem_create_source_binding sg ->
  state.(EventState).(unUsedEventStates) = eid :: rest ->
  (kernel_program_inv sg state ** frame) before ->
  exists image after,
    state.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image /\
    event_pool_addr sg eid <> 0 /\
    pointer_load sg.(g_OSEventFreeList) (event_pool_addr sg eid) before /\
    pointer_load (event_pool_addr sg eid + 4)
      (event_encode_pool_link sg (hd_error rest)) before /\
    kernel_heap_execution
      (pointer_store_writes sg.(g_OSEventFreeList) (event_encode_pool_link sg (hd_error rest)))
      before after /\
    event_create_allocate_critical state (Some (eid, image))
      (replace_EventS (event_detach_head state.(EventState) eid rest image) state) /\
    (event_private_storage_rep sg eid (sem_create_allocation_identity state image) **
     kernel_program_inv sg (replace_EventS (event_detach_head state.(EventState) eid rest image) state) **
     frame) after.
Proof.
  intros sg state eid rest before frame Hsource Hhead Hpre.
  assert (Hvalid : UCOS2_state_inv sg state).
  { destruct Hpre as [owned [other [Hjoin [Hinv Hother]]]]; exact (proj1 Hinv). }
  destruct (sem_create_pool_nonempty_facts sg state eid rest Hvalid Hhead)
    as [Hrange [image [Himage Hnext]]].
  pose proof Hsource as [_ [Hroot [_ Hlayout]]].
  destruct (Hlayout eid Hrange) as [[Hpositive Hupper] Hlink].
  assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = false).
  { destruct Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
  assert (Hopen : kernel_program_inv sg state ** frame |--
    sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid **
    ((event_pool_addr sg eid + 4) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
     (sem_create_node_frame sg state eid image ** unmap_table_rep sg ** frame))).
  { rewrite kernel_program_inv_split_unmap,
      (sem_create_pool_split_head sg state Hsource).
    Intros.
    sep_apply_l_atomic (sem_create_pool_split_node sg state eid rest image
      Hsource Hvalid Hhead Himage).
    unfold sem_create_pool_head; rewrite Hhead, Hroot, Hlink.
    cbn [hd_error event_encode_pool_link]; entailer!. }
  pose proof (Hopen before Hpre) as Howned.
  pose proof (framed_pointer_store_load _ _ _ _ Howned) as Hread_head.
  assert (Hnext_order : sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid **
    ((event_pool_addr sg eid + 4) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
     (sem_create_node_frame sg state eid image ** unmap_table_rep sg ** frame)) |--
    (event_pool_addr sg eid + 4) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
    (sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid **
     sem_create_node_frame sg state eid image ** unmap_table_rep sg ** frame)) by entailer!.
  pose proof (framed_pointer_store_load _ _ _ _ (Hnext_order before Howned)) as Hread_next.
  assert (Hwrite_order : sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid **
    ((event_pool_addr sg eid + 4) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
     (sem_create_node_frame sg state eid image ** unmap_table_rep sg ** frame)) |--
    sg.(g_OSEventFreeList) # Ptr |->_ **
    ((event_pool_addr sg eid + 4) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
     (sem_create_node_frame sg state eid image ** unmap_table_rep sg ** frame))).
  { sep_apply_l_atomic (store_ptr_undef_store_ptr sg.(g_OSEventFreeList) (event_pool_addr sg eid));
    entailer!. }
  destruct (framed_pointer_store_execution _ _ _ before (proj1 Hread_next)
    (Hwrite_order before Howned)) as [after [Hwrite Hafter]].
  assert (Hclose : sg.(g_OSEventFreeList) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
    ((event_pool_addr sg eid + 4) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
     (sem_create_node_frame sg state eid image ** unmap_table_rep sg ** frame)) |--
    event_private_storage_rep sg eid (sem_create_allocation_identity state image) **
    kernel_program_inv sg (replace_EventS (event_detach_head state.(EventState) eid rest image) state) ** frame).
  { pose proof (sem_create_pool_merge_detached_node sg state eid rest image
      Hsource Hvalid Hhead Himage) as Hmerge.
    rewrite Hroot, Hlink in Hmerge.
    unfold event_private_storage_rep, sem_create_allocation_identity.
    cbn [eventPrivateStorage]; rewrite Hnames, kernel_program_inv_split_unmap.
    cancel (unmap_table_rep sg); cancel frame.
    exact Hmerge. }
  exists image, after; split; [exact Himage|]. split; [lia|].
  split; [exact Hread_head|]. split; [exact Hread_next|]. split; [exact Hwrite|].
  split.
  - unfold event_create_allocate_critical; rewrite Hhead.
    exists image; repeat split; assumption || reflexivity.
  - exact (Hclose after Hafter).
Qed.

(** An immediate consumer of the real free-pop output, not a lemma with
    caller-invented private bytes. All padding and payload cells remain
    in the creator's exact residual while Type is lent at this one cut.
    A later Del read must transport/recover this owner from its actual
    intervening source execution; no unchanged frame across Restore is
    asserted here. The output can be merged by the existing inverse. *)
Lemma event_create_detach_type_loan : forall sg state eid rest before (frame : Assertion),
  sem_create_source_binding sg ->
  state.(EventState).(unUsedEventStates) = eid :: rest ->
  (kernel_program_inv sg state ** frame) before ->
  exists image after,
    pointer_load sg.(g_OSEventFreeList) (event_pool_addr sg eid) before /\
    pointer_load (event_pool_addr sg eid + 4)
      (event_encode_pool_link sg (hd_error rest)) before /\
    kernel_heap_execution
      (pointer_store_writes sg.(g_OSEventFreeList) (event_encode_pool_link sg (hd_error rest)))
      before after /\
    event_create_allocate_critical state (Some (eid, image))
      (replace_EventS (event_detach_head state.(EventState) eid rest image) state) /\
    (event_pool_addr sg eid # UChar |-> 0 **
     event_private_storage_without_type sg eid (sem_create_allocation_identity state image) **
     kernel_program_inv sg (replace_EventS (event_detach_head state.(EventState) eid rest image) state) **
     frame) after.
Proof.
  intros sg state eid rest before frame Hsource Hhead Hpre.
  assert (Hvalid : UCOS2_state_inv sg state).
  { destruct Hpre as [owned [other [Hjoin [Hinv Hother]]]]; exact (proj1 Hinv). }
  destruct (event_create_detach_heap_resources sg state eid rest before frame Hsource Hhead Hpre)
    as [image [after [Himage [Hnonzero [Hread [Hnext [Hwrite [Hstep Hafter]]]]]]]].
  pose proof (event_create_allocate_critical_image_type sg state eid image _ Hvalid Hstep) as Htype.
  assert (Hsplit : event_private_storage_rep sg eid (sem_create_allocation_identity state image) **
    kernel_program_inv sg (replace_EventS (event_detach_head state.(EventState) eid rest image) state) ** frame |--
    event_pool_addr sg eid # UChar |-> 0 **
    event_private_storage_without_type sg eid (sem_create_allocation_identity state image) **
    kernel_program_inv sg (replace_EventS (event_detach_head state.(EventState) eid rest image) state) ** frame).
  { sep_apply_l_atomic (event_private_storage_rep_split_type sg eid
      (sem_create_allocation_identity state image) 0 Htype); entailer!. }
  exists image, after; split; [exact Hread|]. split; [exact Hnext|]. split; [exact Hwrite|].
  split; [exact Hstep|exact (Hsplit after Hafter)].
Qed.

(** Complete free-pop fragment, including ordinary pool exhaustion. The
    image/result pair is the existing abstract operation's observation,
    not an extra C return. A nonempty run performs the real next read and
    root store; the empty run returns NULL with the entire heap unchanged.
    Existing invocation/CPU/stack owners can be the same disjoint frame. *)
Lemma event_create_allocate_heap_source : forall sg state before (frame : Assertion),
  sem_create_source_binding sg ->
  (kernel_program_inv sg state ** frame) before ->
  exists result allocated after,
    pointer_load sg.(g_OSEventFreeList) (event_create_return_ptr sg result) before /\
    event_create_allocate_critical state result allocated /\
    (match result with
     | None => after = before
     | Some (eid, _) => event_pool_addr sg eid <> 0 /\ exists next,
         pointer_load (event_pool_addr sg eid + 4) next before /\
         kernel_heap_execution (pointer_store_writes sg.(g_OSEventFreeList) next) before after
     end) /\
    (kernel_program_inv sg allocated **
     (match result with
      | None => emp
      | Some (eid, image) => event_private_storage_rep sg eid (sem_create_allocation_identity state image)
      end) ** frame) after.
Proof.
  intros sg state before frame Hsource Hpre.
  destruct state.(EventState).(unUsedEventStates) as [|eid rest] eqn:Hhead.
  - exists None, state, before.
    assert (Hroot : kernel_program_inv sg state ** frame |--
      sg.(g_OSEventFreeList) # Ptr |-> 0 ** (sem_create_pool_frame sg state ** unmap_table_rep sg ** frame)).
    { rewrite kernel_program_inv_split_unmap, (sem_create_pool_split_head sg state Hsource).
      pose proof Hsource as [_ [Haddress _]].
      unfold sem_create_pool_head; rewrite Hhead, Haddress.
      cbn [hd_error event_encode_pool_link]; entailer!. }
    split; [exact (framed_pointer_store_load _ _ _ _ (Hroot before Hpre))|].
    split; [unfold event_create_allocate_critical; rewrite Hhead; split; reflexivity|].
    split; [reflexivity|].
    assert (Hclose : kernel_program_inv sg state ** frame |-- kernel_program_inv sg state ** emp ** frame)
      by entailer!.
    exact (Hclose before Hpre).
  - destruct (event_create_detach_heap_resources sg state eid rest before frame Hsource Hhead Hpre)
      as [image [after [Himage [Hnonzero [Hread [Hnext [Hwrite [Hstep Hafter]]]]]]]].
    exists (Some (eid, image)),
      (replace_EventS (event_detach_head state.(EventState) eid rest image) state), after.
    split; [exact Hread|]. split; [exact Hstep|]. split.
    + split; [exact Hnonzero|]. exists (event_encode_pool_link sg (hd_error rest)); split; assumption.
    + assert (Hclose : event_private_storage_rep sg eid (sem_create_allocation_identity state image) **
        kernel_program_inv sg (replace_EventS (event_detach_head state.(EventState) eid rest image) state) ** frame |--
        kernel_program_inv sg (replace_EventS (event_detach_head state.(EventState) eid rest image) state) **
        event_private_storage_rep sg eid (sem_create_allocation_identity state image) ** frame) by entailer!.
      exact (Hclose after Hafter).
Qed.
