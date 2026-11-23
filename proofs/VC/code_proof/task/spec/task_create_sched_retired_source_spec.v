Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_save_global_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_client_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Actual masked TCB-SP write after self-delete. OSTCBCur still names a
    free-pool slot; its current free image, not a stale live TCB or old
    free-list head, supplies the cell. The NoDup/membership facts come from
    the existing pool invariant. No new task generation is attached to the
    retiring invocation and no absent-owner totalization is used.

    An earlier IRQ/reuse interval must establish THIS observed free owner
    or a different actual source case. This local producer does not freeze
    allocation status across that interval. *)
Lemma os_sched_store_free_sp_call_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg state slot image sp focus (frame : Assertion) before,
  state.(SchedState).(curTaskID) = Some slot ->
  state.(TskState).(inUsedTaskStates) slot = None ->
  state.(TskState).(taskLifecycle).(taskFreeStorage) slot = Some image ->
  tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot ->
  0 <= sp < 4294967296 ->
  (UCOS2_inv sg state ** armv7a_task_call_stacks abi state.(TskState) focus
    state.(TskState).(parkedTaskStacks) ** frame) before ->
  pointer_load sg.(g_OSTCBCur) (task_slot_addr sg slot) before /\
  exists after,
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg slot) sp) before after /\
    (UCOS2_inv sg (os_sched_save_current_sp state slot sp) **
     armv7a_task_call_stacks abi (os_sched_save_current_sp state slot sp).(TskState) focus
       (os_sched_save_current_sp state slot sp).(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi sg state slot image sp focus frame before
    Hcurrent Hunused Himage Haddress Hsp Hpre.
  assert (Hopen : UCOS2_inv sg state ** armv7a_task_call_stacks abi state.(TskState) focus
      state.(TskState).(parkedTaskStacks) ** frame |--
    coq_prop (UCOS2_state_inv sg state) &&
    (UCOS2_raw_rep sg state ** armv7a_task_call_stacks abi state.(TskState) focus
      state.(TskState).(parkedTaskStacks) ** frame)) by (unfold UCOS2_inv; entailer!).
  destruct (Hopen before Hpre) as [Hvalid Hraw].
  pose proof (proj1 (proj1 (proj2 Hvalid))) as Hpool.
  assert (Hnodup : NoDup state.(TskState).(unUsedTaskStates)) by (unfold task_pool_partition in Hpool; tauto).
  assert (Hin : In slot state.(TskState).(unUsedTaskStates)).
  { destruct Hpool as [_ [_ [_ [_ [Hdomain _]]]]]. apply (proj2 (Hdomain slot)); eauto. }
  assert (Hload : pointer_load sg.(g_OSTCBCur) (task_slot_addr sg slot) before).
  { match type of Hraw with ?P before => assert (Hcell : P |--
      sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg slot ** TT) end.
    { unfold UCOS2_raw_rep, sched_raw_rep, sched_physical_rep; rewrite Hcurrent.
      cbn [encode_task_link]; entailer!; intros ? ?; exact I. }
    eapply framed_pointer_store_load; exact (Hcell before Hraw). }
  split; [exact Hload|].
  let rest := constr:(task_free_storage_without_saved_sp sg state.(TskState) slot image **
    (store_used_task_map sg state.(TskState).(inUsedTaskStates) **
     sg.(g_OSTCBFreeList) # Ptr |-> encode_task_link sg (hd_error state.(TskState).(unUsedTaskStates)) **
     sg.(g_OSTCBList) # Ptr |-> encode_task_link sg state.(TskState).(tcbListHead) **
     sg.(g_OSTaskCtr) # UChar |-> state.(TskState).(taskCount) **
     store_prio_tbl sg state.(TskState).(prioTbl) ** task_reg_allocator_rep sg state.(TskState) **
     sched_raw_rep sg state.(TskState) state.(SchedState) **
     UCOS2_raw_rep_missing_task_storage_sched sg state **
     armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame)) in
  assert (Hsplit : UCOS2_raw_rep sg state ** armv7a_task_call_stacks abi state.(TskState) focus
      state.(TskState).(parkedTaskStacks) ** frame |-- task_slot_addr sg slot # Ptr |->_ ** rest).
  { unfold UCOS2_raw_rep, task_shared_rep, task_public_storage,
      UCOS2_raw_rep_missing_task_storage_sched.
    sep_apply_l_atomic (task_free_storage_split_saved_sp sg state.(TskState) slot image Hnodup Hin Himage).
    cbn [tcb_layout_cell tcb_cell]; rewrite Haddress.
    destruct (image (TCBCommonField TCBStkPtr)) as [old|].
    - sep_apply_l_atomic (store_ptr_undef_store_ptr (task_slot_addr sg slot) old); entailer!.
    - entailer!. }
  destruct (framed_pointer_store_execution (task_slot_addr sg slot) sp _ before Hsp (Hsplit before Hraw))
    as [after [Hwrite Hafter]].
  assert (Hupdated : UCOS2_state_inv sg (os_sched_save_current_sp state slot sp)).
  { unfold os_sched_save_current_sp; rewrite Hunused; apply os_sched_save_free_sp_preserves_validity;
      exact Hvalid. }
  assert (Hsched : sched_raw_rep sg state.(TskState) state.(SchedState) =
    sched_raw_rep sg (task_save_free_sp state.(TskState) slot sp) state.(SchedState)).
  { apply sched_raw_rep_change_task_index; reflexivity. }
  assert (Hevent : event_raw_rep sg state.(TskState) state.(EventState) =
    event_raw_rep sg (task_save_free_sp state.(TskState) slot sp) state.(EventState)).
  { apply event_raw_rep_change_task_index, event_wait_priority_agreement_encodes;
      intros eid event tid Hlookup Hin_wait; reflexivity. }
  match type of Hafter with ?P after => assert (Hmerge : P |--
    UCOS2_inv sg (os_sched_save_current_sp state slot sp) **
    armv7a_task_call_stacks abi (os_sched_save_current_sp state slot sp).(TskState) focus
      (os_sched_save_current_sp state slot sp).(TskState).(parkedTaskStacks) ** frame) end.
  { assert (Hcell : task_slot_addr sg slot # Ptr |-> sp |--
      tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg slot)
        (TCBCommonField TCBStkPtr) (Some sp)).
    { cbn [tcb_layout_cell tcb_cell]; rewrite Haddress; reflexivity. }
    sep_apply_l_atomic Hcell.
    sep_apply_l_atomic (task_free_storage_merge_saved_sp sg state.(TskState) slot image sp
      Hnodup Hin Himage).
    unfold UCOS2_inv; entailer!.
    unfold os_sched_save_current_sp; rewrite Hunused.
    unfold UCOS2_raw_rep, task_shared_rep, task_public_storage, UCOS2_raw_rep_missing_task_storage_sched.
    cbn [replace_TskS TskState SchedState IntrState EventState TickState FlagState MemoryState
      TimerState StatsState ControlState NameState task_save_free_sp glob_task_set_lifecycle
      inUsedTaskStates unUsedTaskStates taskLifecycle taskFreeStorage tcbListHead taskCount prioTbl parkedTaskStacks].
    entailer!.
    rewrite <- Hsched, <- Hevent.
    sep_apply_l_atomic (armv7a_task_call_stacks_used_map_eq external platform port abi
      state.(TskState) (task_save_free_sp state.(TskState) slot sp) focus
      state.(TskState).(parkedTaskStacks) eq_refl).
    unfold task_reg_allocator_rep.
    cbn [task_save_free_sp glob_task_set_lifecycle taskRegNextID]; entailer!. }
  exists after; split; [exact Hwrite|exact (Hmerge after Hafter)].
Qed.

(** The retiring call still owns its physical stack and execution lease.
    The current TCB allocation is free, so only its free image receives
    the real SP store. Its old-generation descriptor is then parked under
    its old key; the high-ready live task, never that free image, supplies
    the restore destination. All geometry/register premises describe this
    actual source cut and are not inferred from coverage or the CPU ABI. *)
Lemma os_sched_source_free_switch_destination_resources :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    (task_abi : Armv7aTaskContextABI external platform port abi)
    (initial : Armv7aInitialEntryABI external platform port abi)
    sg state image call old_sp cpsr registers lr prefix suffix first old_words
    focus publication (frame : Assertion) before,
  state.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = None ->
  state.(TskState).(taskLifecycle).(taskFreeStorage) call.(os_sched_call_stack).(stackLeaseSlot) = Some image ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  sched_high_ready_consistency state.(TskState) state.(SchedState) ->
  state.(SchedState).(readyList) <> [] ->
  (task_stack_key call.(os_sched_call_stack) = armv7a_call_focus_key focus ->
    focus = armv7a_call_focus call lr lr) ->
  call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    call.(os_sched_call_fragments) ->
  task_publication_happened state.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  List.length registers = 13%nat ->
  0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) registers ->
  armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  (os_sched_source_switch_pre external platform port abi sg call focus state ** frame) before ->
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  let saved := armv7a_task_save_image call old_sp cpsr registers lr fragments in
  let updated := os_sched_save_current_sp state call.(os_sched_call_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_sp) in
  exists written stored,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      saved.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi call saved stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step external.(os_sched_hook_action) sg updated updated ->
      exists incoming resumed installed selected current,
        external.(os_sched_arch_save_source) call saved.(armv7a_continuation_sp) fragments /\
        os_sched_destination_binding external call fragments updated incoming resumed /\
        incoming.(stackLeaseSlot) <> call.(os_sched_call_stack).(stackLeaseSlot) /\
        selected.(armv7a_continuation_fragments) = resumed /\
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        (forall payload,
          updated.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
          task_stack_key incoming <> armv7a_call_focus_key focus ->
          (os_sched_install_context call fragments incoming updated).(TskState).(parkedTaskStacks)
            (armv7a_call_focus_key focus) = Some payload) /\
        (forall restored, armv7a_task_restore_transition task_abi call selected installed restored ->
          os_sched_source_switch_execution external platform port abi task_abi sg state call old_sp cpsr
            registers lr saved incoming selected before restored /\
          armv7a_task_restored_source external selected /\
          (os_sched_source_selected_post external platform port abi sg focus incoming selected current
             (os_sched_install_context call fragments incoming updated) ** frame) restored)).
Proof.
  intros external platform port abi task_abi initial sg state image call old_sp cpsr registers lr prefix
    suffix first old_words focus publication frame before Hcurrent Hunused Himage Hnone Hhigh Hnonempty
    Hfocus Hfragments Hregion Hgeometry Hhistory Hlength Hcpsr Hlr Hranges Hmask Hsp32 Hsp Haddress Hpre
    fragments saved updated.
  assert (Hopen : os_sched_source_switch_pre external platform port abi sg call focus state ** frame |--
    coq_prop (task_stack_live_coverage state.(TskState) (Some (task_stack_key call.(os_sched_call_stack)))) &&
    (task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion)
      (prefix ++ [(first, first + 16, old_words)] ++ suffix) **
     (UCOS2_inv sg state **
      armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
      (interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
       external.(os_sched_arch_running) call ** frame)))).
  { unfold os_sched_source_switch_pre, kernel_call_execution_owned, os_sched_context_resources;
      rewrite Hfragments; entailer!. }
  destruct (Hopen before Hpre) as [Hcoverage Howned].
  destruct (armv7a_task_save_fragment_execution call old_sp cpsr registers lr prefix suffix first old_words
    _ before Hlength Hcpsr Hlr Hranges Hsp Howned)
    as [written [Hwrites [Hwritten [Hreads Hslice]]]].
  fold fragments saved in Hwritten, Hreads, Hslice.
  match type of Hwritten with ?P written => assert (Horder : P |--
    UCOS2_inv sg state **
    armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
    (task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
       saved.(armv7a_continuation_fragments) **
     interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
     external.(os_sched_arch_running) call ** frame)) end.
  { unfold saved, armv7a_task_save_image; cbn; entailer!. }
  destruct (os_sched_store_free_sp_call_resources external platform port abi sg state
    call.(os_sched_call_stack).(stackLeaseSlot) image saved.(armv7a_continuation_sp) focus _ written
    Hcurrent Hunused Himage (Haddress _) Hsp32 (Horder written Hwritten))
    as [Hload [stored [Hstore Hstored]]].
  fold updated in Hstored.
  assert (Hbinding : armv7a_continuation_binding saved)
    by (apply armv7a_task_save_image_binding; exact Hlength).
  assert (Hlive : task_stack_live_sp updated.(TskState) (task_stack_key call.(os_sched_call_stack))
    saved.(armv7a_continuation_sp)).
  { unfold updated, os_sched_save_current_sp; rewrite Hunused.
    intros node Hnode Hgeneration.
    change (state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node) in Hnode.
    rewrite Hunused in Hnode; discriminate. }
  assert (Hcovered : task_stack_live_coverage updated.(TskState)
    (Some (task_stack_key call.(os_sched_call_stack)))).
  { unfold updated, os_sched_save_current_sp; rewrite Hunused; exact Hcoverage. }
  assert (Hstored_reads : armv7a_continuation_restore_reads saved stored).
  { eapply armv7a_task_frame_slice_restore_reads; [exact Hbinding|exact Hslice|].
    match type of Hstored with ?P stored => assert (Hread_order : P |--
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) **
      (UCOS2_inv sg updated **
       armv7a_task_call_stacks abi updated.(TskState) focus updated.(TskState).(parkedTaskStacks) **
       interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
       external.(os_sched_arch_running) call ** frame)) by entailer! end.
    exact (Hread_order stored Hstored). }
  assert (Hsaved : os_sched_saved_stack_binding call fragments updated).
  { unfold os_sched_saved_stack_binding, updated, os_sched_save_current_sp; rewrite Hunused.
    split; [exact Hregion|]. split.
    - unfold fragments; apply armv7a_task_frame_update_preserves_fragment_bounds with (old_words := old_words).
      rewrite <- Hfragments; exact Hgeometry.
    - split; [exists publication; exact Hhistory|]. split; [|exact Hnone].
      intros node Hnode Hgeneration.
      change (state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node) in Hnode.
      rewrite Hunused in Hnode; discriminate. }
  assert (Hhigh_after : sched_high_ready_consistency updated.(TskState) updated.(SchedState)).
  { unfold updated, os_sched_save_current_sp; rewrite Hunused; exact Hhigh. }
  exists written, stored; split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcapture Hhook_heap Hhook_step.
  assert (Hfocus_saved : task_stack_key saved.(armv7a_continuation_stack) = armv7a_call_focus_key focus ->
    armv7a_continuation_focus_binding focus saved).
  { intros Heq; specialize (Hfocus Heq); subst focus.
    unfold armv7a_continuation_focus_binding, saved, armv7a_task_save_image, armv7a_call_focus; cbn; tauto. }
  assert (Hsaved_mask : armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr) = 192).
  { unfold saved, armv7a_task_save_image; cbn; rewrite armv7a_task_saved_cpsr_mask; exact Hmask. }
  match type of Hstored with ?P stored => assert (Hcapture_input : P |--
    interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
    external.(os_sched_arch_running) call ** UCOS2_inv sg updated **
    armv7a_task_call_stacks abi updated.(TskState) focus updated.(TskState).(parkedTaskStacks) **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** frame) by entailer! end.
  destruct (armv7a_task_capture_global_call_resources external platform port abi task_abi sg updated
    call saved focus frame stored captured eq_refl Hbinding Hslice Hlive Hfocus_saved Hstored_reads Hsaved_mask
    (Hcapture_input stored Hstored) Hcapture) as [Hmemory [Hsource Hcaptured_owned]].
  assert (Hunchanged : hooked = captured).
  { eapply kernel_heap_execution_deterministic; [exact Hhook_heap|].
    split; [constructor|]; split; reflexivity. }
  subst hooked.
  match type of Hcaptured_owned with ?P captured => assert (Hrestore_input : P |--
    UCOS2_inv sg updated ** task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
    armv7a_task_call_stack_entry abi updated.(TskState) focus (task_stack_key call.(os_sched_call_stack))
      (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
    armv7a_task_call_stacks abi updated.(TskState) focus updated.(TskState).(parkedTaskStacks) **
    (armv7a_task_switch_control task_abi call ** frame)) by entailer! end.
  destruct (os_sched_source_restore_destination_resources external platform port abi task_abi initial
    sg call fragments updated focus frame captured Hsaved Hhigh_after Hnonempty Haddress Hcovered
    (Hrestore_input captured Hcaptured_owned))
    as [incoming [resumed [installed [selected [current [Hdestination [Hselected_fragments
      [Hinstall [Hselected_reads [Hpending Hrestore_resources]]]]]]]]]].
  assert (Hdiffer : incoming.(stackLeaseSlot) <> call.(os_sched_call_stack).(stackLeaseSlot)).
  { intros Heq. destruct Hdestination as [_ [[node [Hnode _]] _]].
    unfold updated, os_sched_save_current_sp in Hnode; rewrite Hunused in Hnode.
    change (state.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node) in Hnode.
    rewrite Heq, Hunused in Hnode; discriminate. }
  exists incoming, resumed, installed, selected, current.
  split; [exact Hsource|]. split; [exact Hdestination|]. split; [exact Hdiffer|].
  split; [exact Hselected_fragments|]. split; [exact Hinstall|]. split; [exact Hselected_reads|].
  split; [exact Hpending|]. intros restored Hrestore. split.
  - exists written, stored, captured, captured, installed.
    exact (conj Hwrites (conj Hload (conj Hstore (conj Hcapture
      (conj Hhook_heap (conj Hhook_step (conj Hinstall Hrestore))))))).
  - exact (Hrestore_resources restored Hrestore).
Qed.
