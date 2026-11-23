Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Updating the active TCB's SP preserves every already parked descriptor,
    including its exact local cut. The active generation is absent from the
    map. A retired entry at the same slot but another generation therefore
    imposes no SP constraint on this write. No entry is forgotten here. *)
Lemma kernel_saved_continuation_map_save_sp : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks node sp outgoing
  (local : Armv7aContinuation -> Assertion) stacks,
  tasks.(inUsedTaskStates) outgoing.(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = outgoing.(stackLeaseGeneration) ->
  stacks (task_stack_key outgoing) = None ->
  store_parked_continuations (kernel_saved_continuation_entry abi tasks local) stacks |--
  store_parked_continuations
    (kernel_saved_continuation_entry abi
      (glob_task_set_usedtask tasks outgoing.(stackLeaseSlot) (task_set_saved_sp node sp)) local) stacks.
Proof.
  intros external platform port abi tasks node sp outgoing local stacks Hnode Hgeneration Hnone.
  unfold store_parked_continuations.
  apply TaskFieldStorage.store_map_mono; intros [slot generation] payload Hlookup.
  unfold kernel_saved_continuation_entry; Intros descriptor.
  assert (Hlive : task_stack_live_sp tasks (slot, generation)
    descriptor.(armv7a_continuation_sp)) by tauto.
  assert (Hupdated : task_stack_live_sp
    (glob_task_set_usedtask tasks outgoing.(stackLeaseSlot) (task_set_saved_sp node sp))
    (slot, generation) descriptor.(armv7a_continuation_sp)).
  { intros current Hcurrent Hgen; cbn in Hgen.
    cbn [fst glob_task_set_usedtask inUsedTaskStates] in Hcurrent.
    destruct (Z.eqb slot outgoing.(stackLeaseSlot)) eqn:Hslot.
    - apply Z.eqb_eq in Hslot; subst slot; injection Hcurrent as Hcurrent; subst current.
      change (node.(taskGeneration) = generation) in Hgen.
      assert (Hkey : (outgoing.(stackLeaseSlot), generation) = task_stack_key outgoing)
        by (unfold task_stack_key; f_equal; congruence).
      rewrite Hkey, Hnone in Hlookup; discriminate.
    - apply Hlive; assumption. }
  Exists descriptor; entailer!.
Qed.

(** The physical TCB-SP write on the complete global owner. All descriptor
    resources are carried as a disjoint frame of this masked memory step,
    then reindexed using the absent active generation. *)
Lemma kernel_saved_continuation_store_live_sp_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state lease node sp
  (local : Armv7aContinuation -> Assertion) (frame : Assertion) before,
  state.(TskState).(inUsedTaskStates) lease.(stackLeaseSlot) = Some node ->
  node.(taskID) = lease.(stackLeaseSlot) ->
  node.(taskGeneration) = lease.(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key lease) = None ->
  tcb_field_address (task_slot_addr sg lease.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg lease.(stackLeaseSlot) ->
  0 <= sp < 4294967296 ->
  (UCOS2_inv sg state **
   store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
     state.(TskState).(parkedTaskStacks) ** frame) before ->
  exists after,
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg lease.(stackLeaseSlot)) sp) before after /\
    (UCOS2_inv sg (os_sched_save_current_sp state lease.(stackLeaseSlot) sp) **
     store_parked_continuations
       (kernel_saved_continuation_entry abi
         (os_sched_save_current_sp state lease.(stackLeaseSlot) sp).(TskState) local)
       (os_sched_save_current_sp state lease.(stackLeaseSlot) sp).(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi sg state lease node sp local frame before
    Hnode Hid Hgen Hnone Haddress Hsp Hbefore.
  match type of Hbefore with ?P before => assert (Hopen : P |--
    coq_prop (UCOS2_state_inv sg state) &&
      (UCOS2_raw_rep sg state **
       (store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
          state.(TskState).(parkedTaskStacks) ** frame))) end.
  { unfold UCOS2_inv; entailer!. }
  destruct (Hopen before Hbefore) as [Hvalid [owned [rest [Hjoin [Hraw Hrest]]]]].
  destruct (armv7a_irq_store_live_sp_raw_post sg state lease.(stackLeaseSlot) node sp owned
    Hnode Haddress Hsp Hraw) as [written [Hwrite Hwritten]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hwrite Hjoin) as [after [Hrun Hafter]].
  assert (Hupdated : UCOS2_state_inv sg (os_sched_save_current_sp state lease.(stackLeaseSlot) sp)).
  { unfold os_sched_save_current_sp; rewrite Hnode.
    exact (os_sched_save_live_sp_preserves_validity sg state node sp lease Hvalid Hnode Hid Hgen Hnone). }
  assert (Hclose : UCOS2_raw_rep sg (os_sched_save_current_sp state lease.(stackLeaseSlot) sp) **
      (store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
         state.(TskState).(parkedTaskStacks) ** frame) |--
    UCOS2_inv sg (os_sched_save_current_sp state lease.(stackLeaseSlot) sp) **
    store_parked_continuations
      (kernel_saved_continuation_entry abi
        (os_sched_save_current_sp state lease.(stackLeaseSlot) sp).(TskState) local)
      (os_sched_save_current_sp state lease.(stackLeaseSlot) sp).(TskState).(parkedTaskStacks) ** frame).
  { unfold UCOS2_inv.
    sep_apply_l_atomic (kernel_saved_continuation_map_save_sp external platform port abi
      state.(TskState) node sp lease local state.(TskState).(parkedTaskStacks) Hnode Hgen Hnone).
    unfold os_sched_save_current_sp in Hupdated |- *; rewrite Hnode in Hupdated |- *.
    cbn [replace_TskS TskState glob_task_set_usedtask parkedTaskStacks]; entailer!. }
  exists after; split; [exact Hrun|].
  apply Hclose; exists written, rest; tauto.
Qed.

(** Actual non-VFP OSCtxSw producer: sixteen stack stores, OSTCBCur read,
    TCB-SP store, then the already approved authority exchange. The local
    predicate is owned BEFORE these steps and is put beside this exact
    descriptor, so later generic park/take can recover the same cut.

    For a Scheduler cut, [local descriptor] can own its own Save token and
    inside handle; an IRQ producer instead retains the interrupted C cut.
    This lemma does not classify a phase from PC/CPSR, promise future return,
    or reconstruct current invocation registration from a dormant owner. *)
Lemma kernel_task_save_continuation_resources :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    (task_abi : Armv7aTaskContextABI external platform port abi)
    sg state node call old_sp cpsr registers lr prefix suffix first old_words
    (local : Armv7aContinuation -> Assertion) (frame : Assertion) before,
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  let descriptor := armv7a_task_save_image call old_sp cpsr registers lr fragments in
  let updated := os_sched_save_current_sp state call.(os_sched_call_stack).(stackLeaseSlot)
    descriptor.(armv7a_continuation_sp) in
  state.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  task_stack_live_coverage state.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  List.length registers = 13%nat ->
  0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) registers ->
  armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  (kernel_call_execution_owned external platform call 192 ** UCOS2_inv sg state **
   store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
     state.(TskState).(parkedTaskStacks) ** local descriptor ** frame) before ->
  exists written stored,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      descriptor.(armv7a_continuation_sp)) written stored /\
    task_stack_live_coverage updated.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) /\
    (forall captured, armv7a_task_capture_transition task_abi call descriptor stored captured ->
      captured.(ConAssertion.s_mem) = stored.(ConAssertion.s_mem) /\
      external.(os_sched_arch_save_source) call descriptor.(armv7a_continuation_sp) fragments /\
      (UCOS2_inv sg updated **
       task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
       kernel_saved_continuation_entry abi updated.(TskState) local
         (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
       store_parked_continuations (kernel_saved_continuation_entry abi updated.(TskState) local)
         updated.(TskState).(parkedTaskStacks) **
       armv7a_task_switch_control task_abi call ** frame) captured).
Proof.
  intros external platform port abi task_abi sg state node call old_sp cpsr registers lr prefix suffix first
    old_words local frame before fragments descriptor updated Hcurrent Hnode Hid Hgen Hnone Hcoverage Hfragments
    Hlength Hcpsr Hlr Hranges Hmask Hsprange Hsp Haddress Hpre.
  match type of Hpre with ?P before => assert (Horder : P |--
    task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion)
      (prefix ++ [(first, first + 16, old_words)] ++ suffix) **
    (UCOS2_inv sg state **
     store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
       state.(TskState).(parkedTaskStacks) **
     interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
     external.(os_sched_arch_running) call ** local descriptor ** frame)) end.
  { unfold kernel_call_execution_owned, os_sched_context_resources; rewrite Hfragments; entailer!. }
  destruct (armv7a_task_save_fragment_execution call old_sp cpsr registers lr prefix suffix first old_words
    _ before Hlength Hcpsr Hlr Hranges Hsp (Horder before Hpre))
    as [written [Hwrites [Hwritten [Hreads Hslice]]]].
  fold fragments descriptor in Hwritten, Hreads, Hslice.
  assert (Hload : pointer_load sg.(g_OSTCBCur)
    (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written).
  { match type of Hwritten with ?P written => assert (Hcell : P |--
      sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** TT) end.
    { unfold UCOS2_inv, UCOS2_raw_rep, sched_raw_rep, sched_physical_rep;
        rewrite Hcurrent; cbn [encode_task_link]; entailer!; intros ? ?; exact I. }
    eapply framed_pointer_store_load; exact (Hcell written Hwritten). }
  match type of Hwritten with ?P written => assert (Hstore_input : P |--
    UCOS2_inv sg state **
    store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
      state.(TskState).(parkedTaskStacks) **
    (task_stack_fragments_rep descriptor.(armv7a_continuation_stack).(stackLeaseRegion)
       descriptor.(armv7a_continuation_fragments) **
     interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
     external.(os_sched_arch_running) call ** local descriptor ** frame)) end.
  { unfold descriptor, armv7a_task_save_image; cbn; entailer!. }
  destruct (kernel_saved_continuation_store_live_sp_resources external platform port abi sg state
    call.(os_sched_call_stack) node descriptor.(armv7a_continuation_sp) local _ written
    Hnode Hid Hgen Hnone Haddress Hsprange (Hstore_input written Hwritten))
    as [stored [Hstore Hstored]].
  fold updated in Hstored.
  assert (Hbinding : armv7a_continuation_binding descriptor)
    by (apply armv7a_task_save_image_binding; exact Hlength).
  assert (Hlive : task_stack_live_sp updated.(TskState) (task_stack_key call.(os_sched_call_stack))
    descriptor.(armv7a_continuation_sp)).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode.
    intros other Hother Hothergen;
      cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates task_stack_key fst] in Hother.
    rewrite Z.eqb_refl in Hother; injection Hother as Hother; subst other; reflexivity. }
  assert (Hcovered : task_stack_live_coverage updated.(TskState)
    (Some (task_stack_key call.(os_sched_call_stack)))).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode.
    apply task_stack_save_sp_preserves_coverage; assumption. }
  assert (Hstored_reads : armv7a_continuation_restore_reads descriptor stored).
  { eapply armv7a_task_frame_slice_restore_reads; [exact Hbinding|exact Hslice|].
    match type of Hstored with ?P stored => assert (Hfocus : P |--
      task_stack_fragments_rep descriptor.(armv7a_continuation_stack).(stackLeaseRegion)
        descriptor.(armv7a_continuation_fragments) **
      (UCOS2_inv sg updated **
       store_parked_continuations (kernel_saved_continuation_entry abi updated.(TskState) local)
         updated.(TskState).(parkedTaskStacks) **
       interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
       external.(os_sched_arch_running) call ** local descriptor ** frame)) by entailer! end.
    exact (Hfocus stored Hstored). }
  exists written, stored.
  split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  split; [exact Hcovered|]. intros captured Hcapture.
  match type of Hstored with ?P stored => assert (Hcapture_input : P |--
    interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
    external.(os_sched_arch_running) call ** local descriptor **
    (UCOS2_inv sg updated **
     store_parked_continuations (kernel_saved_continuation_entry abi updated.(TskState) local)
       updated.(TskState).(parkedTaskStacks) **
     task_stack_fragments_rep descriptor.(armv7a_continuation_stack).(stackLeaseRegion)
       descriptor.(armv7a_continuation_fragments) ** frame)) by entailer! end.
  assert (Hdescriptor_mask : armv7a_irq_fiq_mask descriptor.(armv7a_continuation_cpsr) = 192).
  { unfold descriptor, armv7a_task_save_image; cbn; rewrite armv7a_task_saved_cpsr_mask; exact Hmask. }
  destruct (kernel_saved_continuation_capture_source external platform port abi task_abi
    updated.(TskState) local call descriptor _ stored captured
    eq_refl Hbinding Hslice Hlive Hstored_reads Hdescriptor_mask
    (Hcapture_input stored Hstored) Hcapture)
    as [Hmemory [Hsource Hcaptured]].
  match type of Hcaptured with ?P captured => assert (Hclose : P |--
    UCOS2_inv sg updated ** task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
    kernel_saved_continuation_entry abi updated.(TskState) local
      (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
    store_parked_continuations (kernel_saved_continuation_entry abi updated.(TskState) local)
      updated.(TskState).(parkedTaskStacks) ** armv7a_task_switch_control task_abi call ** frame) end.
  { assert (Hlease : descriptor.(armv7a_continuation_stack) = call.(os_sched_call_stack))
      by reflexivity.
    assert (Hdescriptor_fragments : descriptor.(armv7a_continuation_fragments) = fragments)
      by reflexivity.
    rewrite Hlease, Hdescriptor_fragments; entailer!. }
  exact (conj Hmemory (conj Hsource (Hclose captured Hcaptured))).
Qed.
