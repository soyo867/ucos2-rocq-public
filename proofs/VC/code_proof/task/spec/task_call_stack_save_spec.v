Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_context Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_client_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The active generation is absent from the map; its real SP store
    therefore cannot overwrite any saved call's matching-generation SP. *)
Lemma armv7a_task_call_stacks_save_sp : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks node sp outgoing focus stacks,
  tasks.(inUsedTaskStates) outgoing.(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = outgoing.(stackLeaseGeneration) ->
  stacks (task_stack_key outgoing) = None ->
  armv7a_task_call_stacks abi tasks focus stacks |--
  armv7a_task_call_stacks abi
    (glob_task_set_usedtask tasks outgoing.(stackLeaseSlot) (task_set_saved_sp node sp)) focus stacks.
Proof.
  intros external platform port abi tasks node sp outgoing focus stacks Hnode Hgeneration Hnone.
  apply armv7a_task_call_stacks_reindex.
  intros [slot generation] payload updated Hlookup Hupdated Hgen; cbn in Hgen.
  cbn [fst glob_task_set_usedtask inUsedTaskStates] in Hupdated.
  destruct (Z.eqb slot outgoing.(stackLeaseSlot)) eqn:Hslot.
  - apply Z.eqb_eq in Hslot; subst slot; injection Hupdated as Hupdated; subst updated.
    change (node.(taskGeneration) = generation) in Hgen.
    assert (Hkey : (outgoing.(stackLeaseSlot), generation) = task_stack_key outgoing)
      by (unfold task_stack_key; f_equal; congruence).
    rewrite Hkey, Hnone in Hlookup; discriminate.
  - exists updated; auto.
Qed.

(** Same physical save producer, with the pending-call map retained as
    an owned frame through the sixteen stack stores and real TCB-SP store.
    No weak-to-strong map conversion or new CPU resource is used. *)
Lemma task_call_stack_live_save_source :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg tasks node call old_sp cpsr registers lr prefix suffix first old_words focus (frame : Assertion) before,
  tasks.(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  tasks.(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  task_stack_live_coverage tasks (Some (task_stack_key call.(os_sched_call_stack))) ->
  call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  List.length registers = 13%nat ->
  0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) registers ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  (task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) call.(os_sched_call_fragments) **
   task_public_storage sg tasks ** armv7a_task_call_stacks abi tasks focus tasks.(parkedTaskStacks) **
   sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame) before ->
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  let saved := armv7a_task_save_image call old_sp cpsr registers lr fragments in
  let updated := glob_task_set_usedtask tasks call.(os_sched_call_stack).(stackLeaseSlot)
    (task_set_saved_sp node saved.(armv7a_continuation_sp)) in
  exists written after,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes
      (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) saved.(armv7a_continuation_sp)) written after /\
    armv7a_continuation_binding saved /\ armv7a_task_frame_slice saved /\
    task_stack_live_sp updated (task_stack_key call.(os_sched_call_stack)) saved.(armv7a_continuation_sp) /\
    task_stack_live_coverage updated (Some (task_stack_key call.(os_sched_call_stack))) /\
    armv7a_continuation_restore_reads saved after /\
    (task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
       saved.(armv7a_continuation_fragments) ** task_public_storage sg updated **
     armv7a_task_call_stacks abi updated focus updated.(parkedTaskStacks) **
     sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame) after.
Proof.
  intros external platform port abi sg tasks node call old_sp cpsr registers lr prefix suffix first old_words
    focus frame before Hnode Hgen Hnone Hcoverage Hfragments Hlength Hcpsr Hlr Hranges Hsprange Hsp Haddress Hbefore.
  cbv zeta.
  set (fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix).
  set (saved := armv7a_task_save_image call old_sp cpsr registers lr fragments).
  set (updated := glob_task_set_usedtask tasks call.(os_sched_call_stack).(stackLeaseSlot)
    (task_set_saved_sp node saved.(armv7a_continuation_sp))).
  assert (Horder : task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion)
      call.(os_sched_call_fragments) ** task_public_storage sg tasks **
      armv7a_task_call_stacks abi tasks focus tasks.(parkedTaskStacks) **
      sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame |--
    task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion)
      (prefix ++ [(first, first + 16, old_words)] ++ suffix) **
    (task_public_storage sg tasks ** armv7a_task_call_stacks abi tasks focus tasks.(parkedTaskStacks) **
     sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame)).
  { rewrite Hfragments; entailer!. }
  destruct (armv7a_task_save_fragment_execution call old_sp cpsr registers lr prefix suffix first old_words
    _ before Hlength Hcpsr Hlr Hranges Hsp (Horder before Hbefore))
    as [written [Hstores [Hwritten [Hreads Hslice]]]].
  fold fragments in Hwritten, Hslice; fold saved in Hwritten, Hslice.
  assert (Hcurrent : pointer_load sg.(g_OSTCBCur)
    (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written).
  { match type of Hwritten with ?P written =>
      assert (Hload : P |-- sg.(g_OSTCBCur) # Ptr |->
        task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** TT)
    end.
    { entailer!; intros ? ?; exact I. }
    eapply framed_pointer_store_load; exact (Hload written Hwritten). }
  match type of Hwritten with ?P written =>
    assert (Hsplit : P |-- task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) # Ptr |->_ **
      (task_public_storage_without_field sg tasks call.(os_sched_call_stack).(stackLeaseSlot)
         node (TCBCommonField TCBStkPtr) **
       task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
         saved.(armv7a_continuation_fragments) **
       armv7a_task_call_stacks abi tasks focus tasks.(parkedTaskStacks) **
       sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame))
  end.
  { sep_apply_l_atomic (task_public_storage_split_saved_sp sg tasks
      call.(os_sched_call_stack).(stackLeaseSlot) node Hnode).
    cbn [tcb_layout_cell tcb_cell].
    rewrite Haddress.
    sep_apply_l_atomic (store_ptr_undef_store_ptr
      (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) node.(tcbStkPtr)); entailer!. }
  destruct (framed_pointer_store_execution
    (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) saved.(armv7a_continuation_sp)
    _ written Hsprange (Hsplit written Hwritten)) as [after [Hstore Hafter]].
  match type of Hafter with ?P after =>
    assert (Hmerge : P |-- task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** task_public_storage sg updated **
      armv7a_task_call_stacks abi updated focus updated.(parkedTaskStacks) **
      sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame)
  end.
  { rewrite <- Haddress at 1.
    sep_apply_l_atomic (task_public_storage_merge_saved_sp sg tasks
      call.(os_sched_call_stack).(stackLeaseSlot) node saved.(armv7a_continuation_sp)).
    sep_apply_l_atomic (armv7a_task_call_stacks_save_sp external platform port abi tasks
      node saved.(armv7a_continuation_sp) call.(os_sched_call_stack) focus tasks.(parkedTaskStacks) Hnode Hgen Hnone).
    unfold updated; cbn [glob_task_set_usedtask parkedTaskStacks]; entailer!. }
  pose proof (Hmerge after Hafter) as Hresources.
  assert (Hbinding : armv7a_continuation_binding saved) by (apply armv7a_task_save_image_binding; exact Hlength).
  assert (Hlive_sp : task_stack_live_sp updated (task_stack_key call.(os_sched_call_stack))
    saved.(armv7a_continuation_sp)).
  { intros other Hother Hothergen; cbn [updated glob_task_set_usedtask inUsedTaskStates task_stack_key fst] in Hother.
    rewrite Z.eqb_refl in Hother; injection Hother as Hother; subst other; reflexivity. }
  assert (Hcovered : task_stack_live_coverage updated (Some (task_stack_key call.(os_sched_call_stack)))).
  { apply task_stack_save_sp_preserves_coverage; assumption. }
  assert (Hafter_reads : armv7a_continuation_restore_reads saved after).
  { eapply armv7a_task_frame_slice_restore_reads; [exact Hbinding|exact Hslice|].
    assert (Hfocus : task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) ** task_public_storage sg updated **
        armv7a_task_call_stacks abi updated focus updated.(parkedTaskStacks) **
        sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame |--
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) **
      (task_public_storage sg updated ** armv7a_task_call_stacks abi updated focus updated.(parkedTaskStacks) **
       sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame)) by entailer!.
    exact (Hfocus after Hresources). }
  exists written, after; fold fragments saved updated.
  split; [exact Hstores|]. split; [exact Hcurrent|]. split; [exact Hstore|].
  split; [exact Hbinding|]. split; [exact Hslice|]. split; [exact Hlive_sp|].
  split; [exact Hcovered|]. split; assumption.
Qed.

(** A different running task may enter OSCtxSw while this call is parked.
    Its actual save/capture creates the outgoing entry and preserves the
    existing pending caller. This is the live-current non-VFP branch, not
    a statement that an arbitrary hook preserves these resources. *)
Lemma armv7a_task_save_keeps_pending_call :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    (task_abi : Armv7aTaskContextABI external platform port abi)
    sg tasks node call old_sp cpsr registers lr prefix suffix first old_words focus payload (frame : Assertion) before,
  tasks.(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  tasks.(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tasks.(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
  task_stack_live_coverage tasks (Some (task_stack_key call.(os_sched_call_stack))) ->
  call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  List.length registers = 13%nat ->
  0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) registers ->
  armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  (kernel_call_execution_owned external platform call 192 ** task_public_storage sg tasks **
   armv7a_task_call_stacks abi tasks focus tasks.(parkedTaskStacks) **
   sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame) before ->
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  let saved := armv7a_task_save_image call old_sp cpsr registers lr fragments in
  let updated := glob_task_set_usedtask tasks call.(os_sched_call_stack).(stackLeaseSlot)
    (task_set_saved_sp node saved.(armv7a_continuation_sp)) in
  exists written stored,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      saved.(armv7a_continuation_sp)) written stored /\
    task_stack_live_coverage updated (Some (task_stack_key call.(os_sched_call_stack))) /\
    (forall captured, armv7a_task_capture_transition task_abi call saved stored captured ->
      captured.(ConAssertion.s_mem) = stored.(ConAssertion.s_mem) /\
      external.(os_sched_arch_save_source) call saved.(armv7a_continuation_sp) fragments /\
      (armv7a_task_switch_control task_abi call **
       task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
       task_public_storage sg updated **
       armv7a_task_call_stacks abi updated focus updated.(parkedTaskStacks) **
       armv7a_task_call_stack_entry abi updated focus (task_stack_key call.(os_sched_call_stack))
         (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
       sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame) captured).
Proof.
  intros external platform port abi task_abi sg tasks node call old_sp cpsr registers lr prefix suffix first
    old_words focus payload frame before Hnode Hgen Hnone Hpending Hcoverage Hfragments Hlength Hcpsr Hlr Hranges Hmask Hsprange
    Hsp Haddress Hbefore.
  assert (Hother : task_stack_key call.(os_sched_call_stack) <> armv7a_call_focus_key focus) by congruence.
  cbv zeta.
  set (fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix).
  set (saved := armv7a_task_save_image call old_sp cpsr registers lr fragments).
  set (updated := glob_task_set_usedtask tasks call.(os_sched_call_stack).(stackLeaseSlot)
    (task_set_saved_sp node saved.(armv7a_continuation_sp))).
  match type of Hbefore with ?P before =>
    assert (Horder : P |-- task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion)
      call.(os_sched_call_fragments) ** task_public_storage sg tasks **
      armv7a_task_call_stacks abi tasks focus tasks.(parkedTaskStacks) **
      sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) **
      (interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
       external.(os_sched_arch_running) call ** frame))
  end.
  { unfold kernel_call_execution_owned, os_sched_context_resources; entailer!. }
  destruct (task_call_stack_live_save_source external platform port abi sg tasks node call old_sp cpsr registers
    lr prefix suffix first old_words focus _ before Hnode Hgen Hnone Hcoverage Hfragments Hlength Hcpsr Hlr
    Hranges Hsprange Hsp Haddress (Horder before Hbefore))
    as [written [stored [Hstores [Hload [Hstore [Hbinding [Hslice [Hlive [Hcovered [Hreads Hstored]]]]]]]]]].
  fold fragments saved updated in Hstored, Hbinding, Hslice, Hlive, Hreads, Hstore, Hcovered.
  exists written, stored; fold fragments saved updated.
  split; [exact Hstores|]. split; [exact Hload|]. split; [exact Hstore|].
  split; [exact Hcovered|]. intros captured Hcapture.
  match type of Hstored with ?P stored =>
    assert (Hcapture_input : P |--
      interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
      external.(os_sched_arch_running) call **
      (task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
       task_public_storage sg updated ** armv7a_task_call_stacks abi updated focus updated.(parkedTaskStacks) **
       sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame))
  end.
  { unfold saved, armv7a_task_save_image; cbn; entailer!. }
  assert (Hsaved_mask : armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr) = 192).
  { unfold saved, armv7a_task_save_image; cbn; rewrite armv7a_task_saved_cpsr_mask; exact Hmask. }
  destruct (armv7a_task_capture_resources _ _ _ abi task_abi call saved _ stored captured
    eq_refl Hreads Hsaved_mask (Hcapture_input stored Hstored) Hcapture)
    as [Hmemory [Hsource Hcaptured]].
  split; [exact Hmemory|]. split; [exact Hsource|].
  match type of Hcaptured with ?P captured =>
    assert (Hclose : P |-- armv7a_task_switch_control task_abi call **
      task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
      task_public_storage sg updated ** armv7a_task_call_stacks abi updated focus updated.(parkedTaskStacks) **
      armv7a_task_call_stack_entry abi updated focus (task_stack_key call.(os_sched_call_stack))
        (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
      sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame)
  end.
  { assert (Hentry : armv7a_dormant_continuation abi saved |--
      armv7a_task_call_stack_entry abi updated focus (task_stack_key call.(os_sched_call_stack))
        (call.(os_sched_call_stack).(stackLeaseRegion), fragments)).
    { unfold armv7a_task_call_stack_entry; destruct task_stack_key_eq_dec; [contradiction|].
      change (armv7a_task_continuation_resource abi saved |--
        armv7a_task_stack_entry abi updated (task_stack_key saved.(armv7a_continuation_stack))
          (saved.(armv7a_continuation_stack).(stackLeaseRegion), saved.(armv7a_continuation_fragments))).
      apply armv7a_task_stack_entry_resources; assumption. }
    sep_apply_l_atomic Hentry; entailer!. }
  exact (Hclose captured Hcaptured).
Qed.
