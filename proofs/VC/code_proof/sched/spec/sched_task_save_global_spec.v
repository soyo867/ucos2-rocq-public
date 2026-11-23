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
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_save_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Reuse the real TCB-SP store on the complete kernel owner. The logical
    validity proof and physical reconstruction concern the same successor
    state. The parked call map is reindexed, not recreated or weakened. *)
Lemma os_sched_store_live_sp_call_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state lease node sp
  focus (frame : Assertion) before,
  state.(TskState).(inUsedTaskStates) lease.(stackLeaseSlot) = Some node ->
  node.(taskID) = lease.(stackLeaseSlot) ->
  node.(taskGeneration) = lease.(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key lease) = None ->
  tcb_field_address (task_slot_addr sg lease.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg lease.(stackLeaseSlot) ->
  0 <= sp < 4294967296 ->
  (UCOS2_inv sg state **
   armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame) before ->
  exists after,
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg lease.(stackLeaseSlot)) sp) before after /\
    (UCOS2_inv sg (os_sched_save_current_sp state lease.(stackLeaseSlot) sp) **
     armv7a_task_call_stacks abi (os_sched_save_current_sp state lease.(stackLeaseSlot) sp).(TskState)
       focus (os_sched_save_current_sp state lease.(stackLeaseSlot) sp).(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi sg state lease node sp focus frame before
    Hnode Hid Hgen Hnone Haddress Hsp Hbefore.
  assert (Hopen : UCOS2_inv sg state **
      armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame |--
    coq_prop (UCOS2_state_inv sg state) &&
      (UCOS2_raw_rep sg state **
       (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold UCOS2_inv; entailer!. }
  destruct (Hopen before Hbefore) as [Hvalid [owned [rest [Hjoin [Hraw Hrest]]]]].
  destruct (armv7a_irq_store_live_sp_raw_post sg state lease.(stackLeaseSlot) node sp owned
    Hnode Haddress Hsp Hraw) as [written [Hwrite Hwritten]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hwrite Hjoin) as [after [Hrun Hafter]].
  assert (Hupdated : UCOS2_state_inv sg (os_sched_save_current_sp state lease.(stackLeaseSlot) sp)).
  { unfold os_sched_save_current_sp; rewrite Hnode.
    exact (os_sched_save_live_sp_preserves_validity sg state node sp lease Hvalid Hnode Hid Hgen Hnone). }
  assert (Hclose : UCOS2_raw_rep sg (os_sched_save_current_sp state lease.(stackLeaseSlot) sp) **
      (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame) |--
    UCOS2_inv sg (os_sched_save_current_sp state lease.(stackLeaseSlot) sp) **
      armv7a_task_call_stacks abi (os_sched_save_current_sp state lease.(stackLeaseSlot) sp).(TskState)
        focus (os_sched_save_current_sp state lease.(stackLeaseSlot) sp).(TskState).(parkedTaskStacks) ** frame).
  { unfold UCOS2_inv; sep_apply_l_atomic (armv7a_task_call_stacks_save_sp external platform port abi
      state.(TskState) node sp lease focus state.(TskState).(parkedTaskStacks) Hnode Hgen Hnone).
    unfold os_sched_save_current_sp in Hupdated |- *; rewrite Hnode in Hupdated |- *.
    cbn [replace_TskS TskState glob_task_set_usedtask parkedTaskStacks]; entailer!. }
  exists after; split; [exact Hrun|].
  apply Hclose; exists written, rest; tauto.
Qed.

(** Source order is the real non-VFP OSCtxSw save: two LR stores, R0--R12,
    corrected CPSR, OSTCBCur read and TCB-SP store. Unlike the field-local
    producer, this result reconstructs the entire kernel invariant on the
    actual final heap. It is still the LIVE-current save prefix, not the
    intervening application hook, a retired caller or eventual return. *)
Lemma armv7a_task_save_global_resources :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg state node call old_sp cpsr registers lr prefix suffix first old_words
    focus (frame : Assertion) before,
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
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  (task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) call.(os_sched_call_fragments) **
   UCOS2_inv sg state ** armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
   frame) before ->
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
    armv7a_continuation_binding saved /\ armv7a_task_frame_slice saved /\
    task_stack_live_sp updated.(TskState) (task_stack_key call.(os_sched_call_stack)) saved.(armv7a_continuation_sp) /\
    task_stack_live_coverage updated.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) /\
    armv7a_continuation_restore_reads saved stored /\
    (UCOS2_inv sg updated **
     armv7a_task_call_stacks abi updated.(TskState) focus updated.(TskState).(parkedTaskStacks) **
     task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
       saved.(armv7a_continuation_fragments) ** frame) stored.
Proof.
  intros external platform port abi sg state node call old_sp cpsr registers lr prefix suffix first
    old_words focus frame before Hcurrent Hnode Hid Hgen Hnone Hcoverage Hfragments Hlength Hcpsr Hlr
    Hranges Hsprange Hsp Haddress Hbefore.
  cbv zeta.
  set (fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix).
  set (saved := armv7a_task_save_image call old_sp cpsr registers lr fragments).
  set (updated := os_sched_save_current_sp state call.(os_sched_call_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_sp)).
  match type of Hbefore with ?P before =>
    assert (Horder : P |-- task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion)
      (prefix ++ [(first, first + 16, old_words)] ++ suffix) **
      (UCOS2_inv sg state **
       armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame))
  end.
  { rewrite Hfragments; entailer!. }
  destruct (armv7a_task_save_fragment_execution call old_sp cpsr registers lr prefix suffix first old_words
    _ before Hlength Hcpsr Hlr Hranges Hsp (Horder before Hbefore))
    as [written [Hwrites [Hwritten [Hreads Hslice]]]].
  fold fragments saved in Hwritten, Hreads, Hslice.
  assert (Hload : pointer_load sg.(g_OSTCBCur)
    (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written).
  { match type of Hwritten with ?P written =>
      assert (Hcell : P |-- sg.(g_OSTCBCur) # Ptr |->
        task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** TT)
    end.
    { unfold UCOS2_inv, UCOS2_raw_rep, sched_raw_rep, sched_physical_rep;
        rewrite Hcurrent; cbn [encode_task_link]; entailer!; intros ? ?; exact I. }
    eapply framed_pointer_store_load; exact (Hcell written Hwritten). }
  match type of Hwritten with ?P written =>
    assert (Hstore_input : P |-- UCOS2_inv sg state **
      armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
      (task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) ** frame))
  end.
  { unfold saved, armv7a_task_save_image; cbn; entailer!. }
  destruct (os_sched_store_live_sp_call_resources external platform port abi sg state
    call.(os_sched_call_stack) node saved.(armv7a_continuation_sp) focus _ written
    Hnode Hid Hgen Hnone Haddress Hsprange (Hstore_input written Hwritten))
    as [stored [Hstore Hstored]].
  fold updated in Hstored.
  assert (Hbinding : armv7a_continuation_binding saved)
    by (apply armv7a_task_save_image_binding; exact Hlength).
  assert (Hlive : task_stack_live_sp updated.(TskState) (task_stack_key call.(os_sched_call_stack))
    saved.(armv7a_continuation_sp)).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode.
    intros other Hother Hothergen;
      cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates task_stack_key fst] in Hother.
    rewrite Z.eqb_refl in Hother; injection Hother as Hother; subst other; reflexivity. }
  assert (Hcovered : task_stack_live_coverage updated.(TskState)
    (Some (task_stack_key call.(os_sched_call_stack)))).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode.
    apply task_stack_save_sp_preserves_coverage; assumption. }
  match type of Hstored with ?P stored =>
    assert (Hpost : P |-- UCOS2_inv sg updated **
      armv7a_task_call_stacks abi updated.(TskState) focus updated.(TskState).(parkedTaskStacks) **
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) ** frame)
  end.
  { entailer!. }
  pose proof (Hpost stored Hstored) as Hresources.
  assert (Hstored_reads : armv7a_continuation_restore_reads saved stored).
  { eapply armv7a_task_frame_slice_restore_reads; [exact Hbinding|exact Hslice|].
    match type of Hresources with ?P stored =>
      assert (Hfocus : P |-- task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) **
        (UCOS2_inv sg updated **
         armv7a_task_call_stacks abi updated.(TskState) focus updated.(TskState).(parkedTaskStacks) ** frame))
    end.
    { entailer!. }
    exact (Hfocus stored Hresources). }
  exists written, stored; fold fragments saved updated.
  exact (conj Hwrites (conj Hload (conj Hstore (conj Hbinding
    (conj Hslice (conj Hlive (conj Hcovered (conj Hstored_reads Hresources)))))))).
Qed.

(** Authority exchange after the physical save. The focus may be this
    outgoing call or a different already parked call. In the former case
    the supplied equality concerns the descriptor actually just written,
    not an identity inferred from a matching TCB address. No kernel
    preservation law is added to the approved CPU contract. *)
Lemma armv7a_task_capture_global_call_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  sg state call saved focus (frame : Assertion) before after,
  saved.(armv7a_continuation_call) = Some call ->
  armv7a_continuation_binding saved ->
  armv7a_task_frame_slice saved ->
  task_stack_live_sp state.(TskState) (task_stack_key saved.(armv7a_continuation_stack))
    saved.(armv7a_continuation_sp) ->
  (task_stack_key saved.(armv7a_continuation_stack) = armv7a_call_focus_key focus ->
    armv7a_continuation_focus_binding focus saved) ->
  armv7a_continuation_restore_reads saved before ->
  armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr) = 192 ->
  (interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
   external.(os_sched_arch_running) call ** UCOS2_inv sg state **
   armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
   task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
     saved.(armv7a_continuation_fragments) ** frame) before ->
  armv7a_task_capture_transition task_abi call saved before after ->
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  external.(os_sched_arch_save_source) call saved.(armv7a_continuation_sp)
    saved.(armv7a_continuation_fragments) /\
  (UCOS2_inv sg state **
   armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
   task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
     saved.(armv7a_continuation_fragments) **
   armv7a_task_call_stack_entry abi state.(TskState) focus (task_stack_key saved.(armv7a_continuation_stack))
     (saved.(armv7a_continuation_stack).(stackLeaseRegion), saved.(armv7a_continuation_fragments)) **
   armv7a_task_switch_control task_abi call ** frame) after.
Proof.
  intros external platform port abi task_abi sg state call saved focus frame before after
    Hcall Hbinding Hslice Hlive Hfocus Hreads Hmask Hbefore Hcapture.
  match type of Hbefore with ?P before =>
    assert (Horder : P |--
      interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
      external.(os_sched_arch_running) call **
      (UCOS2_inv sg state **
       armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
       task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
         saved.(armv7a_continuation_fragments) ** frame))
  end.
  { entailer!. }
  destruct (armv7a_task_capture_resources _ _ _ abi task_abi call saved _ before after
    Hcall Hreads Hmask (Horder before Hbefore) Hcapture) as [Hmemory [Hsource Hafter]].
  assert (Hentry : armv7a_dormant_continuation abi saved |--
    armv7a_task_call_stack_entry abi state.(TskState) focus
      (task_stack_key saved.(armv7a_continuation_stack))
      (saved.(armv7a_continuation_stack).(stackLeaseRegion), saved.(armv7a_continuation_fragments))).
  { unfold armv7a_task_call_stack_entry; destruct task_stack_key_eq_dec as [Heq|Hneq].
    - Exists saved; entailer!.
    - unfold armv7a_task_stack_entry; Exists saved.
      unfold armv7a_task_continuation_resource; rewrite Hcall; entailer!. }
  match type of Hafter with ?P after =>
    assert (Hclose : P |-- UCOS2_inv sg state **
      armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) **
      armv7a_task_call_stack_entry abi state.(TskState) focus (task_stack_key saved.(armv7a_continuation_stack))
        (saved.(armv7a_continuation_stack).(stackLeaseRegion), saved.(armv7a_continuation_fragments)) **
      armv7a_task_switch_control task_abi call ** frame)
  end.
  { sep_apply_l_atomic Hentry; entailer!. }
  exact (conj Hmemory (conj Hsource (Hclose after Hafter))).
Qed.

(** Whole save-side producer consumed at the actual hook entry: the
    complete global owner, every parked continuation, outgoing saved
    bytes and dormant call all refer to the SAME physical execution.
    Choosing focus = armv7a_call_focus call lr lr handles a first save;
    an existing foreign focus also works without relabelling its entry. *)
Lemma armv7a_task_save_global_call :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    (task_abi : Armv7aTaskContextABI external platform port abi)
    sg state node call old_sp cpsr registers lr prefix suffix first old_words
    focus (frame : Assertion) before,
  state.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  task_stack_live_coverage state.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  (task_stack_key call.(os_sched_call_stack) = armv7a_call_focus_key focus ->
    focus = armv7a_call_focus call lr lr) ->
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
   armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame) before ->
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
    task_stack_live_coverage updated.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) /\
    (forall captured, armv7a_task_capture_transition task_abi call saved stored captured ->
      captured.(ConAssertion.s_mem) = stored.(ConAssertion.s_mem) /\
      external.(os_sched_arch_save_source) call saved.(armv7a_continuation_sp) fragments /\
      (UCOS2_inv sg updated **
       armv7a_task_call_stacks abi updated.(TskState) focus updated.(TskState).(parkedTaskStacks) **
       task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
       armv7a_task_call_stack_entry abi updated.(TskState) focus (task_stack_key call.(os_sched_call_stack))
         (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
       armv7a_task_switch_control task_abi call ** frame) captured).
Proof.
  intros external platform port abi task_abi sg state node call old_sp cpsr registers lr prefix suffix first
    old_words focus frame before Hcurrent Hnode Hid Hgen Hnone Hcoverage Hfocus Hfragments Hlength Hcpsr Hlr
    Hranges Hmask Hsprange Hsp Haddress Hbefore.
  cbv zeta.
  set (fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix).
  set (saved := armv7a_task_save_image call old_sp cpsr registers lr fragments).
  set (updated := os_sched_save_current_sp state call.(os_sched_call_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_sp)).
  match type of Hbefore with ?P before =>
    assert (Horder : P |-- task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion)
      call.(os_sched_call_fragments) ** UCOS2_inv sg state **
      armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
      (interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
       external.(os_sched_arch_running) call ** frame))
  end.
  { unfold kernel_call_execution_owned, os_sched_context_resources; entailer!. }
  destruct (armv7a_task_save_global_resources external platform port abi sg state node call old_sp cpsr
    registers lr prefix suffix first old_words focus _ before Hcurrent Hnode Hid Hgen Hnone Hcoverage
    Hfragments Hlength Hcpsr Hlr Hranges Hsprange Hsp Haddress (Horder before Hbefore))
    as [written [stored [Hwrites [Hload [Hstore [Hbinding [Hslice [Hlive [Hcovered [Hreads Hstored]]]]]]]]]].
  fold fragments saved updated in Hstore, Hbinding, Hslice, Hlive, Hcovered, Hreads, Hstored.
  exists written, stored; fold fragments saved updated.
  split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|]. split; [exact Hcovered|].
  intros captured Hcapture.
  assert (Hfocus_saved : task_stack_key saved.(armv7a_continuation_stack) = armv7a_call_focus_key focus ->
    armv7a_continuation_focus_binding focus saved).
  { intros Heq; specialize (Hfocus Heq); subst focus.
    unfold armv7a_continuation_focus_binding, saved, armv7a_task_save_image, armv7a_call_focus; cbn; tauto. }
  assert (Hsaved_mask : armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr) = 192).
  { unfold saved, armv7a_task_save_image; cbn; rewrite armv7a_task_saved_cpsr_mask; exact Hmask. }
  match type of Hstored with ?P stored =>
    assert (Hcapture_input : P |--
      interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
      external.(os_sched_arch_running) call ** UCOS2_inv sg updated **
      armv7a_task_call_stacks abi updated.(TskState) focus updated.(TskState).(parkedTaskStacks) **
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) ** frame)
  end.
  { entailer!. }
  exact (armv7a_task_capture_global_call_resources external platform port abi task_abi sg updated
    call saved focus frame stored captured eq_refl Hbinding Hslice Hlive Hfocus_saved Hreads Hsaved_mask
    (Hcapture_input stored Hstored) Hcapture).
Qed.
