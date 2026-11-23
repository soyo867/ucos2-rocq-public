Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Task-level OSCtxSw, after its real frame save, outgoing TCB-SP store
    and OSTaskSwHook. The source now reads/writes the priority/current
    caches and reads the selected TCB SP. Only these masked memory steps
    admit this ordinary disjoint frame: it is not an interference rule
    across the earlier hook or a later switch/Restore interval. *)
Lemma os_sched_install_heap_take_destination_frame :
  forall external sg context saved hooked incoming resumed (frame : Assertion) heap,
  os_sched_saved_stack_binding context saved hooked ->
  os_sched_destination_binding external context saved hooked incoming resumed ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  ((UCOS2_inv sg hooked **
    task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) saved) ** frame) heap ->
  exists final sp,
    sched_install_heap_fragment sg heap final (task_slot_addr sg incoming.(stackLeaseSlot)) sp /\
    (coq_prop (task_current_at (os_sched_install_context context saved incoming hooked)
        incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
      external.(os_sched_arch_restore_source) incoming sp resumed) &&
     ((UCOS2_inv sg (os_sched_install_context context saved incoming hooked) **
       task_stack_fragments_rep incoming.(stackLeaseRegion) resumed) ** frame)) final.
Proof.
  intros external sg context saved hooked incoming resumed frame heap Hsaved Hdestination Haddress
    [owned [rest [Hjoin [Hbefore Hframe]]]].
  destruct (os_sched_install_heap_take_destination external sg context saved hooked incoming resumed
    owned Hsaved Hdestination Haddress Hbefore) as [after [sp [Hrun [Hfacts Hafter]]]].
  destruct (sched_install_heap_fragment_frame _ _ _ _ _ _ _ Hrun Hjoin)
    as [final [Hwhole Hfinal]].
  exists final, sp; split; [exact Hwhole|]. split; [exact Hfacts|].
  exists after, rest; split; [exact Hfinal|]; split; assumption.
Qed.

(** The map entry may retain additional source facts, such as the saved
    SP associated with a matching live TCB generation. Do not erase those
    facts merely to use the basic continuation interface. The parameter
    is an actual owned assertion, not an assumed preservation theorem.
    Installation does not change the live TCB map; clients may instantiate
    it with an entry whose interpretation depends on that unchanged map. *)
Lemma os_sched_install_continuation_map_resources :
  forall external sg context saved hooked incoming resumed
    (resource : (TaskID * nat) -> (TaskStackRegion * TaskStackFragments) -> Assertion)
    (frame : Assertion) heap,
  os_sched_saved_stack_binding context saved hooked ->
  os_sched_destination_binding external context saved hooked incoming resumed ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  (UCOS2_inv sg hooked **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) saved **
   resource (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), saved) **
   store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) ** frame) heap ->
  exists final sp,
    sched_install_heap_fragment sg heap final (task_slot_addr sg incoming.(stackLeaseSlot)) sp /\
    (coq_prop (task_current_at (os_sched_install_context context saved incoming hooked)
        incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
      external.(os_sched_arch_restore_source) incoming sp resumed) &&
     (UCOS2_inv sg (os_sched_install_context context saved incoming hooked) **
      task_stack_fragments_rep incoming.(stackLeaseRegion) resumed **
      resource (task_stack_key incoming) (incoming.(stackLeaseRegion), resumed) **
      store_parked_continuations resource
        (os_sched_install_context context saved incoming hooked).(TskState).(parkedTaskStacks) **
      frame)) final.
Proof.
  intros external sg context saved hooked incoming resumed resource frame heap
    Hsaved Hdestination Haddress Hbefore.
  assert (Hnone : hooked.(TskState).(parkedTaskStacks)
    (task_stack_key context.(os_sched_call_stack)) = None).
  { unfold os_sched_saved_stack_binding in Hsaved; tauto. }
  pose proof Hdestination as [_ [_ [_ Hparked]]].
  assert (Horder : UCOS2_inv sg hooked **
      task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) saved **
      resource (task_stack_key context.(os_sched_call_stack))
        (context.(os_sched_call_stack).(stackLeaseRegion), saved) **
      store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) ** frame |--
    (UCOS2_inv sg hooked **
      task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) saved) **
    (resource (task_stack_key context.(os_sched_call_stack))
       (context.(os_sched_call_stack).(stackLeaseRegion), saved) **
     store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) ** frame)) by entailer!.
  destruct (os_sched_install_heap_take_destination_frame external sg context saved hooked incoming
    resumed _ heap Hsaved Hdestination Haddress (Horder heap Hbefore))
    as [final [sp [Hrun [Hfacts Hafter]]]].
  assert (Hswitch :
    (UCOS2_inv sg (os_sched_install_context context saved incoming hooked) **
     task_stack_fragments_rep incoming.(stackLeaseRegion) resumed) **
    (resource (task_stack_key context.(os_sched_call_stack))
       (context.(os_sched_call_stack).(stackLeaseRegion), saved) **
     store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) ** frame) |--
    UCOS2_inv sg (os_sched_install_context context saved incoming hooked) **
    task_stack_fragments_rep incoming.(stackLeaseRegion) resumed **
    resource (task_stack_key incoming) (incoming.(stackLeaseRegion), resumed) **
    store_parked_continuations resource
      (os_sched_install_context context saved incoming hooked).(TskState).(parkedTaskStacks) ** frame).
  { sepcon_assoc_change.
    sep_apply_l_atomic (store_parked_continuations_switch resource hooked.(TskState).(parkedTaskStacks)
      context.(os_sched_call_stack) incoming saved resumed Hnone Hparked).
    unfold os_sched_install_context.
    cbn [replace_SchedS replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks].
    entailer!. }
  exists final, sp; split; [exact Hrun|]. split; [exact Hfacts|exact (Hswitch final Hafter)].
Qed.

(** The physical stack owner and its continuation capability are parked
    and taken together. The outgoing descriptor is supplied by the actual
    task-level save; this lemma does not synthesize it from a call identity
    or reuse the IRQ-only save transition. The input includes every old
    capsule, and the output retains the entire successor map.

    Initial-entry and suspended-call descriptors remain distinct. No
    distinct-key premise is needed: parking then taking also covers a
    hook that selects the same task generation. Selecting any descriptor
    is not evidence that the original C call has returned. *)
Lemma os_sched_install_take_task_continuation :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg context outgoing hooked incoming resumed (frame : Assertion) heap,
  armv7a_continuation_call outgoing = Some context ->
  armv7a_continuation_binding outgoing ->
  os_sched_saved_stack_binding context outgoing.(armv7a_continuation_fragments) hooked ->
  os_sched_destination_binding external context outgoing.(armv7a_continuation_fragments)
    hooked incoming resumed ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  (UCOS2_inv sg hooked **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion)
     outgoing.(armv7a_continuation_fragments) **
   armv7a_dormant_continuation abi outgoing **
   armv7a_task_continuations abi hooked.(TskState).(parkedTaskStacks) ** frame) heap ->
  exists final sp selected,
    sched_install_heap_fragment sg heap final (task_slot_addr sg incoming.(stackLeaseSlot)) sp /\
    armv7a_continuation_binding selected /\
    selected.(armv7a_continuation_stack) = incoming /\
    selected.(armv7a_continuation_fragments) = resumed /\
    task_current_at
      (os_sched_install_context context outgoing.(armv7a_continuation_fragments) incoming hooked)
      incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
    external.(os_sched_arch_restore_source) incoming sp resumed /\
    (UCOS2_inv sg
       (os_sched_install_context context outgoing.(armv7a_continuation_fragments) incoming hooked) **
     armv7a_task_continuations abi
       (os_sched_install_context context outgoing.(armv7a_continuation_fragments)
         incoming hooked).(TskState).(parkedTaskStacks) **
     task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
       selected.(armv7a_continuation_fragments) **
     armv7a_task_continuation_resource abi selected ** frame) final.
Proof.
  intros external platform port abi sg context outgoing hooked incoming resumed frame heap
    Hcall Hbinding Hsaved Hdestination Haddress Hbefore.
  assert (Hstack : outgoing.(armv7a_continuation_stack) = context.(os_sched_call_stack)).
  { destruct Hbinding as [Hlength Hlease]; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  assert (Hentry : armv7a_dormant_continuation abi outgoing |--
    armv7a_task_continuation_entry abi (task_stack_key context.(os_sched_call_stack))
      (context.(os_sched_call_stack).(stackLeaseRegion), outgoing.(armv7a_continuation_fragments))).
  { rewrite <- Hstack.
    assert (Hresource : armv7a_dormant_continuation abi outgoing |--
      armv7a_task_continuation_resource abi outgoing).
    { unfold armv7a_task_continuation_resource; rewrite Hcall; entailer!. }
    sep_apply_l_atomic Hresource.
    apply armv7a_task_continuation_entry_resources; exact Hbinding. }
  assert (Horder : UCOS2_inv sg hooked **
      task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion)
        outgoing.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi outgoing **
      armv7a_task_continuations abi hooked.(TskState).(parkedTaskStacks) ** frame |--
    UCOS2_inv sg hooked **
      task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion)
        outgoing.(armv7a_continuation_fragments) **
    armv7a_task_continuation_entry abi (task_stack_key context.(os_sched_call_stack))
      (context.(os_sched_call_stack).(stackLeaseRegion), outgoing.(armv7a_continuation_fragments)) **
    store_parked_continuations (armv7a_task_continuation_entry abi)
      hooked.(TskState).(parkedTaskStacks) ** frame).
  { sep_apply_l_atomic Hentry; unfold armv7a_task_continuations; entailer!. }
  destruct (os_sched_install_continuation_map_resources external sg context
    outgoing.(armv7a_continuation_fragments) hooked incoming resumed _ _ heap Hsaved Hdestination
    Haddress (Horder heap Hbefore)) as [final [sp [Hrun [[Hcurrent Hrestore] Hafter]]]].
  assert (Htake :
    UCOS2_inv sg
       (os_sched_install_context context outgoing.(armv7a_continuation_fragments) incoming hooked) **
    task_stack_fragments_rep incoming.(stackLeaseRegion) resumed **
    armv7a_task_continuation_entry abi (task_stack_key incoming) (incoming.(stackLeaseRegion), resumed) **
    store_parked_continuations (armv7a_task_continuation_entry abi)
      (os_sched_install_context context outgoing.(armv7a_continuation_fragments)
        incoming hooked).(TskState).(parkedTaskStacks) ** frame |--
    EX selected,
      coq_prop (armv7a_continuation_binding selected /\
        selected.(armv7a_continuation_stack) = incoming /\
        selected.(armv7a_continuation_fragments) = resumed) &&
      (UCOS2_inv sg
         (os_sched_install_context context outgoing.(armv7a_continuation_fragments) incoming hooked) **
       armv7a_task_continuations abi
         (os_sched_install_context context outgoing.(armv7a_continuation_fragments)
           incoming hooked).(TskState).(parkedTaskStacks) **
       task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
         selected.(armv7a_continuation_fragments) **
       armv7a_task_continuation_resource abi selected ** frame)).
  { unfold armv7a_task_continuation_entry; Intros selected.
    assert (Hkey : task_stack_key selected.(armv7a_continuation_stack) = task_stack_key incoming)
      by tauto.
    assert (Hpayload : (selected.(armv7a_continuation_stack).(stackLeaseRegion),
      selected.(armv7a_continuation_fragments)) = (incoming.(stackLeaseRegion), resumed)) by tauto.
    assert (Hselected : selected.(armv7a_continuation_stack) = incoming).
    { unfold task_stack_key in Hkey.
      destruct selected.(armv7a_continuation_stack), incoming; cbn in *; congruence. }
    assert (Hfragments : selected.(armv7a_continuation_fragments) = resumed) by congruence.
    Exists selected; unfold armv7a_task_continuations.
    rewrite Hselected, Hfragments; entailer!. }
  destruct (Htake final Hafter) as [selected [[Hvalid [Hlease Hfragments]] Howned]].
  exists final, sp, selected; split; [exact Hrun|]. split; [exact Hvalid|].
  split; [exact Hlease|]. split; [exact Hfragments|].
  split; [exact Hcurrent|]. split; [exact Hrestore|exact Howned].
Qed.

(** A source consumer must use the supplied actual final heap and SP, not
    a different existential run. Equal ordered loads and stores determine
    both. The read-only UnMapTbl belongs to the shared program owner; it
    survives these local masked instructions and is returned with the
    updated dynamic world and all untaken capsules. *)
Lemma os_sched_install_program_continuation_resources :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg context outgoing hooked incoming resumed (frame : Assertion) before after sp,
  armv7a_continuation_call outgoing = Some context ->
  armv7a_continuation_binding outgoing ->
  os_sched_saved_stack_binding context outgoing.(armv7a_continuation_fragments) hooked ->
  os_sched_destination_binding external context outgoing.(armv7a_continuation_fragments)
    hooked incoming resumed ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  (kernel_program_inv sg hooked **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion)
     outgoing.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi outgoing **
   armv7a_task_continuations abi hooked.(TskState).(parkedTaskStacks) ** frame) before ->
  sched_install_heap_fragment sg before after (task_slot_addr sg incoming.(stackLeaseSlot)) sp ->
  exists selected,
    armv7a_continuation_binding selected /\
    selected.(armv7a_continuation_stack) = incoming /\
    selected.(armv7a_continuation_fragments) = resumed /\
    task_current_at
      (os_sched_install_context context outgoing.(armv7a_continuation_fragments) incoming hooked)
      incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
    external.(os_sched_arch_restore_source) incoming sp resumed /\
    (kernel_program_inv sg
       (os_sched_install_context context outgoing.(armv7a_continuation_fragments) incoming hooked) **
     armv7a_task_continuations abi
       (os_sched_install_context context outgoing.(armv7a_continuation_fragments)
         incoming hooked).(TskState).(parkedTaskStacks) **
     task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
       selected.(armv7a_continuation_fragments) **
     armv7a_task_continuation_resource abi selected ** frame) after.
Proof.
  intros external platform port abi sg context outgoing hooked incoming resumed frame before after sp
    Hcall Hbinding Hsaved Hdestination Haddress Hbefore Hactual.
  assert (Hsplit : kernel_program_inv sg hooked **
      task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion)
        outgoing.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi outgoing **
      armv7a_task_continuations abi hooked.(TskState).(parkedTaskStacks) ** frame |--
    UCOS2_inv sg hooked **
      task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion)
        outgoing.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi outgoing **
      armv7a_task_continuations abi hooked.(TskState).(parkedTaskStacks) **
      (unmap_table_rep sg ** frame)).
  { rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (os_sched_install_take_task_continuation external platform port abi sg context outgoing
    hooked incoming resumed _ before Hcall Hbinding Hsaved Hdestination Haddress (Hsplit before Hbefore))
    as [final [actual_sp [selected [Hrun [Hvalid [Hlease [Hfragments [Hcurrent [Hrestore Howned]]]]]]]]].
  destruct (sched_install_heap_fragment_deterministic _ _ _ _ _ _ _ _ Hrun Hactual)
    as [Hheap [Hpointer Hsp]].
  subst final actual_sp.
  exists selected; split; [exact Hvalid|]. split; [exact Hlease|]. split; [exact Hfragments|].
  split; [exact Hcurrent|]. split; [exact Hrestore|].
  assert (Hmerge : UCOS2_inv sg
      (os_sched_install_context context outgoing.(armv7a_continuation_fragments) incoming hooked) **
    armv7a_task_continuations abi
      (os_sched_install_context context outgoing.(armv7a_continuation_fragments)
        incoming hooked).(TskState).(parkedTaskStacks) **
    task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
      selected.(armv7a_continuation_fragments) **
    armv7a_task_continuation_resource abi selected ** (unmap_table_rep sg ** frame) |--
    kernel_program_inv sg
      (os_sched_install_context context outgoing.(armv7a_continuation_fragments) incoming hooked) **
    armv7a_task_continuations abi
      (os_sched_install_context context outgoing.(armv7a_continuation_fragments)
        incoming hooked).(TskState).(parkedTaskStacks) **
    task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
      selected.(armv7a_continuation_fragments) **
    armv7a_task_continuation_resource abi selected ** frame).
  { rewrite kernel_program_inv_split_unmap; entailer!. }
  exact (Hmerge after Howned).
Qed.
