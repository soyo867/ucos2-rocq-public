Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_switch_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Selection observes the SAME parked map subsequently consumed by
    install. The pure architecture-source observation comes from its
    selected owner and the existing approved continuation contract. The
    generic local is retained in that owner; no weak-map conversion occurs.
    This lemma is used below by the actual switching C composition. *)
Lemma os_sched_continuation_high_destination : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (initial : Armv7aInitialEntryABI external platform port abi)
  sg call outgoing hooked local (frame : Assertion) heap,
  os_sched_saved_stack_binding call outgoing hooked ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  hooked.(SchedState).(readyList) <> [] ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  (UCOS2_inv sg hooked **
   kernel_saved_continuation_entry abi hooked.(TskState) local
     (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations (kernel_saved_continuation_entry abi hooked.(TskState) local)
     hooked.(TskState).(parkedTaskStacks) ** frame) heap ->
  exists incoming resumed node,
    os_sched_destination_binding external call outgoing hooked incoming resumed /\
    hooked.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node /\
    node.(taskGeneration) = incoming.(stackLeaseGeneration) /\
    In incoming.(stackLeaseSlot) hooked.(SchedState).(readyList) /\
    is_effectively_ready node.(stat) node.(dly) = true.
Proof.
  intros external platform port abi task_abi initial sg call outgoing hooked local frame heap
    Hsaved Hhigh Hnonempty Hcoverage Hpre.
  assert (Hvalid : UCOS2_state_inv sg hooked).
  { match type of Hpre with ?P heap => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg hooked) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve heap Hpre)). }
  destruct (os_sched_covered_high_destination sg call outgoing hooked Hvalid Hsaved Hhigh Hnonempty Hcoverage)
    as [incoming [resumed [node [Hselected [Hnode [Hgen [Hpriority [Hlive [Hlookup [Hin Hready]]]]]]]]]].
  assert (Habsent : hooked.(TskState).(parkedTaskStacks)
    (task_stack_key call.(os_sched_call_stack)) = None) by (unfold os_sched_saved_stack_binding in Hsaved; tauto).
  assert (Hentry : kernel_saved_continuation_entry abi hooked.(TskState) local
      (task_stack_key incoming) (incoming.(stackLeaseRegion), resumed) |--
    coq_prop (os_sched_destination_binding external call outgoing hooked incoming resumed) && TT).
  { unfold kernel_saved_continuation_entry; Intros descriptor.
    assert (Hkey : task_stack_key descriptor.(armv7a_continuation_stack) = task_stack_key incoming) by tauto.
    assert (Hpayload : (descriptor.(armv7a_continuation_stack).(stackLeaseRegion),
      descriptor.(armv7a_continuation_fragments)) = (incoming.(stackLeaseRegion), resumed)) by tauto.
    assert (Hlease : descriptor.(armv7a_continuation_stack) = incoming).
    { unfold task_stack_key in Hkey; destruct descriptor.(armv7a_continuation_stack), incoming;
        cbn in *; congruence. }
    assert (Hfragments : descriptor.(armv7a_continuation_fragments) = resumed) by congruence.
    assert (Hsp : node.(tcbStkPtr) = descriptor.(armv7a_continuation_sp)).
    { assert (Hlive_sp : task_stack_live_sp hooked.(TskState) (task_stack_key incoming)
        descriptor.(armv7a_continuation_sp)) by tauto.
      apply Hlive_sp; assumption. }
    sep_apply_l_atomic (armv7a_task_continuation_restore_source external platform port abi task_abi initial descriptor).
    Intros.
    assert (Harch : external.(os_sched_arch_restore_source) incoming node.(tcbStkPtr) resumed).
    { rewrite Hsp, <- Hlease, <- Hfragments; assumption. }
    assert (Hdestination : os_sched_destination_binding external call outgoing hooked incoming resumed).
    { unfold os_sched_destination_binding; split; [exact Hselected|].
      split; [exists node; tauto|]. split; assumption. }
    entailer!; intros ? ?; exact I. }
  match type of Hpre with ?P heap => assert (Hobserve : P |--
    coq_prop (os_sched_destination_binding external call outgoing hooked incoming resumed) && TT) end.
  { sep_apply_l_atomic (store_parked_continuations_switch
      (kernel_saved_continuation_entry abi hooked.(TskState) local)
      hooked.(TskState).(parkedTaskStacks) call.(os_sched_call_stack) incoming outgoing resumed Habsent Hlookup).
    sep_apply_l_atomic Hentry; entailer!; intros ? ?; exact I. }
  exists incoming, resumed, node; split; [exact (proj1 (Hobserve heap Hpre))|]; tauto.
Qed.

(** Real masked C prefix, existing save/capture contract, and the checked
    reference hook's empty C effect. The destination is produced from the
    resulting map and ready selector, never supplied as a future success
    condition. The output is the actual hook endpoint, with every local
    owner retained. A nonempty custom hook must use its own C producer.

    Frame geometry is precisely the existing executed save interface;
    this theorem adds no ARM/BSP law and performs no ISA re-verification. *)
Lemma os_sched_modular_switch_continuation_selection :
  forall external platform port critical
    (abi : Armv7aContinuationABI external platform port)
    (task_abi : Armv7aTaskContextABI external platform port abi)
    (initial : Armv7aInitialEntryABI external platform port abi)
    sg state node call saved acquired other old_sp cpsr registers lr prefix suffix first old_words
    publication before (frame : Assertion),
  let checkpoint := os_sched_prefix_state state in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  let descriptor := armv7a_task_save_image call old_sp cpsr registers lr fragments in
  let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
    descriptor.(armv7a_continuation_sp) in
  let local := kernel_sched_saved_local_at platform critical sg checkpoint.(TskState) call saved acquired other in
  os_sched_requests_switch state = true -> state.(SchedState).(readyList) <> [] ->
  kernel_call_task_source call state ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    call.(os_sched_call_fragments) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
  task_publication_happened state.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  List.length registers = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) registers -> armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  (kernel_continuation_call_masked abi kernel_program_inv other critical sg
     (Some (task_stack_key call.(os_sched_call_stack))) call saved acquired state ** frame) before ->
  exists prefix_heap written stored,
    os_sched_source_switch_prefix_execution sg before prefix_heap /\
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) prefix_heap written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      descriptor.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi call descriptor stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step external.(os_sched_hook_action) sg updated updated ->
      exists incoming resumed selected_node,
        external.(os_sched_arch_save_source) call descriptor.(armv7a_continuation_sp) fragments /\
        os_sched_saved_stack_binding call fragments updated /\
        os_sched_destination_binding external call fragments updated incoming resumed /\
        updated.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some selected_node /\
        selected_node.(taskGeneration) = incoming.(stackLeaseGeneration) /\
        In incoming.(stackLeaseSlot) updated.(SchedState).(readyList) /\
        is_effectively_ready selected_node.(stat) selected_node.(dly) = true /\
        task_stack_live_coverage updated.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) /\
        (UCOS2_inv sg updated **
         task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
         kernel_saved_continuation_entry abi updated.(TskState) local
           (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
         store_parked_continuations (kernel_saved_continuation_entry abi updated.(TskState) local)
           updated.(TskState).(parkedTaskStacks) **
         (armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame)) hooked /\
        (tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
            task_slot_addr sg incoming.(stackLeaseSlot) ->
         exists installed selected,
           sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
             selected.(armv7a_continuation_sp) /\
           armv7a_continuation_restore_reads selected installed /\
           armv7a_continuation_binding selected /\
           selected.(armv7a_continuation_stack) = incoming /\
           selected.(armv7a_continuation_fragments) = resumed /\
           task_current_at (os_sched_install_context call fragments incoming updated)
             incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
           task_stack_live_coverage (os_sched_install_context call fragments incoming updated).(TskState)
             (Some (task_stack_key incoming)) /\
           (forall restored,
             armv7a_task_restore_transition task_abi call selected installed restored ->
             restored.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
             armv7a_task_restored_source external selected /\
             (armv7a_task_restored_execution external platform port abi selected ** local selected **
              kernel_program_inv sg (os_sched_install_context call fragments incoming updated) **
              store_parked_continuations
                (kernel_saved_continuation_entry abi
                  (os_sched_install_context call fragments incoming updated).(TskState) local)
                (os_sched_install_context call fragments incoming updated).(TskState).(parkedTaskStacks) ** frame) restored))).
Proof.
  intros external platform port critical abi task_abi initial sg state node call saved acquired other
    old_sp cpsr registers lr prefix suffix first old_words publication before frame
    checkpoint fragments descriptor updated local Hswitch Hnonempty Hsource Hnode Hid Hgen Habsent
    Hfragments Hregion Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr Hranges Hmask Hsp32 Hsp Haddress Hpre.
  destruct (os_sched_modular_switch_capture external platform port critical abi task_abi sg state node call
    saved acquired other old_sp cpsr registers lr prefix suffix first old_words before frame
    Hswitch Hnonempty Hsource Hnode Hid Hgen Habsent Hfragments Hlength Hcpsr Hlr Hranges Hmask Hsp32 Hsp
    Haddress Hpre) as [prefix_heap [written [stored [Hprefix [Hhigh [Hwrites [Hload [Hstore [Hcovered Hcapture]]]]]]]]].
  fold checkpoint fragments descriptor updated local in Hhigh, Hstore, Hcovered, Hcapture.
  assert (Hsaved : os_sched_saved_stack_binding call fragments updated).
  { apply task_create_saved_context_binding with (node := node) (publication := publication); try assumption.
    unfold fragments; apply armv7a_task_frame_update_preserves_fragment_bounds with (old_words := old_words).
    rewrite <- Hfragments; exact Hgeometry. }
  assert (Hready_checkpoint : checkpoint.(SchedState).(readyList) = state.(SchedState).(readyList)).
  { exact (proj1 (os_sched_ready_checkpoint_frame state)). }
  assert (Hnonempty_updated : updated.(SchedState).(readyList) <> []).
  { change (checkpoint.(SchedState).(readyList) <> []); rewrite Hready_checkpoint; exact Hnonempty. }
  assert (Hhigh_updated : sched_high_ready_consistency updated.(TskState) updated.(SchedState)).
  { unfold updated, os_sched_save_current_sp; change checkpoint.(TskState) with state.(TskState); rewrite Hnode.
    cbn [replace_TskS TskState SchedState].
    unfold sched_high_ready_consistency in *.
    destruct checkpoint.(SchedState).(readyList) as [|head tail] eqn:Hlist.
    - exfalso; apply Hnonempty; congruence.
    - destruct Hhigh as [Hhigh [high [Hlookup Hpriority]]]; split; [exact Hhigh|].
      destruct (Z.eqb head call.(os_sched_call_stack).(stackLeaseSlot)) eqn:Heq.
      + apply Z.eqb_eq in Heq; subst head.
        change (state.(TskState).(inUsedTaskStates)
          call.(os_sched_call_stack).(stackLeaseSlot) = Some high) in Hlookup.
        assert (high = node) by congruence; subst high.
        exists (task_set_saved_sp node descriptor.(armv7a_continuation_sp)); split; [|exact Hpriority].
        cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
      + exists high; split; [|exact Hpriority].
        cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Heq; exact Hlookup. }
  exists prefix_heap, written, stored.
  split; [exact Hprefix|]. split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcaptured Hhook_heap Hhook_step.
  assert (Hunchanged : hooked = captured).
  { eapply kernel_heap_execution_deterministic; [exact Hhook_heap|].
    split; [constructor|]; split; reflexivity. }
  subst hooked; destruct (Hcapture captured Hcaptured) as [Hmemory [Hsave_source Howned]].
  match type of Howned with ?P captured => assert (Hselect : P |--
    UCOS2_inv sg updated **
    kernel_saved_continuation_entry abi updated.(TskState) local
      (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
    store_parked_continuations (kernel_saved_continuation_entry abi updated.(TskState) local)
      updated.(TskState).(parkedTaskStacks) **
    (task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
     armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame)) by entailer! end.
  destruct (os_sched_continuation_high_destination external platform port abi task_abi initial sg call fragments
    updated local _ captured Hsaved Hhigh_updated Hnonempty_updated Hcovered (Hselect captured Howned))
    as [incoming [resumed [selected_node [Hdestination [Hselected [Hgeneration [Hin Hready]]]]]]].
  exists incoming, resumed, selected_node.
  split; [exact Hsave_source|]. split; [exact Hsaved|]. split; [exact Hdestination|].
  split; [exact Hselected|]. split; [exact Hgeneration|]. split; [exact Hin|]. split; [exact Hready|].
  split; [exact Hcovered|].
  assert (Hordered : (UCOS2_inv sg updated **
    task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
    kernel_saved_continuation_entry abi updated.(TskState) local
      (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
    store_parked_continuations (kernel_saved_continuation_entry abi updated.(TskState) local)
      updated.(TskState).(parkedTaskStacks) **
    (armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame)) captured).
  { match type of Howned with ?P captured => match goal with |- ?Q captured =>
      assert (Horder : P |-- Q) by entailer! end end.
    exact (Horder captured Howned). }
  split; [exact Hordered|]. intro Hselected_address.
  exact (kernel_saved_continuation_install_source external platform port abi task_abi sg call fragments
    updated incoming resumed local captured frame Hsaved Hdestination Hselected_address Hcovered Hordered).
Qed.
