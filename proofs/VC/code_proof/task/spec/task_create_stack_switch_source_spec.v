Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_save_global_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The saved-stack fact follows from the actual live TCB-SP update and
    the saved fragment bounds. It is not a desired consequence added to
    the architecture save relation. The next lemma supplies this update
    from the real assembly stores and consumes the resulting fact. *)
Lemma task_create_saved_context_binding : forall state call node sp fragments publication,
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0 fragments ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) sp ->
  task_publication_happened state.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  os_sched_saved_stack_binding call fragments
    (os_sched_save_current_sp state call.(os_sched_call_stack).(stackLeaseSlot) sp).
Proof.
  intros state call node sp fragments publication Hnode Hid Hnone Hregion Hgeometry Hsp Hhistory.
  unfold os_sched_saved_stack_binding, os_sched_save_current_sp; rewrite Hnode.
  cbn [replace_TskS TskState glob_task_set_usedtask parkedTaskStacks taskLifecycle].
  split; [exact Hregion|]. split; [exact Hgeometry|]. split.
  - exists publication; exact Hhistory.
  - split; [|exact Hnone].
    intros updated Hupdated Hgeneration.
    cbn [glob_task_set_usedtask inUsedTaskStates] in Hupdated.
    rewrite Z.eqb_refl in Hupdated; injection Hupdated as Hupdated; subst updated.
    unfold task_stack_lease_matches_task; cbn [task_set_saved_sp taskID tcbStkPtr].
    exact (conj Hid (conj Hgeneration Hsp)).
Qed.

(** Live-current, no-kernel-write hook branch of the real OSCtxSw source.
    Save, TCB-SP store, destination cache stores and restore are executed
    in order on one heap. The hook's empty memory/STS effect is an EXPLICIT
    source obligation, suitable for the separately checked reference hook;
    it is not inferred from the generic hook certificate. A custom hook
    with kernel effects must use its own source/resource producer instead.
    The high-ready checkpoint is the preceding OS_Sched C selector's cut,
    not a future destination supplied by the API caller. *)
Lemma task_create_live_switch_selected_source :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    (task_abi : Armv7aTaskContextABI external platform port abi)
    (initial : Armv7aInitialEntryABI external platform port abi)
    sg state node call old_sp cpsr registers lr prefix suffix first old_words
    focus publication (frame : Assertion) before,
  state.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  task_stack_live_coverage state.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  sched_high_ready_consistency state.(TskState) state.(SchedState) ->
  state.(SchedState).(readyList) <> [] ->
  (task_stack_key call.(os_sched_call_stack) = armv7a_call_focus_key focus ->
    focus = armv7a_call_focus call lr lr) ->
  call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    call.(os_sched_call_fragments) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
  task_publication_happened state.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  List.length registers = 13%nat ->
  0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) registers ->
  armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
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
    (forall captured hooked,
      armv7a_task_capture_transition task_abi call saved stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step external.(os_sched_hook_action) sg updated updated ->
      exists incoming installed selected current,
        external.(os_sched_arch_save_source) call saved.(armv7a_continuation_sp) fragments /\
        os_sched_saved_stack_binding call fragments updated /\
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        selected.(armv7a_continuation_stack) = incoming /\
        (task_stack_key incoming = armv7a_call_focus_key focus ->
          armv7a_continuation_focus_binding focus selected) /\
        sched_current_ready_at (os_sched_install_context call fragments incoming updated).(TskState)
          (os_sched_install_context call fragments incoming updated).(SchedState)
          incoming.(stackLeaseSlot) current /\
        current.(taskGeneration) = incoming.(stackLeaseGeneration) /\
        task_stack_live_coverage (os_sched_install_context call fragments incoming updated).(TskState)
          (Some (task_stack_key incoming)) /\
        (forall payload,
          updated.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
          task_stack_key incoming <> armv7a_call_focus_key focus ->
          (os_sched_install_context call fragments incoming updated).(TskState).(parkedTaskStacks)
            (armv7a_call_focus_key focus) = Some payload) /\
        (forall restored, armv7a_task_restore_transition task_abi call selected installed restored ->
          restored.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
          armv7a_task_restored_source external selected /\
          (armv7a_task_restored_execution external platform port abi selected **
           UCOS2_inv sg (os_sched_install_context call fragments incoming updated) **
           armv7a_task_call_stacks abi (os_sched_install_context call fragments incoming updated).(TskState)
             focus (os_sched_install_context call fragments incoming updated).(TskState).(parkedTaskStacks) **
           frame) restored /\
          (task_stack_key incoming = armv7a_call_focus_key focus ->
           (kernel_call_execution_owned external platform
              (armv7a_continuation_resumed_call selected focus.(armv7a_focus_call))
              (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) **
            UCOS2_inv sg (os_sched_install_context call fragments incoming updated) **
            armv7a_task_call_stacks abi (os_sched_install_context call fragments incoming updated).(TskState)
              focus (os_sched_install_context call fragments incoming updated).(TskState).(parkedTaskStacks) **
            frame) restored))).
Proof.
  intros external platform port abi task_abi initial sg state node call old_sp cpsr registers lr prefix suffix
    first old_words focus publication frame before Hcurrent Hnode Hid Hgen Hnone Hcoverage Hhigh Hnonempty
    Hfocus Hfragments Hregion Hgeometry Hsp_range Hhistory Hlength Hcpsr Hlr Hranges Hmask Hsp32 Hsp
    Haddress Hpre fragments saved updated.
  destruct (armv7a_task_save_global_call external platform port abi task_abi sg state node call old_sp
    cpsr registers lr prefix suffix first old_words focus frame before Hcurrent Hnode Hid Hgen Hnone
    Hcoverage Hfocus Hfragments Hlength Hcpsr Hlr Hranges Hmask Hsp32 Hsp
    (Haddress _) Hpre) as [written [stored [Hwrites [Hload [Hstore [Hcovered Hcapture]]]]]].
  fold fragments saved updated in Hstore, Hcovered, Hcapture.
  assert (Hsaved : os_sched_saved_stack_binding call fragments updated).
  { apply task_create_saved_context_binding with (node := node) (publication := publication);
      try assumption.
    unfold fragments; apply armv7a_task_frame_update_preserves_fragment_bounds with (old_words := old_words).
    rewrite <- Hfragments; exact Hgeometry. }
  assert (Hhigh_after : sched_high_ready_consistency updated.(TskState) updated.(SchedState)).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode.
    cbn [replace_TskS TskState SchedState].
    unfold sched_high_ready_consistency in *.
    destruct state.(SchedState).(readyList) as [|head tail] eqn:Hlist; [contradiction|].
    destruct Hhigh as [Hhigh [high [Hlookup Hpriority]]]; split; [exact Hhigh|].
    destruct (Z.eqb head call.(os_sched_call_stack).(stackLeaseSlot)) eqn:Heq.
    - apply Z.eqb_eq in Heq; subst head.
      assert (high = node) by congruence; subst high.
      exists (task_set_saved_sp node saved.(armv7a_continuation_sp)); split; [|exact Hpriority].
      cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
    - exists high; split; [|exact Hpriority].
      cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Heq; exact Hlookup. }
  exists written, stored; split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcaptured Hhook_heap Hhook_step.
  assert (Hunchanged : hooked = captured).
  { eapply kernel_heap_execution_deterministic; [exact Hhook_heap|].
    split; [constructor|]; split; reflexivity. }
  subst hooked.
  destruct (Hcapture captured Hcaptured) as [Hmemory [Hsource Howned]].
  match type of Howned with ?P captured => assert (Horder : P |--
    UCOS2_inv sg updated ** task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
    armv7a_task_call_stack_entry abi updated.(TskState) focus (task_stack_key call.(os_sched_call_stack))
      (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
    armv7a_task_call_stacks abi updated.(TskState) focus updated.(TskState).(parkedTaskStacks) **
    (armv7a_task_switch_control task_abi call ** frame)) by entailer!
  end.
  destruct (armv7a_task_restore_selected_call external platform port abi task_abi initial sg call fragments
    updated focus frame captured Hsaved Hhigh_after Hnonempty (fun slot _ _ => Haddress slot)
    Hcovered (Horder captured Howned))
    as [incoming [installed [selected [current Hselected]]]].
  exists incoming, installed, selected, current; split; [exact Hsource|].
  split; [exact Hsaved|]; exact Hselected.
Qed.
