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
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_retired_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_call_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Actual selected64 C prefix and checked reference hook when the current
    invocation has already recycled its TCB. This is a source producer for
    the same general selected-post interface as the live-current branch.
    It proves that the destination cannot be the free current slot; it
    never revives the retired generation or manufactures a return to it.
    Earlier interrupt/reuse intervals must establish the observed owner at
    this cut and are not hidden in this theorem's external contract. *)
Lemma task_create_reference_sched_free_switch_source :
  forall configured platform port
    (abi : Armv7aContinuationABI (tmr_task_reference_external configured) platform port)
    (task_abi : Armv7aTaskContextABI (tmr_task_reference_external configured) platform port abi)
    (initial : Armv7aInitialEntryABI (tmr_task_reference_external configured) platform port abi)
    sg state image call old_sp cpsr registers lr prefix suffix first old_words
    focus publication (frame : Assertion) before,
  os_sched_requests_switch state = true ->
  state.(SchedState).(readyList) <> [] ->
  state.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = None ->
  state.(TskState).(taskLifecycle).(taskFreeStorage) call.(os_sched_call_stack).(stackLeaseSlot) = Some image ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
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
  (os_sched_source_switch_pre (tmr_task_reference_external configured) platform port abi
     sg call focus state ** unmap_table_rep sg ** frame) before ->
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  let saved := armv7a_task_save_image call old_sp cpsr registers lr fragments in
  let selected_state := os_sched_prefix_state state in
  let updated := os_sched_save_current_sp selected_state call.(os_sched_call_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_sp) in
  exists selected_heap written stored,
    os_sched_source_switch_prefix_execution sg before selected_heap /\
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) selected_heap written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      saved.(armv7a_continuation_sp)) written stored /\
    (forall captured,
      armv7a_task_capture_transition task_abi call saved stored captured ->
      exists incoming resumed installed selected current,
        os_sched_switch_source (tmr_task_reference_external configured) sg state call
          (os_sched_install_context call fragments incoming updated) /\
        os_sched_destination_binding (tmr_task_reference_external configured)
          call fragments updated incoming resumed /\
        incoming.(stackLeaseSlot) <> call.(os_sched_call_stack).(stackLeaseSlot) /\
        selected.(armv7a_continuation_fragments) = resumed /\
        sched_install_heap_fragment sg captured installed (task_slot_addr sg incoming.(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        (os_sched_current_storage_binding sg call state ->
          task_execution_source_step (tmr_task_reference_external configured) port sg
            call.(os_sched_call_origin) state
            (RunningInvocation incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration))
            (os_sched_install_context call fragments incoming updated)) /\
        (forall payload,
          updated.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
          task_stack_key incoming <> armv7a_call_focus_key focus ->
          (os_sched_install_context call fragments incoming updated).(TskState).(parkedTaskStacks)
            (armv7a_call_focus_key focus) = Some payload) /\
        (forall restored, armv7a_task_restore_transition task_abi call selected installed restored ->
          os_sched_source_switch_execution (tmr_task_reference_external configured) platform port abi task_abi
            sg selected_state call old_sp cpsr registers lr saved incoming selected selected_heap restored /\
          armv7a_task_restored_source (tmr_task_reference_external configured) selected /\
          (os_sched_source_selected_post (tmr_task_reference_external configured) platform port abi
             sg focus incoming selected current (os_sched_install_context call fragments incoming updated) **
           (unmap_table_rep sg ** frame)) restored)).
Proof.
  intros configured platform port abi task_abi initial sg state image call old_sp cpsr registers lr prefix
    suffix first old_words focus publication frame before Hswitch Hready Hcurrent Hunused Himage Hnone
    Hfocus Hfragments Hregion Hgeometry Hpublication Hlength Hcpsr Hlr Hranges Hmask Hsp32 Hsp
    Haddress Hpre fragments saved selected_state updated.
  destruct (os_sched_source_switch_prefix_resources (tmr_task_reference_external configured) platform port abi
    sg state call focus frame before Hswitch Hready Hpre) as [selected_heap [Hprefix [Hhigh Hselected]]].
  assert (Henabled : os_sched_selection_enabled state = true)
    by (apply (proj1 (os_sched_requests_switch_iff state)) in Hswitch; tauto).
  assert (Hselected_current : selected_state.(SchedState).(curTaskID) =
    Some call.(os_sched_call_stack).(stackLeaseSlot)).
  { unfold selected_state, os_sched_prefix_state, os_sched_ready_checkpoint;
      rewrite Henabled, Hswitch; exact Hcurrent. }
  assert (Hselected_ready : selected_state.(SchedState).(readyList) <> []).
  { unfold selected_state, os_sched_prefix_state, os_sched_ready_checkpoint;
      rewrite Henabled, Hswitch; exact Hready. }
  assert (Horder : os_sched_source_switch_pre (tmr_task_reference_external configured) platform port abi
      sg call focus selected_state ** unmap_table_rep sg ** frame |--
    os_sched_source_switch_pre (tmr_task_reference_external configured) platform port abi
      sg call focus selected_state ** (unmap_table_rep sg ** frame)) by entailer!.
  destruct (os_sched_source_free_switch_destination_resources (tmr_task_reference_external configured)
    platform port abi task_abi initial sg selected_state image call old_sp cpsr registers lr prefix suffix
    first old_words focus publication (unmap_table_rep sg ** frame) selected_heap Hselected_current
    Hunused Himage Hnone Hhigh Hselected_ready Hfocus Hfragments Hregion Hgeometry Hpublication
    Hlength Hcpsr Hlr Hranges Hmask Hsp32 Hsp Haddress (Horder selected_heap Hselected))
    as [written [stored [Hwrites [Hload [Hstore Hrun]]]]].
  fold fragments saved updated in Hstore, Hrun.
  exists selected_heap, written, stored; split; [exact Hprefix|].
  split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured Hcapture.
  assert (Hempty : kernel_heap_execution [] captured captured) by (split; [constructor|auto]).
  assert (Hhook : kernel_client_step (tmr_task_reference_external configured).(os_sched_hook_action)
    sg updated updated) by reflexivity.
  destruct (Hrun captured captured Hcapture Hempty Hhook)
    as [incoming [resumed [installed [selected [current [Hsave [Hdestination [Hdifferent [Hselected_fragments
      [Hinstall [Hreads [Hpending Hrestore]]]]]]]]]]]].
  exists incoming, resumed, installed, selected, current.
  split.
  - split; [exact Hswitch|].
    exists saved.(armv7a_continuation_sp), fragments, updated, incoming, resumed.
    exact (conj Hsave (conj Hhook (conj Hdestination eq_refl))).
  - split; [exact Hdestination|]. split; [exact Hdifferent|]. split; [exact Hselected_fragments|].
    split; [exact Hinstall|]. split; [exact Hreads|]. split.
    + intros Hstorage.
      eapply TaskExecutionSchedulerTransfer with (sp := saved.(armv7a_continuation_sp))
        (resumed := resumed); eassumption.
    + split; [exact Hpending|exact Hrestore].
Qed.
