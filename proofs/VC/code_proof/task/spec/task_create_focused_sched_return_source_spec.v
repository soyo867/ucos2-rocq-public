Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.sched Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_saved_call_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_focus_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The focused map is the view transported by the registered client
    execution. Its original Save/inside pair remains linearly owned in
    that execution's frame. At the ACTUAL selector cut, reconstruct the
    exact entry from the same physical frame and current saved SP, then
    consume the already proved physical install and C Restore source.
    All returned facts describe that finite execution; there is no
    premise promising that a future scheduler will select this task.

    Descriptor binding/slice/mask/PC are observations retained from the
    original OSCtxSw save. Active registration, SP and payload must be
    transported by the actual intervening trace. Arbitrary foreign code
    and IRQ branches are not classified by this selected-cut consumer. *)
Lemma task_create_focused_sched_return_source : forall environment critical arch
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg state node context old_sp cpsr values lr prefix suffix first old_words publication
  original saved acquired descriptor call_entry region args task_return lower old_frame upper
  before (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original descriptor.(armv7a_continuation_pc)
    descriptor.(armv7a_continuation_lr) in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let outgoing := armv7a_task_save_image context old_sp cpsr values lr fragments in
  os_sched_source_live_save_input sg state node context old_sp cpsr values lr
    prefix suffix first old_words focus publication ->
  state.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), descriptor.(armv7a_continuation_fragments)) ->
  task_stack_live_coverage state.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  armv7a_continuation_binding descriptor ->
  descriptor.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice descriptor ->
  descriptor.(armv7a_continuation_pc) = descriptor.(armv7a_continuation_lr) ->
  armv7a_irq_fiq_mask descriptor.(armv7a_continuation_cpsr) = 192 ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at state descriptor.(armv7a_continuation_stack) descriptor.(armv7a_continuation_sp) ->
  (kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
     context 192 ** kernel_program_inv sg state **
   armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
   interrupt_platform_saved environment.(task_stack_call_platform)
     (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
   critical_region_inside critical sg original.(os_sched_call_invocation) acquired ** frame) before ->
  exists written stored,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
      outgoing.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi context outgoing stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg
        (os_sched_save_current_sp state context.(os_sched_call_stack).(stackLeaseSlot)
          outgoing.(armv7a_continuation_sp))
        (os_sched_save_current_sp state context.(os_sched_call_stack).(stackLeaseSlot)
          outgoing.(armv7a_continuation_sp)) ->
      exists installed,
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
          descriptor.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads descriptor installed /\
        descriptor.(armv7a_continuation_call) = Some original /\
        (forall restored,
          armv7a_task_restore_transition task_abi context descriptor installed restored ->
          forall cursor restore_written middle final_cursor after,
          cursor.(kernel_restore_r0) = saved ->
          armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
          armv7a_restore_prefix_transition restore cursor restored restore_written middle ->
          armv7a_restore_suffix_transition restore restore_written middle final_cursor after ->
          kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
          final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
          (os_sched_stack_return_post environment kernel_program_inv sg original
             (armv7a_irq_fiq_mask saved) call_entry ** frame) after /\
          (task_create_stack_post environment critical sg region args task_return lower old_frame upper
             original (armv7a_irq_fiq_mask saved) 0 ** frame) after)).
Proof.
  intros environment critical arch task_abi restore sg state node context old_sp cpsr values lr prefix suffix
    first old_words publication original saved acquired descriptor call_entry region args task_return
    lower old_frame upper before frame abi focus fragments outgoing Hinput Hselected Hparked Hcoverage
    Hbinding Hcall Hslice Hpc Hmask Horigin Hactive Hpointer Hpre.
  match type of Hpre with ?P before => assert (Hmerge : P |--
    kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      context 192 ** kernel_program_inv sg state **
    store_parked_continuations
      (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor state.(TskState) focus)
      state.(TskState).(parkedTaskStacks) ** frame) end.
  { unfold focus; sepcon_assoc_change.
    sep_apply_l_atomic (kernel_saved_sched_call_merge_focus_resources _ _ _ abi critical sg original
      saved acquired descriptor state Hbinding Hcall Hslice Hpc Hmask Horigin Hactive Hpointer Hparked).
    entailer!. }
  exact (task_create_saved_sched_return_source environment critical arch task_abi restore sg state node
    context old_sp cpsr values lr prefix suffix first old_words publication original saved acquired descriptor
    focus call_entry region args task_return lower old_frame upper before frame
    Hinput Hselected Hparked Hcoverage (Hmerge before Hpre)).
Qed.
