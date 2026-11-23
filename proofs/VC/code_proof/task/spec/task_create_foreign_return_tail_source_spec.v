Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_foreign_callee_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_return_tail_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** One heap-connected consumer of the foreign-return producer and the
    actual remaining OSTaskCreate C branches. After the original TCBInit
    call resumes, its result selects the proven current OSRunning/Sched
    continuation or the actual Save/NULL-store/Restore failure tail.
    The original initialized stack is retained only on the failure branch.

    The observed destination classifies THIS return. The theorem adds no
    eventual-selection, no-IRQ, application-termination or platform law.
    The two final local Save/Restore continuations use their actual ABI
    transitions; other interrupt returns use the shared return interfaces. *)
Lemma task_create_foreign_return_tail_source :
  forall environment critical arch
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg region args task_return lower old_frame upper initial_name initial result
    original suspended released state node call old_sp cpsr registers lr prefix suffix first old_words
    publication saved acquired (frame : Assertion) before,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let retained := interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) acquired **
    task_tcb_init_stack_buffer_result region args task_return lower upper result ** frame in
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) initial ->
  task_tcb_init_stack_call_result critical sg region args task_return lower upper initial_name
    original.(os_sched_call_invocation) original.(os_sched_call_origin) initial result released ->
  UCOS2_state_inv sg released ->
  task_tcb_init_stack_source_preserved original initial released ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released state ->
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended -> armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  call.(os_sched_call_stack).(stackLeaseSlot) <> original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_saved_pointer_at state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  os_sched_source_live_save_input sg state node call old_sp cpsr registers lr
    prefix suffix first old_words focus publication ->
  (os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
     environment.(task_stack_call_port) abi sg call focus state ** unmap_table_rep sg ** retained) before ->
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  let foreign_saved := armv7a_task_save_image call old_sp cpsr registers lr fragments in
  let updated := os_sched_save_current_sp state call.(os_sched_call_stack).(stackLeaseSlot)
    foreign_saved.(armv7a_continuation_sp) in
  exists written stored,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      foreign_saved.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi call foreign_saved stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg updated updated ->
      os_sched_destination_binding environment.(task_stack_call_external) call fragments updated
        original.(os_sched_call_stack) suspended.(armv7a_continuation_fragments) ->
      exists installed selected,
        sched_install_heap_fragment sg hooked installed
          (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
        selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
        selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
        (forall restored,
          armv7a_task_restore_transition task_abi call selected installed restored ->
          forall cursor restore_written middle final_cursor after,
          cursor.(kernel_restore_r0) = saved ->
          cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
          armv7a_restore_prefix_transition restore cursor restored restore_written middle ->
          armv7a_restore_suffix_transition restore restore_written middle final_cursor after ->
          kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
          task_create_tcb_return_source_continuation environment critical arch save restore sg region args task_return
            lower old_frame upper original (armv7a_irq_fiq_mask saved) result after frame)).
Proof.
  intros environment critical arch task_abi save restore sg region args task_return lower old_frame upper
    initial_name initial result original suspended released state node call old_sp cpsr registers lr
    prefix suffix first old_words publication saved acquired frame before abi focus retained Hentry Hresult
    Hreleased Hordinary Hhistory Horigin Hbinding Hcall Hslice Hmask Hdifferent Hpointer Hinput Hpre
    fragments foreign_saved updated.
  destruct (task_tcb_init_foreign_capture_callee_return environment critical arch task_abi restore sg region args
    task_return lower upper initial_name original.(os_sched_call_invocation) original.(os_sched_call_origin)
    initial result original suspended released state node call old_sp cpsr registers lr prefix suffix first old_words
    publication saved acquired frame before Hresult Hreleased Hordinary Hhistory Horigin Hbinding Hcall Hslice
    Hmask Hdifferent Hpointer Hinput Hpre)
    as [written [stored [Hwrites [Hload [Hstore Hcapture]]]]].
  exists written, stored; split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcaptured Hhook Hstep Hdestination.
  destruct (Hcapture captured hooked Hcaptured Hhook Hstep Hdestination)
    as [installed [selected [Hinstall [Hreads [Hsp [Hcpsr [Hregisters Hreturn]]]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  split; [exact Hsp|]. split; [exact Hcpsr|]. split; [exact Hregisters|].
  intros restored Hrestored cursor restore_written middle final_cursor after Hr0 Hcursor Hprefix Hsuffix.
  destruct (Hreturn restored Hrestored cursor restore_written middle final_cursor after Hr0 Hcursor Hprefix Hsuffix)
    as [Hexecution Hafter].
  split; [exact Hexecution|].
  eapply task_create_tcb_return_source; [exact Hentry|exact Hafter].
Qed.
