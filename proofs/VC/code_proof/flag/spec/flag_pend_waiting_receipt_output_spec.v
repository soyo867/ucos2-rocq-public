Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_phase_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_selected_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_waiting_environment_consumer_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagWaitingReceiptCaller.
Import PrimitiveComponent CriticalComponent.
Import SelectedEnvironmentCProgram SelectedEnvironmentCSource SelectedEnvironmentScopedEnvironment.
Import FlagWaitingEnvironmentConsumer.

(** The concrete publication/Task-or-IRQ producer supplies this run and
    the proved recovery of its computed receipt.  The two ABI transitions
    below are the closing return and the original caller's Save suffix. *)
Lemma environment_receipt_save_active_output :
  forall environment critical initial_local next_local initial_private active receipt frame sg original
    closing_saved closing_acquired initial first_heap stopped returned current restored
    closing_arch
    (closing_restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical closing_arch)
    closing_cursor closing_written closing_middle closing_final environment_heap
    caller_heap private_before save_arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical save_arch)
    registers final_registers whole_after
    (run : kernel_c_sequence (kernel_program_environment_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap
      (flag_pend_caller_save_input environment critical initial_local active sg
        (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask closing_saved) initial ** initial_private)
      stopped current restored
      (coq_prop (flag_pend_call_endpoint_observations environment sg
        (FlagPendTaskCaller original) original initial returned current) &&
       flag_pend_caller_restore_input environment critical next_local (fun _ _ => receipt ** frame) sg
        (FlagPendTaskCaller returned) returned closing_saved closing_acquired current)),
  kernel_program_environment_c_sequence_source environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ run ->
  (receipt |-- active returned current) ->
  closing_cursor.(kernel_restore_r0) = closing_saved ->
  armv7a_irq_fiq_mask closing_cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition closing_restore closing_cursor restored closing_written closing_middle ->
  armv7a_restore_suffix_transition closing_restore closing_written closing_middle closing_final environment_heap ->
  flag_pend_caller_save_input environment critical initial_local active sg
    (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask closing_saved) initial caller_heap ->
  initial_private private_before -> join caller_heap private_before first_heap ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask closing_saved ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current environment_heap
    final_registers current whole_after ->
  kernel_call_task_source returned current ->
  exists last_heap,
    CompletedCallerEvents.flag_pend_selected_caller_save_event environment critical initial_local active sg
      (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask closing_saved) final_registers.(kernel_save_r0) initial
      (FlagPendTaskCaller returned) returned current next_local caller_heap last_heap /\
    FlagPendActiveCaller.flag_pend_selected_caller_save_output environment critical initial_local active sg
      (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask closing_saved) initial caller_heap
      final_registers.(kernel_save_r0) last_heap.
Proof.
  intros environment critical initial_local next_local initial_private active receipt frame sg original
    closing_saved closing_acquired initial first_heap stopped returned current restored closing_arch closing_restore
    closing_cursor closing_written closing_middle closing_final environment_heap caller_heap private_before save_arch save
    registers final_registers whole_after run Hsource Hrecover Hclosing_r0 Hclosing_mask Hclosing_prefix Hclosing_suffix
    Hinput Hprivate Hjoin Hreturn Hvalid Hmask Hsuffix Hreturned.
  destruct (environment_receipt_return_environment environment critical initial_local next_local initial_private active receipt frame sg
    original closing_saved closing_acquired initial first_heap stopped returned current restored closing_arch closing_restore
    closing_cursor closing_written closing_middle closing_final environment_heap run
    Hsource Hrecover Hclosing_r0 Hclosing_mask Hclosing_prefix Hclosing_suffix) as [scoped Hscoped].
  exact (environment_scoped_save_active_output environment critical initial_local next_local active sg
    original (armv7a_irq_fiq_mask closing_saved) initial caller_heap initial_private frame private_before first_heap
    (orb stopped false) returned current environment_heap save_arch save registers final_registers whole_after scoped
    Hscoped Hinput Hprivate Hjoin Hreturn Hvalid Hmask Hsuffix Hreturned).
Qed.

(** The closing saved word and the outer caller's saved word are distinct.
    Only their actual restored masks agree.  The caller's original preheap
    and the real Restore prefix heap remain separate indices. *)
Lemma environment_receipt_restore_active_output :
  forall environment critical initial_local next_local initial_private active receipt frame sg original
    closing_saved closing_acquired initial prefix_heap stopped returned current restored
    closing_arch
    (closing_restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical closing_arch)
    closing_cursor closing_written closing_middle closing_final environment_heap
    outer_saved outer_acquired caller_heap private_before whole_before restore_arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical restore_arch)
    cursor written final_cursor whole_after
    (run : kernel_c_sequence (kernel_program_environment_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial prefix_heap
      (flag_pend_caller_save_input environment critical initial_local active sg
        (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask closing_saved) initial ** initial_private)
      stopped current restored
      (coq_prop (flag_pend_call_endpoint_observations environment sg
        (FlagPendTaskCaller original) original initial returned current) &&
       flag_pend_caller_restore_input environment critical next_local (fun _ _ => receipt ** frame) sg
        (FlagPendTaskCaller returned) returned closing_saved closing_acquired current)),
  kernel_program_environment_c_sequence_source environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ run ->
  (receipt |-- active returned current) ->
  closing_cursor.(kernel_restore_r0) = closing_saved ->
  armv7a_irq_fiq_mask closing_cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition closing_restore closing_cursor restored closing_written closing_middle ->
  armv7a_restore_suffix_transition closing_restore closing_written closing_middle closing_final environment_heap ->
  armv7a_irq_fiq_mask outer_saved = armv7a_irq_fiq_mask closing_saved ->
  cursor.(kernel_restore_r0) = outer_saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical initial_local active sg
    (FlagPendTaskCaller original) original outer_saved outer_acquired initial caller_heap ->
  initial_private private_before -> join caller_heap private_before whole_before ->
  armv7a_restore_prefix_transition restore cursor whole_before written prefix_heap ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor whole_after ->
  kernel_call_task_source returned current ->
  exists last_heap,
    CompletedCallerEvents.flag_pend_selected_caller_restore_event environment critical initial_local active sg
      (FlagPendTaskCaller original) original outer_saved outer_acquired initial
      (FlagPendTaskCaller returned) returned current next_local caller_heap last_heap /\
    FlagPendActiveCaller.flag_pend_selected_caller_restore_output environment critical initial_local active sg
      (FlagPendTaskCaller original) original outer_saved outer_acquired initial caller_heap last_heap.
Proof.
  intros environment critical initial_local next_local initial_private active receipt frame sg original
    closing_saved closing_acquired initial prefix_heap stopped returned current restored closing_arch closing_restore
    closing_cursor closing_written closing_middle closing_final environment_heap outer_saved outer_acquired caller_heap
    private_before whole_before restore_arch restore cursor written final_cursor whole_after run
    Hsource Hrecover Hclosing_r0 Hclosing_mask Hclosing_prefix Hclosing_suffix
    Hrestored_mask Hr0 Hmask Hinput Hprivate Hjoin Hprefix Hsuffix Hreturned.
  destruct (environment_receipt_return_environment environment critical initial_local next_local initial_private active receipt frame sg
    original closing_saved closing_acquired initial prefix_heap stopped returned current restored closing_arch closing_restore
    closing_cursor closing_written closing_middle closing_final environment_heap run
    Hsource Hrecover Hclosing_r0 Hclosing_mask Hclosing_prefix Hclosing_suffix) as [scoped Hscoped].
  assert (Hsaved_environment : exists (saved_run : flag_pend_scoped_environment_run environment critical initial_local next_local active sg
    original (armv7a_irq_fiq_mask outer_saved) initial prefix_heap initial_private
    (orb stopped false) returned current environment_heap frame),
    flag_pend_scoped_environment_source environment critical initial_local next_local active sg None
      original (armv7a_irq_fiq_mask outer_saved) initial prefix_heap initial_private
      (orb stopped false) returned current environment_heap frame saved_run).
  { rewrite Hrestored_mask; exists scoped; exact Hscoped. }
  destruct Hsaved_environment as [saved_run Hsaved_source].
  exact (environment_scoped_restore_active_output environment critical initial_local next_local active sg
    original outer_saved outer_acquired initial caller_heap initial_private frame private_before whole_before
    (orb stopped false) returned current environment_heap restore_arch restore cursor written prefix_heap final_cursor whole_after saved_run
    Hr0 Hmask Hinput Hprivate Hjoin Hprefix Hsaved_source Hsuffix Hreturned).
Qed.

End FlagWaitingReceiptCaller.
