(** Extracted from a passed fixed check; ordinary integration is pending. *)
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import SimpleC.SL.Mem.
Require Import SimpleC.SL.ConAssertion.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.micromega.Lia.
From SimpleC.SL Require Import ArrayLib.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import AUXLib.ListLib.
From MonadLib Require Import Monad.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.VC.code.core.spec.kernel_idle_ready_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_api_entry_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_fields_resources_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_resources_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_unlink_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_unlink_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_always_nonswitch_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_wake_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_inherit_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_api_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_region_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_fields_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_local_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_sched_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_save_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_wake_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_client_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_irq_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_disabled_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_delete_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_nontimer_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_irq_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Import Ucos2Verify.VC.code.task.spec.flag_fields_publication_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_return_stage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_api_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_idle_guard_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.flag_node_fields.
Require Import Ucos2Verify.lib.flag_stack.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_execution.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.task_retirement.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_selected_completion_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_return_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_completion_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_call_value_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_terminal_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


(** Compose the original approved Save/Restore C primitive with the SAME
    environment sequence.  The selected-return producer computes [call]
    before these lemmas are used.  No endpoint-equal replacement run or
    extra source/cache/ready premise is introduced here. *)
Module SelectedCompletionSuffix.
Import CriticalComponent PrimitiveComponent SelectedReturnPrimitive TaskSelectedCompletion IRQSelectedCompletion.

Lemma kernel_program_return_c_sequence_resources :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_c_sequence (kernel_program_return_c_step environment critical sg observer origin)
    state before input stopped current after output -> input before /\ output after.
Proof.
  intros environment critical sg observer origin.
  apply kernel_c_sequence_resources.
  exact (kernel_program_return_c_step_resources environment critical sg observer origin).
Qed.

Lemma kernel_selected_c_sequence_restore_completion :
  forall environment critical sg observer origin local active call saved acquired
    initial before input stopped current restored arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written middle final_cursor after,
  kernel_c_sequence (kernel_program_return_c_step environment critical sg observer origin)
    initial before input stopped current restored
    (flag_pend_caller_restore_input environment critical local active sg
      (FlagPendTaskCaller call) call saved acquired current) ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor restored written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  let event := flag_pend_task_restore_c_event environment critical local active sg call saved acquired current restored after in
  flag_pend_task_primitive_c_event environment critical sg event /\
  kernel_c_sequence (kernel_program_return_c_step environment critical sg observer origin)
    initial before input stopped current after event.(flag_pend_event_output).
Proof.
  intros environment critical sg observer origin local active call saved acquired initial before input stopped current restored
    arch restore cursor written middle final_cursor after Hrun Hr0 Hmask Hprefix Hsuffix event.
  pose proof (proj2 (kernel_program_return_c_sequence_resources environment critical sg observer origin
    initial before input stopped current restored _ Hrun)) as Hinput.
  assert (Hprimitive : flag_pend_task_primitive_c_event environment critical sg event).
  { unfold event; eapply FlagPendTaskPrimitiveRestore; eassumption. }
  split; [exact Hprimitive|].
  replace stopped with (orb stopped false) at 1 by apply Bool.orb_false_r.
  eapply KernelCSequenceThen; [exact Hrun|intros h H; exact H|].
  apply KernelCSequenceAtom, KernelProgramReturnOriginal, KernelProgramCPairedPrimitive.
  exact (FlagPendTaskPrimitiveCStep environment critical sg event Hprimitive).
Qed.

Lemma kernel_selected_c_sequence_save_completion :
  forall environment critical sg observer origin local active call mask
    initial before input stopped current resumed arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers final_registers after,
  kernel_c_sequence (kernel_program_return_c_step environment critical sg observer origin)
    initial before input stopped current resumed
    (flag_pend_caller_save_input environment critical local active sg
      (FlagPendTaskCaller call) call mask current) ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current resumed
    final_registers current after ->
  let event := flag_pend_task_save_c_event environment critical local active sg call mask
    final_registers.(kernel_save_r0) current resumed after in
  flag_pend_task_primitive_c_event environment critical sg event /\
  kernel_c_sequence (kernel_program_return_c_step environment critical sg observer origin)
    initial before input stopped current after event.(flag_pend_event_output).
Proof.
  intros environment critical sg observer origin local active call mask initial before input stopped current resumed
    arch save registers final_registers after Hrun Hnone Hvalid Hmask Hsuffix event.
  pose proof (proj2 (kernel_program_return_c_sequence_resources environment critical sg observer origin
    initial before input stopped current resumed _ Hrun)) as Hinput.
  assert (Hprimitive : flag_pend_task_primitive_c_event environment critical sg event).
  { unfold event; eapply FlagPendTaskPrimitiveSave; eassumption. }
  split; [exact Hprimitive|].
  replace stopped with (orb stopped false) at 1 by apply Bool.orb_false_r.
  eapply KernelCSequenceThen; [exact Hrun|intros h H; exact H|].
  apply KernelCSequenceAtom, KernelProgramReturnOriginal, KernelProgramCPairedPrimitive.
  exact (FlagPendTaskPrimitiveCStep environment critical sg event Hprimitive).
Qed.

(** The concrete Task route includes the install, its exact selected
    return and the real following Restore.  Its output is the existing
    primitive event output, ready for a subsequent Save/completion. *)
Lemma task_selected_c_restore_completion :
  forall environment critical
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    sg observer origin frame call original saved acquired receipt other
    before installed sp actual selected restored arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written middle final_cursor after,
  let local := FlagPendSchedulerResources.kernel_sched_saved_local_resource_at
    environment.(task_stack_call_platform) critical sg
    call.(InstallComponent.task_install_fields_entry).(TskState) original saved acquired receipt other in
  let rest := armv7a_task_switch_control task_abi call.(InstallComponent.task_install_fields_context) **
    unmap_table_rep sg ** frame in
  forall (complete : InstallComponent.task_install_c_segment environment local sg rest call before installed sp actual),
  TerminalReturn.task_install_selected_owner environment local sg rest call selected installed ->
  call.(InstallComponent.task_install_fields_incoming) = original.(os_sched_call_stack) ->
  task_stack_live_coverage call.(InstallComponent.task_install_fields_entry).(TskState)
    (Some (task_stack_key call.(InstallComponent.task_install_fields_context).(os_sched_call_stack))) ->
  armv7a_task_restore_transition task_abi call.(InstallComponent.task_install_fields_context) selected installed restored ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor restored written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  let current := InstallComponent.task_install_fields_current call in
  let returned := kernel_selected_call selected current in
  let event := flag_pend_task_restore_c_event environment critical other (fun _ _ => receipt ** frame)
    sg returned saved acquired current restored after in
  flag_pend_task_primitive_c_event environment critical sg event /\
  kernel_c_sequence (kernel_program_return_c_step environment critical sg observer origin)
    call.(InstallComponent.task_install_fields_entry) before
    (InstallComponent.task_install_fields_entry_owner environment local sg call ** rest) false current after
    event.(flag_pend_event_output) /\
  kernel_call_task_source returned current /\ task_tcb_init_stack_same_call returned original.
Proof.
  intros environment critical task_abi sg observer origin frame call original saved acquired receipt other
    before installed sp actual selected restored arch restore cursor written middle final_cursor after
    local rest complete Hselected Hincoming Hcoverage Hreturn Hr0 Hmask Hprefix Hsuffix current returned event.
  destruct (task_selected_c_completion_sequence environment critical task_abi sg observer origin frame call original
    saved acquired receipt other before installed sp actual selected restored complete
    Hselected Hincoming Hcoverage Hreturn) as [Hrun [Hsource Hsame]].
  destruct (kernel_selected_c_sequence_restore_completion environment critical sg observer origin other
    (fun _ _ => receipt ** frame) returned saved acquired call.(InstallComponent.task_install_fields_entry)
    before _ false current restored arch restore cursor written middle final_cursor after
    Hrun Hr0 Hmask Hprefix Hsuffix) as [Hprimitive Hcomplete].
  exact (conj Hprimitive (conj Hcomplete (conj Hsource Hsame))).
Qed.

Lemma irq_selected_c_restore_completion :
  forall environment critical sg observer origin handler entry transfer original saved acquired receipt other frame
    before installed selected restored source install irq_restore arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written middle final_cursor after,
  kernel_irq_selected_suffix_c_completion environment critical sg handler entry transfer original saved acquired receipt other
    frame before installed selected restored source install irq_restore ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor restored written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  let returned := TerminalCallValue.kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack)
    transfer.(os_int_exit_incoming_fragments) in
  let current := os_int_exit_installed_state transfer in
  let event := flag_pend_task_restore_c_event environment critical other
    (fun _ _ => irq_selected_suffix_receipt handler receipt frame) sg returned saved acquired current restored after in
  flag_pend_task_primitive_c_event environment critical sg event /\
  kernel_c_sequence (kernel_program_return_c_step environment critical sg observer origin)
    transfer.(os_int_exit_hooked_state) before
    (irq_selected_suffix_input environment critical sg handler transfer original saved acquired receipt other frame)
    false current after event.(flag_pend_event_output) /\
  kernel_call_task_source returned current /\ task_tcb_init_stack_same_call returned original.
Proof.
  intros environment critical sg observer origin handler entry transfer original saved acquired receipt other frame
    before installed selected restored source install irq_restore arch restore cursor written middle final_cursor after
    Hcomplete Hr0 Hmask Hprefix Hsuffix returned current event.
  assert (Hrun : kernel_c_sequence (kernel_program_return_c_step environment critical sg observer origin)
    transfer.(os_int_exit_hooked_state) before
    (irq_selected_suffix_input environment critical sg handler transfer original saved acquired receipt other frame)
    false current restored (irq_selected_suffix_output environment critical sg handler transfer original saved acquired receipt other frame)).
  { apply KernelCSequenceAtom; eapply KernelProgramReturnIRQSelectedSuffix; exact Hcomplete. }
  destruct (kernel_selected_c_sequence_restore_completion environment critical sg observer origin other
    (fun _ _ => irq_selected_suffix_receipt handler receipt frame) returned saved acquired
    transfer.(os_int_exit_hooked_state) before _ false current restored arch restore cursor written middle final_cursor after
    Hrun Hr0 Hmask Hprefix Hsuffix) as [Hprimitive Hrun_after].
  split; [exact Hprimitive|]. split; [exact Hrun_after|]. split.
  - exact (kernel_irq_selected_suffix_c_completion_task_source environment critical sg handler entry transfer
      original saved acquired receipt other frame before installed selected restored source install irq_restore Hcomplete).
  - destruct Hcomplete as [Hinput Hincoming Horigin Hactive Hterminal].
    unfold returned, TerminalCallValue.kernel_restored_stack_call, task_tcb_init_stack_same_call; cbn; auto.
Qed.

End SelectedCompletionSuffix.
