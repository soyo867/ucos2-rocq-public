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
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_c_environment_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


(** The marker below belongs to the very middle execution selected by the
    C call.  Its constructors retain the real module call/allocation
    identities; it is not an endpoint preservation premise. *)
Module ContinuationPhaseSource.
Import CriticalComponent PrimitiveComponent SelectedCProgram SelectedCSource SelectedEnvironment.

Definition flag_pend_task_c_environment_call_source environment critical local next_local active sg
  event_observer original mask before first_heap stopped returned current last_heap
  (run : flag_pend_task_c_environment_run environment critical local next_local active sg
    original mask before first_heap stopped returned current last_heap) : Prop :=
  kernel_program_selected_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer
    before first_heap
    (flag_pend_caller_save_input environment critical local active sg
      (FlagPendTaskCaller original) original mask before)
    stopped current last_heap
    (flag_pend_task_c_environment_output environment critical next_local active sg
      original before returned current mask) run.

Lemma flag_pend_task_c_environment_call_source_frames :
  forall environment critical local next_local active sg event_observer
    original mask before first_heap stopped returned current last_heap
    (run : flag_pend_task_c_environment_run environment critical local next_local active sg
      original mask before first_heap stopped returned current last_heap),
  flag_pend_task_c_environment_call_source environment critical local next_local active sg
    event_observer original mask before first_heap stopped returned current last_heap run ->
  task_creation_frame original.(os_sched_call_invocation) before.(TskState) current.(TskState) /\
  (forall invocation, event_observer = Some invocation ->
    event_creation_frame invocation before.(EventState) current.(EventState)) /\
  before.(NameState) = current.(NameState) /\
  timer_public_trace sg before.(TimerState) current.(TimerState).
Proof.
  intros until run; intro Hsource.
  eapply kernel_program_selected_c_sequence_source_frames; exact Hsource.
Qed.

(** The suffix and its label are constructed together.  In particular the
    existential below contains the proof used by the returned source
    marker, rather than an independently chosen endpoint-equal tree. *)
Lemma flag_pend_task_environment_save_sequence_source :
  forall environment critical local next_local active sg event_observer original mask before first_heap
    stopped returned current environment_heap arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers final_registers last_heap
    (run : flag_pend_task_c_environment_run environment critical local next_local active sg
      original mask before first_heap stopped returned current environment_heap),
  flag_pend_task_c_environment_call_source environment critical local next_local active sg
    event_observer original mask before first_heap stopped returned current environment_heap run ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current environment_heap
    final_registers current last_heap ->
  interrupt_saved_value mask final_registers.(kernel_save_r0) /\
  exists (completed : kernel_c_sequence_spec.kernel_c_sequence
    (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    before first_heap
    (flag_pend_caller_save_input environment critical local active sg
      (FlagPendTaskCaller original) original mask before)
    stopped current last_heap
    (coq_prop (flag_pend_call_endpoint_observations environment sg
       (FlagPendTaskCaller original) original before returned current) &&
     flag_pend_caller_restore_input environment critical next_local active sg
       (FlagPendTaskCaller returned) returned final_registers.(kernel_save_r0) current current)),
  kernel_program_selected_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer
    _ _ _ _ _ _ _ completed.
Proof.
  intros environment critical local next_local active sg event_observer original mask before first_heap
    stopped returned current environment_heap arch save registers final_registers last_heap run
    Hsource Hreturn Hvalid Hmask Hsuffix.
  destruct (flag_pend_task_c_environment_resources environment critical local next_local active sg
    original mask before first_heap stopped returned current environment_heap run)
    as [Hinitial [Hobservations Hclosed]].
  destruct (flag_pend_task_uninterrupted_save_resources environment critical sg
    next_local active returned mask current arch save registers environment_heap final_registers last_heap
    Hreturn Hvalid Hmask Hclosed Hsuffix) as [Hsaved Hmasked].
  split; [exact Hsaved|].
  assert (Hprimitive : flag_pend_task_primitive_c_step environment critical sg
    current environment_heap
    (flag_pend_caller_save_input environment critical next_local active sg
      (FlagPendTaskCaller returned) returned mask current)
    false current last_heap
    ((flag_pend_task_save_c_event environment critical next_local active sg
      returned mask final_registers.(kernel_save_r0) current environment_heap last_heap)
      .(flag_pend_event_output))).
  { apply (FlagPendTaskPrimitiveCStep environment critical sg
      (flag_pend_task_save_c_event environment critical next_local active sg
        returned mask final_registers.(kernel_save_r0) current environment_heap last_heap)).
    eapply FlagPendTaskPrimitiveSave; eassumption. }
  pose (Hstep := @kernel_program_selected_paired_primitive environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    _ _ _ _ _ _ _ Hprimitive).
  pose (Hatom := kernel_c_sequence_spec.KernelCSequenceAtom _ _ _ _ _ _ _ _ Hstep).
  pose (Htail := kernel_c_sequence_spec.KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _
    (conj Hobservations Hclosed)
    (fun heap Howner => proj2 Howner) Hatom
    (fun heap Howner => conj Hobservations (proj2 Howner))).
  replace stopped with (orb stopped false) by apply Bool.orb_false_r.
  exists (kernel_c_sequence_spec.KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _
    run (fun heap Howner => Howner) Htail).
  unfold kernel_program_selected_c_sequence_source.
  apply KernelCSourceThen.
  - exact Hsource.
  - unfold Htail; apply KernelCSourceAdapt.
    unfold Hatom; apply KernelCSourceAtom.
    unfold Hstep; apply kernel_program_selected_paired_primitive_source.
Qed.

Lemma flag_pend_task_environment_restore_sequence_source :
  forall environment critical local next_local active sg event_observer original saved acquired before first_heap
    stopped returned current arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written prefix_heap environment_heap final_cursor last_heap
    (run : flag_pend_task_c_environment_run environment critical local next_local active sg
      original (armv7a_irq_fiq_mask saved) before prefix_heap stopped returned current environment_heap),
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before first_heap ->
  armv7a_restore_prefix_transition restore cursor first_heap written prefix_heap ->
  flag_pend_task_c_environment_call_source environment critical local next_local active sg
    event_observer original (armv7a_irq_fiq_mask saved) before prefix_heap stopped returned current environment_heap run ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor last_heap ->
  exists (completed : kernel_c_sequence_spec.kernel_c_sequence
    (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    before first_heap
    (flag_pend_caller_restore_input environment critical local active sg
      (FlagPendTaskCaller original) original saved acquired before)
    stopped current last_heap
    (coq_prop (flag_pend_call_endpoint_observations environment sg
       (FlagPendTaskCaller original) original before returned current) &&
     flag_pend_caller_save_input environment critical next_local active sg
       (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current)),
  kernel_program_selected_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer
    _ _ _ _ _ _ _ completed.
Proof.
  intros environment critical local next_local active sg event_observer original saved acquired before first_heap
    stopped returned current arch restore cursor written prefix_heap environment_heap final_cursor last_heap run
    Hr0 Hmask Hinput Hprefix Hsource Hsuffix.
  destruct (flag_pend_task_c_environment_resources environment critical local next_local active sg
    original (armv7a_irq_fiq_mask saved) before prefix_heap stopped returned current environment_heap run)
    as [Hprefix_owned [Hobservations Hclosed]].
  destruct (flag_pend_task_restore_prefix_written_mask environment critical arch restore
    cursor first_heap written prefix_heap saved Hr0 Hprefix) as [word [Hword Hword_mask]].
  assert (Hprefix_primitive : flag_pend_task_primitive_c_step environment critical sg
    before first_heap
    (flag_pend_caller_restore_input environment critical local active sg
      (FlagPendTaskCaller original) original saved acquired before)
    false before prefix_heap
    (flag_pend_caller_save_input environment critical local active sg
      (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) before)).
  { eapply FlagPendTaskRestoreCPrefix; eassumption. }
  assert (Hsuffix_primitive : flag_pend_task_primitive_c_step environment critical sg
    current environment_heap
    (flag_pend_caller_save_input environment critical next_local active sg
      (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current)
    false current last_heap
    (flag_pend_caller_save_input environment critical next_local active sg
      (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current)).
  { rewrite <- Hword_mask.
    eapply FlagPendTaskRestoreCSuffix; [exact Hword| |exact Hsuffix].
    rewrite Hword_mask; exact Hclosed. }
  pose (Hprefix_step := @kernel_program_selected_paired_primitive environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    _ _ _ _ _ _ _ Hprefix_primitive).
  pose (Hprefix_atom := kernel_c_sequence_spec.KernelCSequenceAtom _ _ _ _ _ _ _ _ Hprefix_step).
  pose (Hsuffix_step := @kernel_program_selected_paired_primitive environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    _ _ _ _ _ _ _ Hsuffix_primitive).
  pose (Hsuffix_atom := kernel_c_sequence_spec.KernelCSequenceAtom _ _ _ _ _ _ _ _ Hsuffix_step).
  pose (Htail := kernel_c_sequence_spec.KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _
    (conj Hobservations Hclosed)
    (fun heap Howner => proj2 Howner) Hsuffix_atom
    (fun heap Howner => conj Hobservations Howner)).
  pose (Hmiddle := kernel_c_sequence_spec.KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _
    run (fun heap Howner => Howner) Htail).
  replace stopped with (orb false (orb stopped false)) by (simpl; apply Bool.orb_false_r).
  exists (kernel_c_sequence_spec.KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _
    Hprefix_atom (fun heap Howner => Howner) Hmiddle).
  unfold kernel_program_selected_c_sequence_source.
  apply KernelCSourceThen.
  - unfold Hprefix_atom; apply KernelCSourceAtom.
    unfold Hprefix_step; apply kernel_program_selected_paired_primitive_source.
  - unfold Hmiddle; apply KernelCSourceThen; [exact Hsource|].
    unfold Htail; apply KernelCSourceAdapt.
    unfold Hsuffix_atom; apply KernelCSourceAtom.
    unfold Hsuffix_step; apply kernel_program_selected_paired_primitive_source.
Qed.

End ContinuationPhaseSource.
