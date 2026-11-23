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
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_c_events_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


Module SelectedEnvironment.
(** A selected environment is an actual sequence of the fixed C program.
    Its existing return owner contains the original C endpoint contract.
    The ABI suffix/prefix below is composed with that very sequence; there
    is no independently supplied old source or endpoint-equal replacement
    tree.  State, caller, local resources and heaps may all change in the
    environment.  Its stopped bit is retained, not assumed false. *)
Import CriticalComponent PrimitiveComponent SelectedCProgram SelectedProgramEvents.

Definition flag_pend_task_c_environment_output environment critical next_local active sg
  original before returned current mask : Assertion :=
  coq_prop (flag_pend_call_endpoint_observations environment sg
    (FlagPendTaskCaller original) original before returned current) &&
  flag_pend_caller_save_input environment critical next_local active sg
    (FlagPendTaskCaller returned) returned mask current.

(** This abbreviation selects the actual C interpretation.  Unlike an
    arbitrary linked predicate, it has only the constructors of the fixed
    program and sequence.  It introduces no preservation callback. *)
Definition flag_pend_task_c_environment_run environment critical local next_local active sg
  original mask before first_heap stopped returned current last_heap : Prop :=
  kernel_c_sequence_spec.kernel_c_sequence
    (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    before first_heap
    (flag_pend_caller_save_input environment critical local active sg
      (FlagPendTaskCaller original) original mask before)
    stopped current last_heap
    (flag_pend_task_c_environment_output environment critical next_local active sg
      original before returned current mask).

Lemma flag_pend_task_c_environment_resources :
  forall environment critical local next_local active sg original mask before first_heap
    stopped returned current last_heap,
  flag_pend_task_c_environment_run environment critical local next_local active sg
    original mask before first_heap stopped returned current last_heap ->
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller original) original mask before first_heap /\
  flag_pend_task_c_environment_output environment critical next_local active sg
    original before returned current mask last_heap.
Proof.
  intros until last_heap; intro Hrun.
  eapply kernel_program_selected_c_sequence_resources; exact Hrun.
Qed.

(** A real module's post-to-pre adaptation is performed at the same
    supplied heap.  Neither entailment can change the state or heap.
    This is the entry used by concrete critical, publication, install or
    captured composite C producers. *)
Lemma flag_pend_task_c_environment_from_c_sequence :
  forall environment critical local next_local active sg original mask before first_heap
    input stopped returned current last_heap output,
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller original) original mask before first_heap ->
  (flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller original) original mask before |-- input) ->
  kernel_c_sequence_spec.kernel_c_sequence
    (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    before first_heap input stopped current last_heap output ->
  (output |-- flag_pend_task_c_environment_output environment critical next_local active sg
    original before returned current mask) ->
  flag_pend_task_c_environment_run environment critical local next_local active sg
    original mask before first_heap stopped returned current last_heap.
Proof.
  intros until output; intros Hinput Hopen Hactual Hclose.
  unfold flag_pend_task_c_environment_run.
  eapply kernel_c_sequence_spec.KernelCSequenceAdapt; eassumption.
Qed.

(** General Save environment branch.  The middle sequence may contain
    state-changing C calls and temporary non-closed phases.  The actual
    suffix starts on its exact output heap and returned call. *)
Lemma flag_pend_task_environment_save_sequence :
  forall environment critical local next_local active sg original mask before first_heap
    stopped returned current environment_heap arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers final_registers last_heap,
  flag_pend_task_c_environment_run environment critical local next_local active sg
    original mask before first_heap stopped returned current environment_heap ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current environment_heap
    final_registers current last_heap ->
  interrupt_saved_value mask final_registers.(kernel_save_r0) /\
  kernel_c_sequence_spec.kernel_c_sequence
    (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    before first_heap
    (flag_pend_caller_save_input environment critical local active sg
      (FlagPendTaskCaller original) original mask before)
    stopped current last_heap
    (coq_prop (flag_pend_call_endpoint_observations environment sg
       (FlagPendTaskCaller original) original before returned current) &&
     flag_pend_caller_restore_input environment critical next_local active sg
       (FlagPendTaskCaller returned) returned final_registers.(kernel_save_r0) current current).
Proof.
  intros environment critical local next_local active sg original mask before first_heap
    stopped returned current environment_heap arch save registers final_registers last_heap
    Hrun Hreturn Hvalid Hmask Hsuffix.
  destruct (flag_pend_task_c_environment_resources environment critical local next_local active sg
    original mask before first_heap stopped returned current environment_heap Hrun)
    as [Hinitial [Hobservations Hclosed]].
  pose proof (flag_pend_task_uninterrupted_save_resources environment critical sg
    next_local active returned mask current arch save registers environment_heap final_registers last_heap
    Hreturn Hvalid Hmask Hclosed Hsuffix) as [Hsaved Hmasked].
  split; [exact Hsaved|].
  replace stopped with (orb stopped false) by apply Bool.orb_false_r.
  eapply kernel_c_sequence_spec.KernelCSequenceThen; [exact Hrun| |].
  - intros heap Howner; exact Howner.
  - eapply kernel_c_sequence_spec.KernelCSequenceAdapt with
      (inner_input := flag_pend_caller_save_input environment critical next_local active sg
        (FlagPendTaskCaller returned) returned mask current)
      (inner_output := (flag_pend_task_save_c_event environment critical next_local active sg
        returned mask final_registers.(kernel_save_r0) current environment_heap last_heap)
        .(flag_pend_event_output)).
    + exact (conj Hobservations Hclosed).
    + intros heap Howner; exact (proj2 Howner).
    + apply kernel_c_sequence_spec.KernelCSequenceAtom, kernel_program_selected_paired_primitive.
      apply (FlagPendTaskPrimitiveCStep environment critical sg
        (flag_pend_task_save_c_event environment critical next_local active sg
          returned mask final_registers.(kernel_save_r0) current environment_heap last_heap)).
      eapply FlagPendTaskPrimitiveSave; eassumption.
    + intros heap Howner; exact (conj Hobservations (proj2 Howner)).
Qed.

(** The emitted source is computed from the preceding actual execution.
    No Hsource argument is accepted.  All original event indices,
    including local/next_local and first/last heaps, are fixed here. *)
Lemma flag_pend_task_environment_save_c_event :
  forall environment critical local next_local active sg original mask before first_heap
    stopped returned current environment_heap arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers final_registers last_heap,
  flag_pend_task_c_environment_run environment critical local next_local active sg
    original mask before first_heap stopped returned current environment_heap ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current environment_heap
    final_registers current last_heap ->
  interrupt_saved_value mask final_registers.(kernel_save_r0) /\
  flag_pend_program_c_event environment critical sg
    (flag_pend_task_save_completed_c_event environment critical local next_local active sg
      original mask final_registers.(kernel_save_r0) before first_heap returned current last_heap).
Proof.
  intros until last_heap; intros Hrun Hreturn Hvalid Hmask Hsuffix.
  destruct (flag_pend_task_environment_save_sequence environment critical local next_local active sg
    original mask before first_heap stopped returned current environment_heap arch save
    registers final_registers last_heap Hrun Hreturn Hvalid Hmask Hsuffix) as [Hsaved Hsequence].
  split; [exact Hsaved|]. exists stopped; exact Hsequence.
Qed.

(** The Restore suffix follows the same cursor written by the actual
    prefix.  Its mask equality is projected from that prefix's approved
    source contract; it is not an extra output assumption. *)
Lemma flag_pend_task_restore_prefix_written_mask :
  forall environment critical arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor first_heap written prefix_heap saved,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_restore_prefix_transition restore cursor first_heap written prefix_heap ->
  exists word, written.(kernel_restore_msr_word) = Some word /\
    armv7a_irq_fiq_mask word = armv7a_irq_fiq_mask saved.
Proof.
  intros environment critical arch restore cursor first_heap written prefix_heap saved Hr0 Hprefix.
  pose proof (armv7a_restore_prefix_source _ _ _ _ restore _ _ _ _ Hprefix) as Hsource.
  pose proof (kernel_call_restore_prefix_cursor _ _ _ _ _ Hsource) as Hwritten.
  subst written; cbn [kernel_restore_write_cpsr].
  eexists; split; [reflexivity|].
  rewrite Hr0; apply armv7a_cpsr_restore_mask_eq.
Qed.

Lemma flag_pend_task_environment_restore_sequence :
  forall environment critical local next_local active sg original saved acquired before first_heap
    stopped returned current arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written prefix_heap environment_heap final_cursor last_heap,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before first_heap ->
  armv7a_restore_prefix_transition restore cursor first_heap written prefix_heap ->
  flag_pend_task_c_environment_run environment critical local next_local active sg
    original (armv7a_irq_fiq_mask saved) before prefix_heap stopped returned current environment_heap ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor last_heap ->
  kernel_c_sequence_spec.kernel_c_sequence
    (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    before first_heap
    (flag_pend_caller_restore_input environment critical local active sg
      (FlagPendTaskCaller original) original saved acquired before)
    stopped current last_heap
    (coq_prop (flag_pend_call_endpoint_observations environment sg
       (FlagPendTaskCaller original) original before returned current) &&
     flag_pend_caller_save_input environment critical next_local active sg
       (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current).
Proof.
  intros environment critical local next_local active sg original saved acquired before first_heap
    stopped returned current arch restore cursor written prefix_heap environment_heap final_cursor last_heap
    Hr0 Hmask Hinput Hprefix Hrun Hsuffix.
  destruct (flag_pend_task_c_environment_resources environment critical local next_local active sg
    original (armv7a_irq_fiq_mask saved) before prefix_heap stopped returned current environment_heap Hrun)
    as [Hprefix_owned [Hobservations Hclosed]].
  destruct (flag_pend_task_restore_prefix_written_mask environment critical arch restore
    cursor first_heap written prefix_heap saved Hr0 Hprefix) as [word [Hword Hword_mask]].
  assert (Htail : kernel_c_sequence_spec.kernel_c_sequence
    (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    current environment_heap
    (flag_pend_task_c_environment_output environment critical next_local active sg
      original before returned current (armv7a_irq_fiq_mask saved))
    false current last_heap
    (coq_prop (flag_pend_call_endpoint_observations environment sg
       (FlagPendTaskCaller original) original before returned current) &&
     flag_pend_caller_save_input environment critical next_local active sg
       (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current)).
  { eapply kernel_c_sequence_spec.KernelCSequenceAdapt with
      (inner_input := flag_pend_caller_save_input environment critical next_local active sg
        (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask word) current)
      (inner_output := flag_pend_caller_save_input environment critical next_local active sg
        (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask word) current).
    - exact (conj Hobservations Hclosed).
    - rewrite Hword_mask; intros heap Howner; exact (proj2 Howner).
    - apply kernel_c_sequence_spec.KernelCSequenceAtom, kernel_program_selected_paired_primitive.
      eapply FlagPendTaskRestoreCSuffix; [exact Hword| |exact Hsuffix].
      rewrite Hword_mask; exact Hclosed.
    - rewrite Hword_mask; intros heap Howner; exact (conj Hobservations Howner). }
  replace stopped with (orb false (orb stopped false)) by (simpl; apply Bool.orb_false_r).
  eapply kernel_c_sequence_spec.KernelCSequenceThen.
  - apply kernel_c_sequence_spec.KernelCSequenceAtom, kernel_program_selected_paired_primitive.
    eapply FlagPendTaskRestoreCPrefix; eassumption.
  - intros heap Howner; exact Howner.
  - eapply kernel_c_sequence_spec.KernelCSequenceThen; [exact Hrun| |exact Htail].
    intros heap Howner; exact Howner.
Qed.

Lemma flag_pend_task_environment_restore_c_event :
  forall environment critical local next_local active sg original saved acquired before first_heap
    stopped returned current arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written prefix_heap environment_heap final_cursor last_heap,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before first_heap ->
  armv7a_restore_prefix_transition restore cursor first_heap written prefix_heap ->
  flag_pend_task_c_environment_run environment critical local next_local active sg
    original (armv7a_irq_fiq_mask saved) before prefix_heap stopped returned current environment_heap ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor last_heap ->
  flag_pend_program_c_event environment critical sg
    (flag_pend_task_restore_completed_c_event environment critical local next_local active sg
      original saved acquired before first_heap returned current last_heap).
Proof.
  intros until last_heap; intros Hr0 Hmask Hinput Hprefix Hrun Hsuffix.
  exists stopped.
  eapply flag_pend_task_environment_restore_sequence; eassumption.
Qed.

End SelectedEnvironment.
