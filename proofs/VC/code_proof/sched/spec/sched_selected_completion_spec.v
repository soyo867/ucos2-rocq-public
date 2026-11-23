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
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_return_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_call_value_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_terminal_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


(** From the actual installed C owner to the selected running caller.
    The descriptor is opened in that same post, then the approved return
    primitive consumes it.  The receipt and all remaining resources are
    retained; the subsequent Restore is the existing primitive C event. *)
Module TaskSelectedCompletion.
Import CriticalComponent PrimitiveComponent TerminalReturn TerminalCallValue SelectedReturnPrimitive.
Import FlagPendSchedulerResources.

Definition task_selected_return_frame environment local sg call selected (frame : Assertion) : Assertion :=
  local selected ** kernel_program_fields_inv sg (InstallComponent.task_install_fields_current call) **
  store_parked_continuations (InstallComponent.task_install_fields_saved_resource environment local call)
    (InstallComponent.task_install_fields_current call).(TskState).(parkedTaskStacks) ** frame.

Lemma task_install_selected_owner_return_reads :
  forall environment local sg frame call selected installed,
  task_install_selected_owner environment local sg frame call selected installed ->
  armv7a_continuation_restore_reads selected installed.
Proof.
  intros environment local sg frame call selected installed Howner.
  destruct (task_install_selected_owner_tuple environment local sg frame call selected installed Howner)
    as [Hstack Hfragments].
  assert (Hfacts : task_install_selected_owner environment local sg frame call selected |--
    coq_prop (armv7a_continuation_binding selected /\ armv7a_task_frame_slice selected) &&
    task_install_selected_owner environment local sg frame call selected).
  { unfold task_install_selected_owner; Intros; entailer!; tauto. }
  destruct (proj1 (Hfacts installed Howner)) as [Hbinding Hslice].
  eapply armv7a_task_frame_slice_restore_reads; [exact Hbinding|exact Hslice|].
  assert (Horder : task_install_selected_owner environment local sg frame call selected |--
    task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
      selected.(armv7a_continuation_fragments) **
    (UCOS2_fields_inv sg (InstallComponent.task_install_fields_current call) **
     (coq_prop (armv7a_continuation_binding selected /\
       task_stack_key selected.(armv7a_continuation_stack) =
         task_stack_key call.(InstallComponent.task_install_fields_incoming) /\
       (selected.(armv7a_continuation_stack).(stackLeaseRegion), selected.(armv7a_continuation_fragments)) =
         (call.(InstallComponent.task_install_fields_incoming).(stackLeaseRegion),
          call.(InstallComponent.task_install_fields_resumed)) /\
       armv7a_task_frame_slice selected /\
       task_stack_live_sp call.(InstallComponent.task_install_fields_entry).(TskState)
         (task_stack_key call.(InstallComponent.task_install_fields_incoming)) selected.(armv7a_continuation_sp)) &&
       (armv7a_task_continuation_resource environment.(task_stack_call_continuations) selected ** local selected)) **
     store_parked_continuations (InstallComponent.task_install_fields_saved_resource environment local call)
       (InstallComponent.task_install_fields_current call).(TskState).(parkedTaskStacks) ** frame)).
  { rewrite Hstack, Hfragments; unfold task_install_selected_owner; entailer!. }
  exact (Horder installed Howner).
Qed.

Lemma task_install_selected_owner_return_input :
  forall environment task_abi local sg frame call selected,
  selected.(armv7a_continuation_stack) = call.(InstallComponent.task_install_fields_incoming) ->
  selected.(armv7a_continuation_fragments) = call.(InstallComponent.task_install_fields_resumed) ->
  task_install_selected_owner environment local sg
    (armv7a_task_switch_control task_abi call.(InstallComponent.task_install_fields_context) **
      unmap_table_rep sg ** frame) call selected |--
  task_selected_return_input environment task_abi call.(InstallComponent.task_install_fields_context) selected
    (task_selected_return_frame environment local sg call selected frame).
Proof.
  intros environment task_abi local sg frame call selected Hstack Hfragments.
  unfold task_selected_return_input, task_selected_return_frame, task_install_selected_owner.
  rewrite kernel_program_fields_inv_split_unmap, Hstack, Hfragments; Intros; entailer!.
Qed.

Lemma task_install_selected_owner_saved_facts :
  forall environment critical sg frame call original saved acquired receipt other selected installed,
  let local := kernel_sched_saved_local_resource_at environment.(task_stack_call_platform) critical sg
    call.(InstallComponent.task_install_fields_entry).(TskState) original saved acquired receipt other in
  selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) ->
  task_install_selected_owner environment local sg frame call selected installed ->
  selected.(armv7a_continuation_call) = Some original /\
  armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) = 192 /\
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) /\
  task_invocation_active call.(InstallComponent.task_install_fields_entry).(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin).
Proof.
  intros environment critical sg frame call original saved acquired receipt other selected installed local Hstack Howner.
  destruct Howner as [owned [rest [Hjoin [Howned Hframe]]]].
  destruct Howned as [left [parked [Hjoin_parked [Hleft Hparked]]]].
  destruct Hleft as [fields_fragments [capsule [Hjoin_capsule [Hfields_fragments [Hbinding Hcapsule]]]]].
  destruct Hcapsule as [arch_heap [local_heap [Hjoin_local [Harch Hlocal]]]].
  unfold local in Hlocal.
  rewrite (kernel_sched_saved_local_resource_at_selected environment.(task_stack_call_platform) critical sg
    call.(InstallComponent.task_install_fields_entry).(TskState) original saved acquired receipt other
    selected Hstack) in Hlocal.
  destruct Hlocal as [saved_heap [receipt_heap [Hjoin_receipt [[Hfacts Hsaved_owner] Hreceipt]]]].
  destruct Hfacts as [Hcall [Hpc [Hmask [Horigin Hactive]]]].
  exact (conj Hcall (conj Hmask (conj Horigin Hactive))).
Qed.

Lemma task_selected_return_output_masked :
  forall environment critical sg call original saved acquired receipt other selected frame,
  let local := kernel_sched_saved_local_resource_at environment.(task_stack_call_platform) critical sg
    call.(InstallComponent.task_install_fields_entry).(TskState) original saved acquired receipt other in
  let current := InstallComponent.task_install_fields_current call in
  let returned := kernel_selected_call selected current in
  selected.(armv7a_continuation_call) = Some original ->
  selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) ->
  call.(InstallComponent.task_install_fields_incoming) = original.(os_sched_call_stack) ->
  armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) = 192 ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_live_coverage call.(InstallComponent.task_install_fields_entry).(TskState)
    (Some (task_stack_key call.(InstallComponent.task_install_fields_context).(os_sched_call_stack))) ->
  task_selected_return_output environment selected
    (task_selected_return_frame environment local sg call selected frame) |--
  flag_pend_caller_restore_input environment critical other (fun _ _ => receipt ** frame) sg
    (FlagPendTaskCaller returned) returned saved acquired current.
Proof.
  intros environment critical sg call original saved acquired receipt other selected frame local current returned
    Hcall Hstack Hincoming Hmask Horigin Hcoverage.
  assert (Hreturned : returned = armv7a_continuation_resumed_call selected original).
  { unfold returned, kernel_selected_call; rewrite Hcall; reflexivity. }
  assert (Hcovered : task_stack_live_coverage current.(TskState)
    (Some (task_stack_key original.(os_sched_call_stack)))).
  { unfold current, InstallComponent.task_install_fields_current.
    rewrite <- Hincoming.
    exact (task_stack_take_covers_selected
      (glob_task_set_parked_stacks call.(InstallComponent.task_install_fields_entry).(TskState)
        (task_stack_park_fragments call.(InstallComponent.task_install_fields_entry).(TskState).(parkedTaskStacks)
          call.(InstallComponent.task_install_fields_context).(os_sched_call_stack)
          call.(InstallComponent.task_install_fields_outgoing)))
      call.(InstallComponent.task_install_fields_incoming)
      (task_stack_park_covers_active _ _ _ Hcoverage)). }
  assert (Habsent : current.(TskState).(parkedTaskStacks)
    (task_stack_key original.(os_sched_call_stack)) = None).
  { unfold current, InstallComponent.task_install_fields_current; rewrite <- Hincoming; apply task_stack_take_lookup. }
  assert (Hmap : store_parked_continuations
    (InstallComponent.task_install_fields_saved_resource environment local call) current.(TskState).(parkedTaskStacks) |--
    store_parked_continuations
      (kernel_saved_continuation_entry environment.(task_stack_call_continuations) current.(TskState) other)
      current.(TskState).(parkedTaskStacks)).
  { change (store_parked_continuations
      (kernel_saved_continuation_entry environment.(task_stack_call_continuations) current.(TskState) local)
      current.(TskState).(parkedTaskStacks) |--
    store_parked_continuations
      (kernel_saved_continuation_entry environment.(task_stack_call_continuations) current.(TskState) other)
      current.(TskState).(parkedTaskStacks)).
    unfold local; apply kernel_saved_continuation_resource_map_unfocus_absent; exact Habsent. }
  assert (Hlocal : local selected = kernel_sched_saved_local environment.(task_stack_call_platform) critical sg
    call.(InstallComponent.task_install_fields_entry).(TskState) original saved acquired selected ** receipt).
  { unfold local; apply kernel_sched_saved_local_resource_at_selected; exact Hstack. }
  assert (Hclose : task_selected_return_output environment selected
    (task_selected_return_frame environment local sg call selected frame) |--
    kernel_continuation_call_masked environment.(task_stack_call_continuations)
      kernel_program_fields_inv other critical sg (task_stack_call_active_key returned)
      returned saved acquired current ** (receipt ** frame)).
  {
  unfold task_selected_return_output, task_selected_return_frame.
  change (armv7a_task_restored_execution environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) selected **
    (local selected ** kernel_program_fields_inv sg current **
     store_parked_continuations (InstallComponent.task_install_fields_saved_resource environment local call)
       current.(TskState).(parkedTaskStacks) ** frame) |--
    kernel_continuation_call_masked environment.(task_stack_call_continuations)
      kernel_program_fields_inv other critical sg (task_stack_call_active_key returned)
      returned saved acquired current ** (receipt ** frame)).
  sep_apply_l_atomic Hmap; rewrite Hlocal.
  assert (Hkey : task_stack_call_active_key returned = Some (task_stack_key original.(os_sched_call_stack))).
  { rewrite Hreturned; unfold task_stack_call_active_key, armv7a_continuation_resumed_call; cbn; rewrite Horigin; reflexivity. }
  rewrite Hkey.
  unfold kernel_continuation_call_masked, kernel_continuation_inv, armv7a_task_restored_execution.
  rewrite Hcall, Hmask, Hreturned.
  unfold kernel_sched_saved_local, kernel_call_execution_owned, critical_region_masked,
    armv7a_continuation_resumed_call; cbn [os_sched_call_invocation os_sched_call_origin]; entailer!.
  }
  intros heap Howned.
  apply (proj2 (flag_pend_task_restore_input_masked_equiv
    environment critical other (fun _ _ => receipt ** frame) sg returned saved acquired current)).
  exact (Hclose heap Howned).
Qed.

(** A genuine sequence on the same install proof and middle heap.  The
    first atom captures the selected descriptor in the actual C post;
    the second atom is its real platform return, with the static owner
    entailment as the only bridge.  Returned is computed, not supplied. *)
Lemma task_selected_c_completion_sequence :
  forall environment critical
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    sg observer origin frame call original saved acquired receipt other
    before installed sp actual selected restored,
  let local := kernel_sched_saved_local_resource_at environment.(task_stack_call_platform) critical sg
    call.(InstallComponent.task_install_fields_entry).(TskState) original saved acquired receipt other in
  let rest := armv7a_task_switch_control task_abi call.(InstallComponent.task_install_fields_context) **
    unmap_table_rep sg ** frame in
  forall (complete : InstallComponent.task_install_c_segment environment local sg rest call before installed sp actual),
  task_install_selected_owner environment local sg rest call selected installed ->
  call.(InstallComponent.task_install_fields_incoming) = original.(os_sched_call_stack) ->
  task_stack_live_coverage call.(InstallComponent.task_install_fields_entry).(TskState)
    (Some (task_stack_key call.(InstallComponent.task_install_fields_context).(os_sched_call_stack))) ->
  armv7a_task_restore_transition task_abi call.(InstallComponent.task_install_fields_context) selected installed restored ->
  let current := InstallComponent.task_install_fields_current call in
  let returned := kernel_selected_call selected current in
  kernel_c_sequence (kernel_program_return_c_step environment critical sg observer origin)
    call.(InstallComponent.task_install_fields_entry) before
    (InstallComponent.task_install_fields_entry_owner environment local sg call ** rest) false current restored
    (flag_pend_caller_restore_input environment critical other (fun _ _ => receipt ** frame) sg
      (FlagPendTaskCaller returned) returned saved acquired current) /\
  kernel_call_task_source returned current /\ task_tcb_init_stack_same_call returned original.
Proof.
  intros environment critical task_abi sg observer origin frame call original saved acquired receipt other
    before installed sp actual selected restored local rest complete Hselected Hincoming Hcoverage Hrestore current returned.
  destruct (task_install_selected_owner_tuple environment local sg rest call selected installed Hselected)
    as [Hstack Hfragments].
  assert (Horiginal : selected.(armv7a_continuation_stack) = original.(os_sched_call_stack)) by congruence.
  destruct (task_install_selected_owner_saved_facts environment critical sg rest call original saved acquired
    receipt other selected installed Horiginal Hselected) as [Hcall [Hmask [Horigin Hactive]]].
  pose proof (task_install_selected_owner_return_reads environment local sg rest call selected installed Hselected) as Hreads.
  pose proof (task_install_selected_owner_return_input environment task_abi local sg frame call selected
    Hstack Hfragments) as Hbridge.
  pose proof (Hbridge installed Hselected) as Hprimitive_pre.
  pose proof (task_selected_return_output_masked environment critical sg call original saved acquired receipt other
    selected frame Hcall Horiginal Hincoming Hmask Horigin Hcoverage) as Hclose.
  split.
  - replace false with (orb false false) by reflexivity.
    eapply KernelCSequenceThen with
      (middle := current) (middle_heap := installed)
      (first_output := task_install_selected_owner environment local sg rest call selected)
      (next_input := task_selected_return_input environment task_abi
        call.(InstallComponent.task_install_fields_context) selected
        (task_selected_return_frame environment local sg call selected frame)).
    + apply KernelCSequenceAtom.
      eapply KernelProgramReturnTaskSelectedInstall with (actual := actual) (complete := complete).
      * constructor; exact Hselected.
      * exact Hselected.
    + exact Hbridge.
    + eapply KernelCSequenceAdapt; [exact Hprimitive_pre|intros h H; exact H| |exact Hclose].
      apply KernelCSequenceAtom, KernelProgramReturnSelected.
      eapply KernelSelectedReturnTask; eassumption.
  - destruct (task_install_c_terminal_return_caller environment critical sg rest call original saved acquired
      receipt other before installed sp actual complete Hincoming) as [_ [Hsource Hsame]].
    assert (Hvalue : returned = kernel_restored_stack_call original call.(InstallComponent.task_install_fields_incoming)
      call.(InstallComponent.task_install_fields_resumed)).
    { unfold returned, kernel_selected_call; rewrite Hcall; apply armv7a_continuation_resumed_call_tuple; assumption. }
    rewrite Hvalue; exact (conj Hsource Hsame).
Qed.

End TaskSelectedCompletion.
