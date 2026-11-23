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
Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_acquired_return_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_control_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_critical_control_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_selected_endpoint_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_return_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_suspend_masked_c_step_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


(** Running is transported by each real C leaf, including counter-changing
    leaves.  Interrupt/lock equality is obtained only from actual enabled
    selector endpoints below, not from an arbitrary sequence. *)
Module SelectedControlComposition.
Import CriticalComponent PrimitiveComponent SelectedReturnPrimitive SelectedCProgram.
Import SelectedControlFrames SelectedCriticalControl.

Lemma kernel_program_c_step_running : forall environment critical sg observer origin
  state before input stopped current after output,
  kernel_program_c_step environment critical sg observer origin state before input stopped current after output ->
  current.(SchedState).(isRunning) = state.(SchedState).(isRunning).
Proof.
  intros environment critical sg observer origin state before input stopped current after output Hstep; destruct Hstep.
  - eapply kernel_critical_c_segment_running; eassumption.
  - eapply kernel_builtin_c_segment_running; eassumption.
  - exact (proj1 (task_install_c_step_control _ _ _ _ _ _ _ _ _ _ H)).
  - exact (proj1 (kernel_wake_c_segment_control _ _ _ _ _ _ _ H)).
  - exact (proj1 (kernel_status_c_segment_control _ _ _ _ _ _ H)).
  - exact (proj1 (kernel_task_creation_c_segment_control _ _ _ _ _ _ _ H)).
  - exact (proj1 (kernel_event_creation_c_segment_control _ _ _ _ _ _ _ H)).
  - exact (proj1 (kernel_queue_creation_c_segment_control _ _ _ _ _ _ _ H)).
  - eapply mutex_pend_inheritance_c_segment_running; eassumption.
  - eapply mutex_post_critical_c_segment_running; eassumption.
  - exact (proj1 (task_delete_primitive_c_segment_control _ _ _ _ _ _ _ _ _ _ H)).
  - exact (proj1 (flag_pend_task_primitive_c_step_control _ _ _ _ _ _ _ _ _ _ H)).
  - eapply task_delete_own_c_segment_running; eassumption.
Qed.

Lemma kernel_program_return_c_step_running : forall environment critical sg observer origin
  state before input stopped current after output,
  kernel_program_return_c_step environment critical sg observer origin state before input stopped current after output ->
  current.(SchedState).(isRunning) = state.(SchedState).(isRunning).
Proof.
  intros environment critical sg observer origin state before input stopped current after output Hstep; destruct Hstep.
  - eapply kernel_program_c_step_running; exact H.
  - destruct (kernel_selected_return_c_step_state_stop _ _ _ _ _ _ _ _ H) as [-> _]; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma kernel_program_selected_c_step_running : forall environment critical sg observer origin
  state before input stopped current after output,
  kernel_program_selected_c_step environment critical sg observer origin state before input stopped current after output ->
  current.(SchedState).(isRunning) = state.(SchedState).(isRunning).
Proof.
  intros environment critical sg observer origin state before input stopped current after output Hstep; destruct Hstep.
  - eapply kernel_program_return_c_step_running; exact H.
  - destruct H.
    destruct (SelectedEndpointObservations.irq_acquired_c_completion_endpoint_facts environment critical sg handler entry
      transfer original saved acquired receipt other frame before prepared hooked_heap installed selected after
      source prefix hook install restore H) as [_ [_ [_ [_ [Hrunning _]]]]].
    exact Hrunning.
  - exact (proj1 (TaskSuspendMaskedC.task_suspend_masked_c_step_control_fields
      environment critical sg _ _ _ _ _ _ _ H)).
Qed.

Lemma kernel_program_selected_c_sequence_running : forall environment critical sg observer origin
  state before input stopped current after output,
  kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    state before input stopped current after output ->
  current.(SchedState).(isRunning) = state.(SchedState).(isRunning).
Proof.
  intros environment critical sg observer origin state before input stopped current after output Hrun; induction Hrun.
  - reflexivity.
  - eapply kernel_program_selected_c_step_running; exact H.
  - congruence.
  - exact IHHrun.
Qed.

(** The last install record is built from the very components of the C
    switch source.  This preserves context/outgoing/incoming/hooked and
    the actual prefix endpoint; matching only final states would not bind
    that selector.  Counter changes inside the prefix remain permitted. *)
Lemma task_last_call_selected_sequence_control :
  forall environment critical sg observer origin first_entry original first_installed
    last_entry context saved_sp outgoing hooked incoming resumed
    (Hfirst : os_sched_switch_source (task_sw_hook_call_environment environment).(task_stack_call_external)
      sg first_entry original first_installed)
    (Hswitch : os_sched_requests_switch last_entry = true)
    (Hsave : (task_sw_hook_call_environment environment).(task_stack_call_external).(os_sched_arch_save_source)
      context saved_sp outgoing)
    (Hhook : kernel_client_step (task_sw_hook_call_environment environment).(task_stack_call_external).(os_sched_hook_action)
      sg (os_sched_save_current_sp (os_sched_prefix_state last_entry)
        context.(os_sched_call_stack).(stackLeaseSlot) saved_sp) hooked)
    (Hdestination : os_sched_destination_binding (task_sw_hook_call_environment environment).(task_stack_call_external)
      context outgoing hooked incoming resumed),
  let call := {| InstallComponent.task_install_fields_context := context;
                 InstallComponent.task_install_fields_outgoing := outgoing;
                 InstallComponent.task_install_fields_incoming := incoming;
                 InstallComponent.task_install_fields_resumed := resumed;
                 InstallComponent.task_install_fields_entry := hooked |} in
  forall before input stopped installed_heap output,
  kernel_c_sequence (kernel_program_selected_c_step (task_sw_hook_call_environment environment) critical sg observer origin)
    first_installed before input stopped hooked installed_heap output ->
  kernel_call_control_rely sg first_entry (InstallComponent.task_install_fields_current call).
Proof.
  intros environment critical sg observer origin first_entry original first_installed last_entry context saved_sp outgoing
    hooked incoming resumed Hfirst Hswitch Hsave Hhook Hdestination call before input stopped installed_heap output Hrun.
  pose proof (kernel_program_selected_c_sequence_running (task_sw_hook_call_environment environment) critical sg observer origin
    _ _ _ _ _ _ _ Hrun) as Hrunning.
  change (hooked = os_sched_save_current_sp (os_sched_prefix_state last_entry)
    context.(os_sched_call_stack).(stackLeaseSlot) saved_sp) in Hhook.
  destruct Hfirst as [Hfirst_switch [first_sp [first_outgoing [first_hooked [first_incoming [first_resumed
    [Hfirst_save [Hfirst_hook [Hfirst_destination Hfirst_installed]]]]]]]]].
  change (first_hooked = os_sched_save_current_sp (os_sched_prefix_state first_entry)
    original.(os_sched_call_stack).(stackLeaseSlot) first_sp) in Hfirst_hook.
  assert (Hfirst_running : first_installed.(SchedState).(isRunning) = first_entry.(SchedState).(isRunning)).
  { rewrite Hfirst_installed, Hfirst_hook.
    exact (proj2 (proj2 (proj2 (os_sched_ready_checkpoint_frame first_entry)))). }
  unfold kernel_call_control_rely; split.
  - change (hooked.(SchedState).(isRunning) = first_entry.(SchedState).(isRunning)); congruence.
  - change (hooked.(IntrState) = first_entry.(IntrState)); rewrite Hhook.
    change (last_entry.(IntrState) = first_entry.(IntrState)).
    pose proof (proj1 (proj1 (os_sched_requests_switch_iff first_entry) Hfirst_switch)) as Hfirst_enabled.
    pose proof (proj1 (proj1 (os_sched_requests_switch_iff last_entry) Hswitch)) as Hlast_enabled.
    apply os_sched_selection_enabled_iff in Hfirst_enabled; apply os_sched_selection_enabled_iff in Hlast_enabled.
    destruct first_entry.(IntrState), last_entry.(IntrState); cbn in *; intuition congruence.
Qed.

Lemma irq_acquired_selected_sequence_control :
  forall environment critical sg observer origin handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap installed selected after source prefix hook install restore initial first_heap input stopped output,
  IRQAcquiredReturn.kernel_irq_acquired_c_completion environment critical sg handler entry transfer original saved acquired receipt other
    frame before prepared hooked_heap installed selected after source prefix hook install restore ->
  os_sched_selection_enabled initial = true ->
  kernel_c_sequence (kernel_program_selected_c_step (task_sw_hook_call_environment environment) critical sg observer origin)
    initial first_heap input stopped entry before output ->
  kernel_call_control_rely sg initial (os_int_exit_installed_state transfer).
Proof.
  intros environment critical sg observer origin handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap installed selected after source prefix hook install restore initial first_heap input stopped output
    Hcomplete Henabled Hrun.
  eapply SelectedEndpointObservations.irq_acquired_c_completion_control_at_enabled_entry;
    [exact Hcomplete|exact Henabled|].
  eapply kernel_program_selected_c_sequence_running; exact Hrun.
Qed.

End SelectedControlComposition.
