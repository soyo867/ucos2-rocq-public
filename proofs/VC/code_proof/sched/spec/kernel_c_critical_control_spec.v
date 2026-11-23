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
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_del_c_segment_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_priority_c_segment_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


(** Control fields of the actual critical C completions.  The source and
    both owners remain those of the original segment.  Counter enter/exit
    and TaskDel lock/release retain their real interrupt-state updates. *)
Module SelectedCriticalControl.
Import CriticalComponent BuiltinComponent PendComponent PostComponent DeleteComponent.

Lemma task_change_prio_critical_control_fields :
  forall sg requested priority entry code returned,
  task_change_prio_critical sg requested priority entry code returned ->
  returned.(SchedState).(isRunning) = entry.(SchedState).(isRunning) /\
  returned.(IntrState) = entry.(IntrState).
Proof.
  intros sg requested priority entry code returned Hstep.
  unfold task_change_prio_critical in Hstep.
  destruct (entry.(TskState).(prioTbl) priority).
  - destruct Hstep as [selected [Hselected Hstep]].
    unfold task_change_prio_selected_effect in Hstep.
    destruct (Z.eqb selected sg.(osLowestPrio)).
    + destruct Hstep as [_ ->]; split; reflexivity.
    + destruct (entry.(TskState).(prioTbl) selected).
      * destruct Hstep as [_ ->]; split; reflexivity.
      * destruct Hstep as [_ ->]; split; reflexivity.
      * destruct Hstep as [node [Hnode [_ ->]]]; split.
        -- exact (proj2 (proj2 (proj2 (proj2 (proj2
             (task_change_prio_state_sched_caches sg entry _ node selected priority)))))).
        -- exact (proj1 (task_change_prio_state_module_frames sg entry _ node selected priority)).
  - destruct Hstep as [_ ->]; split; reflexivity.
  - destruct Hstep as [_ ->]; split; reflexivity.
Qed.

Lemma kernel_critical_c_segment_control_fields :
  forall environment critical local sg frame call before after,
  kernel_critical_c_segment environment critical local sg frame call before after ->
  (kernel_critical_c_returned call).(SchedState).(isRunning) =
    (kernel_critical_c_entry call).(SchedState).(isRunning) /\
  (kernel_critical_c_returned call).(IntrState) = (kernel_critical_c_entry call).(IntrState).
Proof.
  intros environment critical local sg frame [actual|actual] before after
    [Hcompletion [Hphysical [Hsource Hpacket]]]; clear Hpacket; simpl in *.
  - destruct Hsource as [code [Hcritical Hresult]].
    eapply task_change_prio_critical_control_fields; exact Hcritical.
  - unfold mutex_del_critical_fields_observation in Hsource.
    destruct Hsource as [result code request checkpoint Hguard Hobservation|kind Htype Hother].
    + destruct Hobservation as [error [scheduled [Hcritical Hencoding]]].
      destruct (mutex_del_critical_interrupt_frame _ _ _ _ _ _ Hcritical); split; assumption.
    + split; reflexivity.
Qed.

Lemma kernel_critical_c_segment_running :
  forall environment critical local sg frame call before after,
  kernel_critical_c_segment environment critical local sg frame call before after ->
  (kernel_critical_c_returned call).(SchedState).(isRunning) =
    (kernel_critical_c_entry call).(SchedState).(isRunning).
Proof.
  intros; exact (proj1 (kernel_critical_c_segment_control_fields _ _ _ _ _ _ _ _ H)).
Qed.

Lemma kernel_critical_c_segment_interrupt :
  forall environment critical local sg frame call before after,
  kernel_critical_c_segment environment critical local sg frame call before after ->
  (kernel_critical_c_returned call).(IntrState) = (kernel_critical_c_entry call).(IntrState).
Proof.
  intros; exact (proj2 (kernel_critical_c_segment_control_fields _ _ _ _ _ _ _ _ H)).
Qed.

Lemma kernel_builtin_c_segment_running :
  forall environment critical local sg state before returned after input output,
  kernel_builtin_c_segment environment critical local sg state before returned after input output ->
  returned.(SchedState).(isRunning) = state.(SchedState).(isRunning).
Proof.
  intros environment critical local sg state before returned after input output Hstep.
  destruct Hstep as
    [operation state frame before after code Hcompletion|
     publication state frame before after code effect Hcompletion|
     handler saved entry transfer frame before after Hcompletion].
  - destruct operation; reflexivity.
  - reflexivity.
  - pose proof (kernel_irq_transfer_c_completion_source environment critical sg handler saved
      entry transfer frame before after Hcompletion) as Hsource.
    pose proof (os_int_exit_configured_transfer_hooked_eq environment sg handler entry transfer Hsource) as Hhook.
    unfold os_int_exit_installed_state; rewrite Hhook; reflexivity.
Qed.

(** Publication and the post-counter IRQ transfer preserve IntrState.
    This statement deliberately does not cover the counter constructor. *)
Lemma kernel_publication_c_completion_interrupt :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    local sg publication state frame before after code effect,
  kernel_publication_c_completion abi local sg publication state frame before after code effect ->
  (task_create_stack_publication_state sg publication state).(IntrState) = state.(IntrState).
Proof. intros; reflexivity. Qed.

Lemma kernel_irq_transfer_c_completion_interrupt :
  forall environment critical sg handler saved entry transfer frame before after,
  kernel_irq_transfer_c_completion environment critical sg handler saved entry transfer frame before after ->
  (os_int_exit_installed_state transfer).(IntrState) =
    (os_int_exit_ready_checkpoint true entry).(IntrState).
Proof.
  intros environment critical sg handler saved entry transfer frame before after Hcompletion.
  pose proof (kernel_irq_transfer_c_completion_source environment critical sg handler saved
    entry transfer frame before after Hcompletion) as Hsource.
  pose proof (os_int_exit_configured_transfer_hooked_eq environment sg handler entry transfer Hsource) as Hhook.
  unfold os_int_exit_installed_state; rewrite Hhook; reflexivity.
Qed.

Lemma mutex_pend_inheritance_c_segment_control_fields :
  forall environment critical local sg frame call before after,
  mutex_pend_inheritance_c_segment environment critical local sg frame call before after ->
  call.(mutex_pend_inheritance_returned).(SchedState).(isRunning) =
    call.(mutex_pend_inheritance_entry).(SchedState).(isRunning) /\
  call.(mutex_pend_inheritance_returned).(IntrState) = call.(mutex_pend_inheritance_entry).(IntrState).
Proof.
  intros environment critical local sg frame call before after
    [[Hnode [Hother Hstep]] Hinput Houtput].
  unfold mutex_pend_inherit_step in Hstep.
  destruct (mutex_pend_inherit_action _ _ _ _ _).
  - rewrite Hstep; split; reflexivity.
  - rewrite Hstep; split; reflexivity.
  - destruct Hstep as [events [Hevents Hstep]]; rewrite Hstep; split; reflexivity.
Qed.

Lemma mutex_pend_inheritance_c_segment_running :
  forall environment critical local sg frame call before after,
  mutex_pend_inheritance_c_segment environment critical local sg frame call before after ->
  call.(mutex_pend_inheritance_returned).(SchedState).(isRunning) =
    call.(mutex_pend_inheritance_entry).(SchedState).(isRunning).
Proof.
  intros; exact (proj1 (mutex_pend_inheritance_c_segment_control_fields _ _ _ _ _ _ _ _ H)).
Qed.

Lemma mutex_pend_inheritance_c_segment_interrupt :
  forall environment critical local sg frame call before after,
  mutex_pend_inheritance_c_segment environment critical local sg frame call before after ->
  call.(mutex_pend_inheritance_returned).(IntrState) = call.(mutex_pend_inheritance_entry).(IntrState).
Proof.
  intros; exact (proj2 (mutex_pend_inheritance_c_segment_control_fields _ _ _ _ _ _ _ _ H)).
Qed.

Lemma mutex_post_prepare_running : forall sg mutex owner entry prepared,
  mutex_post_prepare sg mutex owner entry prepared ->
  prepared.(SchedState).(isRunning) = entry.(SchedState).(isRunning).
Proof.
  intros sg mutex owner entry prepared Hprepare.
  unfold mutex_post_prepare in Hprepare; destruct Z.eq_dec.
  - subst prepared; reflexivity.
  - destruct Hprepare as [node [priority [Hnode [Hscan ->]]]].
    unfold mutex_post_owner_priority_state; destruct Z.eq_dec; reflexivity.
Qed.

Lemma mutex_post_critical_running : forall sg eid caller entry result schedule checkpoint,
  mutex_post_critical sg eid caller entry result schedule checkpoint ->
  checkpoint.(SchedState).(isRunning) = entry.(SchedState).(isRunning).
Proof.
  intros sg eid caller entry result schedule checkpoint Hcritical; destruct Hcritical.
  - reflexivity.
  - change (prepared.(SchedState).(isRunning) = entry.(SchedState).(isRunning)).
    eapply mutex_post_prepare_running; eassumption.
  - change (woken.(SchedState).(isRunning) = entry.(SchedState).(isRunning)).
    destruct (mutex_del_wake_interrupt_frame _ _ _ _ _ _ _ _ H5) as [Hinterrupt Hrunning].
    rewrite Hrunning; eapply mutex_post_prepare_running; eassumption.
Qed.

Lemma mutex_post_critical_c_segment_running :
  forall source_env external platform critical local sg frame call before after,
  mutex_post_critical_c_segment source_env external platform critical local sg frame call before after ->
  call.(mutex_post_critical_checkpoint).(SchedState).(isRunning) =
    call.(mutex_post_critical_entry).(SchedState).(isRunning).
Proof.
  intros source_env external platform critical local sg frame call before after [[Hcaller Hcritical] Hinput Houtput].
  eapply mutex_post_critical_running; exact Hcritical.
Qed.

Lemma mutex_post_critical_c_segment_interrupt :
  forall source_env external platform critical local sg frame call before after,
  mutex_post_critical_c_segment source_env external platform critical local sg frame call before after ->
  call.(mutex_post_critical_checkpoint).(IntrState) = call.(mutex_post_critical_entry).(IntrState).
Proof.
  intros source_env external platform critical local sg frame call before after [[Hcaller Hcritical] Hinput Houtput].
  eapply mutex_post_critical_interrupt_frame; exact Hcritical.
Qed.

Lemma task_delete_own_c_segment_running :
  forall environment critical sg observer origin state before input stopped returned after output,
  task_delete_own_c_segment environment critical sg observer origin
    state before input stopped returned after output ->
  returned.(SchedState).(isRunning) = state.(SchedState).(isRunning).
Proof.
  intros environment critical sg observer origin state before input stopped returned after output Hstep.
  destruct Hstep as [inputs before_heap prepared_heap Hcontext Hcompletion|
                    capture after_heap Hcontext Hcompletion].
  - destruct Hcompletion as [Hpreparation Hinput Houtput].
    unfold task_delete_capture_preparation, task_delete_preparation_history in Hpreparation.
    destruct Hpreparation as [Hlive [Hprepare Hprotocol]].
    destruct (task_delete_prepare_single_wait_frame _ _ _ _ _ Hprepare) as [node [Hfields Hnode]].
    exact (f_equal (fun state => state.(SchedState).(isRunning)) Hfields).
  - reflexivity.
Qed.

End SelectedCriticalControl.
