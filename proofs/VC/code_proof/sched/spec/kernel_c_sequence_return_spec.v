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
Require Export Ucos2Verify.VC.code.event.spec.event_create_c_segment_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_priority_c_segment_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Export Ucos2Verify.VC.code.queue.spec.q_create_c_segment_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_c_segment_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


(** Return selection is indexed by the original C execution proof.  The
    flowing focus is the selected TaskStackLease, not a cache or TaskSource
    proposition.  C atoms retain it; actual installs replace it by their
    incoming lease.  The fixed lifetime observer remains independent. *)
Module SequenceReturn.
Import CriticalComponent PrimitiveComponent.

Import EventStateDef.

Lemma kernel_critical_c_source_current_eq : forall sg call,
  CriticalComponent.kernel_critical_c_source sg call ->
  (CriticalComponent.kernel_critical_c_returned call).(SchedState).(curTaskID) =
  (CriticalComponent.kernel_critical_c_entry call).(SchedState).(curTaskID).
Proof.
  intros sg [call|call] Hsource; cbn in Hsource |- *.
  - destruct Hsource as [error [Hcode Hresult]].
    exact (proj1 (CriticalComponent.task_change_prio_critical_current_timer_frame
      _ _ _ _ _ _ Hcode)).
  - unfold CriticalComponent.mutex_del_critical_fields_observation in Hsource.
    destruct (CriticalComponent.mutex_del_critical_call_observation_fields
      _ _ _ _ _ _ _ _ Hsource) as [[_ [_ [_ [Hcurrent _]]]] _].
    exact Hcurrent.
Qed.

Lemma kernel_wake_c_source_current_eq : forall sg entry returned,
  WakeComponent.kernel_wake_c_source sg entry returned ->
  returned.(SchedState).(curTaskID) = entry.(SchedState).(curTaskID).
Proof.
  intros sg entry returned Hsource; destruct Hsource.
  - destruct (flag_task_rdy_result _ _ _ _ _ _ _ H)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]]; reflexivity.
  - unfold event_task_rdy in H.
    destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
    destruct (entry.(TskState).(prioTbl) (event_wait_priority entry.(TskState) event))
      as [| |slot]; try discriminate.
    destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|]; [|discriminate].
    injection H as Hpriority Hreturned; subst returned.
    unfold event_wake_state, sched_wake_by_status; cbn zeta;
      repeat match goal with |- context [if ?test then _ else _] => destruct test end; reflexivity.
  - unfold tick_task_step, sched_wake_by_status; cbn zeta;
      repeat match goal with |- context [if ?test then _ else _] => destruct test end; reflexivity.
Qed.

Lemma kernel_task_creation_c_source_current_eq : forall sg entry returned,
  CreationComponent.kernel_task_creation_c_source sg entry returned ->
  returned.(SchedState).(curTaskID) = entry.(SchedState).(curTaskID).
Proof.
  intros sg entry returned Hsource; destruct Hsource.
  - reflexivity.
  - unfold task_create_critical in H; destruct (Z.ltb 0 entry.(IntrState).(intNesting)).
    + destruct H as [_ ->]; reflexivity.
    + destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority);
        destruct Hstep as [_ ->]; reflexivity.
  - destruct H2 as [_ ->]; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma mutex_pend_inheritance_c_source_current_eq : forall sg call,
  PendComponent.mutex_pend_inheritance_c_source sg call ->
  call.(PendComponent.mutex_pend_inheritance_returned).(SchedState).(curTaskID) =
  call.(PendComponent.mutex_pend_inheritance_entry).(SchedState).(curTaskID).
Proof.
  intros sg call [Hnode [Hnonowner Hstep]].
  unfold mutex_pend_inherit_step in Hstep.
  destruct (mutex_pend_inherit_action sg.(osPrioMutexCeilDis)
    call.(PendComponent.mutex_pend_inheritance_base)
    call.(PendComponent.mutex_pend_inheritance_node).(curPrio)
    call.(PendComponent.mutex_pend_inheritance_waiter)
    call.(PendComponent.mutex_pend_inheritance_ceiling)).
  - rewrite Hstep; reflexivity.
  - rewrite Hstep; reflexivity.
  - destruct Hstep as [events [Hevents Hstep]].
    unfold mutex_pend_promoted_events in Hevents.
    destruct (mutex_pend_owner_was_ready call.(PendComponent.mutex_pend_inheritance_entry)
      call.(PendComponent.mutex_pend_inheritance_node)).
    + rewrite Hstep, Hevents; reflexivity.
    + destruct call.(PendComponent.mutex_pend_inheritance_node).(eventPtr).
      * destruct Hevents as [old [Hget Hevents]]; rewrite Hstep, Hevents; reflexivity.
      * rewrite Hstep, Hevents; reflexivity.
Qed.

Lemma mutex_post_critical_c_source_current_eq : forall sg call,
  PostComponent.mutex_post_critical_c_source sg call ->
  call.(PostComponent.mutex_post_critical_checkpoint).(SchedState).(curTaskID) =
  call.(PostComponent.mutex_post_critical_entry).(SchedState).(curTaskID).
Proof.
  intros sg call [Hcaller Hcritical].
  exact (proj1 (proj2 (proj2 (proj2
    (mutex_post_critical_call_fields_eq _ _ _ _ _ _ _ Hcritical))))).
Qed.

Lemma task_delete_own_c_segment_current_eq :
  forall environment critical sg observer origin state before input stopped returned after output,
  DeleteComponent.task_delete_own_c_segment environment critical sg observer origin
    state before input stopped returned after output ->
  returned.(SchedState).(curTaskID) = state.(SchedState).(curTaskID).
Proof.
  intros environment critical sg observer origin state before input stopped returned after output Hstep.
  destruct Hstep as [inputs before_heap prepared_heap Hcontext Hcomplete|
    capture after_heap Hcontext Hcomplete].
  - destruct Hcomplete as [Hpreparation Hbefore Hafter].
    destruct Hpreparation as [Hlive [Hprepare Hprotocol]].
    exact (proj2 (proj2 (proj2 (proj2
      (TaskDeleteCompletedMacro.task_delete_prepare_single_wait_metadata_frame _ _ _ _ _ Hprepare))))).
  - reflexivity.
Qed.

Lemma flag_pend_task_primitive_c_step_current_eq :
  forall environment critical sg state before input stopped returned after output,
  flag_pend_task_primitive_c_step environment critical sg
    state before input stopped returned after output ->
  returned.(SchedState).(curTaskID) = state.(SchedState).(curTaskID).
Proof.
  intros environment critical sg state before input stopped returned after output Hstep.
  destruct Hstep; try reflexivity.
  destruct H; reflexivity.
Qed.

Section ProgramReturnCall.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (observer : nat) (observer_origin : TaskInvocationOrigin).
Let segment := kernel_program_c_step environment critical sg observer observer_origin.

(** The constructors below are a finite interpretation of the actual
    original atoms.  No constructor takes a current-pointer equality. *)
Inductive kernel_program_c_step_return_call :
  forall state before input stopped returned after output,
  segment state before input stopped returned after output ->
  TaskStackLease -> TaskStackLease -> Prop :=
| KernelProgramCriticalReturn : forall local frame call before after Hcomplete focus,
    kernel_program_c_step_return_call _ _ _ _ _ _ _
      (@KernelProgramCCritical environment critical sg observer observer_origin
        local frame call before after Hcomplete) focus focus
| KernelProgramCounterReturn : forall local operation state frame before after code Hcomplete focus,
    kernel_program_c_step_return_call _ _ _ _ _ _ _
      (@KernelProgramCBuiltin environment critical sg observer observer_origin local _ _ _ _ _ _
        (@BuiltinComponent.KernelBuiltinCCounter environment critical local sg
          operation state frame before after code Hcomplete)) focus focus
| KernelProgramPublicationReturn : forall local publication state frame before after code effect Hcomplete focus,
    kernel_program_c_step_return_call _ _ _ _ _ _ _
      (@KernelProgramCBuiltin environment critical sg observer observer_origin local _ _ _ _ _ _
        (@BuiltinComponent.KernelBuiltinCPublication environment critical local sg
          publication state frame before after code effect Hcomplete)) focus focus
| KernelProgramIRQReturn : forall local handler saved entry transfer frame before after Hcomplete focus,
    kernel_program_c_step_return_call _ _ _ _ _ _ _
      (@KernelProgramCBuiltin environment critical sg observer observer_origin local _ _ _ _ _ _
        (@BuiltinComponent.KernelBuiltinCIRQTransfer environment critical local sg
          handler saved entry transfer frame before after Hcomplete))
      focus transfer.(os_int_exit_incoming_stack)
| KernelProgramInstallReturn : forall local frame call before after sp Hactual Hcomplete focus,
    kernel_program_c_step_return_call _ _ _ _ _ _ _
      (@KernelProgramCInstall environment critical sg observer observer_origin local _ _ _ _ _ _ _
        (@InstallComponent.TaskInstallCStep environment local sg
          frame call before after sp Hactual Hcomplete))
      focus call.(InstallComponent.task_install_fields_incoming)
| KernelProgramWakeReturn : forall state before input returned after output Hcomplete focus,
    kernel_program_c_step_return_call _ _ _ _ _ _ _
      (@KernelProgramCWake environment critical sg observer observer_origin
        state before input returned after output Hcomplete) focus focus
| KernelProgramStatusReturn : forall state before returned after frame Hcomplete focus,
    kernel_program_c_step_return_call _ _ _ _ _ _ _
      (@KernelProgramCStatus environment critical sg observer observer_origin
        state before returned after frame Hcomplete) focus focus
| KernelProgramTaskCreationReturn : forall state before input returned after output Hcomplete focus,
    kernel_program_c_step_return_call _ _ _ _ _ _ _
      (@KernelProgramCTaskCreation environment critical sg observer observer_origin
        state before input returned after output Hcomplete) focus focus
| KernelProgramEventCreationReturn : forall state before input returned after output Hcomplete focus,
    kernel_program_c_step_return_call _ _ _ _ _ _ _
      (@KernelProgramCEventCreation environment critical sg observer observer_origin
        state before input returned after output Hcomplete) focus focus
| KernelProgramQueueCreationReturn : forall state before input returned after output Hcomplete focus,
    kernel_program_c_step_return_call _ _ _ _ _ _ _
      (@KernelProgramCQueueCreation environment critical sg observer observer_origin
        state before input returned after output Hcomplete) focus focus
| KernelProgramMutexPendReturn : forall local frame call before after Hcomplete focus,
    kernel_program_c_step_return_call _ _ _ _ _ _ _
      (@KernelProgramCMutexPend environment critical sg observer observer_origin
        local frame call before after Hcomplete) focus focus
| KernelProgramMutexPostReturn : forall source_env local frame call before after Hcomplete focus,
    kernel_program_c_step_return_call _ _ _ _ _ _ _
      (@KernelProgramCMutexPost environment critical sg observer observer_origin
        source_env local frame call before after Hcomplete) focus focus
| KernelProgramDeletePrimitiveReturn : forall state before input stopped returned after output Hcomplete focus,
    kernel_program_c_step_return_call _ _ _ _ _ _ _
      (@KernelProgramCDeletePrimitive environment critical sg observer observer_origin
        state before input stopped returned after output Hcomplete) focus focus
| KernelProgramPairedPrimitiveReturn : forall state before input stopped returned after output Hcomplete focus,
    kernel_program_c_step_return_call _ _ _ _ _ _ _
      (@KernelProgramCPairedPrimitive environment critical sg observer observer_origin
        state before input stopped returned after output Hcomplete) focus focus
| KernelProgramDeleteReturn : forall state before input stopped returned after output Hcomplete focus,
    kernel_program_c_step_return_call _ _ _ _ _ _ _
      (@KernelProgramCDelete environment critical sg observer observer_origin
        state before input stopped returned after output Hcomplete) focus focus.

Lemma kernel_program_c_step_return_call_exists :
  forall state before input stopped returned after output
    (step : segment state before input stopped returned after output) focus,
  exists final_focus,
    kernel_program_c_step_return_call state before input stopped returned after output step focus final_focus.
Proof.
  intros state before input stopped returned after output step focus.
  destruct step; try solve [eexists; constructor].
  - match goal with Hcomplete : BuiltinComponent.kernel_builtin_c_segment _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hcomplete end; eexists; constructor.
  - match goal with Hcomplete : InstallComponent.task_install_c_step _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hcomplete end; eexists; constructor.
Qed.

Lemma kernel_program_c_step_return_call_current :
  forall state before input stopped returned after output
    (step : segment state before input stopped returned after output) focus final_focus,
  kernel_program_c_step_return_call state before input stopped returned after output step focus final_focus ->
  state.(SchedState).(curTaskID) = Some focus.(stackLeaseSlot) ->
  returned.(SchedState).(curTaskID) = Some final_focus.(stackLeaseSlot).
Proof.
  intros state before input stopped returned after output step focus final_focus Hreturn Hcurrent.
  destruct Hreturn.
  - destruct Hcomplete as [Hcompletion [Hphysical [Hsource Hpacket]]].
    rewrite (kernel_critical_c_source_current_eq sg call Hsource); exact Hcurrent.
  - change ((BuiltinComponent.kernel_counter_c_state operation state).(SchedState).(curTaskID) =
      Some focus.(stackLeaseSlot)).
    destruct operation; unfold BuiltinComponent.kernel_counter_c_state,
      os_int_enter_state, os_int_exit_counter_state;
      repeat match goal with |- context [if ?test then _ else _] => destruct test end; exact Hcurrent.
  - exact Hcurrent.
  - pose proof (BuiltinComponent.kernel_irq_transfer_c_completion_source
      environment critical sg handler saved entry transfer frame before after Hcomplete) as Htransfer.
    exact (proj1 (os_int_exit_transfer_current_at
      (task_sw_hook_call_environment environment).(task_stack_call_external)
      environment.(task_stack_call_port) sg handler entry transfer Htransfer)).
  - destruct Hcomplete as [Hsource Hcompletion].
    destruct Hcompletion as [Hmodule Haddress Hpre Hselected Hrestore Hpost].
    exact (proj1 Hselected).
  - rewrite (kernel_wake_c_source_current_eq sg state returned
      (WakeComponent.kernel_wake_c_segment_source _ _ _ _ _ _ _ Hcomplete)); exact Hcurrent.
  - destruct Hcomplete as [Hsource Hpre Hpost].
    rewrite (StatusComponent.kernel_status_c_source_current_eq sg state returned Hsource); exact Hcurrent.
  - rewrite (kernel_task_creation_c_source_current_eq sg state returned
      (CreationComponent.kernel_task_creation_c_segment_source _ _ _ _ _ _ _ Hcomplete)); exact Hcurrent.
  - rewrite (proj2 (EventCreationComponent.kernel_event_creation_c_source_fields_eq state returned
      (EventCreationComponent.kernel_event_creation_c_segment_source _ _ _ _ _ _ _ Hcomplete))); exact Hcurrent.
  - rewrite (proj2 (QueueCreationComponent.kernel_queue_creation_c_source_fields_eq sg state returned
      (QueueCreationComponent.kernel_queue_creation_c_segment_source _ _ _ _ _ _ _ Hcomplete))); exact Hcurrent.
  - destruct Hcomplete as [Hsource Hpre Hpost].
    rewrite (mutex_pend_inheritance_c_source_current_eq sg call Hsource); exact Hcurrent.
  - destruct Hcomplete as [Hsource Hpre Hpost].
    rewrite (mutex_post_critical_c_source_current_eq sg call Hsource); exact Hcurrent.
  - destruct Hcomplete; exact Hcurrent.
  - rewrite (flag_pend_task_primitive_c_step_current_eq _ _ _ _ _ _ _ _ _ _ Hcomplete); exact Hcurrent.
  - rewrite (task_delete_own_c_segment_current_eq _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete); exact Hcurrent.
Qed.

(** Then and Adapt retain the exact old proof term, including the original
    middle heap/state and its actual post-to-pre implication. *)
Inductive kernel_program_c_sequence_return_call :
  forall state before input stopped returned after output,
  kernel_c_sequence segment state before input stopped returned after output ->
  TaskStackLease -> TaskStackLease -> Prop :=
| KernelProgramReturnRefl : forall state heap owner (owned : owner heap) focus,
    kernel_program_c_sequence_return_call _ _ _ _ _ _ _
      (KernelCSequenceRefl segment state heap owner owned) focus focus
| KernelProgramReturnAtom : forall state before input stopped returned after output
    (step : segment state before input stopped returned after output) focus final_focus,
    kernel_program_c_step_return_call _ _ _ _ _ _ _ step focus final_focus ->
    kernel_program_c_sequence_return_call _ _ _ _ _ _ _
      (KernelCSequenceAtom segment state before input stopped returned after output step) focus final_focus
| KernelProgramReturnThen : forall state before input first_stopped middle middle_heap
    first_output next_input last_stopped returned after output
    (first : kernel_c_sequence segment state before input first_stopped middle middle_heap first_output)
    (bridge : first_output |-- next_input)
    (last : kernel_c_sequence segment middle middle_heap next_input last_stopped returned after output)
    focus middle_focus final_focus,
    kernel_program_c_sequence_return_call _ _ _ _ _ _ _ first focus middle_focus ->
    kernel_program_c_sequence_return_call _ _ _ _ _ _ _ last middle_focus final_focus ->
    kernel_program_c_sequence_return_call _ _ _ _ _ _ _
      (KernelCSequenceThen segment state before input first_stopped middle middle_heap
        first_output next_input last_stopped returned after output first bridge last) focus final_focus
| KernelProgramReturnAdapt : forall state before input inner_input stopped returned after inner_output output
    (owned : input before) (open_input : input |-- inner_input)
    (inner : kernel_c_sequence segment state before inner_input stopped returned after inner_output)
    (close_output : inner_output |-- output) focus final_focus,
    kernel_program_c_sequence_return_call _ _ _ _ _ _ _ inner focus final_focus ->
    kernel_program_c_sequence_return_call _ _ _ _ _ _ _
      (KernelCSequenceAdapt segment state before input inner_input stopped returned after inner_output output
        owned open_input inner close_output) focus final_focus.

Lemma kernel_program_c_sequence_return_call_exists :
  forall state before input stopped returned after output
    (run : kernel_c_sequence segment state before input stopped returned after output) focus,
  exists final_focus,
    kernel_program_c_sequence_return_call state before input stopped returned after output run focus final_focus.
Proof.
  fix IH 8.
  intros state before input stopped returned after output run focus.
  destruct run as [state heap owner Howned|
    state before input stopped returned after output step|
    state before input first_stopped middle middle_heap first_output next_input last_stopped
      returned after output first bridge last|
    state before input inner_input stopped returned after inner_output output owned open_input inner close_output].
  - exists focus; constructor.
  - destruct (kernel_program_c_step_return_call_exists _ _ _ _ _ _ _ step focus) as [final_focus Hreturn].
    exists final_focus; constructor; exact Hreturn.
  - destruct (IH _ _ _ _ _ _ _ first focus) as [middle_focus Hfirst].
    destruct (IH _ _ _ _ _ _ _ last middle_focus) as [final_focus Hlast].
    exists final_focus; econstructor; eassumption.
  - destruct (IH _ _ _ _ _ _ _ inner focus) as [final_focus Hinner].
    exists final_focus; constructor; exact Hinner.
Qed.

Lemma kernel_program_c_sequence_return_call_current :
  forall state before input stopped returned after output
    (run : kernel_c_sequence segment state before input stopped returned after output) focus final_focus,
  kernel_program_c_sequence_return_call state before input stopped returned after output run focus final_focus ->
  state.(SchedState).(curTaskID) = Some focus.(stackLeaseSlot) ->
  returned.(SchedState).(curTaskID) = Some final_focus.(stackLeaseSlot).
Proof.
  intros state before input stopped returned after output run focus final_focus Hreturn.
  induction Hreturn; intro Hcurrent.
  - exact Hcurrent.
  - eapply kernel_program_c_step_return_call_current; eassumption.
  - apply IHHreturn2; apply IHHreturn1; exact Hcurrent.
  - apply IHHreturn; exact Hcurrent.
Qed.
End ProgramReturnCall.

(** Projection of an actual selected descriptor.  Both resumed calls and
    initial calls carry its incoming lease; this does not create a call
    registration or obtain a descriptor from an arbitrary endpoint. *)
Lemma kernel_selected_call_stack : forall selected current,
  (kernel_selected_call selected current).(os_sched_call_stack) =
    selected.(armv7a_continuation_stack).
Proof.
  intros selected current; unfold kernel_selected_call.
  destruct selected.(armv7a_continuation_call); reflexivity.
Qed.

Lemma kernel_program_install_selected_return :
  forall environment critical sg observer origin local frame call before after sp Hactual Hcomplete
    focus selected,
  selected.(armv7a_continuation_stack) = call.(InstallComponent.task_install_fields_incoming) ->
  kernel_program_c_step_return_call environment critical sg observer origin _ _ _ _ _ _ _
    (@KernelProgramCInstall environment critical sg observer origin local _ _ _ _ _ _ _
      (@InstallComponent.TaskInstallCStep environment local sg
        frame call before after sp Hactual Hcomplete)) focus
    (kernel_selected_call selected (InstallComponent.task_install_fields_current call)).(os_sched_call_stack).
Proof.
  intros; rewrite kernel_selected_call_stack, H; constructor.
Qed.

Lemma kernel_program_irq_selected_return :
  forall environment critical sg observer origin local handler saved entry transfer frame before after Hcomplete
    focus selected,
  selected.(armv7a_continuation_stack) = transfer.(os_int_exit_incoming_stack) ->
  kernel_program_c_step_return_call environment critical sg observer origin _ _ _ _ _ _ _
    (@KernelProgramCBuiltin environment critical sg observer origin local _ _ _ _ _ _
      (@BuiltinComponent.KernelBuiltinCIRQTransfer environment critical local sg
        handler saved entry transfer frame before after Hcomplete)) focus
    (kernel_selected_call selected (os_int_exit_installed_state transfer)).(os_sched_call_stack).
Proof.
  intros; rewrite kernel_selected_call_stack, H; constructor.
Qed.

(** The output owner is the real callee assertion at this same heap.  The
    active-fields projection has already proved fresh/waiting instances. *)
Lemma flag_pend_caller_save_input_task_fields :
  forall environment critical local active sg original call mask state,
  (forall observed current, active observed current |--
    coq_prop (exists task, flag_active_task_fields original observed current task) &&
      active observed current) ->
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller call) call mask state |--
  coq_prop (exists task, flag_active_task_fields original call state task) &&
    flag_pend_caller_save_input environment critical local active sg
      (FlagPendTaskCaller call) call mask state.
Proof.
  intros environment critical local active sg original call mask state Hfields heap Howned.
  split; [|exact Howned].
  destruct Howned as [_ [owned [rest [Hjoin [Hsave Hunmap]]]]].
  destruct Hsave as [core [active_heap [Hsplit [Hcore Hactive]]]].
  exact (proj1 (Hfields call state active_heap Hactive)).
Qed.

End SequenceReturn.
