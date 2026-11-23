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
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_idle_frames_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


Module SelectedIdleWakeStatus.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import PrimitiveComponent SelectedIdleFrames.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma tick_task_update_keeps_ready_task_ready : forall node,
  is_effectively_ready node.(stat) node.(dly) = true ->
  is_effectively_ready (tick_task_update node).(stat) (tick_task_update node).(dly) = true.
Proof.
  intros node Hready; unfold tick_task_update.
  destruct (Z.eqb node.(dly) 0) eqn:Hzero; [exact Hready|].
  unfold is_effectively_ready in Hready.
  destruct (Z.eqb (task_non_suspension_bits node.(stat)) 0); [|discriminate].
  rewrite Hzero, Bool.andb_false_r in Hready; discriminate.
Qed.

Lemma kernel_wake_c_source_used_priority_transport : forall sg entry returned,
  WakeComponent.kernel_wake_c_source sg entry returned ->
  task_used_priority_transport entry.(TskState) returned.(TskState).
Proof.
  intros sg entry returned Hsource; destruct Hsource.
  - destruct (flag_task_rdy_result _ _ _ _ _ _ _ H)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]].
    eapply task_update_used_priority_transport; [exact Hold|reflexivity|reflexivity].
  - unfold event_task_rdy in H.
    destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
    destruct (entry.(TskState).(prioTbl) (event_wait_priority entry.(TskState) event))
      as [| |slot]; try discriminate.
    destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
    injection H as Hpriority Hreturned; subst returned.
    eapply task_update_used_priority_transport; [exact Hold|reflexivity|reflexivity].
  - rewrite (tick_task_step_task_state_eq sg slot old entry H).
    eapply task_update_used_priority_transport; [exact H| |];
      unfold tick_task_update; destruct (Z.eqb old.(dly) 0); reflexivity.
Qed.

Lemma kernel_wake_c_source_preserves_idle_ready : forall sg entry returned,
  WakeComponent.kernel_wake_c_source sg entry returned ->
  task_idle_ready sg entry.(TskState) -> task_idle_ready sg returned.(TskState).
Proof.
  intros sg entry returned Hsource Hidle; destruct Hsource.
  - destruct (flag_task_rdy_result _ _ _ _ _ _ _ H)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]].
    eapply task_update_ready_preserves_idle_ready; [exact Hold|reflexivity| |exact Hidle].
    apply task_flag_wake_keeps_ready_task_ready.
  - unfold event_task_rdy in H.
    destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
    destruct (entry.(TskState).(prioTbl) (event_wait_priority entry.(TskState) event))
      as [| |slot]; try discriminate.
    destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
    injection H as Hpriority Hreturned; subst returned.
    eapply task_update_ready_preserves_idle_ready; [exact Hold|reflexivity| |exact Hidle].
    apply task_event_wake_single_keeps_ready_task_ready.
  - rewrite (tick_task_step_task_state_eq sg slot old entry H).
    eapply task_update_ready_preserves_idle_ready; [exact H| | |exact Hidle].
    + unfold tick_task_update; destruct (Z.eqb old.(dly) 0); reflexivity.
    + apply tick_task_update_keeps_ready_task_ready.
Qed.

Lemma kernel_wake_c_segment_idle_non_idle : forall sg call entry before input returned after output,
  WakeComponent.kernel_wake_c_segment sg entry before input returned after output ->
  (task_idle_ready sg entry.(TskState) -> task_idle_ready sg returned.(TskState)) /\
  (flag_pend_non_idle_at sg call entry -> flag_pend_non_idle_at sg call returned).
Proof.
  intros sg call entry before input returned after output Hstep.
  pose proof (WakeComponent.kernel_wake_c_segment_source _ _ _ _ _ _ _ Hstep) as Hsource.
  split; [eapply kernel_wake_c_source_preserves_idle_ready; exact Hsource|].
  apply task_used_priority_transport_non_idle.
  eapply kernel_wake_c_source_used_priority_transport; exact Hsource.
Qed.

Lemma kernel_status_c_source_used_priority_transport : forall sg entry returned,
  StatusComponent.kernel_status_c_source sg entry returned ->
  task_used_priority_transport entry.(TskState) returned.(TskState).
Proof.
  intros sg entry returned Hsource; destruct Hsource.
  - destruct H as [cid [current [_ [_ [_ Hstep]]]]].
    destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg priority current))).
    + destruct Hstep as [_ ->]; apply task_used_priority_transport_refl.
    + destruct Hstep as [_ ->]; apply task_used_priority_transport_refl.
    + destruct Hstep as [old [Hold [_ ->]]].
      eapply task_update_used_priority_transport; [exact Hold|reflexivity|reflexivity].
  - destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority).
    + destruct Hstep as [_ ->]; apply task_used_priority_transport_refl.
    + destruct Hstep as [_ ->]; apply task_used_priority_transport_refl.
    + destruct Hstep as [old [Hold Hstep]]; destruct (task_is_suspended old.(stat)).
      * destruct Hstep as [_ ->].
        eapply task_update_used_priority_transport; [exact Hold|reflexivity|reflexivity].
      * destruct Hstep as [_ ->]; apply task_used_priority_transport_refl.
  - destruct H as [event [fields [_ [_ [_ ->]]]]]; destruct (Z.ltb 0 fields.(semCount));
      apply task_used_priority_transport_refl.
Qed.

(** This marker retains the actual Suspend branch observation on the same
    source proof.  Resume and SemAccept need no extra source condition. *)
Inductive kernel_status_c_idle_source (sg : StableGlobVars) : forall entry returned,
  StatusComponent.kernel_status_c_source sg entry returned -> Prop :=
| KernelStatusCSuspendIdleSource : forall entry priority result returned
    (actual : task_suspend_critical sg priority entry result returned),
    task_suspend_idle_guard_critical sg priority entry result returned ->
    kernel_status_c_idle_source sg entry returned
      (StatusComponent.KernelStatusCSuspendSource sg entry priority result returned actual)
| KernelStatusCResumeIdleSource : forall entry priority result returned
    (actual : task_resume_critical sg priority entry result returned),
    kernel_status_c_idle_source sg entry returned
      (StatusComponent.KernelStatusCResumeSource sg entry priority result returned actual)
| KernelStatusCSemAcceptIdleSource : forall entry eid count returned
    (actual : sem_accept_critical sg eid entry count returned),
    kernel_status_c_idle_source sg entry returned
      (StatusComponent.KernelStatusCSemAcceptSource sg entry eid count returned actual).

Lemma task_suspend_idle_guard_source_cases : forall sg priority entry result returned,
  task_suspend_idle_guard_critical sg priority entry result returned ->
  returned = entry \/
  exists actual : task_suspend_critical sg priority entry result returned,
    kernel_status_c_idle_source sg entry returned
      (StatusComponent.KernelStatusCSuspendSource sg entry priority result returned actual).
Proof.
  intros sg priority entry result returned Hactual.
  destruct (task_suspend_idle_guard_original_or_unchanged _ _ _ _ _ Hactual) as [Heq|Hcritical].
  - left; exact Heq.
  - right; exists Hcritical; constructor; exact Hactual.
Qed.

Lemma kernel_status_c_idle_source_preserves_idle_ready : forall sg entry returned
  (source : StatusComponent.kernel_status_c_source sg entry returned),
  UCOS2_state_inv sg entry -> kernel_status_c_idle_source sg entry returned source ->
  task_idle_ready sg entry.(TskState) -> task_idle_ready sg returned.(TskState).
Proof.
  intros sg entry returned source Hvalid Hactual Hidle.
  destruct Hactual as [entry priority result returned Hcritical Hguard|
    entry priority result returned Hcritical|entry eid count returned Hcritical].
  - eapply task_suspend_idle_guard_preserves_idle_ready; eassumption.
  - destruct Hcritical as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority).
    + destruct Hstep as [_ ->]; exact Hidle.
    + destruct Hstep as [_ ->]; exact Hidle.
    + destruct Hstep as [old [Hold Hstep]]; destruct (task_is_suspended old.(stat)) eqn:Hsusp.
      * destruct Hstep as [_ ->].
        eapply task_update_ready_preserves_idle_ready; [exact Hold|reflexivity| |exact Hidle].
        intro Hready; exfalso; unfold is_effectively_ready in Hready.
        destruct (Z.eqb (task_non_suspension_bits old.(stat)) 0); [|discriminate].
        rewrite Hsusp in Hready; discriminate.
      * destruct Hstep as [_ ->]; exact Hidle.
  - destruct Hcritical as [event [fields [_ [_ [_ ->]]]]]; destruct (Z.ltb 0 fields.(semCount)); exact Hidle.
Qed.

Lemma kernel_status_c_segment_idle_non_idle : forall sg call entry before returned after frame
  (segment : StatusComponent.kernel_status_c_segment sg entry before returned after frame),
  kernel_status_c_idle_source sg entry returned
    (StatusComponent.kernel_status_c_segment_code _ _ _ _ _ _ segment) ->
  (task_idle_ready sg entry.(TskState) -> task_idle_ready sg returned.(TskState)) /\
  (flag_pend_non_idle_at sg call entry -> flag_pend_non_idle_at sg call returned).
Proof.
  intros sg call entry before returned after frame [Hsource Hinput Houtput] Hactual; simpl in Hactual.
  destruct Hinput as [owned [rest [Hjoin [[Hvalid Hraw] Hframe]]]].
  split; [eapply kernel_status_c_idle_source_preserves_idle_ready; eassumption|].
  apply task_used_priority_transport_non_idle.
  eapply kernel_status_c_source_used_priority_transport; exact Hsource.
Qed.

End SelectedIdleWakeStatus.
