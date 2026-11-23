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
Require Export Ucos2Verify.VC.code.task.spec.task_del_c_segment_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_create_c_segment_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Export Ucos2Verify.VC.code.queue.spec.q_create_c_segment_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_c_segment_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


Module SelectedIdleFrames.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import PrimitiveComponent.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The lookup retains the same slot and generation.  Priority equality is
    proved only for source operations that actually frame priority. *)
Definition task_used_priority_transport (before after : Glob_TaskAbstractState) : Prop :=
  forall slot node, before.(inUsedTaskStates) slot = Some node ->
  exists current, after.(inUsedTaskStates) slot = Some current /\
    current.(taskGeneration) = node.(taskGeneration) /\ current.(curPrio) = node.(curPrio).

Lemma task_used_priority_transport_refl : forall tasks,
  task_used_priority_transport tasks tasks.
Proof. intros tasks slot node Hnode; exists node; auto. Qed.

Lemma task_used_priority_transport_non_idle : forall sg call before after,
  task_used_priority_transport before.(TskState) after.(TskState) ->
  flag_pend_non_idle_at sg call before -> flag_pend_non_idle_at sg call after.
Proof.
  intros sg call before after Htransport [node [Hnode [Hgeneration Hpriority]]].
  destruct (Htransport _ _ Hnode) as [current [Hcurrent [Hg Hp]]].
  exists current; split; [exact Hcurrent|]. rewrite Hg, Hp; auto.
Qed.

Lemma task_used_map_eq_idle_non_idle : forall sg call before after,
  after.(TskState).(inUsedTaskStates) = before.(TskState).(inUsedTaskStates) ->
  (task_idle_ready sg before.(TskState) -> task_idle_ready sg after.(TskState)) /\
  (flag_pend_non_idle_at sg call before -> flag_pend_non_idle_at sg call after).
Proof.
  intros sg call before after Hnodes; unfold task_idle_ready, flag_pend_non_idle_at.
  rewrite Hnodes; auto.
Qed.

Lemma task_update_used_priority_transport : forall tasks slot old updated,
  tasks.(inUsedTaskStates) slot = Some old ->
  updated.(taskGeneration) = old.(taskGeneration) -> updated.(curPrio) = old.(curPrio) ->
  task_used_priority_transport tasks (glob_task_set_usedtask tasks slot updated).
Proof.
  intros tasks slot old updated Hold Hg Hp observed node Hnode.
  destruct (Z.eq_dec observed slot) as [->|Hdifferent].
  - assert (node = old) by congruence; subst node. exists updated.
    cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; auto.
  - exists node; cbn [glob_task_set_usedtask inUsedTaskStates].
    rewrite (proj2 (Z.eqb_neq _ _) Hdifferent); auto.
Qed.

Lemma task_update_ready_preserves_idle_ready : forall sg tasks slot old updated,
  tasks.(inUsedTaskStates) slot = Some old -> updated.(curPrio) = old.(curPrio) ->
  (is_effectively_ready old.(stat) old.(dly) = true ->
    is_effectively_ready updated.(stat) updated.(dly) = true) ->
  task_idle_ready sg tasks -> task_idle_ready sg (glob_task_set_usedtask tasks slot updated).
Proof.
  intros sg tasks slot old updated Hold Hp Hready [idle [node [Hnode [Hprio Hnode_ready]]]].
  destruct (Z.eq_dec idle slot) as [->|Hdifferent].
  - assert (node = old) by congruence; subst node. exists slot, updated.
    cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl.
    split; [reflexivity|]. split; [congruence|apply Hready; exact Hnode_ready].
  - exists idle, node; cbn [glob_task_set_usedtask inUsedTaskStates].
    rewrite (proj2 (Z.eqb_neq _ _) Hdifferent); auto.
Qed.

Lemma kernel_task_creation_c_source_used_map_eq : forall sg entry returned,
  CreationComponent.kernel_task_creation_c_source sg entry returned ->
  returned.(TskState).(inUsedTaskStates) = entry.(TskState).(inUsedTaskStates).
Proof.
  intros sg entry returned Hsource; destruct Hsource; try reflexivity.
  - unfold task_create_critical in H; destruct (Z.ltb 0 entry.(IntrState).(intNesting)).
    + destruct H as [_ ->]; reflexivity.
    + destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority);
        destruct Hstep as [_ ->]; reflexivity.
  - destruct H2 as [_ ->]; reflexivity.
Qed.

Lemma kernel_task_creation_c_segment_idle_non_idle : forall sg call entry before input returned after output,
  CreationComponent.kernel_task_creation_c_segment sg entry before input returned after output ->
  (task_idle_ready sg entry.(TskState) -> task_idle_ready sg returned.(TskState)) /\
  (flag_pend_non_idle_at sg call entry -> flag_pend_non_idle_at sg call returned).
Proof.
  intros; apply task_used_map_eq_idle_non_idle.
  eapply kernel_task_creation_c_source_used_map_eq,
    CreationComponent.kernel_task_creation_c_segment_source; eassumption.
Qed.

Lemma kernel_event_creation_c_segment_idle_non_idle : forall sg call entry before input returned after output,
  EventCreationComponent.kernel_event_creation_c_segment sg entry before input returned after output ->
  (task_idle_ready sg entry.(TskState) -> task_idle_ready sg returned.(TskState)) /\
  (flag_pend_non_idle_at sg call entry -> flag_pend_non_idle_at sg call returned).
Proof.
  intros sg call entry before input returned after output Hstep.
  pose proof (EventCreationComponent.kernel_event_creation_c_segment_source _ _ _ _ _ _ _ Hstep) as Hsource.
  pose proof (proj1 (EventCreationComponent.kernel_event_creation_c_source_fields_eq _ _ Hsource)) as Htasks.
  apply task_used_map_eq_idle_non_idle; rewrite Htasks; reflexivity.
Qed.

Lemma kernel_queue_creation_c_segment_idle_non_idle : forall sg call entry before input returned after output,
  QueueCreationComponent.kernel_queue_creation_c_segment sg entry before input returned after output ->
  (task_idle_ready sg entry.(TskState) -> task_idle_ready sg returned.(TskState)) /\
  (flag_pend_non_idle_at sg call entry -> flag_pend_non_idle_at sg call returned).
Proof.
  intros sg call entry before input returned after output Hstep.
  pose proof (QueueCreationComponent.kernel_queue_creation_c_segment_source _ _ _ _ _ _ _ Hstep) as Hsource.
  pose proof (proj1 (QueueCreationComponent.kernel_queue_creation_c_source_fields_eq _ _ _ Hsource)) as Htasks.
  apply task_used_map_eq_idle_non_idle; rewrite Htasks; reflexivity.
Qed.

Lemma task_install_c_step_idle_non_idle : forall environment local sg call entry before input stopped returned after output,
  InstallComponent.task_install_c_step environment local sg entry before input stopped returned after output ->
  (task_idle_ready sg entry.(TskState) -> task_idle_ready sg returned.(TskState)) /\
  (flag_pend_non_idle_at sg call entry -> flag_pend_non_idle_at sg call returned).
Proof.
  intros environment local sg observed entry before input stopped returned after output Hstep.
  destruct Hstep as [frame call before after sp Hactual [Hsource Hcomplete]].
  pose proof (proj1 (os_sched_install_client_state_frame environment.(task_stack_call_external)
    call.(InstallComponent.task_install_fields_context) call.(InstallComponent.task_install_fields_outgoing)
    call.(InstallComponent.task_install_fields_incoming) call.(InstallComponent.task_install_fields_resumed)
    sg call.(InstallComponent.task_install_fields_entry)
    (InstallComponent.task_install_fields_current call) Hsource)) as Hnodes.
  apply task_used_map_eq_idle_non_idle; exact Hnodes.
Qed.

Lemma task_delete_primitive_c_segment_idle_non_idle :
  forall environment critical sg call entry before input stopped returned after output,
  DeleteComponent.task_delete_primitive_c_segment environment critical sg
    entry before input stopped returned after output ->
  (task_idle_ready sg entry.(TskState) -> task_idle_ready sg returned.(TskState)) /\
  (flag_pend_non_idle_at sg call entry -> flag_pend_non_idle_at sg call returned).
Proof. intros; destruct H; split; auto. Qed.

Lemma flag_pend_task_primitive_c_step_idle_non_idle :
  forall environment critical sg call entry before input stopped returned after output,
  flag_pend_task_primitive_c_step environment critical sg entry before input stopped returned after output ->
  (task_idle_ready sg entry.(TskState) -> task_idle_ready sg returned.(TskState)) /\
  (flag_pend_non_idle_at sg call entry -> flag_pend_non_idle_at sg call returned).
Proof.
  intros until output; intro Hstep; destruct Hstep.
  - destruct H; split; auto.
  - split; auto.
  - split; auto.
Qed.

End SelectedIdleFrames.
