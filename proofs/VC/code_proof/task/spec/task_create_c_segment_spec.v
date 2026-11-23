(** Report-only ordinary module extracted from the frozen checked C context.
    The original proof bodies are retained under the recorded shared-reference map. *)
Require Import Coq.micromega.Lia.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_preparation_spec.
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
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_always_nonswitch_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_wake_source_spec.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_region_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_nontimer_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.flag_fields_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.lib.kernel_execution.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_local_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_irq_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.lib.task_retirement.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_sched_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_inherit_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_client_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_return_spec.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_api_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_disabled_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.lib.flag_stack.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_unlink_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_source_call_spec.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.lib.flag_node_fields.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_unlink_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_fields_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_fields_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_api_entry_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_return_stage_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_idle_ready_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_call_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_save_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_wake_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_irq_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_delete_source_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module CreationComponent.





























Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Import FlagPendSchedulerResources.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

















Import TaskStateDef SchedStateDef.
Local Open Scope Z_scope.














Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma task_observer_lifetime_transport_inactive : forall observer origin before after,
  task_observer_lifetime_transport observer origin before after ->
  task_observer_lifetime before observer origin ->
  ~ task_invocation_active before observer origin ->
  ~ task_invocation_active after observer origin.
Proof. intros observer origin before after Hstep Hlife Hgone Hactive; apply Hgone; exact (proj2 (Hstep Hlife) Hactive). Qed.

Lemma task_begin_invocation_observer_lifetime_transport : forall tasks caller observer origin,
  task_observer_lifetime_transport observer origin tasks (task_begin_invocation caller tasks).
Proof.
  intros tasks caller observer origin [Hreg [Hbound [Hg Hprivate]]].
  assert (Hneq : observer <> tasks.(taskLifecycle).(taskNextInvocation)) by lia.
  split.
  - unfold task_observer_lifetime; simpl; destruct Nat.eq_dec; [contradiction|].
    split; [exact Hreg|]. split; [lia|]. split; assumption.
  - intros [Hmap [Hret Hlive]].
    unfold task_begin_invocation in Hmap, Hret; simpl in Hmap, Hret.
    destruct Nat.eq_dec; [contradiction|]. repeat split; assumption.
Qed.
Lemma task_reserve_observer_lifetime_transport : forall tasks p invocation caller observer origin,
  task_observer_lifetime_transport observer origin tasks (task_reserve tasks p invocation caller).
Proof.
  intros tasks p invocation caller observer origin [Hreg [Hbound [Hg Hprivate]]]; split.
  - split; [exact Hreg|]. split; [exact Hbound|]. split; [exact Hg|].
    destruct origin as [|slot generation]; [exact I|].
    intros q entry allocation Hentry Halloc Hslot; simpl in Hentry.
    destruct (Z.eq_dec q p).
    + injection Hentry as Hentry; subst entry; discriminate.
    + eapply Hprivate; eassumption.
  - exact (fun H => H).
Qed.
Lemma task_detach_observer_lifetime_transport : forall tasks p entry tid rest image observer origin,
  task_observer_lifetime_transport observer origin tasks (task_detach_head tasks p entry tid rest image).
Proof.
  intros tasks p entry tid rest image observer origin [Hreg [Hbound [Hg Hprivate]]]; split.
  - split; [exact Hreg|]. split; [exact Hbound|].
    destruct origin as [|slot generation]; [split; exact I|].
    split; [unfold task_observer_generation_bound in *; simpl; lia|].
    intros q selected allocation Hentry Halloc Hslot; simpl in Hentry.
    destruct (Z.eq_dec q p).
    + injection Hentry as He; subst selected; simpl in Halloc; injection Halloc as Ha; subst allocation.
      simpl; unfold task_observer_generation_bound in Hg; lia.
    + eapply Hprivate; eassumption.
  - exact (fun H => H).
Qed.
Lemma task_private_image_observer_lifetime_transport :
  forall tasks p entry allocation image observer origin,
  tasks.(taskLifecycle).(taskReservations) p = Some entry ->
  entry.(creationAllocation) = Some allocation ->
  task_observer_lifetime_transport observer origin tasks (task_update_private_image tasks p entry allocation image).
Proof.
  intros tasks p entry allocation image observer origin Hentry Halloc [Hreg [Hbound [Hg Hprivate]]]; split.
  - split; [exact Hreg|]. split; [exact Hbound|]. split; [exact Hg|].
    destruct origin as [|slot generation]; [exact I|].
    intros q selected own Hselected Hown Hslot; simpl in Hselected.
    destruct (Z.eq_dec q p).
    + injection Hselected as He; subst selected; simpl in Hown; injection Hown as Ha; subst own.
      simpl in Hslot |- *; eapply Hprivate; eassumption.
    + eapply Hprivate; eassumption.
  - exact (fun H => H).
Qed.
Lemma task_rollback_observer_lifetime_transport : forall tasks p observer origin,
  task_observer_lifetime_transport observer origin tasks (task_rollback_reservation tasks p).
Proof.
  intros tasks p observer origin [Hreg [Hbound [Hg Hprivate]]]; split.
  - split; [exact Hreg|]. split; [exact Hbound|]. split; [exact Hg|].
    destruct origin as [|slot generation]; [exact I|].
    intros q entry allocation Hentry Halloc Hslot; simpl in Hentry.
    destruct (Z.eq_dec q p); [discriminate|]. eapply Hprivate; eassumption.
  - exact (fun H => H).
Qed.
(** The actual creation bookkeeping and C store phases.  Publication and
    retirement have their own already checked leaves.  None of the phases
    below changes a live node's priority or the current scheduler cache. *)
Inductive kernel_task_creation_c_source (sg : StableGlobVars) :
  UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| KernelTaskCreationCBeginSource : forall entry caller,
    task_generation_closure entry.(TskState) ->
    task_invocation_origin_live entry.(TskState) caller ->
    kernel_task_creation_c_source sg entry
      (replace_TskS (task_begin_invocation caller entry.(TskState)) entry)
| KernelTaskCreationCCriticalSource : forall entry priority invocation caller result returned,
    task_create_critical sg priority invocation caller entry result returned ->
    kernel_task_creation_c_source sg entry returned
| KernelTaskCreationCRollbackSource : forall critical args invocation caller initial released
    entry result returned,
    task_tcb_init_entry sg args invocation caller initial ->
    task_tcb_init_result critical sg args invocation caller initial 66 released ->
    critical_region_interval critical sg invocation released entry ->
    task_create_rollback_store args.(initPrio) entry result returned ->
    kernel_task_creation_c_source sg entry returned
| KernelTaskCreationCDetachSource : forall args invocation caller entry slot rest image,
    task_tcb_init_entry sg args invocation caller entry ->
    task_tcb_init_detach_observation args invocation caller entry slot rest image ->
    kernel_task_creation_c_source sg entry
      (task_tcb_init_detached_state args invocation caller entry slot rest image)
| KernelTaskCreationCPrivateSource : forall args entry reservation allocation,
    entry.(TskState).(taskLifecycle).(taskReservations) args.(initPrio) = Some reservation ->
    reservation.(creationAllocation) = Some allocation ->
    kernel_task_creation_c_source sg entry
      (replace_TskS (task_tcb_init_initialize_private sg args entry.(TskState)
        reservation allocation) entry)
| KernelTaskCreationCPrepareFieldsSource : forall input slot rest image,
    task_create_stack_input_facts sg input ->
    input.(stack_input_state).(IntrState).(intNesting) = 0 ->
    input.(stack_input_state).(TskState).(prioTbl) input.(stack_input_args).(createPriority) = PTFree ->
    task_tcb_init_detach_observation (task_create_stack_input_args input)
      input.(stack_input_call).(os_sched_call_invocation) input.(stack_input_call).(os_sched_call_origin)
      (task_create_stack_input_acquired input) slot rest image ->
    kernel_task_creation_c_source sg input.(stack_input_state)
      (task_create_stack_input_detached input slot rest image).

Lemma kernel_task_creation_c_source_preserves_observer_cache : forall sg entry returned origin,
  kernel_task_creation_c_source sg entry returned ->
  sched_observer_current_cache origin entry -> sched_observer_current_cache origin returned.
Proof.
  intros sg entry returned origin Hsource Hcache; destruct Hsource.
  - exact Hcache.
  - unfold task_create_critical in H; destruct (Z.ltb 0 entry.(IntrState).(intNesting)).
    + destruct H as [_ ->]; exact Hcache.
    + destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority);
        destruct Hstep as [_ ->]; exact Hcache.
  - destruct H2 as [_ ->]; exact Hcache.
  - exact Hcache.
  - exact Hcache.
  - exact Hcache.
Qed.

Lemma kernel_task_creation_c_source_preserves_observer_active :
  forall sg entry returned observer origin,
  kernel_task_creation_c_source sg entry returned ->
  task_invocation_active entry.(TskState) observer origin ->
  task_invocation_active returned.(TskState) observer origin.
Proof.
  intros sg entry returned observer origin Hsource Hactive; destruct Hsource.
  - apply task_begin_invocation_preserves_invocation_active; assumption.
  - unfold task_create_critical in H; destruct (Z.ltb 0 entry.(IntrState).(intNesting)).
    + destruct H as [_ ->]; exact Hactive.
    + destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority);
        destruct Hstep as [_ ->]; exact Hactive.
  - destruct H2 as [_ ->]; exact Hactive.
  - exact Hactive.
  - exact Hactive.
  - exact Hactive.
Qed.

Lemma kernel_task_creation_c_source_lifetime_result : forall sg entry returned observer origin,
  kernel_task_creation_c_source sg entry returned ->
  task_observer_lifetime_result observer origin entry.(TskState) returned.(TskState) false.
Proof.
  intros sg entry returned observer origin Hsource.
  apply task_observer_lifetime_result_not_stopped; destruct Hsource.
  - apply task_begin_invocation_observer_lifetime_transport.
  - unfold task_create_critical in H; destruct (Z.ltb 0 entry.(IntrState).(intNesting)).
    + destruct H as [_ ->]; apply task_observer_lifetime_transport_refl.
    + destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority);
        destruct Hstep as [_ ->].
      * apply task_reserve_observer_lifetime_transport.
      * apply task_observer_lifetime_transport_refl.
      * apply task_observer_lifetime_transport_refl.
  - destruct H2 as [_ ->]; apply task_rollback_observer_lifetime_transport.
  - apply task_detach_observer_lifetime_transport.
  - apply task_private_image_observer_lifetime_transport; assumption.
  - eapply task_observer_lifetime_transport_trans with
      (middle := (task_create_stack_input_acquired input).(TskState)).
    + apply task_reserve_observer_lifetime_transport.
    + apply task_detach_observer_lifetime_transport.
Qed.

(** Each constructor fixes the actual module owner.  Detach transfers the
    free TCB image to the caller; private initialization keeps that image
    separately owned.  The frame is never copied or replaced. *)
Inductive kernel_task_creation_c_segment (sg : StableGlobVars) :
  UCOS2_Verify_State -> model -> Assertion -> UCOS2_Verify_State -> model -> Assertion -> Prop :=
| KernelTaskCreationCBeginSegment : forall entry caller h frame,
    task_generation_closure entry.(TskState) ->
    task_invocation_origin_live entry.(TskState) caller ->
    (UCOS2_inv sg entry ** frame) h ->
    (UCOS2_inv sg (replace_TskS (task_begin_invocation caller entry.(TskState)) entry) ** frame) h ->
    kernel_task_creation_c_segment sg entry h (UCOS2_inv sg entry ** frame)
      (replace_TskS (task_begin_invocation caller entry.(TskState)) entry) h
      (UCOS2_inv sg (replace_TskS (task_begin_invocation caller entry.(TskState)) entry) ** frame)
| KernelTaskCreationCCriticalSegment : forall entry priority invocation caller result returned before after frame,
    task_create_critical sg priority invocation caller entry result returned ->
    (UCOS2_inv sg entry ** frame) before ->
    (UCOS2_inv sg returned ** frame) after ->
    kernel_task_creation_c_segment sg entry before (UCOS2_inv sg entry ** frame)
      returned after (UCOS2_inv sg returned ** frame)
| KernelTaskCreationCRollbackSegment : forall critical args invocation caller initial released
    entry result returned before after frame,
    task_tcb_init_entry sg args invocation caller initial ->
    task_tcb_init_result critical sg args invocation caller initial 66 released ->
    critical_region_interval critical sg invocation released entry ->
    task_create_rollback_store args.(initPrio) entry result returned ->
    (UCOS2_inv sg entry ** frame) before ->
    (UCOS2_inv sg returned ** frame) after ->
    kernel_task_creation_c_segment sg entry before (UCOS2_inv sg entry ** frame)
      returned after (UCOS2_inv sg returned ** frame)
| KernelTaskCreationCDetachSegment : forall args invocation caller entry slot rest image before after frame,
    task_tcb_init_entry sg args invocation caller entry ->
    task_tcb_init_detach_observation args invocation caller entry slot rest image ->
    (UCOS2_inv sg entry ** frame) before ->
    (UCOS2_inv sg (task_tcb_init_detached_state args invocation caller entry slot rest image) **
      (task_slot_storage_rep sg slot image ** frame)) after ->
    kernel_task_creation_c_segment sg entry before (UCOS2_inv sg entry ** frame)
      (task_tcb_init_detached_state args invocation caller entry slot rest image) after
      (UCOS2_inv sg (task_tcb_init_detached_state args invocation caller entry slot rest image) **
        (task_slot_storage_rep sg slot image ** frame))
| KernelTaskCreationCPrivateSegment : forall args entry reservation allocation before after frame,
    entry.(TskState).(taskLifecycle).(taskReservations) args.(initPrio) = Some reservation ->
    reservation.(creationAllocation) = Some allocation ->
    (UCOS2_inv sg entry ** (task_slot_storage_rep sg allocation.(privateSlot)
      allocation.(privateStorage) ** frame)) before ->
    (UCOS2_inv sg (replace_TskS (task_tcb_init_initialize_private sg args entry.(TskState)
      reservation allocation) entry) **
      (task_slot_storage_rep sg allocation.(privateSlot)
        (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
          sg.(osKernelConfig).(cfgTaskProfile) args allocation.(privateStorage)) ** frame)) after ->
    kernel_task_creation_c_segment sg entry before
      (UCOS2_inv sg entry ** (task_slot_storage_rep sg allocation.(privateSlot)
        allocation.(privateStorage) ** frame))
      (replace_TskS (task_tcb_init_initialize_private sg args entry.(TskState)
        reservation allocation) entry) after
      (UCOS2_inv sg (replace_TskS (task_tcb_init_initialize_private sg args entry.(TskState)
        reservation allocation) entry) **
        (task_slot_storage_rep sg allocation.(privateSlot)
          (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
            sg.(osKernelConfig).(cfgTaskProfile) args allocation.(privateStorage)) ** frame))
| KernelTaskCreationCPrepareFieldsSegment : forall input slot rest image before after frame,
    task_create_stack_input_facts sg input ->
    input.(stack_input_state).(IntrState).(intNesting) = 0 ->
    input.(stack_input_state).(TskState).(prioTbl) input.(stack_input_args).(createPriority) = PTFree ->
    task_tcb_init_detach_observation (task_create_stack_input_args input)
      input.(stack_input_call).(os_sched_call_invocation) input.(stack_input_call).(os_sched_call_origin)
      (task_create_stack_input_acquired input) slot rest image ->
    task_create_stack_preparation_fragment sg input slot rest before after ->
    (UCOS2_fields_inv sg input.(stack_input_state) **
      task_stack_storage input.(stack_input_region)
        (input.(stack_input_lower) ++ input.(stack_input_old_frame) ++ input.(stack_input_upper)) ** frame) before ->
    (task_tcb_init_publication_fields_tail_storage sg (task_create_stack_input_args input)
       (task_create_stack_input_detached input slot rest image) slot image **
      task_stack_storage input.(stack_input_region)
        (task_create_stack_publication_words (task_create_stack_prepared_publication input slot image)) ** frame) after ->
    kernel_task_creation_c_segment sg input.(stack_input_state) before
      (UCOS2_fields_inv sg input.(stack_input_state) **
        task_stack_storage input.(stack_input_region)
          (input.(stack_input_lower) ++ input.(stack_input_old_frame) ++ input.(stack_input_upper)) ** frame)
      (task_create_stack_input_detached input slot rest image) after
      (task_tcb_init_publication_fields_tail_storage sg (task_create_stack_input_args input)
         (task_create_stack_input_detached input slot rest image) slot image **
        task_stack_storage input.(stack_input_region)
          (task_create_stack_publication_words (task_create_stack_prepared_publication input slot image)) ** frame).

Lemma task_begin_invocation_c_owner_segment : forall sg entry caller h frame,
  task_invocation_origin_live entry.(TskState) caller ->
  (UCOS2_inv sg entry ** frame) h ->
  kernel_task_creation_c_segment sg entry h (UCOS2_inv sg entry ** frame)
    (replace_TskS (task_begin_invocation caller entry.(TskState)) entry) h
    (UCOS2_inv sg (replace_TskS (task_begin_invocation caller entry.(TskState)) entry) ** frame).
Proof.
  intros sg entry caller h frame Hlive Hpre.
  destruct Hpre as [hbody [hframe [Hjoin [Hbody Hframe]]]].
  pose proof (proj1 Hbody) as Hvalid.
  pose proof (proj1 (proj2 Hvalid)) as Htasks.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 Htasks))))) as Hgeneration.
  apply KernelTaskCreationCBeginSegment; try assumption.
  - exists hbody, hframe; split; [exact Hjoin|]; split; assumption.
  - exists hbody, hframe; split; [exact Hjoin|]; split; [|exact Hframe].
    exact (UCOS2_inv_begin_task_invocation sg entry caller Hlive hbody Hbody).
Qed.

Lemma task_create_critical_c_post_segment :
  forall sg entry priority invocation caller result returned before after frame,
  (UCOS2_inv sg entry ** frame) before ->
  (coq_prop (task_create_critical sg priority invocation caller entry result returned) &&
    (UCOS2_inv sg returned ** frame)) after ->
  kernel_task_creation_c_segment sg entry before (UCOS2_inv sg entry ** frame)
    returned after (UCOS2_inv sg returned ** frame).
Proof.
  intros sg entry priority invocation caller result returned before after frame Hpre [Hcode Hpost].
  eapply KernelTaskCreationCCriticalSegment; eassumption.
Qed.

Lemma task_create_rollback_c_store_post_segment :
  forall critical sg args invocation caller initial released entry result returned before after frame,
  task_tcb_init_entry sg args invocation caller initial ->
  task_tcb_init_result critical sg args invocation caller initial 66 released ->
  critical_region_interval critical sg invocation released entry ->
  task_create_rollback_store args.(initPrio) entry result returned ->
  (UCOS2_inv sg entry ** frame) before ->
  (((sg.(g_OSTCBPrioTbl) + args.(initPrio) * sizeof(PTR)) # Ptr |-> 0 **
    store_prio_tbl_missing_i sg entry.(TskState).(prioTbl) args.(initPrio) **
    UCOS2_raw_rep_missing_priority_table sg entry) ** frame) after ->
  kernel_task_creation_c_segment sg entry before (UCOS2_inv sg entry ** frame)
    returned after (UCOS2_inv sg returned ** frame).
Proof.
  intros critical sg args invocation caller initial released entry result returned before after frame
    Hinitial Hresult Hinterval Hcode Hpre Hpost.
  eapply KernelTaskCreationCRollbackSegment; try eassumption.
  destruct Hpost as [hbody [hframe [Hjoin [Hbody Hframe]]]].
  exists hbody, hframe; split; [exact Hjoin|]; split; [|exact Hframe].
  destruct Hcode as [_ ->].
  exact (proj2 (task_create_no_free_rollback_merge_inv critical sg args invocation caller
    initial released entry Hinitial Hresult Hinterval hbody Hbody)).
Qed.

Lemma task_tcb_init_detach_c_store_post_segment :
  forall sg args invocation caller entry slot rest image before after frame,
  task_tcb_init_entry sg args invocation caller entry ->
  task_tcb_init_detach_observation args invocation caller entry slot rest image ->
  (UCOS2_inv sg entry ** frame) before ->
  ((sg.(g_OSTCBFreeList) # Ptr |-> task_tcb_init_free_next sg rest **
    task_tcb_init_public_without_free_head sg entry rest) **
    (task_slot_storage_rep sg slot image ** frame)) after ->
  kernel_task_creation_c_segment sg entry before (UCOS2_inv sg entry ** frame)
    (task_tcb_init_detached_state args invocation caller entry slot rest image) after
    (UCOS2_inv sg (task_tcb_init_detached_state args invocation caller entry slot rest image) **
      (task_slot_storage_rep sg slot image ** frame)).
Proof.
  intros sg args invocation caller entry slot rest image before after frame Hentry Hdetach Hpre Hpost.
  apply KernelTaskCreationCDetachSegment; try assumption.
  destruct Hpost as [hbody [hframe [Hjoin [Hbody Hframe]]]].
  exists hbody, hframe; split; [exact Hjoin|]; split; [|exact Hframe].
  exact (task_tcb_init_detach_merge_invariant sg args invocation caller entry slot rest image
    Hentry Hdetach hbody Hbody).
Qed.

Lemma task_tcb_init_private_c_store_post_segment :
  forall sg args entry reservation allocation before after frame,
  entry.(TskState).(taskLifecycle).(taskReservations) args.(initPrio) = Some reservation ->
  reservation.(creationAllocation) = Some allocation ->
  (UCOS2_inv sg entry ** (task_slot_storage_rep sg allocation.(privateSlot)
    allocation.(privateStorage) ** frame)) before ->
  (UCOS2_inv sg entry ** (task_slot_storage_rep sg allocation.(privateSlot)
    (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
      sg.(osKernelConfig).(cfgTaskProfile) args allocation.(privateStorage)) ** frame)) after ->
  kernel_task_creation_c_segment sg entry before
    (UCOS2_inv sg entry ** (task_slot_storage_rep sg allocation.(privateSlot)
      allocation.(privateStorage) ** frame))
    (replace_TskS (task_tcb_init_initialize_private sg args entry.(TskState)
      reservation allocation) entry) after
    (UCOS2_inv sg (replace_TskS (task_tcb_init_initialize_private sg args entry.(TskState)
      reservation allocation) entry) **
      (task_slot_storage_rep sg allocation.(privateSlot)
        (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
          sg.(osKernelConfig).(cfgTaskProfile) args allocation.(privateStorage)) ** frame)).
Proof.
  intros sg args entry reservation allocation before after frame Hreservation Halloc Hpre Hpost.
  apply KernelTaskCreationCPrivateSegment; try assumption.
  destruct Hpost as [hbody [hframe [Hjoin [Hbody Hframe]]]].
  exists hbody, hframe; split; [exact Hjoin|]; split; [|exact Hframe].
  exact (task_tcb_init_private_initialization_frames_global_inv sg args entry reservation allocation
    Hreservation Halloc hbody Hbody).
Qed.

Lemma kernel_task_creation_c_segment_source : forall sg entry before input returned after output,
  kernel_task_creation_c_segment sg entry before input returned after output ->
  kernel_task_creation_c_source sg entry returned.
Proof.
  intros sg entry before input returned after output Hsegment; destruct Hsegment.
  - eapply KernelTaskCreationCBeginSource; eassumption.
  - eapply KernelTaskCreationCCriticalSource; eassumption.
  - eapply KernelTaskCreationCRollbackSource; eassumption.
  - eapply KernelTaskCreationCDetachSource; eassumption.
  - eapply KernelTaskCreationCPrivateSource; eassumption.
  - eapply KernelTaskCreationCPrepareFieldsSource; eassumption.
Qed.

Lemma kernel_task_creation_c_segment_resources : forall sg entry before input returned after output,
  kernel_task_creation_c_segment sg entry before input returned after output ->
  input before /\ output after.
Proof. intros sg entry before input returned after output Hsegment; destruct Hsegment; split; assumption. Qed.

Lemma kernel_task_creation_c_segment_preserves_observer :
  forall sg entry before input returned after output observer origin,
  kernel_task_creation_c_segment sg entry before input returned after output ->
  task_invocation_active entry.(TskState) observer origin /\ sched_observer_current_cache origin entry ->
  task_invocation_active returned.(TskState) observer origin /\ sched_observer_current_cache origin returned.
Proof.
  intros sg entry before input returned after output observer origin Hsegment [Hactive Hcache].
  pose proof (kernel_task_creation_c_segment_source _ _ _ _ _ _ _ Hsegment) as Hsource.
  split.
  - eapply kernel_task_creation_c_source_preserves_observer_active; eassumption.
  - eapply kernel_task_creation_c_source_preserves_observer_cache; eassumption.
Qed.

Lemma kernel_task_creation_c_segment_lifetime_result :
  forall sg entry before input returned after output observer origin,
  kernel_task_creation_c_segment sg entry before input returned after output ->
  task_observer_lifetime_result observer origin entry.(TskState) returned.(TskState) false.
Proof.
  intros sg entry before input returned after output observer origin Hsegment.
  apply kernel_task_creation_c_source_lifetime_result with (sg := sg).
  eapply kernel_task_creation_c_segment_source; exact Hsegment.
Qed.














End CreationComponent.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
(** Sources decorate the original C completion proof.  They retain the
    invocation/allocation from that completion; no constructor assumes any
    creation-frame, cache, ready or future-return conclusion. *)
Import EventStateDef.
Import EventStateDef.
