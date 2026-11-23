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
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_idle_protocol_spec.
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
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_critical_control_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_c_idle_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


Module SelectedIdleCritical.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import CriticalComponent PrimitiveComponent SelectedCriticalControl SelectedMutexIdle.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma task_change_priority_state_idle_fields : forall sg entry tid old selected destination,
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  let returned := task_change_priority_state sg entry tid old selected destination in
  returned.(TskState).(taskLifecycle) = entry.(TskState).(taskLifecycle) /\
  (forall slot node, entry.(TskState).(inUsedTaskStates) slot = Some node ->
    exists current, returned.(TskState).(inUsedTaskStates) slot = Some current /\
      current.(taskGeneration) = node.(taskGeneration) /\
      current.(stat) = node.(stat) /\ current.(dly) = node.(dly)).
Proof.
  intros sg entry tid old selected destination Hold returned.
  split; [reflexivity|]. intros slot node Hnode.
  change (exists current,
    (glob_task_set_usedtask entry.(TskState) tid (mutex_priority_task old destination)).(inUsedTaskStates)
      slot = Some current /\ current.(taskGeneration) = node.(taskGeneration) /\
      current.(stat) = node.(stat) /\ current.(dly) = node.(dly)).
  cbn [glob_task_set_usedtask inUsedTaskStates].
  destruct (Z.eqb slot tid) eqn:Heq.
  - apply Z.eqb_eq in Heq; subst slot. assert (node = old) by congruence; subst node.
    exists (mutex_priority_task old destination); repeat split; reflexivity.
  - exists node; repeat split; assumption || reflexivity.
Qed.

Lemma task_change_prio_critical_idle_fields : forall sg requested destination entry result returned,
  task_change_prio_critical sg requested destination entry result returned ->
  returned.(TskState).(taskLifecycle) = entry.(TskState).(taskLifecycle) /\
  (forall slot node, entry.(TskState).(inUsedTaskStates) slot = Some node ->
    exists current, returned.(TskState).(inUsedTaskStates) slot = Some current /\
      current.(taskGeneration) = node.(taskGeneration) /\
      current.(stat) = node.(stat) /\ current.(dly) = node.(dly)).
Proof.
  intros sg requested destination entry result returned Hcritical.
  assert (Hrefl : entry.(TskState).(taskLifecycle) = entry.(TskState).(taskLifecycle) /\
    (forall slot node, entry.(TskState).(inUsedTaskStates) slot = Some node ->
      exists current, entry.(TskState).(inUsedTaskStates) slot = Some current /\
        current.(taskGeneration) = node.(taskGeneration) /\
        current.(stat) = node.(stat) /\ current.(dly) = node.(dly))).
  { split; [reflexivity|]. intros; exists node; auto. }
  unfold task_change_prio_critical in Hcritical.
  destruct (entry.(TskState).(prioTbl) destination).
  - destruct Hcritical as [selected [Hselection Hcritical]].
    unfold task_change_prio_selected_effect in Hcritical.
    destruct (Z.eqb selected sg.(osLowestPrio)).
    + destruct Hcritical as [_ ->]; exact Hrefl.
    + destruct (entry.(TskState).(prioTbl) selected).
      * destruct Hcritical as [_ ->]; exact Hrefl.
      * destruct Hcritical as [_ ->]; exact Hrefl.
      * destruct Hcritical as [old [Hold [_ ->]]].
        apply task_change_priority_state_idle_fields; exact Hold.
  - destruct Hcritical as [_ ->]; exact Hrefl.
  - destruct Hcritical as [_ ->]; exact Hrefl.
Qed.

Lemma kernel_critical_c_source_idle_fields : forall sg call,
  kernel_critical_c_source sg call ->
  (kernel_critical_c_returned call).(TskState).(taskLifecycle) =
    (kernel_critical_c_entry call).(TskState).(taskLifecycle) /\
  (forall slot old, (kernel_critical_c_entry call).(TskState).(inUsedTaskStates) slot = Some old ->
    exists current, (kernel_critical_c_returned call).(TskState).(inUsedTaskStates) slot = Some current /\
      current.(taskGeneration) = old.(taskGeneration)) /\
  mutex_del_preserves_runnable (kernel_critical_c_entry call) (kernel_critical_c_returned call).
Proof.
  intros sg [actual|actual] Hsource; simpl in *.
  - destruct Hsource as [result [Hcritical Hencoded]].
    destruct (task_change_prio_critical_idle_fields _ _ _ _ _ _ Hcritical) as [Hlife Hfields].
    split; [exact Hlife|]. split.
    + intros slot old Hold; destruct (Hfields slot old Hold) as [current [Hcurrent [Hg Hrest]]].
      exists current; auto.
    + intros slot old Hold Hready.
      destruct (Hfields slot old Hold) as [current [Hcurrent [Hg [Hs Hd]]]].
      exists current; split; [exact Hcurrent|]. rewrite Hs, Hd; exact Hready.
  - unfold mutex_del_critical_fields_observation in Hsource.
    destruct Hsource as [result code request checkpoint Hguard Hobservation|kind Htype Hnotmutex].
    + destruct Hobservation as [error [scheduled [Hcritical Hencoding]]].
      destruct (mutex_del_critical_call_fields_eq _ _ _ _ _ _ Hcritical)
        as [Hnodes [Hstacks [Hlife Hrest]]].
      split; [exact Hlife|]. split.
      * intros slot old Hold; pose proof (Hnodes slot) as Hnode; rewrite Hold in Hnode.
        destruct (checkpoint.(TskState).(inUsedTaskStates) slot) as [current|] eqn:Hcurrent;
          simpl in Hnode; [|discriminate].
        exists current; split; [reflexivity|congruence].
      * eapply mutex_del_critical_preserves_runnable; exact Hcritical.
    + split; [reflexivity|]. split.
      * intros slot old Hold; exists old; auto.
      * apply mutex_del_preserves_runnable_refl.
Qed.

Lemma kernel_critical_c_owner_valid : forall environment critical local sg frame call state heap,
  (kernel_critical_c_owner environment critical local sg call state ** frame) heap ->
  UCOS2_state_inv sg state.
Proof.
  intros environment critical local sg frame call state heap Howner.
  assert (Hvalid : kernel_critical_c_owner environment critical local sg call state ** frame |--
    coq_prop (UCOS2_state_inv sg state) &&
      (kernel_critical_c_owner environment critical local sg call state ** frame)).
  { destruct call; unfold kernel_critical_c_owner, task_change_prio_fields_owner,
      task_change_prio_masked, mutex_del_fields_owner,
      mutex_del_runtime_program_restore_pre, kernel_program_inv, UCOS2_inv;
      Intros; entailer!. }
  exact (proj1 (Hvalid heap Howner)).
Qed.

Lemma kernel_critical_c_segment_idle_non_idle :
  forall environment critical local sg frame call before after observed,
  kernel_critical_c_segment environment critical local sg frame call before after ->
  (kernel_critical_c_entry call).(SchedState).(isRunning) = true ->
  (task_idle_ready sg (kernel_critical_c_entry call).(TskState) ->
    task_idle_ready sg (kernel_critical_c_returned call).(TskState)) /\
  (flag_pend_non_idle_at sg observed (kernel_critical_c_entry call) ->
    flag_pend_non_idle_at sg observed (kernel_critical_c_returned call)).
Proof.
  intros environment critical local sg frame call before after observed Hsegment Hrunning.
  destruct (kernel_critical_c_segment_resources _ _ _ _ _ _ _ _ Hsegment) as [Hinput Houtput].
  pose proof Hsegment as [Hcompletion [Hphysical [Hsource Hpacket]]].
  destruct (kernel_critical_c_source_idle_fields sg call Hsource) as [Hlife [Hnodes Hrunnable]].
  eapply running_active_order_preserves_idle_non_idle.
  - eapply kernel_critical_c_owner_valid; exact Hinput.
  - eapply kernel_critical_c_owner_valid; exact Houtput.
  - exact Hrunning.
  - eapply kernel_critical_c_segment_running; exact Hsegment.
  - rewrite Hlife; reflexivity.
  - exact Hnodes.
  - exact Hrunnable.
Qed.

End SelectedIdleCritical.
