(** Report-only ordinary module extracted from the frozen checked C context.
    The original proof bodies are retained under the recorded shared-reference map. *)
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
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.















Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.




















Import UCOS2_C_Rules TaskStateDef SchedStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.



















































Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition sched_observer_current_cache (origin : TaskInvocationOrigin)
  (state : UCOS2_Verify_State) : Prop :=
  match origin with
  | BootInvocation => True
  | RunningInvocation slot generation =>
      forall node, state.(TskState).(inUsedTaskStates) slot = Some node ->
        node.(taskGeneration) = generation ->
        state.(SchedState).(curTaskID) = Some slot ->
        state.(SchedState).(curSchedPrio) = Some node.(curPrio)
  end.


Lemma sched_current_consistency_implies_observer_cache : forall origin state,
  sched_current_consistency state.(TskState) state.(SchedState) ->
  sched_observer_current_cache origin state.
Proof.
  intros [|slot generation] state Hconsistent; [exact I|].
  intros node Hnode Hgeneration Hcurrent.
  unfold sched_current_consistency in Hconsistent; rewrite Hcurrent in Hconsistent.
  destruct Hconsistent as [current [Hlookup Hcache]].
  assert (current = node) by congruence; subst current; exact Hcache.
Qed.

Lemma sched_current_frame_preserves_observer_cache :
  forall observer origin before after,
  task_invocation_active before.(TskState) observer origin ->
  after.(SchedState).(curTaskID) = before.(SchedState).(curTaskID) ->
  (sched_current_consistency before.(TskState) before.(SchedState) ->
   sched_current_consistency after.(TskState) after.(SchedState)) ->
  sched_observer_current_cache origin before ->
  sched_observer_current_cache origin after.
Proof.
  intros observer [|slot generation] before after Hactive Hframe Hwriter Hbefore;
    [exact I|].
  intros node Hnode Hgeneration Hcurrent.
  destruct Hactive as [_ [_ [old [Hold Hold_generation]]]].
  assert (Hcurrent_before : before.(SchedState).(curTaskID) = Some slot)
    by (rewrite <- Hframe; exact Hcurrent).
  assert (Hconsistent_before : sched_current_consistency before.(TskState) before.(SchedState)).
  { unfold sched_current_consistency; rewrite Hcurrent_before.
    exists old; split; [exact Hold|].
    exact (Hbefore old Hold Hold_generation Hcurrent_before). }
  pose proof (Hwriter Hconsistent_before) as Hconsistent_after.
  exact (sched_current_consistency_implies_observer_cache
    (RunningInvocation slot generation) after Hconsistent_after
    node Hnode Hgeneration Hcurrent).
Qed.

Lemma task_create_stack_publication_current_timer_frame :
  forall publication sg before after,
  kernel_client_step (task_create_stack_publication_client publication) sg before after ->
  after.(SchedState).(curTaskID) = before.(SchedState).(curTaskID) /\
  before.(TimerState) = after.(TimerState).
Proof.
  intros publication sg before after [_ ->]; split; reflexivity.
Qed.

Lemma task_create_stack_publication_preserves_observer_cache :
  forall publication sg observer origin before after,
  UCOS2_state_inv sg before ->
  task_invocation_active before.(TskState) observer origin ->
  sched_observer_current_cache origin before ->
  kernel_client_step (task_create_stack_publication_client publication) sg before after ->
  sched_observer_current_cache origin after.
Proof.
  intros publication sg observer origin before after Hvalid Hactive Hcache Hstep.
  eapply sched_current_frame_preserves_observer_cache; [exact Hactive| | |exact Hcache].
  - exact (proj1 (task_create_stack_publication_current_timer_frame
      publication sg before after Hstep)).
  - intro Hcurrent.
    exact (task_create_stack_publication_preserves_current_consistency
      publication sg before after Hvalid Hcurrent Hstep).
Qed.

Lemma kernel_call_task_source_observer_cache : forall call state,
  kernel_call_task_source call state ->
  sched_observer_current_cache call.(os_sched_call_origin) state ->
  sched_current_consistency state.(TskState) state.(SchedState).
Proof.
  intros call state [Horigin [Hactive Hcurrent]] Hcache.
  rewrite Horigin in Hactive, Hcurrent, Hcache.
  destruct Hactive as [_ [_ [node [Hnode Hgeneration]]]].
  unfold task_execution_current in Hcurrent.
  unfold sched_current_consistency; rewrite Hcurrent.
  exists node; split; [exact Hnode|].
  exact (Hcache node Hnode Hgeneration Hcurrent).
Qed.











Definition task_observer_private_fresh tasks origin : Prop :=
  match origin with
  | BootInvocation => True
  | RunningInvocation slot generation =>
      forall p entry allocation,
        tasks.(taskLifecycle).(taskReservations) p = Some entry ->
        entry.(creationAllocation) = Some allocation ->
        allocation.(privateSlot) = slot -> allocation.(privateGeneration) <> generation
  end.

Definition task_observer_generation_bound tasks origin : Prop :=
  match origin with
  | BootInvocation => True
  | RunningInvocation _ generation =>
      (generation < tasks.(taskLifecycle).(taskNextGeneration))%nat
  end.

(** No active/current-live requirement occurs here. The registered old
    observer remains meaningful after its slot has become a free image. *)

Definition task_observer_lifetime tasks observer origin : Prop :=
  tasks.(taskLifecycle).(taskInvocations) observer = Some origin /\
  (observer < tasks.(taskLifecycle).(taskNextInvocation))%nat /\
  task_observer_generation_bound tasks origin /\ task_observer_private_fresh tasks origin.

Definition task_observer_lifetime_transport observer origin before after : Prop :=
  task_observer_lifetime before observer origin ->
  task_observer_lifetime after observer origin /\
  (task_invocation_active after observer origin -> task_invocation_active before observer origin).

(** A proved property of a concrete segment, not a constructor for its
    source. [stopped] is computed by the actual retirement/recycle branch. *)

Definition task_observer_lifetime_result observer origin before after stopped : Prop :=
  task_observer_lifetime_transport observer origin before after /\
  (task_observer_lifetime before observer origin -> stopped = true ->
   ~ task_invocation_active after observer origin).

Lemma task_observer_lifetime_from_active : forall sg tasks observer origin,
  task_in_range sg tasks -> task_invocation_active tasks observer origin ->
  task_observer_lifetime tasks observer origin.
Proof.
  intros sg tasks observer origin [Hpool [_ [_ [_ [Hgeneration _]]]]] [Hreg [Hret Hlive]].
  destruct Hgeneration as [_ [_ [Hinv [Horigin _]]]].
  unfold task_observer_lifetime; split; [exact Hreg|].
  split; [eapply Hinv; exact Hreg|].
  destruct origin as [|slot generation]; [split; exact I|].
  split; [eapply Horigin; exact Hreg|].
  intros p entry allocation Hentry Halloc Hslot Hgeneration.
  destruct Hlive as [node [Hnode Hg]].
  assert (Hprivate : task_private_slot tasks slot).
  { exists p, entry, allocation; repeat split; assumption. }
  destruct Hpool as [_ [Hused _]].
  exact (proj2 (Hused slot node Hnode) Hprivate).
Qed.

Lemma task_observer_lifetime_transport_refl : forall tasks observer origin,
  task_observer_lifetime_transport observer origin tasks tasks.
Proof. intros tasks observer origin Hlife; split; [exact Hlife|auto]. Qed.

Lemma task_observer_lifetime_transport_trans : forall observer origin before middle after,
  task_observer_lifetime_transport observer origin before middle ->
  task_observer_lifetime_transport observer origin middle after ->
  task_observer_lifetime_transport observer origin before after.
Proof.
  intros observer origin before middle after Hfirst Hlast Hlife.
  destruct (Hfirst Hlife) as [Hmiddle Hback1].
  destruct (Hlast Hmiddle) as [Hafter Hback2]; split; [exact Hafter|auto].
Qed.

Lemma task_observer_lifetime_result_not_stopped : forall observer origin before after,
  task_observer_lifetime_transport observer origin before after ->
  task_observer_lifetime_result observer origin before after false.
Proof. intros; split; [exact H|intros _ Hbad; discriminate]. Qed.

Lemma task_observer_lifetime_result_seq : forall observer origin before middle after first_stop last_stop,
  task_observer_lifetime_result observer origin before middle first_stop ->
  task_observer_lifetime_result observer origin middle after last_stop ->
  task_observer_lifetime_result observer origin before after (orb first_stop last_stop).
Proof.
  intros observer origin before middle after first_stop last_stop [Hfirst Hstop1] [Hlast Hstop2].
  split; [eapply task_observer_lifetime_transport_trans; eassumption|].
  intros Hlife Hstop Hactive; apply Bool.orb_true_iff in Hstop.
  destruct (Hfirst Hlife) as [Hmiddle Hback1].
  destruct Hstop as [Hstop|Hstop].
  - apply (Hstop1 Hlife Hstop); exact (proj2 (Hlast Hmiddle) Hactive).
  - exact (Hstop2 Hmiddle Hstop Hactive).
Qed.

Lemma task_observer_lifetime_transport_fields : forall observer origin before after,
  after.(taskLifecycle) = before.(taskLifecycle) ->
  (forall slot, option_map taskGeneration (after.(inUsedTaskStates) slot) =
                option_map taskGeneration (before.(inUsedTaskStates) slot)) ->
  task_observer_lifetime_transport observer origin before after.
Proof.
  intros observer origin before after Hlife Hnodes Hscope; split.
  - unfold task_observer_lifetime, task_observer_generation_bound, task_observer_private_fresh in *.
    rewrite Hlife; exact Hscope.
  - intros [Hreg [Hret Hlive]].
    split; [rewrite <- Hlife; exact Hreg|]. split; [rewrite <- Hlife; exact Hret|].
    destruct origin as [|slot generation]; [exact I|].
    destruct Hlive as [node [Hnode Hg]].
    pose proof (Hnodes slot) as Hobs; rewrite Hnode in Hobs; simpl in Hobs.
    destruct (before.(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
    exists old; split; [exact Hold|]. simpl in Hobs; congruence.
Qed.

Lemma task_update_observer_lifetime_transport : forall tasks tid old replacement observer origin,
  tasks.(inUsedTaskStates) tid = Some old -> replacement.(taskGeneration) = old.(taskGeneration) ->
  task_observer_lifetime_transport observer origin tasks (glob_task_set_usedtask tasks tid replacement).
Proof.
  intros tasks tid old replacement observer origin Hold Hg.
  apply task_observer_lifetime_transport_fields; [reflexivity|].
  intro slot; simpl; destruct (Z.eqb slot tid) eqn:Heq; [|reflexivity].
  apply Z.eqb_eq in Heq; subst slot; rewrite Hold; simpl; congruence.
Qed.

Lemma kernel_call_same_return_observer_active : forall original returned after,
  task_tcb_init_stack_same_call returned original -> kernel_call_task_source returned after ->
  task_invocation_active after.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin).
Proof.
  intros original returned after [Hinv [Horigin Hstack]] [_ [Hactive _]].
  rewrite <- Hinv, <- Horigin; exact Hactive.
Qed.

Lemma kernel_call_completed_observer_not_stopped : forall original returned before after stopped,
  task_observer_lifetime before.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_observer_lifetime_result original.(os_sched_call_invocation) original.(os_sched_call_origin)
    before.(TskState) after.(TskState) stopped ->
  kernel_call_normal_return original before returned after ->
  kernel_call_task_source returned after -> stopped = false.
Proof.
  intros original returned before after stopped Hlife [Htransport Hstopped] [Hsame Havailable] Hsource.
  destruct stopped; [|reflexivity].
  exfalso; apply (Hstopped Hlife eq_refl).
  eapply kernel_call_same_return_observer_active; eassumption.
Qed.

Lemma kernel_call_completed_task_source_not_stopped : forall sg original returned before after stopped,
  task_in_range sg before.(TskState) -> kernel_call_task_source original before ->
  task_observer_lifetime_result original.(os_sched_call_invocation) original.(os_sched_call_origin)
    before.(TskState) after.(TskState) stopped ->
  kernel_call_normal_return original before returned after ->
  kernel_call_task_source returned after -> stopped = false.
Proof.
  intros sg original returned before after stopped Hrange [_ [Hactive Hcurrent]] Hresult Hnormal Hreturned.
  eapply kernel_call_completed_observer_not_stopped; [|exact Hresult|exact Hnormal|exact Hreturned].
  eapply task_observer_lifetime_from_active; eassumption.
Qed.

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
