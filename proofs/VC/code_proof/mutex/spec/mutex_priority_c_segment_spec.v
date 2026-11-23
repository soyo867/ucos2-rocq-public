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
Require Export Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module PendComponent.





























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

(** The busy branch's owner snapshot supplies a real old-node lookup and
    owner <> current.  The three inheritance actions retain this exact
    source relation; no endpoint cache or future-return premise is added. *)
Lemma mutex_pend_inherit_preserves_observer_cache :
  forall sg origin entry owner node base waiter ceiling inherited,
  entry.(SchedState).(curTaskID) <> Some owner ->
  mutex_pend_inherit_step sg entry owner node base waiter ceiling inherited ->
  sched_observer_current_cache origin entry ->
  sched_observer_current_cache origin inherited.
Proof.
  intros sg [|slot generation] entry owner node base waiter ceiling inherited
    Hother Hstep Hcache; [exact I|].
  unfold mutex_pend_inherit_step in Hstep.
  destruct (mutex_pend_inherit_action _ _ _ _ _).
  - subst inherited; exact Hcache.
  - subst inherited; exact Hcache.
  - destruct Hstep as [events [_ ->]].
    intros current Hcurrent Hgen Hslot.
    change (entry.(SchedState).(curTaskID) = Some slot) in Hslot.
    change ((if Z.eqb slot owner then Some (mutex_priority_task node ceiling)
      else entry.(TskState).(inUsedTaskStates) slot) = Some current) in Hcurrent.
    assert (Hneq : slot <> owner) by congruence.
    rewrite (proj2 (Z.eqb_neq slot owner) Hneq) in Hcurrent.
    exact (Hcache current Hcurrent Hgen Hslot).
Qed.

Lemma mutex_pend_inherit_preserves_observer_active :
  forall sg entry owner node base waiter ceiling inherited observer origin,
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  mutex_pend_inherit_step sg entry owner node base waiter ceiling inherited ->
  task_invocation_active entry.(TskState) observer origin ->
  task_invocation_active inherited.(TskState) observer origin.
Proof.
  intros sg entry owner node base waiter ceiling inherited observer origin Hnode Hstep
    [Hregistered [Hretired Hlive]].
  destruct (mutex_pend_inherit_call_fields_eq _ _ _ _ _ _ _ _ Hstep) as [Hlife _].
  destruct (mutex_pend_inherit_stack_nodes _ _ _ _ _ _ _ _ Hnode Hstep) as [_ Hforward].
  split; [rewrite Hlife; exact Hregistered|].
  split; [rewrite Hlife; exact Hretired|].
  destruct origin as [|slot generation]; [exact I|].
  destruct Hlive as [old [Hold Hg]].
  destruct (Hforward slot old Hold) as [current [Hcurrent [Hgen Hsp]]].
  exists current; split; [exact Hcurrent|congruence].
Qed.

Lemma mutex_pend_inherit_observer_lifetime_result :
  forall sg entry owner node base waiter ceiling inherited observer origin,
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  mutex_pend_inherit_step sg entry owner node base waiter ceiling inherited ->
  task_observer_lifetime_result observer origin entry.(TskState) inherited.(TskState) false.
Proof.
  intros sg entry owner node base waiter ceiling inherited observer origin Hnode Hstep.
  apply task_observer_lifetime_result_not_stopped.
  destruct (mutex_pend_inherit_call_fields_eq _ _ _ _ _ _ _ _ Hstep) as [Hlife _].
  destruct (mutex_pend_inherit_stack_nodes _ _ _ _ _ _ _ _ Hnode Hstep) as [Hback Hforward].
  apply task_observer_lifetime_transport_fields; [exact Hlife|].
  intro slot.
  destruct (inherited.(TskState).(inUsedTaskStates) slot) as [current|] eqn:Hcurrent.
  - destruct (Hback slot current Hcurrent) as [old [Hold [Hg Hsp]]].
    rewrite Hold; simpl; congruence.
  - destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|reflexivity].
    destruct (Hforward slot old Hold) as [current [Hcurrent' _]]; congruence.
Qed.

Record MutexPendInheritanceCCall : Type := {
  mutex_pend_inheritance_context : OsSchedCallContext;
  mutex_pend_inheritance_saved : Z;
  mutex_pend_inheritance_entry : UCOS2_Verify_State;
  mutex_pend_inheritance_returned : UCOS2_Verify_State;
  mutex_pend_inheritance_owner : TaskID;
  mutex_pend_inheritance_node : TaskAbstractState;
  mutex_pend_inheritance_base : Priority;
  mutex_pend_inheritance_waiter : Priority;
  mutex_pend_inheritance_ceiling : Priority
}.

Definition mutex_pend_inheritance_c_source sg call : Prop :=
  call.(mutex_pend_inheritance_entry).(TskState).(inUsedTaskStates)
    call.(mutex_pend_inheritance_owner) = Some call.(mutex_pend_inheritance_node) /\
  call.(mutex_pend_inheritance_entry).(SchedState).(curTaskID) <>
    Some call.(mutex_pend_inheritance_owner) /\
  mutex_pend_inherit_step sg call.(mutex_pend_inheritance_entry)
    call.(mutex_pend_inheritance_owner) call.(mutex_pend_inheritance_node)
    call.(mutex_pend_inheritance_base) call.(mutex_pend_inheritance_waiter)
    call.(mutex_pend_inheritance_ceiling) call.(mutex_pend_inheritance_returned).

Section MutexPendInheritanceCSegment.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (saved_local : Armv7aContinuation -> Assertion) (sg : StableGlobVars) (frame : Assertion).

(** The literal masked frame in mutex_pend_api_spec:126, followed by the
    original UCOS2_inv.  Its token remains indexed by the acquired entry;
    only coverage and capsules are indexed by the actual current state. *)
Definition mutex_pend_inheritance_c_owner call state : Assertion :=
  (coq_prop (task_stack_live_coverage state.(TskState)
     (task_stack_call_active_key call.(mutex_pend_inheritance_context))) &&
   (critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(mutex_pend_inheritance_context).(os_sched_call_invocation)
      call.(mutex_pend_inheritance_context).(os_sched_call_origin)
      call.(mutex_pend_inheritance_saved) call.(mutex_pend_inheritance_entry) **
    os_sched_context_resources environment.(task_stack_call_external)
      call.(mutex_pend_inheritance_context) **
    task_tcb_init_continuation_capsules environment saved_local state ** unmap_table_rep sg)) **
  UCOS2_inv sg state.

(** C contract graph: both owners and the typed source observation are
    exported by the same critical completion, with the same outside frame.
    This is neither a new raw execution relation nor a registered client. *)
Record mutex_pend_inheritance_c_segment call before after : Prop := {
  mutex_pend_inheritance_segment_source : mutex_pend_inheritance_c_source sg call;
  mutex_pend_inheritance_segment_input :
    (mutex_pend_inheritance_c_owner call call.(mutex_pend_inheritance_entry) ** frame) before;
  mutex_pend_inheritance_segment_output :
    (mutex_pend_inheritance_c_owner call call.(mutex_pend_inheritance_returned) ** frame) after
}.

Lemma mutex_pend_inheritance_c_post_segment : forall call before after,
  (mutex_pend_inheritance_c_owner call call.(mutex_pend_inheritance_entry) ** frame) before ->
  (coq_prop (mutex_pend_inheritance_c_source sg call) &&
    (mutex_pend_inheritance_c_owner call call.(mutex_pend_inheritance_returned) ** frame)) after ->
  mutex_pend_inheritance_c_segment call before after.
Proof. intros call before after Hinput [Hsource Houtput]; constructor; assumption. Qed.

(** The real busy-call protocol supplies the nonowner observation.  This
    projection uses the same event/owner/current operands as the C branch. *)
Lemma mutex_pend_inheritance_busy_c_post_segment :
  forall call before after eid event mutex current,
  call.(mutex_pend_inheritance_entry).(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some call.(mutex_pend_inheritance_owner) ->
  call.(mutex_pend_inheritance_entry).(SchedState).(curTaskID) = Some current ->
  task_holds_no_mutex call.(mutex_pend_inheritance_entry).(EventState) current ->
  call.(mutex_pend_inheritance_entry).(TskState).(inUsedTaskStates)
    call.(mutex_pend_inheritance_owner) = Some call.(mutex_pend_inheritance_node) ->
  (mutex_pend_inheritance_c_owner call call.(mutex_pend_inheritance_entry) ** frame) before ->
  (coq_prop (mutex_pend_inherit_step sg call.(mutex_pend_inheritance_entry)
      call.(mutex_pend_inheritance_owner) call.(mutex_pend_inheritance_node)
      call.(mutex_pend_inheritance_base) call.(mutex_pend_inheritance_waiter)
      call.(mutex_pend_inheritance_ceiling) call.(mutex_pend_inheritance_returned)) &&
    (mutex_pend_inheritance_c_owner call call.(mutex_pend_inheritance_returned) ** frame)) after ->
  mutex_pend_inheritance_c_segment call before after.
Proof.
  intros call before after eid event mutex current He Htype Hmutex Howner Hcurrent
    Hholds Hnode Hinput [Hstep Houtput].
  constructor; [|exact Hinput|exact Houtput].
  split; [exact Hnode|]. split; [|exact Hstep].
  intro Hbad; assert (current = call.(mutex_pend_inheritance_owner)) by congruence.
  apply (Hholds eid event mutex He Htype Hmutex); congruence.
Qed.

Lemma mutex_pend_inheritance_c_segment_resources : forall call before after,
  mutex_pend_inheritance_c_segment call before after ->
  (mutex_pend_inheritance_c_owner call call.(mutex_pend_inheritance_entry) ** frame) before /\
  (mutex_pend_inheritance_c_owner call call.(mutex_pend_inheritance_returned) ** frame) after.
Proof. intros call before after [Hsource Hinput Houtput]; auto. Qed.

Lemma mutex_pend_inheritance_c_segment_preserves_observer :
  forall call before after observer origin,
  mutex_pend_inheritance_c_segment call before after ->
  task_invocation_active call.(mutex_pend_inheritance_entry).(TskState) observer origin /\
    sched_observer_current_cache origin call.(mutex_pend_inheritance_entry) ->
  task_invocation_active call.(mutex_pend_inheritance_returned).(TskState) observer origin /\
    sched_observer_current_cache origin call.(mutex_pend_inheritance_returned).
Proof.
  intros call before after observer origin [[Hnode [Hother Hstep]] Hinput Houtput] [Hactive Hcache].
  split.
  - eapply mutex_pend_inherit_preserves_observer_active; eassumption.
  - eapply mutex_pend_inherit_preserves_observer_cache; eassumption.
Qed.

Lemma mutex_pend_inheritance_c_segment_lifetime_result :
  forall call before after observer origin,
  mutex_pend_inheritance_c_segment call before after ->
  task_observer_lifetime_result observer origin call.(mutex_pend_inheritance_entry).(TskState)
    call.(mutex_pend_inheritance_returned).(TskState) false.
Proof.
  intros call before after observer origin [[Hnode [Hother Hstep]] Hinput Houtput].
  eapply mutex_pend_inherit_observer_lifetime_result; eassumption.
Qed.
End MutexPendInheritanceCSegment.










End PendComponent.
Module PostComponent.





























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

Lemma sched_observer_cache_fields_backward : forall origin before after,
  after.(SchedState).(curTaskID) = before.(SchedState).(curTaskID) ->
  after.(SchedState).(curSchedPrio) = before.(SchedState).(curSchedPrio) ->
  (forall slot node, after.(TskState).(inUsedTaskStates) slot = Some node ->
    exists old, before.(TskState).(inUsedTaskStates) slot = Some old /\
      old.(taskGeneration) = node.(taskGeneration) /\ old.(curPrio) = node.(curPrio)) ->
  sched_observer_current_cache origin before -> sched_observer_current_cache origin after.
Proof.
  intros [|slot generation] before after Hcurrent Hcache Hlookup Hbefore; [exact I|].
  intros node Hnode Hgeneration Hslot.
  destruct (Hlookup slot node Hnode) as [old [Hold [Hgen Hprio]]].
  rewrite Hcache, <- Hprio.
  apply (Hbefore old Hold); [rewrite Hgen; exact Hgeneration|].
  rewrite <- Hcurrent; exact Hslot.
Qed.
Lemma sched_observer_cache_update_task : forall origin before after tid old updated,
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  updated.(taskGeneration) = old.(taskGeneration) ->
  updated.(curPrio) = old.(curPrio) ->
  after.(TskState) = glob_task_set_usedtask before.(TskState) tid updated ->
  after.(SchedState).(curTaskID) = before.(SchedState).(curTaskID) ->
  after.(SchedState).(curSchedPrio) = before.(SchedState).(curSchedPrio) ->
  sched_observer_current_cache origin before -> sched_observer_current_cache origin after.
Proof.
  intros origin before after tid old updated Hold Hgen Hprio Htasks Hcurrent Hcache Hbefore.
  eapply sched_observer_cache_fields_backward; [exact Hcurrent|exact Hcache| |exact Hbefore].
  intros slot node Hnode; rewrite Htasks in Hnode.
  cbn [glob_task_set_usedtask inUsedTaskStates] in Hnode.
  destruct (Z.eqb slot tid) eqn:Hslot.
  - apply Z.eqb_eq in Hslot; subst slot.
    injection Hnode as Hnode; subst node.
    exists old; split; [exact Hold|]. split; symmetry; assumption.
  - exists node; split; [exact Hnode|]. split; reflexivity.
Qed.
Lemma mutex_del_relocated_preserves_observer_cache :
  forall sg origin entry ceiling owner node priority,
  sched_observer_current_cache origin entry ->
  sched_observer_current_cache origin (mutex_del_relocated_state sg entry ceiling owner node priority).
Proof.
  intros sg [|slot generation] entry ceiling owner node priority Hcache; [exact I|].
  intros after Hafter Hgeneration Hcurrent.
  change ((if Z.eqb slot owner then Some (mutex_priority_task node priority)
    else entry.(TskState).(inUsedTaskStates) slot) = Some after) in Hafter.
  change (entry.(SchedState).(curTaskID) = Some slot) in Hcurrent.
  change (mutex_del_current_priority entry owner priority = Some after.(curPrio)).
  unfold mutex_del_current_priority; rewrite Hcurrent.
  destruct (Z.eq_dec owner slot) as [Heq|Hdifferent].
  - subst slot; rewrite Z.eqb_refl in Hafter; injection Hafter as Hafter; subst after; reflexivity.
  - rewrite (proj2 (Z.eqb_neq slot owner) ltac:(congruence)) in Hafter.
    exact (Hcache after Hafter Hgeneration Hcurrent).
Qed.
Lemma mutex_del_wake_preserves_observer_cache :
  forall sg origin before eid kind message result priority after,
  event_task_rdy sg before eid kind message result = Some (priority, after) ->
  sched_observer_current_cache origin before -> sched_observer_current_cache origin after.
Proof.
  intros sg origin before eid kind message result priority after Hstep Hcache.
  unfold event_task_rdy in Hstep.
  destruct (before.(EventState).(inUsedEventStates) eid) as [event|] eqn:He; [|discriminate].
  destruct (before.(TskState).(prioTbl) (event_wait_priority before.(TskState) event))
    as [| |tid] eqn:Htable; try discriminate.
  destruct (before.(TskState).(inUsedTaskStates) tid) as [old|] eqn:Hold; [|discriminate].
  injection Hstep as Hpriority Hafter; subst after.
  eapply sched_observer_cache_update_task with
    (tid := tid) (old := old) (updated := task_event_wake_single old kind message result).
  - exact Hold.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [event_wake_state replace_SchedS SchedState]; unfold sched_wake_by_status.
    destruct task_status_is_suspended; reflexivity.
  - cbn [event_wake_state replace_SchedS SchedState]; unfold sched_wake_by_status.
    destruct task_status_is_suspended; reflexivity.
  - exact Hcache.
Qed.
(** The actual Post priority scan uses the same conditional cache store
    as Del, then restores the reserved ceiling view.  No observer/current
    liveness condition is needed for that physical priority update. *)
Lemma mutex_post_prepare_preserves_observer_cache :
  forall sg origin mutex owner entry prepared,
  mutex_post_prepare sg mutex owner entry prepared ->
  sched_observer_current_cache origin entry -> sched_observer_current_cache origin prepared.
Proof.
  intros sg origin mutex owner entry prepared Hprepare Hcache.
  unfold mutex_post_prepare in Hprepare; destruct Z.eq_dec.
  - subst prepared; exact Hcache.
  - destruct Hprepare as [node [priority [Hnode [Hscan ->]]]].
    unfold mutex_post_owner_priority_state; destruct Z.eq_dec.
    + exact Hcache.
    + change (sched_observer_current_cache origin
        (mutex_del_relocated_state sg entry mutex.(mfPCP) owner node priority)).
      apply mutex_del_relocated_preserves_observer_cache; exact Hcache.
Qed.

(** Keep NOT_OWNER, empty release, and successful/error handover results,
    including their literal schedule-request boolean.  A request is not
    observer retirement and is not used as the segment's stop result. *)
Lemma mutex_post_critical_preserves_observer_cache :
  forall sg origin eid caller entry result schedule checkpoint,
  mutex_post_critical sg eid caller entry result schedule checkpoint ->
  sched_observer_current_cache origin entry -> sched_observer_current_cache origin checkpoint.
Proof.
  intros sg origin eid caller entry result schedule checkpoint Hcritical Hcache.
  destruct Hcritical.
  - exact Hcache.
  - change (sched_observer_current_cache origin prepared).
    eapply mutex_post_prepare_preserves_observer_cache; eassumption.
  - change (sched_observer_current_cache origin woken).
    eapply mutex_del_wake_preserves_observer_cache; [exact H5|].
    eapply mutex_post_prepare_preserves_observer_cache; eassumption.
Qed.

Lemma mutex_post_critical_observer_fields :
  forall sg eid caller entry result schedule checkpoint,
  mutex_post_critical sg eid caller entry result schedule checkpoint ->
  checkpoint.(TskState).(taskLifecycle) = entry.(TskState).(taskLifecycle) /\
  (forall slot, option_map taskGeneration (checkpoint.(TskState).(inUsedTaskStates) slot) =
                option_map taskGeneration (entry.(TskState).(inUsedTaskStates) slot)).
Proof.
  intros sg eid caller entry result schedule checkpoint Hcritical.
  destruct (mutex_post_critical_call_fields_eq _ _ _ _ _ _ _ Hcritical)
    as [Hnodes [Hstacks [Hlife [Hcurrent Hprivate]]]].
  split; [exact Hlife|].
  intro slot; specialize (Hnodes slot).
  destruct (checkpoint.(TskState).(inUsedTaskStates) slot) as [post|];
    destruct (entry.(TskState).(inUsedTaskStates) slot) as [pre|];
    simpl in Hnodes |- *; congruence.
Qed.

Lemma mutex_post_critical_preserves_observer_active :
  forall sg eid caller entry result schedule checkpoint observer origin,
  mutex_post_critical sg eid caller entry result schedule checkpoint ->
  task_invocation_active entry.(TskState) observer origin ->
  task_invocation_active checkpoint.(TskState) observer origin.
Proof.
  intros sg eid caller entry result schedule checkpoint observer origin Hcritical
    [Hregistered [Hretired Hlive]].
  destruct (mutex_post_critical_observer_fields _ _ _ _ _ _ _ Hcritical) as [Hlife Hnodes].
  split; [rewrite Hlife; exact Hregistered|].
  split; [rewrite Hlife; exact Hretired|].
  destruct origin as [|slot generation]; [exact I|].
  destruct Hlive as [old [Hold Hg]].
  specialize (Hnodes slot); rewrite Hold in Hnodes.
  destruct (checkpoint.(TskState).(inUsedTaskStates) slot) as [current|] eqn:Hcurrent;
    simpl in Hnodes; [|discriminate].
  exists current; split; [exact Hcurrent|congruence].
Qed.

Lemma mutex_post_critical_observer_lifetime_result :
  forall sg eid caller entry result schedule checkpoint observer origin,
  mutex_post_critical sg eid caller entry result schedule checkpoint ->
  task_observer_lifetime_result observer origin entry.(TskState) checkpoint.(TskState) false.
Proof.
  intros sg eid caller entry result schedule checkpoint observer origin Hcritical.
  apply task_observer_lifetime_result_not_stopped.
  destruct (mutex_post_critical_observer_fields _ _ _ _ _ _ _ Hcritical) as [Hlife Hnodes].
  apply task_observer_lifetime_transport_fields; assumption.
Qed.

Record MutexPostCriticalCCall : Type := {
  mutex_post_critical_context : OsSchedCallContext;
  mutex_post_critical_saved : Z;
  mutex_post_critical_entry : UCOS2_Verify_State;
  mutex_post_critical_checkpoint : UCOS2_Verify_State;
  mutex_post_critical_eid : EventID;
  mutex_post_critical_caller : TaskID;
  mutex_post_critical_node : TaskAbstractState;
  mutex_post_critical_result : OSErrCode;
  mutex_post_critical_schedule : bool
}.

Definition mutex_post_critical_c_source sg call : Prop :=
  mutex_post_native_caller sg call.(mutex_post_critical_context).(os_sched_call_invocation)
    call.(mutex_post_critical_context).(os_sched_call_origin) call.(mutex_post_critical_entry)
    call.(mutex_post_critical_context) call.(mutex_post_critical_caller)
    call.(mutex_post_critical_node) /\
  mutex_post_critical sg call.(mutex_post_critical_eid) call.(mutex_post_critical_caller)
    call.(mutex_post_critical_entry) call.(mutex_post_critical_result)
    call.(mutex_post_critical_schedule) call.(mutex_post_critical_checkpoint).

Section MutexPostCriticalCSegment.
Context (source_env : MutexDelCallEnvironment) (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (saved_local : Armv7aContinuation -> Assertion) (sg : StableGlobVars) (frame : Assertion).

(** Literal critical owner before the real Restore in OSMutexPost.c.
    The acquired continuation stays indexed by its original acquired
    state, just as the already proved C contract requires. *)
Definition mutex_post_critical_c_owner call state : Assertion :=
  critical_region_masked platform critical sg
    call.(mutex_post_critical_context).(os_sched_call_invocation)
    call.(mutex_post_critical_context).(os_sched_call_origin)
    call.(mutex_post_critical_saved) call.(mutex_post_critical_entry) **
  UCOS2_inv sg state ** unmap_table_rep sg **
  mutex_del_continuation_acquired source_env external platform saved_local sg
    call.(mutex_post_critical_context) call.(mutex_post_critical_entry).

Record mutex_post_critical_c_segment call before after : Prop := {
  mutex_post_critical_segment_source : mutex_post_critical_c_source sg call;
  mutex_post_critical_segment_input :
    (mutex_post_critical_c_owner call call.(mutex_post_critical_entry) ** frame) before;
  mutex_post_critical_segment_output :
    (mutex_post_critical_c_owner call call.(mutex_post_critical_checkpoint) ** frame) after
}.

Lemma mutex_post_critical_c_post_segment : forall call before after,
  (mutex_post_critical_c_owner call call.(mutex_post_critical_entry) ** frame) before ->
  (coq_prop (mutex_post_critical_c_source sg call) &&
    (mutex_post_critical_c_owner call call.(mutex_post_critical_checkpoint) ** frame)) after ->
  mutex_post_critical_c_segment call before after.
Proof. intros call before after Hinput [Hsource Houtput]; constructor; assumption. Qed.

Lemma mutex_post_critical_c_segment_resources : forall call before after,
  mutex_post_critical_c_segment call before after ->
  (mutex_post_critical_c_owner call call.(mutex_post_critical_entry) ** frame) before /\
  (mutex_post_critical_c_owner call call.(mutex_post_critical_checkpoint) ** frame) after.
Proof. intros call before after [Hsource Hinput Houtput]; auto. Qed.

Lemma mutex_post_critical_c_segment_preserves_observer :
  forall call before after observer origin,
  mutex_post_critical_c_segment call before after ->
  task_invocation_active call.(mutex_post_critical_entry).(TskState) observer origin /\
    sched_observer_current_cache origin call.(mutex_post_critical_entry) ->
  task_invocation_active call.(mutex_post_critical_checkpoint).(TskState) observer origin /\
    sched_observer_current_cache origin call.(mutex_post_critical_checkpoint).
Proof.
  intros call before after observer origin [[Hcaller Hcritical] Hinput Houtput] [Hactive Hcache].
  split.
  - eapply mutex_post_critical_preserves_observer_active; eassumption.
  - eapply mutex_post_critical_preserves_observer_cache; eassumption.
Qed.

Lemma mutex_post_critical_c_segment_lifetime_result :
  forall call before after observer origin,
  mutex_post_critical_c_segment call before after ->
  task_observer_lifetime_result observer origin call.(mutex_post_critical_entry).(TskState)
    call.(mutex_post_critical_checkpoint).(TskState) false.
Proof.
  intros call before after observer origin [[Hcaller Hcritical] Hinput Houtput].
  eapply mutex_post_critical_observer_lifetime_result; eassumption.
Qed.
End MutexPostCriticalCSegment.











End PostComponent.

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
