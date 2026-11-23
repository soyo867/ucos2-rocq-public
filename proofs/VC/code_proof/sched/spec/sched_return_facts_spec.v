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
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module SchedulerReturnFacts.





























Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Only the SP field changes.  This pure C-state statement covers the
    existing live/free storage alternatives; it introduces no memory-safety
    or physical capture claim for a free current slot. *)
Lemma os_sched_save_sp_preserves_high_consistency : forall state slot sp,
  sched_high_ready_consistency state.(TskState) state.(SchedState) ->
  sched_high_ready_consistency (os_sched_save_current_sp state slot sp).(TskState)
    (os_sched_save_current_sp state slot sp).(SchedState).
Proof.
  intros state slot sp Hhigh.
  unfold os_sched_save_current_sp.
  destruct (state.(TskState).(inUsedTaskStates) slot) as [node|] eqn:Hnode.
  - cbn [replace_TskS TskState SchedState].
    unfold sched_high_ready_consistency in *.
    destruct state.(SchedState).(readyList) as [|head tail] eqn:Hlist.
    + exact Hhigh.
    + destruct Hhigh as [Hhead [high [Hlookup Hpriority]]].
      split; [exact Hhead|].
      destruct (Z.eqb head slot) eqn:Heq.
      * apply Z.eqb_eq in Heq; subst head.
        assert (high = node) by congruence; subst high.
        exists (task_set_saved_sp node sp); split; [|exact Hpriority].
        cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
      * exists high; split; [|exact Hpriority].
        cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Heq; exact Hlookup.
  - exact Hhigh.
Qed.

(** The LAST complete C switch source runs its own selector before SP-save
    and the fixed hook.  Its returning task identity comes from the already
    selected call contract.  This proves ready at that same final state;
    neither a first installed state nor an arbitrary old trace is used. *)
Lemma task_sw_hook_switch_source_current_ready : forall environment sg entry context current returned,
  UCOS2_state_inv sg entry -> UCOS2_state_inv sg current ->
  os_sched_switch_source (task_sw_hook_call_environment environment).(task_stack_call_external)
    sg entry context current ->
  kernel_call_task_source returned current ->
  os_sched_task_current_ready returned current.
Proof.
  intros environment sg entry context current returned Hentry Hcurrent
    [Hswitch [sp [outgoing [hooked [incoming [resumed [Hsave [Hhook [Hdestination Hinstalled]]]]]]]]]
    Hsource.
  change (hooked = os_sched_save_current_sp (os_sched_prefix_state entry)
    context.(os_sched_call_stack).(stackLeaseSlot) sp) in Hhook.
  assert (Hhigh : sched_high_ready_consistency hooked.(TskState) hooked.(SchedState)).
  { rewrite Hhook; apply os_sched_save_sp_preserves_high_consistency.
    change (sched_high_ready_consistency entry.(TskState) (os_sched_ready_checkpoint entry)).
    apply (os_sched_ready_checkpoint_high_consistency sg entry).
    - exact (proj1 (proj1 (proj2 (proj2 Hentry)))).
    - exact (proj1 (proj1 (os_sched_requests_switch_iff entry) Hswitch)). }
  subst current.
  destruct (kernel_call_task_source_current_at returned
    (os_sched_install_context context outgoing incoming hooked) Hsource)
    as [Hcaller_current [caller_node [Hcaller_node Hcaller_generation]]].
  change (hooked.(SchedState).(highRdyTid) = Some returned.(os_sched_call_stack).(stackLeaseSlot))
    in Hcaller_current.
  change (hooked.(TskState).(inUsedTaskStates) returned.(os_sched_call_stack).(stackLeaseSlot) =
    Some caller_node) in Hcaller_node.
  destruct Hdestination as [Hselected [[node [Hnode [Hgeneration [Hpriority Hrestore]]]] Hrest]].
  assert (Hslot : incoming.(stackLeaseSlot) = returned.(os_sched_call_stack).(stackLeaseSlot))
    by congruence.
  rewrite Hslot in Hnode.
  assert (caller_node = node) by congruence; subst caller_node.
  pose proof (proj1 (proj1 (proj1 (proj2 (proj2 Hcurrent))))) as Hready.
  change (forall tid, In tid hooked.(SchedState).(readyList) -> exists t,
    hooked.(TskState).(inUsedTaskStates) tid = Some t /\
    task_priority_in_range sg t.(curPrio) /\
    is_effectively_ready t.(stat) t.(dly) = true) in Hready.
  unfold sched_high_ready_consistency in Hhigh.
  destruct hooked.(SchedState).(readyList) as [|head tail] eqn:Hlist.
  - destruct Hhigh as [Hnone _]; congruence.
  - destruct Hhigh as [Hhead Hhigh_node].
    assert (Hhead_slot : head = returned.(os_sched_call_stack).(stackLeaseSlot)) by congruence.
    destruct (Hready returned.(os_sched_call_stack).(stackLeaseSlot) (or_introl Hhead_slot))
      as [ready_node [Hready_node [_ Heffective]]].
    assert (ready_node = node) by congruence; subst ready_node.
    unfold os_sched_task_current_ready; exists node; split; [|exact Hcaller_generation].
    unfold sched_current_ready_at.
    change (hooked.(TskState).(inUsedTaskStates) returned.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
      hooked.(SchedState).(highRdyTid) = Some returned.(os_sched_call_stack).(stackLeaseSlot) /\
      hooked.(SchedState).(highRdyPrio) = Some node.(curPrio) /\
      In returned.(os_sched_call_stack).(stackLeaseSlot) hooked.(SchedState).(readyList) /\
      is_effectively_ready node.(stat) node.(dly) = true).
    split; [exact Hnode|]. split; [exact Hcaller_current|]. split; [exact Hpriority|].
    split; [rewrite Hlist; left; exact Hhead_slot|exact Heffective].
Qed.

(** The returned world supplies validity at the actual installed endpoint.
    Only the live-task/ready-list projection is used; a closed invariant is
    not retrospectively asserted at an earlier transient C phase. *)
Lemma os_sched_install_current_ready : forall external sg context outgoing hooked incoming resumed returned,
  UCOS2_state_inv sg (os_sched_install_context context outgoing incoming hooked) ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  os_sched_destination_binding external context outgoing hooked incoming resumed ->
  returned.(os_sched_call_stack) = incoming ->
  os_sched_task_current_ready returned (os_sched_install_context context outgoing incoming hooked).
Proof.
  intros external sg context outgoing hooked incoming resumed returned Hvalid Hhigh
    [Hselected [[node [Hnode [Hgeneration [Hpriority Hrestore]]]] Hrest]] Hstack.
  pose proof (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid))))) as Hready.
  change (forall tid, In tid hooked.(SchedState).(readyList) -> exists t,
    hooked.(TskState).(inUsedTaskStates) tid = Some t /\
    task_priority_in_range sg t.(curPrio) /\
    is_effectively_ready t.(stat) t.(dly) = true) in Hready.
  unfold sched_high_ready_consistency in Hhigh.
  destruct hooked.(SchedState).(readyList) as [|slot tail] eqn:Hlist.
  - destruct Hhigh as [Hnone _]; congruence.
  - destruct Hhigh as [Hhead _].
    assert (Hslot : slot = incoming.(stackLeaseSlot)) by congruence.
    assert (Hin : In incoming.(stackLeaseSlot) hooked.(SchedState).(readyList)).
    { rewrite Hlist; left; exact Hslot. }
    destruct (Hready incoming.(stackLeaseSlot) (or_introl Hslot))
      as [ready_node [Hready_node [_ Heffective]]].
    assert (ready_node = node) by congruence; subst ready_node.
    unfold os_sched_task_current_ready; rewrite Hstack; exists node; split; [|exact Hgeneration].
    unfold sched_current_ready_at.
    change (hooked.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node /\
      hooked.(SchedState).(highRdyTid) = Some incoming.(stackLeaseSlot) /\
      hooked.(SchedState).(highRdyPrio) = Some node.(curPrio) /\
      In incoming.(stackLeaseSlot) hooked.(SchedState).(readyList) /\
      is_effectively_ready node.(stat) node.(dly) = true).
    exact (conj Hnode (conj Hselected (conj Hpriority (conj Hin Heffective)))).
Qed.

(** The pinned, checked TaskSwHook is identity.  OSIntExit's real selector
    therefore supplies the high cache used by its final current-cache stores.
    No ready/current property is attributed to the opaque resume relation. *)
Lemma task_sw_hook_irq_transfer_current_ready : forall environment sg handler entry transfer returned,
  os_int_exit_transfer_source
    (task_sw_hook_call_environment environment).(task_stack_call_external)
    (task_sw_hook_call_environment environment).(task_stack_call_port) sg handler entry transfer ->
  UCOS2_state_inv sg (os_int_exit_installed_state transfer) ->
  returned.(os_sched_call_stack) = transfer.(os_int_exit_incoming_stack) ->
  os_sched_task_current_ready returned (os_int_exit_installed_state transfer).
Proof.
  intros environment sg handler entry transfer returned
    [Hswitch [_ [_ [Hhook [Hdestination _]]]]] Hvalid Hstack.
  change (transfer.(os_int_exit_hooked_state) = os_int_exit_ready_checkpoint true entry) in Hhook.
  assert (Hrange : sched_ready_in_range sg
    transfer.(os_int_exit_hooked_state).(TskState)
    transfer.(os_int_exit_hooked_state).(SchedState)).
  { exact (proj1 (proj1 (proj2 (proj2 Hvalid)))). }
  assert (Henabled : os_sched_selection_enabled (os_int_exit_after_nesting entry) = true).
  { change (os_sched_requests_switch (os_int_exit_after_nesting entry) = true) in Hswitch.
    unfold os_sched_requests_switch in Hswitch.
    destruct (os_sched_selection_enabled (os_int_exit_after_nesting entry)) eqn:Henabled;
      [reflexivity|discriminate]. }
  assert (Hhigh : sched_high_ready_consistency
    transfer.(os_int_exit_hooked_state).(TskState)
    transfer.(os_int_exit_hooked_state).(SchedState)).
  { rewrite Hhook in Hrange |- *.
    change (sched_high_ready_consistency (os_int_exit_after_nesting entry).(TskState)
      (os_sched_ready_checkpoint (os_int_exit_after_nesting entry))).
    apply (os_sched_ready_checkpoint_high_consistency sg (os_int_exit_after_nesting entry)); [|exact Henabled].
    change (sched_ready_in_range sg (os_int_exit_after_nesting entry).(TskState)
      (os_sched_ready_checkpoint (os_int_exit_after_nesting entry))) in Hrange.
    unfold sched_ready_in_range in *.
    rewrite (proj1 (os_sched_ready_checkpoint_frame (os_int_exit_after_nesting entry))) in Hrange.
    exact Hrange. }
  destruct Hdestination as [Hselected [[node [Hnode [Hgeneration [Hpriority Hsp]]]] Hrest]].
  pose proof (proj1 Hrange) as Hready.
  unfold sched_high_ready_consistency in Hhigh.
  destruct transfer.(os_int_exit_hooked_state).(SchedState).(readyList) as [|slot tail] eqn:Hlist.
  - destruct Hhigh as [Hnone _]; congruence.
  - destruct Hhigh as [Hhead _].
    assert (Hslot : slot = transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)) by congruence.
    assert (Hin : In transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)
      transfer.(os_int_exit_hooked_state).(SchedState).(readyList)).
    { rewrite Hlist; left; exact Hslot. }
    destruct (Hready transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) (or_introl Hslot))
      as [ready_node [Hready_node [_ Heffective]]].
    assert (ready_node = node) by congruence; subst ready_node.
    unfold os_sched_task_current_ready; rewrite Hstack; exists node; split; [|exact Hgeneration].
    unfold sched_current_ready_at.
    change (transfer.(os_int_exit_hooked_state).(TskState).(inUsedTaskStates)
        transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) = Some node /\
      transfer.(os_int_exit_hooked_state).(SchedState).(highRdyTid) =
        Some transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) /\
      transfer.(os_int_exit_hooked_state).(SchedState).(highRdyPrio) = Some node.(curPrio) /\
      In transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)
        transfer.(os_int_exit_hooked_state).(SchedState).(readyList) /\
      is_effectively_ready node.(stat) node.(dly) = true).
    exact (conj Hnode (conj Hselected (conj Hpriority (conj Hin Heffective)))).
Qed.

Lemma os_sched_task_current_ready_current_consistency : forall call state,
  os_sched_task_current_ready call state ->
  sched_current_consistency state.(TskState) state.(SchedState).
Proof.
  intros call state [node [[Hnode [Hcurrent [Hcache Hrest]]] Hgeneration]].
  unfold sched_current_consistency; rewrite Hcurrent; exists node; auto.
Qed.

Lemma kernel_call_control_rely_trans : forall sg before current after,
  kernel_call_control_rely sg before current -> kernel_call_control_rely sg current after ->
  kernel_call_control_rely sg before after.
Proof. intros sg before current after [Hrun Hints] [Hrun' Hints']; split; congruence. Qed.
End SchedulerReturnFacts.

