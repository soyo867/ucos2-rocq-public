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
Require Export Ucos2Verify.VC.code.sched.spec.sched_continuation_phase_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_return_facts_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_legacy_prefix_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Instantiate the TaskDel composite with the concrete program union.
    Both syntactic inclusions are discharged by its actual constructors.
    The original two captured sources, local frames and five heaps remain
    those of the checked body producer. *)
Import DeleteComponent CriticalComponent.

(** This is a fixed C interpretation, not a law asserted about an arbitrary
    old linked predicate.  Its producer must supply the same actual C run;
    the raw endpoint observations are part of that run's original output. *)
Import CriticalComponent PrimitiveComponent.

(** The selected source has a concrete interpretation for each original
    caller kind.  Task execution uses the proved C program.  IRQ execution
    additionally admits the already explicit view primitive contract; that
    contract is not promoted to a Task cache-preservation law. *)
Import CriticalComponent PrimitiveComponent.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
(** Sources decorate the original C completion proof.  They retain the
    invocation/allocation from that completion; no constructor assumes any
    creation-frame, cache, ready or future-return conclusion. *)
Import EventStateDef.
Import EventStateDef.












(** Provenance follows the existing execution proof.  An atomic marker is
    supplied by that C module's actual call/allocation protocol.  In
    particular, it may retain a foreign invocation condition; it is not a
    second execution picked for its endpoints. *)
Import CriticalComponent.



(** A selected environment is an actual sequence of the fixed C program.
    Its existing return owner contains the original C endpoint contract.
    The ABI suffix/prefix below is composed with that very sequence; there
    is no independently supplied old source or endpoint-equal replacement
    tree.  State, caller, local resources and heaps may all change in the
    environment.  Its stopped bit is retained, not assumed false. *)
Import PrimitiveComponent.
Module SchedulerPhaseCandidate.
Import CriticalComponent SelectedCProgram SelectedCSource.




























Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** These are observations of a completed source segment.  The normal and
    control parts are the existing paired C-call contract, not new ARM ABI
    fields.  Current consistency is obtained from the concrete source edges
    of sched_current_source_spec, which include priority-changing writers. *)
Definition os_sched_task_save_observation environment critical sg original mask saved before returned acquired : Prop :=
  ContinuationPhaseEffects.os_sched_continuation_phase_save_effect environment critical sg original mask saved before returned acquired /\
  task_tcb_init_stack_same_call returned original /\ interrupt_saved_value mask saved /\
  task_tcb_init_stack_source_preserved original before acquired /\ os_sched_call_cut sg returned acquired /\
  (sched_current_consistency before.(TskState) before.(SchedState) ->
    sched_current_consistency acquired.(TskState) acquired.(SchedState)) /\
  kernel_call_normal_return original before returned acquired /\ kernel_call_control_rely sg before acquired.


(** The previous closed-client outcomes remain represented.  A new phase
    outcome retains the actual heap-indexed resource cut of its completed
    C prefix.  The callee contract separately returns the same call/state
    tuple with its actual endpoint ownership; no instruction read or
    physical restore witness is required by this C program.
    The compatibility constructor does not classify arbitrary registered
    clients as phase sources or certify completeness of the dispatcher. *)
Inductive os_sched_task_return_prefix (environment : TaskStackCallEnvironment)
  (critical : CriticalRegionResources) sg observer :
  UCOS2_Verify_State -> UCOS2_Verify_State -> model -> Prop :=
| OsSchedTaskReturnPrefixLegacy : forall before current final_heap,
    LegacyTaskReturnPrefix.os_sched_task_return_prefix environment critical sg observer before current final_heap ->
    os_sched_task_return_prefix environment critical sg observer before current final_heap
| OsSchedTaskReturnPrefixCSequence : forall origin event_observer state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      state before input stopped current after output),
    kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
      state before input stopped current after output run ->
    os_sched_task_return_prefix environment critical sg observer state current after.

Lemma os_sched_task_c_sequence_prefix :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      state before input stopped current after output),
  kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    state before input stopped current after output run ->
  os_sched_task_return_prefix environment critical sg observer state current after.
Proof. intros; eapply OsSchedTaskReturnPrefixCSequence; exact H. Qed.

Definition os_sched_task_irq_return_prefix environment critical sg observer before current : Prop :=
  kernel_client_trace critical.(critical_region_clients) sg observer before false current \/
  exists final_heap, os_sched_task_return_prefix environment critical sg observer before current final_heap.


(** These retain the existing callable legacy constructor interfaces.
    Their old source proofs are injected without constructing a C run. *)
Lemma OsSchedTaskReturnPrefixClients : forall environment critical sg observer before after final_heap,
  kernel_client_trace critical.(critical_region_clients) sg observer before false after ->
  os_sched_task_return_prefix environment critical sg observer before after final_heap.
Proof.
  intros; apply OsSchedTaskReturnPrefixLegacy.
  apply LegacyTaskReturnPrefix.OsSchedTaskReturnPrefixClients; assumption.
Qed.

Lemma OsSchedTaskReturnPrefixPhases : forall environment critical sg observer before initial_heap after final_heap,
  sched_task_phase_heap_source environment critical sg before initial_heap after final_heap ->
  os_sched_task_return_prefix environment critical sg observer before after final_heap.
Proof.
  intros; apply OsSchedTaskReturnPrefixLegacy.
  eapply LegacyTaskReturnPrefix.OsSchedTaskReturnPrefixPhases; eassumption.
Qed.


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


(** C-function source branches.  The final state is the actual selected
    C install or interrupt-exit transfer.  The port supplies normal-call
    identity through its already selected abstract contract; instruction
    reads and physical restore transitions are sufficient implementations
    of these branches, not additional witnesses required by this program.

    The phase prefix keeps its actual C resource cut.  This declaration
    does not derive it, current readiness, or endpoint control from an
    arbitrary old registered trace. *)
Inductive os_sched_task_body_source (environment : TaskStackCallEnvironment) critical sg :
  UCOS2_Verify_State -> OsSchedCallContext -> OsSchedCallContext -> UCOS2_Verify_State -> Prop :=
| OsSchedTaskBodyNoSwitch : forall entry original,
    os_sched_requests_switch entry = false ->
    os_sched_task_body_source environment critical sg entry original original (os_sched_prefix_state entry)
| OsSchedTaskBodyTaskLastInstall : forall
    entry original first_installed context outgoing hooked resumed returned before_heap,
    os_sched_switch_source environment.(task_stack_call_external) sg entry original first_installed ->
    os_sched_task_return_prefix environment critical sg original.(os_sched_call_invocation)
      first_installed hooked before_heap ->
    kernel_client_stops environment.(task_stack_call_external).(os_sched_hook_action)
      original.(os_sched_call_invocation) = false ->
    os_sched_saved_stack_binding context outgoing hooked ->
    os_sched_destination_binding environment.(task_stack_call_external)
      context outgoing hooked original.(os_sched_call_stack) resumed ->
    sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
    task_tcb_init_stack_same_call returned original ->
    os_sched_task_body_source environment critical sg entry original returned
      (os_sched_install_context context outgoing original.(os_sched_call_stack) hooked)
| OsSchedTaskBodyIRQLastInstall : forall entry original first_installed handler irq_entry transfer returned,
    os_sched_switch_source environment.(task_stack_call_external) sg entry original first_installed ->
    os_sched_task_irq_return_prefix environment critical sg original.(os_sched_call_invocation)
      first_installed irq_entry ->
    kernel_client_stops environment.(task_stack_call_external).(os_sched_hook_action)
      original.(os_sched_call_invocation) = false ->
    os_int_exit_transfer_source environment.(task_stack_call_external) environment.(task_stack_call_port)
      sg handler irq_entry transfer ->
    transfer.(os_int_exit_incoming_stack) = original.(os_sched_call_stack) ->
    task_tcb_init_stack_same_call returned original ->
    os_sched_task_body_source environment critical sg entry original returned
      (os_int_exit_installed_state transfer)
| OsSchedTaskBodyTaskLastCall : forall entry original first_installed last_entry
    last_context returned current last_entry_heap,
    os_sched_switch_source environment.(task_stack_call_external) sg entry original first_installed ->
    os_sched_task_return_prefix environment critical sg original.(os_sched_call_invocation)
      first_installed last_entry last_entry_heap ->
    UCOS2_state_inv sg last_entry ->
    os_sched_switch_source environment.(task_stack_call_external) sg last_entry last_context current ->
    task_tcb_init_stack_same_call returned original ->
    kernel_call_task_source returned current ->
    os_sched_task_body_source environment critical sg entry original returned current.

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

Lemma os_sched_task_body_source_current_ready : forall environment critical sg entry original returned current,
  UCOS2_state_inv sg entry -> UCOS2_state_inv sg current ->
  kernel_call_task_source original entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  os_sched_selection_enabled entry = true -> os_sched_call_cut sg original entry ->
  os_sched_task_body_source (task_sw_hook_call_environment environment)
    critical sg entry original returned current ->
  os_sched_task_current_ready returned current.
Proof.
  intros environment critical sg entry original returned current Hentry Hcurrent Hsource Hconsistent Henabled Hcut Hbody.
  destruct Hbody.
  - apply (os_sched_task_ready_source_current_ready (task_sw_hook_call_environment environment) sg).
    apply OsSchedTaskReadyPrefix; eapply OsSchedTaskReadyNonswitch; try eassumption.
    apply (proj1 Hcut); exact Henabled.
  - eapply SchedulerReturnFacts.os_sched_install_current_ready; try eassumption.
    exact (proj2 (proj2 H5)).
  - eapply SchedulerReturnFacts.task_sw_hook_irq_transfer_current_ready; try eassumption.
    rewrite (proj2 (proj2 H4)); symmetry; exact H3.
  - eapply SchedulerReturnFacts.task_sw_hook_switch_source_current_ready; eassumption.
Qed.

Lemma os_sched_task_current_ready_current_consistency : forall call state,
  os_sched_task_current_ready call state ->
  sched_current_consistency state.(TskState) state.(SchedState).
Proof.
  intros call state [node [[Hnode [Hcurrent [Hcache Hrest]]] Hgeneration]].
  unfold sched_current_consistency; rewrite Hcurrent; exists node; auto.
Qed.

(** The actual OSCtxSw call has already taken the C switch guard.  Its
    returned world, final C source and fixed hook suffice for readiness;
    no entry invariant or independent ready label is added to this leaf. *)
Lemma os_sched_task_switch_source_current_ready : forall environment critical sg entry original returned current,
  os_sched_requests_switch entry = true -> UCOS2_state_inv sg current ->
  os_sched_task_body_source (task_sw_hook_call_environment environment)
    critical sg entry original returned current -> os_sched_task_current_ready returned current.
Proof.
  intros environment critical sg entry original returned current Hrequest Hvalid Hbody; destruct Hbody.
  - congruence.
  - eapply SchedulerReturnFacts.os_sched_install_current_ready; try eassumption.
    exact (proj2 (proj2 H5)).
  - eapply SchedulerReturnFacts.task_sw_hook_irq_transfer_current_ready; try eassumption.
    rewrite (proj2 (proj2 H4)); symmetry; exact H3.
  - eapply SchedulerReturnFacts.task_sw_hook_switch_source_current_ready; eassumption.
Qed.

Definition os_sched_task_body_observation environment critical sg call entry returned current : Prop :=
  os_sched_task_body_source environment critical sg entry call returned current /\
  os_sched_task_current_ready returned current /\
  kernel_call_normal_return call entry returned current /\ kernel_call_control_rely sg entry current /\
  (kernel_call_task_source call entry -> kernel_call_task_source returned current).

Definition os_sched_task_call_history environment critical sg original mask before returned current : Prop :=
  exists scheduled entry resumed released saved,
    ContinuationPhaseEffects.os_sched_continuation_phase_save_effect environment critical sg original mask saved before scheduled entry /\
    os_sched_task_body_source environment critical sg entry scheduled resumed released /\
    ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect environment critical sg resumed released returned current.

Definition os_sched_task_body_program environment critical sg scheduled :
  program UCOS2_Verify_State OsSchedCallContext :=
  fun entry resumed released => os_sched_task_body_source environment critical sg entry scheduled resumed released.

Definition os_sched_task_program environment critical sg original mask :
  program UCOS2_Verify_State OsSchedCallContext :=
  StateRelMonad.bind (ContinuationPhaseEffects.os_sched_continuation_phase_save_program environment critical sg original mask)
    (fun entered => StateRelMonad.bind (os_sched_task_body_program environment critical sg (fst entered))
      (fun resumed => ContinuationPhaseEffects.os_sched_continuation_phase_restore_program environment critical sg resumed)).

Lemma os_sched_task_program_iff : forall environment critical sg original mask before returned current,
  os_sched_task_program environment critical sg original mask before returned current <->
  os_sched_task_call_history environment critical sg original mask before returned current.
Proof.
  intros; unfold os_sched_task_program, ContinuationPhaseEffects.os_sched_continuation_phase_save_program,
    os_sched_task_body_program, ContinuationPhaseEffects.os_sched_continuation_phase_restore_program,
    os_sched_task_call_history, StateRelMonad.bind.
  split.
  - intros [[scheduled saved] [entry [Hsave [resumed [released [Hbody Hrestore]]]]]].
    exists scheduled, entry, resumed, released, saved; exact (conj Hsave (conj Hbody Hrestore)).
  - intros [scheduled [entry [resumed [released [saved [Hsave [Hbody Hrestore]]]]]]].
    exists (scheduled, saved), entry; split; [exact Hsave|].
    exists resumed, released; split; assumption.
Qed.

(** Compatibility is stated only for an actual classified source.
    A broad old returning relation alone does not identify its last install. *)
Lemma os_sched_task_nonswitch_source_is_c_return : forall environment critical sg entry original,
  os_sched_requests_switch entry = false ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry original original
    (os_sched_prefix_state entry).
Proof. intros; unfold os_sched_c_return; rewrite H; auto. Qed.

Definition os_sched_task_restore_observation environment critical sg original released returned current : Prop :=
  ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect environment critical sg original released returned current /\
  task_tcb_init_stack_same_call returned original /\
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released current /\
  (UCOS2_state_inv sg released -> task_tcb_init_stack_source_preserved original released current) /\
  os_sched_task_current_ready returned current /\
  kernel_call_normal_return original released returned current /\ kernel_call_control_rely sg released current.

Lemma kernel_call_control_rely_trans : forall sg before current after,
  kernel_call_control_rely sg before current -> kernel_call_control_rely sg current after ->
  kernel_call_control_rely sg before after.
Proof. intros sg before current after [Hrun Hints] [Hrun' Hints']; split; congruence. Qed.

Lemma os_sched_task_save_preserves_entry : forall environment critical sg original mask saved before returned acquired,
  os_sched_task_save_observation environment critical sg original mask saved before returned acquired ->
  kernel_call_task_source original before ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  os_sched_selection_enabled before = true ->
  kernel_call_task_source returned acquired /\
  sched_current_consistency acquired.(TskState) acquired.(SchedState) /\
  os_sched_selection_enabled acquired = true.
Proof.
  intros environment critical sg original mask saved before returned acquired
    [Heffect [Hsame [Hsaved [Hsource [Hcut [Htrace [Hnormal [Hrunning Hints]]]]]]]]
    Hinitial Hcurrent Henabled.
  split.
  - apply (proj2 (task_tcb_init_stack_same_call_source_iff returned original acquired Hsame)).
    apply Hsource; exact Hinitial.
  - split.
    + apply Htrace; exact Hcurrent.
    + unfold os_sched_selection_enabled in *; rewrite Hints; exact Henabled.
Qed.

(** Constructed at the actual equal-priority branch of the C body.  The
    selector result and guards are current observations; no ready caller is
    required on entry. *)
Lemma os_sched_task_nonswitch_body_observation : forall environment critical sg call entry,
  UCOS2_state_inv sg entry -> kernel_call_task_source call entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  os_sched_selection_enabled entry = true -> os_sched_requests_switch entry = false ->
  entry.(SchedState).(readyList) <> [] ->
  os_sched_task_body_observation environment critical sg call entry call (os_sched_prefix_state entry).
Proof.
  intros environment critical sg call entry Hvalid Hsource Hcurrent Henabled Hnoswitch Hnonempty.
  split; [apply OsSchedTaskBodyNoSwitch; exact Hnoswitch|].
  split.
  - apply (os_sched_task_ready_source_current_ready environment sg).
    apply OsSchedTaskReadyPrefix; eapply OsSchedTaskReadyNonswitch; eassumption.
  - split; [apply os_sched_prefix_normal_return|].
    split; [apply os_sched_prefix_control_rely|apply os_sched_prefix_preserves_task_source].
Qed.

(** The actual selected leaf supplies the final source and descriptor.
    This helper adds endpoint properties from that same destination binding;
    the body source itself is produced by the actual restore below. *)
Lemma os_sched_task_selected_body_observation : forall environment critical sg original entry
  context outgoing hooked incoming resumed returned,
  UCOS2_state_inv sg hooked ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  os_sched_destination_binding environment.(task_stack_call_external)
    context outgoing hooked incoming resumed ->
  returned.(os_sched_call_stack) = incoming ->
  kernel_call_task_source returned (os_sched_install_context context outgoing incoming hooked) ->
  task_tcb_init_stack_same_call returned original ->
  kernel_call_control_rely sg entry hooked ->
  os_sched_task_body_source environment critical sg entry original returned
    (os_sched_install_context context outgoing incoming hooked) ->
  os_sched_task_body_observation environment critical sg original entry returned
    (os_sched_install_context context outgoing incoming hooked).
Proof.
  intros environment critical sg original entry context outgoing hooked incoming resumed returned
    Hvalid Hhigh Hdestination Hstack Hsource Hsame Hcontrol Hbody.
  split; [exact Hbody|]. split.
  - apply (os_sched_task_ready_source_current_ready environment sg).
    eapply OsSchedTaskReadySelected; eassumption.
  - split.
    + split; [exact Hsame|]. intro Havailable.
      unfold kernel_call_stack_available; rewrite (proj1 Hsource), Hstack; apply task_stack_take_lookup.
    + split; [exact Hcontrol|intros; exact Hsource].
Qed.

(** A returning switch has a real first transfer and a registered interval
    ending at this actual restored invocation.  The selected descriptor's
    resume source supplies the port observation; the C return relation is
    constructed here, rather than assumed from a stronger callee post. *)
Lemma os_sched_task_switch_return_from_source : forall external critical sg entry original
  installed returned current,
  os_sched_switch_source external sg entry original installed ->
  kernel_client_trace critical.(critical_region_clients) sg original.(os_sched_call_invocation)
    installed false current ->
  kernel_client_stops external.(os_sched_hook_action) original.(os_sched_call_invocation) = false ->
  external.(os_sched_arch_resume_source) original returned ->
  task_tcb_init_stack_same_call returned original ->
  kernel_call_task_source returned current ->
  kernel_call_stack_available returned current ->
  os_sched_c_return external critical sg entry original returned current.
Proof.
  intros external critical sg entry original installed returned current
    Hfirst Htrace Hhook Hresume Hsame Hsource Havailable.
  unfold os_sched_c_return; rewrite (proj1 Hfirst).
  exists installed; split; [exact Hfirst|].
  split.
  - exists false; split; [exact Htrace|rewrite Hhook; reflexivity].
  - split; [exact Hresume|].
    destruct Hsame as [Hinv [Horigin Hstack]].
    split; [exact Hinv|]. split; [exact Horigin|]. split; [exact Hstack|].
    split.
    + rewrite <- Hinv, <- Horigin; exact (proj1 (proj2 Hsource)).
    + split.
      * rewrite <- Hstack; exact (proj1 (kernel_call_task_source_current_at returned current Hsource)).
      * unfold kernel_call_stack_available in Havailable.
        rewrite (proj1 Hsource) in Havailable.
        rewrite <- Hstack; exact Havailable.
Qed.

Lemma os_sched_task_client_trace_trans : forall clients sg observer before middle after,
  kernel_client_trace clients sg observer before false middle ->
  kernel_client_trace clients sg observer middle false after ->
  kernel_client_trace clients sg observer before false after.
Proof.
  intros clients sg observer before middle after Hfirst Hlast.
  assert (Hjoin : forall initial stopped final,
      kernel_client_trace clients sg observer initial stopped final -> stopped = false ->
      kernel_client_trace clients sg observer final false after ->
      kernel_client_trace clients sg observer initial false after).
  { intros initial stopped final Htrace; induction Htrace; intros Hstop Htail.
    - exact Htail.
    - apply Bool.orb_false_iff in Hstop; destruct Hstop as [Hfirst_stop Hrest_stop].
      replace false with (orb (kernel_client_stops action observer) false)
        by (rewrite Hfirst_stop; reflexivity).
      eapply KernelClientTraceStep; try eassumption.
      apply IHHtrace; assumption. }
  exact (Hjoin before false middle Hfirst eq_refl Hlast).
Qed.

Lemma os_sched_task_selected_body_from_source : forall environment critical
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg original entry first_installed context outgoing hooked resumed selected before installed restored,
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  let returned := kernel_selected_call selected current in
  os_sched_switch_source environment.(task_stack_call_external) sg entry original first_installed ->
  os_sched_task_return_prefix environment critical sg original.(os_sched_call_invocation)
    first_installed hooked before ->
  kernel_client_stops environment.(task_stack_call_external).(os_sched_hook_action)
    original.(os_sched_call_invocation) = false ->
  UCOS2_state_inv sg hooked ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding environment.(task_stack_call_external)
    context outgoing hooked original.(os_sched_call_stack) resumed ->
  selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) ->
  selected.(armv7a_continuation_call) = Some original ->
  sched_install_heap_fragment sg before installed
    (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) ->
  armv7a_continuation_restore_reads selected installed ->
  armv7a_task_restore_transition task_abi context selected installed restored ->
  kernel_call_task_source returned current ->
  task_tcb_init_stack_same_call returned original ->
  kernel_call_control_rely sg entry hooked ->
  os_sched_task_body_observation environment critical sg original entry returned current.
Proof.
  intros environment critical task_abi sg original entry first_installed context outgoing hooked resumed
    selected before installed restored current returned Hfirst Htrace Hhook Hvalid Hhigh Hsaved Hdestination
    Hlease Hcall Hinstall Hreads Hrestore Hsource Hsame Hcontrol.
  unfold current; eapply os_sched_task_selected_body_observation; try eassumption.
  - exact (proj2 (proj2 Hsame)).
  - unfold returned, current; eapply OsSchedTaskBodyTaskLastInstall; eassumption.
Qed.

Lemma os_sched_task_observations_compose : forall environment critical sg
  original scheduled resumed returned mask saved before entry released current,
  os_sched_task_save_observation environment critical sg original mask saved before scheduled entry ->
  os_sched_task_body_observation environment critical sg scheduled entry resumed released ->
  os_sched_task_restore_observation environment critical sg resumed released returned current ->
  UCOS2_state_inv sg released ->
  os_sched_task_call_history environment critical sg original mask before returned current /\
  task_tcb_init_stack_same_call returned original /\
  (kernel_call_task_source original before -> kernel_call_task_source returned current) /\
  os_sched_task_current_ready returned current /\
  kernel_call_normal_return original before returned current /\ kernel_call_control_rely sg before current.
Proof.
  intros environment critical sg original scheduled resumed returned mask saved before entry released current
    [Hsave [Hscheduled [Hsaved [Hentry_source [Hcut [Hcurrent [Hsave_normal Hsave_control]]]]]]]
    [Hbody [Hbody_ready [Hbody_normal [Hbody_control Hbody_source]]]]
    [Hrestore [Hreturned [Hpreserved [Hsource [Hready [Hrestore_normal Hrestore_control]]]]]] Hvalid.
  assert (Hhistory : os_sched_task_call_history environment critical sg original mask before returned current).
  { exists scheduled, entry, resumed, released, saved; auto. }
  assert (Hsame : task_tcb_init_stack_same_call returned original).
  { destruct Hbody_normal as [Hmiddle Havailability].
    unfold task_tcb_init_stack_same_call in *; intuition congruence. }
  split; [exact Hhistory|]. split; [exact Hsame|]. split.
  - intro Hinitial.
    assert (Hscheduled_source : kernel_call_task_source scheduled entry).
    { apply (proj2 (task_tcb_init_stack_same_call_source_iff scheduled original entry Hscheduled)).
      apply Hentry_source; exact Hinitial. }
    assert (Hreleased : kernel_call_task_source resumed released).
    { apply Hbody_source; exact Hscheduled_source. }
    apply (proj2 (task_tcb_init_stack_same_call_source_iff returned resumed current Hreturned)).
    exact (Hsource Hvalid Hreleased).
  - split; [exact Hready|]. split.
    + eapply kernel_call_normal_return_trans; [exact Hsave_normal|].
      eapply kernel_call_normal_return_trans; eassumption.
    + eapply kernel_call_control_rely_trans; [exact Hsave_control|].
      eapply kernel_call_control_rely_trans; eassumption.
Qed.

(** Publicly consumable result of the strengthened C proof.  There is no
    caller-selected event predicate with only an elimination law.  The C
    proof constructs the three observations above from its actual callee
    returns, preserving one returned/current/world/active tuple. *)
Definition os_sched_task_history_return_post environment critical active sg original mask before : Assertion :=
  EX returned current next_local,
    coq_prop (os_sched_task_call_history environment critical sg original mask before returned current /\
      task_tcb_init_stack_same_call returned original /\
      (kernel_call_task_source original before -> kernel_call_task_source returned current) /\
      os_sched_task_current_ready returned current /\
      kernel_call_normal_return original before returned current /\ kernel_call_control_rely sg before current) &&
    (kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_fields_inv
      next_local sg (task_stack_call_active_key returned) returned mask current ** active returned current).

Lemma os_sched_task_history_return_safeexec : forall environment critical sg original mask before returned current
  (X : OsSchedCallContext -> UCOS2_Verify_State -> Prop),
  os_sched_task_call_history environment critical sg original mask before returned current ->
  safeExec (fun state => state = before)
    (os_sched_task_program environment critical sg original mask) X ->
  safeExec (fun state => state = current) (StateRelMonad.ret returned) X.
Proof.
  intros environment critical sg original mask before returned current X Hhistory Hsafe.
  eapply (highstependret_derive (os_sched_task_program environment critical sg original mask)
    (fun state => state = before) returned (fun _ state => state = current)).
  - intros state Hstate; subst state; exists current; split.
    + apply os_sched_task_program_iff; exact Hhistory.
    + reflexivity.
  - exact Hsafe.
Qed.

Lemma os_sched_task_body_return_safeexec :
  forall environment critical sg original entry returned current
    (X : OsSchedCallContext -> UCOS2_Verify_State -> Prop),
  os_sched_task_body_source environment critical sg entry original returned current ->
  safeExec (fun state => state = entry) (os_sched_task_body_program environment critical sg original) X ->
  safeExec (fun state => state = current) (StateRelMonad.ret returned) X.
Proof.
  intros environment critical sg original entry returned current X Hbody Hsafe.
  eapply (highstependret_derive (os_sched_task_body_program environment critical sg original)
    (fun state => state = entry) returned (fun _ state => state = current)).
  - intros state Hstate; subst state; exists current; split; [exact Hbody|reflexivity].
  - exact Hsafe.
Qed.

End SchedulerPhaseCandidate.
