(** Report-only ordinary module extracted from the frozen checked C context.
    The original proof bodies are retained under the recorded shared-reference map. *)
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_events_spec.
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
Require Export Ucos2Verify.VC.code.flag.spec.flag_pend_selected_call_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_task_return_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_fields_active_phase_spec.
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

(** The two Task-source facts and the returned cut are the existing
    Scheduler C target's observations of this same call.  Its cache
    consequence is now obtained from this event's selected C execution. *)
Module SchedulerSelectedSave.
Import PrimitiveComponent.

Lemma os_sched_task_save_observation_from_selected_c_event :
  forall environment critical local next_local active sg original mask saved before
    returned_caller returned acquired first_heap last_heap,
  SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event
    environment critical local active sg (FlagPendTaskCaller original) original mask saved before
    returned_caller returned acquired next_local first_heap last_heap ->
  kernel_call_task_source original before ->
  kernel_call_task_source returned acquired ->
  os_sched_call_cut sg returned acquired ->
  SchedulerPhaseCandidate.os_sched_task_save_observation
    environment critical sg original mask saved before returned acquired.
Proof.
  intros environment critical local next_local active sg original mask saved before
    returned_caller returned acquired first_heap last_heap Hpaired Hsource Hreturned Hcut.
  destruct Hpaired as [Hobservation [Hsaved [Hinput [Houtput Hcompleted]]]].
  assert (Hcaller : returned_caller = FlagPendTaskCaller returned).
  { destruct returned_caller as [next|view key].
    - cbn [PendPhaseCandidate.flag_pend_caller_save_observation] in Hobservation.
      destruct Hobservation as [_ [Hnext _]]; subst next; reflexivity.
    - contradiction. }
  subst returned_caller.
  cbn [PendPhaseCandidate.flag_pend_caller_save_observation] in Hobservation.
  destruct Hobservation as [_ [_ [Heffect [Hsame Hpreserved]]]].
  assert (Hactual : SelectedEventSources.flag_pend_selected_event_source environment critical sg
    (flag_pend_task_save_completed_c_event environment critical local next_local active sg
      original mask saved before first_heap returned acquired last_heap)).
  { exact Hcompleted. }
  pose proof (SelectedEventSources.flag_pend_selected_event_source_resources environment critical sg
    (flag_pend_task_save_completed_c_event environment critical local next_local active sg
      original mask saved before first_heap returned acquired last_heap) Hactual)
    as [_ [Hendpoints _]].
  destruct Hendpoints as [Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]].
  assert (Hnonboot : original.(os_sched_call_origin) <> BootInvocation).
  { rewrite (proj1 Hsource); discriminate. }
  specialize (Hcontrol Hnonboot).
  unfold SchedulerPhaseCandidate.os_sched_task_save_observation.
  split; [exact Heffect|]. split; [exact Hsame|]. split; [exact Hsaved|].
  split; [exact Hpreserved|]. split; [exact Hcut|].
  split.
  - intro Hcache.
    eapply SelectedEventSources.flag_pend_selected_save_current_cache;
      [exact Hactual|exact Hsource|exact Hcache|exact Hreturned].
  - split; assumption.
Qed.

End SchedulerSelectedSave.

(** Existing paired Save bridge, now consuming the fixed selected phase event.
    Its entry heap and active subheap remain different explicit indices. *)
Module SchedulerPairedPhaseComponent.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Import PrimitiveComponent PendPhaseCandidate SelectedCallerPhaseComponent.
Import SchedulerActivePhaseComponent SchedulerCalleePhaseComponent SchedulerPhaseCandidate.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The Scheduler supplies the same complete footprint as the paired Save
    declaration, including unmap. Its entry cut facts remain available. *)
Lemma os_sched_active_save_input_implies_caller_input :
  forall environment critical local active sg call mask state,
  os_sched_active_save_input environment critical local active sg call mask state **
    unmap_table_rep sg |--
  coq_prop (os_sched_call_cut sg call state /\ kernel_sched_ready_clients critical) &&
    flag_pend_caller_save_input environment critical local active sg
      (FlagPendTaskCaller call) call mask state.
Proof.
  intros environment critical local active sg call mask state heap
    [active_heap [unmap_heap [Hjoin [[Hfacts Hactive] Hunmap]]]].
  split; [exact Hfacts|].
  split; [reflexivity|].
  exists active_heap, unmap_heap; exact (conj Hjoin (conj Hactive Hunmap)).
Qed.

Lemma os_sched_active_restore_input_state_inv :
  forall environment critical local active sg call saved acquired current,
  os_sched_active_restore_input environment critical local active sg call saved acquired current |--
  coq_prop (UCOS2_state_inv sg current) &&
    os_sched_active_restore_input environment critical local active sg call saved acquired current.
Proof.
  intros; unfold os_sched_active_restore_input, os_sched_fields_restore_input, UCOS2_fields_inv.
  Intros; entailer!.
Qed.

(** This uses the already returned Task endpoint packet. Idle is transported
    as an existing C environment fact; the blocked caller is never made ready.
    Layout and entry availability are explicit existing caller facts whose
    transport into the internal Scheduler interface remains to be wired. *)
Lemma os_sched_paired_save_call_cut_from_endpoints :
  forall environment sg original before returned acquired,
  kernel_tcb_stack_field_layout sg ->
  kernel_call_task_source original before ->
  kernel_call_stack_available original before ->
  task_idle_ready sg before.(TskState) ->
  task_tcb_init_stack_same_call returned original ->
  task_tcb_init_stack_source_preserved original before acquired ->
  flag_pend_call_endpoint_observations environment sg
    (FlagPendTaskCaller original) original before returned acquired ->
  UCOS2_state_inv sg acquired ->
  kernel_call_task_source returned acquired /\ os_sched_call_cut sg returned acquired.
Proof.
  intros environment sg original before returned acquired Hlayout Hsource Havailable
    Hidle Hsame Hpreserved [_ [Hidle_return [_ [Hnormal Hcontrol]]]] Hvalid.
  assert (Hreturned_source : kernel_call_task_source returned acquired).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff returned original acquired Hsame)).
    apply Hpreserved; exact Hsource. }
  split; [exact Hreturned_source|].
  eapply os_sched_call_cut_from_source.
  - exact Hvalid.
  - exact Hreturned_source.
  - eapply sched_idle_ready_nonempty.
    + exact (proj1 (proj1 (proj2 (proj2 Hvalid)))).
    + exact (Hidle_return (conj Hsource Hidle)).
  - exact (proj2 Hnormal Havailable).
  - eapply kernel_call_task_source_stack_field_address; eassumption.
Qed.

(** The same completed Save event supplies both captured heaps. The active
    input subheap is recovered from its original full input, never equated
    with a separately captured snapshot. The exact returned tuple is kept.
    Cache consistency is deliberately not part of this non-cache bridge. *)
Lemma os_sched_caller_save_event_active_event :
  forall environment critical local active sg original mask saved before
    returned_caller returned acquired next_local before_heap after_heap,
  kernel_tcb_stack_field_layout sg ->
  kernel_call_task_source original before ->
  kernel_call_stack_available original before ->
  task_idle_ready sg before.(TskState) ->
  os_sched_call_cut sg original before ->
  kernel_sched_ready_clients critical ->
  SelectedCallerPhaseComponent.flag_pend_selected_caller_save_event environment critical local active sg
    (FlagPendTaskCaller original) original mask saved before
    returned_caller returned acquired next_local before_heap after_heap ->
  exists active_before,
    (os_sched_active_heap_cut
      (os_sched_active_save_input environment critical local active sg original mask before)
      active_before ** unmap_table_rep sg) before_heap /\
    kernel_call_normal_return original before returned acquired /\
    kernel_call_control_rely sg before acquired /\
    kernel_call_task_source returned acquired /\
    os_sched_call_cut sg returned acquired /\
    ((fun active_after => os_sched_active_save_event environment critical local active sg
      original mask saved before returned acquired next_local active_before active_after) **
      unmap_table_rep sg) after_heap.
Proof.
  intros environment critical local active sg original mask saved before
    returned_caller returned acquired next_local before_heap after_heap
    Hlayout Hsource Havailable Hidle Hcut_before Hclients
    [Hobservation [Hsaved [Hbefore [Hafter Hcompleted]]]].
  destruct returned_caller as [next|view key]; [|contradiction].
  destruct Hobservation as [_ [Hnext [Heffect [Hsame Hpreserved]]]]; subst next.
  assert (Hend : flag_pend_call_endpoint_observations environment sg
    (FlagPendTaskCaller original) original before returned acquired).
  { destruct (SelectedEventSources.flag_pend_selected_event_source_resources
      _ _ _ _ Hcompleted) as [_ [Hendpoint_actual _]].
    exact Hendpoint_actual. }
  destruct Hbefore as [_ [active_before [unmap_before [Hjoin_before [Hraw_before Hunmap_before]]]]].
  destruct Hafter as [_ [active_after [unmap_after [Hjoin_after [Hraw_after Hunmap_after]]]]].
  change (os_sched_active_restore_input environment critical next_local active sg
    returned saved acquired acquired active_after) in Hraw_after.
  pose proof (proj1 (os_sched_active_restore_input_state_inv environment critical next_local
    active sg returned saved acquired acquired active_after Hraw_after)) as Hvalid_after.
  destruct (os_sched_paired_save_call_cut_from_endpoints environment sg original before
    returned acquired Hlayout Hsource Havailable Hidle Hsame Hpreserved Hend Hvalid_after)
    as [Hreturned_source Hcut_after].
  destruct Hend as [_ [_ [_ [Hnormal Hcontrol]]]].
  assert (Hnonboot : original.(os_sched_call_origin) <> BootInvocation).
  { rewrite (proj1 Hsource); discriminate. }
  specialize (Hcontrol Hnonboot).
  assert (Hactive_before : os_sched_active_save_input environment critical local active sg
    original mask before active_before).
  { split; [exact (conj Hcut_before Hclients)|exact Hraw_before]. }
  exists active_before; split.
  - exists active_before, unmap_before; split; [exact Hjoin_before|].
    split; [exact (conj eq_refl Hactive_before)|exact Hunmap_before].
  - split; [exact Hnormal|]. split; [exact Hcontrol|].
    split; [exact Hreturned_source|]. split; [exact Hcut_after|].
    exists active_after, unmap_after; split; [exact Hjoin_after|].
    split; [|exact Hunmap_after].
    exact (conj Heffect (conj Hsame (conj Hsaved (conj Hpreserved
      (conj Hcut_after (conj Hactive_before Hraw_after)))))).
Qed.

(** The actual callee Ensure is existential. Open that returned tuple once
    and keep it in the result, together with its original captured input. *)
Lemma os_sched_caller_save_output_active_event :
  forall environment critical local active sg original mask saved before before_heap,
  kernel_tcb_stack_field_layout sg ->
  kernel_call_task_source original before ->
  kernel_call_stack_available original before ->
  task_idle_ready sg before.(TskState) ->
  os_sched_call_cut sg original before ->
  kernel_sched_ready_clients critical ->
  SelectedCallerPhaseComponent.flag_pend_selected_caller_save_output environment critical local active sg
    (FlagPendTaskCaller original) original mask before before_heap saved |--
  EX returned acquired next_local active_before,
    coq_prop (
      (os_sched_active_heap_cut
        (os_sched_active_save_input environment critical local active sg original mask before)
        active_before ** unmap_table_rep sg) before_heap /\
      kernel_call_normal_return original before returned acquired /\
      kernel_call_control_rely sg before acquired /\
      kernel_call_task_source returned acquired /\ os_sched_call_cut sg returned acquired) &&
    ((fun active_after => os_sched_active_save_event environment critical local active sg
      original mask saved before returned acquired next_local active_before active_after) **
      unmap_table_rep sg).
Proof.
  intros environment critical local active sg original mask saved before before_heap
    Hlayout Hsource Havailable Hidle Hcut Hclients after_heap
    [returned_caller [returned [acquired [next_local Hevent]]]].
  destruct (os_sched_caller_save_event_active_event environment critical local active
    sg original mask saved before returned_caller returned acquired next_local before_heap after_heap
    Hlayout Hsource Havailable Hidle Hcut Hclients Hevent)
    as [active_before [Hpre [Hnormal [Hcontrol [Hreturned [Hcut_after Howned]]]]]].
  exists returned, acquired, next_local, active_before; split; [|exact Howned].
  exact (conj Hpre (conj Hnormal (conj Hcontrol (conj Hreturned Hcut_after)))).
Qed.
(** The concrete Pend active resource already owns Idle-ready at the current
    state; extracting it imposes no ready condition on the blocked waiter. *)
Lemma os_sched_wait_active_save_input_idle_ready :
  forall environment critical local sg waiter node call mask state,
  os_sched_active_save_input environment critical local
    (PendPhaseCandidate.flag_pend_wait_active sg waiter node) sg call mask state ** unmap_table_rep sg |--
  coq_prop (task_idle_ready sg state.(TskState)) &&
  (os_sched_active_save_input environment critical local
    (PendPhaseCandidate.flag_pend_wait_active sg waiter node) sg call mask state ** unmap_table_rep sg).
Proof.
  intros; unfold os_sched_active_save_input, PendPhaseCandidate.flag_pend_wait_active.
  Intros; entailer!.
Qed.


(** A name for the first pure consequence of the checked event bridge.
    entry_heap is the complete captured input; active_before is its active
    subheap, alongside the original unmap ownership. *)
Definition os_sched_paired_save_entry_heap environment critical local active
  sg original mask before entry_heap active_before : Prop :=
  (os_sched_active_heap_cut
     (os_sched_active_save_input environment critical local active
       sg original mask before) active_before ** unmap_table_rep sg) entry_heap.

End SchedulerPairedPhaseComponent.

Module SchedulerRestorePhaseComponent.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Import PrimitiveComponent PendPhaseCandidate SelectedCallerPhaseComponent.
Import SchedulerActivePhaseComponent SchedulerCalleePhaseComponent SchedulerPhaseCandidate.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Append after the shared flag_pend_spec declarations and import the
    report direct-ready Scheduler contract.  This consumes the actual
    paired C Restore event.  Both unmap pieces are obtained by splitting
    its own h0/h1, not by joining unrelated existential observations. *)
Lemma flag_pend_completed_restore_sched_output : forall environment critical local active sg
  original saved acquired released before_heap,
  kernel_call_task_source original released ->
  os_sched_task_current_ready original released ->
  SelectedCallerPhaseComponent.flag_pend_selected_caller_restore_output environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired released before_heap |--
  EX active_before,
    coq_prop (exists unmap_before,
      join active_before unmap_before before_heap /\ unmap_table_rep sg unmap_before) &&
    (os_sched_task_restore_output environment critical local active sg original saved acquired released
      active_before ** unmap_table_rep sg).
Proof.
  intros environment critical local active sg original saved acquired released before_heap
    Hsource Hready after_heap
    [returned_caller [returned [current [next_local [Hobservation [Hbefore [Hafter Hcompleted]]]]]]].
  destruct returned_caller as [next|view key].
  2: contradiction.
  cbn [flag_pend_caller_restore_observation] in Hobservation.
  destruct Hobservation as [_ [Hnext [Heffect [Hsame [Hpreserved Htransport]]]]].
  subst next.
  assert (Hendpoint : flag_pend_call_endpoint_observations environment sg
    (FlagPendTaskCaller original) original released returned current).
  { destruct (SelectedEventSources.flag_pend_selected_event_source_resources
      _ _ _ _ Hcompleted) as [_ [Hendpoint_actual _]].
    exact Hendpoint_actual. }
  destruct Hendpoint as [Hready_after [Hidle [Hnonidle [Hnormal Hcontrol]]]].
  assert (Hnonboot : original.(os_sched_call_origin) <> BootInvocation).
  { rewrite (proj1 Hsource); discriminate. }
  specialize (Hcontrol Hnonboot).
  assert (Hcurrent_ready : os_sched_task_current_ready returned current).
  { apply Hready_after; split; assumption. }
  cbn [flag_pend_caller_restore_input] in Hbefore.
  destruct Hbefore as [_ [active_before [unmap_before [Hjoin_before [Howned_before Hunmap_before]]]]].
  cbn [flag_pend_caller_save_input] in Hafter.
  destruct Hafter as [_ [active_after [unmap_after [Hjoin_after [Howned_after Hunmap_after]]]]].
  exists active_before; split.
  - exists unmap_before; split; assumption.
  - exists active_after, unmap_after; split; [exact Hjoin_after|]; split; [|exact Hunmap_after].
    eapply os_sched_task_restore_output_from_current_ready; try eassumption.
    exact (conj Heffect (conj Hsame (conj (Hpreserved Hsource)
      (conj Htransport (conj Howned_before Howned_after))))).
Qed.

(** C call-site consequences of the existing paired Restore contract.
    The full before heap includes unmap, exactly as the shared callee does. *)
Lemma os_sched_task_restore_input_implies_caller_input :
  forall environment critical local active sg call saved acquired released,
  os_sched_task_restore_input environment critical local active sg call saved acquired released **
    unmap_table_rep sg |--
  coq_prop (os_sched_task_current_ready call released) &&
    flag_pend_caller_restore_input environment critical local active sg
      (FlagPendTaskCaller call) call saved acquired released.
Proof.
  intros environment critical local active sg call saved acquired released heap
    [active_heap [unmap_heap [Hjoin [[Hready Hactive] Hunmap]]]].
  split; [exact Hready|].
  split; [reflexivity|].
  exists active_heap, unmap_heap; exact (conj Hjoin (conj Hactive Hunmap)).
Qed.

(** The final C call consumes the SAME saved/body observations and produces
    the public Scheduler history post. No independently chosen active-before
    heap is identified with the shared callee's full captured heap. *)
Lemma os_sched_task_caller_restore_output_implies_history_return_post :
  forall environment critical local active sg original scheduled resumed
    mask saved before entry released before_heap,
  kernel_call_task_source scheduled entry ->
  os_sched_task_save_observation environment critical sg original mask saved before scheduled entry ->
  os_sched_task_body_observation environment critical sg scheduled entry resumed released ->
  UCOS2_state_inv sg released ->
  SelectedCallerPhaseComponent.flag_pend_selected_caller_restore_output environment critical local active sg
    (FlagPendTaskCaller resumed) resumed saved entry released before_heap |--
  os_sched_task_history_return_post environment critical active sg original mask before.
Proof.
  intros environment critical local active sg original scheduled resumed
    mask saved before entry released before_heap Hsource Hsave Hbody Hvalid heap Hrestore.
  destruct Hbody as [Hbody_source [Hready [Hnormal [Hcontrol Htransport]]]].
  assert (Hbody : os_sched_task_body_observation environment critical sg scheduled entry resumed released).
  { exact (conj Hbody_source (conj Hready (conj Hnormal (conj Hcontrol Htransport)))). }
  destruct (flag_pend_completed_restore_sched_output environment critical local active sg
    resumed saved entry released before_heap (Htransport Hsource) Hready heap Hrestore)
    as [active_before [Hsplit Hpost]].
  exact (os_sched_task_restore_output_return environment critical local active sg original
    scheduled resumed mask saved before entry released active_before Hsave Hbody Hvalid heap Hpost).
Qed.

End SchedulerRestorePhaseComponent.
