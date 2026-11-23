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
Require Export Ucos2Verify.VC.code.task.spec.task_del_c_segment_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


Module SelectedDeleteIdle.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import DeleteComponent PrimitiveComponent SelectedIdleFrames.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma task_delete_prepare_single_wait_idle_non_idle :
  forall sg call entry tid old prepared loan,
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  task_delete_prepare_single_wait entry tid old = Some (prepared, loan) ->
  (task_idle_ready sg entry.(TskState) -> task_idle_ready sg prepared.(TskState)) /\
  (flag_pend_non_idle_at sg call entry -> flag_pend_non_idle_at sg call prepared).
Proof.
  intros sg call entry tid old prepared loan Hold Hprepare.
  destruct (task_delete_prepare_single_wait_frame _ _ _ _ _ Hprepare)
    as [updated [Hstate [Hpriority [Hstatus [Hid [Hgen Hsp]]]]]].
  pose proof (proj2 (task_delete_preparation_task_projections__release_and_recycle_resources
    _ _ _ _ _ Hprepare)) as Hprepared.
  rewrite Hstate in Hprepared.
  change ((if Z.eqb tid tid then Some updated else entry.(TskState).(inUsedTaskStates) tid) =
    Some (task_delete_prepared_node old)) in Hprepared.
  rewrite Z.eqb_refl in Hprepared; injection Hprepared as Hupdated; subst updated.
  split.
  - rewrite Hstate; cbn [replace_FlagS replace_EventS replace_SchedS replace_TskS TskState].
    eapply task_update_ready_preserves_idle_ready;
      [exact Hold|reflexivity|intros; reflexivity].
  - apply task_used_priority_transport_non_idle.
    rewrite Hstate; cbn [replace_FlagS replace_EventS replace_SchedS replace_TskS TskState].
    eapply task_update_used_priority_transport; [exact Hold|reflexivity|reflexivity].
Qed.

Lemma task_delete_cut_non_idle : forall sg observed prepared resumed tid priority node name,
  observed.(os_sched_call_stack).(stackLeaseSlot) <> tid ->
  flag_pend_non_idle_at sg observed resumed ->
  flag_pend_non_idle_at sg observed (task_delete_cut sg prepared resumed tid priority node name).
Proof.
  intros sg observed prepared resumed tid priority node name Hother [old [Hold [Hg Hp]]].
  destruct (task_unlink_used_map_preserves_other_fields resumed.(TskState).(inUsedTaskStates)
    tid (task_delete_prepared_node node) _ old Hother Hold) as [current [Hcurrent Hfields]].
  pose proof (f_equal taskGeneration Hfields) as Hgen.
  pose proof (f_equal curPrio Hfields) as Hprio.
  cbn [task_set_links taskGeneration curPrio] in Hgen, Hprio.
  exists current; split; [exact Hcurrent|]. split; congruence.
Qed.

(** Both observations are the stored proofs of this capture's actual
    Restore and Save. Their protocol outputs are composed in that order. *)
Lemma task_delete_capture_resumed_protocol : forall capture,
  let inputs := capture.(delete_save_restore).(delete_restore_inputs) in
  task_delete_shared_validity inputs.(delete_capture_globals) inputs.(delete_capture_tid)
    inputs.(delete_capture_node).(taskGeneration) capture.(delete_save_resumed) /\
  task_delete_running_protocol inputs.(delete_capture_globals) capture.(delete_save_returned)
    capture.(delete_save_resumed).
Proof.
  intros capture inputs.
  pose proof capture.(delete_save_restore).(delete_restore_preparation) as Hpreparation.
  destruct Hpreparation as [Hlive [Hprepare Hprotocol]].
  pose proof capture.(delete_save_restore).(delete_restore_history) as Hrestore.
  destruct Hrestore as [Hrestore_source [Hrestore_normal [Hrestore_rely [Hrestore_protocol Hrestore_success]]]].
  pose proof capture.(delete_save_observation) as Hsave.
  destruct Hsave as [Hsave_source [Hsave_normal [Hsave_rely [Hsave_protocol Hsave_success]]]].
  split.
  - exact (proj1 (proj2 (proj2 Hsave_rely))).
  - apply Hsave_protocol; apply Hrestore_protocol; exact Hprotocol.
Qed.

Lemma task_delete_capture_recycle_idle : forall capture,
  let inputs := capture.(delete_save_restore).(delete_restore_inputs) in
  capture.(delete_save_resumed).(SchedState).(isRunning) = true ->
  task_idle_ready inputs.(delete_capture_globals) (task_delete_capture_cut capture).(TskState).
Proof.
  intros capture inputs Hrunning.
  destruct (task_delete_capture_resumed_protocol capture) as [Hvalid Hprotocol].
  destruct (Hprotocol Hrunning) as [[idle [node [Hnode [Hpriority Hin]]]] Hother].
  pose proof (proj1 (proj1 (proj2 (proj2 Hvalid)))) as Hprepared.
  destruct Hprepared as [[Hstructure Hmembership] Hretiring].
  destruct (proj1 (Hmembership idle node Hnode) Hin) as [Hready Hnot].
  assert (Hdifferent : idle <> inputs.(delete_capture_tid)).
  { intro Heq; apply Hnot; left; symmetry; exact Heq. }
  destruct (task_unlink_used_map_preserves_other_fields
    capture.(delete_save_resumed).(TskState).(inUsedTaskStates) inputs.(delete_capture_tid)
    (task_delete_prepared_node inputs.(delete_capture_node)) idle node Hdifferent Hnode)
    as [current [Hcurrent Hfields]].
  pose proof (f_equal curPrio Hfields) as Hp.
  pose proof (f_equal stat Hfields) as Hs.
  pose proof (f_equal dly Hfields) as Hd.
  cbn [task_set_links curPrio stat dly] in Hp, Hs, Hd.
  exists idle, current; split; [exact Hcurrent|].
  split; [rewrite Hp; exact Hpriority|rewrite Hs, Hd; exact Hready].
Qed.

Lemma task_delete_own_c_segment_idle_non_idle :
  forall environment critical sg observed state before input stopped returned after output,
  task_delete_own_c_segment environment critical sg
    observed.(os_sched_call_invocation) observed.(os_sched_call_origin)
    state before input stopped returned after output ->
  observed.(os_sched_call_origin) = RunningInvocation
    observed.(os_sched_call_stack).(stackLeaseSlot)
    observed.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(SchedState).(isRunning) = true -> stopped = false ->
  (task_idle_ready sg state.(TskState) -> task_idle_ready sg returned.(TskState)) /\
  (flag_pend_non_idle_at sg observed state -> flag_pend_non_idle_at sg observed returned).
Proof.
  intros environment critical sg observed state before input stopped returned after output
    Hstep Horigin Hrunning Hstop.
  destruct Hstep as [inputs before_heap prepared_heap Hcontext Hcompletion|
                    capture after_heap Hcontext Hcompletion].
  - destruct Hcontext as [Henv [Hcritical Hsg]]; subst sg.
    destruct Hcompletion as [Hpreparation Hinput Houtput].
    destruct Hpreparation as [[Hlookup [Hselected [Hlive Hpointer]]] [Hprepare Hprotocol]].
    change ((task_idle_ready inputs.(delete_capture_globals) inputs.(delete_capture_acquired).(TskState) ->
      task_idle_ready inputs.(delete_capture_globals) inputs.(delete_capture_prepared).(TskState)) /\
      (flag_pend_non_idle_at inputs.(delete_capture_globals) observed inputs.(delete_capture_acquired) ->
       flag_pend_non_idle_at inputs.(delete_capture_globals) observed inputs.(delete_capture_prepared))).
    eapply task_delete_prepare_single_wait_idle_non_idle.
    + exact (proj2 (task_delete_table_lookup_live _ _ _ _ Hlive)).
    + exact Hprepare.
  - destruct Hcontext as [Henv [Hcritical Hsg]]; subst sg; split.
    + intro Hidle; apply task_delete_capture_recycle_idle; exact Hrunning.
    + apply task_delete_cut_non_idle.
      unfold task_delete_recycle_stops_origin in Hstop; rewrite Horigin in Hstop.
      apply Z.eqb_neq; exact Hstop.
Qed.
End SelectedDeleteIdle.
