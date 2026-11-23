(** Report-only ordinary module extracted from the frozen checked C context.
    The original proof bodies are retained under the recorded shared-reference map. *)
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
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
Require Export Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Export Ucos2Verify.VC.code.flag.spec.flag_pend_selected_call_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_task_return_callee_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_sched_source_spec.


























































Module PendSchedulerInputSources.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import PrimitiveComponent PendPhaseCandidate SelectedCallerPhaseComponent
  SchedulerPhaseCandidate SchedulerCalleePhaseComponent.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Lemma flag_pend_first_waiting_current_waiter__block_waiting :
  forall sg i requested wait_type timeout acquired node blocked,
  flag_pend_first_waiting sg i requested wait_type timeout acquired node blocked ->
  exists waiter,
    blocked.(SchedState).(curTaskID) = Some waiter.(flagTask) /\
    blocked.(FlagState).(flagWaitNodes) node = Some waiter.
Proof.
  intros sg i requested wait_type timeout acquired node blocked Hwaiting.
  unfold flag_pend_first_waiting, flag_pend_first_critical in Hwaiting.
  destruct (decode_flag_wait_mode sg.(osKernelConfig) (Z.land wait_type 127)) as [mode|];
    [|destruct Hwaiting as [Hfalse _]; discriminate].
  destruct Hwaiting as [image [Himage Hwaiting]].
  destruct (negb (Z.eqb image.(flagImageType) 5));
    [destruct Hwaiting as [Hfalse _]; discriminate|].
  destruct (flag_wait_satisfied mode (flag_ready_bits sg.(osKernelConfig) image.(flagImageBits) requested mode) requested);
    [destruct Hwaiting as [tid [old [_ [_ [Hfalse _]]]]]; discriminate|].
  destruct Hwaiting as [waiter [old [group [post [Hprotocol
    [Hgroup [Hmask [Hmode [Hblock [Hphase Hpost]]]]]]]]]].
  injection Hphase as Hnode; subst node; subst blocked.
  destruct (flag_block_spec.flag_block_result _ _ _ _ _ Hblock)
    as [tid [old2 [flags [Hcurrent [Hlookup [Hflags Hpost]]]]]].
  pose proof (proj1 Hprotocol) as Hcurrent_waiter.
  assert (Htid : tid = waiter.(flagTask)) by congruence; subst tid; subst post.
  unfold flag_block_node in Hflags.
  destruct (acquired.(FlagState).(flagUsed) waiter.(flagGroup)) as [g|]; [|discriminate].
  destruct (acquired.(FlagState).(flagImages) waiter.(flagGroup)) as [v|]; [|discriminate].
  injection Hflags as Hflags; subst flags.
  cbn [flag_block_spec.flag_block_state replace_FlagS replace_SchedS replace_TskS SchedState FlagState
    sched_remove_ready_task curTaskID flagWaitNodes].
  destruct (Z.eqb v.(flagImageHead) 0) eqn:Hhead.
  - rewrite kernel_resources.kernel_map_set_same.
    eexists; split; [|reflexivity]; exact Hcurrent_waiter.
  - unfold flag_nodes_set_prev.
    destruct (Z.eq_dec waiter.(flagNodeAddr) v.(flagImageHead)) as [Heq|Hneq].
    + rewrite <- Heq.
      rewrite !kernel_resources.kernel_map_set_same.
      cbn [option_map].
      eexists; split; [|reflexivity]; exact Hcurrent_waiter.
    + rewrite kernel_resources.kernel_map_set_other by exact Hneq.
      rewrite kernel_resources.kernel_map_set_same.
      eexists; split; [|reflexivity]; exact Hcurrent_waiter.
Qed.

Lemma flag_pend_waiting_active_task_source__block_waiting :
  forall sg i requested wait_type timeout acquired node blocked original call,
  flag_pend_first_waiting sg i requested wait_type timeout acquired node blocked ->
  flag_pend_wait_active sg original node call blocked |--
    coq_prop (task_resume_spec.kernel_call_task_source call blocked).
Proof.
  intros sg i requested wait_type timeout acquired node blocked original call Hwaiting.
  destruct (flag_pend_first_waiting_current_waiter__block_waiting _ _ _ _ _ _ _ _ Hwaiting)
    as [waiter [Hcurrent Hnode]].
  unfold flag_pend_wait_active, flag_active_phase_source_spec.flag_active_waiting.
  Intros.
  entailer!.
  destruct H0 as [task [Hfields Hregistration]].
  rewrite Hnode in Hregistration.
  destruct Hregistration as [Hnode_addr [Hkey Hbacklink]].
  destruct Hfields as [[Hinv_eq [Horigin_eq Hstack_eq]]
    [Horigin [Hlookup [Hgen [Hinv Hclear]]]]].
  assert (Hslot : original.(os_sched_call_stack).(stackLeaseSlot) = waiter.(flagTask)).
  { exact (f_equal fst Hkey). }
  unfold task_resume_spec.kernel_call_task_source.
  split; [rewrite Horigin_eq, Hstack_eq; exact Horigin|].
  split; [rewrite Hinv_eq, Horigin_eq; exact Hinv|].
  unfold task_resume_spec.task_execution_current; rewrite Horigin_eq, Horigin, Hslot; exact Hcurrent.
Qed.

Lemma flag_pend_waiting_restore_input_facts__block_waiting :
  forall environment critical local sg original node call saved acquired blocked
    i requested wait_type timeout,
  flag_pend_first_waiting sg i requested wait_type timeout acquired node blocked ->
  flag_pend_caller_restore_input environment critical local
    (flag_pend_wait_active sg original node) sg (FlagPendTaskCaller call)
    call saved acquired blocked |--
  coq_prop (UCOS2_state_inv sg blocked /\
    task_resume_spec.kernel_call_task_source call blocked).
Proof.
  intros environment critical local sg original node call saved acquired blocked
    i requested wait_type timeout Hwaiting.
  unfold flag_pend_caller_restore_input, flag_pend_active_restore_input,
    os_sched_fields_restore_input.
  Intros.
  prop_apply_p (flag_pend_waiting_active_task_source__block_waiting
    sg i requested wait_type timeout acquired node blocked original call Hwaiting).
  Intros.
  unfold UCOS2_fields_inv; Intros; entailer!.
Qed.
End PendSchedulerInputSources.


Module PendSchedulerEntry.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import PrimitiveComponent PendPhaseCandidate SelectedCallerPhaseComponent
  SchedulerCalleePhaseComponent PendSchedulerInputSources.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma flag_pend_first_waiting_block_source :
  forall sg i requested wait_type timeout acquired node blocked,
  flag_pend_first_waiting sg i requested wait_type timeout acquired node blocked ->
  exists waiter old group image,
    flag_block_call_protocol sg acquired waiter old group image timeout /\
    flag_block_spec.flag_block sg acquired waiter timeout = Some blocked.
Proof.
  intros sg i requested wait_type timeout acquired node blocked Hwaiting.
  unfold flag_pend_first_waiting, flag_pend_first_critical in Hwaiting.
  destruct (decode_flag_wait_mode sg.(osKernelConfig) (Z.land wait_type 127)) as [mode|];
    [|destruct Hwaiting as [Hfalse _]; discriminate].
  destruct Hwaiting as [image [Himage Hwaiting]].
  destruct (negb (Z.eqb image.(flagImageType) 5));
    [destruct Hwaiting as [Hfalse _]; discriminate|].
  destruct (flag_wait_satisfied mode
    (flag_ready_bits sg.(osKernelConfig) image.(flagImageBits) requested mode) requested);
    [destruct Hwaiting as [tid [old [_ [_ [Hfalse _]]]]]; discriminate|].
  destruct Hwaiting as [waiter [old [group [post [Hprotocol
    [Hgroup [Hmask [Hmode [Hblock [Hphase Hpost]]]]]]]]]].
  subst blocked. exists waiter, old, group, image; split; assumption.
Qed.

Lemma flag_pend_first_waiting_current_consistency :
  forall sg i requested wait_type timeout acquired node blocked,
  flag_pend_first_waiting sg i requested wait_type timeout acquired node blocked ->
  sched_current_consistency blocked.(TskState) blocked.(SchedState).
Proof.
  intros sg i requested wait_type timeout acquired node blocked Hwaiting.
  destruct (flag_pend_first_waiting_block_source _ _ _ _ _ _ _ _ Hwaiting)
    as [waiter [old [group [image [Hprotocol Hblock]]]]].
  apply (flag_block_preserves_current_consistency sg acquired waiter timeout blocked Hblock).
  destruct Hprotocol as [Hcurrent [Hpriority [Hlookup Hrest]]].
  unfold sched_current_consistency; rewrite Hcurrent.
  exists old; split; assumption.
Qed.

Lemma flag_pend_first_waiting_control :
  forall sg i requested wait_type timeout acquired node blocked,
  flag_pend_first_waiting sg i requested wait_type timeout acquired node blocked ->
  kernel_call_control_rely sg acquired blocked.
Proof.
  intros sg i requested wait_type timeout acquired node blocked Hwaiting.
  destruct (flag_pend_first_waiting_block_source _ _ _ _ _ _ _ _ Hwaiting)
    as [waiter [old [group [image [Hprotocol Hblock]]]]].
  exact (flag_block_control_rely sg acquired waiter timeout blocked Hblock).
Qed.

Lemma flag_pend_task_save_input_interrupt_range :
  forall environment critical local active sg call mask state,
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller call) call mask state |--
  coq_prop (interrupt_in_range state.(IntrState)).
Proof.
  intros.
  unfold flag_pend_caller_save_input, flag_pend_active_save_input,
    os_sched_fields_save_input.
  Intros.
  rewrite (UCOS2_fields_inv_split_module sg state InterruptModule) by discriminate.
  cbn [UCOS2_module_rep].
  unfold interrupt_inv; Intros; entailer!.
Qed.

(** The before and after resources, source and endpoint observation below
    all come from this one selected Restore event. *)
Lemma flag_pend_waiting_restore_output_scheduler_facts :
  forall environment critical local sg original node call saved acquired blocked
    before_heap i requested wait_type timeout,
  flag_pend_first_waiting sg i requested wait_type timeout acquired node blocked ->
  SelectedCallerPhaseComponent.flag_pend_selected_caller_restore_output
    environment critical local (flag_pend_wait_active sg original node) sg
    (FlagPendTaskCaller call) call saved acquired blocked before_heap |--
  EX returned current next_local,
    coq_prop
      (ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect
         environment critical sg call blocked returned current /\
       kernel_call_task_source returned current /\
       sched_current_consistency current.(TskState) current.(SchedState) /\
       flag_pend_call_source_observations environment sg
         (FlagPendTaskCaller call) call blocked returned current /\
       kernel_call_control_rely sg blocked current) &&
    flag_pend_caller_save_input environment critical next_local
      (flag_pend_wait_active sg original node) sg (FlagPendTaskCaller returned)
      returned (armv7a_irq_fiq_mask saved) current.
Proof.
  intros environment critical local sg original node call saved acquired blocked
    before_heap i requested wait_type timeout Hwaiting heap
    [returned_caller [returned [current [next_local [Hobs [Hbefore [Hafter Hcompleted]]]]]]].
  pose proof (flag_pend_waiting_restore_input_facts__block_waiting
    environment critical local sg original node call saved acquired blocked
    i requested wait_type timeout Hwaiting before_heap Hbefore) as Hfacts.
  change (UCOS2_state_inv sg blocked /\ kernel_call_task_source call blocked) in Hfacts.
  destruct Hfacts as [Hvalid Hsource].
  pose proof (PendPhaseCandidate.flag_pend_caller_completed_source_observations
    FlagPendRestoreSource environment critical sg
    (SelectedEventSources.flag_pend_selected_linked_sources environment critical sg)
    (FlagPendTaskCaller call) call blocked _ before_heap
    returned_caller returned current heap _ Hcompleted) as Hobserved.
  pose proof (PendPhaseCandidate.flag_pend_caller_completed_source_endpoints
    FlagPendRestoreSource environment critical sg
    (SelectedEventSources.flag_pend_selected_linked_sources environment critical sg)
    (FlagPendTaskCaller call) call blocked _ before_heap
    returned_caller returned current heap _ Hcompleted) as Hendpoints.
  destruct returned_caller as [next|view key]; [|contradiction].
  destruct Hobs as [Hactual [Hnext [Heffect [Hsame [Hpreserved Htransport]]]]].
  subst next.
  assert (Hreturned : kernel_call_task_source returned current).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff returned call current Hsame)).
    exact (Htransport Hvalid Hsource). }
  assert (Hcache : sched_current_consistency current.(TskState) current.(SchedState)).
  { eapply (SelectedEventSources.flag_pend_selected_restore_current_cache environment critical local next_local
      (flag_pend_wait_active sg original node) sg call saved acquired blocked
      before_heap returned current heap).
    - exact Hcompleted.
    - exact Hsource.
    - eapply flag_pend_first_waiting_current_consistency; exact Hwaiting.
    - exact Hreturned. }
  destruct Hendpoints as [Hready [Hidle [Hnonidle [Hnormal Hcontrol]]]].
  assert (Hnonboot : call.(os_sched_call_origin) <> BootInvocation).
  { pose proof (proj1 Hsource) as Horigin; rewrite Horigin; discriminate. }
  specialize (Hcontrol Hnonboot).
  exists returned, current, next_local; split; [|exact Hafter].
  exact (conj Heffect (conj Hreturned (conj Hcache (conj Hobserved Hcontrol)))).
Qed.

(** This is the call-site consequence after the actual first Save's counter
    observation has been retained.  It does not establish that observation
    from the old, weaker saved_prefix. *)
Lemma flag_pend_waiting_restore_output_scheduler_entry :
  forall environment critical local sg original node call saved acquired blocked
    before before_heap mask i pgrp requested wait_type timeout,
  flag_pend_saved_prefix environment critical sg original mask before i pgrp
    call saved acquired ->
  before.(IntrState) = acquired.(IntrState) ->
  flag_pend_first_waiting sg i requested wait_type timeout acquired node blocked ->
  SelectedCallerPhaseComponent.flag_pend_selected_caller_restore_output
    environment critical local (flag_pend_wait_active sg original node) sg
    (FlagPendTaskCaller call) call saved acquired blocked before_heap |--
  EX returned current next_local,
    coq_prop
      (ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect
         environment critical sg call blocked returned current /\
       flag_pend_call_source_observations environment sg
         (FlagPendTaskCaller call) call blocked returned current /\
       SchedulerCalleePhaseComponent.os_sched_task_entry_observation returned current) &&
    flag_pend_caller_save_input environment critical next_local
      (flag_pend_wait_active sg original node) sg (FlagPendTaskCaller returned)
      returned (armv7a_irq_fiq_mask saved) current.
Proof.
  intros environment critical local sg original node call saved acquired blocked
    before before_heap mask i pgrp requested wait_type timeout Hprefix Hsaved_control Hwaiting.
  sep_apply_l_atomic (flag_pend_waiting_restore_output_scheduler_facts
    environment critical local sg original node call saved acquired blocked
    before_heap i requested wait_type timeout Hwaiting).
  Intros returned current next_local.
  destruct H as [Heffect [Hsource [Hcache [Hobserved Hcontrol]]]].
  prop_apply_p (flag_pend_task_save_input_interrupt_range environment critical next_local
    (flag_pend_wait_active sg original node) sg returned (armv7a_irq_fiq_mask saved) current).
  Intros.
  assert (Hrange : interrupt_in_range current.(IntrState)) by assumption.
  destruct Hrange as [Hints_range Hlocks_range].
  destruct Hprefix as [Hpgrp [Hints [Hlocks Hrest]]].
  pose proof (proj2 (flag_pend_first_waiting_control _ _ _ _ _ _ _ _ Hwaiting)) as Hblock_control.
  pose proof (proj2 Hcontrol) as Hrestore_control.
  assert (Hcounters : before.(IntrState) = current.(IntrState)).
  { rewrite Hrestore_control, Hblock_control; exact Hsaved_control. }
  rewrite Hcounters in Hints, Hlocks.
  assert (Henabled : os_sched_selection_enabled current = true).
  { unfold os_sched_selection_enabled.
    assert (Hi : current.(IntrState).(intNesting) = 0) by lia.
    assert (Hl : current.(IntrState).(lockNesting) = 0) by lia.
    rewrite Hi, Hl; reflexivity. }
  Exists returned current next_local.
  unfold SchedulerCalleePhaseComponent.os_sched_task_entry_observation.
  entailer!.
Qed.

End PendSchedulerEntry.












(** Use only with the new report seed in this directory.
    This producer retains the first Save's actual endpoint fact.
    It does not add an input requirement or select a different event. *)
Module PendSchedulerSeedAdapter.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import PrimitiveComponent PendPhaseCandidate SelectedCallerPhaseComponent
  SchedulerPhaseCandidate SchedulerCalleePhaseComponent.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Lemma flag_pend_acquired_task_stage_with_counters :
  forall environment critical sg caller call mask i pgrp requested mode timeout before X
    entered_caller entered saved acquired,
  flag_pend_public_entry environment critical sg caller call mask i pgrp requested mode timeout before X ->
  flag_pend_caller_saved_prefix environment critical sg caller call mask before i pgrp
    entered_caller entered saved acquired ->
  flag_pend_call_source_observations environment sg caller call before entered acquired ->
  flag_pend_first_registration mode call before entered acquired ->
  flag_pend_valid_mode mode ->
  entered_caller = FlagPendTaskCaller entered /\
  flag_pend_saved_prefix environment critical sg call mask before i pgrp entered saved acquired /\
  flag_pend_task_stage entered acquired.
Proof.
  intros environment critical sg caller call mask i pgrp requested mode timeout before X
    entered_caller entered saved acquired Hentry Hprefix Hsource Hregistration Hmode.
  destruct Hentry as [Hconfig [Haddress [Hrequested [Hmode_range [Htimeout [Hcaller Hsafe]]]]]].
  destruct Hprefix as [Hptr [Hnest [Hlock [[image [Himage Htype]] [Hsave Hsaved]]]]].
  destruct caller as [actual|view key].
  2: { destruct Hcaller as [Hirq Hdomain]; exfalso.
       exact (Hdomain Hptr Hnest Hlock image Himage Htype Hmode). }
  destruct Hcaller as [Eactual Hdomain]; subst actual.
  destruct (Hdomain Hptr Hnest Hlock image Himage Htype Hmode)
    as [Htask [Hidle Hnonidle]].
  destruct entered_caller as [next|view key]; [|contradiction].
  destruct Hsave as [_ [Enext [Heffect [Hsame Hpreserved]]]]; subst next.
  pose proof (PendPhaseCandidate.flag_pend_caller_return_control_task_source
    call before entered acquired (flag_pend_task_entry_call_source call before Htask)
    (proj2 (proj2 (proj2 Hsource)))) as Htask_control.
  split; [reflexivity|]. split.
  - unfold flag_pend_saved_prefix.
    split; [exact Hptr|]. split; [exact Hnest|]. split; [exact Hlock|].
    split; [exists image; auto|]. split; [exact Heffect|].
    split; [exact Hsaved|]. split; [exact Hsame|].
    exact (proj2 (proj2 Htask_control)).
  - destruct Hsource as [Hready [Hidle_after [Hnonidle_after Hcontrol]]].
    apply flag_pend_fresh_ready_task_stage with (original:=call).
    + apply Hregistration; left; exact Hmode.
    + apply Hready; split.
      * apply flag_pend_task_entry_call_source; exact Htask.
      * destruct Htask as [[Ho [Hr [Hp [node [Hready_node [Hgen Hclean]]]]]] Hactive].
        exists node; auto.
    + eapply flag_pend_return_control_running_available; [exact Htask_control|].
      destruct Htask as [[Ho [Hr [Hp Hrest]]] Hactive].
      unfold flag_pend_running_available. split; [exact Hr|].
      unfold kernel_call_stack_available; rewrite Ho; exact Hp.
Qed.

Lemma flag_pend_task_source_observations_interrupts_eq :
  forall environment sg original before returned current,
  kernel_call_task_source original before ->
  flag_pend_call_source_observations environment sg (FlagPendTaskCaller original)
    original before returned current ->
  before.(IntrState) = current.(IntrState).
Proof.
  intros environment sg original before returned current Hsource
    [_ [_ [_ Hcaller_control]]].
  exact (proj2 (proj2 (PendPhaseCandidate.flag_pend_caller_return_control_task_source
    original before returned current Hsource Hcaller_control))).
Qed.

Lemma flag_pend_saved_prefix_interrupts_eq :
  forall environment critical sg original mask before i pgrp entered saved acquired,
  flag_pend_saved_prefix environment critical sg original mask before i pgrp
    entered saved acquired ->
  before.(IntrState) = acquired.(IntrState).
Proof.
  intros environment critical sg original mask before i pgrp entered saved acquired
    [_ [_ [_ [_ [_ [_ [_ Hcounters]]]]]]].
  exact Hcounters.
Qed.

End PendSchedulerSeedAdapter.


(** Append after entry-proofs.v.in in the new seed's unified context. *)
Module PendSchedulerSeedEntry.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import PrimitiveComponent PendPhaseCandidate SelectedCallerPhaseComponent
  SchedulerCalleePhaseComponent PendSchedulerSeedAdapter.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma flag_pend_waiting_restore_output_entry_from_saved_prefix :
  forall environment critical local sg original node call saved acquired blocked
    before before_heap mask i pgrp requested wait_type timeout,
  flag_pend_saved_prefix environment critical sg original mask before i pgrp
    call saved acquired ->
  flag_pend_first_waiting sg i requested wait_type timeout acquired node blocked ->
  SelectedCallerPhaseComponent.flag_pend_selected_caller_restore_output
    environment critical local (flag_pend_wait_active sg original node) sg
    (FlagPendTaskCaller call) call saved acquired blocked before_heap |--
  EX returned current next_local,
    coq_prop
      (ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect
         environment critical sg call blocked returned current /\
       flag_pend_call_source_observations environment sg
         (FlagPendTaskCaller call) call blocked returned current /\
       SchedulerCalleePhaseComponent.os_sched_task_entry_observation returned current) &&
    flag_pend_caller_save_input environment critical next_local
      (flag_pend_wait_active sg original node) sg (FlagPendTaskCaller returned)
      returned (armv7a_irq_fiq_mask saved) current.
Proof.
  intros environment critical local sg original node call saved acquired blocked
    before before_heap mask i pgrp requested wait_type timeout Hprefix Hwaiting.
  eapply PendSchedulerEntry.flag_pend_waiting_restore_output_scheduler_entry.
  - exact Hprefix.
  - eapply flag_pend_saved_prefix_interrupts_eq; exact Hprefix.
  - exact Hwaiting.
Qed.

End PendSchedulerSeedEntry.
