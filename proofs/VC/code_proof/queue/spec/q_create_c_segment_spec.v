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

Module QueueCreationComponent.





























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

Import EventStateDef.

Definition queue_creation_reserve_written_owner sg entry qid rest : Assertion :=
  event_raw_rep sg entry.(TskState) entry.(EventState) **
    (store_map (published_queue_node_rep sg entry.(EventState)) entry.(EventState).(inUsedEventStates) **
      (sg.(g_OSQFreeList) # Ptr |-> queue_free_head sg rest **
        (free_queue_node sg qid (queue_free_head sg rest) ** store_free_queue_nodes sg rest))) **
    UCOS2_raw_rep_missing_event_queue sg entry.

Definition queue_creation_rollback_written_owner sg entry eid allocation : Assertion :=
  store_map (used_event_rep sg entry.(TskState)) entry.(EventState).(inUsedEventStates) **
    (event_cell (event_pool_addr sg eid) EventPtrField
      (Some (event_encode_pool_link sg (hd_error entry.(EventState).(unUsedEventStates)))) **
      event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
        allocation.(eventPrivateStorage) EventPtrField **
      event_free_storage_rep sg entry.(EventState) **
      sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid) **
    queue_storage_rep sg entry.(EventState) ** UCOS2_raw_rep_missing_event_queue sg entry.

Definition queue_creation_publication_owner sg entry free eid allocation qid qcb_image start size slots : Assertion :=
  (event_private_storage_rep sg eid allocation ** event_raw_rep sg entry.(TskState) entry.(EventState)) **
    (store_map (published_queue_node_rep sg entry.(EventState)) entry.(EventState).(inUsedEventStates) **
      (qcb_storage_rep sg qid (qcb_initialize qcb_image start size) **
        (PtrArray.mixed_full start size slots ** store_free_queue_list sg free))) **
    UCOS2_raw_rep_missing_event_queue sg entry.

Inductive kernel_queue_creation_c_source (sg : StableGlobVars) :
  UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| KernelQueueCreationCReserveSource : forall entry eid free result returned,
    queue_pool_partition sg entry.(EventState) free ->
    q_create_reserve_critical sg eid free entry result returned ->
    kernel_queue_creation_c_source sg entry returned
| KernelQueueCreationCPublishSource : forall entry free eid allocation qid start size slots name,
    queue_pool_partition sg entry.(EventState) free ->
    entry.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
    allocation.(eventPrivateQueue) = Some qid ->
    event_name_valid sg entry.(NameState) (q_create_initialized_event allocation qid start size name) ->
    kernel_queue_creation_c_source sg entry
      (replace_EventS (queue_publish entry.(EventState) eid
        (q_create_initialized_event allocation qid start size name) qid slots) entry).

Lemma kernel_queue_creation_c_source_fields_eq : forall sg entry returned,
  kernel_queue_creation_c_source sg entry returned ->
  returned.(TskState) = entry.(TskState) /\ returned.(SchedState) = entry.(SchedState).
Proof.
  intros sg entry returned Hsource; destruct Hsource; [|split; reflexivity].
  destruct H0 as [allocation [Hget Hcode]]; destruct free;
    destruct Hcode as [_ ->]; split; reflexivity.
Qed.

Inductive kernel_queue_creation_c_segment (sg : StableGlobVars) :
  UCOS2_Verify_State -> model -> Assertion -> UCOS2_Verify_State -> model -> Assertion -> Prop :=
| KernelQueueCreationCReserveSegment : forall entry eid allocation qid rest before after frame,
    queue_pool_partition sg entry.(EventState) (qid :: rest) ->
    q_create_reserve_critical sg eid (qid :: rest) entry (Some qid)
      (replace_EventS (queue_reserve_control_block entry.(EventState) eid allocation qid) entry) ->
    (UCOS2_inv sg entry ** (event_private_storage_rep sg eid allocation ** frame)) before ->
    ((free_queue_node sg qid (queue_free_head sg rest) **
      UCOS2_inv sg (replace_EventS (queue_reserve_control_block entry.(EventState) eid allocation qid) entry)) **
      (event_private_storage_rep sg eid allocation ** frame)) after ->
    kernel_queue_creation_c_segment sg entry before
      (UCOS2_inv sg entry ** (event_private_storage_rep sg eid allocation ** frame))
      (replace_EventS (queue_reserve_control_block entry.(EventState) eid allocation qid) entry) after
      ((free_queue_node sg qid (queue_free_head sg rest) **
        UCOS2_inv sg (replace_EventS (queue_reserve_control_block entry.(EventState) eid allocation qid) entry)) **
        (event_private_storage_rep sg eid allocation ** frame))
| KernelQueueCreationCRollbackSegment : forall entry eid allocation before after frame,
    queue_pool_partition sg entry.(EventState) [] ->
    q_create_reserve_critical sg eid [] entry None
      (replace_EventS (event_rollback sg entry.(EventState) eid allocation) entry) ->
    (UCOS2_inv sg entry ** (event_private_storage_rep sg eid allocation ** frame)) before ->
    (UCOS2_inv sg (replace_EventS (event_rollback sg entry.(EventState) eid allocation) entry) ** frame) after ->
    kernel_queue_creation_c_segment sg entry before
      (UCOS2_inv sg entry ** (event_private_storage_rep sg eid allocation ** frame))
      (replace_EventS (event_rollback sg entry.(EventState) eid allocation) entry) after
      (UCOS2_inv sg (replace_EventS (event_rollback sg entry.(EventState) eid allocation) entry) ** frame)
| KernelQueueCreationCPublishSegment : forall entry free eid allocation qid qcb_image start size slots name h frame,
    queue_pool_partition sg entry.(EventState) free ->
    entry.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
    allocation.(eventPrivateQueue) = Some qid ->
    event_name_valid sg entry.(NameState) (q_create_initialized_event allocation qid start size name) ->
    (queue_creation_publication_owner sg entry free eid allocation qid qcb_image start size slots ** frame) h ->
    (UCOS2_inv sg (replace_EventS (queue_publish entry.(EventState) eid
      (q_create_initialized_event allocation qid start size name) qid slots) entry) ** frame) h ->
    kernel_queue_creation_c_segment sg entry h
      (queue_creation_publication_owner sg entry free eid allocation qid qcb_image start size slots ** frame)
      (replace_EventS (queue_publish entry.(EventState) eid
        (q_create_initialized_event allocation qid start size name) qid slots) entry) h
      (UCOS2_inv sg (replace_EventS (queue_publish entry.(EventState) eid
        (q_create_initialized_event allocation qid start size name) qid slots) entry) ** frame).

Lemma q_create_reserve_c_store_post_segment : forall sg entry eid allocation qid rest before after frame,
  queue_published_storage_binding entry.(EventState) ->
  queue_pool_partition sg entry.(EventState) (qid :: rest) ->
  entry.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None -> allocation.(eventPrivateMutexPCP) = None ->
  (UCOS2_inv sg entry ** (event_private_storage_rep sg eid allocation ** frame)) before ->
  (queue_creation_reserve_written_owner sg entry qid rest **
    (event_private_storage_rep sg eid allocation ** frame)) after ->
  kernel_queue_creation_c_segment sg entry before
    (UCOS2_inv sg entry ** (event_private_storage_rep sg eid allocation ** frame))
    (replace_EventS (queue_reserve_control_block entry.(EventState) eid allocation qid) entry) after
    ((free_queue_node sg qid (queue_free_head sg rest) **
      UCOS2_inv sg (replace_EventS (queue_reserve_control_block entry.(EventState) eid allocation qid) entry)) **
      (event_private_storage_rep sg eid allocation ** frame)).
Proof.
  intros sg entry eid allocation qid rest before after frame Hbinding Hpool Hget Hqueue Hpcp Hpre Hpost.
  assert (Hvalid : UCOS2_state_inv sg entry).
  { destruct Hpre as [hbody [hframe [Hjoin [[Hvalid Hraw] Hframe]]]]; exact Hvalid. }
  apply KernelQueueCreationCReserveSegment; try assumption.
  - exists allocation; split; [exact Hget|]; split; reflexivity.
  - destruct Hpost as [hbody [hframe [Hjoin [Hbody Hframe]]]].
    exists hbody, hframe; split; [exact Hjoin|]; split; [|exact Hframe].
    exact (q_create_reserve_merge sg entry eid allocation qid rest
      Hvalid Hbinding Hpool Hget Hqueue Hpcp hbody Hbody).
Qed.

Lemma q_create_rollback_c_store_post_segment : forall sg entry eid allocation before after frame,
  queue_pool_partition sg entry.(EventState) [] ->
  entry.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None ->
  allocation.(eventPrivateStorage) EventTypeField = Some 0 -> allocation.(eventPrivateMutexPCP) = None ->
  (UCOS2_inv sg entry ** (event_private_storage_rep sg eid allocation ** frame)) before ->
  (queue_creation_rollback_written_owner sg entry eid allocation ** frame) after ->
  kernel_queue_creation_c_segment sg entry before
    (UCOS2_inv sg entry ** (event_private_storage_rep sg eid allocation ** frame))
    (replace_EventS (event_rollback sg entry.(EventState) eid allocation) entry) after
    (UCOS2_inv sg (replace_EventS (event_rollback sg entry.(EventState) eid allocation) entry) ** frame).
Proof.
  intros sg entry eid allocation before after frame Hpool Hget Hqueue Htype Hpcp Hpre Hpost.
  assert (Hvalid : UCOS2_state_inv sg entry).
  { destruct Hpre as [hbody [hframe [Hjoin [[Hvalid Hraw] Hframe]]]]; exact Hvalid. }
  apply KernelQueueCreationCRollbackSegment; try assumption.
  - exists allocation; split; [exact Hget|]; split; reflexivity.
  - destruct Hpost as [hbody [hframe [Hjoin [Hbody Hframe]]]].
    exists hbody, hframe; split; [exact Hjoin|]; split; [|exact Hframe].
    exact (q_create_rollback_merge sg entry eid allocation Hvalid Hget Hqueue Htype Hpcp hbody Hbody).
Qed.

Lemma q_create_publication_c_owner_segment :
  forall sg entry free eid allocation eid_image qid qcb_image start size slots name h frame,
  UCOS2_state_inv sg entry -> queue_published_storage_binding entry.(EventState) ->
  queue_pool_partition sg entry.(EventState) free ->
  entry.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = Some qid ->
  allocation.(eventPrivateStorage) = event_create_image sg.(osKernelConfig).(cfgEventNames)
    2 0 (qcb_addr sg qid) name eid_image ->
  0 < start -> 0 <= size <= 65535 -> Zlength slots = size ->
  event_name_valid sg entry.(NameState) (q_create_initialized_event allocation qid start size name) ->
  (queue_creation_publication_owner sg entry free eid allocation qid qcb_image start size slots ** frame) h ->
  kernel_queue_creation_c_segment sg entry h
    (queue_creation_publication_owner sg entry free eid allocation qid qcb_image start size slots ** frame)
    (replace_EventS (queue_publish entry.(EventState) eid
      (q_create_initialized_event allocation qid start size name) qid slots) entry) h
    (UCOS2_inv sg (replace_EventS (queue_publish entry.(EventState) eid
      (q_create_initialized_event allocation qid start size name) qid slots) entry) ** frame).
Proof.
  intros sg entry free eid allocation eid_image qid qcb_image start size slots name h frame
    Hvalid Hbinding Hpool Hget Howner Himage Hstart Hsize Hlength Hname Hpre.
  apply KernelQueueCreationCPublishSegment; try assumption.
  destruct Hpre as [hbody [hframe [Hjoin [Hbody Hframe]]]].
  exists hbody, hframe; split; [exact Hjoin|]; split; [|exact Hframe].
  exact (q_create_publish_merge sg entry free eid allocation eid_image qid qcb_image start size slots name
    Hvalid Hbinding Hpool Hget Howner Himage Hstart Hsize Hlength Hname hbody Hbody).
Qed.

Lemma kernel_queue_creation_c_segment_source : forall sg entry before input returned after output,
  kernel_queue_creation_c_segment sg entry before input returned after output ->
  kernel_queue_creation_c_source sg entry returned.
Proof.
  intros sg entry before input returned after output Hsegment; destruct Hsegment.
  - eapply KernelQueueCreationCReserveSource; eassumption.
  - eapply KernelQueueCreationCReserveSource; eassumption.
  - eapply KernelQueueCreationCPublishSource; eassumption.
Qed.

Lemma kernel_queue_creation_c_segment_resources : forall sg entry before input returned after output,
  kernel_queue_creation_c_segment sg entry before input returned after output ->
  input before /\ output after.
Proof. intros sg entry before input returned after output Hsegment; destruct Hsegment; split; assumption. Qed.

Lemma kernel_queue_creation_c_segment_preserves_observer :
  forall sg entry before input returned after output observer origin,
  kernel_queue_creation_c_segment sg entry before input returned after output ->
  task_invocation_active entry.(TskState) observer origin /\ sched_observer_current_cache origin entry ->
  task_invocation_active returned.(TskState) observer origin /\ sched_observer_current_cache origin returned.
Proof.
  intros sg entry before input returned after output observer origin Hsegment [Hactive Hcache].
  pose proof (kernel_queue_creation_c_segment_source _ _ _ _ _ _ _ Hsegment) as Hsource.
  destruct (kernel_queue_creation_c_source_fields_eq _ _ _ Hsource) as [Htasks Hsched].
  split; [rewrite Htasks; exact Hactive|].
  destruct origin; [exact I|]; unfold sched_observer_current_cache in *; rewrite Htasks, Hsched; exact Hcache.
Qed.

Lemma kernel_queue_creation_c_segment_lifetime_result :
  forall sg entry before input returned after output observer origin,
  kernel_queue_creation_c_segment sg entry before input returned after output ->
  task_observer_lifetime_result observer origin entry.(TskState) returned.(TskState) false.
Proof.
  intros sg entry before input returned after output observer origin Hsegment.
  pose proof (kernel_queue_creation_c_segment_source _ _ _ _ _ _ _ Hsegment) as Hsource.
  destruct (kernel_queue_creation_c_source_fields_eq _ _ _ Hsource) as [Htasks Hsched].
  rewrite Htasks; apply task_observer_lifetime_result_not_stopped.
  apply task_observer_lifetime_transport_refl.
Qed.










End QueueCreationComponent.

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
