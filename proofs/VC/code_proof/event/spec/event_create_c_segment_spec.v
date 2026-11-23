(** Report-only ordinary module extracted from the frozen checked C context.
    The original proof bodies are retained under the recorded shared-reference map. *)
Require Import Coq.micromega.Lia.
Require Import Ucos2Verify.VC.code.event.spec.event_create_heap_spec.
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

Module EventCreationComponent.





























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

Inductive kernel_event_creation_c_source : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| KernelEventCreationCAllocateSource : forall entry result returned,
    event_create_allocate_critical entry result returned ->
    kernel_event_creation_c_source entry returned
| KernelEventCreationCStoreSource : forall entry eid allocation field value,
    entry.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
    kernel_event_creation_c_source entry
      (replace_EventS (event_private_write entry.(EventState) eid allocation field (Some value)) entry)
| KernelEventCreationCPublishSource : forall entry eid allocation node,
    entry.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
    kernel_event_creation_c_source entry
      (replace_EventS (event_publish entry.(EventState) eid node) entry).

Lemma kernel_event_creation_c_source_fields_eq : forall entry returned,
  kernel_event_creation_c_source entry returned ->
  returned.(TskState) = entry.(TskState) /\ returned.(SchedState) = entry.(SchedState).
Proof.
  intros entry returned Hsource; destruct Hsource; try (split; reflexivity).
  unfold event_create_allocate_critical in H; destruct (entry.(EventState).(unUsedEventStates)).
  - destruct H as [_ ->]; split; reflexivity.
  - destruct H as [image [_ [_ ->]]]; split; reflexivity.
Qed.

Definition event_creation_allocation_owner (sg : StableGlobVars)
  (result : option (EventID * EventStorage)) (state : UCOS2_Verify_State) : Assertion :=
  match result with
  | None => UCOS2_inv sg state
  | Some (eid, image) => event_storage_rep sg.(osKernelConfig).(cfgEventNames)
      (event_pool_addr sg eid) image ** UCOS2_inv sg state
  end.

Definition event_creation_publication_owner sg entry eid allocation : Assertion :=
  event_private_storage_rep sg eid allocation **
    (event_raw_rep sg entry.(TskState) entry.(EventState) **
      queue_storage_rep sg entry.(EventState) ** UCOS2_raw_rep_missing_event_queue sg entry).

(** Allocation retains the observed result and the detached ECB image;
    private stores retain that ECB; publication consumes that same private
    owner.  The generic publication constructor uses the existing non-Mutex
    payload contract.  Mutex PCP reservation and QCB publication are distinct
    C contracts and are not silently treated as this constructor. *)
Inductive kernel_event_creation_c_segment (sg : StableGlobVars) :
  UCOS2_Verify_State -> model -> Assertion -> UCOS2_Verify_State -> model -> Assertion -> Prop :=
| KernelEventCreationCAllocateSegment : forall entry result returned before after frame,
    event_create_allocate_critical entry result returned ->
    (UCOS2_inv sg entry ** frame) before ->
    (event_creation_allocation_owner sg result returned ** frame) after ->
    kernel_event_creation_c_segment sg entry before (UCOS2_inv sg entry ** frame)
      returned after (event_creation_allocation_owner sg result returned ** frame)
| KernelEventCreationCStoreSegment : forall entry eid allocation field value before after frame,
    entry.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
    In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
    ((event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
      allocation.(eventPrivateStorage) ** UCOS2_inv sg entry) ** frame) before ->
    ((event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
      (event_write allocation.(eventPrivateStorage) field (Some value)) **
      UCOS2_inv sg (replace_EventS
        (event_private_write entry.(EventState) eid allocation field (Some value)) entry)) ** frame) after ->
    kernel_event_creation_c_segment sg entry before
      ((event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
        allocation.(eventPrivateStorage) ** UCOS2_inv sg entry) ** frame)
      (replace_EventS (event_private_write entry.(EventState) eid allocation field (Some value)) entry) after
      ((event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
        (event_write allocation.(eventPrivateStorage) field (Some value)) **
        UCOS2_inv sg (replace_EventS
          (event_private_write entry.(EventState) eid allocation field (Some value)) entry)) ** frame)
| KernelEventCreationCPublishSegment : forall entry eid allocation node h frame,
    entry.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
    event_name_valid sg entry.(NameState) node ->
    node.(eventType) <> OS_EVENT_TYPE_MUTEX ->
    (event_creation_publication_owner sg entry eid allocation ** frame) h ->
    (UCOS2_inv sg (replace_EventS (event_publish entry.(EventState) eid node) entry) ** frame) h ->
    kernel_event_creation_c_segment sg entry h
      (event_creation_publication_owner sg entry eid allocation ** frame)
      (replace_EventS (event_publish entry.(EventState) eid node) entry) h
      (UCOS2_inv sg (replace_EventS (event_publish entry.(EventState) eid node) entry) ** frame)
| KernelEventCreationCAllocateFieldsSegment : forall entry result returned before after frame,
    pointer_load sg.(g_OSEventFreeList) (event_create_return_ptr sg result) before ->
    event_create_allocate_critical entry result returned ->
    (match result with
     | None => after = before
     | Some (eid, _) => event_pool_addr sg eid <> 0 /\ exists next,
         pointer_load (event_pool_addr sg eid + 4) next before /\
         kernel_heap_execution (pointer_store_writes sg.(g_OSEventFreeList) next) before after
     end) ->
    (kernel_program_fields_inv sg entry ** frame) before ->
    (kernel_program_fields_inv sg returned **
      (match result with None => emp | Some (eid, image) =>
         event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image end) ** frame) after ->
    kernel_event_creation_c_segment sg entry before (kernel_program_fields_inv sg entry ** frame)
      returned after (kernel_program_fields_inv sg returned **
        (match result with None => emp | Some (eid, image) =>
           event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image end) ** frame)
| KernelEventCreationCStoreFieldsSegment : forall entry eid allocation field value final before after frame,
    entry.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
    In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
    (event_private_write entry.(EventState) eid allocation field (Some value)).(eventLifecycle).(eventPrivate)
      eid = Some final ->
    kernel_heap_execution (event_create_field_writes (event_pool_addr sg eid) field value) before after ->
    (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg entry ** frame) before ->
    (event_private_storage_rep sg eid final ** kernel_program_fields_inv sg
      (replace_EventS (event_private_write entry.(EventState) eid allocation field (Some value)) entry) ** frame) after ->
    kernel_event_creation_c_segment sg entry before
      (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg entry ** frame)
      (replace_EventS (event_private_write entry.(EventState) eid allocation field (Some value)) entry) after
      (event_private_storage_rep sg eid final ** kernel_program_fields_inv sg
        (replace_EventS (event_private_write entry.(EventState) eid allocation field (Some value)) entry) ** frame)
| KernelEventCreationCPublishFieldsSegment : forall entry eid allocation node h frame,
    entry.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
    event_name_valid sg entry.(NameState) node ->
    node.(eventType) <> OS_EVENT_TYPE_MUTEX ->
    (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg entry ** frame) h ->
    (kernel_program_fields_inv sg (replace_EventS (event_publish entry.(EventState) eid node) entry) ** frame) h ->
    kernel_event_creation_c_segment sg entry h
      (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg entry ** frame)
      (replace_EventS (event_publish entry.(EventState) eid node) entry) h
      (kernel_program_fields_inv sg (replace_EventS (event_publish entry.(EventState) eid node) entry) ** frame).

Lemma event_create_allocate_c_post_segment : forall sg entry result returned before after frame,
  (UCOS2_inv sg entry ** frame) before ->
  (coq_prop (event_create_allocate_critical entry result returned) &&
    (event_creation_allocation_owner sg result returned ** frame)) after ->
  kernel_event_creation_c_segment sg entry before (UCOS2_inv sg entry ** frame)
    returned after (event_creation_allocation_owner sg result returned ** frame).
Proof.
  intros sg entry result returned before after frame Hpre [Hcode Hpost].
  eapply KernelEventCreationCAllocateSegment; eassumption.
Qed.

Lemma event_create_detach_c_store_post_segment : forall sg entry eid rest image before after frame,
  entry.(EventState).(unUsedEventStates) = eid :: rest ->
  entry.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image ->
  (UCOS2_inv sg entry ** frame) before ->
  (((store_map (used_event_rep sg entry.(TskState)) entry.(EventState).(inUsedEventStates) **
    event_free_storage_rep sg entry.(EventState) **
    sg.(g_OSEventFreeList) # Ptr |-> event_encode_pool_link sg (hd_error rest)) **
    queue_storage_rep sg entry.(EventState) ** UCOS2_raw_rep_missing_event_queue sg entry) ** frame) after ->
  kernel_event_creation_c_segment sg entry before (UCOS2_inv sg entry ** frame)
    (replace_EventS (event_detach_head entry.(EventState) eid rest image) entry) after
    (event_creation_allocation_owner sg (Some (eid, image))
      (replace_EventS (event_detach_head entry.(EventState) eid rest image) entry) ** frame).
Proof.
  intros sg entry eid rest image before after frame Hhead Himage Hpre Hpost.
  assert (Hvalid : UCOS2_state_inv sg entry).
  { destruct Hpre as [hbody [hframe [Hjoin [[Hvalid Hraw] Hframe]]]]; exact Hvalid. }
  apply KernelEventCreationCAllocateSegment; [|exact Hpre|].
  - unfold event_create_allocate_critical; rewrite Hhead.
    exists image; split; [exact Himage|]; split; reflexivity.
  - destruct Hpost as [hbody [hframe [Hjoin [Hbody Hframe]]]].
    exists hbody, hframe; split; [exact Hjoin|]; split; [|exact Hframe].
    exact (UCOS2_inv_merge_event_detach_head sg entry eid rest image Hvalid Hhead Himage hbody Hbody).
Qed.

Lemma event_create_private_c_store_post_segment :
  forall sg entry eid allocation field value before after frame,
  entry.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
  ((event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    allocation.(eventPrivateStorage) ** UCOS2_inv sg entry) ** frame) before ->
  (((event_cell (event_pool_addr sg eid) field (Some value) **
    event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
      allocation.(eventPrivateStorage) field) ** UCOS2_inv sg entry) ** frame) after ->
  kernel_event_creation_c_segment sg entry before
    ((event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
      allocation.(eventPrivateStorage) ** UCOS2_inv sg entry) ** frame)
    (replace_EventS (event_private_write entry.(EventState) eid allocation field (Some value)) entry) after
    ((event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
      (event_write allocation.(eventPrivateStorage) field (Some value)) **
      UCOS2_inv sg (replace_EventS
        (event_private_write entry.(EventState) eid allocation field (Some value)) entry)) ** frame).
Proof.
  intros sg entry eid allocation field value before after frame Hget Hfield Hpre Hpost.
  apply KernelEventCreationCStoreSegment; try assumption.
  destruct Hpost as [hbody [hframe [Hjoin [Hbody Hframe]]]].
  exists hbody, hframe; split; [exact Hjoin|]; split; [|exact Hframe].
  exact (event_create_private_store_merge sg entry eid allocation field value Hget Hfield hbody Hbody).
Qed.

Lemma event_create_publication_c_owner_segment : forall sg entry eid allocation node h frame,
  UCOS2_state_inv sg entry ->
  entry.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None ->
  (forall field, In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
    allocation.(eventPrivateStorage) field = event_image sg entry.(TskState) node field) ->
  node.(eventGeneration) = allocation.(eventPrivateGeneration) ->
  node.(eventType) <> OS_EVENT_TYPE_MUTEX -> node.(queueFields) = None -> node.(waitList) = nil ->
  event_fields_consistency node -> event_payload_consistency sg node ->
  event_name_valid sg entry.(NameState) node -> allocation.(eventPrivateMutexPCP) = None ->
  (event_creation_publication_owner sg entry eid allocation ** frame) h ->
  kernel_event_creation_c_segment sg entry h
    (event_creation_publication_owner sg entry eid allocation ** frame)
    (replace_EventS (event_publish entry.(EventState) eid node) entry) h
    (UCOS2_inv sg (replace_EventS (event_publish entry.(EventState) eid node) entry) ** frame).
Proof.
  intros sg entry eid allocation node h frame Hvalid Hget Hqueue Himage Hgeneration
    Hkind Hfields Hwait Hconsistent Hpayload Hname Hpcp Hpre.
  apply KernelEventCreationCPublishSegment; try assumption.
  destruct Hpre as [hbody [hframe [Hjoin [Hbody Hframe]]]].
  exists hbody, hframe; split; [exact Hjoin|]; split; [|exact Hframe].
  exact (UCOS2_inv_merge_event_publish sg entry eid allocation node Hvalid Hget Hqueue Himage
    Hgeneration Hkind Hfields Hwait Hconsistent Hpayload Hname Hpcp hbody Hbody).
Qed.

Lemma kernel_event_creation_c_segment_source : forall sg entry before input returned after output,
  kernel_event_creation_c_segment sg entry before input returned after output ->
  kernel_event_creation_c_source entry returned.
Proof.
  intros sg entry before input returned after output Hsegment; destruct Hsegment.
  - eapply KernelEventCreationCAllocateSource; eassumption.
  - eapply KernelEventCreationCStoreSource; eassumption.
  - eapply KernelEventCreationCPublishSource; eassumption.
  - eapply KernelEventCreationCAllocateSource; eassumption.
  - eapply KernelEventCreationCStoreSource; eassumption.
  - eapply KernelEventCreationCPublishSource; eassumption.
Qed.

Lemma kernel_event_creation_c_segment_resources : forall sg entry before input returned after output,
  kernel_event_creation_c_segment sg entry before input returned after output ->
  input before /\ output after.
Proof. intros sg entry before input returned after output Hsegment; destruct Hsegment; split; assumption. Qed.

Lemma kernel_event_creation_c_segment_preserves_observer :
  forall sg entry before input returned after output observer origin,
  kernel_event_creation_c_segment sg entry before input returned after output ->
  task_invocation_active entry.(TskState) observer origin /\ sched_observer_current_cache origin entry ->
  task_invocation_active returned.(TskState) observer origin /\ sched_observer_current_cache origin returned.
Proof.
  intros sg entry before input returned after output observer origin Hsegment [Hactive Hcache].
  pose proof (kernel_event_creation_c_segment_source _ _ _ _ _ _ _ Hsegment) as Hsource.
  destruct (kernel_event_creation_c_source_fields_eq _ _ Hsource) as [Htasks Hsched].
  split; [rewrite Htasks; exact Hactive|].
  destruct origin; [exact I|]; unfold sched_observer_current_cache in *; rewrite Htasks, Hsched; exact Hcache.
Qed.

Lemma kernel_event_creation_c_segment_lifetime_result :
  forall sg entry before input returned after output observer origin,
  kernel_event_creation_c_segment sg entry before input returned after output ->
  task_observer_lifetime_result observer origin entry.(TskState) returned.(TskState) false.
Proof.
  intros sg entry before input returned after output observer origin Hsegment.
  pose proof (kernel_event_creation_c_segment_source _ _ _ _ _ _ _ Hsegment) as Hsource.
  destruct (kernel_event_creation_c_source_fields_eq _ _ Hsource) as [Htasks Hsched].
  rewrite Htasks; apply task_observer_lifetime_result_not_stopped.
  apply task_observer_lifetime_transport_refl.
Qed.











End EventCreationComponent.

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
