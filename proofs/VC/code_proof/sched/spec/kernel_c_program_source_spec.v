(** Report-only ordinary module extracted from the frozen checked C context.
    The original proof bodies are retained under the recorded shared-reference map. *)
Require Import Coq.micromega.Lia.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_preparation_spec.
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
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
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
Module NamedSourceFrames.
Lemma kernel_task_creation_c_source_other_fields : forall sg entry returned,
  CreationComponent.kernel_task_creation_c_source sg entry returned ->
  returned.(EventState) = entry.(EventState) /\
  entry.(NameState) = returned.(NameState) /\ returned.(TimerState) = entry.(TimerState).
Proof.
  intros sg entry returned Hsource; destruct Hsource; try (repeat split; reflexivity).
  - unfold task_create_critical in H; destruct (Z.ltb 0 entry.(IntrState).(intNesting)).
    + destruct H as [_ ->]; repeat split; reflexivity.
    + destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority);
        destruct Hstep as [_ ->]; repeat split; reflexivity.
  - destruct H2 as [_ ->]; repeat split; reflexivity.
Qed.

Lemma task_create_critical_frames_other_call :
  forall sg priority invocation origin entry result returned observer,
  UCOS2_state_inv sg entry ->
  task_create_critical sg priority invocation origin entry result returned ->
  invocation <> observer -> task_creation_frame observer entry.(TskState) returned.(TskState).
Proof.
  intros sg priority invocation origin entry result returned observer Hvalid Hcode Hforeign.
  unfold task_create_critical in Hcode; destruct (Z.ltb 0 entry.(IntrState).(intNesting)).
  - destruct Hcode as [_ ->]; reflexivity.
  - destruct Hcode as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority) eqn:Htable;
      destruct Hstep as [_ ->]; try reflexivity.
    apply task_reserve_frames_other_invocation; [|exact Hforeign].
    pose proof (proj1 (proj2 Hvalid)) as Htasks.
    pose proof (proj1 (proj2 (proj2 (proj2 Htasks)))) as Hreservations.
    destruct (entry.(TskState).(taskLifecycle).(taskReservations) priority) as [reservation|] eqn:Hget;
      [|reflexivity].
    pose proof (proj1 Hreservations priority reservation Hget) as [_ [Hreserved _]].
    congruence.
Qed.

Lemma task_create_rollback_frames_other_call :
  forall critical sg args invocation origin initial released acquired result returned observer,
  task_tcb_init_result critical sg args invocation origin initial 66 released ->
  critical_region_interval critical sg invocation released acquired ->
  task_create_rollback_store args.(initPrio) acquired result returned ->
  invocation <> observer -> task_creation_frame observer acquired.(TskState) returned.(TskState).
Proof.
  intros critical sg args invocation origin initial released acquired result returned observer
    Hresult Hinterval Hstore Hforeign.
  destruct (task_create_no_free_rollback_store_client critical sg args invocation origin
    initial released acquired result returned Hresult Hinterval Hstore) as [Hguard ->].
  eapply task_rollback_frames_other_invocation; eassumption.
Qed.

Lemma task_tcb_init_detach_frames_other_call :
  forall args invocation origin entry slot rest image observer,
  task_tcb_init_detach_observation args invocation origin entry slot rest image ->
  invocation <> observer ->
  task_creation_frame observer entry.(TskState)
    (task_tcb_init_detached_state args invocation origin entry slot rest image).(TskState).
Proof.
  intros args invocation origin entry slot rest image observer Hdetach Hforeign.
  apply task_detach_frames_other_invocation; [exact (proj1 (proj2 Hdetach))|exact Hforeign].
Qed.

Lemma task_tcb_init_private_frames_other_call :
  forall sg args entry reservation allocation observer,
  entry.(TskState).(taskLifecycle).(taskReservations) args.(initPrio) = Some reservation ->
  reservation.(creationInvocation) <> observer ->
  task_creation_frame observer entry.(TskState)
    (task_tcb_init_initialize_private sg args entry.(TskState) reservation allocation).
Proof. intros; apply task_private_image_frames_other_invocation; assumption. Qed.

Lemma kernel_event_creation_c_source_other_fields : forall entry returned,
  EventCreationComponent.kernel_event_creation_c_source entry returned ->
  returned.(TskState) = entry.(TskState) /\
  entry.(NameState) = returned.(NameState) /\ returned.(TimerState) = entry.(TimerState).
Proof.
  intros entry returned Hsource; destruct Hsource; try (repeat split; reflexivity).
  unfold event_create_allocate_critical in H; destruct (entry.(EventState).(unUsedEventStates)).
  - destruct H as [_ ->]; repeat split; reflexivity.
  - destruct H as [image [_ [_ ->]]]; repeat split; reflexivity.
Qed.

Lemma event_create_allocate_frames_other_call : forall sg entry result returned observer,
  UCOS2_state_inv sg entry -> event_create_allocate_critical entry result returned ->
  entry.(EventState).(eventLifecycle).(eventNextInvocation) <> observer ->
  event_creation_frame observer entry.(EventState) returned.(EventState).
Proof.
  intros sg entry result returned observer Hvalid Hcode Hforeign.
  eapply kernel_client_frames_event_creation with
    (action := event_create_allocate_client None entry.(EventState).(eventLifecycle).(eventNextInvocation));
    [apply event_create_allocate_client_certificate|exact Hvalid| |].
  - split; [reflexivity|exists result; exact Hcode].
  - change (Some entry.(EventState).(eventLifecycle).(eventNextInvocation) <> Some observer); congruence.
Qed.

Lemma event_create_private_frames_other_call : forall entry eid allocation field value observer,
  entry.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateInvocation) <> observer ->
  event_creation_frame observer entry.(EventState)
    (replace_EventS (event_private_write entry.(EventState) eid allocation field (Some value)) entry).(EventState).
Proof. intros; apply event_private_write_frames_other_invocation; assumption. Qed.

Lemma event_create_publication_frames_other_call : forall entry eid allocation node observer,
  entry.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateInvocation) <> observer ->
  event_creation_frame observer entry.(EventState)
    (replace_EventS (event_publish entry.(EventState) eid node) entry).(EventState).
Proof. intros; eapply event_publish_frames_other_invocation; eassumption. Qed.

Lemma kernel_queue_creation_c_source_other_fields : forall sg entry returned,
  QueueCreationComponent.kernel_queue_creation_c_source sg entry returned ->
  returned.(TskState) = entry.(TskState) /\
  entry.(NameState) = returned.(NameState) /\ returned.(TimerState) = entry.(TimerState).
Proof.
  intros sg entry returned Hsource; destruct Hsource; [|repeat split; reflexivity].
  destruct H0 as [allocation [Hget Hcode]]; destruct free;
    destruct Hcode as [_ ->]; repeat split; reflexivity.
Qed.

Lemma q_create_reserve_frames_other_call :
  forall sg eid free entry result returned allocation observer,
  entry.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  q_create_reserve_critical sg eid free entry result returned ->
  allocation.(eventPrivateInvocation) <> observer ->
  event_creation_frame observer entry.(EventState) returned.(EventState).
Proof.
  intros sg eid free entry result returned allocation observer Hget [actual [Hactual Hcode]] Hforeign.
  assert (actual = allocation) by congruence; subst actual.
  destruct free; destruct Hcode as [_ ->].
  - eapply event_rollback_frames_other_invocation; eassumption.
  - eapply queue_reserve_frames_other_invocation; eassumption.
Qed.

Lemma q_create_publication_frames_other_call :
  forall entry eid allocation node qid slots observer,
  entry.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateInvocation) <> observer ->
  event_creation_frame observer entry.(EventState)
    (replace_EventS (queue_publish entry.(EventState) eid node qid slots) entry).(EventState).
Proof. intros; eapply queue_publish_frames_other_invocation; eassumption. Qed.

Lemma kernel_status_c_source_creation_frames : forall sg entry returned task_observer event_observer,
  StatusComponent.kernel_status_c_source sg entry returned ->
  task_creation_frame task_observer entry.(TskState) returned.(TskState) /\
  event_creation_frame event_observer entry.(EventState) returned.(EventState) /\
  entry.(NameState) = returned.(NameState) /\
  timer_public_trace sg entry.(TimerState) returned.(TimerState).
Proof.
  intros sg entry returned task_observer event_observer Hsource; destruct Hsource.
  - destruct H as [cid [current [_ [_ [_ Hstep]]]]].
    destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg priority current))).
    + destruct Hstep as [_ ->]; repeat split; try reflexivity; constructor.
    + destruct Hstep as [_ ->]; repeat split; try reflexivity; constructor.
    + destruct Hstep as [old [_ [_ ->]]]; repeat split; try reflexivity; constructor.
  - destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority).
    + destruct Hstep as [_ ->]; repeat split; try reflexivity; constructor.
    + destruct Hstep as [_ ->]; repeat split; try reflexivity; constructor.
    + destruct Hstep as [old [_ Hstep]]; destruct (task_is_suspended old.(stat)).
      * destruct Hstep as [_ ->].
        unfold task_resume_state, sched_resume_task, sched_wake_by_status;
          cbn [replace_SchedS replace_TskS];
          repeat match goal with |- context [if ?c then _ else _] => destruct c end;
          repeat split; try reflexivity; constructor.
      * destruct Hstep as [_ ->]; repeat split; try reflexivity; constructor.
  - destruct H as [event [fields [_ [_ [_ ->]]]]]; destruct (Z.ltb 0 fields.(semCount));
      repeat split; try reflexivity; constructor.
Qed.

Lemma kernel_wake_c_source_creation_frames : forall sg entry returned task_observer event_observer,
  WakeComponent.kernel_wake_c_source sg entry returned ->
  task_creation_frame task_observer entry.(TskState) returned.(TskState) /\
  event_creation_frame event_observer entry.(EventState) returned.(EventState) /\
  entry.(NameState) = returned.(NameState) /\
  timer_public_trace sg entry.(TimerState) returned.(TimerState).
Proof.
  intros sg entry returned task_observer event_observer Hsource; destruct Hsource.
  - destruct (flag_task_rdy_result _ _ _ _ _ _ _ H)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]].
    repeat split; try reflexivity; constructor.
  - unfold event_task_rdy in H.
    destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
    destruct (entry.(TskState).(prioTbl) (event_wait_priority entry.(TskState) event))
      as [| |slot]; try discriminate.
    destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|]; [|discriminate].
    injection H as Hpriority Hreturned; subst returned.
    repeat split; try reflexivity; constructor.
  - split.
    + rewrite (tick_task_step_task_state_eq sg slot old entry H); reflexivity.
    + unfold tick_task_step, sched_wake_by_status; cbn zeta;
        repeat match goal with |- context [if ?c then _ else _] => destruct c end;
        repeat split; try reflexivity; constructor.
Qed.

End NamedSourceFrames.
(** Sources decorate the original C completion proof.  They retain the
    invocation/allocation from that completion; no constructor assumes any
    creation-frame, cache, ready or future-return conclusion. *)
Import EventStateDef.

Inductive kernel_task_creation_c_segment_source (sg : StableGlobVars) (observer : nat) :
  forall state before input returned after output,
  CreationComponent.kernel_task_creation_c_segment sg state before input returned after output -> Prop :=
| KernelTaskCreationCBeginSourceAt : forall state caller h frame Hgeneration Hlive Hpre Hpost,
    kernel_task_creation_c_segment_source sg observer _ _ _ _ _ _
      (@CreationComponent.KernelTaskCreationCBeginSegment sg state caller h frame
        Hgeneration Hlive Hpre Hpost)
| KernelTaskCreationCCriticalSourceAt : forall state priority invocation caller result returned before after frame
    Hcode Hpre Hpost,
    invocation <> observer ->
    kernel_task_creation_c_segment_source sg observer _ _ _ _ _ _
      (@CreationComponent.KernelTaskCreationCCriticalSegment sg state priority invocation caller result
        returned before after frame Hcode Hpre Hpost)
| KernelTaskCreationCRollbackSourceAt : forall critical args invocation caller initial released state result
    returned before after frame Hentry Hresult Hwindow Hstore Hpre Hpost,
    invocation <> observer ->
    kernel_task_creation_c_segment_source sg observer _ _ _ _ _ _
      (@CreationComponent.KernelTaskCreationCRollbackSegment sg critical args invocation caller initial
        released state result returned before after frame Hentry Hresult Hwindow Hstore Hpre Hpost)
| KernelTaskCreationCDetachSourceAt : forall args invocation caller state slot rest image before after frame
    Hentry Hdetach Hpre Hpost,
    invocation <> observer ->
    kernel_task_creation_c_segment_source sg observer _ _ _ _ _ _
      (@CreationComponent.KernelTaskCreationCDetachSegment sg args invocation caller state slot rest image
        before after frame Hentry Hdetach Hpre Hpost)
| KernelTaskCreationCPrivateSourceAt : forall args state reservation allocation before after frame
    Hget Hallocation Hpre Hpost,
    reservation.(creationInvocation) <> observer ->
    kernel_task_creation_c_segment_source sg observer _ _ _ _ _ _
      (@CreationComponent.KernelTaskCreationCPrivateSegment sg args state reservation allocation
        before after frame Hget Hallocation Hpre Hpost)
| KernelTaskCreationCPrepareFieldsSourceAt : forall input slot rest image before after frame
    Hfacts Hnest Hfree Hdetach Hrun Hpre Hpost,
    input.(stack_input_call).(os_sched_call_invocation) <> observer ->
    kernel_task_creation_c_segment_source sg observer _ _ _ _ _ _
      (@CreationComponent.KernelTaskCreationCPrepareFieldsSegment sg input slot rest image before after
        frame Hfacts Hnest Hfree Hdetach Hrun Hpre Hpost).

Lemma kernel_task_creation_c_segment_source_frame :
  forall sg observer state before input returned after output
    (Hsegment : CreationComponent.kernel_task_creation_c_segment sg state before input returned after output),
  kernel_task_creation_c_segment_source sg observer state before input returned after output Hsegment ->
  task_creation_frame observer state.(TskState) returned.(TskState).
Proof.
  intros sg observer state before input returned after output Hsegment Hsource.
  destruct Hsource as
    [state caller h frame Hgeneration Hlive Hpre Hpost
    |state priority invocation caller result returned before after frame Hcode Hpre Hpost Hforeign
    |critical args invocation caller initial released state result returned before after frame
      Hentry Hresult Hwindow Hstore Hpre Hpost Hforeign
    |args invocation caller state slot rest image before after frame Hentry Hdetach Hpre Hpost Hforeign
    |args state reservation allocation before after frame Hget Hallocation Hpre Hpost Hforeign
    |input slot rest image before after frame Hfacts Hnest Hfree Hdetach Hrun Hpre Hpost Hforeign].
  - reflexivity.
  - assert (Hvalid : UCOS2_state_inv sg state).
    { destruct Hpre as [hbody [hframe [Hjoin [[Hvalid Hraw] Hframe]]]]; exact Hvalid. }
    eapply NamedSourceFrames.task_create_critical_frames_other_call; eassumption.
  - eapply NamedSourceFrames.task_create_rollback_frames_other_call; eassumption.
  - eapply NamedSourceFrames.task_tcb_init_detach_frames_other_call; eassumption.
  - eapply NamedSourceFrames.task_tcb_init_private_frames_other_call; eassumption.
  - pose proof Hfacts as [Hentry [Hbasic [Hpriority Hrest]]].
    assert (Hcode : task_create_critical sg input.(stack_input_args).(createPriority)
      input.(stack_input_call).(os_sched_call_invocation) input.(stack_input_call).(os_sched_call_origin)
      input.(stack_input_state) None (task_create_stack_input_acquired input)).
    { unfold task_create_critical; rewrite Hnest; cbn [Z.ltb]; rewrite Hfree.
      split; [exact Hpriority|]. split; reflexivity. }
    pose proof (NamedSourceFrames.task_create_critical_frames_other_call _ _ _ _ _ _ _ _
      (proj1 Hentry) Hcode Hforeign) as Hreserve.
    pose proof (NamedSourceFrames.task_tcb_init_detach_frames_other_call _ _ _ _ _ _ _ _
      Hdetach Hforeign) as Hdetach_frame.
    unfold task_creation_frame in *; etransitivity; eassumption.
Qed.

Inductive kernel_event_creation_c_segment_source (sg : StableGlobVars) (observer : option nat) :
  forall state before input returned after output,
  EventCreationComponent.kernel_event_creation_c_segment sg state before input returned after output -> Prop :=
| KernelEventCreationCAllocateSourceAt : forall state result returned before after frame Hcode Hpre Hpost,
    (forall invocation, observer = Some invocation ->
      state.(EventState).(eventLifecycle).(eventNextInvocation) <> invocation) ->
    kernel_event_creation_c_segment_source sg observer _ _ _ _ _ _
      (@EventCreationComponent.KernelEventCreationCAllocateSegment sg state result returned before after
        frame Hcode Hpre Hpost)
| KernelEventCreationCStoreSourceAt : forall state eid allocation field value before after frame
    Hget Hfield Hpre Hpost,
    (forall invocation, observer = Some invocation -> allocation.(eventPrivateInvocation) <> invocation) ->
    kernel_event_creation_c_segment_source sg observer _ _ _ _ _ _
      (@EventCreationComponent.KernelEventCreationCStoreSegment sg state eid allocation field value before after
        frame Hget Hfield Hpre Hpost)
| KernelEventCreationCPublishSourceAt : forall state eid allocation node h frame Hget Hname Hkind Hpre Hpost,
    (forall invocation, observer = Some invocation -> allocation.(eventPrivateInvocation) <> invocation) ->
    kernel_event_creation_c_segment_source sg observer _ _ _ _ _ _
      (@EventCreationComponent.KernelEventCreationCPublishSegment sg state eid allocation node h frame
        Hget Hname Hkind Hpre Hpost)
| KernelEventCreationCAllocateFieldsSourceAt : forall state result returned before after frame
    Hread Hcode Hrun Hpre Hpost,
    (forall invocation, observer = Some invocation ->
      state.(EventState).(eventLifecycle).(eventNextInvocation) <> invocation) ->
    kernel_event_creation_c_segment_source sg observer _ _ _ _ _ _
      (@EventCreationComponent.KernelEventCreationCAllocateFieldsSegment sg state result returned before after
        frame Hread Hcode Hrun Hpre Hpost)
| KernelEventCreationCStoreFieldsSourceAt : forall state eid allocation field value final before after frame
    Hget Hfield Hfinal Hrun Hpre Hpost,
    (forall invocation, observer = Some invocation -> allocation.(eventPrivateInvocation) <> invocation) ->
    kernel_event_creation_c_segment_source sg observer _ _ _ _ _ _
      (@EventCreationComponent.KernelEventCreationCStoreFieldsSegment sg state eid allocation field value final before after
        frame Hget Hfield Hfinal Hrun Hpre Hpost)
| KernelEventCreationCPublishFieldsSourceAt : forall state eid allocation node h frame Hget Hname Hkind Hpre Hpost,
    (forall invocation, observer = Some invocation -> allocation.(eventPrivateInvocation) <> invocation) ->
    kernel_event_creation_c_segment_source sg observer _ _ _ _ _ _
      (@EventCreationComponent.KernelEventCreationCPublishFieldsSegment sg state eid allocation node h frame
        Hget Hname Hkind Hpre Hpost).

Lemma kernel_event_creation_c_segment_source_frame :
  forall sg observer state before input returned after output
    (Hsegment : EventCreationComponent.kernel_event_creation_c_segment sg state before input returned after output),
  kernel_event_creation_c_segment_source sg observer state before input returned after output Hsegment ->
  forall invocation, observer = Some invocation ->
    event_creation_frame invocation state.(EventState) returned.(EventState).
Proof.
  intros sg observer state before input returned after output Hsegment Hsource invocation Hobserver.
  destruct Hsource as
    [state result returned before after frame Hcode Hpre Hpost Hforeign
    |state eid allocation field value before after frame Hget Hfield Hpre Hpost Hforeign
    |state eid allocation node h frame Hget Hname Hkind Hpre Hpost Hforeign
    |state result returned before after frame Hread Hcode Hrun Hpre Hpost Hforeign
    |state eid allocation field value final before after frame Hget Hfield Hfinal Hrun Hpre Hpost Hforeign
    |state eid allocation node h frame Hget Hname Hkind Hpre Hpost Hforeign].
  - assert (Hvalid : UCOS2_state_inv sg state).
    { destruct Hpre as [hbody [hframe [Hjoin [[Hvalid Hraw] Hframe]]]]; exact Hvalid. }
    eapply NamedSourceFrames.event_create_allocate_frames_other_call; [exact Hvalid|exact Hcode|].
    exact (Hforeign invocation Hobserver).
  - eapply NamedSourceFrames.event_create_private_frames_other_call;
      [exact Hget|exact (Hforeign invocation Hobserver)].
  - eapply NamedSourceFrames.event_create_publication_frames_other_call;
      [exact Hget|exact (Hforeign invocation Hobserver)].
  - assert (Hvalid : UCOS2_state_inv sg state).
    { destruct Hpre as [hbody [hframe [Hjoin [[Hvalid Hraw] Hframe]]]]; exact Hvalid. }
    eapply NamedSourceFrames.event_create_allocate_frames_other_call; [exact Hvalid|exact Hcode|].
    exact (Hforeign invocation Hobserver).
  - eapply NamedSourceFrames.event_create_private_frames_other_call;
      [exact Hget|exact (Hforeign invocation Hobserver)].
  - eapply NamedSourceFrames.event_create_publication_frames_other_call;
      [exact Hget|exact (Hforeign invocation Hobserver)].
Qed.

Inductive kernel_queue_creation_c_segment_source (sg : StableGlobVars) (observer : option nat) :
  forall state before input returned after output,
  QueueCreationComponent.kernel_queue_creation_c_segment sg state before input returned after output -> Prop :=
| KernelQueueCreationCReserveSourceAt : forall state eid allocation qid rest before after frame
    Hpool Hcode Hpre Hpost,
    state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
    (forall invocation, observer = Some invocation -> allocation.(eventPrivateInvocation) <> invocation) ->
    kernel_queue_creation_c_segment_source sg observer _ _ _ _ _ _
      (@QueueCreationComponent.KernelQueueCreationCReserveSegment sg state eid allocation qid rest
        before after frame Hpool Hcode Hpre Hpost)
| KernelQueueCreationCRollbackSourceAt : forall state eid allocation before after frame Hpool Hcode Hpre Hpost,
    state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
    (forall invocation, observer = Some invocation -> allocation.(eventPrivateInvocation) <> invocation) ->
    kernel_queue_creation_c_segment_source sg observer _ _ _ _ _ _
      (@QueueCreationComponent.KernelQueueCreationCRollbackSegment sg state eid allocation before after frame
        Hpool Hcode Hpre Hpost)
| KernelQueueCreationCPublishSourceAt : forall state free eid allocation qid image start size slots name h frame
    Hpool Hget Hqueue Hname Hpre Hpost,
    (forall invocation, observer = Some invocation -> allocation.(eventPrivateInvocation) <> invocation) ->
    kernel_queue_creation_c_segment_source sg observer _ _ _ _ _ _
      (@QueueCreationComponent.KernelQueueCreationCPublishSegment sg state free eid allocation qid image
        start size slots name h frame Hpool Hget Hqueue Hname Hpre Hpost).

Lemma kernel_queue_creation_c_segment_source_frame :
  forall sg observer state before input returned after output
    (Hsegment : QueueCreationComponent.kernel_queue_creation_c_segment sg state before input returned after output),
  kernel_queue_creation_c_segment_source sg observer state before input returned after output Hsegment ->
  forall invocation, observer = Some invocation ->
    event_creation_frame invocation state.(EventState) returned.(EventState).
Proof.
  intros sg observer state before input returned after output Hsegment Hsource invocation Hobserver.
  destruct Hsource as
    [state eid allocation qid rest before after frame Hpool Hcode Hpre Hpost Hget Hforeign
    |state eid allocation before after frame Hpool Hcode Hpre Hpost Hget Hforeign
    |state free eid allocation qid image start size slots name h frame Hpool Hget Hqueue Hname Hpre Hpost Hforeign].
  - eapply NamedSourceFrames.q_create_reserve_frames_other_call;
      [exact Hget|exact Hcode|exact (Hforeign invocation Hobserver)].
  - eapply NamedSourceFrames.q_create_reserve_frames_other_call;
      [exact Hget|exact Hcode|exact (Hforeign invocation Hobserver)].
  - eapply NamedSourceFrames.q_create_publication_frames_other_call;
      [exact Hget|exact (Hforeign invocation Hobserver)].
Qed.

Section KernelProgramCStepSources.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (observer : nat) (observer_origin : TaskInvocationOrigin)
  (event_observer : option nat).

Inductive kernel_program_c_step_source :
  forall state before input stopped returned after output,
  kernel_program_c_step environment critical sg observer observer_origin
    state before input stopped returned after output -> Prop :=
| KernelProgramCWakeSource : forall state before input returned after output Hsegment,
    kernel_program_c_step_source _ _ _ _ _ _ _
      (@KernelProgramCWake environment critical sg observer observer_origin
        state before input returned after output Hsegment)
| KernelProgramCStatusSource : forall state before returned after frame Hsegment,
    kernel_program_c_step_source _ _ _ _ _ _ _
      (@KernelProgramCStatus environment critical sg observer observer_origin
        state before returned after frame Hsegment)
| KernelProgramCTaskCreationSource : forall state before input returned after output Hsegment,
    kernel_task_creation_c_segment_source sg observer state before input returned after output Hsegment ->
    kernel_program_c_step_source _ _ _ _ _ _ _
      (@KernelProgramCTaskCreation environment critical sg observer observer_origin
        state before input returned after output Hsegment)
| KernelProgramCEventCreationSource : forall state before input returned after output Hsegment,
    kernel_event_creation_c_segment_source sg event_observer state before input returned after output Hsegment ->
    kernel_program_c_step_source _ _ _ _ _ _ _
      (@KernelProgramCEventCreation environment critical sg observer observer_origin
        state before input returned after output Hsegment)
| KernelProgramCQueueCreationSource : forall state before input returned after output Hsegment,
    kernel_queue_creation_c_segment_source sg event_observer state before input returned after output Hsegment ->
    kernel_program_c_step_source _ _ _ _ _ _ _
      (@KernelProgramCQueueCreation environment critical sg observer observer_origin
        state before input returned after output Hsegment).

Lemma kernel_program_c_step_source_frames :
  forall state before input stopped returned after output
    (Hstep : kernel_program_c_step environment critical sg observer observer_origin
      state before input stopped returned after output),
  kernel_program_c_step_source state before input stopped returned after output Hstep ->
  task_creation_frame observer state.(TskState) returned.(TskState) /\
  (forall invocation, event_observer = Some invocation ->
    event_creation_frame invocation state.(EventState) returned.(EventState)) /\
  state.(NameState) = returned.(NameState) /\
  timer_public_trace sg state.(TimerState) returned.(TimerState).
Proof.
  intros state before input stopped returned after output Hstep Hsource; destruct Hsource.
  - pose proof (WakeComponent.kernel_wake_c_segment_source _ _ _ _ _ _ _ Hsegment) as Hcode.
    pose proof (NamedSourceFrames.kernel_wake_c_source_creation_frames sg _ _ observer 0%nat Hcode)
      as [Htask [_ [Hname Htimer]]].
    split; [exact Htask|]. split; [|split; assumption].
    intros invocation _; exact (proj1 (proj2
      (NamedSourceFrames.kernel_wake_c_source_creation_frames sg _ _ observer invocation Hcode))).
  - pose proof (StatusComponent.kernel_status_c_segment_code _ _ _ _ _ _ Hsegment) as Hcode.
    pose proof (NamedSourceFrames.kernel_status_c_source_creation_frames sg _ _ observer 0%nat Hcode)
      as [Htask [_ [Hname Htimer]]].
    split; [exact Htask|]. split; [|split; assumption].
    intros invocation _; exact (proj1 (proj2
      (NamedSourceFrames.kernel_status_c_source_creation_frames sg _ _ observer invocation Hcode))).
  - pose proof (CreationComponent.kernel_task_creation_c_segment_source _ _ _ _ _ _ _ Hsegment) as Hcode.
    destruct (NamedSourceFrames.kernel_task_creation_c_source_other_fields _ _ _ Hcode) as [Hevent [Hname Htimer]].
    split; [eapply kernel_task_creation_c_segment_source_frame; eassumption|].
    split; [intros; rewrite Hevent; reflexivity|]. split; [exact Hname|rewrite Htimer; constructor].
  - pose proof (EventCreationComponent.kernel_event_creation_c_segment_source _ _ _ _ _ _ _ Hsegment) as Hcode.
    destruct (NamedSourceFrames.kernel_event_creation_c_source_other_fields _ _ Hcode) as [Htask [Hname Htimer]].
    split; [rewrite Htask; reflexivity|].
    split; [eapply kernel_event_creation_c_segment_source_frame; eassumption|].
    split; [exact Hname|rewrite Htimer; constructor].
  - pose proof (QueueCreationComponent.kernel_queue_creation_c_segment_source _ _ _ _ _ _ _ Hsegment) as Hcode.
    destruct (NamedSourceFrames.kernel_queue_creation_c_source_other_fields _ _ _ Hcode) as [Htask [Hname Htimer]].
    split; [rewrite Htask; reflexivity|].
    split; [eapply kernel_queue_creation_c_segment_source_frame; eassumption|].
    split; [exact Hname|rewrite Htimer; constructor].
Qed.
End KernelProgramCStepSources.

Module TaskDeleteCompletedMacro.
Import DeleteComponent.
Lemma task_delete_prepare_single_wait_metadata_frame :
  forall before tid node prepared loan,
  task_delete_prepare_single_wait before tid node = Some (prepared, loan) ->
  prepared.(TskState).(taskLifecycle) = before.(TskState).(taskLifecycle) /\
  prepared.(EventState).(eventLifecycle) = before.(EventState).(eventLifecycle) /\
  prepared.(NameState) = before.(NameState) /\
  prepared.(TimerState) = before.(TimerState) /\
  prepared.(SchedState).(curTaskID) = before.(SchedState).(curTaskID).
Proof.
  intros before tid node prepared loan Hprepare.
  unfold task_delete_prepare_single_wait in Hprepare.
  destruct node.(eventPtr) as [eid|];
    [destruct (before.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate]|];
    cbn [task_set_event_ptr tcbFlagNode] in Hprepare;
    destruct (Z.eqb node.(tcbFlagNode) 0);
    try (destruct (flag.flag_unlink_node before.(FlagState) node.(tcbFlagNode))
      as [[waiter flags]|]; [|discriminate]);
    inversion Hprepare; subst;
    repeat split; reflexivity.
Qed.
End TaskDeleteCompletedMacro.

Module TaskDeletePhaseFrames.
Import DeleteComponent TaskDeleteCompletedMacro.
Lemma task_delete_prepare_c_creation_name_timer_frames :
  forall inputs before_heap prepared_heap,
  task_delete_prepare_c_completion inputs before_heap prepared_heap ->
  (forall observer, task_creation_frame observer inputs.(delete_capture_acquired).(TskState)
    (task_delete_locked inputs.(delete_capture_prepared)).(TskState)) /\
  (forall observer, event_creation_frame observer inputs.(delete_capture_acquired).(EventState)
    (task_delete_locked inputs.(delete_capture_prepared)).(EventState)) /\
  inputs.(delete_capture_acquired).(NameState) =
    (task_delete_locked inputs.(delete_capture_prepared)).(NameState) /\
  inputs.(delete_capture_acquired).(TimerState) =
    (task_delete_locked inputs.(delete_capture_prepared)).(TimerState).
Proof.
  intros inputs before_heap prepared_heap [Hpreparation Hbefore Hafter].
  destruct Hpreparation as [Hlive [Hprepare Hprotocol]].
  destruct (task_delete_prepare_single_wait_metadata_frame _ _ _ _ _ Hprepare)
    as [Htasks [Hevents [Hname [Htimer Hcurrent]]]].
  unfold task_delete_locked; split.
  - intro observer; unfold task_creation_frame, task_creation_view; cbn; rewrite Htasks; reflexivity.
  - split.
    + intro observer; unfold event_creation_frame, event_creation_view; cbn; rewrite Hevents; reflexivity.
    + split; cbn; symmetry; assumption.
Qed.
Lemma task_delete_recycle_c_creation_name_timer_frames : forall capture,
  (forall observer, task_creation_frame observer capture.(delete_save_resumed).(TskState)
    (task_delete_capture_cut capture).(TskState)) /\
  (forall observer, event_creation_frame observer capture.(delete_save_resumed).(EventState)
    (task_delete_capture_cut capture).(EventState)) /\
  capture.(delete_save_resumed).(NameState) = (task_delete_capture_cut capture).(NameState) /\
  capture.(delete_save_resumed).(TimerState) = (task_delete_capture_cut capture).(TimerState).
Proof.
  intros capture; unfold task_delete_capture_cut, task_delete_cut, task_delete_recycled.
  split; [intro observer; unfold task_creation_frame, task_creation_view; reflexivity|].
  split; [intro observer; unfold event_creation_frame, event_creation_view; reflexivity|].
  split; reflexivity.
Qed.
Lemma task_delete_own_c_segment_creation_name_timer_frames :
  forall environment critical sg observer origin state before input stopped returned after output,
  task_delete_own_c_segment environment critical sg observer origin
    state before input stopped returned after output ->
  (forall invocation, task_creation_frame invocation state.(TskState) returned.(TskState)) /\
  (forall invocation, event_creation_frame invocation state.(EventState) returned.(EventState)) /\
  state.(NameState) = returned.(NameState) /\ state.(TimerState) = returned.(TimerState).
Proof.
  intros environment critical sg observer origin state before input stopped returned after output Hstep.
  destruct Hstep as [inputs before_heap prepared_heap Hcontext Hcompleted|capture after_heap Hcontext Hcompleted].
  - exact (task_delete_prepare_c_creation_name_timer_frames inputs before_heap prepared_heap Hcompleted).
  - exact (task_delete_recycle_c_creation_name_timer_frames capture).
Qed.
Lemma task_delete_primitive_c_segment_creation_name_timer_frames :
  forall environment critical sg state before input stopped returned after output,
  task_delete_primitive_c_segment environment critical sg
    state before input stopped returned after output ->
  (forall invocation, task_creation_frame invocation state.(TskState) returned.(TskState)) /\
  (forall invocation, event_creation_frame invocation state.(EventState) returned.(EventState)) /\
  state.(NameState) = returned.(NameState) /\ state.(TimerState) = returned.(TimerState).
Proof.
  intros environment critical sg state before input stopped returned after output Hstep; destruct Hstep;
    (split; [intro invocation; unfold task_creation_frame; reflexivity|];
     split; [intro invocation; unfold event_creation_frame; reflexivity|]; split; reflexivity).
Qed.
End TaskDeletePhaseFrames.
Import EventStateDef.

Lemma kernel_critical_c_source_creation_frames : forall sg call observer,
  CriticalComponent.kernel_critical_c_source sg call ->
  task_creation_frame observer (CriticalComponent.kernel_critical_c_entry call).(TskState)
    (CriticalComponent.kernel_critical_c_returned call).(TskState) /\
  (forall event_observer, event_creation_frame event_observer
    (CriticalComponent.kernel_critical_c_entry call).(EventState)
    (CriticalComponent.kernel_critical_c_returned call).(EventState)) /\
  (CriticalComponent.kernel_critical_c_entry call).(NameState) =
    (CriticalComponent.kernel_critical_c_returned call).(NameState) /\
  timer_public_trace sg (CriticalComponent.kernel_critical_c_entry call).(TimerState)
    (CriticalComponent.kernel_critical_c_returned call).(TimerState).
Proof.
  intros sg [actual|actual] observer Hsource; cbn in Hsource |- *.
  - destruct Hsource as [error [Hcritical Hcode]].
    destruct (CriticalComponent.task_change_prio_critical_creation_name_frames
      _ _ _ _ _ _ observer 0%nat Hcritical) as [Htask [_ Hname]].
    pose proof (proj2 (CriticalComponent.task_change_prio_critical_current_timer_frame
      _ _ _ _ _ _ Hcritical)) as Htimer.
    split; [exact Htask|]. split.
    + intro invocation; exact (proj1 (proj2
        (CriticalComponent.task_change_prio_critical_creation_name_frames
          _ _ _ _ _ _ observer invocation Hcritical))).
    + split; [exact Hname|rewrite Htimer; constructor].
  - unfold CriticalComponent.mutex_del_critical_fields_observation in Hsource.
    destruct (CriticalComponent.mutex_del_critical_call_observation_fields
      _ _ _ _ _ _ _ _ Hsource) as [[Hnodes [Hstacks [Hlife [Hcurrent Hprivate]]]] [Hname Htimer]].
    split.
    + unfold task_creation_frame, task_creation_view; rewrite Hlife; reflexivity.
    + split.
      * intro invocation; unfold event_creation_frame, event_creation_view; rewrite Hprivate; reflexivity.
      * split; [exact Hname|rewrite Htimer; constructor].
Qed.

Lemma mutex_pend_inheritance_c_source_creation_frames : forall sg call observer,
  PendComponent.mutex_pend_inheritance_c_source sg call ->
  task_creation_frame observer call.(PendComponent.mutex_pend_inheritance_entry).(TskState)
    call.(PendComponent.mutex_pend_inheritance_returned).(TskState) /\
  (forall event_observer, event_creation_frame event_observer
    call.(PendComponent.mutex_pend_inheritance_entry).(EventState)
    call.(PendComponent.mutex_pend_inheritance_returned).(EventState)) /\
  call.(PendComponent.mutex_pend_inheritance_entry).(NameState) =
    call.(PendComponent.mutex_pend_inheritance_returned).(NameState) /\
  timer_public_trace sg call.(PendComponent.mutex_pend_inheritance_entry).(TimerState)
    call.(PendComponent.mutex_pend_inheritance_returned).(TimerState).
Proof.
  intros sg call observer [Hnode [Hnonowner Hstep]].
  unfold mutex_pend_inherit_step in Hstep.
  destruct (mutex_pend_inherit_action sg.(osPrioMutexCeilDis)
    call.(PendComponent.mutex_pend_inheritance_base)
    call.(PendComponent.mutex_pend_inheritance_node).(curPrio)
    call.(PendComponent.mutex_pend_inheritance_waiter)
    call.(PendComponent.mutex_pend_inheritance_ceiling)).
  - rewrite Hstep; split; [reflexivity|]. split; [intros; reflexivity|].
    split; [reflexivity|constructor].
  - rewrite Hstep; split; [reflexivity|]. split; [intros; reflexivity|].
    split; [reflexivity|constructor].
  - destruct Hstep as [events [Hevents Hstep]].
    unfold mutex_pend_promoted_events in Hevents.
    destruct (mutex_pend_owner_was_ready call.(PendComponent.mutex_pend_inheritance_entry)
      call.(PendComponent.mutex_pend_inheritance_node)).
    + rewrite Hstep, Hevents; split; [reflexivity|]. split; [intros; reflexivity|].
      split; [reflexivity|constructor].
    + destruct call.(PendComponent.mutex_pend_inheritance_node).(eventPtr).
      * destruct Hevents as [old [Hget Hevents]].
        rewrite Hstep, Hevents; split; [reflexivity|]. split; [intros; reflexivity|].
        split; [reflexivity|constructor].
      * rewrite Hstep, Hevents; split; [reflexivity|]. split; [intros; reflexivity|].
        split; [reflexivity|constructor].
Qed.

Lemma mutex_post_prepare_name_timer_fields : forall sg mutex owner entry prepared,
  mutex_post_prepare sg mutex owner entry prepared ->
  entry.(NameState) = prepared.(NameState) /\ entry.(TimerState) = prepared.(TimerState).
Proof.
  intros sg mutex owner entry prepared Hprepare; unfold mutex_post_prepare in Hprepare.
  destruct Z.eq_dec; [subst; split; reflexivity|].
  destruct Hprepare as [node [priority [_ [_ ->]]]].
  unfold mutex_post_owner_priority_state; destruct Z.eq_dec; split; reflexivity.
Qed.

Lemma mutex_post_critical_name_timer_fields : forall sg eid caller entry result schedule checkpoint,
  mutex_post_critical sg eid caller entry result schedule checkpoint ->
  entry.(NameState) = checkpoint.(NameState) /\ entry.(TimerState) = checkpoint.(TimerState).
Proof.
  intros sg eid caller entry result schedule checkpoint Hcritical; destruct Hcritical.
  - split; reflexivity.
  - change (entry.(NameState) = prepared.(NameState) /\ entry.(TimerState) = prepared.(TimerState)).
    eapply mutex_post_prepare_name_timer_fields; eassumption.
  - change (entry.(NameState) = woken.(NameState) /\ entry.(TimerState) = woken.(TimerState)).
    destruct (mutex_post_prepare_name_timer_fields _ _ _ _ _ H3) as [Hname Htimer].
    destruct (CriticalComponent.mutex_del_wake_name_timer_frame _ _ _ _ _ _ _ _ H5)
      as [Hname' Htimer']; split; congruence.
Qed.

Lemma mutex_post_critical_c_source_creation_frames : forall sg call observer,
  PostComponent.mutex_post_critical_c_source sg call ->
  task_creation_frame observer call.(PostComponent.mutex_post_critical_entry).(TskState)
    call.(PostComponent.mutex_post_critical_checkpoint).(TskState) /\
  (forall event_observer, event_creation_frame event_observer
    call.(PostComponent.mutex_post_critical_entry).(EventState)
    call.(PostComponent.mutex_post_critical_checkpoint).(EventState)) /\
  call.(PostComponent.mutex_post_critical_entry).(NameState) =
    call.(PostComponent.mutex_post_critical_checkpoint).(NameState) /\
  timer_public_trace sg call.(PostComponent.mutex_post_critical_entry).(TimerState)
    call.(PostComponent.mutex_post_critical_checkpoint).(TimerState).
Proof.
  intros sg call observer [Hcaller Hcritical].
  destruct (mutex_post_critical_call_fields_eq _ _ _ _ _ _ _ Hcritical)
    as [Hnodes [Hstacks [Hlife [Hcurrent Hprivate]]]].
  destruct (mutex_post_critical_name_timer_fields _ _ _ _ _ _ _ Hcritical) as [Hname Htimer].
  split.
  - unfold task_creation_frame, task_creation_view; rewrite Hlife; reflexivity.
  - split.
    + intro invocation; unfold event_creation_frame, event_creation_view; rewrite Hprivate; reflexivity.
    + split; [exact Hname|rewrite Htimer; constructor].
Qed.

Lemma task_install_c_step_creation_frames :
  forall environment local sg observer state before input stopped returned after output,
  InstallComponent.task_install_c_step environment local sg
    state before input stopped returned after output ->
  task_creation_frame observer state.(TskState) returned.(TskState) /\
  (forall event_observer, event_creation_frame event_observer state.(EventState) returned.(EventState)) /\
  state.(NameState) = returned.(NameState) /\ timer_public_trace sg state.(TimerState) returned.(TimerState).
Proof.
  intros environment local sg observer state before input stopped returned after output Hstep.
  destruct Hstep as [frame call before after sp Hactual [Hsource Hcompletion]].
  destruct (os_sched_install_client_state_frame environment.(task_stack_call_external)
    call.(InstallComponent.task_install_fields_context) call.(InstallComponent.task_install_fields_outgoing)
    call.(InstallComponent.task_install_fields_incoming) call.(InstallComponent.task_install_fields_resumed)
    sg call.(InstallComponent.task_install_fields_entry) (InstallComponent.task_install_fields_current call) Hsource)
    as [Hnodes [Hlife [Hevent [Hrunning [Hinterrupt [Hname Htimer]]]]]].
  split.
  - unfold task_creation_frame, task_creation_view; rewrite Hlife; reflexivity.
  - split; [intros; rewrite Hevent; reflexivity|]. split; [symmetry; exact Hname|rewrite Htimer; constructor].
Qed.

Section KernelBuiltinCSource.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (local : Armv7aContinuation -> Assertion) (sg : StableGlobVars) (observer : nat).

Inductive kernel_builtin_c_segment_source :
  forall state before returned after input output,
  BuiltinComponent.kernel_builtin_c_segment environment critical local sg
    state before returned after input output -> Prop :=
| KernelBuiltinCCounterSourceAt : forall operation state frame before after code Hcompletion,
    kernel_builtin_c_segment_source _ _ _ _ _ _
      (@BuiltinComponent.KernelBuiltinCCounter environment critical local sg operation state frame before after
        code Hcompletion)
| KernelBuiltinCPublicationSourceAt : forall publication state frame before after code effect Hcompletion,
    publication.(stack_publication_invocation) <> observer ->
    kernel_builtin_c_segment_source _ _ _ _ _ _
      (@BuiltinComponent.KernelBuiltinCPublication environment critical local sg publication state frame
        before after code effect Hcompletion)
| KernelBuiltinCIRQTransferSourceAt : forall handler saved entry transfer frame before after Hcompletion,
    kernel_builtin_c_segment_source _ _ _ _ _ _
      (@BuiltinComponent.KernelBuiltinCIRQTransfer environment critical local sg handler saved entry transfer frame
        before after Hcompletion).

Lemma kernel_builtin_c_segment_source_frames :
  forall state before returned after input output
    (Hsegment : BuiltinComponent.kernel_builtin_c_segment environment critical local sg
      state before returned after input output),
  kernel_builtin_c_segment_source state before returned after input output Hsegment ->
  task_creation_frame observer state.(TskState) returned.(TskState) /\
  (forall event_observer, event_creation_frame event_observer state.(EventState) returned.(EventState)) /\
  state.(NameState) = returned.(NameState) /\ timer_public_trace sg state.(TimerState) returned.(TimerState).
Proof.
  intros state before returned after input output Hsegment Hsource; destruct Hsource.
  - destruct operation; (split; [reflexivity|]; split; [intros; reflexivity|]; split; [reflexivity|constructor]).
  - destruct Hcompletion as [Hpre Hpost].
    assert (Hvalid : UCOS2_state_inv sg state).
    { destruct Hpre as [owned [rest [Hjoin [[Hfacts Howned] Hrest]]]]; exact (proj1 Hfacts). }
    split.
    + eapply kernel_client_frames_creation;
        [apply (task_create_stack_publication_certificate publication)|exact Hvalid|exact effect|].
      change (Some publication.(stack_publication_invocation) <> Some observer); congruence.
    + split.
      * intro invocation; eapply kernel_client_frames_event_creation;
          [apply (task_create_stack_publication_certificate publication)|exact Hvalid|exact effect|discriminate].
      * split; [eapply task_create_stack_publication_name_frame; exact effect|].
        rewrite (task_create_stack_publication_timer_state_eq _ _ _ _ effect); constructor.
  - pose proof (BuiltinComponent.kernel_irq_transfer_c_completion_source environment critical sg
      handler saved entry transfer frame before after Hcompletion) as Htransfer.
    destruct (BuiltinComponent.os_int_exit_configured_transfer_state_frame environment sg handler entry transfer Htransfer)
      as [Hnodes [Hlife [Hevent [Hname Htimer]]]].
    split.
    + change (task_creation_frame observer entry.(TskState) (os_int_exit_installed_state transfer).(TskState)).
      unfold task_creation_frame, task_creation_view; rewrite Hlife; reflexivity.
    + split; [intro invocation; change (event_creation_frame invocation entry.(EventState)
        (os_int_exit_installed_state transfer).(EventState)); rewrite Hevent; reflexivity|].
      split; [symmetry; exact Hname|change (timer_public_trace sg entry.(TimerState)
        (os_int_exit_installed_state transfer).(TimerState)); rewrite Htimer; constructor].
Qed.
End KernelBuiltinCSource.

Lemma flag_pend_task_primitive_c_step_creation_frames :
  forall environment critical sg observer state before input stopped returned after output,
  PrimitiveComponent.flag_pend_task_primitive_c_step environment critical sg
    state before input stopped returned after output ->
  task_creation_frame observer state.(TskState) returned.(TskState) /\
  (forall event_observer, event_creation_frame event_observer state.(EventState) returned.(EventState)) /\
  state.(NameState) = returned.(NameState) /\ timer_public_trace sg state.(TimerState) returned.(TimerState).
Proof.
  intros environment critical sg observer state before input stopped returned after output Hstep.
  destruct Hstep.
  - destruct H; (split; [reflexivity|]; split; [intros; reflexivity|]; split; [reflexivity|constructor]).
  - split; [reflexivity|]. split; [intros; reflexivity|]. split; [reflexivity|constructor].
  - split; [reflexivity|]. split; [intros; reflexivity|]. split; [reflexivity|constructor].
Qed.

(** The right side of the final sum, over the same root Hstep.  Only
    publication has a task-creation actor here; its actual identity is
    retained by the indexed builtin source above. *)
Section KernelProgramRemainingCSources.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (observer : nat) (observer_origin : TaskInvocationOrigin)
  (event_observer : option nat).

Inductive kernel_program_c_step_remaining_source :
  forall state before input stopped returned after output,
  kernel_program_c_step environment critical sg observer observer_origin
    state before input stopped returned after output -> Prop :=
| KernelProgramCCriticalSource : forall local frame call before after Hsegment,
    kernel_program_c_step_remaining_source _ _ _ _ _ _ _
      (@KernelProgramCCritical environment critical sg observer observer_origin local frame call before after Hsegment)
| KernelProgramCBuiltinSource : forall local state before returned after input output Hsegment,
    kernel_builtin_c_segment_source environment critical local sg observer
      state before returned after input output Hsegment ->
    kernel_program_c_step_remaining_source _ _ _ _ _ _ _
      (@KernelProgramCBuiltin environment critical sg observer observer_origin local state before returned after input output Hsegment)
| KernelProgramCInstallSource : forall local state before input stopped returned after output Hsegment,
    kernel_program_c_step_remaining_source _ _ _ _ _ _ _
      (@KernelProgramCInstall environment critical sg observer observer_origin local
        state before input stopped returned after output Hsegment)
| KernelProgramCMutexPendSource : forall local frame call before after Hsegment,
    kernel_program_c_step_remaining_source _ _ _ _ _ _ _
      (@KernelProgramCMutexPend environment critical sg observer observer_origin local frame call before after Hsegment)
| KernelProgramCMutexPostSource : forall source_env local frame call before after Hsegment,
    kernel_program_c_step_remaining_source _ _ _ _ _ _ _
      (@KernelProgramCMutexPost environment critical sg observer observer_origin source_env local frame call before after Hsegment)
| KernelProgramCDeletePrimitiveSource : forall state before input stopped returned after output Hsegment,
    kernel_program_c_step_remaining_source _ _ _ _ _ _ _
      (@KernelProgramCDeletePrimitive environment critical sg observer observer_origin
        state before input stopped returned after output Hsegment)
| KernelProgramCPairedPrimitiveSource : forall state before input stopped returned after output Hsegment,
    kernel_program_c_step_remaining_source _ _ _ _ _ _ _
      (@KernelProgramCPairedPrimitive environment critical sg observer observer_origin
        state before input stopped returned after output Hsegment)
| KernelProgramCDeleteSource : forall state before input stopped returned after output Hsegment,
    kernel_program_c_step_remaining_source _ _ _ _ _ _ _
      (@KernelProgramCDelete environment critical sg observer observer_origin
        state before input stopped returned after output Hsegment).

Lemma kernel_program_c_step_remaining_source_frames :
  forall state before input stopped returned after output
    (Hstep : kernel_program_c_step environment critical sg observer observer_origin
      state before input stopped returned after output),
  kernel_program_c_step_remaining_source state before input stopped returned after output Hstep ->
  task_creation_frame observer state.(TskState) returned.(TskState) /\
  (forall invocation, event_observer = Some invocation ->
    event_creation_frame invocation state.(EventState) returned.(EventState)) /\
  state.(NameState) = returned.(NameState) /\ timer_public_trace sg state.(TimerState) returned.(TimerState).
Proof.
  intros state before input stopped returned after output Hstep Hsource; destruct Hsource.
  - destruct Hsegment as [Hcompletion [Hphysical [Hcode Hpacket]]].
    destruct (kernel_critical_c_source_creation_frames _ _ observer Hcode)
      as [Htask [Hevent Hrest]].
    split; [exact Htask|]. split; [intros; apply Hevent|exact Hrest].
  - destruct (kernel_builtin_c_segment_source_frames environment critical local sg observer
      _ _ _ _ _ _ Hsegment H) as [Htask [Hevent Hrest]].
    split; [exact Htask|]. split; [intros; apply Hevent|exact Hrest].
  - destruct (task_install_c_step_creation_frames environment local sg observer _ _ _ _ _ _ _ Hsegment)
      as [Htask [Hevent Hrest]].
    split; [exact Htask|]. split; [intros; apply Hevent|exact Hrest].
  - destruct Hsegment as [Hcode Hpre Hpost].
    destruct (mutex_pend_inheritance_c_source_creation_frames _ _ observer Hcode)
      as [Htask [Hevent Hrest]].
    split; [exact Htask|]. split; [intros; apply Hevent|exact Hrest].
  - destruct Hsegment as [Hcode Hpre Hpost].
    destruct (mutex_post_critical_c_source_creation_frames _ _ observer Hcode)
      as [Htask [Hevent Hrest]].
    split; [exact Htask|]. split; [intros; apply Hevent|exact Hrest].
  - destruct (TaskDeletePhaseFrames.task_delete_primitive_c_segment_creation_name_timer_frames
      environment critical sg _ _ _ _ _ _ _ Hsegment) as [Htask [Hevent [Hname Htimer]]].
    split; [apply Htask|]. split; [intros; apply Hevent|]. split; [exact Hname|rewrite Htimer; constructor].
  - destruct (flag_pend_task_primitive_c_step_creation_frames environment critical sg observer
      _ _ _ _ _ _ _ Hsegment) as [Htask [Hevent Hrest]].
    split; [exact Htask|]. split; [intros; apply Hevent|exact Hrest].
  - destruct (TaskDeletePhaseFrames.task_delete_own_c_segment_creation_name_timer_frames
      environment critical sg observer observer_origin _ _ _ _ _ _ _ Hsegment)
      as [Htask [Hevent [Hname Htimer]]].
    split; [apply Htask|]. split; [intros; apply Hevent|]. split; [exact Hname|rewrite Htimer; constructor].
Qed.
End KernelProgramRemainingCSources.












(** Provenance follows the existing execution proof.  An atomic marker is
    supplied by that C module's actual call/allocation protocol.  In
    particular, it may retain a foreign invocation condition; it is not a
    second execution picked for its endpoints. *)
Import CriticalComponent.

(** The two source families cover the actual program constructors and keep
    each constructor's own call/allocation evidence on that same Hstep. *)
Section KernelProgramCSequenceSource.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (observer : nat) (observer_origin : TaskInvocationOrigin)
  (event_observer : option nat).

Definition kernel_program_c_step_call_source state before input stopped returned after output
  (step : kernel_program_c_step environment critical sg observer observer_origin
    state before input stopped returned after output) : Prop :=
  kernel_program_c_step_source environment critical sg observer observer_origin event_observer
    state before input stopped returned after output step \/
  kernel_program_c_step_remaining_source environment critical sg observer observer_origin
    state before input stopped returned after output step.

Definition kernel_program_c_sequence_call_source state before input stopped returned after output
  (run : kernel_c_sequence_spec.kernel_c_sequence
    (kernel_program_c_step environment critical sg observer observer_origin)
    state before input stopped returned after output) : Prop :=
  kernel_c_sequence_has_source
    (kernel_program_c_step environment critical sg observer observer_origin)
    kernel_program_c_step_call_source state before input stopped returned after output run.

Lemma kernel_program_c_step_call_source_frames :
  forall state before input stopped returned after output
    (step : kernel_program_c_step environment critical sg observer observer_origin
      state before input stopped returned after output),
  kernel_program_c_step_call_source state before input stopped returned after output step ->
  task_creation_frame observer state.(TskState) returned.(TskState) /\
  (forall invocation, event_observer = Some invocation ->
    event_creation_frame invocation state.(EventState) returned.(EventState)) /\
  state.(NameState) = returned.(NameState) /\
  timer_public_trace sg state.(TimerState) returned.(TimerState).
Proof.
  intros state before input stopped returned after output step [Hnamed|Hremaining].
  - exact (kernel_program_c_step_source_frames environment critical sg observer observer_origin
      event_observer state before input stopped returned after output step Hnamed).
  - exact (kernel_program_c_step_remaining_source_frames environment critical sg observer observer_origin
      event_observer state before input stopped returned after output step Hremaining).
Qed.

(** This is an induction over the original run.  Both adjacent runs use
    the original middle state, heap and resource implication; no trace is
    reselected by its endpoints. *)
Lemma kernel_program_c_sequence_call_source_frames :
  forall state before input stopped returned after output
    (run : kernel_c_sequence_spec.kernel_c_sequence
      (kernel_program_c_step environment critical sg observer observer_origin)
      state before input stopped returned after output),
  kernel_program_c_sequence_call_source state before input stopped returned after output run ->
  task_creation_frame observer state.(TskState) returned.(TskState) /\
  (forall invocation, event_observer = Some invocation ->
    event_creation_frame invocation state.(EventState) returned.(EventState)) /\
  state.(NameState) = returned.(NameState) /\
  timer_public_trace sg state.(TimerState) returned.(TimerState).
Proof.
  intros state before input stopped returned after output run Hsource.
  eapply (kernel_c_sequence_source_relation
    (kernel_program_c_step environment critical sg observer observer_origin)
    kernel_program_c_step_call_source
    (fun entry final =>
      task_creation_frame observer entry.(TskState) final.(TskState) /\
      (forall invocation, event_observer = Some invocation ->
        event_creation_frame invocation entry.(EventState) final.(EventState)) /\
      entry.(NameState) = final.(NameState) /\
      timer_public_trace sg entry.(TimerState) final.(TimerState))).
  - intro entry; split; [reflexivity|].
    split; [intros; reflexivity|]. split; [reflexivity|constructor].
  - intros first middle last [Htask [Hevent [Hname Htimer]]]
      [Htask' [Hevent' [Hname' Htimer']]].
    split.
    + unfold task_creation_frame in *; etransitivity; [exact Htask'|exact Htask].
    + split.
      * intros invocation Hobserver.
        unfold event_creation_frame in *; etransitivity;
          [exact (Hevent' invocation Hobserver)|exact (Hevent invocation Hobserver)].
      * split; [etransitivity; eassumption|].
        eapply timer_public_trace_trans; eassumption.
  - intros; eapply kernel_program_c_step_call_source_frames; eassumption.
  - exact Hsource.
Qed.

End KernelProgramCSequenceSource.



(** A selected environment is an actual sequence of the fixed C program.
    Its existing return owner contains the original C endpoint contract.
    The ABI suffix/prefix below is composed with that very sequence; there
    is no independently supplied old source or endpoint-equal replacement
    tree.  State, caller, local resources and heaps may all change in the
    environment.  Its stopped bit is retained, not assumed false. *)
Import PrimitiveComponent.
