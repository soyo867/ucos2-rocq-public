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

Module CriticalComponent.














Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.




















Import UCOS2_C_Rules TaskStateDef SchedStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.



















































Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
























Definition mutex_del_no_pend_critical_call_guard (sg : StableGlobVars)
  (eid : EventID) (entry : UCOS2_Verify_State) : Prop :=
  exists event mutex,
    mutex_del_parent_entry sg eid entry event mutex /\
    (forall owner, mutex.(mfOwner) = Some owner -> task_slot_addr sg owner <> 1).

Definition mutex_del_no_pend_critical_call_client (actor : option nat)
  (eid : EventID) : KernelClientAction :=
  {| kernel_client_actor := actor;
     kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       mutex_del_no_pend_critical_call_guard sg eid before /\
       exists result code request,
         mutex_del_parent_critical_observation sg eid 0 result code request before after |}.

Lemma mutex_del_fields_task_pointer_not_reserved : forall sg state owner node,
  tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner ->
  state.(TskState).(inUsedTaskStates) owner = Some node ->
  UCOS2_fields_inv sg state |--
    coq_prop (task_slot_addr sg owner <> 1) && UCOS2_fields_inv sg state.
Proof.
  intros sg state owner node Haddress Hnode heap Hfields.
  pose proof (proj1 (UCOS2_fields_inv_split_task_storage_sched_flag sg state)
    heap Hfields) as [Hvalid [modules_heap [rest_heap [Hjoin [Hmodules Hrest]]]]].
  destruct Hmodules as [task_sched_heap [flag_heap [Hjoin_flag [Htask_sched Hflag]]]].
  destruct Htask_sched as [task_heap [sched_heap [Hjoin_sched [Htasks Hsched]]]].
  pose proof (task_public_storage_split_task sg state.(TskState) owner node Hnode
    task_heap Htasks) as [owner_heap [other_heap [Hjoin_owner [Howner Hother]]]].
  pose proof (mutex_del_task_storage_pointer_not_reserved sg owner node Haddress
    owner_heap Howner) as [Hpointer Howned].
  split; [exact Hpointer|exact Hfields].
Qed.

Lemma mutex_del_no_pend_critical_call_guard_from_fields :
  forall sg eid entry event mutex,
  mutex_del_parent_layout sg ->
  mutex_del_parent_entry sg eid entry event mutex ->
  UCOS2_fields_inv sg entry |--
    coq_prop (mutex_del_no_pend_critical_call_guard sg eid entry) &&
    UCOS2_fields_inv sg entry.
Proof.
  intros sg eid entry event mutex Hlayout Hentry heap Hfields.
  assert (Hpointer : forall owner, mutex.(mfOwner) = Some owner ->
    task_slot_addr sg owner <> 1).
  { intros owner Howner.
    pose proof Hentry as [Hvalid [He [Htype [Hmutex Huse]]]].
    pose proof Hvalid as [_ [_ [_ [_ [Hcross _]]]]].
    destruct Hcross as [_ [Hsnapshot _]].
    destruct (Hsnapshot eid event mutex owner He Htype Hmutex Howner)
      as [node [base [snapshot [Hnode Hrest]]]].
    assert (Haddress : forall base, tcb_field_address base TCBStkPtr = base).
    { unfold mutex_del_parent_layout in Hlayout; tauto. }
    exact (proj1 (mutex_del_fields_task_pointer_not_reserved
      sg entry owner node (Haddress (task_slot_addr sg owner)) Hnode heap Hfields)). }
  split; [exists event, mutex; split; assumption|exact Hfields].
Qed.

Lemma mutex_del_no_pend_critical_call_observation_step :
  forall actor sg eid result code request entry checkpoint,
  mutex_del_no_pend_critical_call_guard sg eid entry ->
  mutex_del_parent_critical_observation sg eid 0 result code request entry checkpoint ->
  kernel_client_step (mutex_del_no_pend_critical_call_client actor eid) sg entry checkpoint.
Proof.
  intros actor sg eid result code request entry checkpoint Hguard Hobservation.
  split; [exact Hguard|]. exists result, code, request; exact Hobservation.
Qed.

Lemma mutex_del_prepare_name_timer_frame : forall sg mutex entry prepared,
  mutex_del_prepare sg mutex entry prepared ->
  entry.(NameState) = prepared.(NameState) /\
  entry.(TimerState) = prepared.(TimerState).
Proof.
  intros sg mutex entry prepared Hprepare; unfold mutex_del_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis));
    [subst; split; reflexivity|].
  destruct mutex.(mfOwner) as [owner|]; [|subst; split; reflexivity].
  destruct Hprepare as [node [priority [Hnode [Hpriority ->]]]].
  unfold mutex_del_owner_priority_state; destruct Z.eq_dec; split; reflexivity.
Qed.

Lemma mutex_del_no_pend_critical_name_timer_frame : forall sg eid entry result checkpoint,
  mutex_del_critical sg eid 0 entry result checkpoint ->
  entry.(NameState) = checkpoint.(NameState) /\
  entry.(TimerState) = checkpoint.(TimerState).
Proof.
  intros sg eid entry result checkpoint [event [mutex [He [Htype [Hmutex Hrun]]]]].
  destruct (Z.eq_dec 0 0); [|contradiction].
  destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) entry.(TskState)) 0).
  - destruct Hrun as [prepared [Hprepare [-> Hresult]]].
    change (entry.(NameState) = prepared.(NameState) /\
      entry.(TimerState) = prepared.(TimerState)).
    exact (mutex_del_prepare_name_timer_frame sg mutex entry prepared Hprepare).
  - destruct Hrun as [-> Hresult]; split; reflexivity.
Qed.

Lemma mutex_del_no_pend_critical_call_client_certificate : forall actor eid,
  KernelClientCertificate (mutex_del_no_pend_critical_call_client actor eid).
Proof.
  intros actor eid; constructor.
  - intros sg before after Hvalid [Hguard [result [code [request
      [error [scheduled [Hcritical Hencoding]]]]]]].
    destruct Hguard as [event [mutex [[Hentry [He [Htype [Hmutex Huse]]]] Hpointer]]].
    eapply mutex_del_critical_under_owner_use_preserves_validity;
      [exact Hvalid|exact Huse| |exact Hcritical].
    intros other_event other_mutex owner He' Htype' Hmutex' Howner.
    unfold mutex_query_lookup in He.
    assert (other_event = event) by congruence; subst other_event.
    assert (other_mutex = mutex) by congruence; subst other_mutex.
    exact (Hpointer owner Howner).
  - intros sg before after observer Hvalid [Hguard [result [code [request
      [error [scheduled [Hcritical Hencoding]]]]]]] Hforeign.
    pose proof (mutex_del_critical_call_fields_eq
      sg eid 0 before (result, (error, scheduled)) after Hcritical)
      as [Hnodes [Hstacks [Hlife [Hcurrent Hprivate]]]].
    unfold task_creation_frame, task_creation_view; rewrite Hlife; reflexivity.
  - intros sg before after observer origin Hvalid [Hguard [result [code [request
      [error [scheduled [Hcritical Hencoding]]]]]]] Hstop
      [Hinvocation [Hretired Hlive]].
    pose proof (mutex_del_critical_call_fields_eq
      sg eid 0 before (result, (error, scheduled)) after Hcritical)
      as [Hnodes [Hstacks [Hlife [Hcurrent Hprivate]]]].
    unfold task_invocation_active; rewrite Hlife.
    split; [exact Hinvocation|]. split; [exact Hretired|].
    destruct origin as [|slot generation]; [exact I|].
    destruct Hlive as [node [Hnode Hgeneration]].
    specialize (Hnodes slot); rewrite Hnode in Hnodes.
    destruct (after.(TskState).(inUsedTaskStates) slot) as [returned|] eqn:Hreturned;
      [|discriminate].
    cbn in Hnodes; injection Hnodes as Hgeneration' Hstack.
    exists returned; split; [exact Hreturned|congruence].
  - intros sg before after observer Hvalid [Hguard [result [code [request
      [error [scheduled [Hcritical Hencoding]]]]]]] Hforeign.
    pose proof (mutex_del_critical_call_fields_eq
      sg eid 0 before (result, (error, scheduled)) after Hcritical)
      as [Hnodes [Hstacks [Hlife [Hcurrent Hprivate]]]].
    unfold event_creation_frame, event_creation_view; rewrite Hprivate; reflexivity.
Qed.

Lemma mutex_del_no_pend_critical_call_client_name_frame :
  forall actor eid sg before after,
  kernel_client_step (mutex_del_no_pend_critical_call_client actor eid) sg before after ->
  before.(NameState) = after.(NameState).
Proof.
  intros actor eid sg before after [Hguard [result [code [request
    [error [scheduled [Hcritical Hencoding]]]]]]].
  exact (proj1 (mutex_del_no_pend_critical_name_timer_frame
    sg eid before (result, (error, scheduled)) after Hcritical)).
Qed.

Lemma mutex_del_no_pend_critical_call_observation_completed_source :
  forall external port clients sg observer event_observer origin actor eid
    result code request entry checkpoint,
  clients (mutex_del_no_pend_critical_call_client actor eid) ->
  actor <> Some observer ->
  mutex_del_no_pend_critical_call_guard sg eid entry ->
  mutex_del_parent_critical_observation sg eid 0 result code request entry checkpoint ->
  kernel_resumption_task_source_trace external port clients sg observer event_observer
    origin entry false origin checkpoint.
Proof.
  intros external port clients sg observer event_observer origin actor eid
    result code request entry checkpoint Hmember Hforeign Hguard Hobservation.
  pose proof Hobservation as [error [scheduled [Hcritical Hencoding]]].
  pose proof (mutex_del_critical_call_fields_eq
    sg eid 0 entry (result, (error, scheduled)) checkpoint Hcritical)
    as [Hnodes [Hstacks [Hlife [Hcurrent Hprivate]]]].
  change (kernel_resumption_task_source_trace external port clients sg observer event_observer
    origin entry (kernel_client_stops
      (mutex_del_no_pend_critical_call_client actor eid) observer) origin checkpoint).
  eapply kernel_client_framed_step_resumption_source with
    (action := mutex_del_no_pend_critical_call_client actor eid).
  - exact Hmember.
  - exact Hforeign.
  - intros invocation Hevent; discriminate.
  - eapply mutex_del_no_pend_critical_call_observation_step; eassumption.
  - symmetry; exact Hcurrent.
  - exact (proj2 (mutex_del_no_pend_critical_name_timer_frame
      sg eid entry (result, (error, scheduled)) checkpoint Hcritical)).
Qed.

Definition mutex_del_no_pend_critical_call_clients (action : KernelClientAction) : Prop :=
  exists actor eid, action = mutex_del_no_pend_critical_call_client actor eid.

Lemma mutex_del_no_pend_critical_call_clients_certificate : forall action,
  mutex_del_no_pend_critical_call_clients action -> KernelClientCertificate action.
Proof.
  intros action [actor [eid ->]]; apply mutex_del_no_pend_critical_call_client_certificate.
Qed.

Lemma mutex_del_no_pend_critical_call_clients_name_frame : forall action,
  mutex_del_no_pend_critical_call_clients action -> forall sg before after,
  kernel_client_step action sg before after -> before.(NameState) = after.(NameState).
Proof.
  intros action [actor [eid ->]] sg before after Hstep.
  exact (mutex_del_no_pend_critical_call_client_name_frame actor eid sg before after Hstep).
Qed.

(** Link actual module certificates into the existing physical critical
    region.  Original clients remain registered.  Cache/source properties
    are proved from their C packets elsewhere, not asserted by this record. *)
Section CriticalRegionClientExtension.
Context (critical : CriticalRegionResources)
  (module_clients : KernelClientAction -> Prop)
  (module_certificates : forall action, module_clients action -> KernelClientCertificate action)
  (module_name_frame : forall action, module_clients action -> forall sg before after,
    kernel_client_step action sg before after -> before.(NameState) = after.(NameState)).

Definition critical_region_extend_clients : CriticalRegionResources.
Proof.
  refine {| critical_region_outside_without_running := critical.(critical_region_outside_without_running);
            critical_region_outside_without_running_rep := critical.(critical_region_outside_without_running_rep);
            critical_region_inside := critical.(critical_region_inside);
            critical_region_clients := fun action => critical.(critical_region_clients) action \/ module_clients action |}.
  - intros action [Horiginal|Hmodule].
    + exact (critical_region_client_certificates critical action Horiginal).
    + exact (module_certificates action Hmodule).
  - intros action [Horiginal|Hmodule] sg before after Hstep.
    + exact (critical_region_client_name_frame critical action Horiginal sg before after Hstep).
    + exact (module_name_frame action Hmodule sg before after Hstep).
Defined.
End CriticalRegionClientExtension.

Lemma mutex_del_released_preserves_observer_cache : forall origin entry ceiling,
  sched_observer_current_cache origin entry ->
  sched_observer_current_cache origin (mutex_del_released_state entry ceiling).
Proof. intros origin entry ceiling Hcache; exact Hcache. Qed.

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

Lemma mutex_del_owner_priority_preserves_observer_cache :
  forall sg origin entry ceiling owner node priority,
  sched_observer_current_cache origin entry ->
  sched_observer_current_cache origin (mutex_del_owner_priority_state sg entry ceiling owner node priority).
Proof.
  intros sg origin entry ceiling owner node priority Hcache.
  unfold mutex_del_owner_priority_state; destruct (Z.eq_dec node.(curPrio) priority).
  - apply mutex_del_released_preserves_observer_cache; exact Hcache.
  - apply mutex_del_relocated_preserves_observer_cache; exact Hcache.
Qed.

Lemma mutex_del_prepare_preserves_observer_cache : forall sg origin mutex entry after,
  mutex_del_prepare sg mutex entry after ->
  sched_observer_current_cache origin entry -> sched_observer_current_cache origin after.
Proof.
  intros sg origin mutex entry after Hprepare Hcache.
  unfold mutex_del_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)).
  - subst after; exact Hcache.
  - destruct mutex.(mfOwner) as [owner|].
    + destruct Hprepare as [node [priority [Hnode [Hscan ->]]]].
      apply mutex_del_owner_priority_preserves_observer_cache; exact Hcache.
    + subst after; apply mutex_del_released_preserves_observer_cache; exact Hcache.
Qed.

Lemma mutex_del_recycle_preserves_observer_cache : forall sg origin eid event state,
  sched_observer_current_cache origin state ->
  sched_observer_current_cache origin (mutex_del_recycle_state sg eid event state).
Proof. intros sg origin eid event state Hcache; exact Hcache. Qed.

Lemma mutex_del_call_fields_preserve_invocation : forall before after observer origin,
  mutex_del_call_fields_eq before after ->
  task_invocation_active before.(TskState) observer origin ->
  task_invocation_active after.(TskState) observer origin.
Proof.
  intros before after observer origin [Hnodes [Hparked [Hlife Hrest]]]
    [Hinvocation [Hretired Hlive]].
  unfold task_invocation_active; rewrite Hlife; split; [exact Hinvocation|].
  split; [exact Hretired|].
  destruct origin as [|slot generation]; [exact I|].
  destruct Hlive as [node [Hnode Hgeneration]].
  specialize (Hnodes slot); rewrite Hnode in Hnodes.
  destruct (after.(TskState).(inUsedTaskStates) slot) as [returned|] eqn:Hreturned;
    [|discriminate].
  cbn in Hnodes; injection Hnodes as Hgeneration' Hsp.
  exists returned; split; [exact Hreturned|congruence].
Qed.

Section MutexDelFieldsOriginalOwnerDefinitions.
Variable source_env : MutexDelCallEnvironment.
Definition mutex_del_continuation_stack_support external platform saved_local sg original state : Assertion :=
  EX environment returned,
    coq_prop (mutex_del_callsite_environment environment external platform /\
      kernel_stack_call_same_call returned original /\
      mutex_program_selected_reachable sg state /\
      mutex_del_private_types_non_mutex state.(EventState) /\
      task_stack_live_coverage state.(TskState) (task_stack_call_active_key original) /\
      environment = source_env) &&
    (os_sched_context_resources external returned **
     store_parked_continuations (kernel_saved_continuation_entry environment.(mutex_del_call_continuations) state.(TskState)
       (task_create_continuation_local saved_local)) state.(TskState).(parkedTaskStacks)).

Definition mutex_del_continuation_acquired external platform saved_local sg original state : Assertion :=
  event_private_pool_rep sg state.(EventState) **
  mutex_del_continuation_stack_support external platform saved_local sg original state.
End MutexDelFieldsOriginalOwnerDefinitions.

(** Concrete NO_PEND acquired->checkpoint C contract graph.  The runner
    supplies the original continuation_acquired definitions from their
    fixed source, the checked registration, and the checked NO_PEND observer
    theorem.  No old Mutex API module is compiled for this integration. *)

Definition mutex_del_fields_environment (environment : TaskStackCallEnvironment)
  : MutexDelCallEnvironment :=
  {| mutex_del_call_external := environment.(task_stack_call_external);
     mutex_del_call_platform := environment.(task_stack_call_platform);
     mutex_del_call_port := environment.(task_stack_call_port);
     mutex_del_call_continuations := environment.(task_stack_call_continuations) |}.

Record MutexDelFieldsCall : Type := {
  mutex_del_fields_original : OsSchedCallContext;
  mutex_del_fields_mask : Z;
  mutex_del_fields_saved : Z;
  mutex_del_fields_before : UCOS2_Verify_State;
  mutex_del_fields_entry : UCOS2_Verify_State;
  mutex_del_fields_checkpoint : UCOS2_Verify_State;
  mutex_del_fields_eid : EventID;
  mutex_del_fields_result : Z;
  mutex_del_fields_code : Z;
  mutex_del_fields_request : Z
}.

Definition mutex_del_fields_actor (call : MutexDelFieldsCall) : option nat :=
  Some call.(mutex_del_fields_original).(os_sched_call_invocation).

Definition mutex_del_fields_linked_region (critical : CriticalRegionResources) :=
  critical_region_extend_clients critical mutex_del_no_pend_critical_call_clients
    mutex_del_no_pend_critical_call_clients_certificate
    mutex_del_no_pend_critical_call_clients_name_frame.

Lemma mutex_del_fields_linked_region_includes_call : forall critical actor eid,
  (mutex_del_fields_linked_region critical).(critical_region_clients)
    (mutex_del_no_pend_critical_call_client actor eid).
Proof. intros; right; exists actor, eid; reflexivity. Qed.

Section MutexDelFieldsInstance.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (saved_local : Armv7aContinuation -> Assertion) (frame : Assertion) (observer : nat).

Let linked := mutex_del_fields_linked_region critical.
Let local := task_create_continuation_local saved_local.

(** Exactly the C owner at lines 411--412, with state=entry at the acquired
    cut and state=checkpoint immediately before Restore.  The original
    physical critical region and invocation/capsule owner are retained. *)
Definition mutex_del_fields_owner sg call state : Assertion :=
  mutex_del_runtime_program_restore_pre environment.(task_stack_call_platform) critical
    sg call.(mutex_del_fields_original) call.(mutex_del_fields_mask) call.(mutex_del_fields_saved)
    call.(mutex_del_fields_before) call.(mutex_del_fields_entry) state **
  mutex_del_continuation_acquired (mutex_del_fields_environment environment)
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    saved_local sg call.(mutex_del_fields_original) call.(mutex_del_fields_entry).

(** The storage producer is applied inside the original C owner.  Padding,
    unmap, masked resources and continuation support stay on their original
    heap; only the proved pure guard is extracted. *)
Lemma mutex_del_fields_owner_call_guard : forall sg call event mutex,
  mutex_del_parent_layout sg ->
  mutex_del_parent_entry sg call.(mutex_del_fields_eid) call.(mutex_del_fields_entry) event mutex ->
  mutex_del_fields_owner sg call call.(mutex_del_fields_entry) |--
    coq_prop (mutex_del_no_pend_critical_call_guard sg call.(mutex_del_fields_eid)
      call.(mutex_del_fields_entry)) &&
    mutex_del_fields_owner sg call call.(mutex_del_fields_entry).
Proof.
  intros sg call event mutex Hlayout Hentry heap Howned.
  pose proof Howned as [runtime_heap [support_heap [Hjoin [Hruntime Hsupport]]]].
  destruct Hruntime as [Hfacts [masked_heap [program_heap [Hjoin_program [Hmasked Hprogram]]]]].
  pose proof (proj1 (kernel_program_inv_split_unmap sg call.(mutex_del_fields_entry))
    program_heap Hprogram) as [inv_heap [unmap_heap [Hjoin_unmap [Hinv Hunmap]]]].
  pose proof (proj1 (UCOS2_inv_fields_padding sg call.(mutex_del_fields_entry))
    inv_heap Hinv) as [fields_heap [padding_heap [Hjoin_padding [Hfields Hpadding]]]].
  pose proof (mutex_del_no_pend_critical_call_guard_from_fields
    sg call.(mutex_del_fields_eid) call.(mutex_del_fields_entry) event mutex Hlayout Hentry
    fields_heap Hfields) as [Hguard Hfields_again].
  split; [exact Hguard|exact Howned].
Qed.

(** Only actual C pre/post facts form a completion.  In particular the
    guard is derived from the pre heap, and cache/ready are absent here. *)
Inductive mutex_del_fields_completion sg call before after : Prop :=
| MutexDelFieldsComplete : forall event mutex,
    mutex_del_parent_layout sg ->
    mutex_del_parent_entry sg call.(mutex_del_fields_eid) call.(mutex_del_fields_entry) event mutex ->
    mutex_del_parent_critical_observation sg call.(mutex_del_fields_eid) 0
      call.(mutex_del_fields_result) call.(mutex_del_fields_code) call.(mutex_del_fields_request)
      call.(mutex_del_fields_entry) call.(mutex_del_fields_checkpoint) ->
    (mutex_del_fields_owner sg call call.(mutex_del_fields_entry) ** frame) before ->
    (mutex_del_fields_owner sg call call.(mutex_del_fields_checkpoint) ** frame) after ->
    mutex_del_fields_completion sg call before after.

Lemma mutex_del_fields_completion_from_c_post : forall sg call event mutex before after,
  mutex_del_parent_layout sg ->
  mutex_del_parent_entry sg call.(mutex_del_fields_eid) call.(mutex_del_fields_entry) event mutex ->
  (mutex_del_fields_owner sg call call.(mutex_del_fields_entry) ** frame) before ->
  (coq_prop (mutex_del_parent_critical_observation sg call.(mutex_del_fields_eid) 0
      call.(mutex_del_fields_result) call.(mutex_del_fields_code) call.(mutex_del_fields_request)
      call.(mutex_del_fields_entry) call.(mutex_del_fields_checkpoint)) &&
    (mutex_del_fields_owner sg call call.(mutex_del_fields_checkpoint) ** frame)) after ->
  mutex_del_fields_completion sg call before after.
Proof.
  intros sg call event mutex before after Hlayout Hentry Hpre [Hobservation Hpost].
  econstructor; eassumption.
Qed.

Lemma mutex_del_fields_completion_call_guard : forall sg call before after,
  mutex_del_fields_completion sg call before after ->
  mutex_del_no_pend_critical_call_guard sg call.(mutex_del_fields_eid) call.(mutex_del_fields_entry).
Proof.
  intros sg call before after [event mutex Hlayout Hentry Hobservation Hpre Hpost].
  destruct Hpre as [owned [rest [Hjoin [Howned Hrest]]]].
  exact (proj1 (mutex_del_fields_owner_call_guard sg call event mutex Hlayout Hentry owned Howned)).
Qed.

Lemma mutex_del_fields_completion_observation : forall sg call before after,
  mutex_del_fields_completion sg call before after ->
  mutex_del_parent_critical_observation sg call.(mutex_del_fields_eid) 0
    call.(mutex_del_fields_result) call.(mutex_del_fields_code) call.(mutex_del_fields_request)
    call.(mutex_del_fields_entry) call.(mutex_del_fields_checkpoint).
Proof. intros sg call before after Hcompletion; destruct Hcompletion; assumption. Qed.

Lemma mutex_del_fields_completion_resources : forall sg call before after,
  mutex_del_fields_completion sg call before after ->
  (mutex_del_fields_owner sg call call.(mutex_del_fields_entry) ** frame) before /\
  (mutex_del_fields_owner sg call call.(mutex_del_fields_checkpoint) ** frame) after.
Proof. intros sg call before after Hcompletion; destruct Hcompletion; split; assumption. Qed.

Definition mutex_del_fields_completion_source sg call before after
  (Hcompletion : mutex_del_fields_completion sg call before after)
  (origin : TaskInvocationOrigin) (Hforeign : mutex_del_fields_actor call <> Some observer) :=
  mutex_del_no_pend_critical_call_observation_completed_source
    environment.(task_stack_call_external) environment.(task_stack_call_port)
    linked.(critical_region_clients) sg observer None origin (mutex_del_fields_actor call)
    call.(mutex_del_fields_eid) call.(mutex_del_fields_result) call.(mutex_del_fields_code)
    call.(mutex_del_fields_request) call.(mutex_del_fields_entry) call.(mutex_del_fields_checkpoint)
    (mutex_del_fields_linked_region_includes_call critical
      (mutex_del_fields_actor call) call.(mutex_del_fields_eid)) Hforeign
    (mutex_del_fields_completion_call_guard sg call before after Hcompletion)
    (mutex_del_fields_completion_observation sg call before after Hcompletion).
End MutexDelFieldsInstance.












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

Definition sched_task_mutex_del_always_execution sg eid entry prepared
  (before after : model) : Prop :=
  exists preparation_heap,
    mutex_del_prepare_source_execution sg (event_addr sg eid) eid
      entry prepared before preparation_heap /\
    mutex_del_always_after_prepare_execution sg (event_addr sg eid)
      preparation_heap after.




(** The wake loop changes status/wait membership, but leaves the task's
    generation and priority, and the physical current cache, unchanged.
    This lemma applies within the real prepared phase, without a closed
    invariant or an exclusion of the observer from the wake targets. *)
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

Lemma mutex_del_broadcast_preserves_observer_cache :
  forall sg origin eid kind message result before priorities after,
  event_broadcast sg eid kind message result before priorities after ->
  sched_observer_current_cache origin before -> sched_observer_current_cache origin after.
Proof.
  intros sg origin eid kind message result before priorities after Hrun; induction Hrun.
  - exact (fun Hcache => Hcache).
  - intros Hcache; apply IHHrun.
    eapply mutex_del_wake_preserves_observer_cache; eassumption.
Qed.

Lemma mutex_del_wake_name_timer_frame :
  forall sg before eid kind message result priority after,
  event_task_rdy sg before eid kind message result = Some (priority, after) ->
  before.(NameState) = after.(NameState) /\ before.(TimerState) = after.(TimerState).
Proof.
  intros sg before eid kind message result priority after Hstep.
  unfold event_task_rdy in Hstep.
  destruct (before.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
  destruct (before.(TskState).(prioTbl) (event_wait_priority before.(TskState) event))
    as [| |tid]; try discriminate.
  destruct (before.(TskState).(inUsedTaskStates) tid) as [old|]; [|discriminate].
  injection Hstep as Hpriority Hafter; subst after; split; reflexivity.
Qed.

Lemma mutex_del_broadcast_name_timer_frame :
  forall sg eid kind message result before priorities after,
  event_broadcast sg eid kind message result before priorities after ->
  before.(NameState) = after.(NameState) /\ before.(TimerState) = after.(TimerState).
Proof.
  intros sg eid kind message result before priorities after Hrun; induction Hrun.
  - split; reflexivity.
  - destruct (mutex_del_wake_name_timer_frame sg s eid kind message result priority mid H1)
      as [Hname Htimer]. destruct IHHrun as [Hname' Htimer']; split; congruence.
Qed.

Lemma mutex_del_critical_name_timer_frame : forall sg eid option entry result checkpoint,
  mutex_del_critical sg eid option entry result checkpoint ->
  entry.(NameState) = checkpoint.(NameState) /\
  entry.(TimerState) = checkpoint.(TimerState).
Proof.
  intros sg eid option entry result checkpoint [event [mutex [He [Htype [Hmutex Hrun]]]]].
  destruct (Z.eq_dec option 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) entry.(TskState)) 0).
    + destruct Hrun as [prepared [Hprepare [-> Hresult]]].
      exact (mutex_del_prepare_name_timer_frame sg mutex entry prepared Hprepare).
    + destruct Hrun as [-> Hresult]; split; reflexivity.
  - destruct (Z.eq_dec option 1).
    + destruct Hrun as [prepared [priorities [drained [Hprepare [Hbroadcast [-> Hresult]]]]]].
      destruct (mutex_del_prepare_name_timer_frame sg mutex entry prepared Hprepare) as [Hname Htimer].
      destruct (mutex_del_broadcast_name_timer_frame sg eid PendMutex 0 PendAbort
        prepared priorities drained Hbroadcast) as [Hname' Htimer'].
      change (entry.(NameState) = drained.(NameState) /\ entry.(TimerState) = drained.(TimerState)).
      split; congruence.
    + destruct Hrun as [-> Hresult]; split; reflexivity.
Qed.

Lemma mutex_del_critical_preserves_observer_cache : forall sg origin eid option entry result checkpoint,
  mutex_del_critical sg eid option entry result checkpoint ->
  sched_observer_current_cache origin entry -> sched_observer_current_cache origin checkpoint.
Proof.
  intros sg origin eid option entry result checkpoint [event [mutex [He [Htype [Hmutex Hrun]]]]] Hcache.
  destruct (Z.eq_dec option 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) entry.(TskState)) 0).
    + destruct Hrun as [prepared [Hprepare [-> Hresult]]].
      apply mutex_del_recycle_preserves_observer_cache.
      eapply mutex_del_prepare_preserves_observer_cache; eassumption.
    + destruct Hrun as [-> Hresult]; exact Hcache.
  - destruct (Z.eq_dec option 1).
    + destruct Hrun as [prepared [priorities [drained [Hprepare [Hbroadcast [-> Hresult]]]]]].
      apply mutex_del_recycle_preserves_observer_cache.
      eapply mutex_del_broadcast_preserves_observer_cache; [exact Hbroadcast|].
      eapply mutex_del_prepare_preserves_observer_cache; eassumption.
    + destruct Hrun as [-> Hresult]; exact Hcache.
Qed.

(** Complete acquired critical domain: the live Mutex body retains all
    options and its exact request bit.  The acquired type-recheck error is
    the actual C184--196 identity branch, before parent_entry exists. *)
Inductive mutex_del_critical_call_observation sg eid option entry :
  Z -> Z -> Z -> UCOS2_Verify_State -> Prop :=
| MutexDelCriticalLive : forall result code request checkpoint,
    mutex_del_no_pend_critical_call_guard sg eid entry ->
    mutex_del_parent_critical_observation sg eid option result code request entry checkpoint ->
    mutex_del_critical_call_observation sg eid option entry result code request checkpoint
| MutexDelCriticalTypeError : forall kind,
    mutex_del_runtime_type_observation sg eid entry kind -> kind <> 4 ->
    mutex_del_critical_call_observation sg eid option entry (event_addr sg eid)
      (encode_os_err_code OS_ERR_EVENT_TYPE) 0 entry.

Definition mutex_del_critical_call_client (actor : option nat) (eid option : Z) : KernelClientAction :=
  {| kernel_client_actor := actor;
     kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       exists result code request,
         mutex_del_critical_call_observation sg eid option before result code request after |}.

Lemma mutex_del_critical_call_observation_fields : forall sg eid option entry result code request checkpoint,
  mutex_del_critical_call_observation sg eid option entry result code request checkpoint ->
  mutex_del_call_fields_eq entry checkpoint /\
  entry.(NameState) = checkpoint.(NameState) /\ entry.(TimerState) = checkpoint.(TimerState).
Proof.
  intros sg eid option entry result code request checkpoint Hobservation; destruct Hobservation.
  - destruct H0 as [error [scheduled [Hcritical Hencoding]]].
    split; [eapply mutex_del_critical_call_fields_eq; exact Hcritical|].
    eapply mutex_del_critical_name_timer_frame; exact Hcritical.
  - split; [apply mutex_del_call_fields_eq_refl|split; reflexivity].
Qed.

Lemma mutex_del_critical_call_client_certificate : forall actor eid option,
  KernelClientCertificate (mutex_del_critical_call_client actor eid option).
Proof.
  intros actor eid option; constructor.
  - intros sg before after Hvalid [result [code [request Hobservation]]].
    destruct Hobservation as [result code request checkpoint Hguard Hobservation|kind Htype Hnotmutex].
    + destruct Hobservation as [error [scheduled [Hcritical Hencoding]]].
      destruct Hguard as [event [mutex [[Hentry [He [Htype [Hmutex Huse]]]] Hpointer]]].
      eapply mutex_del_critical_under_owner_use_preserves_validity;
        [exact Hvalid|exact Huse| |exact Hcritical].
      intros other_event other_mutex owner He' Htype' Hmutex' Howner.
      unfold mutex_query_lookup in He.
      assert (other_event = event) by congruence; subst other_event.
      assert (other_mutex = mutex) by congruence; subst other_mutex.
      exact (Hpointer owner Howner).
    + exact Hvalid.
  - intros sg before after observer Hvalid [result [code [request Hobservation]]] Hforeign.
    destruct (proj1 (mutex_del_critical_call_observation_fields
      sg eid option before result code request after Hobservation))
      as [Hnodes [Hstacks [Hlife [Hcurrent Hprivate]]]].
    unfold task_creation_frame, task_creation_view; rewrite Hlife; reflexivity.
  - intros sg before after observer origin Hvalid [result [code [request Hobservation]]] Hstop Hactive.
    eapply mutex_del_call_fields_preserve_invocation; [|exact Hactive].
    exact (proj1 (mutex_del_critical_call_observation_fields
      sg eid option before result code request after Hobservation)).
  - intros sg before after observer Hvalid [result [code [request Hobservation]]] Hforeign.
    destruct (proj1 (mutex_del_critical_call_observation_fields
      sg eid option before result code request after Hobservation))
      as [Hnodes [Hstacks [Hlife [Hcurrent Hprivate]]]].
    unfold event_creation_frame, event_creation_view; rewrite Hprivate; reflexivity.
Qed.

Lemma mutex_del_critical_call_client_name_frame : forall actor eid option sg before after,
  kernel_client_step (mutex_del_critical_call_client actor eid option) sg before after ->
  before.(NameState) = after.(NameState).
Proof.
  intros actor eid option sg before after [result [code [request Hobservation]]].
  exact (proj1 (proj2 (mutex_del_critical_call_observation_fields
    sg eid option before result code request after Hobservation))).
Qed.

Lemma mutex_del_critical_call_observation_source :
  forall external port clients sg observer event_observer origin actor eid option
    entry result code request checkpoint,
  clients (mutex_del_critical_call_client actor eid option) -> actor <> Some observer ->
  mutex_del_critical_call_observation sg eid option entry result code request checkpoint ->
  kernel_resumption_task_source_trace external port clients sg observer event_observer
    origin entry false origin checkpoint.
Proof.
  intros external port clients sg observer event_observer origin actor eid option
    entry result code request checkpoint Hmember Hforeign Hobservation.
  pose proof (mutex_del_critical_call_observation_fields
    sg eid option entry result code request checkpoint Hobservation)
    as [[Hnodes [Hstacks [Hlife [Hcurrent Hprivate]]]] [Hname Htimer]].
  change (kernel_resumption_task_source_trace external port clients sg observer event_observer
    origin entry (kernel_client_stops (mutex_del_critical_call_client actor eid option) observer)
    origin checkpoint).
  eapply kernel_client_framed_step_resumption_source with
    (action := mutex_del_critical_call_client actor eid option).
  - exact Hmember.
  - exact Hforeign.
  - intros invocation Hevent; discriminate.
  - exists result, code, request; exact Hobservation.
  - symmetry; exact Hcurrent.
  - exact Htimer.
Qed.

Lemma mutex_del_critical_call_observation_preserves_observer :
  forall sg observer origin eid option entry result code request checkpoint,
  mutex_del_critical_call_observation sg eid option entry result code request checkpoint ->
  task_invocation_active entry.(TskState) observer origin ->
  sched_observer_current_cache origin entry ->
  task_invocation_active checkpoint.(TskState) observer origin /\
  sched_observer_current_cache origin checkpoint.
Proof.
  intros sg observer origin eid option entry result code request checkpoint Hobservation Hactive Hcache.
  split.
  - eapply mutex_del_call_fields_preserve_invocation; [|exact Hactive].
    exact (proj1 (mutex_del_critical_call_observation_fields
      sg eid option entry result code request checkpoint Hobservation)).
  - destruct Hobservation.
    + destruct H0 as [error [scheduled [Hcritical Hencoding]]].
      eapply mutex_del_critical_preserves_observer_cache; eassumption.
    + exact Hcache.
Qed.

Definition mutex_del_critical_call_clients (action : KernelClientAction) : Prop :=
  exists actor eid option, action = mutex_del_critical_call_client actor eid option.

Lemma mutex_del_critical_call_clients_certificate : forall action,
  mutex_del_critical_call_clients action -> KernelClientCertificate action.
Proof. intros action [actor [eid [option ->]]]; apply mutex_del_critical_call_client_certificate. Qed.

Lemma mutex_del_critical_call_clients_name_frame : forall action,
  mutex_del_critical_call_clients action -> forall sg before after,
  kernel_client_step action sg before after -> before.(NameState) = after.(NameState).
Proof.
  intros action [actor [eid [option ->]]] sg before after Hstep.
  exact (mutex_del_critical_call_client_name_frame actor eid option sg before after Hstep).
Qed.



(** The old checked phase-prefix definition is loaded verbatim by the
    runner.  It retains the actual preparation_heap shared by prepare and
    the literal wake-loop/release/recycle execution. *)
Lemma mutex_del_program_call_guard : forall sg eid entry event mutex,
  mutex_del_parent_layout sg -> mutex_del_parent_entry sg eid entry event mutex ->
  kernel_program_inv sg entry |--
    coq_prop (mutex_del_no_pend_critical_call_guard sg eid entry) && kernel_program_inv sg entry.
Proof.
  intros sg eid entry event mutex Hlayout Hentry heap Hprogram.
  pose proof (proj1 (kernel_program_inv_split_unmap sg entry) heap Hprogram)
    as [inv_heap [unmap_heap [Hjoin [Hinv Hunmap]]]].
  pose proof (proj1 (UCOS2_inv_fields_padding sg entry) inv_heap Hinv)
    as [fields_heap [padding_heap [Hjoin_padding [Hfields Hpadding]]]].
  split; [|exact Hprogram].
  exact (proj1 (mutex_del_no_pend_critical_call_guard_from_fields
    sg eid entry event mutex Hlayout Hentry fields_heap Hfields)).
Qed.

(** Every original live-Mutex C critical code is retained.  The guard comes
    from the same acquired program heap, not a caller-supplied output fact. *)
Lemma mutex_del_critical_post_call_observation :
  forall sg eid option entry event mutex before after result code request checkpoint
    (frame owned : Assertion),
  mutex_del_parent_layout sg -> mutex_del_parent_entry sg eid entry event mutex ->
  (kernel_program_inv sg entry ** frame) before ->
  (coq_prop (mutex_del_parent_critical_observation sg eid option result code request entry checkpoint)
    && owned) after ->
  (coq_prop (mutex_del_critical_call_observation sg eid option entry result code request checkpoint)
    && owned) after.
Proof.
  intros sg eid option entry event mutex before after result code request checkpoint frame owned
    Hlayout Hentry [program_heap [rest_heap [Hjoin [Hprogram Hrest]]]] [Hobservation Howned].
  split; [|exact Howned].
  apply MutexDelCriticalLive; [|exact Hobservation].
  exact (proj1 (mutex_del_program_call_guard sg eid entry event mutex Hlayout Hentry program_heap Hprogram)).
Qed.

Lemma mutex_del_type_error_post_call_observation :
  forall sg eid option entry kind (owned : Assertion),
  coq_prop (mutex_del_runtime_type_observation sg eid entry kind /\ kind <> 4) && owned |--
  coq_prop (mutex_del_critical_call_observation sg eid option entry (event_addr sg eid)
    (encode_os_err_code OS_ERR_EVENT_TYPE) 0 entry) && owned.
Proof.
  intros sg eid option entry kind owned heap [[Htype Hnotmutex] Howned].
  split; [eapply MutexDelCriticalTypeError; eassumption|exact Howned].
Qed.

Definition mutex_del_always_schedule_request entry event : Z :=
  if negb (Z.eqb (encode_event_wait_grp event.(waitList) entry.(TskState)) 0) then 1 else 0.

(** This is a producer from the literal C execution and the original input
    owner.  Its output is the exact loop-computed checkpoint and request,
    with the same external frame at the actual after heap. *)
Lemma mutex_del_always_call_source_resources :
  forall sg eid entry prepared event mutex before after (frame : Assertion),
  mutex_del_parent_layout sg -> event_object_layout_prop sg eid ->
  mutex_del_parent_entry sg eid entry event mutex ->
  (kernel_program_inv sg entry ** frame) before ->
  sched_task_mutex_del_always_execution sg eid entry prepared before after ->
  let checkpoint := mutex_del_always_checkpoint sg eid event prepared in
  mutex_del_critical_call_observation sg eid 1 entry 0 (encode_os_err_code OS_ERR_NONE)
    (mutex_del_always_schedule_request entry event) checkpoint /\
  (kernel_program_inv sg checkpoint ** frame) after.
Proof.
  intros sg eid entry prepared event mutex before after frame Hlayout Hobject Hentry Hpre
    [preparation_heap [Hprepare Hsuffix]] checkpoint.
  assert (Hguard : mutex_del_no_pend_critical_call_guard sg eid entry).
  { destruct Hpre as [program_heap [rest_heap [Hjoin [Hprogram Hrest]]]].
    exact (proj1 (mutex_del_program_call_guard sg eid entry event mutex Hlayout Hentry
      program_heap Hprogram)). }
  pose proof (mutex_del_prepare_source_resources sg eid entry prepared event mutex
    before preparation_heap frame Hlayout Hentry Hpre Hprepare) as Hprepared.
  destruct (mutex_del_always_after_prepare_resources sg eid entry prepared event mutex
    preparation_heap after frame Hobject Hprepared Hsuffix) as [Hcritical Hafter].
  split; [|exact Hafter].
  apply MutexDelCriticalLive; [exact Hguard|].
  exists OS_ERR_NONE,
    (negb (Z.eqb (encode_event_wait_grp event.(waitList) entry.(TskState)) 0)).
  split; [exact Hcritical|]. split; reflexivity.
Qed.

(** Full acquired critical domain, sharing the exact original C owner used
    by the NO_PEND instance.  The frozen narrower instance is unchanged. *)
Record MutexDelCriticalFieldsCall : Type := {
  mutex_del_critical_fields_base : MutexDelFieldsCall;
  mutex_del_critical_fields_option : Z
}.

Inductive MutexDelCriticalFieldsCut : Type :=
| MutexDelCriticalFieldsEntry (call : MutexDelCriticalFieldsCall)
| MutexDelCriticalFieldsCheckpoint (call : MutexDelCriticalFieldsCall).

Definition mutex_del_critical_fields_result (call : MutexDelFieldsCall) option result code request checkpoint
  : MutexDelCriticalFieldsCall :=
  {| mutex_del_critical_fields_option := option;
     mutex_del_critical_fields_base :=
       {| mutex_del_fields_original := call.(mutex_del_fields_original);
          mutex_del_fields_mask := call.(mutex_del_fields_mask);
          mutex_del_fields_saved := call.(mutex_del_fields_saved);
          mutex_del_fields_before := call.(mutex_del_fields_before);
          mutex_del_fields_entry := call.(mutex_del_fields_entry);
          mutex_del_fields_checkpoint := checkpoint;
          mutex_del_fields_eid := call.(mutex_del_fields_eid);
          mutex_del_fields_result := result;
          mutex_del_fields_code := code;
          mutex_del_fields_request := request |} |}.

Definition mutex_del_critical_fields_region critical :=
  critical_region_extend_clients critical mutex_del_critical_call_clients
    mutex_del_critical_call_clients_certificate mutex_del_critical_call_clients_name_frame.

Lemma mutex_del_critical_fields_includes_call : forall critical actor eid option,
  (mutex_del_critical_fields_region critical).(critical_region_clients)
    (mutex_del_critical_call_client actor eid option).
Proof. intros; right; exists actor, eid, option; reflexivity. Qed.

Section MutexDelCriticalFields.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (saved_local : Armv7aContinuation -> Assertion) (frame : Assertion) (observer : nat).
Let linked := mutex_del_critical_fields_region critical.
Let local := task_create_continuation_local saved_local.
Let owner := mutex_del_fields_owner environment critical saved_local.

Definition mutex_del_critical_fields_observation sg call :=
  let actual := call.(mutex_del_critical_fields_base) in
  mutex_del_critical_call_observation sg actual.(mutex_del_fields_eid)
    call.(mutex_del_critical_fields_option) actual.(mutex_del_fields_entry)
    actual.(mutex_del_fields_result) actual.(mutex_del_fields_code) actual.(mutex_del_fields_request)
    actual.(mutex_del_fields_checkpoint).

Inductive mutex_del_critical_fields_completion sg call before after : Prop :=
| MutexDelCriticalFieldsComplete :
    mutex_del_critical_fields_observation sg call ->
    (owner sg call.(mutex_del_critical_fields_base)
      call.(mutex_del_critical_fields_base).(mutex_del_fields_entry) ** frame) before ->
    (owner sg call.(mutex_del_critical_fields_base)
      call.(mutex_del_critical_fields_base).(mutex_del_fields_checkpoint) ** frame) after ->
    mutex_del_critical_fields_completion sg call before after.

Lemma mutex_del_critical_fields_completion_from_c_post :
  forall sg call event mutex before after,
  mutex_del_parent_layout sg ->
  mutex_del_parent_entry sg call.(mutex_del_critical_fields_base).(mutex_del_fields_eid)
    call.(mutex_del_critical_fields_base).(mutex_del_fields_entry) event mutex ->
  (owner sg call.(mutex_del_critical_fields_base)
    call.(mutex_del_critical_fields_base).(mutex_del_fields_entry) ** frame) before ->
  (coq_prop (mutex_del_parent_critical_observation sg
      call.(mutex_del_critical_fields_base).(mutex_del_fields_eid) call.(mutex_del_critical_fields_option)
      call.(mutex_del_critical_fields_base).(mutex_del_fields_result)
      call.(mutex_del_critical_fields_base).(mutex_del_fields_code)
      call.(mutex_del_critical_fields_base).(mutex_del_fields_request)
      call.(mutex_del_critical_fields_base).(mutex_del_fields_entry)
      call.(mutex_del_critical_fields_base).(mutex_del_fields_checkpoint)) &&
    (owner sg call.(mutex_del_critical_fields_base)
      call.(mutex_del_critical_fields_base).(mutex_del_fields_checkpoint) ** frame)) after ->
  mutex_del_critical_fields_completion sg call before after.
Proof.
  intros sg call event mutex before after Hlayout Hentry Hpre [Hobservation Hpost].
  constructor; [|exact Hpre|exact Hpost].
  apply MutexDelCriticalLive; [|exact Hobservation].
  destruct Hpre as [owned [rest [Hjoin [Howned Hrest]]]].
  exact (proj1 (mutex_del_fields_owner_call_guard environment critical saved_local
    sg call.(mutex_del_critical_fields_base) event mutex Hlayout Hentry owned Howned)).
Qed.

Lemma mutex_del_critical_fields_type_error_from_c_post :
  forall sg call option kind before after,
  (owner sg call call.(mutex_del_fields_entry) ** frame) before ->
  (coq_prop (mutex_del_runtime_type_observation sg call.(mutex_del_fields_eid)
      call.(mutex_del_fields_entry) kind /\ kind <> 4) &&
    (owner sg call call.(mutex_del_fields_entry) ** frame)) after ->
  mutex_del_critical_fields_completion sg
    (mutex_del_critical_fields_result call option (event_addr sg call.(mutex_del_fields_eid))
      (encode_os_err_code OS_ERR_EVENT_TYPE) 0 call.(mutex_del_fields_entry)) before after.
Proof.
  intros sg call option kind before after Hpre [[Htype Hnotmutex] Hpost].
  constructor; [|exact Hpre|exact Hpost].
  eapply MutexDelCriticalTypeError; eassumption.
Qed.

Definition mutex_del_critical_fields_retained sg call : Assertion :=
  critical_region_masked environment.(task_stack_call_platform) critical sg
    call.(mutex_del_fields_original).(os_sched_call_invocation)
    call.(mutex_del_fields_original).(os_sched_call_origin) call.(mutex_del_fields_saved)
    call.(mutex_del_fields_entry) **
  mutex_del_continuation_acquired (mutex_del_fields_environment environment)
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    saved_local sg call.(mutex_del_fields_original) call.(mutex_del_fields_entry) ** frame.

Lemma mutex_del_critical_fields_owner_program_frame : forall sg call state,
  owner sg call state ** frame --||--
  coq_prop (mutex_del_runtime_save_facts sg call.(mutex_del_fields_mask) call.(mutex_del_fields_saved)
    call.(mutex_del_fields_before) call.(mutex_del_fields_entry)) &&
  (kernel_program_inv sg state ** mutex_del_critical_fields_retained sg call).
Proof.
  intros; unfold owner, mutex_del_fields_owner, mutex_del_runtime_program_restore_pre,
    mutex_del_critical_fields_retained; split; entailer!.
Qed.

(** The literal C execution supplies the entire ALWAYS body; its retained
    resource is the actual masked/capsule owner.  All result fields are
    computed here, so no desired endpoint guard is assumed. *)
Lemma mutex_del_critical_fields_always_from_execution :
  forall sg call event mutex prepared before after,
  mutex_del_parent_layout sg -> event_object_layout_prop sg call.(mutex_del_fields_eid) ->
  mutex_del_parent_entry sg call.(mutex_del_fields_eid) call.(mutex_del_fields_entry) event mutex ->
  (owner sg call call.(mutex_del_fields_entry) ** frame) before ->
  sched_task_mutex_del_always_execution sg call.(mutex_del_fields_eid)
    call.(mutex_del_fields_entry) prepared before after ->
  mutex_del_critical_fields_completion sg
    (mutex_del_critical_fields_result call 1 0 (encode_os_err_code OS_ERR_NONE)
      (mutex_del_always_schedule_request call.(mutex_del_fields_entry) event)
      (mutex_del_always_checkpoint sg call.(mutex_del_fields_eid) event prepared)) before after.
Proof.
  intros sg call event mutex prepared before after Hlayout Hobject Hentry Hpre Hactual.
  pose proof (proj1 (mutex_del_critical_fields_owner_program_frame sg call call.(mutex_del_fields_entry))
    before Hpre) as [Hfacts Hprogram].
  destruct (mutex_del_always_call_source_resources sg call.(mutex_del_fields_eid)
    call.(mutex_del_fields_entry) prepared event mutex before after
    (mutex_del_critical_fields_retained sg call) Hlayout Hobject Hentry Hprogram Hactual)
    as [Hobservation Hpost].
  constructor; [exact Hobservation|exact Hpre|].
  apply (proj2 (mutex_del_critical_fields_owner_program_frame sg call
    (mutex_del_always_checkpoint sg call.(mutex_del_fields_eid) event prepared)) after).
  split; assumption.
Qed.

Lemma mutex_del_critical_fields_completion_observation : forall sg call before after,
  mutex_del_critical_fields_completion sg call before after -> mutex_del_critical_fields_observation sg call.
Proof. intros sg call before after Hcompletion; destruct Hcompletion; assumption. Qed.

Lemma mutex_del_critical_fields_completion_resources : forall sg call before after,
  mutex_del_critical_fields_completion sg call before after ->
  (owner sg call.(mutex_del_critical_fields_base)
    call.(mutex_del_critical_fields_base).(mutex_del_fields_entry) ** frame) before /\
  (owner sg call.(mutex_del_critical_fields_base)
    call.(mutex_del_critical_fields_base).(mutex_del_fields_checkpoint) ** frame) after.
Proof. intros sg call before after Hcompletion; destruct Hcompletion; split; assumption. Qed.

Inductive mutex_del_critical_fields_step sg :
  KernelClientHeapCut MutexDelCriticalFieldsCut -> model ->
  KernelClientHeapCut MutexDelCriticalFieldsCut -> model -> Prop :=
| MutexDelCriticalFieldsStep : forall call before after,
    mutex_del_critical_fields_completion sg call before after ->
    mutex_del_critical_fields_step sg
      (KernelClientHeapExtra (MutexDelCriticalFieldsEntry call)) before
      (KernelClientHeapExtra (MutexDelCriticalFieldsCheckpoint call)) after.

Definition mutex_del_critical_fields_completion_source sg call before after
  (Hcompletion : mutex_del_critical_fields_completion sg call before after) origin
  (Hforeign : mutex_del_fields_actor call.(mutex_del_critical_fields_base) <> Some observer) :=
  mutex_del_critical_call_observation_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) linked.(critical_region_clients) sg observer None origin
    (mutex_del_fields_actor call.(mutex_del_critical_fields_base))
    call.(mutex_del_critical_fields_base).(mutex_del_fields_eid) call.(mutex_del_critical_fields_option)
    call.(mutex_del_critical_fields_base).(mutex_del_fields_entry)
    call.(mutex_del_critical_fields_base).(mutex_del_fields_result)
    call.(mutex_del_critical_fields_base).(mutex_del_fields_code)
    call.(mutex_del_critical_fields_base).(mutex_del_fields_request)
    call.(mutex_del_critical_fields_base).(mutex_del_fields_checkpoint)
    (mutex_del_critical_fields_includes_call critical
      (mutex_del_fields_actor call.(mutex_del_critical_fields_base))
      call.(mutex_del_critical_fields_base).(mutex_del_fields_eid) call.(mutex_del_critical_fields_option))
    Hforeign (mutex_del_critical_fields_completion_observation sg call before after Hcompletion).
End MutexDelCriticalFields.













(** All actual critical return codes are retained.  The success case uses
    the checked C transform, including its conditional OSPrioCur store. *)
Lemma task_change_prio_critical_current_timer_frame :
  forall sg requested priority before code after,
  task_change_prio_critical sg requested priority before code after ->
  after.(SchedState).(curTaskID) = before.(SchedState).(curTaskID) /\
  before.(TimerState) = after.(TimerState).
Proof.
  intros sg requested priority before code after Hstep.
  unfold task_change_prio_critical in Hstep.
  destruct (before.(TskState).(prioTbl) priority).
  - destruct Hstep as [selected [Hselected Hstep]].
    unfold task_change_prio_selected_effect in Hstep.
    destruct (Z.eqb selected sg.(osLowestPrio)).
    + destruct Hstep as [_ ->]; split; reflexivity.
    + destruct (before.(TskState).(prioTbl) selected).
      * destruct Hstep as [_ ->]; split; reflexivity.
      * destruct Hstep as [_ ->]; split; reflexivity.
      * destruct Hstep as [node [Hnode [_ ->]]]; split.
        -- exact (proj1 (task_change_prio_state_sched_caches
             sg before _ node selected priority)).
        -- reflexivity.
  - destruct Hstep as [_ ->]; split; reflexivity.
  - destruct Hstep as [_ ->]; split; reflexivity.
Qed.

Lemma task_change_prio_critical_preserves_invocation_active :
  forall sg requested priority before code after observer observer_origin,
  task_change_prio_critical sg requested priority before code after ->
  task_invocation_active before.(TskState) observer observer_origin ->
  task_invocation_active after.(TskState) observer observer_origin.
Proof.
  intros sg requested priority before code after observer observer_origin Hstep Hactive.
  unfold task_change_prio_critical in Hstep.
  destruct (before.(TskState).(prioTbl) priority).
  - destruct Hstep as [selected [Hselected Hstep]].
    unfold task_change_prio_selected_effect in Hstep.
    destruct (Z.eqb selected sg.(osLowestPrio)).
    + destruct Hstep as [_ ->]; exact Hactive.
    + destruct (before.(TskState).(prioTbl) selected).
      * destruct Hstep as [_ ->]; exact Hactive.
      * destruct Hstep as [_ ->]; exact Hactive.
      * destruct Hstep as [node [Hnode [_ ->]]].
        change (task_invocation_active
          (glob_task_set_usedtask before.(TskState) tid (mutex_priority_task node priority))
          observer observer_origin).
        eapply glob_task_set_usedtask_preserves_invocation_active;
          [exact Hnode|reflexivity|exact Hactive].
  - destruct Hstep as [_ ->]; exact Hactive.
  - destruct Hstep as [_ ->]; exact Hactive.
Qed.

(** The observer, not every transient current task, supplies the old live
    slot/generation.  The ordinary cache theorem is applied only when that
    observer is current.  No global live-current premise is added. *)
Lemma task_change_prio_critical_preserves_observer_cache :
  forall sg requested priority before code after observer observer_origin,
  task_change_prio_critical sg requested priority before code after ->
  task_invocation_active before.(TskState) observer observer_origin ->
  sched_observer_current_cache observer_origin before ->
  sched_observer_current_cache observer_origin after.
Proof.
  intros sg requested priority before code after observer [|slot generation]
    Hstep Hactive Hcache; [exact I|].
  intros node Hnode Hgeneration Hcurrent.
  destruct Hactive as [_ [_ [old [Hold Hold_generation]]]].
  pose proof (proj1 (task_change_prio_critical_current_timer_frame
    sg requested priority before code after Hstep)) as Hframe.
  assert (Hcurrent_before : before.(SchedState).(curTaskID) = Some slot)
    by (rewrite <- Hframe; exact Hcurrent).
  assert (Hconsistent : sched_current_consistency before.(TskState) before.(SchedState)).
  { unfold sched_current_consistency; rewrite Hcurrent_before.
    exists old; split; [exact Hold|].
    exact (Hcache old Hold Hold_generation Hcurrent_before). }
  pose proof (task_change_prio_critical_preserves_current_consistency
    sg requested priority before code after Hstep Hconsistent) as Hafter.
  unfold sched_current_consistency in Hafter; rewrite Hcurrent in Hafter.
  destruct Hafter as [current [Hlookup Hpriority]].
  assert (current = node) by congruence; subst current; exact Hpriority.
Qed.


Definition task_change_prio_critical_call_guard (sg : StableGlobVars)
  (requested priority : Priority) (entry : UCOS2_Verify_State) : Prop :=
  0 <= requested <= 255 /\ (requested < 63 \/ requested = 255) /\
  0 <= priority < 63 /\
  task_change_prio_owner_protocol sg requested priority entry /\
  task_change_prio_self_protocol sg requested priority entry.

Definition task_change_prio_critical_call_client (actor : option nat)
  (requested priority : Priority) : KernelClientAction :=
  {| kernel_client_actor := actor;
     kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       task_change_prio_critical_call_guard sg requested priority before /\
       exists error, task_change_prio_critical sg requested priority before error after |}.

Lemma task_change_prio_critical_call_preserves_validity :
  forall sg requested priority before error after,
  UCOS2_state_inv sg before ->
  task_change_prio_critical_call_guard sg requested priority before ->
  task_change_prio_critical sg requested priority before error after ->
  UCOS2_state_inv sg after.
Proof.
  intros sg requested priority before error after Hvalid
    [Hrequested [Hargument [Hpriority [Howner Hself]]]] Hcritical.
  pose proof (task_change_prio_profile_constants__task_state sg before Hvalid)
    as [Hlowest Hself_value].
  unfold task_change_prio_critical in Hcritical.
  destruct (before.(TskState).(prioTbl) priority) eqn:Hfree.
  - destruct Hcritical as [selected [Hselection Hcritical]].
    unfold task_change_prio_selected_effect in Hcritical.
    destruct (Z.eqb selected sg.(osLowestPrio)) eqn:Hidle.
    + destruct Hcritical as [_ ->]; exact Hvalid.
    + apply Z.eqb_neq in Hidle.
      destruct (before.(TskState).(prioTbl) selected) as [| |tid] eqn:Htable.
      * destruct Hcritical as [_ ->]; exact Hvalid.
      * destruct Hcritical as [_ ->]; exact Hvalid.
      * destruct Hcritical as [old [Hold [Hresult ->]]].
        assert (Hrange : task_priority_in_range sg selected).
        { pose proof Hselection as [[Hself_selected [slot [current [Hcurrent [Hnode ->]]]]]
            |[Hnotself ->]].
          - pose proof Hvalid as [_ [Htasks _]].
            destruct Htasks as [_ [_ [_ [_ [_ [_ [_ [Hranges _]]]]]]]].
            eapply Hranges; exact Hnode.
          - unfold task_priority_in_range; rewrite Hlowest.
            rewrite Hself_value in Hnotself; lia. }
        assert (Hselected_range : 0 <= selected < 63).
        { unfold task_priority_in_range in Hrange; rewrite Hlowest in Hrange.
          rewrite Hlowest in Hidle; lia. }
        pose proof (Howner Hfree selected tid Hselection Hidle Htable) as Hno_mutex.
        pose proof (task_change_prio_live_selected_priority
          sg before tid old selected Hvalid Hold Hno_mutex Hrange Htable) as Hselected.
        pose proof (task_change_prio_live_distinct_priority
          before.(TskState) tid selected priority Htable Hfree) as Hdistinct.
        apply (task_change_prio_preserves_state_inv__task_state
          sg before requested tid old selected priority).
        unfold task_change_prio_live; repeat (first [assumption | split]).
  - destruct Hcritical as [_ ->]; exact Hvalid.
  - destruct Hcritical as [_ ->]; exact Hvalid.
Qed.

Lemma task_change_prio_critical_creation_name_frames :
  forall sg requested priority before error after task_observer event_observer,
  task_change_prio_critical sg requested priority before error after ->
  task_creation_frame task_observer before.(TskState) after.(TskState) /\
  event_creation_frame event_observer before.(EventState) after.(EventState) /\
  before.(NameState) = after.(NameState).
Proof.
  intros sg requested priority before error after task_observer event_observer Hcritical.
  unfold task_change_prio_critical in Hcritical.
  destruct (before.(TskState).(prioTbl) priority).
  - destruct Hcritical as [selected [Hselection Hcritical]].
    unfold task_change_prio_selected_effect in Hcritical.
    destruct (Z.eqb selected sg.(osLowestPrio)).
    + destruct Hcritical as [_ ->]; repeat split; reflexivity.
    + destruct (before.(TskState).(prioTbl) selected).
      * destruct Hcritical as [_ ->]; repeat split; reflexivity.
      * destruct Hcritical as [_ ->]; repeat split; reflexivity.
      * destruct Hcritical as [old [Hold [Hresult ->]]].
        unfold task_change_priority_state, task_change_priority_events.
        destruct old.(eventPtr) as [eid|];
          [destruct (before.(EventState).(inUsedEventStates) eid)|];
          repeat split; reflexivity.
  - destruct Hcritical as [_ ->]; repeat split; reflexivity.
  - destruct Hcritical as [_ ->]; repeat split; reflexivity.
Qed.

Lemma task_change_prio_critical_call_client_certificate : forall actor requested priority,
  KernelClientCertificate (task_change_prio_critical_call_client actor requested priority).
Proof.
  intros actor requested priority; constructor.
  - intros sg before after Hvalid [Hguard [error Hcritical]].
    eapply task_change_prio_critical_call_preserves_validity; eassumption.
  - intros sg before after observer Hvalid [Hguard [error Hcritical]] Hforeign.
    exact (proj1 (task_change_prio_critical_creation_name_frames
      sg requested priority before error after observer observer Hcritical)).
  - intros sg before after observer origin Hvalid [Hguard [error Hcritical]] Hstop Hactive.
    eapply task_change_prio_critical_preserves_invocation_active; eassumption.
  - intros sg before after observer Hvalid [Hguard [error Hcritical]] Hforeign.
    exact (proj1 (proj2 (task_change_prio_critical_creation_name_frames
      sg requested priority before error after observer observer Hcritical))).
Qed.

Lemma task_change_prio_critical_call_client_name_frame :
  forall actor requested priority sg before after,
  kernel_client_step (task_change_prio_critical_call_client actor requested priority) sg before after ->
  before.(NameState) = after.(NameState).
Proof.
  intros actor requested priority sg before after [Hguard [error Hcritical]].
  exact (proj2 (proj2 (task_change_prio_critical_creation_name_frames
    sg requested priority before error after 0%nat 0%nat Hcritical))).
Qed.

Definition task_change_prio_call_clients (action : KernelClientAction) : Prop :=
  exists actor requested priority,
    action = task_change_prio_critical_call_client actor requested priority.

Lemma task_change_prio_call_clients_certificates : forall action,
  task_change_prio_call_clients action -> KernelClientCertificate action.
Proof.
  intros action [actor [requested [priority ->]]].
  apply task_change_prio_critical_call_client_certificate.
Qed.

(** This file is checked after the already proved task-change-prio packet.
    It gives one concrete C-contract-graph extension, not a new claim that
    an arbitrary physical edge is an actual invocation of this C function. *)





Record TaskChangePrioFieldsCall : Type := {
  change_prio_fields_execution : TaskChangePrioExecution;
  change_prio_fields_saved : Z;
  change_prio_fields_requested : Priority;
  change_prio_fields_priority : Priority;
  change_prio_fields_result : Z;
  change_prio_fields_entry : UCOS2_Verify_State;
  change_prio_fields_released : UCOS2_Verify_State
}.

Inductive TaskChangePrioFieldsCut : Type :=
| TaskChangePrioFieldsEntry (call : TaskChangePrioFieldsCall)
| TaskChangePrioFieldsReleased (call : TaskChangePrioFieldsCall).

Section TaskChangePrioFieldsInstance.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (saved_local : Armv7aContinuation -> Assertion) (frame : Assertion) (observer : nat).

(** This is the actual masked/runtime/capsule owner from the C critical
    post, not a closed world with active-key=None. *)
Definition task_change_prio_fields_owner sg call state : Assertion :=
  task_change_prio_masked environment saved_local critical sg
    call.(change_prio_fields_execution) call.(change_prio_fields_saved)
    call.(change_prio_fields_entry) state.

(** A graph of the verified critical C contract.  A real call boundary
    supplies these SAME heap owners and its exported critical observation.
    No cache/ready law or unlabelled physical transition is accepted here. *)
Inductive task_change_prio_fields_completion sg call before after : Prop :=
| TaskChangePrioFieldsComplete :
    task_change_prio_critical_call_guard sg call.(change_prio_fields_requested)
      call.(change_prio_fields_priority) call.(change_prio_fields_entry) ->
    task_change_prio_critical_code sg call.(change_prio_fields_requested)
      call.(change_prio_fields_priority) call.(change_prio_fields_entry)
      call.(change_prio_fields_result) call.(change_prio_fields_released) ->
    (task_change_prio_fields_owner sg call call.(change_prio_fields_entry) ** frame) before ->
    (task_change_prio_fields_owner sg call call.(change_prio_fields_released) ** frame) after ->
    task_change_prio_fields_completion sg call before after.

Lemma task_change_prio_fields_completion_from_c_post :
  forall sg call before after,
  task_change_prio_critical_call_guard sg call.(change_prio_fields_requested)
    call.(change_prio_fields_priority) call.(change_prio_fields_entry) ->
  (task_change_prio_fields_owner sg call call.(change_prio_fields_entry) ** frame) before ->
  (coq_prop (task_change_prio_critical_code sg call.(change_prio_fields_requested)
      call.(change_prio_fields_priority) call.(change_prio_fields_entry)
      call.(change_prio_fields_result) call.(change_prio_fields_released)) &&
    (task_change_prio_fields_owner sg call call.(change_prio_fields_released) ** frame)) after ->
  task_change_prio_fields_completion sg call before after.
Proof. intros sg call before after Hguard Hpre [Hcode Hpost]; constructor; assumption. Qed.

Inductive task_change_prio_fields_step sg :
  KernelClientHeapCut TaskChangePrioFieldsCut -> model ->
  KernelClientHeapCut TaskChangePrioFieldsCut -> model -> Prop :=
| TaskChangePrioFieldsStep : forall call before after,
    task_change_prio_fields_completion sg call before after ->
    task_change_prio_fields_step sg
      (KernelClientHeapExtra (TaskChangePrioFieldsEntry call)) before
      (KernelClientHeapExtra (TaskChangePrioFieldsReleased call)) after.
End TaskChangePrioFieldsInstance.



(** Two actual acquired C contracts.  Each payload keeps the original
    module call record, including its result and both state endpoints. *)
Inductive KernelCriticalCCall : Type :=
| KernelCriticalChangePrio (call : TaskChangePrioFieldsCall)
| KernelCriticalMutexDel (call : MutexDelCriticalFieldsCall).

Definition kernel_critical_c_entry call : UCOS2_Verify_State :=
  match call with
  | KernelCriticalChangePrio actual => actual.(change_prio_fields_entry)
  | KernelCriticalMutexDel actual =>
      actual.(mutex_del_critical_fields_base).(mutex_del_fields_entry)
  end.

Definition kernel_critical_c_returned call : UCOS2_Verify_State :=
  match call with
  | KernelCriticalChangePrio actual => actual.(change_prio_fields_released)
  | KernelCriticalMutexDel actual =>
      actual.(mutex_del_critical_fields_base).(mutex_del_fields_checkpoint)
  end.

(** These are the source proofs exported at the actual critical C post.
    No resumption trace, registry membership, or foreign-actor test is
    required to interpret either of these local C state transformers. *)
Definition kernel_critical_c_source sg call : Prop :=
  match call with
  | KernelCriticalChangePrio actual =>
      task_change_prio_critical_code sg actual.(change_prio_fields_requested)
        actual.(change_prio_fields_priority) actual.(change_prio_fields_entry)
        actual.(change_prio_fields_result) actual.(change_prio_fields_released)
  | KernelCriticalMutexDel actual => mutex_del_critical_fields_observation sg actual
  end.

Section KernelCriticalCSegments.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (saved_local : Armv7aContinuation -> Assertion) (sg : StableGlobVars) (frame : Assertion).

Definition kernel_critical_c_owner call state : Assertion :=
  match call with
  | KernelCriticalChangePrio actual =>
      task_change_prio_fields_owner environment critical saved_local sg actual state
  | KernelCriticalMutexDel actual =>
      mutex_del_fields_owner environment critical saved_local sg
        actual.(mutex_del_critical_fields_base) state
  end.

Definition kernel_critical_c_completion call before after : Prop :=
  match call with
  | KernelCriticalChangePrio actual =>
      task_change_prio_fields_completion environment critical saved_local frame sg actual before after
  | KernelCriticalMutexDel actual =>
      mutex_del_critical_fields_completion environment critical saved_local frame sg actual before after
  end.

Definition kernel_critical_c_physical call before after : Prop :=
  match call with
  | KernelCriticalChangePrio actual =>
      task_change_prio_fields_step environment critical saved_local frame sg
        (KernelClientHeapExtra (TaskChangePrioFieldsEntry actual)) before
        (KernelClientHeapExtra (TaskChangePrioFieldsReleased actual)) after
  | KernelCriticalMutexDel actual =>
      mutex_del_critical_fields_step environment critical saved_local frame sg
        (KernelClientHeapExtra (MutexDelCriticalFieldsEntry actual)) before
        (KernelClientHeapExtra (MutexDelCriticalFieldsCheckpoint actual)) after
  end.

Definition kernel_critical_c_completion_physical :
  forall call before after,
  kernel_critical_c_completion call before after -> kernel_critical_c_physical call before after.
Proof.
  intros [actual|actual] before after Hcompletion; simpl in *;
    constructor; exact Hcompletion.
Defined.

Definition kernel_critical_c_completion_source :
  forall call before after,
  kernel_critical_c_completion call before after -> kernel_critical_c_source sg call.
Proof.
  intros [actual|actual] before after Hcompletion; simpl in *;
    destruct Hcompletion; assumption.
Defined.

(** The source and physical proof indices are projections of this same
    completion proof.  The constructor cannot accept a second writer with
    coincident endpoints.  Output ownership is kept inside the original
    completion, rather than an added cache/output law. *)
Inductive kernel_critical_c_packet call before after
  (Hcompletion : kernel_critical_c_completion call before after) :
  kernel_critical_c_physical call before after -> kernel_critical_c_source sg call -> Prop :=
| KernelCriticalCPacket :
    kernel_critical_c_packet call before after Hcompletion
      (kernel_critical_c_completion_physical call before after Hcompletion)
      (kernel_critical_c_completion_source call before after Hcompletion).

Definition kernel_critical_c_segment call before after : Prop :=
  exists (Hcompletion : kernel_critical_c_completion call before after)
    (Hphysical : kernel_critical_c_physical call before after)
    (Hsource : kernel_critical_c_source sg call),
    kernel_critical_c_packet call before after Hcompletion Hphysical Hsource.

Lemma kernel_critical_c_completion_segment : forall call before after,
  kernel_critical_c_completion call before after -> kernel_critical_c_segment call before after.
Proof.
  intros call before after Hcompletion.
  exists Hcompletion,
    (kernel_critical_c_completion_physical call before after Hcompletion),
    (kernel_critical_c_completion_source call before after Hcompletion).
  constructor.
Qed.

(** Actual ChangePrio post opener: the guard is the original acquired
    argument/owner protocol; all result codes remain in the original code
    relation.  In particular the requested task may be the observer. *)
Lemma task_change_prio_critical_c_post_segment : forall call before after,
  task_change_prio_critical_call_guard sg call.(change_prio_fields_requested)
    call.(change_prio_fields_priority) call.(change_prio_fields_entry) ->
  (task_change_prio_fields_owner environment critical saved_local sg call
    call.(change_prio_fields_entry) ** frame) before ->
  (coq_prop (task_change_prio_critical_code sg call.(change_prio_fields_requested)
      call.(change_prio_fields_priority) call.(change_prio_fields_entry)
      call.(change_prio_fields_result) call.(change_prio_fields_released)) &&
    (task_change_prio_fields_owner environment critical saved_local sg call
      call.(change_prio_fields_released) ** frame)) after ->
  kernel_critical_c_segment (KernelCriticalChangePrio call) before after.
Proof.
  intros call before after Hguard Hpre Hpost.
  apply kernel_critical_c_completion_segment.
  exact (task_change_prio_fields_completion_from_c_post environment critical saved_local frame
    sg call before after Hguard Hpre Hpost).
Qed.

(** All live-Mutex option branches: NO_PEND success/TASK_WAITING, ALWAYS,
    and INVALID_OPT.  The pointer guard is derived from the real acquired
    owner by the already checked C-post opener. *)
Lemma mutex_del_critical_c_post_segment : forall call event mutex before after,
  mutex_del_parent_layout sg ->
  mutex_del_parent_entry sg call.(mutex_del_critical_fields_base).(mutex_del_fields_eid)
    call.(mutex_del_critical_fields_base).(mutex_del_fields_entry) event mutex ->
  (mutex_del_fields_owner environment critical saved_local sg call.(mutex_del_critical_fields_base)
    call.(mutex_del_critical_fields_base).(mutex_del_fields_entry) ** frame) before ->
  (coq_prop (mutex_del_parent_critical_observation sg
      call.(mutex_del_critical_fields_base).(mutex_del_fields_eid) call.(mutex_del_critical_fields_option)
      call.(mutex_del_critical_fields_base).(mutex_del_fields_result)
      call.(mutex_del_critical_fields_base).(mutex_del_fields_code)
      call.(mutex_del_critical_fields_base).(mutex_del_fields_request)
      call.(mutex_del_critical_fields_base).(mutex_del_fields_entry)
      call.(mutex_del_critical_fields_base).(mutex_del_fields_checkpoint)) &&
    (mutex_del_fields_owner environment critical saved_local sg call.(mutex_del_critical_fields_base)
      call.(mutex_del_critical_fields_base).(mutex_del_fields_checkpoint) ** frame)) after ->
  kernel_critical_c_segment (KernelCriticalMutexDel call) before after.
Proof.
  intros call event mutex before after Hlayout Hentry Hpre Hpost.
  apply kernel_critical_c_completion_segment.
  exact (mutex_del_critical_fields_completion_from_c_post environment critical saved_local frame
    sg call event mutex before after Hlayout Hentry Hpre Hpost).
Qed.

Lemma mutex_del_type_error_c_post_segment : forall call option kind before after,
  (mutex_del_fields_owner environment critical saved_local sg call
    call.(mutex_del_fields_entry) ** frame) before ->
  (coq_prop (mutex_del_runtime_type_observation sg call.(mutex_del_fields_eid)
      call.(mutex_del_fields_entry) kind /\ kind <> 4) &&
    (mutex_del_fields_owner environment critical saved_local sg call
      call.(mutex_del_fields_entry) ** frame)) after ->
  kernel_critical_c_segment
    (KernelCriticalMutexDel (mutex_del_critical_fields_result call option
      (event_addr sg call.(mutex_del_fields_eid)) (encode_os_err_code OS_ERR_EVENT_TYPE)
      0 call.(mutex_del_fields_entry))) before after.
Proof.
  intros call option kind before after Hpre Hpost.
  apply kernel_critical_c_completion_segment.
  exact (mutex_del_critical_fields_type_error_from_c_post environment critical saved_local frame
    sg call option kind before after Hpre Hpost).
Qed.

(** The ALWAYS constructor can also start directly from the original
    literal prepare/wake/recycle execution, producing its calculated
    checkpoint and schedule request with the original capsule/frame. *)
Lemma mutex_del_always_c_execution_segment :
  forall call event mutex prepared before after,
  mutex_del_parent_layout sg -> event_object_layout_prop sg call.(mutex_del_fields_eid) ->
  mutex_del_parent_entry sg call.(mutex_del_fields_eid) call.(mutex_del_fields_entry) event mutex ->
  (mutex_del_fields_owner environment critical saved_local sg call
    call.(mutex_del_fields_entry) ** frame) before ->
  sched_task_mutex_del_always_execution sg call.(mutex_del_fields_eid)
    call.(mutex_del_fields_entry) prepared before after ->
  kernel_critical_c_segment
    (KernelCriticalMutexDel (mutex_del_critical_fields_result call 1 0 (encode_os_err_code OS_ERR_NONE)
      (mutex_del_always_schedule_request call.(mutex_del_fields_entry) event)
      (mutex_del_always_checkpoint sg call.(mutex_del_fields_eid) event prepared))) before after.
Proof.
  intros call event mutex prepared before after Hlayout Hobject Hentry Hpre Hactual.
  apply kernel_critical_c_completion_segment.
  exact (mutex_del_critical_fields_always_from_execution environment critical saved_local frame
    sg call event mutex prepared before after Hlayout Hobject Hentry Hpre Hactual).
Qed.

Lemma kernel_critical_c_segment_resources : forall call before after,
  kernel_critical_c_segment call before after ->
  (kernel_critical_c_owner call (kernel_critical_c_entry call) ** frame) before /\
  (kernel_critical_c_owner call (kernel_critical_c_returned call) ** frame) after.
Proof.
  intros [actual|actual] before after [Hcompletion [Hphysical [Hsource Hpacket]]];
    simpl in *; destruct Hcompletion; split; assumption.
Qed.

Lemma kernel_critical_c_segment_output : forall call before after,
  kernel_critical_c_segment call before after ->
  (kernel_critical_c_owner call (kernel_critical_c_returned call) ** frame) after.
Proof.
  intros call before after Hsegment.
  exact (proj2 (kernel_critical_c_segment_resources call before after Hsegment)).
Qed.

(** Neither operation retires an invocation.  This local fact is proved
    from the actual source transform; it does not require an actor/target
    inequality or a flat registered-client cache certificate. *)
Lemma kernel_critical_c_segment_preserves_observer :
  forall observer observer_origin call before after,
  kernel_critical_c_segment call before after ->
  task_invocation_active (kernel_critical_c_entry call).(TskState) observer observer_origin /\
    sched_observer_current_cache observer_origin (kernel_critical_c_entry call) ->
  task_invocation_active (kernel_critical_c_returned call).(TskState) observer observer_origin /\
    sched_observer_current_cache observer_origin (kernel_critical_c_returned call).
Proof.
  intros observer observer_origin [actual|actual] before after
    [Hcompletion [Hphysical [Hsource Hpacket]]] [Hactive Hcache]; simpl in *.
  - destruct Hsource as [code [Hcritical Hresult]].
    split.
    + eapply task_change_prio_critical_preserves_invocation_active; eassumption.
    + eapply task_change_prio_critical_preserves_observer_cache; eassumption.
  - eapply mutex_del_critical_call_observation_preserves_observer; eassumption.
Qed.
End KernelCriticalCSegments.

(** The observer's registration/private/generation metadata, rather than
    its current active status, supplies the lifetime induction domain. *)
Lemma task_change_prio_critical_observer_lifetime_result :
  forall sg requested priority before code after observer observer_origin,
  task_change_prio_critical sg requested priority before code after ->
  task_observer_lifetime_result observer observer_origin
    before.(TskState) after.(TskState) false.
Proof.
  intros sg requested priority before code after observer observer_origin Hstep.
  apply task_observer_lifetime_result_not_stopped.
  unfold task_change_prio_critical in Hstep.
  destruct (before.(TskState).(prioTbl) priority).
  - destruct Hstep as [selected [Hselected Hstep]].
    unfold task_change_prio_selected_effect in Hstep.
    destruct (Z.eqb selected sg.(osLowestPrio)).
    + destruct Hstep as [_ ->].
      apply task_observer_lifetime_transport_fields; [reflexivity|intro slot; reflexivity].
    + destruct (before.(TskState).(prioTbl) selected).
      * destruct Hstep as [_ ->].
        apply task_observer_lifetime_transport_fields; [reflexivity|intro slot; reflexivity].
      * destruct Hstep as [_ ->].
        apply task_observer_lifetime_transport_fields; [reflexivity|intro slot; reflexivity].
      * destruct Hstep as [node [Hnode [_ ->]]].
        change (task_observer_lifetime_transport observer observer_origin before.(TskState)
          (glob_task_set_usedtask before.(TskState) tid (mutex_priority_task node priority))).
        eapply task_update_observer_lifetime_transport; [exact Hnode|reflexivity].
  - destruct Hstep as [_ ->].
    apply task_observer_lifetime_transport_fields; [reflexivity|intro slot; reflexivity].
  - destruct Hstep as [_ ->].
    apply task_observer_lifetime_transport_fields; [reflexivity|intro slot; reflexivity].
Qed.

(** The already checked full critical relation retains the complete task
    lifecycle and each used node's generation/SP pair.  Projecting the
    generation from that actual observation proves no old origin can be
    resurrected, including while it is inactive. *)
Lemma mutex_del_critical_observer_lifetime_result :
  forall sg eid option entry result code request checkpoint observer observer_origin,
  mutex_del_critical_call_observation sg eid option entry result code request checkpoint ->
  task_observer_lifetime_result observer observer_origin
    entry.(TskState) checkpoint.(TskState) false.
Proof.
  intros sg eid option entry result code request checkpoint observer observer_origin Hactual.
  apply task_observer_lifetime_result_not_stopped.
  destruct (mutex_del_critical_call_observation_fields
    sg eid option entry result code request checkpoint Hactual)
    as [[Hnodes [Hstacks [Hlife [Hcurrent Hprivate]]]] Hother].
  apply task_observer_lifetime_transport_fields; [exact Hlife|].
  intro slot; specialize (Hnodes slot).
  destruct (checkpoint.(TskState).(inUsedTaskStates) slot) as [post|];
    destruct (entry.(TskState).(inUsedTaskStates) slot) as [pre|];
    simpl in Hnodes |- *; congruence.
Qed.

(** This consumes the same C segment and its exact source proof.  No
    current-active/cache premise is used to establish lifetime transport.
    False is the non-retirement result for these two real critical bodies;
    the Mutex schedule request remains in its unchanged call payload. *)
Lemma kernel_critical_c_segment_observer_lifetime_result :
  forall environment critical saved_local sg frame observer observer_origin call before after,
  kernel_critical_c_segment environment critical saved_local sg frame call before after ->
  task_observer_lifetime_result observer observer_origin
    (kernel_critical_c_entry call).(TskState)
    (kernel_critical_c_returned call).(TskState) false.
Proof.
  intros environment critical saved_local sg frame observer observer_origin [actual|actual]
    before after [Hcompletion [Hphysical [Hsource Hpacket]]]; simpl in *.
  - destruct Hsource as [code [Hcritical Hresult]].
    eapply task_change_prio_critical_observer_lifetime_result; exact Hcritical.
  - eapply mutex_del_critical_observer_lifetime_result; exact Hsource.
Qed.

(** A concrete instance, sourced only from the two checked critical C
    contracts.  These theorems close their callbacks by their proved
    module results.  Other C families are added by their own actual posts;
    this instance is not used as a claim about arbitrary kernel clients. *)
Section KernelCriticalCSequence.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (saved_local : Armv7aContinuation -> Assertion) (sg : StableGlobVars).

Inductive kernel_critical_c_step : KernelCSegmentRelation :=
| KernelCriticalCStep : forall frame call before after,
    kernel_critical_c_segment environment critical saved_local sg frame call before after ->
    kernel_critical_c_step (kernel_critical_c_entry call) before
      (kernel_critical_c_owner environment critical saved_local sg call (kernel_critical_c_entry call) ** frame)
      false (kernel_critical_c_returned call) after
      (kernel_critical_c_owner environment critical saved_local sg call (kernel_critical_c_returned call) ** frame).

Lemma kernel_critical_c_sequence_resources : forall state before input stopped returned after output,
  kernel_c_sequence kernel_critical_c_step state before input stopped returned after output ->
  input before /\ output after.
Proof.
  apply kernel_c_sequence_resources.
  intros state before input stopped returned after output Hstep; destruct Hstep.
  eapply kernel_critical_c_segment_resources; exact H.
Qed.

Lemma kernel_critical_c_sequence_completed_current_cache :
  forall original returned initial before input stopped current after output,
  kernel_c_sequence kernel_critical_c_step initial before input stopped current after output ->
  task_in_range sg initial.(TskState) -> kernel_call_task_source original initial ->
  sched_current_consistency initial.(TskState) initial.(SchedState) ->
  kernel_call_normal_return original initial returned current -> kernel_call_task_source returned current ->
  stopped = false /\ sched_current_consistency current.(TskState) current.(SchedState).
Proof.
  intros original returned.
  apply (kernel_c_sequence_completed_current_cache kernel_critical_c_step sg original returned).
  - intros state before input stopped current after output Hstep Hstop Hinitial; destruct Hstep.
    eapply kernel_critical_c_segment_preserves_observer; eassumption.
  - intros state before input stopped current after output Hstep; destruct Hstep.
    eapply kernel_critical_c_segment_observer_lifetime_result; eassumption.
Qed.
End KernelCriticalCSequence.







End CriticalComponent.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Import CriticalComponent.

Import CriticalComponent.

Import CriticalComponent.

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
