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

Module DeleteComponent.













Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition task_delete_save_observation environment critical requested phase sg
  original mask saved before returned acquired : Prop :=
  kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original returned mask saved before acquired /\
  task_delete_same_return original before returned acquired /\
  task_delete_phase_rely requested phase sg before acquired /\
  task_delete_protocol_transport sg requested original before returned acquired.

Record task_delete_completed_body_packet environment critical sg requested
  original initial first acquired priority tid node prepared loan
  middle between returned resumed mask saved name
  (restore_observation : task_delete_restore_history environment critical requested
    (TaskDeletePrepared tid node.(taskGeneration)) sg
    first (task_delete_locked prepared) middle between)
  (save_observation : task_delete_save_observation environment critical requested
    (TaskDeletePrepared tid node.(taskGeneration)) sg
    middle mask saved between returned resumed) : Prop := {
  task_delete_completed_preparation :
    task_delete_preparation_history sg requested original initial first acquired
      priority tid node prepared loan;
  task_delete_completed_result :
    task_delete_result_history sg requested name original initial returned
      (task_delete_cut sg prepared resumed tid priority node name)
}.

Lemma task_delete_recycled_body_completed_packet :
  forall environment critical saved_local sg requested original initial first acquired
    priority tid node prepared loan middle between returned resumed mask saved name
    restore_observation save_observation,
  task_delete_preparation_history sg requested original initial first acquired
    priority tid node prepared loan ->
  task_delete_recycled_body environment critical saved_local sg requested original initial
    returned saved resumed (task_delete_cut sg prepared resumed tid priority node name) loan name |--
  coq_prop (task_delete_completed_body_packet environment critical sg requested
    original initial first acquired priority tid node prepared loan
    middle between returned resumed mask saved name restore_observation save_observation) &&
  task_delete_call_masked environment critical saved_local TaskDeleteStable loan
    sg returned saved resumed (task_delete_cut sg prepared resumed tid priority node name).
Proof.
  intros environment critical saved_local sg requested original initial first acquired
    priority tid node prepared loan middle between returned resumed mask saved name
    restore_observation save_observation Hpreparation.
  unfold task_delete_recycled_body; Intros_p Hresult.
  assert (Hpacket : task_delete_completed_body_packet environment critical sg requested
    original initial first acquired priority tid node prepared loan
    middle between returned resumed mask saved name restore_observation save_observation).
  { constructor; [exact Hpreparation|exact Hresult]. }
  entailer!.
Qed.

Lemma task_delete_prepare_single_wait_preserves_observer_active :
  forall before tid node prepared loan observer observer_origin,
  before.(TskState).(inUsedTaskStates) tid = Some node ->
  task_delete_prepare_single_wait before tid node = Some (prepared, loan) ->
  task_invocation_active before.(TskState) observer observer_origin ->
  task_invocation_active prepared.(TskState) observer observer_origin.
Proof.
  intros before tid node prepared loan observer observer_origin Hnode Hprepare Hactive.
  destruct (task_delete_prepare_single_wait_frame before tid node prepared loan Hprepare)
    as [updated [Hstate [Hprio [Hstatus [Hid [Hgen Hsp]]]]]].
  rewrite Hstate.
  eapply glob_task_set_usedtask_preserves_invocation_active; eassumption.
Qed.

Lemma task_delete_preparation_history_preserves_observer_active :
  forall sg observer observer_origin requested original initial first acquired
    priority tid node prepared loan,
  task_delete_preparation_history sg requested original initial first acquired
    priority tid node prepared loan ->
  task_invocation_active acquired.(TskState) observer observer_origin ->
  task_invocation_active (task_delete_locked prepared).(TskState) observer observer_origin.
Proof.
  intros sg observer observer_origin requested original initial first acquired
    priority tid node prepared loan
    [[Hlookup [Hselected [Hlive Hpointer]]] [Hprepare Hrunning]] Hactive.
  change (task_invocation_active prepared.(TskState) observer observer_origin).
  eapply task_delete_prepare_single_wait_preserves_observer_active.
  - exact (proj2 (task_delete_table_lookup_live acquired.(TskState) priority tid node Hlive)).
  - exact Hprepare.
  - exact Hactive.
Qed.

Definition task_delete_recycle_stops_origin tid (origin : TaskInvocationOrigin) : bool :=
  match origin with
  | BootInvocation => false
  | RunningInvocation slot _ => Z.eqb slot tid
  end.

Lemma task_delete_cut_preserves_observer_active :
  forall sg observer observer_origin prepared resumed tid priority node name,
  task_delete_recycle_stops_origin tid observer_origin = false ->
  task_invocation_active resumed.(TskState) observer observer_origin ->
  task_invocation_active (task_delete_cut sg prepared resumed tid priority node name).(TskState)
    observer observer_origin.
Proof.
  intros sg observer observer_origin prepared resumed tid priority node name Hstop Hactive.
  unfold task_delete_cut, task_delete_recycled; cbn [replace_TskS TskState].
  eapply task_recycle_other_invocation_active; [|exact Hactive].
  destruct observer_origin as [|slot generation]; cbn [task_delete_recycle_stops_origin] in Hstop.
  - intros other Hbad; discriminate.
  - apply Z.eqb_neq in Hstop. intros other Hbad; injection Hbad; congruence.
Qed.

Lemma task_delete_prepared_body_source_resources :
  forall environment critical saved_local sg requested original initial first first_saved acquired
    priority tid node added,
  task_delete_prepared_body environment critical saved_local sg requested original initial
    first first_saved acquired priority (task_slot_addr sg tid) tid node added |--
  EX prepared loan,
    coq_prop (task_delete_preparation_history sg requested original initial first acquired
      priority tid node prepared loan /\
      added = (if task_delete_lock_added prepared.(IntrState) then 1 else 0)) &&
    task_delete_call_masked environment critical saved_local
      (TaskDeletePrepared tid node.(taskGeneration)) loan sg first first_saved acquired
      (task_delete_locked prepared).
Proof.
  intros; unfold task_delete_prepared_body; Intros prepared loan.
  Exists prepared loan; unfold task_delete_preparation_history, task_delete_locked; entailer!.
Qed.

Record TaskDeleteFieldsCall : Type := {
  task_delete_fields_requested : Priority;
  task_delete_fields_original : OsSchedCallContext;
  task_delete_fields_initial : UCOS2_Verify_State;
  task_delete_fields_first : OsSchedCallContext;
  task_delete_fields_acquired : UCOS2_Verify_State;
  task_delete_fields_first_saved : Z;
  task_delete_fields_priority : Priority;
  task_delete_fields_tid : TaskID;
  task_delete_fields_node : TaskAbstractState;
  task_delete_fields_prepared : UCOS2_Verify_State;
  task_delete_fields_loan : option FlagWaiterState;
  task_delete_fields_middle : OsSchedCallContext;
  task_delete_fields_between : UCOS2_Verify_State;
  task_delete_fields_returned : OsSchedCallContext;
  task_delete_fields_resumed : UCOS2_Verify_State;
  task_delete_fields_mask : Z;
  task_delete_fields_saved : Z;
  task_delete_fields_name : Z
}.

Inductive TaskDeleteFieldsCut : Type :=
| TaskDeleteFieldsAcquired
| TaskDeleteFieldsPrepared
| TaskDeleteFieldsBetween
| TaskDeleteFieldsResumed
| TaskDeleteFieldsRecycled.

Section TaskDeleteFieldsBody.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (saved_local : Armv7aContinuation -> Assertion) (frame : Assertion)
  (call : TaskDeleteFieldsCall).

Let requested := call.(task_delete_fields_requested).
Let original := call.(task_delete_fields_original).
Let initial := call.(task_delete_fields_initial).
Let first := call.(task_delete_fields_first).
Let acquired := call.(task_delete_fields_acquired).
Let first_saved := call.(task_delete_fields_first_saved).
Let priority := call.(task_delete_fields_priority).
Let tid := call.(task_delete_fields_tid).
Let node := call.(task_delete_fields_node).
Let prepared := call.(task_delete_fields_prepared).
Let loan := call.(task_delete_fields_loan).
Let middle := call.(task_delete_fields_middle).
Let between := call.(task_delete_fields_between).
Let returned := call.(task_delete_fields_returned).
Let resumed := call.(task_delete_fields_resumed).
Let mask := call.(task_delete_fields_mask).
Let saved := call.(task_delete_fields_saved).
Let name := call.(task_delete_fields_name).
Let phase := TaskDeletePrepared tid node.(taskGeneration).
Let result sg := task_delete_cut sg prepared resumed tid priority node name.

Definition task_delete_fields_state sg (cut : TaskDeleteFieldsCut) :=
  match cut with
  | TaskDeleteFieldsAcquired => acquired
  | TaskDeleteFieldsPrepared => task_delete_locked prepared
  | TaskDeleteFieldsBetween => between
  | TaskDeleteFieldsResumed => resumed
  | TaskDeleteFieldsRecycled => result sg
  end.

(** Each phase uses its original C owner. In particular, Prepared is not
    replaced with UCOS2_inv and Recycled has the original resumed mask cut. *)
Definition task_delete_fields_owner sg (cut : TaskDeleteFieldsCut) : Assertion :=
  match cut with
  | TaskDeleteFieldsAcquired =>
      task_delete_live_body environment critical saved_local sg requested original initial
        first first_saved acquired priority (task_slot_addr sg tid) tid node
  | TaskDeleteFieldsPrepared =>
      task_delete_call_masked environment critical saved_local phase loan
        sg first first_saved acquired (task_delete_locked prepared)
  | TaskDeleteFieldsBetween =>
      task_delete_call_closed environment saved_local phase loan sg middle mask between
  | TaskDeleteFieldsResumed =>
      task_delete_call_masked environment critical saved_local phase loan
        sg returned saved resumed resumed
  | TaskDeleteFieldsRecycled =>
      task_delete_call_masked environment critical saved_local TaskDeleteStable loan
        sg returned saved resumed (result sg)
  end.

Definition task_delete_fields_extra_resources sg cut state : Assertion :=
  coq_prop (state = task_delete_fields_state sg cut) && task_delete_fields_owner sg cut.

(** This match is definitionally the root fields-resource family. Its
    Extra branch retains the actual masked/closed phase owner above. *)
Definition task_delete_fields_resources sg
  (cut : KernelClientHeapCut TaskDeleteFieldsCut) state : Assertion :=
  match cut with
  | KernelClientHeapClosed =>
      kernel_client_continuation_fields_world environment.(task_stack_call_continuations)
        (task_create_continuation_local saved_local) sg state
  | KernelClientHeapTaskPublication publication =>
      kernel_client_continuation_fields_publication environment.(task_stack_call_continuations)
        (task_create_continuation_local saved_local) sg publication state
  | KernelClientHeapExtra actual => task_delete_fields_extra_resources sg actual state
  end.

(** Exactly one middle heap joins the actual Restore return, empty Dummy,
    and Save input. Hrestore/Hsave are indices, not fresh existentials chosen
    after the weaker window_history has already discarded their sources. *)
Record task_delete_fields_body_completion sg
  before_heap prepared_heap middle_heap resumed_heap after_heap
  (Hrestore : task_delete_restore_history environment critical requested phase sg
    first (task_delete_locked prepared) middle between)
  (Hsave : task_delete_save_observation environment critical requested phase sg
    middle mask saved between returned resumed) : Prop := {
  task_delete_fields_body_observation :
    task_delete_completed_body_packet environment critical sg requested
      original initial first acquired priority tid node prepared loan
      middle between returned resumed mask saved name Hrestore Hsave;
  task_delete_fields_before_owner :
    (task_delete_fields_owner sg TaskDeleteFieldsAcquired ** frame) before_heap;
  task_delete_fields_prepared_owner :
    (task_delete_fields_owner sg TaskDeleteFieldsPrepared ** frame) prepared_heap;
  task_delete_fields_middle_owner :
    (task_delete_fields_owner sg TaskDeleteFieldsBetween ** frame) middle_heap;
  task_delete_fields_resumed_owner :
    (task_delete_fields_owner sg TaskDeleteFieldsResumed ** frame) resumed_heap;
  task_delete_fields_after_owner :
    (task_delete_fields_owner sg TaskDeleteFieldsRecycled ** frame) after_heap
}.

(** The resource producer at the recycle C post. All earlier cuts are the
    actual retained call cuts. Only the final owner is unfolded here. *)
Lemma task_delete_fields_body_completion_from_c_posts :
  forall sg before_heap prepared_heap middle_heap resumed_heap after_heap Hrestore Hsave,
  task_delete_preparation_history sg requested original initial first acquired
    priority tid node prepared loan ->
  (task_delete_fields_owner sg TaskDeleteFieldsAcquired ** frame) before_heap ->
  (task_delete_fields_owner sg TaskDeleteFieldsPrepared ** frame) prepared_heap ->
  (task_delete_fields_owner sg TaskDeleteFieldsBetween ** frame) middle_heap ->
  (task_delete_fields_owner sg TaskDeleteFieldsResumed ** frame) resumed_heap ->
  (task_delete_recycled_body environment critical saved_local sg requested original initial
    returned saved resumed (result sg) loan name ** frame) after_heap ->
  task_delete_fields_body_completion sg before_heap prepared_heap middle_heap resumed_heap
    after_heap Hrestore Hsave.
Proof.
  intros sg before_heap prepared_heap middle_heap resumed_heap after_heap Hrestore Hsave
    Hpreparation Hbefore Hprepared Hmiddle Hresumed
    [owned [rest [Hjoin [Hrecycled Hframe]]]].
  pose proof (task_delete_recycled_body_completed_packet environment critical saved_local sg
    requested original initial first acquired priority tid node prepared loan
    middle between returned resumed mask saved name Hrestore Hsave Hpreparation
    owned Hrecycled) as [Hpacket Hafter].
  constructor; try assumption.
  exists owned, rest; split; [exact Hjoin|]. split; assumption.
Qed.
End TaskDeleteFieldsBody.

Definition task_delete_heap_cut (owned : Assertion) (snapshot : model) : Assertion :=
  fun heap => heap = snapshot /\ owned heap.

Record TaskDeleteCaptureInputs : Type := {
  delete_capture_environment : TaskStackCallEnvironment;
  delete_capture_critical : CriticalRegionResources;
  delete_capture_saved_local : Armv7aContinuation -> Assertion;
  delete_capture_frame : Assertion;
  delete_capture_globals : StableGlobVars;
  delete_capture_requested : Priority;
  delete_capture_original : OsSchedCallContext;
  delete_capture_initial : UCOS2_Verify_State;
  delete_capture_first : OsSchedCallContext;
  delete_capture_acquired : UCOS2_Verify_State;
  delete_capture_first_saved : Z;
  delete_capture_priority : Priority;
  delete_capture_tid : TaskID;
  delete_capture_node : TaskAbstractState;
  delete_capture_prepared : UCOS2_Verify_State;
  delete_capture_loan : option FlagWaiterState;
  delete_capture_mask : Z;
  delete_capture_name : Z
}.

Definition task_delete_capture_inputs environment critical saved_local frame sg requested
  original initial first acquired first_saved priority tid node prepared loan mask name :=
  {| delete_capture_environment := environment;
     delete_capture_critical := critical;
     delete_capture_saved_local := saved_local;
     delete_capture_frame := frame;
     delete_capture_globals := sg;
     delete_capture_requested := requested;
     delete_capture_original := original;
     delete_capture_initial := initial;
     delete_capture_first := first;
     delete_capture_acquired := acquired;
     delete_capture_first_saved := first_saved;
     delete_capture_priority := priority;
     delete_capture_tid := tid;
     delete_capture_node := node;
     delete_capture_prepared := prepared;
     delete_capture_loan := loan;
     delete_capture_mask := mask;
     delete_capture_name := name |}.

Definition task_delete_capture_phase inputs :=
  TaskDeletePrepared inputs.(delete_capture_tid) inputs.(delete_capture_node).(taskGeneration).

Definition task_delete_capture_preparation inputs :=
  task_delete_preparation_history inputs.(delete_capture_globals) inputs.(delete_capture_requested)
    inputs.(delete_capture_original) inputs.(delete_capture_initial) inputs.(delete_capture_first)
    inputs.(delete_capture_acquired) inputs.(delete_capture_priority) inputs.(delete_capture_tid)
    inputs.(delete_capture_node) inputs.(delete_capture_prepared) inputs.(delete_capture_loan).

Definition task_delete_capture_before_owner inputs : Assertion :=
  task_delete_live_body inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_saved_local) inputs.(delete_capture_globals) inputs.(delete_capture_requested)
    inputs.(delete_capture_original) inputs.(delete_capture_initial) inputs.(delete_capture_first)
    inputs.(delete_capture_first_saved) inputs.(delete_capture_acquired) inputs.(delete_capture_priority)
    (task_slot_addr inputs.(delete_capture_globals) inputs.(delete_capture_tid))
    inputs.(delete_capture_tid) inputs.(delete_capture_node) ** inputs.(delete_capture_frame).

Definition task_delete_capture_prepared_owner inputs : Assertion :=
  task_delete_call_masked inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_saved_local) (task_delete_capture_phase inputs) inputs.(delete_capture_loan)
    inputs.(delete_capture_globals) inputs.(delete_capture_first) inputs.(delete_capture_first_saved)
    inputs.(delete_capture_acquired) (task_delete_locked inputs.(delete_capture_prepared)) **
  inputs.(delete_capture_frame).

Definition task_delete_capture_middle_owner inputs middle between : Assertion :=
  task_delete_call_closed inputs.(delete_capture_environment) inputs.(delete_capture_saved_local)
    (task_delete_capture_phase inputs) inputs.(delete_capture_loan) inputs.(delete_capture_globals)
    middle inputs.(delete_capture_mask) between ** inputs.(delete_capture_frame).

Definition task_delete_capture_restore_history inputs middle between :=
  task_delete_restore_history inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_requested) (task_delete_capture_phase inputs) inputs.(delete_capture_globals)
    inputs.(delete_capture_first) (task_delete_locked inputs.(delete_capture_prepared)) middle between.

Record TaskDeleteRestoreCapture : Type := {
  delete_restore_inputs : TaskDeleteCaptureInputs;
  delete_restore_before_heap : model;
  delete_restore_prepared_heap : model;
  delete_restore_middle : OsSchedCallContext;
  delete_restore_between : UCOS2_Verify_State;
  delete_restore_middle_heap : model;
  delete_restore_preparation : task_delete_capture_preparation delete_restore_inputs;
  delete_restore_history : task_delete_capture_restore_history delete_restore_inputs
    delete_restore_middle delete_restore_between;
  delete_restore_before_owned :
    task_delete_capture_before_owner delete_restore_inputs delete_restore_before_heap;
  delete_restore_prepared_owned :
    task_delete_capture_prepared_owner delete_restore_inputs delete_restore_prepared_heap;
  delete_restore_middle_owned : task_delete_capture_middle_owner delete_restore_inputs
    delete_restore_middle delete_restore_between delete_restore_middle_heap
}.

Definition task_delete_make_restore_capture inputs before_heap prepared_heap middle between middle_heap
  Hpreparation Hrestore Hbefore Hprepared Hmiddle : TaskDeleteRestoreCapture :=
  {| delete_restore_inputs := inputs;
     delete_restore_before_heap := before_heap;
     delete_restore_prepared_heap := prepared_heap;
     delete_restore_middle := middle;
     delete_restore_between := between;
     delete_restore_middle_heap := middle_heap;
     delete_restore_preparation := Hpreparation;
     delete_restore_history := Hrestore;
     delete_restore_before_owned := Hbefore;
     delete_restore_prepared_owned := Hprepared;
     delete_restore_middle_owned := Hmiddle |}.

Definition task_delete_capture_save_observation restore saved returned resumed :=
  let inputs := restore.(delete_restore_inputs) in
  task_delete_save_observation inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_requested) (task_delete_capture_phase inputs) inputs.(delete_capture_globals)
    restore.(delete_restore_middle) inputs.(delete_capture_mask) saved restore.(delete_restore_between)
    returned resumed.

Definition task_delete_capture_resumed_owner restore saved returned resumed : Assertion :=
  let inputs := restore.(delete_restore_inputs) in
  task_delete_call_masked inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_saved_local) (task_delete_capture_phase inputs) inputs.(delete_capture_loan)
    inputs.(delete_capture_globals) returned saved resumed resumed ** inputs.(delete_capture_frame).

Record TaskDeleteSaveCapture : Type := {
  delete_save_restore : TaskDeleteRestoreCapture;
  delete_save_saved : Z;
  delete_save_returned : OsSchedCallContext;
  delete_save_resumed : UCOS2_Verify_State;
  delete_save_resumed_heap : model;
  delete_save_observation : task_delete_capture_save_observation delete_save_restore delete_save_saved
    delete_save_returned delete_save_resumed;
  delete_save_resumed_owned : task_delete_capture_resumed_owner delete_save_restore delete_save_saved
    delete_save_returned delete_save_resumed delete_save_resumed_heap
}.

Definition task_delete_make_save_capture restore saved returned resumed resumed_heap
  Hsave Hresumed : TaskDeleteSaveCapture :=
  {| delete_save_restore := restore;
     delete_save_saved := saved;
     delete_save_returned := returned;
     delete_save_resumed := resumed;
     delete_save_resumed_heap := resumed_heap;
     delete_save_observation := Hsave;
     delete_save_resumed_owned := Hresumed |}.

Definition task_delete_fields_call_from_capture capture : TaskDeleteFieldsCall :=
  let restore := capture.(delete_save_restore) in
  let inputs := restore.(delete_restore_inputs) in
  {| task_delete_fields_requested := inputs.(delete_capture_requested);
     task_delete_fields_original := inputs.(delete_capture_original);
     task_delete_fields_initial := inputs.(delete_capture_initial);
     task_delete_fields_first := inputs.(delete_capture_first);
     task_delete_fields_acquired := inputs.(delete_capture_acquired);
     task_delete_fields_first_saved := inputs.(delete_capture_first_saved);
     task_delete_fields_priority := inputs.(delete_capture_priority);
     task_delete_fields_tid := inputs.(delete_capture_tid);
     task_delete_fields_node := inputs.(delete_capture_node);
     task_delete_fields_prepared := inputs.(delete_capture_prepared);
     task_delete_fields_loan := inputs.(delete_capture_loan);
     task_delete_fields_middle := restore.(delete_restore_middle);
     task_delete_fields_between := restore.(delete_restore_between);
     task_delete_fields_returned := capture.(delete_save_returned);
     task_delete_fields_resumed := capture.(delete_save_resumed);
     task_delete_fields_mask := inputs.(delete_capture_mask);
     task_delete_fields_saved := capture.(delete_save_saved);
     task_delete_fields_name := inputs.(delete_capture_name) |}.

Definition task_delete_capture_cut capture :=
  let inputs := capture.(delete_save_restore).(delete_restore_inputs) in
  task_delete_cut inputs.(delete_capture_globals) inputs.(delete_capture_prepared)
    capture.(delete_save_resumed) inputs.(delete_capture_tid) inputs.(delete_capture_priority)
    inputs.(delete_capture_node) inputs.(delete_capture_name).

Definition task_delete_capture_completed capture after_heap : Prop :=
  let restore := capture.(delete_save_restore) in
  let inputs := restore.(delete_restore_inputs) in
  task_delete_fields_body_completion inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_saved_local) inputs.(delete_capture_frame) (task_delete_fields_call_from_capture capture)
    inputs.(delete_capture_globals) restore.(delete_restore_before_heap) restore.(delete_restore_prepared_heap)
    restore.(delete_restore_middle_heap) capture.(delete_save_resumed_heap) after_heap
    restore.(delete_restore_history) capture.(delete_save_observation).

Definition task_delete_capture_recycled_owner capture : Assertion :=
  let inputs := capture.(delete_save_restore).(delete_restore_inputs) in
  task_delete_call_masked inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_saved_local) TaskDeleteStable inputs.(delete_capture_loan)
    inputs.(delete_capture_globals) capture.(delete_save_returned) capture.(delete_save_saved)
    capture.(delete_save_resumed) (task_delete_capture_cut capture) ** inputs.(delete_capture_frame).

Definition task_delete_capture_body_output capture : Assertion :=
  EX after_heap, coq_prop (task_delete_capture_completed capture after_heap) &&
    task_delete_heap_cut (task_delete_capture_recycled_owner capture) after_heap.

Lemma task_delete_capture_recycled_body_output : forall capture,
  let restore := capture.(delete_save_restore) in
  let inputs := restore.(delete_restore_inputs) in
  task_delete_recycled_body inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_saved_local) inputs.(delete_capture_globals) inputs.(delete_capture_requested)
    inputs.(delete_capture_original) inputs.(delete_capture_initial) capture.(delete_save_returned)
    capture.(delete_save_saved) capture.(delete_save_resumed) (task_delete_capture_cut capture)
    inputs.(delete_capture_loan) inputs.(delete_capture_name) ** inputs.(delete_capture_frame) |--
  task_delete_capture_body_output capture.
Proof.
  intros capture restore inputs heap Hrecycled.
  assert (Hcompleted : task_delete_capture_completed capture heap).
  { unfold task_delete_capture_completed.
    eapply task_delete_fields_body_completion_from_c_posts.
    - exact restore.(delete_restore_preparation).
    - exact restore.(delete_restore_before_owned).
    - exact restore.(delete_restore_prepared_owned).
    - exact restore.(delete_restore_middle_owned).
    - exact capture.(delete_save_resumed_owned).
    - exact Hrecycled. }
  exists heap; split; [exact Hcompleted|]. split; [reflexivity|].
  exact (task_delete_fields_after_owner _ _ _ _ _ _ _ _ _ _ _ _ _ Hcompleted).
Qed.

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

Lemma task_delete_prepare_single_wait_preserves_observer_cache :
  forall origin before tid old prepared loan,
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  task_delete_prepare_single_wait before tid old = Some (prepared, loan) ->
  sched_observer_current_cache origin before -> sched_observer_current_cache origin prepared.
Proof.
  intros origin before tid old prepared loan Hold Hprepare Hcache.
  destruct (task_delete_prepare_single_wait_frame before tid old prepared loan Hprepare)
    as [updated [Hstate [Hprio [Hstatus [Hid [Hgen Hsp]]]]]].
  eapply sched_observer_cache_update_task with (tid := tid) (old := old) (updated := updated).
  - exact Hold.
  - exact Hgen.
  - exact Hprio.
  - rewrite Hstate; reflexivity.
  - rewrite Hstate; reflexivity.
  - rewrite Hstate; reflexivity.
  - exact Hcache.
Qed.

Lemma task_delete_locked_preserves_observer_cache : forall origin prepared,
  sched_observer_current_cache origin prepared ->
  sched_observer_current_cache origin (task_delete_locked prepared).
Proof. intros origin prepared Hcache; exact Hcache. Qed.

Lemma task_delete_recycled_preserves_observer_cache :
  forall sg origin tid priority node name resumed added,
  sched_observer_current_cache origin resumed ->
  sched_observer_current_cache origin (task_delete_recycled sg tid priority node name resumed added).
Proof.
  intros sg origin tid priority node name resumed added Hcache.
  eapply sched_observer_cache_fields_backward with (before := resumed);
    [reflexivity|reflexivity| |exact Hcache].
  intros slot after Hafter.
  change (task_unlink_used_map resumed.(TskState).(inUsedTaskStates) tid node slot = Some after) in Hafter.
  destruct (task_unlink_used_map_lookup_origin resumed.(TskState).(inUsedTaskStates)
    tid node slot after Hafter) as [Hdifferent [old [Hold Hfields]]].
  exists old; split; [exact Hold|].
  split.
  - pose proof (f_equal taskGeneration Hfields) as Hgen.
    change (after.(taskGeneration) = old.(taskGeneration)) in Hgen; symmetry; exact Hgen.
  - pose proof (f_equal curPrio Hfields) as Hprio.
    change (after.(curPrio) = old.(curPrio)) in Hprio; symmetry; exact Hprio.
Qed.

Lemma task_delete_cut_preserves_observer_cache :
  forall sg origin prepared resumed tid priority node name,
  sched_observer_current_cache origin resumed ->
  sched_observer_current_cache origin (task_delete_cut sg prepared resumed tid priority node name).
Proof. intros; unfold task_delete_cut; apply task_delete_recycled_preserves_observer_cache; assumption. Qed.

Lemma task_delete_preparation_history_observer_cache :
  forall sg observer_origin requested original initial current acquired priority tid node prepared loan,
  task_delete_preparation_history sg requested original initial current acquired
    priority tid node prepared loan ->
  sched_observer_current_cache observer_origin acquired ->
  sched_observer_current_cache observer_origin (task_delete_locked prepared).
Proof.
  intros sg observer_origin requested original initial current acquired priority tid node prepared loan
    [[Hlookup [Hselected [Hlive Hpointer]]] [Hprepare Hrunning]] Hcache.
  apply task_delete_locked_preserves_observer_cache.
  eapply task_delete_prepare_single_wait_preserves_observer_cache; [|exact Hprepare|exact Hcache].
  exact (proj2 (task_delete_table_lookup_live acquired.(TskState) priority tid node Hlive)).
Qed.

Lemma task_recycle_observer_lifetime_transport : forall sg tasks tid priority node name observer origin,
  task_observer_lifetime_transport observer origin tasks (task_recycle sg tasks tid priority node name).
Proof.
  intros sg tasks tid priority node name observer origin Hscope; split; [exact Hscope|].
  intros [Hreg [Hret Hlive]]; split; [exact Hreg|]. split; [exact Hret|].
  destruct origin as [|slot generation]; [exact I|].
  destruct Hlive as [post [Hpost Hgen]].
  destruct (task_unlink_used_map_lookup_origin tasks.(inUsedTaskStates) tid node slot post Hpost)
    as [Hneq [old [Hold Hfields]]].
  exists old; split; [exact Hold|].
  pose proof (f_equal taskGeneration Hfields) as Hg; simpl in Hg; congruence.
Qed.

Lemma task_recycle_observer_lifetime_result : forall sg tasks tid priority node name observer origin,
  task_observer_lifetime_result observer origin tasks (task_recycle sg tasks tid priority node name)
    (task_delete_recycle_stops_origin tid origin).
Proof.
  intros; split; [apply task_recycle_observer_lifetime_transport|].
  intros Hlife Hstop [_ [_ Hlive]].
  destruct origin as [|slot generation]; [discriminate|].
  apply Z.eqb_eq in Hstop; subst slot.
  exact (task_recycle_invalidates_origin sg tasks tid priority node name generation Hlive).
Qed.

Lemma task_delete_preparation_observer_lifetime_transport :
  forall sg observer origin requested original initial first acquired priority tid node prepared loan,
  task_delete_preparation_history sg requested original initial first acquired
    priority tid node prepared loan ->
  task_observer_lifetime_transport observer origin acquired.(TskState) (task_delete_locked prepared).(TskState).
Proof.
  intros sg observer origin requested original initial first acquired priority tid node prepared loan
    [[Hlookup [Hselected [Hlive Hpointer]]] [Hprepare Hrunning]].
  change (task_observer_lifetime_transport observer origin acquired.(TskState) prepared.(TskState)).
  destruct (task_delete_prepare_single_wait_frame acquired tid node prepared loan Hprepare)
    as [updated [Hstate [Hprio [Hstatus [Hid [Hgen Hsp]]]]]].
  rewrite Hstate; eapply task_update_observer_lifetime_transport; [|exact Hgen].
  exact (proj2 (task_delete_table_lookup_live acquired.(TskState) priority tid node Hlive)).
Qed.

Lemma task_delete_cut_observer_lifetime_result : forall sg observer origin prepared resumed tid priority node name,
  task_observer_lifetime_result observer origin resumed.(TskState)
    (task_delete_cut sg prepared resumed tid priority node name).(TskState)
    (task_delete_recycle_stops_origin tid origin).
Proof.
  intros; change (task_observer_lifetime_result observer origin resumed.(TskState)
    (task_recycle sg resumed.(TskState) tid priority (task_delete_prepared_node node) name)
    (task_delete_recycle_stops_origin tid origin)).
  apply task_recycle_observer_lifetime_result.
Qed.



(** This leaf is the actual own-store preparation, before either window.
    It contains no future returned-state or cache/lifetime premise. *)
Record task_delete_prepare_c_completion (inputs : TaskDeleteCaptureInputs)
  (before_heap prepared_heap : model) : Prop := {
  task_delete_prepare_c_history : task_delete_capture_preparation inputs;
  task_delete_prepare_c_input : task_delete_capture_before_owner inputs before_heap;
  task_delete_prepare_c_output : task_delete_capture_prepared_owner inputs prepared_heap
}.

Lemma task_delete_prepare_c_completion_from_post :
  forall environment critical saved_local sg requested original initial first first_saved acquired
    priority tid node added mask name frame before_heap prepared_heap,
  (task_delete_live_body environment critical saved_local sg requested original initial first first_saved
    acquired priority (task_slot_addr sg tid) tid node ** frame) before_heap ->
  (task_delete_prepared_body environment critical saved_local sg requested original initial first first_saved
    acquired priority (task_slot_addr sg tid) tid node added ** frame) prepared_heap ->
  exists prepared loan,
    added = (if task_delete_lock_added prepared.(IntrState) then 1 else 0) /\
    task_delete_prepare_c_completion
      (task_delete_capture_inputs environment critical saved_local frame sg requested original initial first
        acquired first_saved priority tid node prepared loan mask name) before_heap prepared_heap.
Proof.
  intros environment critical saved_local sg requested original initial first first_saved acquired
    priority tid node added mask name frame before_heap prepared_heap Hbefore
    [owned [rest [Hjoin [Hpost Hframe]]]].
  destruct (task_delete_prepared_body_source_resources environment critical saved_local sg requested
    original initial first first_saved acquired priority tid node added owned Hpost)
    as [prepared [loan [[Hprep Hadded] Hmasked]]].
  exists prepared, loan; split; [exact Hadded|].
  constructor; [exact Hprep|exact Hbefore|].
  exists owned, rest; split; [exact Hjoin|]. split; assumption.
Qed.

Lemma task_delete_restore_capture_prepare_completion : forall restore,
  task_delete_prepare_c_completion restore.(delete_restore_inputs)
    restore.(delete_restore_before_heap) restore.(delete_restore_prepared_heap).
Proof.
  intro restore; constructor.
  - exact restore.(delete_restore_preparation).
  - exact restore.(delete_restore_before_owned).
  - exact restore.(delete_restore_prepared_owned).
Qed.

(** Root's segment union can include these two actual constructors. The
    metadata and owners come from the captured C cuts, including the
    Prepared owner and the recycled-current free-image alternative. *)
Definition task_delete_capture_context environment critical sg inputs : Prop :=
  inputs.(delete_capture_environment) = environment /\
  inputs.(delete_capture_critical) = critical /\
  inputs.(delete_capture_globals) = sg.

Lemma task_delete_capture_inputs_context :
  forall environment critical saved_local frame sg requested original initial first acquired first_saved
    priority tid node prepared loan mask name,
  task_delete_capture_context environment critical sg
    (task_delete_capture_inputs environment critical saved_local frame sg requested original initial first
      acquired first_saved priority tid node prepared loan mask name).
Proof. intros; repeat split; reflexivity. Qed.

Inductive task_delete_own_c_segment environment critical sg
  (observer : nat) (observer_origin : TaskInvocationOrigin) :
  KernelCSegmentRelation :=
| TaskDeleteCPrepare : forall inputs before_heap prepared_heap,
    task_delete_capture_context environment critical sg inputs ->
    task_delete_prepare_c_completion inputs before_heap prepared_heap ->
    task_delete_own_c_segment environment critical sg observer observer_origin
      inputs.(delete_capture_acquired) before_heap (task_delete_capture_before_owner inputs) false
      (task_delete_locked inputs.(delete_capture_prepared)) prepared_heap (task_delete_capture_prepared_owner inputs)
| TaskDeleteCRecycle : forall capture after_heap,
    task_delete_capture_context environment critical sg
      capture.(delete_save_restore).(delete_restore_inputs) ->
    task_delete_capture_completed capture after_heap ->
    task_delete_own_c_segment environment critical sg observer observer_origin
      capture.(delete_save_resumed) capture.(delete_save_resumed_heap)
      (task_delete_capture_resumed_owner capture.(delete_save_restore) capture.(delete_save_saved)
        capture.(delete_save_returned) capture.(delete_save_resumed))
      (task_delete_recycle_stops_origin capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_tid)
        observer_origin)
      (task_delete_capture_cut capture) after_heap (task_delete_capture_recycled_owner capture).

Lemma task_delete_recycle_c_segment_from_post : forall environment critical sg observer origin capture after_heap,
  let inputs := capture.(delete_save_restore).(delete_restore_inputs) in
  task_delete_capture_context environment critical sg inputs ->
  (task_delete_recycled_body inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_saved_local) inputs.(delete_capture_globals) inputs.(delete_capture_requested)
    inputs.(delete_capture_original) inputs.(delete_capture_initial) capture.(delete_save_returned)
    capture.(delete_save_saved) capture.(delete_save_resumed) (task_delete_capture_cut capture)
    inputs.(delete_capture_loan) inputs.(delete_capture_name) ** inputs.(delete_capture_frame)) after_heap ->
  task_delete_own_c_segment environment critical sg observer origin
    capture.(delete_save_resumed) capture.(delete_save_resumed_heap)
    (task_delete_capture_resumed_owner capture.(delete_save_restore) capture.(delete_save_saved)
      capture.(delete_save_returned) capture.(delete_save_resumed))
    (task_delete_recycle_stops_origin inputs.(delete_capture_tid) origin)
    (task_delete_capture_cut capture) after_heap (task_delete_capture_recycled_owner capture).
Proof.
  intros environment critical sg observer origin capture after_heap inputs Hcontext Hpost.
  apply TaskDeleteCRecycle; [exact Hcontext|].
  destruct (task_delete_capture_recycled_body_output capture after_heap Hpost)
    as [actual_heap [Hcompleted [Heq Howned]]].
  subst actual_heap; exact Hcompleted.
Qed.

Lemma task_delete_own_c_segment_resources : forall environment critical sg observer origin state before input stopped returned after output,
  task_delete_own_c_segment environment critical sg observer origin state before input stopped returned after output ->
  input before /\ output after.
Proof.
  intros environment critical sg observer origin state before input stopped returned after output Hstep.
  destruct Hstep as [inputs before_heap prepared_heap Hcontext Hcompletion|capture after_heap Hcontext Hcompletion].
  - destruct Hcompletion as [Hprep Hbefore Hafter]; split; assumption.
  - split; [exact capture.(delete_save_resumed_owned)|].
    exact (task_delete_fields_after_owner _ _ _ _ _ _ _ _ _ _ _ _ _ Hcompletion).
Qed.

Lemma task_delete_own_c_segment_preserves_observer :
  forall environment critical sg observer origin state before input stopped returned after output,
  task_delete_own_c_segment environment critical sg observer origin state before input stopped returned after output ->
  stopped = false ->
  task_invocation_active state.(TskState) observer origin /\ sched_observer_current_cache origin state ->
  task_invocation_active returned.(TskState) observer origin /\ sched_observer_current_cache origin returned.
Proof.
  intros environment critical sg observer origin state before input stopped returned after output Hstep Hstop [Hactive Hcache].
  destruct Hstep as [inputs before_heap prepared_heap Hcontext Hcompletion|capture after_heap Hcontext Hcompletion].
  - destruct Hcompletion as [Hprep Hbefore Hafter]; split.
    + eapply task_delete_preparation_history_preserves_observer_active; eassumption.
    + eapply task_delete_preparation_history_observer_cache; eassumption.
  - split.
    + eapply task_delete_cut_preserves_observer_active; eassumption.
    + apply task_delete_cut_preserves_observer_cache; exact Hcache.
Qed.

Lemma task_delete_own_c_segment_observer_lifetime :
  forall environment critical sg observer origin state before input stopped returned after output,
  task_delete_own_c_segment environment critical sg observer origin state before input stopped returned after output ->
  task_observer_lifetime_result observer origin state.(TskState) returned.(TskState) stopped.
Proof.
  intros environment critical sg observer origin state before input stopped returned after output Hstep.
  destruct Hstep as [inputs before_heap prepared_heap Hcontext Hcompletion|capture after_heap Hcontext Hcompletion].
  - destruct Hcompletion as [Hprep Hbefore Hafter].
    apply task_observer_lifetime_result_not_stopped.
    eapply task_delete_preparation_observer_lifetime_transport; exact Hprep.
  - apply task_delete_cut_observer_lifetime_result.
Qed.

Definition task_delete_restore_observation_source environment critical requested phase sg
  original before returned after
  (observation : task_delete_restore_history environment critical requested phase sg
    original before returned after) :
  kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    before false returned.(os_sched_call_origin) after :=
  match observation with conj source _ => source end.

Definition task_delete_save_observation_source environment critical requested phase sg
  original mask saved before returned acquired
  (observation : task_delete_save_observation environment critical requested phase sg
    original mask saved before returned acquired) :
  kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    before false returned.(os_sched_call_origin) acquired :=
  match observation with conj (conj source _) _ => source end.

Definition task_delete_save_observation_history environment critical requested phase sg
  original mask saved before returned acquired
  (observation : task_delete_save_observation environment critical requested phase sg
    original mask saved before returned acquired) :
  task_delete_restore_history environment critical requested phase sg
    original before returned acquired :=
  match observation with conj (conj source _) remaining => conj source remaining end.

Definition task_delete_capture_observer_stopped capture origin restore_stopped save_stopped :=
  orb restore_stopped (orb save_stopped
    (task_delete_recycle_stops_origin capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_tid) origin)).




(** These three resource edges use the existing platform contracts. They
    do not execute or model foreign C work and do not change the kernel
    state. Their distinct heaps are kept in the surrounding C sequence. *)
Section TaskDeletePrimitiveCSegments.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars).

Lemma task_delete_restore_prefix_closed_resources :
  forall saved_local arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    phase loan call saved acquired released cursor before written after frame,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (task_delete_call_masked environment critical saved_local phase loan sg call saved acquired released ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written after ->
  written = kernel_restore_write_cpsr cursor /\
  (task_delete_call_closed environment saved_local phase loan sg call (armv7a_irq_fiq_mask saved) released ** frame) after.
Proof.
  intros saved_local arch restore phase loan call saved acquired released cursor before written after frame
    Hr0 Hmask Hpre Hprefix.
  unfold task_delete_call_masked, kernel_continuation_call_masked in Hpre.
  assert (Hopen :
    critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) call **
    kernel_continuation_inv environment.(task_stack_call_continuations)
      (task_delete_phase_resources phase loan) (task_create_continuation_local saved_local)
      sg (task_stack_call_active_key call) released ** frame |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) call **
    (kernel_continuation_inv environment.(task_stack_call_continuations)
      (task_delete_phase_resources phase loan) (task_create_continuation_local saved_local)
      sg (task_stack_call_active_key call) released ** frame)) by entailer!.
  destruct (armv7a_restore_prefix_releases_critical_region
    environment.(task_stack_call_external) environment.(task_stack_call_platform) critical arch
    restore sg call saved acquired cursor before written after _ Hr0 Hmask (Hopen before Hpre) Hprefix)
    as [Hwritten [Hmemory Howned]].
  split; [exact Hwritten|].
  match type of Howned with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold task_delete_call_closed, kernel_continuation_call_closed; entailer!. }
  exact (Hclose after Howned).
Qed.

Lemma task_delete_restore_suffix_closed_resources :
  forall saved_local arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    phase loan call state word cursor before final_cursor after frame,
  cursor.(kernel_restore_msr_word) = Some word ->
  (task_delete_call_closed environment saved_local phase loan sg call (armv7a_irq_fiq_mask word) state ** frame) before ->
  armv7a_restore_suffix_transition restore cursor before final_cursor after ->
  final_cursor = kernel_restore_branch_lr cursor /\
  (task_delete_call_closed environment saved_local phase loan sg call (armv7a_irq_fiq_mask word) state ** frame) after.
Proof.
  intros saved_local arch restore phase loan call state word cursor before final_cursor after frame Hword Hpre Hsuffix.
  unfold task_delete_call_closed, kernel_continuation_call_closed in Hpre.
  assert (Hopen :
    kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) call (armv7a_irq_fiq_mask word) **
    kernel_continuation_inv environment.(task_stack_call_continuations)
      (task_delete_phase_resources phase loan) (task_create_continuation_local saved_local)
      sg (task_stack_call_active_key call) state ** frame |--
    kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) call (armv7a_irq_fiq_mask word) **
    (kernel_continuation_inv environment.(task_stack_call_continuations)
      (task_delete_phase_resources phase loan) (task_create_continuation_local saved_local)
      sg (task_stack_call_active_key call) state ** frame)) by entailer!.
  destruct (armv7a_restore_suffix_transports_owned_execution
    environment.(task_stack_call_external) environment.(task_stack_call_platform) critical arch
    restore call word cursor before final_cursor after _ Hword (Hopen before Hpre) Hsuffix)
    as [Hfinal [Hmemory Howned]].
  split; [exact Hfinal|].
  match type of Howned with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold task_delete_call_closed, kernel_continuation_call_closed; entailer!. }
  exact (Hclose after Howned).
Qed.

Lemma task_delete_save_suffix_masked_resources :
  forall saved_local arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    phase loan call state mask registers before final_registers acquired after frame,
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (task_delete_call_closed environment saved_local phase loan sg call mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before final_registers acquired after ->
  acquired = state /\ interrupt_saved_value mask final_registers.(kernel_save_r0) /\
  (task_delete_call_masked environment critical saved_local phase loan sg call
    final_registers.(kernel_save_r0) state state ** frame) after.
Proof.
  intros saved_local arch save phase loan call state mask registers before final_registers acquired after frame
    Hreturn Hvalid Hmask Hpre Hsuffix.
  destruct (kernel_continuation_call_uninterrupted_save
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    environment.(task_stack_call_port) critical arch environment.(task_stack_call_continuations)
    save (task_delete_phase_resources phase loan) (task_create_continuation_local saved_local)
    sg (task_stack_call_active_key call) call state mask registers before final_registers acquired after frame
    Hreturn Hvalid Hmask Hpre Hsuffix) as [Hstate [Hr0 [Hsource Howned]]].
  split; [exact Hstate|]. split; [rewrite Hr0; split; assumption|exact Howned].
Qed.

Inductive task_delete_primitive_c_segment : KernelCSegmentRelation :=
| TaskDeleteCRestorePrefix : forall saved_local arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    phase loan call saved acquired released cursor before written after frame,
    cursor.(kernel_restore_r0) = saved ->
    armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
    (task_delete_call_masked environment critical saved_local phase loan sg call saved acquired released ** frame) before ->
    armv7a_restore_prefix_transition restore cursor before written after ->
    task_delete_primitive_c_segment released before
      (task_delete_call_masked environment critical saved_local phase loan sg call saved acquired released ** frame)
      false released after
      (task_delete_call_closed environment saved_local phase loan sg call (armv7a_irq_fiq_mask saved) released ** frame)
| TaskDeleteCRestoreSuffix : forall saved_local arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    phase loan call state word cursor before final_cursor after frame,
    cursor.(kernel_restore_msr_word) = Some word ->
    (task_delete_call_closed environment saved_local phase loan sg call (armv7a_irq_fiq_mask word) state ** frame) before ->
    armv7a_restore_suffix_transition restore cursor before final_cursor after ->
    task_delete_primitive_c_segment state before
      (task_delete_call_closed environment saved_local phase loan sg call (armv7a_irq_fiq_mask word) state ** frame)
      false state after
      (task_delete_call_closed environment saved_local phase loan sg call (armv7a_irq_fiq_mask word) state ** frame)
| TaskDeleteCSaveSuffix : forall saved_local arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    phase loan call state mask registers before final_registers after frame,
    registers.(kernel_save_return_word) = None ->
    valid_os_cpu_sr registers.(kernel_save_cpsr) ->
    armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
    (task_delete_call_closed environment saved_local phase loan sg call mask state ** frame) before ->
    armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before final_registers state after ->
    task_delete_primitive_c_segment state before
      (task_delete_call_closed environment saved_local phase loan sg call mask state ** frame)
      false state after
      (task_delete_call_masked environment critical saved_local phase loan sg call
        final_registers.(kernel_save_r0) state state ** frame).

Lemma task_delete_primitive_c_segment_resources : forall state before input stopped returned after output,
  task_delete_primitive_c_segment state before input stopped returned after output -> input before /\ output after.
Proof.
  intros state before input stopped returned after output Hrun; destruct Hrun.
  - split; [assumption|]. eapply (proj2 (task_delete_restore_prefix_closed_resources
      saved_local arch restore phase loan call saved acquired released cursor before written after frame H H0 H1 H2)).
  - split; [assumption|]. eapply (proj2 (task_delete_restore_suffix_closed_resources
      saved_local arch restore phase loan call state word cursor before final_cursor after frame H H0 H1)).
  - split; [assumption|]. eapply (proj2 (proj2 (task_delete_save_suffix_masked_resources
      saved_local arch save phase loan call state mask registers before final_registers state after frame H H0 H1 H2 H3))).
Qed.

Lemma task_delete_primitive_c_segment_preserves_observer :
  forall observer origin state before input stopped returned after output,
  task_delete_primitive_c_segment state before input stopped returned after output ->
  task_invocation_active state.(TskState) observer origin /\ sched_observer_current_cache origin state ->
  task_invocation_active returned.(TskState) observer origin /\ sched_observer_current_cache origin returned.
Proof. intros observer origin state before input stopped returned after output Hrun; destruct Hrun; auto. Qed.

Lemma task_delete_primitive_c_segment_observer_lifetime :
  forall observer origin state before input stopped returned after output,
  task_delete_primitive_c_segment state before input stopped returned after output ->
  task_observer_lifetime_result observer origin state.(TskState) returned.(TskState) stopped.
Proof.
  intros observer origin state before input stopped returned after output Hrun; destruct Hrun;
    apply task_observer_lifetime_result_not_stopped, task_observer_lifetime_transport_refl.
Qed.
End TaskDeletePrimitiveCSegments.

(** The selected program is indexed by its actual C sequence proof. Its
    execution relation is built FROM that witness; it is not an old
    execution paired afterwards with an arbitrary endpoint-equal tree.
    No cache, lifetime, stop=false or eventual-return property occurs in
    this selection interface. *)
Section TaskDeleteSelectedCWindow.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (saved_local : Armv7aContinuation -> Assertion) (sg : StableGlobVars)
  (segment : KernelCSegmentRelation).

Definition TaskDeleteCProgramSelection : Type :=
  forall phase loan original before returned after mask before_heap after_heap (frame : Assertion) stopped,
  kernel_c_sequence segment before before_heap
    (task_delete_call_closed environment saved_local phase loan sg original mask before ** frame)
    stopped after after_heap
    (task_delete_call_closed environment saved_local phase loan sg returned mask after ** frame) -> Prop.

Context (selected : TaskDeleteCProgramSelection).

Inductive task_delete_selected_c_execution :
  TaskDeletePhase -> OsSchedCallContext -> UCOS2_Verify_State ->
    OsSchedCallContext -> UCOS2_Verify_State -> model -> model -> Prop :=
| TaskDeleteSelectedCExecution :
    forall phase loan original before returned after mask before_heap after_heap frame stopped
      (run : kernel_c_sequence segment before before_heap
        (task_delete_call_closed environment saved_local phase loan sg original mask before ** frame)
        stopped after after_heap
        (task_delete_call_closed environment saved_local phase loan sg returned mask after ** frame)),
    selected phase loan original before returned after mask before_heap after_heap frame stopped run ->
    task_delete_selected_c_execution phase original before returned after before_heap after_heap.

Definition task_delete_selected_c_environment : TaskDeleteCompletedEnvironment :=
  {| task_delete_environment_execution := task_delete_selected_c_execution;
     task_delete_completed_interval := task_delete_selected_c_execution |}.

Lemma task_delete_selected_c_environment_applicable :
  task_delete_environment_applicable task_delete_selected_c_environment.
Proof. intros phase original before returned after before_heap after_heap Hactual; exact Hactual. Qed.

(** This is the pre-existing TaskDel conditional C rely, instantiated on
    the selected execution above. The selected program must discharge it
    at its real call boundary. It is not strengthened by a new observer
    preservation or current-cache law. *)
Context (requested : Priority)
  (environment_rely : task_delete_c_environment environment critical saved_local requested sg
    task_delete_selected_c_environment).

Definition task_delete_selected_c_return
  phase loan original before returned after mask before_heap after_heap frame stopped
  (run : kernel_c_sequence segment before before_heap
    (task_delete_call_closed environment saved_local phase loan sg original mask before ** frame)
    stopped after after_heap
    (task_delete_call_closed environment saved_local phase loan sg returned mask after ** frame))
  (selection : selected phase loan original before returned after mask before_heap after_heap frame stopped run)
  (owned : (task_delete_call_closed environment saved_local phase loan sg original mask before ** frame) before_heap) :=
  task_delete_actual_environment_return environment critical saved_local requested sg
    task_delete_selected_c_environment phase loan original before returned after mask before_heap after_heap frame
    environment_rely
    (TaskDeleteSelectedCExecution phase loan original before returned after mask before_heap after_heap frame
      stopped run selection) owned.

Definition task_delete_selected_c_history
  phase loan original before returned after mask before_heap after_heap frame stopped run selection owned :
  task_delete_restore_history environment critical requested phase sg original before returned after :=
  match task_delete_selected_c_return phase loan original before returned after mask before_heap after_heap frame
    stopped run selection owned with
  | conj source (conj normal (conj phase_rely (conj protocol resources))) =>
      conj source (conj normal (conj phase_rely protocol))
  end.

Definition task_delete_selected_c_source
  phase loan original before returned after mask before_heap after_heap frame stopped run selection owned :=
  match task_delete_selected_c_return phase loan original before returned after mask before_heap after_heap frame
    stopped run selection owned with conj source _ => source end.

(** The source proof index is computed here. There is no constructor that
    accepts an unrelated source proof and an endpoint-equal C sequence. *)
Inductive task_delete_joint_c_window :
  forall phase loan original before returned after mask before_heap after_heap frame,
  task_delete_restore_history environment critical requested phase sg original before returned after -> bool -> Prop :=
| TaskDeleteJointCWindow :
    forall phase loan original before returned after mask before_heap after_heap frame stopped run selection owned,
    task_delete_joint_c_window phase loan original before returned after mask before_heap after_heap frame
      (task_delete_selected_c_history phase loan original before returned after mask before_heap after_heap frame
        stopped run selection owned) stopped.

Lemma task_delete_joint_c_window_source :
  forall phase loan original before returned after mask before_heap after_heap frame stopped run selection owned,
  task_delete_restore_observation_source environment critical requested phase sg original before returned after
    (task_delete_selected_c_history phase loan original before returned after mask before_heap after_heap frame
      stopped run selection owned) =
  task_delete_selected_c_source phase loan original before returned after mask before_heap after_heap frame
    stopped run selection owned.
Proof.
  intros; unfold task_delete_restore_observation_source, task_delete_selected_c_history,
    task_delete_selected_c_source.
  destruct (task_delete_selected_c_return phase loan original before returned after mask before_heap after_heap frame
    stopped run selection owned) as [source [normal [phase_rely [protocol resources]]]]; reflexivity.
Qed.

Lemma task_delete_joint_c_window_sequence :
  forall phase loan original before returned after mask before_heap after_heap frame history stopped,
  task_delete_joint_c_window phase loan original before returned after mask before_heap after_heap frame history stopped ->
  kernel_c_sequence segment before before_heap
    (task_delete_call_closed environment saved_local phase loan sg original mask before ** frame)
    stopped after after_heap
    (task_delete_call_closed environment saved_local phase loan sg returned mask after ** frame).
Proof. intros until stopped; intro Hwindow; destruct Hwindow; exact run. Qed.

Lemma task_delete_joint_c_window_resources :
  forall phase loan original before returned after mask before_heap after_heap frame history stopped,
  task_delete_joint_c_window phase loan original before returned after mask before_heap after_heap frame history stopped ->
  (task_delete_call_closed environment saved_local phase loan sg original mask before ** frame) before_heap /\
  (task_delete_call_closed environment saved_local phase loan sg returned mask after ** frame) after_heap.
Proof.
  intros until stopped; intro Hwindow; destruct Hwindow.
  split; [exact owned|].
  exact (proj2 (proj2 (proj2 (proj2
    (task_delete_selected_c_return phase loan original before returned after mask before_heap after_heap frame
      stopped run selection owned))))).
Qed.
End TaskDeleteSelectedCWindow.

(** The C selection and existing C rely are local to the exact capture's
    environment, phase resources and saved-local interpretation. *)
Definition TaskDeleteCaptureCSelection segment inputs : Type :=
  TaskDeleteCProgramSelection inputs.(delete_capture_environment) inputs.(delete_capture_saved_local)
    inputs.(delete_capture_globals) segment.

Definition task_delete_capture_c_rely inputs segment (selected : TaskDeleteCaptureCSelection segment inputs) : Prop :=
  task_delete_c_environment inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_saved_local) inputs.(delete_capture_requested) inputs.(delete_capture_globals)
    (task_delete_selected_c_environment inputs.(delete_capture_environment) inputs.(delete_capture_saved_local)
      inputs.(delete_capture_globals) segment selected).

(** A full Restore keeps its two primitive heap cuts around the one
    selected C window. Its history index is the original capture field. *)
Definition task_delete_restore_capture_c_window segment restore
  (selected : TaskDeleteCaptureCSelection segment restore.(delete_restore_inputs))
  (rely : task_delete_capture_c_rely restore.(delete_restore_inputs) segment selected) stopped : Prop :=
  let inputs := restore.(delete_restore_inputs) in
  exists prefix_heap environment_heap,
    task_delete_primitive_c_segment inputs.(delete_capture_environment) inputs.(delete_capture_critical)
      inputs.(delete_capture_globals)
      (task_delete_locked inputs.(delete_capture_prepared)) restore.(delete_restore_prepared_heap)
      (task_delete_capture_prepared_owner inputs) false
      (task_delete_locked inputs.(delete_capture_prepared)) prefix_heap
      (task_delete_capture_middle_owner inputs inputs.(delete_capture_first)
        (task_delete_locked inputs.(delete_capture_prepared))) /\
    task_delete_joint_c_window inputs.(delete_capture_environment) inputs.(delete_capture_critical)
      inputs.(delete_capture_saved_local) inputs.(delete_capture_globals) segment selected
      inputs.(delete_capture_requested) rely
      (task_delete_capture_phase inputs) inputs.(delete_capture_loan) inputs.(delete_capture_first)
      (task_delete_locked inputs.(delete_capture_prepared)) restore.(delete_restore_middle)
      restore.(delete_restore_between) inputs.(delete_capture_mask) prefix_heap environment_heap
      inputs.(delete_capture_frame) restore.(delete_restore_history) stopped /\
    task_delete_primitive_c_segment inputs.(delete_capture_environment) inputs.(delete_capture_critical)
      inputs.(delete_capture_globals)
      restore.(delete_restore_between) environment_heap
      (task_delete_capture_middle_owner inputs restore.(delete_restore_middle) restore.(delete_restore_between)) false
      restore.(delete_restore_between) restore.(delete_restore_middle_heap)
      (task_delete_capture_middle_owner inputs restore.(delete_restore_middle) restore.(delete_restore_between)).

Definition task_delete_restore_capture_from_c_window inputs segment selected
  (rely : task_delete_capture_c_rely inputs segment selected)
  before_heap prepared_heap middle between middle_heap prefix_heap environment_heap stopped
  (preparation : task_delete_prepare_c_completion inputs before_heap prepared_heap)
  (history : task_delete_capture_restore_history inputs middle between)
  (prefix : task_delete_primitive_c_segment inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_globals)
    (task_delete_locked inputs.(delete_capture_prepared)) prepared_heap
    (task_delete_capture_prepared_owner inputs) false
    (task_delete_locked inputs.(delete_capture_prepared)) prefix_heap
    (task_delete_capture_middle_owner inputs inputs.(delete_capture_first)
      (task_delete_locked inputs.(delete_capture_prepared))))
  (window : task_delete_joint_c_window inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_saved_local) inputs.(delete_capture_globals) segment selected
    inputs.(delete_capture_requested) rely
    (task_delete_capture_phase inputs) inputs.(delete_capture_loan) inputs.(delete_capture_first)
    (task_delete_locked inputs.(delete_capture_prepared)) middle between inputs.(delete_capture_mask)
    prefix_heap environment_heap inputs.(delete_capture_frame) history stopped)
  (suffix : task_delete_primitive_c_segment inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_globals) between environment_heap
    (task_delete_capture_middle_owner inputs middle between) false between middle_heap
    (task_delete_capture_middle_owner inputs middle between)) : TaskDeleteRestoreCapture :=
  task_delete_make_restore_capture inputs before_heap prepared_heap middle between middle_heap
    (task_delete_prepare_c_history inputs before_heap prepared_heap preparation) history
    (task_delete_prepare_c_input inputs before_heap prepared_heap preparation)
    (task_delete_prepare_c_output inputs before_heap prepared_heap preparation)
    (proj2 (task_delete_primitive_c_segment_resources _ _ _ _ _ _ _ _ _ _ suffix)).

Lemma task_delete_restore_capture_from_c_window_joint :
  forall inputs segment selected rely before_heap prepared_heap middle between middle_heap prefix_heap environment_heap
    stopped preparation history prefix window suffix,
  task_delete_restore_capture_c_window segment
    (task_delete_restore_capture_from_c_window inputs segment selected rely before_heap prepared_heap middle between
      middle_heap prefix_heap environment_heap stopped preparation history prefix window suffix)
    selected rely stopped.
Proof. intros; exists prefix_heap, environment_heap; split; [exact prefix|]. split; [exact window|exact suffix]. Qed.

Lemma task_delete_restore_capture_from_c_window_source :
  forall inputs segment selected rely before_heap prepared_heap middle between middle_heap prefix_heap environment_heap
    stopped preparation history prefix window suffix,
  delete_restore_history
    (task_delete_restore_capture_from_c_window inputs segment selected rely before_heap prepared_heap middle between
      middle_heap prefix_heap environment_heap stopped preparation history prefix window suffix) = history.
Proof. reflexivity. Qed.

(** Save's observation is rebuilt from the SAME selected history. The
    actual suffix supplies saved; no new source trace is chosen. *)
Definition task_delete_save_observation_from_history environment critical requested phase sg
  original mask saved before returned after
  (history : task_delete_restore_history environment critical requested phase sg original before returned after)
  (saved_value : interrupt_saved_value mask saved) :
  task_delete_save_observation environment critical requested phase sg original mask saved before returned after :=
  match history with
  | conj source (conj (conj (conj invocation (conj origin stack)) available) (conj phase_rely protocol)) =>
      conj (conj source (conj invocation (conj origin (conj stack saved_value))))
        (conj (conj (conj invocation (conj origin stack)) available) (conj phase_rely protocol))
  end.

Lemma task_delete_save_observation_from_history_keeps_history :
  forall environment critical requested phase sg original mask saved before returned after history saved_value,
  task_delete_save_observation_history environment critical requested phase sg original mask saved before returned after
    (task_delete_save_observation_from_history environment critical requested phase sg original mask saved before
      returned after history saved_value) = history.
Proof.
  intros environment critical requested phase sg original mask saved before returned after
    [source [[[invocation [origin stack]] available] [phase_rely protocol]]] saved_value.
  reflexivity.
Qed.

Definition task_delete_save_capture_c_window segment capture
  (selected : TaskDeleteCaptureCSelection segment capture.(delete_save_restore).(delete_restore_inputs))
  (rely : task_delete_capture_c_rely capture.(delete_save_restore).(delete_restore_inputs) segment selected)
  stopped : Prop :=
  let restore := capture.(delete_save_restore) in
  let inputs := restore.(delete_restore_inputs) in
  exists environment_heap,
    task_delete_joint_c_window inputs.(delete_capture_environment) inputs.(delete_capture_critical)
      inputs.(delete_capture_saved_local) inputs.(delete_capture_globals) segment selected
      inputs.(delete_capture_requested) rely
      (task_delete_capture_phase inputs) inputs.(delete_capture_loan) restore.(delete_restore_middle)
      restore.(delete_restore_between) capture.(delete_save_returned) capture.(delete_save_resumed)
      inputs.(delete_capture_mask) restore.(delete_restore_middle_heap) environment_heap inputs.(delete_capture_frame)
      (task_delete_save_observation_history inputs.(delete_capture_environment) inputs.(delete_capture_critical)
        inputs.(delete_capture_requested) (task_delete_capture_phase inputs) inputs.(delete_capture_globals)
        restore.(delete_restore_middle) inputs.(delete_capture_mask) capture.(delete_save_saved)
        restore.(delete_restore_between) capture.(delete_save_returned) capture.(delete_save_resumed)
        capture.(delete_save_observation)) stopped /\
    task_delete_primitive_c_segment inputs.(delete_capture_environment) inputs.(delete_capture_critical)
      inputs.(delete_capture_globals) capture.(delete_save_resumed) environment_heap
      (task_delete_capture_middle_owner inputs capture.(delete_save_returned) capture.(delete_save_resumed)) false
      capture.(delete_save_resumed) capture.(delete_save_resumed_heap)
      (task_delete_capture_resumed_owner restore capture.(delete_save_saved) capture.(delete_save_returned)
        capture.(delete_save_resumed)).

Definition task_delete_capture_save_history restore returned resumed :=
  let inputs := restore.(delete_restore_inputs) in
  task_delete_restore_history inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_requested) (task_delete_capture_phase inputs) inputs.(delete_capture_globals)
    restore.(delete_restore_middle) restore.(delete_restore_between) returned resumed.

Definition task_delete_save_capture_from_c_window restore segment selected
  (rely : task_delete_capture_c_rely restore.(delete_restore_inputs) segment selected)
  saved returned resumed resumed_heap environment_heap stopped
  (history : task_delete_capture_save_history restore returned resumed)
  (saved_value : interrupt_saved_value restore.(delete_restore_inputs).(delete_capture_mask) saved)
  (window : task_delete_joint_c_window
    restore.(delete_restore_inputs).(delete_capture_environment)
    restore.(delete_restore_inputs).(delete_capture_critical)
    restore.(delete_restore_inputs).(delete_capture_saved_local)
    restore.(delete_restore_inputs).(delete_capture_globals) segment selected
    restore.(delete_restore_inputs).(delete_capture_requested) rely
    (task_delete_capture_phase restore.(delete_restore_inputs)) restore.(delete_restore_inputs).(delete_capture_loan)
    restore.(delete_restore_middle) restore.(delete_restore_between) returned resumed
    restore.(delete_restore_inputs).(delete_capture_mask) restore.(delete_restore_middle_heap) environment_heap
    restore.(delete_restore_inputs).(delete_capture_frame) history stopped)
  (suffix : task_delete_primitive_c_segment
    restore.(delete_restore_inputs).(delete_capture_environment)
    restore.(delete_restore_inputs).(delete_capture_critical)
    restore.(delete_restore_inputs).(delete_capture_globals) resumed environment_heap
    (task_delete_capture_middle_owner restore.(delete_restore_inputs) returned resumed) false
    resumed resumed_heap (task_delete_capture_resumed_owner restore saved returned resumed)) : TaskDeleteSaveCapture :=
  let inputs := restore.(delete_restore_inputs) in
  task_delete_make_save_capture restore saved returned resumed resumed_heap
    (task_delete_save_observation_from_history inputs.(delete_capture_environment) inputs.(delete_capture_critical)
      inputs.(delete_capture_requested) (task_delete_capture_phase inputs) inputs.(delete_capture_globals)
      restore.(delete_restore_middle) inputs.(delete_capture_mask) saved restore.(delete_restore_between)
      returned resumed history saved_value)
    (proj2 (task_delete_primitive_c_segment_resources _ _ _ _ _ _ _ _ _ _ suffix)).

Lemma task_delete_save_capture_from_c_window_joint :
  forall restore segment selected rely saved returned resumed resumed_heap environment_heap stopped
    history saved_value window suffix,
  task_delete_save_capture_c_window segment
    (task_delete_save_capture_from_c_window restore segment selected rely saved returned resumed resumed_heap
      environment_heap stopped history saved_value window suffix) selected rely stopped.
Proof.
  intros; destruct history as [source [[[invocation [origin stack]] available] [phase_rely protocol]]].
  unfold task_delete_save_capture_c_window.
  cbn [task_delete_save_capture_from_c_window task_delete_make_save_capture].
  exists environment_heap; split; [exact window|exact suffix].
Qed.

Lemma task_delete_save_capture_from_c_window_source :
  forall restore segment selected rely saved returned resumed resumed_heap environment_heap stopped
    history saved_value window suffix,
  let capture := task_delete_save_capture_from_c_window restore segment selected rely saved returned resumed resumed_heap
    environment_heap stopped history saved_value window suffix in
  let inputs := restore.(delete_restore_inputs) in
  task_delete_save_observation_source inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_requested) (task_delete_capture_phase inputs) inputs.(delete_capture_globals)
    restore.(delete_restore_middle) inputs.(delete_capture_mask) saved restore.(delete_restore_between) returned resumed
    capture.(delete_save_observation) =
  task_delete_restore_observation_source inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_requested) (task_delete_capture_phase inputs) inputs.(delete_capture_globals)
    restore.(delete_restore_middle) restore.(delete_restore_between) returned resumed history.
Proof.
  intros restore segment selected rely saved returned resumed resumed_heap environment_heap stopped
    [source [[[invocation [origin stack]] available] [phase_rely protocol]]] saved_value window suffix.
  reflexivity.
Qed.

(** The embeddings below are the root program union's constructors. They
    are syntactic inclusions of these actual leaf relations, not frame or
    observer preservation assumptions. *)
Lemma task_delete_restore_capture_c_window_sequence :
  forall segment restore selected rely stopped,
  (forall state before input stop returned after output,
    task_delete_primitive_c_segment
      restore.(delete_restore_inputs).(delete_capture_environment)
      restore.(delete_restore_inputs).(delete_capture_critical)
      restore.(delete_restore_inputs).(delete_capture_globals) state before input stop returned after output ->
    segment state before input stop returned after output) ->
  task_delete_restore_capture_c_window segment restore selected rely stopped ->
  kernel_c_sequence segment
    (task_delete_locked restore.(delete_restore_inputs).(delete_capture_prepared)) restore.(delete_restore_prepared_heap)
    (task_delete_capture_prepared_owner restore.(delete_restore_inputs)) stopped
    restore.(delete_restore_between) restore.(delete_restore_middle_heap)
    (task_delete_capture_middle_owner restore.(delete_restore_inputs) restore.(delete_restore_middle)
      restore.(delete_restore_between)).
Proof.
  intros segment restore selected rely stopped Hprimitive [prefix_heap [environment_heap [Hprefix [Hwindow Hsuffix]]]].
  pose proof (task_delete_joint_c_window_sequence _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hwindow) as Hsequence.
  replace stopped with (orb false (orb stopped false)) by (rewrite Bool.orb_false_r; reflexivity).
  eapply KernelCSequenceThen.
  - apply KernelCSequenceAtom, Hprimitive; exact Hprefix.
  - intros heap Howned; exact Howned.
  - eapply KernelCSequenceThen.
    + exact Hsequence.
    + intros heap Howned; exact Howned.
    + apply KernelCSequenceAtom, Hprimitive; exact Hsuffix.
Qed.

Lemma task_delete_save_capture_c_window_sequence :
  forall segment capture selected rely stopped,
  (forall state before input stop returned after output,
    task_delete_primitive_c_segment
      capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_environment)
      capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_critical)
      capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_globals)
      state before input stop returned after output -> segment state before input stop returned after output) ->
  task_delete_save_capture_c_window segment capture selected rely stopped ->
  kernel_c_sequence segment
    capture.(delete_save_restore).(delete_restore_between) capture.(delete_save_restore).(delete_restore_middle_heap)
    (task_delete_capture_middle_owner capture.(delete_save_restore).(delete_restore_inputs)
      capture.(delete_save_restore).(delete_restore_middle) capture.(delete_save_restore).(delete_restore_between)) stopped
    capture.(delete_save_resumed) capture.(delete_save_resumed_heap)
    (task_delete_capture_resumed_owner capture.(delete_save_restore) capture.(delete_save_saved)
      capture.(delete_save_returned) capture.(delete_save_resumed)).
Proof.
  intros segment capture selected rely stopped Hprimitive [environment_heap [Hwindow Hsuffix]].
  pose proof (task_delete_joint_c_window_sequence _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hwindow) as Hsequence.
  replace stopped with (orb stopped false) by apply Bool.orb_false_r.
  eapply KernelCSequenceThen.
  - exact Hsequence.
  - intros heap Howned; exact Howned.
  - apply KernelCSequenceAtom, Hprimitive; exact Hsuffix.
Qed.

Lemma task_delete_capture_c_body_sequence :
  forall segment observer origin capture after_heap restore_selected restore_rely save_selected save_rely
    restore_stopped save_stopped,
  let restore := capture.(delete_save_restore) in
  let inputs := restore.(delete_restore_inputs) in
  (forall state before input stopped returned after output,
    task_delete_own_c_segment inputs.(delete_capture_environment) inputs.(delete_capture_critical)
      inputs.(delete_capture_globals) observer origin state before input stopped returned after output ->
    segment state before input stopped returned after output) ->
  (forall state before input stopped returned after output,
    task_delete_primitive_c_segment inputs.(delete_capture_environment) inputs.(delete_capture_critical)
      inputs.(delete_capture_globals) state before input stopped returned after output ->
    segment state before input stopped returned after output) ->
  task_delete_restore_capture_c_window segment restore restore_selected restore_rely restore_stopped ->
  task_delete_save_capture_c_window segment capture save_selected save_rely save_stopped ->
  task_delete_capture_completed capture after_heap ->
  kernel_c_sequence segment inputs.(delete_capture_acquired) restore.(delete_restore_before_heap)
    (task_delete_capture_before_owner inputs)
    (task_delete_capture_observer_stopped capture origin restore_stopped save_stopped)
    (task_delete_capture_cut capture) after_heap (task_delete_capture_recycled_owner capture).
Proof.
  intros segment observer origin capture after_heap restore_selected restore_rely save_selected save_rely
    restore_stopped save_stopped restore inputs Hown Hprimitive Hrestore Hsave Hcompleted.
  unfold task_delete_capture_observer_stopped.
  change (kernel_c_sequence segment inputs.(delete_capture_acquired) restore.(delete_restore_before_heap)
    (task_delete_capture_before_owner inputs)
    (orb false (orb restore_stopped (orb save_stopped (task_delete_recycle_stops_origin inputs.(delete_capture_tid) origin))))
    (task_delete_capture_cut capture) after_heap (task_delete_capture_recycled_owner capture)).
  eapply KernelCSequenceThen.
  - apply KernelCSequenceAtom, Hown, TaskDeleteCPrepare.
    + repeat split; reflexivity.
    + apply task_delete_restore_capture_prepare_completion.
  - intros heap Howned; exact Howned.
  - eapply KernelCSequenceThen.
    + eapply task_delete_restore_capture_c_window_sequence; [exact Hprimitive|exact Hrestore].
    + intros heap Howned; exact Howned.
    + eapply KernelCSequenceThen.
      * eapply task_delete_save_capture_c_window_sequence; [exact Hprimitive|exact Hsave].
      * intros heap Howned; exact Howned.
      * apply KernelCSequenceAtom, Hown, TaskDeleteCRecycle.
        -- repeat split; reflexivity.
        -- exact Hcompleted.
Qed.

End DeleteComponent.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Import DeleteComponent.

Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
(** Sources decorate the original C completion proof.  They retain the
    invocation/allocation from that completion; no constructor assumes any
    creation-frame, cache, ready or future-return conclusion. *)
Import EventStateDef.
Import EventStateDef.
