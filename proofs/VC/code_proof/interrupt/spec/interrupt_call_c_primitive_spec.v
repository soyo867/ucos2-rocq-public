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
Require Export Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


Module ViewPrimitiveComponent.

(** Insert inside the root ViewPrimitiveComponent module, after loading
    the already checked CriticalComponent and PrimitiveComponent.  No
    FlagPendCaller/Event or C-sequence type is declared here. *)
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import PrimitiveComponent.

Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition flag_pend_same_caller (returned original : flag_pend_call_protocol.FlagPendCaller) : Prop :=
  match returned, original with
  | flag_pend_call_protocol.FlagPendTaskCaller next, flag_pend_call_protocol.FlagPendTaskCaller previous => task_tcb_init_stack_same_call next previous
  | flag_pend_call_protocol.FlagPendInterruptCaller next active, flag_pend_call_protocol.FlagPendInterruptCaller previous old_active =>
      active = old_active /\ sched_fields_same_view next previous
  | _, _ => False
  end.

Definition flag_pend_interrupt_source view state : Prop :=
  exists handler interrupted,
    view.(os_execution_context) = KernelInterrupt handler interrupted /\
    kernel_interrupt_nesting_agrees state.(SchedState).(isRunning) view.(os_execution_context) state.(IntrState).

(** The existing view-side C primitive contract, before the old linked-source
    conjunct.  These posts do not promise cache, Running, Task ownership, or
    a future return.  Their actual invocation is the supplied view.  A caller
    obtains the post from the already explicit platform C contract, not from
    the Task-only Armv7aSaveSuffixABI resource projection.

    The following equivalences check that this factorization retains exactly
    the original observation / saved value / input / output prefix.  No
    flag_pend_caller_save_output, linked record, or new source appears in the
    completion constructors or their producers. *)

Definition flag_pend_view_save_primitive_post environment critical local next_local active sg
  view key call mask saved before first_heap returned acquired last_heap : Prop :=
  sched_fields_same_view returned view /\
  critical_region_interval critical sg view.(os_execution_invocation) before acquired /\
  interrupt_saved_value mask saved /\
  flag_pend_call_protocol.flag_pend_caller_save_input environment critical local active sg
    (flag_pend_call_protocol.FlagPendInterruptCaller view key) call mask before first_heap /\
  flag_pend_call_protocol.flag_pend_caller_restore_input environment critical next_local active sg
    (flag_pend_call_protocol.FlagPendInterruptCaller returned key) call saved acquired acquired last_heap.

Definition flag_pend_view_restore_primitive_post environment critical local next_local active sg
  view key call saved acquired released first_heap returned current last_heap : Prop :=
  sched_fields_same_view returned view /\
  critical_region_interval critical sg view.(os_execution_invocation) released current /\
  flag_pend_call_protocol.flag_pend_caller_restore_input environment critical local active sg
    (flag_pend_call_protocol.FlagPendInterruptCaller view key) call saved acquired released first_heap /\
  flag_pend_call_protocol.flag_pend_caller_save_input environment critical next_local active sg
    (flag_pend_call_protocol.FlagPendInterruptCaller returned key) call (armv7a_irq_fiq_mask saved) current last_heap.

Lemma flag_pend_view_save_primitive_post_old_prefix :
  forall environment critical local next_local active sg view key call mask saved
    before first_heap returned acquired last_heap,
  flag_pend_view_save_primitive_post environment critical local next_local active sg
    view key call mask saved before first_heap returned acquired last_heap <->
  (PrimitiveComponent.flag_pend_caller_save_observation environment critical sg
     (flag_pend_call_protocol.FlagPendInterruptCaller view key) call (flag_pend_call_protocol.FlagPendInterruptCaller returned key) call
     mask saved before acquired /\
   interrupt_saved_value mask saved /\
   flag_pend_call_protocol.flag_pend_caller_save_input environment critical local active sg
     (flag_pend_call_protocol.FlagPendInterruptCaller view key) call mask before first_heap /\
   flag_pend_call_protocol.flag_pend_caller_restore_input environment critical next_local active sg
     (flag_pend_call_protocol.FlagPendInterruptCaller returned key) call saved acquired acquired last_heap).
Proof.
  intros; unfold flag_pend_view_save_primitive_post.
  cbn [PrimitiveComponent.flag_pend_caller_save_observation]; tauto.
Qed.

Lemma flag_pend_view_restore_primitive_post_old_prefix :
  forall environment critical local next_local active sg view key call saved acquired
    released first_heap returned current last_heap,
  flag_pend_view_restore_primitive_post environment critical local next_local active sg
    view key call saved acquired released first_heap returned current last_heap <->
  (PrimitiveComponent.flag_pend_caller_restore_observation environment critical sg
     (flag_pend_call_protocol.FlagPendInterruptCaller view key) call (flag_pend_call_protocol.FlagPendInterruptCaller returned key) call released current /\
   flag_pend_call_protocol.flag_pend_caller_restore_input environment critical local active sg
     (flag_pend_call_protocol.FlagPendInterruptCaller view key) call saved acquired released first_heap /\
   flag_pend_call_protocol.flag_pend_caller_save_input environment critical next_local active sg
     (flag_pend_call_protocol.FlagPendInterruptCaller returned key) call (armv7a_irq_fiq_mask saved) current last_heap).
Proof.
  intros; unfold flag_pend_view_restore_primitive_post.
  cbn [PrimitiveComponent.flag_pend_caller_restore_observation]; tauto.
Qed.

Definition flag_pend_view_save_completed_c_event environment critical local next_local active sg
  view key call mask saved before first_heap returned acquired last_heap : flag_pend_call_protocol.FlagPendLinkedEvent :=
  {| flag_pend_call_protocol.flag_pend_event_operation := flag_pend_call_protocol.FlagPendSaveSource;
     flag_pend_call_protocol.flag_pend_event_caller := flag_pend_call_protocol.FlagPendInterruptCaller view key;
     flag_pend_call_protocol.flag_pend_event_original := call;
     flag_pend_call_protocol.flag_pend_event_returned_caller := flag_pend_call_protocol.FlagPendInterruptCaller returned key;
     flag_pend_call_protocol.flag_pend_event_returned := call;
     flag_pend_call_protocol.flag_pend_event_before := before;
     flag_pend_call_protocol.flag_pend_event_current := acquired;
     flag_pend_call_protocol.flag_pend_event_first_heap := first_heap;
     flag_pend_call_protocol.flag_pend_event_last_heap := last_heap;
     flag_pend_call_protocol.flag_pend_event_input := flag_pend_call_protocol.flag_pend_caller_save_input environment critical local active sg
       (flag_pend_call_protocol.FlagPendInterruptCaller view key) call mask before;
     flag_pend_call_protocol.flag_pend_event_output :=
       coq_prop (flag_pend_call_protocol.flag_pend_call_endpoint_observations environment sg
         (flag_pend_call_protocol.FlagPendInterruptCaller view key) call before call acquired) &&
       flag_pend_call_protocol.flag_pend_caller_restore_input environment critical next_local active sg
         (flag_pend_call_protocol.FlagPendInterruptCaller returned key) call saved acquired acquired |}.

Definition flag_pend_view_restore_completed_c_event environment critical local next_local active sg
  view key call saved acquired released first_heap returned current last_heap : flag_pend_call_protocol.FlagPendLinkedEvent :=
  {| flag_pend_call_protocol.flag_pend_event_operation := flag_pend_call_protocol.FlagPendRestoreSource;
     flag_pend_call_protocol.flag_pend_event_caller := flag_pend_call_protocol.FlagPendInterruptCaller view key;
     flag_pend_call_protocol.flag_pend_event_original := call;
     flag_pend_call_protocol.flag_pend_event_returned_caller := flag_pend_call_protocol.FlagPendInterruptCaller returned key;
     flag_pend_call_protocol.flag_pend_event_returned := call;
     flag_pend_call_protocol.flag_pend_event_before := released;
     flag_pend_call_protocol.flag_pend_event_current := current;
     flag_pend_call_protocol.flag_pend_event_first_heap := first_heap;
     flag_pend_call_protocol.flag_pend_event_last_heap := last_heap;
     flag_pend_call_protocol.flag_pend_event_input := flag_pend_call_protocol.flag_pend_caller_restore_input environment critical local active sg
       (flag_pend_call_protocol.FlagPendInterruptCaller view key) call saved acquired released;
     flag_pend_call_protocol.flag_pend_event_output :=
       coq_prop (flag_pend_call_protocol.flag_pend_call_endpoint_observations environment sg
         (flag_pend_call_protocol.FlagPendInterruptCaller view key) call released call current) &&
       flag_pend_call_protocol.flag_pend_caller_save_input environment critical next_local active sg
         (flag_pend_call_protocol.FlagPendInterruptCaller returned key) call (armv7a_irq_fiq_mask saved) current |}.

Section FlagPendViewPrimitiveCompletion.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources) (sg : StableGlobVars).

(** Hactual is the same observed C primitive post, with its actual returned
    view/local/state/heap.  No endpoint-equal replacement run is selected. *)
Inductive flag_pend_view_primitive_completion : flag_pend_call_protocol.FlagPendLinkedEvent -> Prop :=
| FlagPendViewPrimitiveSave : forall local next_local active view key call mask saved
    before first_heap returned acquired last_heap
    (Hactual : flag_pend_view_save_primitive_post environment critical local next_local active sg
      view key call mask saved before first_heap returned acquired last_heap),
    flag_pend_view_primitive_completion
      (flag_pend_view_save_completed_c_event environment critical local next_local active sg
        view key call mask saved before first_heap returned acquired last_heap)
| FlagPendViewPrimitiveRestore : forall local next_local active view key call saved acquired
    released first_heap returned current last_heap
    (Hactual : flag_pend_view_restore_primitive_post environment critical local next_local active sg
      view key call saved acquired released first_heap returned current last_heap),
    flag_pend_view_primitive_completion
      (flag_pend_view_restore_completed_c_event environment critical local next_local active sg
        view key call saved acquired released first_heap returned current last_heap).

Lemma flag_pend_view_save_completion_from_primitive_post :
  forall local next_local active view key call mask saved before first_heap returned acquired last_heap,
  flag_pend_view_save_primitive_post environment critical local next_local active sg
    view key call mask saved before first_heap returned acquired last_heap ->
  flag_pend_view_primitive_completion
    (flag_pend_view_save_completed_c_event environment critical local next_local active sg
      view key call mask saved before first_heap returned acquired last_heap).
Proof. intros; apply FlagPendViewPrimitiveSave; assumption. Qed.

Lemma flag_pend_view_restore_completion_from_primitive_post :
  forall local next_local active view key call saved acquired released first_heap returned current last_heap,
  flag_pend_view_restore_primitive_post environment critical local next_local active sg
    view key call saved acquired released first_heap returned current last_heap ->
  flag_pend_view_primitive_completion
    (flag_pend_view_restore_completed_c_event environment critical local next_local active sg
      view key call saved acquired released first_heap returned current last_heap).
Proof. intros; apply FlagPendViewPrimitiveRestore; assumption. Qed.

Lemma flag_pend_view_primitive_completion_resources : forall event,
  flag_pend_view_primitive_completion event ->
  event.(flag_pend_call_protocol.flag_pend_event_input) event.(flag_pend_call_protocol.flag_pend_event_first_heap) /\
    event.(flag_pend_call_protocol.flag_pend_event_output) event.(flag_pend_call_protocol.flag_pend_event_last_heap).
Proof.
  intros event Hactual; destruct Hactual as
    [local next_local active view key call mask saved before first_heap returned acquired last_heap Hpost
    |local next_local active view key call saved acquired released first_heap returned current last_heap Hpost];
    unfold flag_pend_view_save_primitive_post, flag_pend_view_restore_primitive_post in Hpost;
    cbn [flag_pend_view_save_completed_c_event flag_pend_view_restore_completed_c_event
      flag_pend_call_protocol.flag_pend_event_input flag_pend_call_protocol.flag_pend_event_output flag_pend_call_protocol.flag_pend_event_first_heap
      flag_pend_call_protocol.flag_pend_event_last_heap flag_pend_call_protocol.flag_pend_call_endpoint_observations].
  - destruct Hpost as [_ [_ [_ [Hinput Houtput]]]]; split; [exact Hinput|].
    split; [exact I|exact Houtput].
  - destruct Hpost as [_ [_ [Hinput Houtput]]]; split; [exact Hinput|].
    split; [exact I|exact Houtput].
Qed.

Lemma flag_pend_view_primitive_completion_same_caller : forall event,
  flag_pend_view_primitive_completion event ->
  flag_pend_same_caller event.(flag_pend_call_protocol.flag_pend_event_returned_caller) event.(flag_pend_call_protocol.flag_pend_event_caller).
Proof.
  intros event Hactual; destruct Hactual as
    [local next_local active view key call mask saved before first_heap returned acquired last_heap Hpost
    |local next_local active view key call saved acquired released first_heap returned current last_heap Hpost];
    unfold flag_pend_view_save_primitive_post, flag_pend_view_restore_primitive_post in Hpost;
    cbn [flag_pend_view_save_completed_c_event flag_pend_view_restore_completed_c_event
      flag_pend_call_protocol.flag_pend_event_caller flag_pend_call_protocol.flag_pend_event_returned_caller flag_pend_same_caller].
  all: split; [reflexivity|exact (proj1 Hpost)].
Qed.

Lemma flag_pend_view_primitive_completion_call_indices : forall event,
  flag_pend_view_primitive_completion event ->
  event.(flag_pend_call_protocol.flag_pend_event_returned) = event.(flag_pend_call_protocol.flag_pend_event_original) /\
  (event.(flag_pend_call_protocol.flag_pend_event_operation) = flag_pend_call_protocol.FlagPendSaveSource \/
   event.(flag_pend_call_protocol.flag_pend_event_operation) = flag_pend_call_protocol.FlagPendRestoreSource).
Proof. intros event Hactual; destruct Hactual; cbn; split; auto. Qed.

End FlagPendViewPrimitiveCompletion.

(** This is the exact source fact consumed at the pre-Save nesting check.
    It says nothing about the parked-map key, and adds no Running premise. *)
Lemma flag_pend_interrupt_source_nonpositive_nesting_not_running : forall view state,
  flag_pend_interrupt_source view state ->
  state.(IntrState).(intNesting) <= 0 -> state.(SchedState).(isRunning) = false.
Proof.
  intros view state [handler [interrupted [Hcontext Hagrees]]] Hnesting.
  assert (Hnotrunning : state.(SchedState).(isRunning) = true -> False).
  { intro Hrunning; unfold kernel_interrupt_nesting_agrees in Hagrees.
    specialize (Hagrees Hrunning); rewrite Hcontext in Hagrees.
    change (state.(IntrState).(intNesting) = Z.of_nat (S (kernel_interrupt_depth interrupted))) in Hagrees.
    rewrite Nat2Z.inj_succ in Hagrees; lia. }
  destruct state.(SchedState).(isRunning); [exfalso; apply Hnotrunning; reflexivity|reflexivity].
Qed.

(** A resource-only C leaf for the original view platform completion.
    invocation/origin are the actual caller view's indices.  The false bit
    is its original critical-region interval, not a statement about an
    arbitrary Task observer.  Other real IRQ C segments remain separate
    constructors of the root-owned program relation. *)

Section FlagPendViewPrimitiveCSegments.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin).

Inductive flag_pend_view_primitive_c_step : kernel_c_sequence_spec.KernelCSegmentRelation :=
| FlagPendViewPrimitiveCStep : forall view key event,
    event.(flag_pend_call_protocol.flag_pend_event_caller) = flag_pend_call_protocol.FlagPendInterruptCaller view key ->
    view.(os_execution_invocation) = invocation ->
    view.(os_execution_origin) = origin ->
    flag_pend_view_primitive_completion environment critical sg event ->
    flag_pend_view_primitive_c_step
      event.(flag_pend_call_protocol.flag_pend_event_before) event.(flag_pend_call_protocol.flag_pend_event_first_heap)
      event.(flag_pend_call_protocol.flag_pend_event_input) false event.(flag_pend_call_protocol.flag_pend_event_current)
      event.(flag_pend_call_protocol.flag_pend_event_last_heap) event.(flag_pend_call_protocol.flag_pend_event_output).

Lemma flag_pend_view_primitive_c_step_resources :
  forall before first_heap input stopped current last_heap output,
  flag_pend_view_primitive_c_step before first_heap input stopped current last_heap output ->
  input first_heap /\ output last_heap.
Proof.
  intros before first_heap input stopped current last_heap output Hstep; destruct Hstep.
  eapply flag_pend_view_primitive_completion_resources; eassumption.
Qed.

Lemma flag_pend_view_primitive_c_step_interval :
  forall before first_heap input stopped current last_heap output,
  flag_pend_view_primitive_c_step before first_heap input stopped current last_heap output ->
  stopped = false /\ critical_region_interval critical sg invocation before current.
Proof.
  intros before first_heap input stopped current last_heap output Hstep.
  destruct Hstep as [view key event Hcaller Hinvocation Horigin Hactual].
  split; [reflexivity|].
  destruct Hactual as
    [local next_local active source_view source_key call mask saved
      state first_heap returned acquired last_heap Hpost
    |local next_local active source_view source_key call saved acquired
      released first_heap returned current last_heap Hpost];
    cbn [flag_pend_view_save_completed_c_event flag_pend_view_restore_completed_c_event
      flag_pend_call_protocol.flag_pend_event_caller] in Hcaller;
    inversion Hcaller; subst view key;
    unfold flag_pend_view_save_primitive_post, flag_pend_view_restore_primitive_post in Hpost;
    cbn [flag_pend_view_save_completed_c_event flag_pend_view_restore_completed_c_event
      flag_pend_call_protocol.flag_pend_event_before flag_pend_call_protocol.flag_pend_event_current];
    rewrite <- Hinvocation; exact (proj1 (proj2 Hpost)).
Qed.

Lemma flag_pend_view_primitive_c_sequence_resources :
  forall before first_heap input stopped current last_heap output,
  kernel_c_sequence_spec.kernel_c_sequence flag_pend_view_primitive_c_step before first_heap input stopped current last_heap output ->
  input first_heap /\ output last_heap.
Proof.
  apply kernel_c_sequence_spec.kernel_c_sequence_resources; exact flag_pend_view_primitive_c_step_resources.
Qed.

End FlagPendViewPrimitiveCSegments.

Lemma flag_pend_view_primitive_completion_c_sequence :
  forall environment critical sg view key event,
  event.(flag_pend_call_protocol.flag_pend_event_caller) = flag_pend_call_protocol.FlagPendInterruptCaller view key ->
  flag_pend_view_primitive_completion environment critical sg event ->
  kernel_c_sequence_spec.kernel_c_sequence
    (flag_pend_view_primitive_c_step environment critical sg
      view.(os_execution_invocation) view.(os_execution_origin))
    event.(flag_pend_call_protocol.flag_pend_event_before) event.(flag_pend_call_protocol.flag_pend_event_first_heap)
    event.(flag_pend_call_protocol.flag_pend_event_input) false event.(flag_pend_call_protocol.flag_pend_event_current)
    event.(flag_pend_call_protocol.flag_pend_event_last_heap) event.(flag_pend_call_protocol.flag_pend_event_output).
Proof.
  intros environment critical sg view key event Hcaller Hactual.
  apply kernel_c_sequence_spec.KernelCSequenceAtom.
  eapply (FlagPendViewPrimitiveCStep environment critical sg
    view.(os_execution_invocation) view.(os_execution_origin) view key event);
    [exact Hcaller|reflexivity|reflexivity|exact Hactual].
Qed.

(** These producers consume the original platform C post, not the new
    caller output/source.  All indices and the Hactual proof are retained
    in the completion constructor inside this exact singleton sequence. *)
Lemma flag_pend_view_save_c_sequence_from_primitive_post :
  forall environment critical local next_local active sg view key call mask saved
    before first_heap returned acquired last_heap,
  flag_pend_view_save_primitive_post environment critical local next_local active sg
    view key call mask saved before first_heap returned acquired last_heap ->
  let event := flag_pend_view_save_completed_c_event environment critical local next_local active sg
    view key call mask saved before first_heap returned acquired last_heap in
  kernel_c_sequence_spec.kernel_c_sequence
    (flag_pend_view_primitive_c_step environment critical sg
      view.(os_execution_invocation) view.(os_execution_origin))
    event.(flag_pend_call_protocol.flag_pend_event_before) event.(flag_pend_call_protocol.flag_pend_event_first_heap)
    event.(flag_pend_call_protocol.flag_pend_event_input) false event.(flag_pend_call_protocol.flag_pend_event_current)
    event.(flag_pend_call_protocol.flag_pend_event_last_heap) event.(flag_pend_call_protocol.flag_pend_event_output).
Proof.
  intros environment critical local next_local active sg view key call mask saved
    before first_heap returned acquired last_heap Hactual event.
  eapply (flag_pend_view_primitive_completion_c_sequence environment critical sg view key event).
  - reflexivity.
  - apply FlagPendViewPrimitiveSave; exact Hactual.
Qed.

Lemma flag_pend_view_restore_c_sequence_from_primitive_post :
  forall environment critical local next_local active sg view key call saved acquired
    released first_heap returned current last_heap,
  flag_pend_view_restore_primitive_post environment critical local next_local active sg
    view key call saved acquired released first_heap returned current last_heap ->
  let event := flag_pend_view_restore_completed_c_event environment critical local next_local active sg
    view key call saved acquired released first_heap returned current last_heap in
  kernel_c_sequence_spec.kernel_c_sequence
    (flag_pend_view_primitive_c_step environment critical sg
      view.(os_execution_invocation) view.(os_execution_origin))
    event.(flag_pend_call_protocol.flag_pend_event_before) event.(flag_pend_call_protocol.flag_pend_event_first_heap)
    event.(flag_pend_call_protocol.flag_pend_event_input) false event.(flag_pend_call_protocol.flag_pend_event_current)
    event.(flag_pend_call_protocol.flag_pend_event_last_heap) event.(flag_pend_call_protocol.flag_pend_event_output).
Proof.
  intros environment critical local next_local active sg view key call saved acquired
    released first_heap returned current last_heap Hactual event.
  eapply (flag_pend_view_primitive_completion_c_sequence environment critical sg view key event).
  - reflexivity.
  - apply FlagPendViewPrimitiveRestore; exact Hactual.
Qed.

End ViewPrimitiveComponent.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Import PrimitiveComponent.

Import PrimitiveComponent.

Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
(** Sources decorate the original C completion proof.  They retain the
    invocation/allocation from that completion; no constructor assumes any
    creation-frame, cache, ready or future-return conclusion. *)
Import EventStateDef.
Import EventStateDef.



(** A selected environment is an actual sequence of the fixed C program.
    Its existing return owner contains the original C endpoint contract.
    The ABI suffix/prefix below is composed with that very sequence; there
    is no independently supplied old source or endpoint-equal replacement
    tree.  State, caller, local resources and heaps may all change in the
    environment.  Its stopped bit is retained, not assumed false. *)
Import PrimitiveComponent.
