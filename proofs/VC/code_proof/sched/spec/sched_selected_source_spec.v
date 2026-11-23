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
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_call_preservation_spec.
Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_selected_completion_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_selected_return_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


(** Source markers refine the very same extended C step.  Existing actors
    and foreign-invocation conditions remain in the original marker.  The
    added return/installation branches use their concrete module effects;
    the required creation/Name/Timer conclusions are not constructor guards. *)
Module SelectedCompletionSource.
Import CriticalComponent PrimitiveComponent SelectedReturnPrimitive IRQSelectedCompletion.

Section SelectedProgramSources.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (observer : nat) (origin : TaskInvocationOrigin) (event_observer : option nat).
Let segment := kernel_program_return_c_step environment critical sg observer origin.

Inductive kernel_program_return_c_step_source :
  forall state before input stopped current after output,
  segment state before input stopped current after output -> Prop :=
| KernelProgramReturnOriginalSource : forall state before input stopped current after output Hstep,
    kernel_program_c_step_call_source environment critical sg observer origin event_observer
      state before input stopped current after output Hstep ->
    kernel_program_return_c_step_source _ _ _ _ _ _ _
      (@KernelProgramReturnOriginal environment critical sg observer origin state before input stopped current after output Hstep)
| KernelProgramReturnPrimitiveSource : forall state before input stopped current after output Hstep,
    kernel_program_return_c_step_source _ _ _ _ _ _ _
      (@KernelProgramReturnSelected environment critical sg observer origin state before input stopped current after output Hstep)
| KernelProgramReturnInstallSource : forall local frame call before installed sp actual complete selected Hterminal Hselected,
    kernel_program_return_c_step_source _ _ _ _ _ _ _
      (@KernelProgramReturnTaskSelectedInstall environment critical sg observer origin
        local frame call before installed sp actual complete selected Hterminal Hselected)
| KernelProgramReturnIRQSource :
    forall handler entry transfer original saved acquired receipt other frame before installed selected after source install restore Hcomplete,
    kernel_program_return_c_step_source _ _ _ _ _ _ _
      (@KernelProgramReturnIRQSelectedSuffix environment critical sg observer origin
        handler entry transfer original saved acquired receipt other frame before installed selected after source install restore Hcomplete).

Lemma kernel_program_return_c_step_source_frames :
  forall state before input stopped current after output
    (step : segment state before input stopped current after output),
  kernel_program_return_c_step_source state before input stopped current after output step ->
  task_creation_frame observer state.(TskState) current.(TskState) /\
  (forall invocation, event_observer = Some invocation ->
    event_creation_frame invocation state.(EventState) current.(EventState)) /\
  state.(NameState) = current.(NameState) /\ timer_public_trace sg state.(TimerState) current.(TimerState).
Proof.
  intros state before input stopped current after output step Hsource; destruct Hsource.
  - eapply kernel_program_c_step_call_source_frames; exact H.
  - destruct (kernel_selected_return_c_step_state_stop _ _ _ _ _ _ _ _ Hstep) as [-> ->].
    split; [reflexivity|]. split; [intros; reflexivity|]. split; [reflexivity|constructor].
  - destruct (task_install_c_step_creation_frames environment local sg observer _ _ _ _ _ _ _
      (@InstallComponent.TaskInstallCStep environment local sg frame call before installed sp actual complete))
      as [Htask [Hevent [Hname Htimer]]].
    exact (conj Htask (conj (fun invocation _ => Hevent invocation) (conj Hname Htimer))).
  - split; [reflexivity|]. split; [intros; reflexivity|]. split; [reflexivity|constructor].
Qed.

Definition kernel_program_return_c_sequence_source state before input stopped current after output
  (run : kernel_c_sequence segment state before input stopped current after output) : Prop :=
  kernel_c_sequence_has_source segment kernel_program_return_c_step_source
    state before input stopped current after output run.

Lemma kernel_program_return_c_sequence_source_frames :
  forall state before input stopped current after output
    (run : kernel_c_sequence segment state before input stopped current after output),
  kernel_program_return_c_sequence_source state before input stopped current after output run ->
  task_creation_frame observer state.(TskState) current.(TskState) /\
  (forall invocation, event_observer = Some invocation ->
    event_creation_frame invocation state.(EventState) current.(EventState)) /\
  state.(NameState) = current.(NameState) /\ timer_public_trace sg state.(TimerState) current.(TimerState).
Proof.
  intros state before input stopped current after output run Hsource.
  eapply (kernel_c_sequence_source_relation segment kernel_program_return_c_step_source
    (fun entry final => task_creation_frame observer entry.(TskState) final.(TskState) /\
      (forall invocation, event_observer = Some invocation -> event_creation_frame invocation entry.(EventState) final.(EventState)) /\
      entry.(NameState) = final.(NameState) /\ timer_public_trace sg entry.(TimerState) final.(TimerState))).
  - intro entry; split; [reflexivity|]. split; [intros; reflexivity|]. split; [reflexivity|constructor].
  - intros first middle last [Htask [Hevent [Hname Htimer]]] [Htask' [Hevent' [Hname' Htimer']]].
    split.
    + unfold task_creation_frame in *; etransitivity; [exact Htask'|exact Htask].
    + split.
      * intros invocation Hobserver; unfold event_creation_frame in *; etransitivity;
          [exact (Hevent' invocation Hobserver)|exact (Hevent invocation Hobserver)].
      * split; [etransitivity; eassumption|]. eapply timer_public_trace_trans; eassumption.
  - intros; eapply kernel_program_return_c_step_source_frames; eassumption.
  - exact Hsource.
Qed.
End SelectedProgramSources.

(** A checked return source is consumed here, not fabricated.  Concrete
    Task/IRQ completion producers above establish it from their actual
    selected tuple.  The creation/Name facts belong to this very run and
    the active-origin transport uses the real registration's uniqueness. *)
Lemma kernel_program_return_c_sequence_call_preserved :
  forall environment critical sg original returned initial before input stopped current after output
    (run : kernel_c_sequence
      (kernel_program_return_c_step environment critical sg
        original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial before input stopped current after output),
  kernel_program_return_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None
    initial before input stopped current after output run ->
  UCOS2_state_inv sg current -> task_in_range sg initial.(TskState) ->
  task_invocation_active initial.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_tcb_init_stack_same_call returned original -> kernel_call_task_source returned current ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) initial current /\
  task_tcb_init_stack_source_preserved original initial current /\ stopped = false.
Proof.
  intros environment critical sg original returned initial before input stopped current after output
    run Hsource Hvalid Hrange Hinitial Hsame Hreturned.
  destruct (kernel_program_return_c_sequence_source_frames environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None
    initial before input stopped current after output run Hsource) as [Htask [Hevent [Hname Htimer]]].
  pose proof (proj1 (task_tcb_init_stack_same_call_source_iff returned original current Hsame) Hreturned) as Horiginal.
  assert (Hlife : task_observer_lifetime_result original.(os_sched_call_invocation) original.(os_sched_call_origin)
    initial.(TskState) current.(TskState) stopped).
  { eapply kernel_c_sequence_observer_lifetime; [|exact run].
    exact (kernel_program_return_c_step_observer_lifetime environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin)). }
  split.
  - intros Hbefore; split; [exact Hvalid|]. split; [exact Htask|]. split.
    + eapply CallPreservation.task_invocation_active_all_origins_transport;
        [exact Hinitial|exact (proj1 (proj2 Horiginal))].
    + exact Hname.
  - split; [intros _; exact Horiginal|].
    destruct stopped; [|reflexivity].
    destruct Hlife as [_ Hretired].
    exfalso; eapply Hretired; [|reflexivity|exact (proj1 (proj2 Horiginal))].
    eapply sched_observer_spec.task_observer_lifetime_from_active;
      [exact Hrange|exact Hinitial].
Qed.

End SelectedCompletionSource.
