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
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.















Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.




















Import UCOS2_C_Rules TaskStateDef SchedStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.



















































Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A sequence of actual module C segments.  Owners are local to each
    segment; only the adjacent state and heap are shared.  The explicit
    entailment is the C call's post-to-pre adaptation, not a global world
    invariant or a requirement that all stages be closed. *)
Definition KernelCSegmentRelation : Type :=
  UCOS2_Verify_State -> model -> Assertion -> bool ->
  UCOS2_Verify_State -> model -> Assertion -> Prop.

Inductive kernel_c_sequence (segment : KernelCSegmentRelation) :
  UCOS2_Verify_State -> model -> Assertion -> bool ->
  UCOS2_Verify_State -> model -> Assertion -> Prop :=
| KernelCSequenceRefl : forall state heap (owner : Assertion),
    owner heap -> kernel_c_sequence segment state heap owner false state heap owner
| KernelCSequenceAtom : forall state before input stopped returned after output,
    segment state before input stopped returned after output ->
    kernel_c_sequence segment state before input stopped returned after output
| KernelCSequenceThen : forall state before input first_stopped middle middle_heap
    first_output next_input last_stopped returned after output,
    kernel_c_sequence segment state before input first_stopped middle middle_heap first_output ->
    (first_output |-- next_input) ->
    kernel_c_sequence segment middle middle_heap next_input last_stopped returned after output ->
    kernel_c_sequence segment state before input (orb first_stopped last_stopped) returned after output
| KernelCSequenceAdapt : forall state before (input inner_input : Assertion) stopped returned after inner_output output,
    input before -> (input |-- inner_input) ->
    kernel_c_sequence segment state before inner_input stopped returned after inner_output ->
    (inner_output |-- output) ->
    kernel_c_sequence segment state before input stopped returned after output.

Lemma kernel_c_sequence_resources : forall segment,
  (forall state before input stopped returned after output,
    segment state before input stopped returned after output -> input before /\ output after) ->
  forall state before input stopped returned after output,
  kernel_c_sequence segment state before input stopped returned after output ->
  input before /\ output after.
Proof.
  intros segment Hsegment state before input stopped returned after output Hrun.
  induction Hrun.
  - split; assumption.
  - eapply Hsegment; exact H.
  - split; [exact (proj1 IHHrun1)|exact (proj2 IHHrun2)].
  - split; [exact H|apply H1; exact (proj2 IHHrun)].
Qed.

Lemma kernel_c_sequence_preserves_observer : forall segment observer origin,
  (forall state before input stopped returned after output,
    segment state before input stopped returned after output -> stopped = false ->
    task_invocation_active state.(TskState) observer origin /\ sched_observer_current_cache origin state ->
    task_invocation_active returned.(TskState) observer origin /\ sched_observer_current_cache origin returned) ->
  forall state before input stopped returned after output,
  kernel_c_sequence segment state before input stopped returned after output -> stopped = false ->
  task_invocation_active state.(TskState) observer origin /\ sched_observer_current_cache origin state ->
  task_invocation_active returned.(TskState) observer origin /\ sched_observer_current_cache origin returned.
Proof.
  intros segment observer origin Hsegment state before input stopped returned after output Hrun.
  induction Hrun; intros Hstop Hinitial.
  - exact Hinitial.
  - eapply Hsegment; eassumption.
  - apply Bool.orb_false_iff in Hstop; destruct Hstop as [Hfirst Hlast].
    apply IHHrun2; [exact Hlast|]. apply IHHrun1; assumption.
  - apply IHHrun; assumption.
Qed.

Lemma kernel_c_sequence_observer_lifetime : forall segment observer origin,
  (forall state before input stopped returned after output,
    segment state before input stopped returned after output ->
    task_observer_lifetime_result observer origin state.(TskState) returned.(TskState) stopped) ->
  forall state before input stopped returned after output,
  kernel_c_sequence segment state before input stopped returned after output ->
  task_observer_lifetime_result observer origin state.(TskState) returned.(TskState) stopped.
Proof.
  intros segment observer origin Hsegment state before input stopped returned after output Hrun.
  induction Hrun.
  - apply task_observer_lifetime_result_not_stopped, task_observer_lifetime_transport_refl.
  - eapply Hsegment; exact H.
  - eapply task_observer_lifetime_result_seq; eassumption.
  - exact IHHrun.
Qed.

(** Completion of the SAME C sequence.  The stopped bit is derived from
    the real module branches.  Its false value follows from old-origin
    lifetime and this call's returned Task source, not from a new cache or
    non-retirement premise.  Execution origins may change inside the run. *)
Lemma kernel_c_sequence_completed_current_cache : forall segment sg original returned,
  (forall state before input stopped current after output,
    segment state before input stopped current after output -> stopped = false ->
    task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
      sched_observer_current_cache original.(os_sched_call_origin) state ->
    task_invocation_active current.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
      sched_observer_current_cache original.(os_sched_call_origin) current) ->
  (forall state before input stopped current after output,
    segment state before input stopped current after output ->
    task_observer_lifetime_result original.(os_sched_call_invocation) original.(os_sched_call_origin)
      state.(TskState) current.(TskState) stopped) ->
  forall initial before input stopped current after output,
  kernel_c_sequence segment initial before input stopped current after output ->
  task_in_range sg initial.(TskState) -> kernel_call_task_source original initial ->
  sched_current_consistency initial.(TskState) initial.(SchedState) ->
  kernel_call_normal_return original initial returned current -> kernel_call_task_source returned current ->
  stopped = false /\ sched_current_consistency current.(TskState) current.(SchedState).
Proof.
  intros segment sg original returned Hpreserves Hlifetime initial before input stopped current after output
    Hrun Hrange Hentry Hcache Hnormal Hreturned.
  pose proof (kernel_c_sequence_observer_lifetime segment
    original.(os_sched_call_invocation) original.(os_sched_call_origin) Hlifetime
    initial before input stopped current after output Hrun) as Hlife.
  pose proof (kernel_call_completed_task_source_not_stopped sg original returned initial current stopped
    Hrange Hentry Hlife Hnormal Hreturned) as Hstop.
  split; [exact Hstop|].
  pose proof (kernel_c_sequence_preserves_observer segment
    original.(os_sched_call_invocation) original.(os_sched_call_origin) Hpreserves
    initial before input stopped current after output Hrun Hstop
    (conj (proj1 (proj2 Hentry)) (sched_current_consistency_implies_observer_cache _ _ Hcache)))
    as [_ Hobserver].
  apply (kernel_call_task_source_observer_cache _ _ Hreturned).
  destruct (proj1 Hnormal) as [Hinv [Horigin Hstack]].
  rewrite Horigin; exact Hobserver.
Qed.

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

Section KernelCSequenceSource.
Context (segment : KernelCSegmentRelation).
Context (atom_source : forall state before input stopped returned after output,
  segment state before input stopped returned after output -> Prop).

Inductive kernel_c_sequence_has_source :
  forall state before input stopped returned after output,
  kernel_c_sequence segment state before input stopped returned after output -> Prop :=
| KernelCSourceRefl : forall state heap (owner : Assertion) (owned : owner heap),
    kernel_c_sequence_has_source state heap owner false state heap owner
      (KernelCSequenceRefl segment state heap owner owned)
| KernelCSourceAtom : forall state before input stopped returned after output
    (step : segment state before input stopped returned after output),
    atom_source state before input stopped returned after output step ->
    kernel_c_sequence_has_source state before input stopped returned after output
      (KernelCSequenceAtom segment state before input stopped returned after output step)
| KernelCSourceThen : forall state before input first_stopped middle middle_heap
    first_output next_input last_stopped returned after output
    (first : kernel_c_sequence segment state before input first_stopped middle middle_heap first_output)
    (bridge : first_output |-- next_input)
    (last : kernel_c_sequence segment middle middle_heap next_input last_stopped returned after output),
    kernel_c_sequence_has_source state before input first_stopped middle middle_heap first_output first ->
    kernel_c_sequence_has_source middle middle_heap next_input last_stopped returned after output last ->
    kernel_c_sequence_has_source state before input (orb first_stopped last_stopped) returned after output
      (KernelCSequenceThen segment state before input first_stopped middle middle_heap
        first_output next_input last_stopped returned after output first bridge last)
| KernelCSourceAdapt : forall state before input inner_input stopped returned after inner_output output
    (owned : input before) (open_input : input |-- inner_input)
    (inner : kernel_c_sequence segment state before inner_input stopped returned after inner_output)
    (close_output : inner_output |-- output),
    kernel_c_sequence_has_source state before inner_input stopped returned after inner_output inner ->
    kernel_c_sequence_has_source state before input stopped returned after output
      (KernelCSequenceAdapt segment state before input inner_input stopped returned after inner_output output
        owned open_input inner close_output).

(** Every conclusion is obtained from markers on the same original atoms.
    The relation may be creation-frame equality, Name equality, or a Timer
    trace.  Its actual atomic producers are discharged in the module layer. *)
Lemma kernel_c_sequence_source_relation :
  forall (relation : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop),
  (forall state, relation state state) ->
  (forall first middle last, relation first middle -> relation middle last -> relation first last) ->
  (forall state before input stopped returned after output
    (step : segment state before input stopped returned after output),
    atom_source state before input stopped returned after output step -> relation state returned) ->
  forall state before input stopped returned after output
    (run : kernel_c_sequence segment state before input stopped returned after output),
  kernel_c_sequence_has_source state before input stopped returned after output run ->
  relation state returned.
Proof.
  intros relation Hrefl Htrans Hatom state before input stopped returned after output run Hsource.
  induction Hsource.
  - apply Hrefl.
  - eapply Hatom; eassumption.
  - eapply Htrans; eassumption.
  - exact IHHsource.
Qed.
End KernelCSequenceSource.

(** Changing the observation requested from each atom leaves the run
    itself unchanged.  This is used to project different actual source
    facts from one joint producer, without another path or heap choice. *)
Lemma kernel_c_sequence_source_map : forall (segment : KernelCSegmentRelation)
  (first_source last_source : forall state before input stopped returned after output,
    segment state before input stopped returned after output -> Prop),
  (forall state before input stopped returned after output
    (step : segment state before input stopped returned after output),
    first_source state before input stopped returned after output step ->
    last_source state before input stopped returned after output step) ->
  forall state before input stopped returned after output
    (run : kernel_c_sequence segment state before input stopped returned after output),
  kernel_c_sequence_has_source segment first_source state before input stopped returned after output run ->
  kernel_c_sequence_has_source segment last_source state before input stopped returned after output run.
Proof.
  intros segment first_source last_source Hmap state before input stopped returned after output run Hsource.
  induction Hsource.
  - apply KernelCSourceRefl.
  - apply KernelCSourceAtom; apply Hmap; assumption.
  - eapply KernelCSourceThen; eassumption.
  - apply KernelCSourceAdapt; assumption.
Qed.
