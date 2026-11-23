Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_wrapper_completion_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_returned_c_segment_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_control_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_envelope_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module OSIntExitCCallCompletion.
Import SelectedReturnedCProgram SelectedReturnedCSource SelectedIRQWrapperCompletion OSIntExitReturnedC
  OSIntExitCCallControl OSIntExitCCallEnvelope.

(** A complete entry/body/return module. It is not an additional raw
    Returned atom: the original sequence remains the exact body witness. *)
Inductive os_int_exit_first_level_c_step environment critical sg observer origin : KernelCSegmentRelation :=
| OSIntExitFirstLevelCStep :
  forall initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    (prefix : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
      (armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
        suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments))
      body_heap body_input prefix_stop observed read_heap prefix_output)
    (acquire : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
      observed read_heap read_input acquire_stop entry acquired_heap acquire_output)
    observation_frame local receipt original node frame middle after,
  os_int_exit_first_level_entry_c_completion environment sg initial entry_node handler suspended
    publication entry_local entry_frame before saved_heap body_heap ->
  (os_int_exit_first_level_entry_output environment sg initial handler suspended entry_local entry_frame |-- body_input) ->
  kernel_returned_c_body_sequence_source environment critical sg observer origin _ _ _ _ _ _ _ prefix ->
  (prefix_output |-- read_input) ->
  kernel_returned_c_body_sequence_source environment critical sg observer origin _ _ _ _ _ _ _ acquire ->
  (acquire_output |-- os_int_exit_returned_c_input environment sg entry local suspended receipt handler frame) ->
  os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
    entry local suspended receipt original node handler frame acquired_heap middle after ->
  os_int_exit_first_level_c_step environment critical sg observer origin initial before
    (os_int_exit_first_level_entry_input environment sg initial handler suspended entry_local entry_frame)
    (orb prefix_stop (orb acquire_stop false))
    (os_int_exit_wrapper_restored_state
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
      suspended.(armv7a_continuation_stack)) after
    (irq_wrapper_c_output environment sg
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
      local suspended receipt original handler (unmap_table_rep sg ** frame)).

Lemma os_int_exit_first_level_c_step_resources :
  forall environment critical sg observer origin state before input stopped current after output,
  os_int_exit_first_level_c_step environment critical sg observer origin
    state before input stopped current after output -> input before /\ output after.
Proof.
  intros until output; intro Hstep; destruct Hstep.
  eapply os_int_exit_first_level_c_call_resources.
  - exact H5.
  - constructor; eassumption.
Qed.

Lemma os_int_exit_first_level_c_step_control :
  forall environment critical sg observer origin state before input stopped current after output,
  os_int_exit_first_level_c_step environment critical sg observer origin
    state before input stopped current after output -> kernel_call_control_rely sg state current.
Proof.
  intros until output; intro Hstep; destruct Hstep.
  eapply os_int_exit_first_level_c_call_control.
  - exact H5.
  - constructor; eassumption.
Qed.

Lemma os_int_exit_first_level_entry_lifecycle_generation :
  forall environment sg initial node handler suspended publication local frame before saved_heap body_heap,
  os_int_exit_first_level_entry_c_completion environment sg initial node handler suspended
    publication local frame before saved_heap body_heap ->
  let parked := armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
    suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments) in
  parked.(TskState).(taskLifecycle) = initial.(TskState).(taskLifecycle) /\
  (forall slot, option_map taskGeneration (parked.(TskState).(inUsedTaskStates) slot) =
    option_map taskGeneration (initial.(TskState).(inUsedTaskStates) slot)).
Proof.
  intros until body_heap; intros Hentry parked.
  pose proof (os_int_exit_first_level_entry_task_fields _ _ _ _ _ _ _ _ _ _ _ _ Hentry) as Htasks.
  fold parked in Htasks.
  rewrite Htasks; split; [reflexivity|].
  intro slot; cbn [glob_task_set_parked_stacks glob_task_set_usedtask inUsedTaskStates].
  destruct (Z.eqb slot handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot)) eqn:Heq.
  - apply Z.eqb_eq in Heq; subst slot.
    rewrite (os_int_exit_entry_node _ _ _ _ _ _ _ _ _ _ _ _ Hentry); reflexivity.
  - reflexivity.
Qed.

Lemma os_int_exit_first_level_entry_source_frames :
  forall environment sg initial node handler suspended publication local frame before saved_heap body_heap,
  os_int_exit_first_level_entry_c_completion environment sg initial node handler suspended
    publication local frame before saved_heap body_heap ->
  let parked := armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
    suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments) in
  (forall observer, task_creation_frame observer initial.(TskState) parked.(TskState)) /\
  parked.(EventState) = initial.(EventState) /\
  parked.(NameState) = initial.(NameState) /\ parked.(TimerState) = initial.(TimerState).
Proof.
  intros until body_heap; intros Hentry parked.
  pose proof (os_int_exit_first_level_entry_task_fields _ _ _ _ _ _ _ _ _ _ _ _ Hentry) as Htasks.
  fold parked in Htasks.
  split.
  - intro observer; unfold task_creation_frame, task_creation_view; rewrite Htasks; reflexivity.
  - unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      os_sched_save_current_sp, armv7a_irq_entry_counter_state.
    rewrite (os_int_exit_entry_running _ _ _ _ _ _ _ _ _ _ _ _ Hentry).
    cbn [replace_IntrS TskState].
    rewrite (os_int_exit_entry_node _ _ _ _ _ _ _ _ _ _ _ _ Hentry).
    repeat split; reflexivity.
Qed.

Section ActualIRQCallSource.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (observer : nat) (origin : TaskInvocationOrigin).
Context (initial : UCOS2_Verify_State) (entry_node : TaskAbstractState)
  (handler : OsIntExitCallContext) (suspended : Armv7aContinuation)
  (publication : nat) (entry_local : Armv7aContinuation -> Assertion) (entry_frame : Assertion)
  (before saved_heap body_heap : model).
Let parked := armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
  suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments).
Context (body_input : Assertion) (prefix_stop : bool) (observed : UCOS2_Verify_State)
  (read_heap : model) (prefix_output read_input : Assertion) (acquire_stop : bool)
  (entry : UCOS2_Verify_State) (acquired_heap : model) (acquire_output : Assertion).
Context (prefix : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
  parked body_heap body_input prefix_stop observed read_heap prefix_output).
Context (acquire : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
  observed read_heap read_input acquire_stop entry acquired_heap acquire_output).
Context (observation_frame : Assertion) (local : Armv7aContinuation -> Assertion)
  (receipt : Assertion) (original : OsSchedCallContext) (node : TaskAbstractState)
  (frame : Assertion) (middle after : model).
Context (returned : os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
  entry local suspended receipt original node handler frame acquired_heap middle after).
Context (call : os_int_exit_first_level_c_call environment critical sg observer origin
  initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
  body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
  prefix acquire local receipt frame).

(** Creation/Name/Timer provenance remains the original proof-indexed
    source on both body segments. The control marker does not replace it. *)
Lemma os_int_exit_first_level_c_tail_source : forall event_observer,
  kernel_program_returned_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ acquire ->
  kernel_program_returned_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _
    (os_int_exit_first_level_c_tail environment critical sg observer origin
      initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
      body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
      prefix acquire observation_frame local receipt original node frame middle after returned call).
Proof.
  intros event_observer Hprefix Hacquire.
  unfold kernel_program_returned_c_sequence_source in *.
  cbn [os_int_exit_first_level_c_tail].
  apply KernelCSourceAdapt, KernelCSourceThen; [exact Hprefix|].
  apply KernelCSourceThen; [exact Hacquire|].
  apply KernelCSourceAtom, KernelProgramReturnedExitSource.
Qed.

Lemma os_int_exit_first_level_c_call_source_frames : forall event_observer,
  kernel_program_returned_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ acquire ->
  let final := os_int_exit_wrapper_restored_state
    (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
    suspended.(armv7a_continuation_stack) in
  task_creation_frame observer initial.(TskState) final.(TskState) /\
  (forall invocation, event_observer = Some invocation ->
    event_creation_frame invocation initial.(EventState) final.(EventState)) /\
  initial.(NameState) = final.(NameState) /\ timer_public_trace sg initial.(TimerState) final.(TimerState).
Proof.
  intros event_observer Hprefix Hacquire final.
  pose proof (os_int_exit_first_level_c_tail_source event_observer Hprefix Hacquire) as Hsource.
  destruct (kernel_program_returned_c_sequence_source_frames environment critical sg observer origin
    event_observer _ _ _ _ _ _ _ _ Hsource) as [Ht [He [Hn Hr]]].
  destruct call as [Hactual Hentrybridge Hcontrolprefix Hreadbridge Hcontrolacquire Hreturnbridge].
  destruct (os_int_exit_first_level_entry_source_frames _ _ _ _ _ _ _ _ _ _ _ _
    Hactual)
    as [Hentry [Hevent [Hname Htimer]]].
  split.
  - unfold task_creation_frame in *; etransitivity; [exact Ht|exact (Hentry observer)].
  - split.
    + intros invocation Hobserver; rewrite <- Hevent; exact (He invocation Hobserver).
    + split.
      * etransitivity; [symmetry; exact Hname|exact Hn].
      * rewrite <- Htimer; exact Hr.
Qed.
End ActualIRQCallSource.

End OSIntExitCCallCompletion.
