Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_next_completion_spec.
(* Report candidate: actual module completions; staged only by the parent. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_local_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_envelope_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_completion_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_returned_c_segment_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_control_spec.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_source_call_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_wrapper_completion_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_environment_spec.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module ReturnedIRQEntryResources.
Import PrimitiveComponent OSIntExitCCallEnvelope OSIntExitCCallCompletion.

(** The actual saving operation supplies the descriptor. Its previously
    absent key may be interpreted by exactly the caller's current receipt.
    No value of the unrelated local assertion at that key is required. *)
Lemma flag_pend_caller_save_input_irq_entry :
  forall environment critical local active sg original mask initial handler suspended private_frame,
  handler.(os_int_exit_interrupted_call) = original ->
  handler.(os_int_exit_interrupted_mask) = mask ->
  suspended.(armv7a_continuation_stack) = original.(os_sched_call_stack) ->
  initial.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) = None ->
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller original) original mask initial **
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** private_frame) |--
  os_int_exit_first_level_entry_input environment sg initial handler suspended
    (kernel_irq_fields_local local suspended (active original initial))
    (unmap_table_rep sg ** private_frame).
Proof.
  intros environment critical local active sg original mask initial handler suspended private_frame
    Hcall Hmask Hstack Hnone.
  assert (Habsent : initial.(TskState).(parkedTaskStacks)
      (task_stack_key suspended.(armv7a_continuation_stack)) = None) by (rewrite Hstack; exact Hnone).
  assert (Hreceipt : kernel_irq_fields_local local suspended (active original initial) suspended =
      coq_prop (suspended = suspended) && active original initial).
  { unfold kernel_irq_fields_local; destruct task_stack_key_eq_dec; [reflexivity|contradiction]. }
  unfold flag_pend_caller_save_input, flag_pend_active_save_input,
    os_sched_fields_save_input, os_sched_fields_capsules,
    os_int_exit_first_level_entry_input, os_int_exit_frame_save_pre.
  rewrite Hcall, Hmask, Hreceipt; Intros.
  sep_apply_l_atomic (proj1 (kernel_irq_fields_local_map_absent
    _ _ _ environment.(task_stack_call_continuations) initial.(TskState)
    initial.(TskState).(parkedTaskStacks) local suspended (active original initial) Habsent)).
  entailer!.
Qed.

Lemma os_int_exit_first_level_entry_preserves_active :
  forall environment sg initial node handler suspended publication local frame before saved_heap body_heap,
  os_int_exit_first_level_entry_c_completion environment sg initial node handler suspended
    publication local frame before saved_heap body_heap ->
  forall invocation origin,
  task_invocation_active initial.(TskState) invocation origin ->
  task_invocation_active
    (armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
      suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments)).(TskState)
    invocation origin.
Proof.
  intros until body_heap; intros Hentry invocation origin [Hregistered [Hretired Hlive]].
  pose proof (os_int_exit_first_level_entry_task_fields _ _ _ _ _ _ _ _ _ _ _ _ Hentry) as Htasks.
  unfold task_invocation_active; rewrite Htasks.
  split; [exact Hregistered|]. split; [exact Hretired|].
  destruct origin as [|slot generation]; [exact I|].
  destruct Hlive as [task [Hlookup Hgeneration]].
  cbn [task_invocation_origin_live glob_task_set_parked_stacks glob_task_set_usedtask inUsedTaskStates].
  destruct (Z.eqb slot handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot)) eqn:Heq.
  - apply Z.eqb_eq in Heq; subst slot.
    pose proof (os_int_exit_entry_node _ _ _ _ _ _ _ _ _ _ _ _ Hentry) as Hnode.
    assert (task = node) by congruence; subst task.
    exists (task_set_saved_sp node suspended.(armv7a_continuation_sp)); split; [reflexivity|exact Hgeneration].
  - exists task; exact (conj Hlookup Hgeneration).
Qed.

Lemma os_int_exit_first_level_entry_preserves_task_source :
  forall environment sg initial node handler suspended publication local frame before saved_heap body_heap,
  os_int_exit_first_level_entry_c_completion environment sg initial node handler suspended
    publication local frame before saved_heap body_heap ->
  forall original, kernel_call_task_source original initial ->
  kernel_call_task_source original
    (armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
      suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments)).
Proof.
  intros until body_heap; intros Hentry original [Horigin [Hactive Hcurrent]].
  split; [exact Horigin|]. split.
  - eapply os_int_exit_first_level_entry_preserves_active; eassumption.
  - unfold armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state, os_sched_save_current_sp.
    rewrite (os_int_exit_entry_running _ _ _ _ _ _ _ _ _ _ _ _ Hentry).
    cbn [replace_IntrS TskState].
    rewrite (os_int_exit_entry_node _ _ _ _ _ _ _ _ _ _ _ _ Hentry).
    exact Hcurrent.
Qed.

End ReturnedIRQEntryResources.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module ReturnedIRQCallSource.
Import SelectedReturnedCProgram SelectedReturnedCSource OSIntExitReturnedC
  OSIntExitCCallControl OSIntExitCCallEnvelope OSIntExitCCallCompletion ReturnedIRQEntryResources.

Lemma os_int_exit_entry_sched_state :
  forall environment sg initial node handler suspended publication local frame before saved_heap body_heap,
  os_int_exit_first_level_entry_c_completion environment sg initial node handler suspended
    publication local frame before saved_heap body_heap ->
  (armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
    suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments)).(SchedState) =
  initial.(SchedState).
Proof.
  intros until body_heap; intro Hentry.
  unfold armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
    armv7a_irq_entry_counter_state, os_sched_save_current_sp.
  rewrite (os_int_exit_entry_running _ _ _ _ _ _ _ _ _ _ _ _ Hentry).
  cbn [replace_IntrS TskState].
  rewrite (os_int_exit_entry_node _ _ _ _ _ _ _ _ _ _ _ _ Hentry).
  reflexivity.
Qed.

Lemma os_int_exit_entry_preserves_observer :
  forall environment sg initial node handler suspended publication local frame before saved_heap body_heap,
  os_int_exit_first_level_entry_c_completion environment sg initial node handler suspended
    publication local frame before saved_heap body_heap ->
  forall observer origin,
  task_invocation_active initial.(TskState) observer origin /\ sched_observer_current_cache origin initial ->
  let parked := armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
    suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments) in
  task_invocation_active parked.(TskState) observer origin /\ sched_observer_current_cache origin parked.
Proof.
  intros until body_heap; intros Hentry observer origin [Hactive Hcache] parked.
  split.
  - eapply os_int_exit_first_level_entry_preserves_active; eassumption.
  - destruct origin as [|slot generation]; [exact I|].
    intros current Hlookup Hgeneration Hcurrent.
    pose proof (os_int_exit_first_level_entry_task_fields _ _ _ _ _ _ _ _ _ _ _ _ Hentry) as Htasks.
    fold parked in Htasks; rewrite Htasks in Hlookup.
    pose proof (os_int_exit_entry_sched_state _ _ _ _ _ _ _ _ _ _ _ _ Hentry) as Hsched.
    fold parked in Hsched; rewrite Hsched in Hcurrent; rewrite Hsched.
    cbn [glob_task_set_parked_stacks glob_task_set_usedtask inUsedTaskStates] in Hlookup.
    destruct (Z.eqb slot handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot)) eqn:Heq.
    + apply Z.eqb_eq in Heq; subst slot.
      injection Hlookup as Hnode; subst current.
      change (initial.(SchedState).(curSchedPrio) = Some node.(curPrio)).
      eapply Hcache; [exact (os_int_exit_entry_node _ _ _ _ _ _ _ _ _ _ _ _ Hentry)|exact Hgeneration|exact Hcurrent].
    + eapply Hcache; eassumption.
Qed.

Lemma os_int_exit_entry_observer_lifetime :
  forall environment sg initial node handler suspended publication local frame before saved_heap body_heap,
  os_int_exit_first_level_entry_c_completion environment sg initial node handler suspended
    publication local frame before saved_heap body_heap ->
  forall observer origin,
  task_observer_lifetime_result observer origin initial.(TskState)
    (armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
      suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments)).(TskState) false.
Proof.
  intros until body_heap; intros Hentry observer origin.
  apply task_observer_lifetime_result_not_stopped, task_observer_lifetime_transport_fields.
  - exact (proj1 (os_int_exit_first_level_entry_lifecycle_generation _ _ _ _ _ _ _ _ _ _ _ _ Hentry)).
  - exact (proj2 (os_int_exit_first_level_entry_lifecycle_generation _ _ _ _ _ _ _ _ _ _ _ _ Hentry)).
Qed.

Section CompleteCall.
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
Let final := os_int_exit_wrapper_restored_state
  (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
  suspended.(armv7a_continuation_stack).
Let tail := os_int_exit_first_level_c_tail environment critical sg observer origin
  initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
  body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
  prefix acquire observation_frame local receipt original node frame middle after returned call.

Lemma os_int_exit_first_level_c_call_observer_lifetime :
  task_observer_lifetime_result observer origin initial.(TskState) final.(TskState)
    (orb prefix_stop (orb acquire_stop false)).
Proof.
  change (task_observer_lifetime_result observer origin initial.(TskState) final.(TskState)
    (orb false (orb prefix_stop (orb acquire_stop false)))).
  eapply task_observer_lifetime_result_seq.
  - eapply os_int_exit_entry_observer_lifetime.
    exact (os_int_exit_call_actual_entry environment critical sg observer origin
      initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
      body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
      prefix acquire local receipt frame call).
  - exact (kernel_program_returned_c_sequence_observer_lifetime _ _ _ _ _ _ _ _ _ _ _ _ tail).
Qed.

Lemma os_int_exit_first_level_c_call_preserves_observer :
  orb prefix_stop (orb acquire_stop false) = false ->
  task_invocation_active initial.(TskState) observer origin /\ sched_observer_current_cache origin initial ->
  task_invocation_active final.(TskState) observer origin /\ sched_observer_current_cache origin final.
Proof.
  intros Hstop Hinitial.
  eapply kernel_program_returned_c_sequence_preserves_observer; [exact tail|exact Hstop|].
  eapply os_int_exit_entry_preserves_observer; [|exact Hinitial].
  exact (os_int_exit_call_actual_entry environment critical sg observer origin
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire local receipt frame call).
Qed.
End CompleteCall.

Lemma os_int_exit_first_level_c_step_observer_lifetime :
  forall environment critical sg observer origin state before input stopped current after output,
  os_int_exit_first_level_c_step environment critical sg observer origin state before input stopped current after output ->
  task_observer_lifetime_result observer origin state.(TskState) current.(TskState) stopped.
Proof.
  intros until output; intro Hstep; destruct Hstep.
  eapply os_int_exit_first_level_c_call_observer_lifetime.
  - exact H5.
  - constructor; eassumption.
Qed.

Lemma os_int_exit_first_level_c_step_preserves_observer :
  forall environment critical sg observer origin state before input stopped current after output,
  os_int_exit_first_level_c_step environment critical sg observer origin state before input stopped current after output ->
  stopped = false ->
  task_invocation_active state.(TskState) observer origin /\ sched_observer_current_cache origin state ->
  task_invocation_active current.(TskState) observer origin /\ sched_observer_current_cache origin current.
Proof.
  intros until output; intros Hstep Hstop Hinitial; destruct Hstep.
  eapply os_int_exit_first_level_c_call_preserves_observer.
  - exact H5.
  - constructor; eassumption.
  - exact Hstop.
  - exact Hinitial.
Qed.

(** This marker inspects the actual complete-call constructor. Its source
    premises are the very two body proofs stored by that constructor. *)
Inductive os_int_exit_first_level_c_step_source
  environment critical sg observer origin (event_observer : option nat) :
  forall state before input stopped current after output,
  os_int_exit_first_level_c_step environment critical sg observer origin
    state before input stopped current after output -> Prop :=
| OSIntExitFirstLevelCStepSource :
  forall initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    (prefix : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
      (armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
        suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments))
      body_heap body_input prefix_stop observed read_heap prefix_output)
    (acquire : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
      observed read_heap read_input acquire_stop entry acquired_heap acquire_output)
    observation_frame local receipt original node frame middle after
    (Hentry : os_int_exit_first_level_entry_c_completion environment sg initial entry_node handler suspended
      publication entry_local entry_frame before saved_heap body_heap)
    (Hentry_bridge : os_int_exit_first_level_entry_output environment sg initial handler suspended entry_local entry_frame |-- body_input)
    (Hprefix_control : kernel_returned_c_body_sequence_source environment critical sg observer origin _ _ _ _ _ _ _ prefix)
    (Hread_bridge : prefix_output |-- read_input)
    (Hacquire_control : kernel_returned_c_body_sequence_source environment critical sg observer origin _ _ _ _ _ _ _ acquire)
    (Hreturn_bridge : acquire_output |-- os_int_exit_returned_c_input environment sg entry local suspended receipt handler frame)
    (Hreturned : os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
      entry local suspended receipt original node handler frame acquired_heap middle after),
  kernel_program_returned_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ acquire ->
  os_int_exit_first_level_c_step_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _
    (@OSIntExitFirstLevelCStep environment critical sg observer origin
      initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
      body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
      prefix acquire observation_frame local receipt original node frame middle after
      Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge Hreturned).

Lemma os_int_exit_first_level_c_step_source_frames :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (step : os_int_exit_first_level_c_step environment critical sg observer origin
      state before input stopped current after output),
  os_int_exit_first_level_c_step_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ step ->
  task_creation_frame observer state.(TskState) current.(TskState) /\
  (forall invocation, event_observer = Some invocation ->
    event_creation_frame invocation state.(EventState) current.(EventState)) /\
  state.(NameState) = current.(NameState) /\ timer_public_trace sg state.(TimerState) current.(TimerState).
Proof.
  intros until step; intro Hsource; destruct Hsource.
  eapply os_int_exit_first_level_c_call_source_frames.
  - exact Hreturned.
  - constructor; eassumption.
  - exact H.
  - exact H0.
Qed.

End ReturnedIRQCallSource.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module SelectedEnvironmentCProgram.
Import SelectedReturnedCProgram OSIntExitCCallCompletion ReturnedIRQCallSource FlagTaskRdyNextCompletion.

(** The existing body language is retained by injection. The other branch
    is the complete, source-indexed IRQ call, including its real entry;
    its internal Returned sequence is neither relabelled nor flattened. *)
Inductive kernel_program_environment_c_step environment critical sg observer origin : KernelCSegmentRelation :=
| KernelProgramEnvironmentBody : forall state before input stopped current after output,
  kernel_program_returned_c_step environment critical sg observer origin
    state before input stopped current after output ->
  kernel_program_environment_c_step environment critical sg observer origin
    state before input stopped current after output
| KernelProgramEnvironmentIRQCall : forall state before input stopped current after output,
  os_int_exit_first_level_c_step environment critical sg observer origin
    state before input stopped current after output ->
  kernel_program_environment_c_step environment critical sg observer origin
    state before input stopped current after output
| KernelProgramEnvironmentFlagTaskRdyNext : forall state before input stopped current after output,
  flag_task_rdy_next_c_segment environment sg state before input stopped current after output ->
  kernel_program_environment_c_step environment critical sg observer origin
    state before input stopped current after output.

Lemma kernel_program_environment_c_step_resources :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_program_environment_c_step environment critical sg observer origin
    state before input stopped current after output -> input before /\ output after.
Proof.
  intros until output; intro Hstep; destruct Hstep.
  - eapply kernel_program_returned_c_step_resources; eassumption.
  - eapply os_int_exit_first_level_c_step_resources; eassumption.
  - eapply flag_task_rdy_next_c_segment_resources; eassumption.
Qed.

Lemma kernel_program_environment_c_step_preserves_observer :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_program_environment_c_step environment critical sg observer origin
    state before input stopped current after output -> stopped = false ->
  task_invocation_active state.(TskState) observer origin /\ sched_observer_current_cache origin state ->
  task_invocation_active current.(TskState) observer origin /\ sched_observer_current_cache origin current.
Proof.
  intros until output; intros Hstep Hstop Hinitial; destruct Hstep.
  - eapply kernel_program_returned_c_step_preserves_observer; eassumption.
  - eapply os_int_exit_first_level_c_step_preserves_observer; eassumption.
  - eapply flag_task_rdy_next_c_segment_observer; eassumption.
Qed.

Lemma kernel_program_environment_c_step_observer_lifetime :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_program_environment_c_step environment critical sg observer origin
    state before input stopped current after output ->
  task_observer_lifetime_result observer origin state.(TskState) current.(TskState) stopped.
Proof.
  intros until output; intro Hstep; destruct Hstep.
  - eapply kernel_program_returned_c_step_observer_lifetime; eassumption.
  - eapply os_int_exit_first_level_c_step_observer_lifetime; eassumption.
  - eapply flag_task_rdy_next_c_segment_lifetime; eassumption.
Qed.

Lemma kernel_program_environment_c_step_running :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_program_environment_c_step environment critical sg observer origin
    state before input stopped current after output ->
  current.(SchedState).(isRunning) = state.(SchedState).(isRunning).
Proof.
  intros until output; intro Hstep; destruct Hstep.
  - eapply kernel_program_returned_c_step_running; eassumption.
  - exact (proj1 (os_int_exit_first_level_c_step_control _ _ _ _ _ _ _ _ _ _ _ _ H)).
  - symmetry; exact (proj1 (flag_task_rdy_next_c_segment_control_fields _ _ _ _ _ _ _ _ _ H)).
Qed.

Lemma kernel_program_environment_c_sequence_resources :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer origin)
    state before input stopped current after output -> input before /\ output after.
Proof.
  intros environment critical sg observer origin.
  apply kernel_c_sequence_resources, kernel_program_environment_c_step_resources.
Qed.

Lemma kernel_program_environment_c_sequence_preserves_observer :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer origin)
    state before input stopped current after output -> stopped = false ->
  task_invocation_active state.(TskState) observer origin /\ sched_observer_current_cache origin state ->
  task_invocation_active current.(TskState) observer origin /\ sched_observer_current_cache origin current.
Proof.
  intros environment critical sg observer origin.
  apply kernel_c_sequence_preserves_observer, kernel_program_environment_c_step_preserves_observer.
Qed.

Lemma kernel_program_environment_c_sequence_observer_lifetime :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer origin)
    state before input stopped current after output ->
  task_observer_lifetime_result observer origin state.(TskState) current.(TskState) stopped.
Proof.
  intros environment critical sg observer origin.
  apply kernel_c_sequence_observer_lifetime, kernel_program_environment_c_step_observer_lifetime.
Qed.

Lemma kernel_program_environment_c_sequence_running :
  forall environment critical sg observer origin state before input stopped current after output,
  kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer origin)
    state before input stopped current after output ->
  current.(SchedState).(isRunning) = state.(SchedState).(isRunning).
Proof.
  intros until output; intro Hrun; induction Hrun.
  - reflexivity.
  - eapply kernel_program_environment_c_step_running; eassumption.
  - etransitivity; eassumption.
  - exact IHHrun.
Qed.

Definition kernel_program_environment_sequence_include
  environment critical sg observer origin state before input stopped current after output
  (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
    state before input stopped current after output) :
  kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer origin)
    state before input stopped current after output.
Proof.
  induction run.
  - eapply KernelCSequenceRefl; eassumption.
  - apply KernelCSequenceAtom, KernelProgramEnvironmentBody; exact H.
  - eapply KernelCSequenceThen; eassumption.
  - eapply KernelCSequenceAdapt; eassumption.
Defined.

End SelectedEnvironmentCProgram.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module SelectedEnvironmentCSource.
Import SelectedReturnedCProgram SelectedReturnedCSource OSIntExitCCallCompletion
  ReturnedIRQCallSource SelectedEnvironmentCProgram FlagTaskRdyNextCompletion.

Inductive kernel_program_environment_c_step_source environment critical sg observer origin event_observer :
  forall state before input stopped current after output,
  kernel_program_environment_c_step environment critical sg observer origin
    state before input stopped current after output -> Prop :=
| KernelProgramEnvironmentBodySource : forall state before input stopped current after output step,
  kernel_program_returned_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output step ->
  kernel_program_environment_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output
    (@KernelProgramEnvironmentBody environment critical sg observer origin
      state before input stopped current after output step)
| KernelProgramEnvironmentIRQCallSource : forall state before input stopped current after output step,
  os_int_exit_first_level_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output step ->
  kernel_program_environment_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output
    (@KernelProgramEnvironmentIRQCall environment critical sg observer origin
      state before input stopped current after output step)
| KernelProgramEnvironmentFlagTaskRdyNextSource : forall state before input stopped current after output step,
  kernel_program_environment_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output
    (@KernelProgramEnvironmentFlagTaskRdyNext environment critical sg observer origin
      state before input stopped current after output step).

Definition kernel_program_environment_c_sequence_source environment critical sg observer origin event_observer
  state before input stopped current after output
  (run : kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer origin)
    state before input stopped current after output) : Prop :=
  kernel_c_sequence_has_source (kernel_program_environment_c_step environment critical sg observer origin)
    (kernel_program_environment_c_step_source environment critical sg observer origin event_observer)
    state before input stopped current after output run.

Lemma kernel_program_environment_c_step_source_frames :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (step : kernel_program_environment_c_step environment critical sg observer origin
      state before input stopped current after output),
  kernel_program_environment_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output step ->
  task_creation_frame observer state.(TskState) current.(TskState) /\
  (forall invocation, event_observer = Some invocation ->
    event_creation_frame invocation state.(EventState) current.(EventState)) /\
  state.(NameState) = current.(NameState) /\ timer_public_trace sg state.(TimerState) current.(TimerState).
Proof.
  intros until step; intro Hsource; destruct Hsource.
  - eapply kernel_program_returned_c_step_source_frames; exact H.
  - eapply os_int_exit_first_level_c_step_source_frames; exact H.
  - pose proof (flag_task_rdy_next_c_segment_source_frames _ _ _ _ _ _ _ _ _ observer 0%nat step)
      as [Ht [_ [Hname Htimer]]].
    split; [exact Ht|]. split.
    + intros invocation _; exact (proj1 (proj2
        (flag_task_rdy_next_c_segment_source_frames _ _ _ _ _ _ _ _ _ observer invocation step))).
    + exact (conj Hname Htimer).
Qed.

Lemma kernel_program_environment_c_sequence_source_frames :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer origin)
      state before input stopped current after output),
  kernel_program_environment_c_sequence_source environment critical sg observer origin event_observer
    state before input stopped current after output run ->
  task_creation_frame observer state.(TskState) current.(TskState) /\
  (forall invocation, event_observer = Some invocation ->
    event_creation_frame invocation state.(EventState) current.(EventState)) /\
  state.(NameState) = current.(NameState) /\ timer_public_trace sg state.(TimerState) current.(TimerState).
Proof.
  intros until run; intro Hsource.
  eapply (kernel_c_sequence_source_relation
    (kernel_program_environment_c_step environment critical sg observer origin)
    (kernel_program_environment_c_step_source environment critical sg observer origin event_observer)
    (fun entry final => task_creation_frame observer entry.(TskState) final.(TskState) /\
      (forall invocation, event_observer = Some invocation ->
        event_creation_frame invocation entry.(EventState) final.(EventState)) /\
      entry.(NameState) = final.(NameState) /\ timer_public_trace sg entry.(TimerState) final.(TimerState))).
  - intro entry; split; [reflexivity|]. split; [intros; reflexivity|]. split; [reflexivity|constructor].
  - intros first middle last [Ht [He [Hn Hr]]] [Ht' [He' [Hn' Hr']]].
    split.
    + unfold task_creation_frame in *; etransitivity; [exact Ht'|exact Ht].
    + split.
      * intros invocation Hobserver; unfold event_creation_frame in *;
          etransitivity; [exact (He' invocation Hobserver)|exact (He invocation Hobserver)].
      * split; [etransitivity; eassumption|]. eapply timer_public_trace_trans; eassumption.
  - intros; eapply kernel_program_environment_c_step_source_frames; eassumption.
  - exact Hsource.
Qed.

Lemma kernel_program_environment_sequence_include_source :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
      state before input stopped current after output),
  kernel_program_returned_c_sequence_source environment critical sg observer origin event_observer
    state before input stopped current after output run ->
  kernel_program_environment_c_sequence_source environment critical sg observer origin event_observer
    state before input stopped current after output
    (kernel_program_environment_sequence_include environment critical sg observer origin
      state before input stopped current after output run).
Proof.
  intros until run; intro Hsource.
  unfold kernel_program_returned_c_sequence_source in Hsource.
  unfold kernel_program_environment_c_sequence_source.
  induction Hsource; cbn [kernel_program_environment_sequence_include].
  - constructor.
  - apply KernelCSourceAtom, KernelProgramEnvironmentBodySource; exact H.
  - apply KernelCSourceThen; assumption.
  - apply KernelCSourceAdapt; assumption.
Qed.

End SelectedEnvironmentCSource.

Module SelectedEnvironmentCache.
Import SelectedEnvironmentCProgram.

Lemma kernel_program_environment_c_sequence_completed_current_cache :
  forall environment critical sg original returned initial before input stopped current after output,
  kernel_c_sequence (kernel_program_environment_c_step environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial before input stopped current after output ->
  task_in_range sg initial.(TskState) -> kernel_call_task_source original initial ->
  sched_current_consistency initial.(TskState) initial.(SchedState) ->
  kernel_call_normal_return original initial returned current -> kernel_call_task_source returned current ->
  stopped = false /\ sched_current_consistency current.(TskState) current.(SchedState).
Proof.
  intros environment critical sg original returned.
  apply (kernel_c_sequence_completed_current_cache
    (kernel_program_environment_c_step environment critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin)) sg original returned).
  - exact (kernel_program_environment_c_step_preserves_observer environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  - exact (kernel_program_environment_c_step_observer_lifetime environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin)).
Qed.

End SelectedEnvironmentCache.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module SelectedLocalRecovery.
Import PrimitiveComponent SelectedIRQWrapperCompletion.

(** Only [private_frame] is a fixed spatial frame.  [receipt] is interpreted
    at the current C cut and is produced there by the concrete C source.
    This definition states no interference-preservation law. *)
Definition flag_pend_call_receipt_owner
  (receipt : OsSchedCallContext -> UCOS2_Verify_State -> Assertion)
  (private_frame : Assertion) : OsSchedCallContext -> UCOS2_Verify_State -> Assertion :=
  fun call state => receipt call state ** private_frame.

(** These are local SL consequence rules.  Their single-cut entailment is
    discharged by concrete Fresh/First/Waiting reconstruction after the
    same source has produced its current receipt; it is not a C Require. *)
Lemma flag_pend_caller_save_input_receipt_consequence :
  forall environment critical local receipt active sg caller call mask state,
  (receipt call state |-- active call state) ->
  flag_pend_caller_save_input environment critical local receipt sg caller call mask state |--
  flag_pend_caller_save_input environment critical local active sg caller call mask state.
Proof.
  intros environment critical local receipt active sg caller call mask state Hrecover.
  destruct caller; unfold flag_pend_caller_save_input, flag_pend_active_save_input;
    Intros; sep_apply_l_atomic Hrecover; entailer!.
Qed.

Lemma flag_pend_caller_restore_input_receipt_consequence :
  forall environment critical local receipt active sg caller call saved acquired state,
  (receipt call state |-- active call state) ->
  flag_pend_caller_restore_input environment critical local receipt sg caller call saved acquired state |--
  flag_pend_caller_restore_input environment critical local active sg caller call saved acquired state.
Proof.
  intros environment critical local receipt active sg caller call saved acquired state Hrecover.
  destruct caller; unfold flag_pend_caller_restore_input, flag_pend_active_restore_input;
    Intros; sep_apply_l_atomic Hrecover; entailer!.
Qed.

Lemma flag_pend_caller_save_input_receipt_frame :
  forall environment critical local receipt sg caller call mask state private_frame,
  flag_pend_caller_save_input environment critical local
    (flag_pend_call_receipt_owner receipt private_frame) sg caller call mask state --||--
  flag_pend_caller_save_input environment critical local receipt sg caller call mask state ** private_frame.
Proof.
  intros; destruct caller; unfold flag_pend_call_receipt_owner,
    flag_pend_caller_save_input, flag_pend_active_save_input; split; entailer!.
Qed.

Lemma flag_pend_caller_restore_input_receipt_frame :
  forall environment critical local receipt sg caller call saved acquired state private_frame,
  flag_pend_caller_restore_input environment critical local
    (flag_pend_call_receipt_owner receipt private_frame) sg caller call saved acquired state --||--
  flag_pend_caller_restore_input environment critical local receipt sg caller call saved acquired state ** private_frame.
Proof.
  intros; destruct caller; unfold flag_pend_call_receipt_owner,
    flag_pend_caller_restore_input, flag_pend_active_restore_input; split; entailer!.
Qed.

(** The ABI returns the exact receipt stored under its selected descriptor.
    This conversion keeps the handler stack and caller's private bytes
    outside the recovered caller observation. *)
Lemma irq_wrapper_c_output_caller_input :
  forall environment critical sg state local suspended receipt original handler private_frame,
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  original.(os_sched_call_stack) = suspended.(armv7a_continuation_stack) ->
  irq_wrapper_c_output environment sg state local suspended receipt original handler
    (unmap_table_rep sg ** private_frame) |--
  flag_pend_caller_save_input environment critical local (fun _ _ => receipt) sg
    (FlagPendTaskCaller (armv7a_continuation_resumed_call suspended original))
    (armv7a_continuation_resumed_call suspended original)
    (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr))
    (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) **
  task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
  private_frame.
Proof.
  intros environment critical sg state local suspended receipt original handler private_frame Horigin Hstack.
  unfold irq_wrapper_c_output, flag_source_save_input,
    flag_pend_caller_save_input, flag_pend_active_save_input,
    os_sched_fields_save_input, os_sched_fields_capsules,
    kernel_continuation_call_closed, kernel_continuation_inv.
  unfold task_stack_call_active_key, armv7a_continuation_resumed_call; simpl.
  rewrite Horigin, Hstack; entailer!.
Qed.

Lemma irq_wrapper_c_completion_recovered_resources :
  forall environment critical sg state local suspended receipt original node handler private_frame
    before after (active : OsSchedCallContext -> UCOS2_Verify_State -> Assertion),
  irq_wrapper_c_completion environment sg state local suspended receipt original node handler
    (unmap_table_rep sg ** private_frame) before after ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  (receipt |-- active (armv7a_continuation_resumed_call suspended original)
    (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack))) ->
  (flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller (armv7a_continuation_resumed_call suspended original))
    (armv7a_continuation_resumed_call suspended original)
    (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr))
    (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
   private_frame) after.
Proof.
  intros until active; intros Hcomplete Horigin Hrecover.
  pose proof (proj2 (irq_wrapper_c_completion_resources _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete)) as Houtput.
  assert (Hstack : original.(os_sched_call_stack) = suspended.(armv7a_continuation_stack)).
  { pose proof (proj2 (irq_wrapper_c_binding _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete)) as Hbinding.
    rewrite (irq_wrapper_c_saved_call _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete) in Hbinding; exact Hbinding. }
  pose proof (irq_wrapper_c_output_caller_input environment critical sg state local suspended receipt
    original handler private_frame Horigin Hstack) as Hopen.
  specialize (Hopen after Houtput).
  match type of Hopen with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic (flag_pend_caller_save_input_receipt_consequence environment critical local
      (fun _ _ => receipt) active sg
      (FlagPendTaskCaller (armv7a_continuation_resumed_call suspended original))
      (armv7a_continuation_resumed_call suspended original)
      (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr))
      (os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack)) Hrecover).
    entailer!. }
  exact (Hclose after Hopen).
Qed.

End SelectedLocalRecovery.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module SelectedWrapperProgramSupport.
Import CriticalComponent PrimitiveComponent SelectedCProgram SelectedCSource.
Import SelectedIRQWrapperSegment SelectedIRQWrapperSource.

Definition kernel_program_wrapper_paired_primitive environment critical sg observer origin
  state before input stopped current after output
  (primitive : flag_pend_task_primitive_c_step environment critical sg
    state before input stopped current after output) :
  kernel_program_wrapper_c_step environment critical sg observer origin
    state before input stopped current after output :=
  @KernelProgramWrapperOriginal environment critical sg observer origin state before input stopped current after output
    (kernel_program_selected_paired_primitive environment critical sg observer origin
      state before input stopped current after output primitive).

Lemma kernel_program_wrapper_paired_primitive_source :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (primitive : flag_pend_task_primitive_c_step environment critical sg
      state before input stopped current after output),
  kernel_program_wrapper_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output
    (kernel_program_wrapper_paired_primitive environment critical sg observer origin
      state before input stopped current after output primitive).
Proof.
  intros; unfold kernel_program_wrapper_paired_primitive.
  apply KernelProgramWrapperOriginalSource, kernel_program_selected_paired_primitive_source.
Qed.

Lemma kernel_program_wrapper_c_sequence_completed_current_cache :
  forall environment critical sg original returned initial before input stopped current after output,
  kernel_c_sequence (kernel_program_wrapper_c_step environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial before input stopped current after output ->
  task_in_range sg initial.(TskState) -> kernel_call_task_source original initial ->
  sched_current_consistency initial.(TskState) initial.(SchedState) ->
  kernel_call_normal_return original initial returned current -> kernel_call_task_source returned current ->
  stopped = false /\ sched_current_consistency current.(TskState) current.(SchedState).
Proof.
  intros environment critical sg original returned.
  apply (kernel_c_sequence_completed_current_cache
    (kernel_program_wrapper_c_step environment critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin)) sg original returned).
  - exact (kernel_program_wrapper_c_step_preserves_observer environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  - exact (kernel_program_wrapper_c_step_observer_lifetime environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin)).
Qed.

End SelectedWrapperProgramSupport.

Module SelectedReturnedPrimitiveSupport.
Import PrimitiveComponent SelectedReturnedCProgram SelectedReturnedCSource SelectedWrapperProgramSupport.

Definition kernel_program_returned_paired_primitive environment critical sg observer origin
  state before input stopped current after output
  (primitive : flag_pend_task_primitive_c_step environment critical sg
    state before input stopped current after output) :
  kernel_program_returned_c_step environment critical sg observer origin
    state before input stopped current after output :=
  @KernelProgramReturnedWrapper environment critical sg observer origin state before input stopped current after output
    (kernel_program_wrapper_paired_primitive environment critical sg observer origin
      state before input stopped current after output primitive).

Lemma kernel_program_returned_paired_primitive_source :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (primitive : flag_pend_task_primitive_c_step environment critical sg
      state before input stopped current after output),
  kernel_program_returned_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output
    (kernel_program_returned_paired_primitive environment critical sg observer origin
      state before input stopped current after output primitive).
Proof.
  intros; unfold kernel_program_returned_paired_primitive.
  apply KernelProgramReturnedWrapperSource, kernel_program_wrapper_paired_primitive_source.
Qed.

End SelectedReturnedPrimitiveSupport.

Module SelectedEnvironmentPrimitiveSupport.
Import PrimitiveComponent SelectedReturnedCProgram SelectedReturnedCSource
  SelectedEnvironmentCProgram SelectedEnvironmentCSource SelectedReturnedPrimitiveSupport.

Definition kernel_program_environment_paired_primitive environment critical sg observer origin
  state before input stopped current after output
  (primitive : flag_pend_task_primitive_c_step environment critical sg
    state before input stopped current after output) :
  kernel_program_environment_c_step environment critical sg observer origin
    state before input stopped current after output :=
  @KernelProgramEnvironmentBody environment critical sg observer origin state before input stopped current after output
    (kernel_program_returned_paired_primitive environment critical sg observer origin
      state before input stopped current after output primitive).

Lemma kernel_program_environment_paired_primitive_source :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (primitive : flag_pend_task_primitive_c_step environment critical sg
      state before input stopped current after output),
  kernel_program_environment_c_step_source environment critical sg observer origin event_observer
    state before input stopped current after output
    (kernel_program_environment_paired_primitive environment critical sg observer origin
      state before input stopped current after output primitive).
Proof.
  intros; unfold kernel_program_environment_paired_primitive.
  apply KernelProgramEnvironmentBodySource, kernel_program_returned_paired_primitive_source.
Qed.

End SelectedEnvironmentPrimitiveSupport.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module SelectedEnvironmentScopedSource.
Import SelectedEnvironmentCProgram SelectedEnvironmentCSource.

Import SelectedIRQWrapperSegment SelectedIRQWrapperSource.

(** The C caller's captured heap and the actual environment heap are
    different indices.  Both joins use the very heaps of the original
    execution.  Private owners are its real entry and return resources;
    no private resource is hidden in a pure caller observation. *)
Inductive kernel_call_scoped_c_execution environment critical sg observer origin
  initial caller_before input stopped current caller_after output : Prop :=
| KernelCallScopedCExecution :
  forall private_input private_output whole_before whole_after private_before private_after
    (run : kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer origin)
      initial whole_before (input ** private_input) stopped current whole_after (output ** private_output)),
  input caller_before -> private_input private_before -> join caller_before private_before whole_before ->
  output caller_after -> private_output private_after -> join caller_after private_after whole_after ->
  kernel_call_scoped_c_execution environment critical sg observer origin
    initial caller_before input stopped current caller_after output.

Inductive kernel_call_scoped_c_execution_source environment critical sg observer origin event_observer :
  forall initial caller_before input stopped current caller_after output,
  kernel_call_scoped_c_execution environment critical sg observer origin
    initial caller_before input stopped current caller_after output -> Prop :=
| KernelCallScopedCExecutionSource :
  forall initial caller_before input stopped current caller_after output
    private_input private_output whole_before whole_after private_before private_after run
    owned_before private_owned_before join_before owned_after private_owned_after join_after,
  kernel_program_environment_c_sequence_source environment critical sg observer origin event_observer
    initial whole_before (input ** private_input) stopped current whole_after (output ** private_output) run ->
  kernel_call_scoped_c_execution_source environment critical sg observer origin event_observer
    initial caller_before input stopped current caller_after output
    (@KernelCallScopedCExecution environment critical sg observer origin initial caller_before input
      stopped current caller_after output private_input private_output whole_before whole_after private_before private_after
      run owned_before private_owned_before join_before owned_after private_owned_after join_after).

Lemma kernel_call_scoped_c_execution_resources :
  forall environment critical sg observer origin initial caller_before input stopped current caller_after output,
  kernel_call_scoped_c_execution environment critical sg observer origin
    initial caller_before input stopped current caller_after output ->
  input caller_before /\ output caller_after.
Proof. intros until output; intro Hactual; destruct Hactual; auto. Qed.

(** A concrete producer fixes the caller's real input heap.  Its output
    caller heap is obtained by destructing the postcondition of that same
    execution, not by supplying a desired future output owner. *)
Lemma kernel_call_scoped_c_execution_from_sequence :
  forall environment critical sg observer origin event_observer initial caller_before input stopped current output
    private_input private_output whole_before whole_after private_before
    (run : kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer origin)
      initial whole_before (input ** private_input) stopped current whole_after (output ** private_output)),
  kernel_program_environment_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ run ->
  input caller_before -> private_input private_before -> join caller_before private_before whole_before ->
  exists caller_after (actual : kernel_call_scoped_c_execution environment critical sg observer origin
    initial caller_before input stopped current caller_after output),
  kernel_call_scoped_c_execution_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ actual.
Proof.
  intros environment critical sg observer origin event_observer initial caller_before input stopped current output
    private_input private_output whole_before whole_after private_before run Hsource Hinput Hprivate Hjoin.
  pose proof (proj2 (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ run)) as Houtput.
  destruct Houtput as [caller_after [private_after [Hjoin_after [Hcaller_after Hprivate_after]]]].
  pose (actual := @KernelCallScopedCExecution environment critical sg observer origin initial caller_before input
    stopped current caller_after output private_input private_output whole_before whole_after private_before private_after
    run Hinput Hprivate Hjoin Hcaller_after Hprivate_after Hjoin_after).
  exists caller_after, actual; unfold actual; constructor; exact Hsource.
Qed.

Lemma kernel_call_scoped_c_execution_source_frames :
  forall environment critical sg observer origin event_observer initial caller_before input stopped current caller_after output
    (actual : kernel_call_scoped_c_execution environment critical sg observer origin
      initial caller_before input stopped current caller_after output),
  kernel_call_scoped_c_execution_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ actual ->
  task_creation_frame observer initial.(TskState) current.(TskState) /\
  (forall invocation, event_observer = Some invocation ->
    event_creation_frame invocation initial.(EventState) current.(EventState)) /\
  initial.(NameState) = current.(NameState) /\ timer_public_trace sg initial.(TimerState) current.(TimerState).
Proof.
  intros until actual; intro Hsource; destruct Hsource.
  eapply kernel_program_environment_c_sequence_source_frames; eassumption.
Qed.

Lemma kernel_call_scoped_c_execution_observer_lifetime :
  forall environment critical sg observer origin initial caller_before input stopped current caller_after output,
  kernel_call_scoped_c_execution environment critical sg observer origin
    initial caller_before input stopped current caller_after output ->
  task_observer_lifetime_result observer origin initial.(TskState) current.(TskState) stopped.
Proof.
  intros until output; intro Hactual; destruct Hactual.
  eapply kernel_program_environment_c_sequence_observer_lifetime; eassumption.
Qed.

Lemma kernel_call_scoped_c_execution_preserves_observer :
  forall environment critical sg observer origin initial caller_before input stopped current caller_after output,
  kernel_call_scoped_c_execution environment critical sg observer origin
    initial caller_before input stopped current caller_after output -> stopped = false ->
  task_invocation_active initial.(TskState) observer origin /\ sched_observer_current_cache origin initial ->
  task_invocation_active current.(TskState) observer origin /\ sched_observer_current_cache origin current.
Proof.
  intros until output; intros Hactual Hstop Hinitial; destruct Hactual.
  eapply kernel_program_environment_c_sequence_preserves_observer; eassumption.
Qed.

Lemma kernel_call_scoped_c_execution_running :
  forall environment critical sg observer origin initial caller_before input stopped current caller_after output,
  kernel_call_scoped_c_execution environment critical sg observer origin
    initial caller_before input stopped current caller_after output ->
  current.(SchedState).(isRunning) = initial.(SchedState).(isRunning).
Proof.
  intros until output; intro Hactual; destruct Hactual.
  eapply kernel_program_environment_c_sequence_running; eassumption.
Qed.

End SelectedEnvironmentScopedSource.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module SelectedEnvironmentScopedPrimitives.
Import SelectedEnvironmentCProgram SelectedEnvironmentCSource.

Import PrimitiveComponent SelectedIRQWrapperSegment SelectedIRQWrapperSource.
Import SelectedLocalRecovery SelectedEnvironmentPrimitiveSupport.

(** These are the unchanged ABI operations on the actual whole heap.
    The private assertion is framed only across this state-preserving
    primitive.  The surrounding C environment may change that assertion. *)
Lemma flag_pend_scoped_save_suffix_sequence :
  forall environment critical local active sg observer origin event_observer
    call mask state private_frame arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers before final_registers after,
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller call) call mask state ** private_frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers state after ->
  interrupt_saved_value mask final_registers.(kernel_save_r0) /\
  exists (completed : kernel_c_sequence
    (kernel_program_environment_c_step environment critical sg observer origin)
    state before
    (flag_pend_caller_save_input environment critical local active sg
      (FlagPendTaskCaller call) call mask state ** private_frame)
    false state after
    (flag_pend_caller_restore_input environment critical local active sg
      (FlagPendTaskCaller call) call final_registers.(kernel_save_r0) state state ** private_frame)),
  kernel_program_environment_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ completed.
Proof.
  intros environment critical local active sg observer origin event_observer call mask state
    private_frame arch save registers before final_registers after Hreturn Hvalid Hmask Hinput Hsuffix.
  pose proof (proj2 (flag_pend_caller_save_input_receipt_frame environment critical local active sg
    (FlagPendTaskCaller call) call mask state private_frame)) as Hin.
  pose proof (Hin before Hinput) as Hclosed.
  pose proof (proj1 (flag_pend_caller_restore_input_receipt_frame environment critical local active sg
    (FlagPendTaskCaller call) call final_registers.(kernel_save_r0) state state private_frame)) as Hout.
  destruct (flag_pend_task_uninterrupted_save_resources environment critical sg local
    (flag_pend_call_receipt_owner active private_frame) call mask state arch save
    registers before final_registers after Hreturn Hvalid Hmask Hclosed Hsuffix) as [Hsaved Hmasked].
  split; [exact Hsaved|].
  assert (Hprimitive : flag_pend_task_primitive_c_step environment critical sg
    state before
    (flag_pend_caller_save_input environment critical local
      (flag_pend_call_receipt_owner active private_frame) sg (FlagPendTaskCaller call) call mask state)
    false state after
    ((flag_pend_task_save_c_event environment critical local
      (flag_pend_call_receipt_owner active private_frame) sg call mask
      final_registers.(kernel_save_r0) state before after).(flag_pend_event_output))).
  { apply (FlagPendTaskPrimitiveCStep environment critical sg
      (flag_pend_task_save_c_event environment critical local
        (flag_pend_call_receipt_owner active private_frame) sg call mask
        final_registers.(kernel_save_r0) state before after)).
    eapply FlagPendTaskPrimitiveSave; eassumption. }
  pose (Hstep := @kernel_program_environment_paired_primitive environment critical sg observer origin
    _ _ _ _ _ _ _ Hprimitive).
  pose (Hatom := KernelCSequenceAtom _ _ _ _ _ _ _ _ Hstep).
  exists (KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput Hin Hatom
    (fun heap Howner => Hout heap (proj2 Howner))).
  unfold kernel_program_environment_c_sequence_source.
  apply KernelCSourceAdapt, KernelCSourceAtom.
  unfold Hstep; apply kernel_program_environment_paired_primitive_source.
Qed.

Lemma flag_pend_scoped_restore_prefix_sequence :
  forall environment critical local active sg observer origin event_observer
    call saved acquired state private_frame arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor before written after,
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller call) call saved acquired state ** private_frame) before ->
  armv7a_restore_prefix_transition restore cursor before written after ->
  exists (completed : kernel_c_sequence
    (kernel_program_environment_c_step environment critical sg observer origin)
    state before
    (flag_pend_caller_restore_input environment critical local active sg
      (FlagPendTaskCaller call) call saved acquired state ** private_frame)
    false state after
    (flag_pend_caller_save_input environment critical local active sg
      (FlagPendTaskCaller call) call (armv7a_irq_fiq_mask saved) state ** private_frame)),
  kernel_program_environment_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ completed.
Proof.
  intros environment critical local active sg observer origin event_observer call saved acquired state
    private_frame arch restore cursor before written after Hr0 Hmask Hinput Hprefix.
  pose proof (proj2 (flag_pend_caller_restore_input_receipt_frame environment critical local active sg
    (FlagPendTaskCaller call) call saved acquired state private_frame)) as Hin.
  pose proof (proj1 (flag_pend_caller_save_input_receipt_frame environment critical local active sg
    (FlagPendTaskCaller call) call (armv7a_irq_fiq_mask saved) state private_frame)) as Hout.
  assert (Hprimitive : flag_pend_task_primitive_c_step environment critical sg
    state before
    (flag_pend_caller_restore_input environment critical local
      (flag_pend_call_receipt_owner active private_frame) sg (FlagPendTaskCaller call) call saved acquired state)
    false state after
    (flag_pend_caller_save_input environment critical local
      (flag_pend_call_receipt_owner active private_frame) sg (FlagPendTaskCaller call) call
      (armv7a_irq_fiq_mask saved) state)).
  { eapply FlagPendTaskRestoreCPrefix; [exact Hr0|exact Hmask|exact (Hin before Hinput)|exact Hprefix]. }
  pose (Hstep := @kernel_program_environment_paired_primitive environment critical sg observer origin
    _ _ _ _ _ _ _ Hprimitive).
  pose (Hatom := KernelCSequenceAtom _ _ _ _ _ _ _ _ Hstep).
  exists (KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput Hin Hatom Hout).
  unfold kernel_program_environment_c_sequence_source.
  apply KernelCSourceAdapt, KernelCSourceAtom.
  unfold Hstep; apply kernel_program_environment_paired_primitive_source.
Qed.

Lemma flag_pend_scoped_restore_suffix_sequence :
  forall environment critical local active sg observer origin event_observer
    call state private_frame word arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor before final_cursor after,
  cursor.(kernel_restore_msr_word) = Some word ->
  (flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller call) call (armv7a_irq_fiq_mask word) state ** private_frame) before ->
  armv7a_restore_suffix_transition restore cursor before final_cursor after ->
  exists (completed : kernel_c_sequence
    (kernel_program_environment_c_step environment critical sg observer origin)
    state before
    (flag_pend_caller_save_input environment critical local active sg
      (FlagPendTaskCaller call) call (armv7a_irq_fiq_mask word) state ** private_frame)
    false state after
    (flag_pend_caller_save_input environment critical local active sg
      (FlagPendTaskCaller call) call (armv7a_irq_fiq_mask word) state ** private_frame)),
  kernel_program_environment_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ completed.
Proof.
  intros environment critical local active sg observer origin event_observer call state
    private_frame word arch restore cursor before final_cursor after Hword Hinput Hsuffix.
  pose proof (flag_pend_caller_save_input_receipt_frame environment critical local active sg
    (FlagPendTaskCaller call) call (armv7a_irq_fiq_mask word) state private_frame) as Hframe.
  assert (Hprimitive : flag_pend_task_primitive_c_step environment critical sg
    state before
    (flag_pend_caller_save_input environment critical local
      (flag_pend_call_receipt_owner active private_frame) sg (FlagPendTaskCaller call) call
      (armv7a_irq_fiq_mask word) state)
    false state after
    (flag_pend_caller_save_input environment critical local
      (flag_pend_call_receipt_owner active private_frame) sg (FlagPendTaskCaller call) call
      (armv7a_irq_fiq_mask word) state)).
  { eapply FlagPendTaskRestoreCSuffix; [exact Hword|exact (proj2 Hframe before Hinput)|exact Hsuffix]. }
  pose (Hstep := @kernel_program_environment_paired_primitive environment critical sg observer origin
    _ _ _ _ _ _ _ Hprimitive).
  pose (Hatom := KernelCSequenceAtom _ _ _ _ _ _ _ _ Hstep).
  exists (KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput (proj2 Hframe) Hatom (proj1 Hframe)).
  unfold kernel_program_environment_c_sequence_source.
  apply KernelCSourceAdapt, KernelCSourceAtom.
  unfold Hstep; apply kernel_program_environment_paired_primitive_source.
Qed.

End SelectedEnvironmentScopedPrimitives.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module SelectedEnvironmentScopedEnvironment.
Import SelectedEnvironmentCProgram SelectedEnvironmentCSource.

Import PrimitiveComponent SelectedIRQWrapperSegment SelectedIRQWrapperSource.
Import SelectedEnvironmentScopedSource SelectedEnvironmentScopedPrimitives.

(** The environment's private owner is allowed to change with its actual
    C execution.  Its heap is never identified with the caller heap cut. *)
Definition flag_pend_scoped_environment_run environment critical local next_local active sg
  original mask initial whole_before private_input stopped returned current whole_after private_output : Prop :=
  kernel_c_sequence
    (kernel_program_environment_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial whole_before
    (flag_pend_caller_save_input environment critical local active sg
      (FlagPendTaskCaller original) original mask initial ** private_input)
    stopped current whole_after
    (coq_prop (flag_pend_call_endpoint_observations environment sg
      (FlagPendTaskCaller original) original initial returned current) &&
     (flag_pend_caller_save_input environment critical next_local active sg
       (FlagPendTaskCaller returned) returned mask current ** private_output)).

Definition flag_pend_scoped_environment_source environment critical local next_local active sg
  event_observer original mask initial whole_before private_input stopped returned current whole_after private_output
  (run : flag_pend_scoped_environment_run environment critical local next_local active sg
    original mask initial whole_before private_input stopped returned current whole_after private_output) : Prop :=
  kernel_program_environment_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer
    _ _ _ _ _ _ _ run.

Lemma flag_pend_scoped_environment_save_sequence :
  forall environment critical local next_local active sg event_observer original mask initial
    whole_before private_input stopped returned current environment_heap private_output arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers final_registers whole_after
    (run : flag_pend_scoped_environment_run environment critical local next_local active sg
      original mask initial whole_before private_input stopped returned current environment_heap private_output),
  flag_pend_scoped_environment_source environment critical local next_local active sg event_observer
    original mask initial whole_before private_input stopped returned current environment_heap private_output run ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current environment_heap
    final_registers current whole_after ->
  interrupt_saved_value mask final_registers.(kernel_save_r0) /\
  exists (completed : kernel_c_sequence
    (kernel_program_environment_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial whole_before
    (flag_pend_caller_save_input environment critical local active sg
      (FlagPendTaskCaller original) original mask initial ** private_input)
    stopped current whole_after
    ((coq_prop (flag_pend_call_endpoint_observations environment sg
       (FlagPendTaskCaller original) original initial returned current) &&
      flag_pend_caller_restore_input environment critical next_local active sg
       (FlagPendTaskCaller returned) returned final_registers.(kernel_save_r0) current current) ** private_output)),
  kernel_program_environment_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer
    _ _ _ _ _ _ _ completed.
Proof.
  intros environment critical local next_local active sg event_observer original mask initial
    whole_before private_input stopped returned current environment_heap private_output arch save
    registers final_registers whole_after run Hsource Hreturn Hvalid Hmask Hsuffix.
  destruct (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ run)
    as [Hinitial [Hendpoint Hclosed]].
  destruct (flag_pend_scoped_save_suffix_sequence environment critical next_local active sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer
    returned mask current private_output arch save registers environment_heap final_registers whole_after
    Hreturn Hvalid Hmask Hclosed Hsuffix) as [Hsaved [Hsuffix_run Hsuffix_source]].
  split; [exact Hsaved|].
  assert (Hpost :
    flag_pend_caller_restore_input environment critical next_local active sg
      (FlagPendTaskCaller returned) returned final_registers.(kernel_save_r0) current current ** private_output |--
    (coq_prop (flag_pend_call_endpoint_observations environment sg
       (FlagPendTaskCaller original) original initial returned current) &&
      flag_pend_caller_restore_input environment critical next_local active sg
       (FlagPendTaskCaller returned) returned final_registers.(kernel_save_r0) current current) ** private_output).
  { entailer!. }
  pose (Htail := KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _
    (conj Hendpoint Hclosed) (fun heap Howner => proj2 Howner) Hsuffix_run Hpost).
  replace stopped with (orb stopped false) by apply Bool.orb_false_r.
  exists (KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _
    run (fun heap Howner => Howner) Htail).
  unfold kernel_program_environment_c_sequence_source.
  apply KernelCSourceThen; [exact Hsource|].
  unfold Htail; apply KernelCSourceAdapt; exact Hsuffix_source.
Qed.

Lemma flag_pend_scoped_environment_restore_sequence :
  forall environment critical local next_local active sg event_observer original saved acquired initial
    whole_before private_input stopped returned current environment_heap private_output arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written prefix_heap final_cursor whole_after
    (run : flag_pend_scoped_environment_run environment critical local next_local active sg
      original (armv7a_irq_fiq_mask saved) initial prefix_heap private_input
      stopped returned current environment_heap private_output),
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired initial ** private_input) whole_before ->
  armv7a_restore_prefix_transition restore cursor whole_before written prefix_heap ->
  flag_pend_scoped_environment_source environment critical local next_local active sg event_observer
    original (armv7a_irq_fiq_mask saved) initial prefix_heap private_input
    stopped returned current environment_heap private_output run ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor whole_after ->
  exists (completed : kernel_c_sequence
    (kernel_program_environment_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial whole_before
    (flag_pend_caller_restore_input environment critical local active sg
      (FlagPendTaskCaller original) original saved acquired initial ** private_input)
    stopped current whole_after
    ((coq_prop (flag_pend_call_endpoint_observations environment sg
       (FlagPendTaskCaller original) original initial returned current) &&
      flag_pend_caller_save_input environment critical next_local active sg
       (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current) ** private_output)),
  kernel_program_environment_c_sequence_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer
    _ _ _ _ _ _ _ completed.
Proof.
  intros environment critical local next_local active sg event_observer original saved acquired initial
    whole_before private_input stopped returned current environment_heap private_output arch restore
    cursor written prefix_heap final_cursor whole_after run Hr0 Hmask Hinput Hprefix Hsource Hsuffix.
  destruct (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ run)
    as [Hinitial [Hendpoint Hclosed]].
  destruct (SelectedEnvironment.flag_pend_task_restore_prefix_written_mask environment critical arch restore
    cursor whole_before written prefix_heap saved Hr0 Hprefix) as [word [Hword Hword_mask]].
  destruct (flag_pend_scoped_restore_prefix_sequence environment critical local active sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer
    original saved acquired initial private_input arch restore cursor whole_before written prefix_heap
    Hr0 Hmask Hinput Hprefix) as [Hprefix_run Hprefix_source].
  assert (Hclosed_word :
    (flag_pend_caller_save_input environment critical next_local active sg
      (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask word) current ** private_output) environment_heap).
  { rewrite Hword_mask; exact Hclosed. }
  destruct (flag_pend_scoped_restore_suffix_sequence environment critical next_local active sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer
    returned current private_output word arch restore written environment_heap final_cursor whole_after
    Hword Hclosed_word Hsuffix) as [Hsuffix_run Hsuffix_source].
  assert (Hpre :
    coq_prop (flag_pend_call_endpoint_observations environment sg
      (FlagPendTaskCaller original) original initial returned current) &&
    (flag_pend_caller_save_input environment critical next_local active sg
      (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current ** private_output) |--
    flag_pend_caller_save_input environment critical next_local active sg
      (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask word) current ** private_output).
  { rewrite Hword_mask; intros heap Howner; exact (proj2 Howner). }
  assert (Hpost :
    flag_pend_caller_save_input environment critical next_local active sg
      (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask word) current ** private_output |--
    (coq_prop (flag_pend_call_endpoint_observations environment sg
       (FlagPendTaskCaller original) original initial returned current) &&
      flag_pend_caller_save_input environment critical next_local active sg
       (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current) ** private_output).
  { rewrite Hword_mask; entailer!. }
  pose (Htail := KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _
    (conj Hendpoint Hclosed) Hpre Hsuffix_run Hpost).
  pose (Hmiddle := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _
    run (fun heap Howner => Howner) Htail).
  replace stopped with (orb false (orb stopped false)) by (simpl; apply Bool.orb_false_r).
  exists (KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _
    Hprefix_run (fun heap Howner => Howner) Hmiddle).
  unfold kernel_program_environment_c_sequence_source.
  apply KernelCSourceThen; [exact Hprefix_source|].
  unfold Hmiddle; apply KernelCSourceThen; [exact Hsource|].
  unfold Htail; apply KernelCSourceAdapt; exact Hsuffix_source.
Qed.

(** The first caller heap is the captured C argument.  The final caller
    heap is produced by splitting the actual composed execution's post. *)
Lemma flag_pend_scoped_environment_save_call :
  forall environment critical local next_local active sg event_observer original mask initial
    caller_before private_before whole_before private_input stopped returned current environment_heap private_output arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers final_registers whole_after
    (run : flag_pend_scoped_environment_run environment critical local next_local active sg
      original mask initial whole_before private_input stopped returned current environment_heap private_output),
  flag_pend_scoped_environment_source environment critical local next_local active sg event_observer
    original mask initial whole_before private_input stopped returned current environment_heap private_output run ->
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller original) original mask initial caller_before ->
  private_input private_before -> join caller_before private_before whole_before ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current environment_heap
    final_registers current whole_after ->
  interrupt_saved_value mask final_registers.(kernel_save_r0) /\
  exists caller_after (actual : kernel_call_scoped_c_execution environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    initial caller_before
    (flag_pend_caller_save_input environment critical local active sg
      (FlagPendTaskCaller original) original mask initial)
    stopped current caller_after
    (coq_prop (flag_pend_call_endpoint_observations environment sg
       (FlagPendTaskCaller original) original initial returned current) &&
      flag_pend_caller_restore_input environment critical next_local active sg
       (FlagPendTaskCaller returned) returned final_registers.(kernel_save_r0) current current)),
  kernel_call_scoped_c_execution_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ actual.
Proof.
  intros environment critical local next_local active sg event_observer original mask initial
    caller_before private_before whole_before private_input stopped returned current environment_heap private_output arch save
    registers final_registers whole_after run Hsource Hinput Hprivate Hjoin Hreturn Hvalid Hmask Hsuffix.
  destruct (flag_pend_scoped_environment_save_sequence environment critical local next_local active sg
    event_observer original mask initial whole_before private_input stopped returned current environment_heap private_output
    arch save registers final_registers whole_after run Hsource Hreturn Hvalid Hmask Hsuffix)
    as [Hsaved [completed Hcompleted_source]].
  split; [exact Hsaved|].
  eapply kernel_call_scoped_c_execution_from_sequence; eassumption.
Qed.

Lemma flag_pend_scoped_environment_restore_call :
  forall environment critical local next_local active sg event_observer original saved acquired initial
    caller_before private_before whole_before private_input stopped returned current environment_heap private_output arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written prefix_heap final_cursor whole_after
    (run : flag_pend_scoped_environment_run environment critical local next_local active sg
      original (armv7a_irq_fiq_mask saved) initial prefix_heap private_input
      stopped returned current environment_heap private_output),
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired initial caller_before ->
  private_input private_before -> join caller_before private_before whole_before ->
  armv7a_restore_prefix_transition restore cursor whole_before written prefix_heap ->
  flag_pend_scoped_environment_source environment critical local next_local active sg event_observer
    original (armv7a_irq_fiq_mask saved) initial prefix_heap private_input
    stopped returned current environment_heap private_output run ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor whole_after ->
  exists caller_after (actual : kernel_call_scoped_c_execution environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    initial caller_before
    (flag_pend_caller_restore_input environment critical local active sg
      (FlagPendTaskCaller original) original saved acquired initial)
    stopped current caller_after
    (coq_prop (flag_pend_call_endpoint_observations environment sg
       (FlagPendTaskCaller original) original initial returned current) &&
      flag_pend_caller_save_input environment critical next_local active sg
       (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current)),
  kernel_call_scoped_c_execution_source environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ actual.
Proof.
  intros environment critical local next_local active sg event_observer original saved acquired initial
    caller_before private_before whole_before private_input stopped returned current environment_heap private_output arch restore
    cursor written prefix_heap final_cursor whole_after run Hr0 Hmask Hinput Hprivate Hjoin Hprefix Hsource Hsuffix.
  assert (Hwhole :
    (flag_pend_caller_restore_input environment critical local active sg
      (FlagPendTaskCaller original) original saved acquired initial ** private_input) whole_before).
  { exists caller_before, private_before; exact (conj Hjoin (conj Hinput Hprivate)). }
  destruct (flag_pend_scoped_environment_restore_sequence environment critical local next_local active sg
    event_observer original saved acquired initial whole_before private_input stopped returned current environment_heap private_output
    arch restore cursor written prefix_heap final_cursor whole_after run Hr0 Hmask Hwhole Hprefix Hsource Hsuffix)
    as [completed Hcompleted_source].
  eapply kernel_call_scoped_c_execution_from_sequence; eassumption.
Qed.

End SelectedEnvironmentScopedEnvironment.
