Require Import Coq.ZArith.ZArith Coq.Bool.Bool.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_local_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_environment_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_wrapper_completion_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_returned_c_segment_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_return_view_control_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_control_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_envelope_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_completion_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_irq_entry_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_irq_call_connection_spec.
Import UCOS2_C_Rules TaskStateDef.
Import SelectedReturnedCProgram SelectedReturnedCSource SelectedIRQWrapperCompletion OSIntExitReturnedC.
Import OSIntExitReturnView OSIntExitCCallControl OSIntExitCCallEnvelope OSIntExitCCallCompletion.
Import ReturnedIRQEntryResources ReturnedIRQCallSource SelectedLocalRecovery.
Import SelectedEnvironmentCProgram SelectedEnvironmentCSource.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The saved receipt is constant: arbitrary caller resources can be kept in
    it without assuming a future state-indexed assertion. The entry local is
    the actual temporary IRQ interpretation of the SAME base local that the
    returned completion recovers. These are not two unrelated EX witnesses. *)
Section SemPendIRQCallerLocal.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (observer : nat) (stored_origin : TaskInvocationOrigin)
  (event_observer : option nat).
Context (initial : UCOS2_Verify_State) (entry_node : TaskAbstractState)
  (handler : OsIntExitCallContext) (suspended : Armv7aContinuation) (publication : nat)
  (local : Armv7aContinuation -> Assertion) (receipt private_frame : Assertion)
  (before saved_heap body_heap : model).
Context (body_input : Assertion) (prefix_stop : bool) (observed : UCOS2_Verify_State)
  (read_heap : model) (prefix_output read_input : Assertion) (acquire_stop : bool)
  (entry : UCOS2_Verify_State) (acquired_heap : model) (acquire_output : Assertion).
Context (prefix : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer stored_origin)
  (sem_pend_irq_entry_state initial handler suspended)
  body_heap body_input prefix_stop observed read_heap prefix_output).
Context (acquire : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer stored_origin)
  observed read_heap read_input acquire_stop entry acquired_heap acquire_output).
Context (observation_frame : Assertion) (original : OsSchedCallContext)
  (node : TaskAbstractState) (middle after : model).
Context (Hentry : os_int_exit_first_level_entry_c_completion environment sg initial entry_node handler suspended
  publication (kernel_irq_fields_local local suspended receipt) (unmap_table_rep sg ** private_frame)
  before saved_heap body_heap).
Context (Hentry_bridge : os_int_exit_first_level_entry_output environment sg initial handler suspended
  (kernel_irq_fields_local local suspended receipt) (unmap_table_rep sg ** private_frame) |-- body_input).
Context (Hprefix_control : kernel_returned_c_body_sequence_source environment critical sg observer stored_origin
  _ _ _ _ _ _ _ prefix).
Context (Hread_bridge : prefix_output |-- read_input).
Context (Hacquire_control : kernel_returned_c_body_sequence_source environment critical sg observer stored_origin
  _ _ _ _ _ _ _ acquire).
Context (Hreturn_bridge : acquire_output |--
  os_int_exit_returned_c_input environment sg entry local suspended receipt handler private_frame).
Context (Hreturned : os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
  entry local suspended receipt original node handler private_frame acquired_heap middle after).
Context (Horigin : original.(os_sched_call_origin) =
  RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration)).

Let caller_input := flag_pend_caller_save_input environment critical local (fun _ _ => receipt) sg
  (FlagPendTaskCaller original) original handler.(os_int_exit_interrupted_mask) initial **
  (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
    private_frame).
Let checkpoint := os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry.
Let resumed := armv7a_continuation_resumed_call suspended original.
Let current := os_int_exit_wrapper_restored_state checkpoint suspended.(armv7a_continuation_stack).
Let caller_output := flag_pend_caller_save_input environment critical local (fun _ _ => receipt) sg
  (FlagPendTaskCaller resumed) resumed (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) current **
  task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
  private_frame.
Let entry_input := os_int_exit_first_level_entry_input environment sg initial handler suspended
  (kernel_irq_fields_local local suspended receipt) (unmap_table_rep sg ** private_frame).
Let returned_output := irq_wrapper_c_output environment sg checkpoint local suspended receipt original handler
  (unmap_table_rep sg ** private_frame).

Lemma sem_pend_irq_caller_local_bridges :
  (caller_input |-- entry_input) /\ (returned_output |-- caller_output).
Proof.
  assert (Hcall : original = handler.(os_int_exit_interrupted_call)).
  { eapply os_int_exit_returned_c_completion_interrupted_call.
    - exact Hreturned.
    - exact (os_int_exit_entry_actual_save _ _ _ _ _ _ _ _ _ _ _ _ Hentry). }
  assert (Hstack : original.(os_sched_call_stack) = suspended.(armv7a_continuation_stack)).
  { pose proof (proj2 (os_int_exit_returned_binding _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hreturned)) as Hbinding.
    rewrite (os_int_exit_returned_saved_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hreturned) in Hbinding.
    exact Hbinding. }
  split.
  - unfold caller_input, entry_input.
    eapply flag_pend_caller_save_input_irq_entry.
    + symmetry; exact Hcall.
    + reflexivity.
    + symmetry; exact Hstack.
    + rewrite Hcall; exact (os_int_exit_entry_not_parked _ _ _ _ _ _ _ _ _ _ _ _ Hentry).
  - unfold returned_output, caller_output, resumed, current.
    apply irq_wrapper_c_output_caller_input; assumption.
Qed.

Let completed := @OSIntExitFirstLevelCStep environment critical sg observer stored_origin
  initial entry_node handler suspended publication (kernel_irq_fields_local local suspended receipt)
  (unmap_table_rep sg ** private_frame) before saved_heap body_heap
  body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
  prefix acquire observation_frame local receipt original node private_frame middle after
  Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge Hreturned.
Let step := @KernelProgramEnvironmentIRQCall environment critical sg observer stored_origin
  _ _ _ _ _ _ _ completed.
Let raw := KernelCSequenceAtom _ _ _ _ _ _ _ _ step.
Let segment := kernel_program_environment_c_step environment critical sg observer stored_origin.
Let observed_leaf := fun state heap input stopped result output_heap output
  (actual : segment state heap input stopped result output_heap output) source_origin result_origin =>
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer event_observer source_origin state stopped result_origin result.

(** Adapt the very whole-call Atom, not a newly chosen execution with equal
    endpoints. Source, certificate and recovered caller owner share that run.
    The prefix and acquire retain their original module-call attachments. *)
Lemma sem_pend_irq_caller_local_sequence :
  forall first prefix_origin acquired_origin
    (prefix_leaf : forall state heap input stopped result output_heap output,
      kernel_program_returned_c_step environment critical sg observer stored_origin
        state heap input stopped result output_heap output -> TaskInvocationOrigin -> TaskInvocationOrigin -> Prop)
    (acquire_leaf : forall state heap input stopped result output_heap output,
      kernel_program_returned_c_step environment critical sg observer stored_origin
        state heap input stopped result output_heap output -> TaskInvocationOrigin -> TaskInvocationOrigin -> Prop)
    (Howned : caller_input before),
  kernel_program_returned_c_sequence_source environment critical sg observer stored_origin event_observer
    _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg observer stored_origin event_observer
    _ _ _ _ _ _ _ acquire ->
  (forall state heap input stopped result output_heap output actual source_origin result_origin,
    prefix_leaf state heap input stopped result output_heap output actual source_origin result_origin ->
    sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical.(critical_region_clients) sg observer event_observer source_origin state stopped result_origin result) ->
  (forall state heap input stopped result output_heap output actual source_origin result_origin,
    acquire_leaf state heap input stopped result output_heap output actual source_origin result_origin ->
    sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical.(critical_region_clients) sg observer event_observer source_origin state stopped result_origin result) ->
  sem_pend_c_sequence_call_certificate _ prefix_leaf _ _ _ _ _ _ _ prefix first prefix_origin ->
  sem_pend_c_sequence_call_certificate _ acquire_leaf _ _ _ _ _ _ _ acquire prefix_origin acquired_origin ->
  exists (open_input : caller_input |-- entry_input) (close_output : returned_output |-- caller_output),
  let actual := KernelCSequenceAdapt segment initial before caller_input entry_input
    (orb prefix_stop (orb acquire_stop false)) current after returned_output caller_output
    Howned open_input raw close_output in
  kernel_program_environment_c_sequence_source environment critical sg observer stored_origin event_observer
    _ _ _ _ _ _ _ actual /\
  sem_pend_c_sequence_call_certificate segment observed_leaf _ _ _ _ _ _ _ actual first
    (RunningInvocation suspended.(armv7a_continuation_stack).(stackLeaseSlot)
      suspended.(armv7a_continuation_stack).(stackLeaseGeneration)) /\
  caller_output after.
Proof.
  intros first prefix_origin acquired_origin prefix_leaf acquire_leaf Howned
    Hprefix_source Hacquire_source Hprefix_decode Hacquire_decode Hprefix_calls Hacquire_calls.
  destruct sem_pend_irq_caller_local_bridges as [Hopen Hclose].
  destruct (sem_pend_irq_first_level_c_call_certificate environment critical sg observer stored_origin event_observer
    initial entry_node handler suspended publication (kernel_irq_fields_local local suspended receipt)
    (unmap_table_rep sg ** private_frame) before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local receipt original node private_frame middle after
    Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge Hreturned
    first prefix_origin acquired_origin prefix_leaf acquire_leaf
    Hprefix_source Hacquire_source Hprefix_decode Hacquire_decode Hprefix_calls Hacquire_calls)
    as [Hsource [Hcalls [Hinput Houtput]]].
  exists Hopen, Hclose; cbn zeta.
  split.
  - apply KernelCSourceAdapt, KernelCSourceAtom; exact Hsource.
  - split.
    + apply SemPendCSequenceCallAdapt; exact Hcalls.
    + apply Hclose; exact Houtput.
Qed.
End SemPendIRQCallerLocal.
