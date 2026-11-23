Require Import Coq.ZArith.ZArith Coq.Bool.Bool.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_local_return_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_environment_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_wrapper_completion_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_returned_c_segment_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_control_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_envelope_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_completion_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_irq_completion_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_irq_entry_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Import UCOS2_C_Rules TaskStateDef.
Import SelectedReturnedCProgram SelectedReturnedCSource SelectedIRQWrapperCompletion OSIntExitReturnedC.
Import OSIntExitCCallControl OSIntExitCCallEnvelope OSIntExitCCallCompletion.
Import ReturnedIRQCallSource SelectedEnvironmentCProgram SelectedEnvironmentCSource.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_irq_local_connection_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_module_assembly_spec.

Lemma sem_pend_irq_whole_module_source :
  forall environment critical sg observer stored_origin event_observer
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    (prefix : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer stored_origin)
      (sem_pend_irq_entry_state initial handler suspended)
      body_heap body_input prefix_stop observed read_heap prefix_output)
    (acquire : kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer stored_origin)
      observed read_heap read_input acquire_stop entry acquired_heap acquire_output)
    observation_frame local receipt original node frame middle after
    (Hentry : os_int_exit_first_level_entry_c_completion environment sg initial entry_node handler suspended
      publication entry_local entry_frame before saved_heap body_heap)
    (Hentry_bridge : os_int_exit_first_level_entry_output environment sg initial handler suspended entry_local entry_frame |-- body_input)
    (Hprefix_control : kernel_returned_c_body_sequence_source environment critical sg observer stored_origin _ _ _ _ _ _ _ prefix)
    (Hread_bridge : prefix_output |-- read_input)
    (Hacquire_control : kernel_returned_c_body_sequence_source environment critical sg observer stored_origin _ _ _ _ _ _ _ acquire)
    (Hreturn_bridge : acquire_output |-- os_int_exit_returned_c_input environment sg entry local suspended receipt handler frame)
    (Hreturned : os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
      entry local suspended receipt original node handler frame acquired_heap middle after)
    first prefix_origin acquired_origin,
  kernel_program_returned_c_sequence_source environment critical sg observer stored_origin event_observer
    _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg observer stored_origin event_observer
    _ _ _ _ _ _ _ acquire ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer event_observer
    first (sem_pend_irq_entry_state initial handler suspended) prefix_stop prefix_origin observed ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer event_observer
    prefix_origin observed acquire_stop acquired_origin entry ->
  let completed := @OSIntExitFirstLevelCStep environment critical sg observer stored_origin
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local receipt original node frame middle after
    Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge Hreturned in
  let step := @KernelProgramEnvironmentIRQCall environment critical sg observer stored_origin
    _ _ _ _ _ _ _ completed in
  let run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step in
  kernel_program_environment_c_step_source environment critical sg observer stored_origin event_observer
    _ _ _ _ _ _ _ step /\
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer event_observer
    first initial (orb prefix_stop (orb acquire_stop false))
    (RunningInvocation suspended.(armv7a_continuation_stack).(stackLeaseSlot)
      suspended.(armv7a_continuation_stack).(stackLeaseGeneration))
    (os_int_exit_wrapper_restored_state (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
      suspended.(armv7a_continuation_stack)) /\
  os_int_exit_first_level_entry_input environment sg initial handler suspended entry_local entry_frame before /\
  irq_wrapper_c_output environment sg
    (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
    local suspended receipt original handler (unmap_table_rep sg ** frame) after.
Proof.
  intros environment critical sg observer stored_origin event_observer
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local receipt original node frame middle after
    Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge Hreturned
    first prefix_origin acquired_origin
    Hprefix_source Hacquire_source Hprefix_trace Hacquire_trace.
  assert (Htrace : sem_pend_observed_client_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg observer event_observer
    first initial (orb prefix_stop (orb acquire_stop false))
    (RunningInvocation suspended.(armv7a_continuation_stack).(stackLeaseSlot)
      suspended.(armv7a_continuation_stack).(stackLeaseGeneration))
    (os_int_exit_wrapper_restored_state (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
      suspended.(armv7a_continuation_stack))).
  { change (orb prefix_stop (orb acquire_stop false)) with
      (orb false (orb prefix_stop (orb acquire_stop false))).
    eapply SemPendObservedThen with (stopped1 := false)
      (stopped2 := orb prefix_stop (orb acquire_stop false)).
    - eapply SemPendObservedIRQEntry with (environment := environment);
        [reflexivity|reflexivity|exact Hentry].
    - eapply SemPendObservedThen with (stopped1 := prefix_stop)
        (stopped2 := orb acquire_stop false); [exact Hprefix_trace|].
      eapply SemPendObservedThen with (stopped1 := acquire_stop) (stopped2 := false);
        [exact Hacquire_trace|].
      eapply SemPendObservedIRQ with (environment := environment) (critical := critical);
        [reflexivity|reflexivity|reflexivity|].
      eapply SemPendIRQReturnedCompletion; exact Hreturned. }
  cbn zeta; split.
  - apply KernelProgramEnvironmentIRQCallSource.
    econstructor; [exact Hprefix_source|exact Hacquire_source].
  - split.
    + exact Htrace.
    + exact (os_int_exit_first_level_c_step_resources environment critical sg observer stored_origin
        _ _ _ _ _ _ _
        (@OSIntExitFirstLevelCStep environment critical sg observer stored_origin
          initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
          body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
          prefix acquire observation_frame local receipt original node frame middle after
          Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge Hreturned)).
Qed.

Section SemPendIRQModuleAssembly.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (observer : nat) (stored_origin : TaskInvocationOrigin)
.
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


(** Both inner runs are the original runs in the C completion. Their whole
    observations may include a stable Delete body; no per-cut certificate
    is requested. The existing local bridge is instantiated, not assumed. *)
Lemma sem_pend_irq_caller_local_module_run :
  forall first prefix_origin acquired_origin (Howned : caller_input before),
  kernel_program_returned_c_sequence_source environment critical sg observer stored_origin None
    _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg observer stored_origin None
    _ _ _ _ _ _ _ acquire ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer None
    first (sem_pend_irq_entry_state initial handler suspended) prefix_stop prefix_origin observed ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer None
    prefix_origin observed acquire_stop acquired_origin entry ->
  exists (open_input : caller_input |-- entry_input) (close_output : returned_output |-- caller_output),
  let actual := KernelCSequenceAdapt segment initial before caller_input entry_input
    (orb prefix_stop (orb acquire_stop false)) current after returned_output caller_output
    Howned open_input raw close_output in
  sem_pend_client_module_run environment critical sg observer stored_origin
    _ _ _ _ _ _ _ actual first
    (RunningInvocation suspended.(armv7a_continuation_stack).(stackLeaseSlot)
      suspended.(armv7a_continuation_stack).(stackLeaseGeneration)) /\
  caller_output after.
Proof.
  intros first prefix_origin acquired_origin Howned Hprefix_source Hacquire_source Hprefix_trace Hacquire_trace.
  assert (Hbridges : (caller_input |-- entry_input) /\ (returned_output |-- caller_output)).
  { eapply sem_pend_irq_caller_local_bridges; eassumption. }
  destruct Hbridges as [Hopen Hclose].
  destruct (sem_pend_irq_whole_module_source environment critical sg observer stored_origin None
    initial entry_node handler suspended publication (kernel_irq_fields_local local suspended receipt)
    (unmap_table_rep sg ** private_frame) before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local receipt original node private_frame middle after
    Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge Hreturned
    first prefix_origin acquired_origin Hprefix_source Hacquire_source Hprefix_trace Hacquire_trace)
    as [Hsource [Htrace [Hinput Houtput]]].
  exists Hopen, Hclose; cbn zeta.
  split.
  - split; [apply KernelCSourceAdapt, KernelCSourceAtom; exact Hsource|exact Htrace].
  - apply Hclose; exact Houtput.
Qed.
End SemPendIRQModuleAssembly.
