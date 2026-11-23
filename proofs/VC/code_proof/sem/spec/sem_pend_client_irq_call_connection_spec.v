Require Import Coq.ZArith.ZArith Coq.Bool.Bool.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
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

(** The entry and return are existing whole C-module completions. The two
    certificates are indexed by the actual prefix/acquire runs stored in the
    original complete-call constructor. The acquired tail is never rebound
    to the initial state, and its input/output heaps remain unchanged. *)
Lemma sem_pend_irq_first_level_c_call_certificate :
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
    first prefix_origin acquired_origin
    (prefix_leaf : forall state heap input stopped result output_heap output,
      kernel_program_returned_c_step environment critical sg observer stored_origin
        state heap input stopped result output_heap output -> TaskInvocationOrigin -> TaskInvocationOrigin -> Prop)
    (acquire_leaf : forall state heap input stopped result output_heap output,
      kernel_program_returned_c_step environment critical sg observer stored_origin
        state heap input stopped result output_heap output -> TaskInvocationOrigin -> TaskInvocationOrigin -> Prop),
  kernel_program_returned_c_sequence_source environment critical sg observer stored_origin event_observer
    _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg observer stored_origin event_observer
    _ _ _ _ _ _ _ acquire ->
  (forall state heap input stopped result output_heap output step source_origin result_origin,
    prefix_leaf state heap input stopped result output_heap output step source_origin result_origin ->
    sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical.(critical_region_clients) sg observer event_observer source_origin state stopped result_origin result) ->
  (forall state heap input stopped result output_heap output step source_origin result_origin,
    acquire_leaf state heap input stopped result output_heap output step source_origin result_origin ->
    sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical.(critical_region_clients) sg observer event_observer source_origin state stopped result_origin result) ->
  sem_pend_c_sequence_call_certificate _ prefix_leaf _ _ _ _ _ _ _ prefix first prefix_origin ->
  sem_pend_c_sequence_call_certificate _ acquire_leaf _ _ _ _ _ _ _ acquire prefix_origin acquired_origin ->
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
  sem_pend_c_sequence_call_certificate _
    (fun state heap input stopped result output_heap output step source_origin result_origin =>
      sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
        critical.(critical_region_clients) sg observer event_observer source_origin state stopped result_origin result)
    _ _ _ _ _ _ _ run first
    (RunningInvocation suspended.(armv7a_continuation_stack).(stackLeaseSlot)
      suspended.(armv7a_continuation_stack).(stackLeaseGeneration)) /\
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
    first prefix_origin acquired_origin prefix_leaf acquire_leaf
    Hprefix_source Hacquire_source Hprefix_decode Hacquire_decode Hprefix_calls Hacquire_calls.
  assert (Hprefix_trace : sem_pend_observed_client_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg observer event_observer
    first (sem_pend_irq_entry_state initial handler suspended) prefix_stop prefix_origin observed).
  { eapply sem_pend_observed_c_sequence_trace; [exact Hprefix_decode|exact Hprefix_calls]. }
  assert (Hacquire_trace : sem_pend_observed_client_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg observer event_observer
    prefix_origin observed acquire_stop acquired_origin entry).
  { eapply sem_pend_observed_c_sequence_trace; [exact Hacquire_decode|exact Hacquire_calls]. }
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
    + apply SemPendCSequenceCallAtom; exact Htrace.
    + exact (os_int_exit_first_level_c_step_resources environment critical sg observer stored_origin
        _ _ _ _ _ _ _
        (@OSIntExitFirstLevelCStep environment critical sg observer stored_origin
          initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap
          body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
          prefix acquire observation_frame local receipt original node frame middle after
          Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge Hreturned)).
Qed.
