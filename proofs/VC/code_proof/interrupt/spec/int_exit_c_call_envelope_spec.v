Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_control_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_program_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_wrapper_completion_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_returned_c_segment_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_return_view_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_api_entry_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module OSIntExitCCallEnvelope.
Import SelectedReturnedCProgram SelectedIRQWrapperCompletion OSIntExitReturnedC
  OSIntExitReturnView OSIntExitCCallControl.

Definition os_int_exit_first_level_entry_input environment sg initial handler suspended
  (local : Armv7aContinuation -> Assertion) (frame : Assertion) : Assertion :=
  os_int_exit_frame_save_pre environment.(task_stack_call_external)
    environment.(task_stack_call_platform) handler **
  (UCOS2_fields_inv sg initial **
    store_parked_continuations
      (kernel_saved_continuation_entry environment.(task_stack_call_continuations) initial.(TskState) local)
      initial.(TskState).(parkedTaskStacks) ** local suspended ** frame).

Definition os_int_exit_first_level_entry_output environment sg initial handler suspended
  (local : Armv7aContinuation -> Assertion) (frame : Assertion) : Assertion :=
  let parked := armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
    suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments) in
  UCOS2_fields_inv sg parked **
  store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations) parked.(TskState) local)
    parked.(TskState).(parkedTaskStacks) **
  (interrupt_platform_running environment.(task_stack_call_platform)
     handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
   os_int_exit_context_resources environment.(task_stack_call_port) handler ** frame).

(** Exactly the existing first-level C/ABI entry premises. Both physical
    executions and their shared saved_heap are retained. No postcondition
    or future return property is a field of this entry observation. *)
Record os_int_exit_first_level_entry_c_completion environment sg initial node handler suspended
  publication local frame before saved_heap body_heap : Prop := {
  os_int_exit_entry_frame_slice : armv7a_task_frame_slice suspended;
  os_int_exit_entry_running : initial.(SchedState).(isRunning) = true;
  os_int_exit_entry_zero : initial.(IntrState).(intNesting) = 0;
  os_int_exit_entry_current : initial.(SchedState).(curTaskID) =
    Some handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot);
  os_int_exit_entry_node : initial.(TskState).(inUsedTaskStates)
    handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot) = Some node;
  os_int_exit_entry_node_id : node.(taskID) =
    handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot);
  os_int_exit_entry_node_generation : node.(taskGeneration) =
    handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseGeneration);
  os_int_exit_entry_not_parked : initial.(TskState).(parkedTaskStacks)
    (task_stack_key handler.(os_int_exit_interrupted_call).(os_sched_call_stack)) = None;
  os_int_exit_entry_stack_address :
    tcb_field_address (task_slot_addr sg handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot);
  os_int_exit_entry_region : valid_task_stack_region
    handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseRegion);
  os_int_exit_entry_geometry : task_stack_fragments_in_range
    handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords)
    0 suspended.(armv7a_continuation_fragments);
  os_int_exit_entry_publication : task_publication_happened initial.(TskState) publication
    handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot)
    handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseGeneration);
  os_int_exit_entry_sp : task_stack_saved_pointer_in_range
    handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseRegion)
    suspended.(armv7a_continuation_sp);
  os_int_exit_entry_coverage : task_stack_live_coverage initial.(TskState)
    (Some (task_stack_key handler.(os_int_exit_interrupted_call).(os_sched_call_stack)));
  os_int_exit_entry_owned :
    os_int_exit_first_level_entry_input environment sg initial handler suspended local frame before;
  os_int_exit_entry_actual_save : armv7a_save_transition environment.(task_stack_call_continuations)
    handler suspended before saved_heap;
  os_int_exit_entry_actual_writes : kernel_heap_execution
    (armv7a_irq_live_entry_writes sg initial
      handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot)
      suspended.(armv7a_continuation_sp)) saved_heap body_heap
}.

Lemma os_int_exit_first_level_entry_c_resources :
  forall environment sg initial node handler suspended publication local frame before saved_heap body_heap,
  os_int_exit_first_level_entry_c_completion environment sg initial node handler suspended
    publication local frame before saved_heap body_heap ->
  os_int_exit_first_level_entry_input environment sg initial handler suspended local frame before /\
  os_int_exit_first_level_entry_output environment sg initial handler suspended local frame body_heap.
Proof.
  intros until body_heap; intro Hentry.
  destruct Hentry as [Hslice Hrunning Hzero Hcurrent Hnode Hid Hgen Hnone Haddress
    Hregion Hgeometry Hpublication Hsp Hcoverage Howned Hsave Hwrites].
  split; [exact Howned|].
  destruct (flag_irq_entry_fields_source _ _ _ environment.(task_stack_call_continuations)
    sg initial node handler suspended publication local frame before saved_heap
    Hslice Hrunning Hzero Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp Hcoverage Howned Hsave) as [actual_heap Hactual].
  destruct Hactual as [Hbinding [Hstack [Hparked [Hcall [Hpc [Hmask [Hmemory [Hexecution [Hcover Houtput]]]]]]]]].
  pose proof (kernel_heap_execution_deterministic _ _ _ _ Hexecution Hwrites) as Hequal.
  subst actual_heap; exact Houtput.
Qed.

Lemma os_int_exit_first_level_entry_task_fields :
  forall environment sg initial node handler suspended publication local frame before saved_heap body_heap,
  os_int_exit_first_level_entry_c_completion environment sg initial node handler suspended
    publication local frame before saved_heap body_heap ->
  (armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
    suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments)).(TskState) =
  glob_task_set_parked_stacks
    (glob_task_set_usedtask initial.(TskState)
      handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot)
      (task_set_saved_sp node suspended.(armv7a_continuation_sp)))
    (task_stack_park_fragments initial.(TskState).(parkedTaskStacks)
      handler.(os_int_exit_interrupted_call).(os_sched_call_stack)
      suspended.(armv7a_continuation_fragments)).
Proof.
  intros until body_heap; intro Hentry.
  pose proof (os_int_exit_entry_running _ _ _ _ _ _ _ _ _ _ _ _ Hentry) as Hr.
  pose proof (os_int_exit_entry_node _ _ _ _ _ _ _ _ _ _ _ _ Hentry) as Hnode.
  unfold armv7a_irq_live_parked_state, armv7a_irq_live_entry_state, armv7a_irq_entry_counter_state.
  rewrite Hr; unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity.
Qed.

Section ActualIRQCall.
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
Let final := os_int_exit_wrapper_restored_state
  (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
  suspended.(armv7a_continuation_stack).
Let output := irq_wrapper_c_output environment sg
  (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
  local suspended receipt original handler (unmap_table_rep sg ** frame).

(** This is a complete C call source. The physical entry is explicitly
    outside the old Returned run; the body keeps its original Hrun. *)
Record os_int_exit_first_level_c_call : Prop := {
  os_int_exit_call_actual_entry : os_int_exit_first_level_entry_c_completion environment sg
    initial entry_node handler suspended publication entry_local entry_frame before saved_heap body_heap;
  os_int_exit_call_entry_bridge : os_int_exit_first_level_entry_output environment sg
    initial handler suspended entry_local entry_frame |-- body_input;
  os_int_exit_call_prefix_source : kernel_returned_c_body_sequence_source environment critical sg observer origin
    _ _ _ _ _ _ _ prefix;
  os_int_exit_call_read_bridge : prefix_output |-- read_input;
  os_int_exit_call_acquire_source : kernel_returned_c_body_sequence_source environment critical sg observer origin
    _ _ _ _ _ _ _ acquire;
  os_int_exit_call_return_bridge : acquire_output |--
    os_int_exit_returned_c_input environment sg entry local suspended receipt handler frame
}.

Definition os_int_exit_first_level_c_tail (call : os_int_exit_first_level_c_call) :
  kernel_c_sequence (kernel_program_returned_c_step environment critical sg observer origin)
    parked body_heap
    (os_int_exit_first_level_entry_output environment sg initial handler suspended entry_local entry_frame)
    (orb prefix_stop (orb acquire_stop false)) final after output.
Proof.
  eapply KernelCSequenceAdapt.
  - exact (proj2 (os_int_exit_first_level_entry_c_resources _ _ _ _ _ _ _ _ _ _ _ _
      (os_int_exit_call_actual_entry call))).
  - exact (os_int_exit_call_entry_bridge call).
  - eapply KernelCSequenceThen.
    + exact prefix.
    + exact (os_int_exit_call_read_bridge call).
    + eapply KernelCSequenceThen.
      * exact acquire.
      * exact (os_int_exit_call_return_bridge call).
      * apply KernelCSequenceAtom, KernelProgramReturnedExit.
        exact (@OSIntExitReturnedCStep environment critical sg observed read_heap observation_frame
          entry local suspended receipt original node handler frame acquired_heap middle after returned).
  - intros heap Howned; exact Howned.
Defined.

Lemma os_int_exit_first_level_c_call_resources : forall call : os_int_exit_first_level_c_call,
  os_int_exit_first_level_entry_input environment sg initial handler suspended entry_local entry_frame before /\
  output after.
Proof.
  intro call; split.
  - exact (proj1 (os_int_exit_first_level_entry_c_resources _ _ _ _ _ _ _ _ _ _ _ _
      (os_int_exit_call_actual_entry call))).
  - exact (proj2 (kernel_program_returned_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _
      (os_int_exit_first_level_c_tail call))).
Qed.

Lemma os_int_exit_first_level_c_call_control : forall call : os_int_exit_first_level_c_call,
  kernel_call_control_rely sg initial final.
Proof.
  intro call.
  pose proof (os_int_exit_call_actual_entry call) as Hentry.
  eapply os_int_exit_first_level_returned_control.
  - exact (os_int_exit_call_prefix_source call).
  - exact (os_int_exit_call_acquire_source call).
  - exact (os_int_exit_entry_running _ _ _ _ _ _ _ _ _ _ _ _ Hentry).
  - exact (os_int_exit_entry_zero _ _ _ _ _ _ _ _ _ _ _ _ Hentry).
  - exact returned.
  - exact (os_int_exit_entry_actual_save _ _ _ _ _ _ _ _ _ _ _ _ Hentry).
Qed.

Lemma os_int_exit_first_level_c_call_original : forall call : os_int_exit_first_level_c_call,
  original = handler.(os_int_exit_interrupted_call).
Proof.
  intro call.
  eapply os_int_exit_returned_c_completion_interrupted_call.
  - exact returned.
  - exact (os_int_exit_entry_actual_save _ _ _ _ _ _ _ _ _ _ _ _
      (os_int_exit_call_actual_entry call)).
Qed.
End ActualIRQCall.

End OSIntExitCCallEnvelope.
