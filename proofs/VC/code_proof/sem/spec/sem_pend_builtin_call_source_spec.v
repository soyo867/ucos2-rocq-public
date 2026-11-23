Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_api_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_c_step_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_masked_c_step_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The selected Suspend atom is the existing protected completion itself.
    Its same-index receipt and observer trace are retained together with
    the exact masked output. No legacy/foreign Suspend guard is introduced. *)
Lemma sem_pend_masked_suspend_call_certificate :
  forall environment critical saved_local sg observer stored_origin origin caller saved call frame before after
    (completion : TaskSuspendMaskedC.task_suspend_masked_completion
      environment critical saved_local sg caller saved call frame before after),
  let primitive := TaskSuspendMaskedC.TaskSuspendMaskedCStep environment critical sg
    saved_local caller saved call frame before after completion in
  let step := @SelectedCProgram.KernelSelectedProgramSuspend critical sg observer stored_origin environment
    _ _ _ _ _ _ _ primitive in
  let run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step in
  sem_pend_c_sequence_call_certificate _
    (fun state heap input stopped current output_heap output actual first last =>
      sem_pend_selected_c_step_receipt environment critical sg observer stored_origin
        state heap input stopped current output_heap output actual /\
      sem_pend_observed_client_trace environment.(task_stack_call_external)
        environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
        first state stopped last current)
    _ _ _ _ _ _ _ run origin origin /\
  (task_suspend_masked environment critical saved_local sg caller saved
    call.(TaskSuspendActualC.suspend_actual_entry) call.(TaskSuspendActualC.suspend_actual_checkpoint) ** frame) after.
Proof.
  intros environment critical saved_local sg observer stored_origin origin caller saved call frame before after
    completion primitive step run.
  split.
  - apply SemPendCSequenceCallAtom; split; [constructor|].
    eapply SemPendObservedSuspend; try reflexivity; exact completion.
  - exact (TaskSuspendMaskedC.suspend_masked_output environment critical saved_local sg
      caller saved call frame before after completion).
Qed.

(** The install atom keeps the original Hactual and selected continuation.
    Its observation changes execution origin to that actual incoming stack;
    the returned installed owner is the segment's original output. *)
Lemma sem_pend_install_call_certificate :
  forall environment critical local sg observer stored_origin frame call before after sp Hactual
    (segment : InstallComponent.task_install_c_segment environment local sg frame call before after sp Hactual),
  let primitive := InstallComponent.TaskInstallCStep environment local sg frame call before after sp Hactual segment in
  let step := @KernelProgramCInstall environment critical sg observer stored_origin local _ _ _ _ _ _ _ primitive in
  let run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step in
  sem_pend_c_sequence_call_certificate _
    (fun state heap input stopped current output_heap output actual first last =>
      sem_pend_program_c_step_receipt environment critical sg observer stored_origin
        state heap input stopped current output_heap output actual /\
      sem_pend_observed_client_trace environment.(task_stack_call_external)
        environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
        first state stopped last current)
    _ _ _ _ _ _ _ run call.(InstallComponent.task_install_fields_context).(os_sched_call_origin)
      (RunningInvocation call.(InstallComponent.task_install_fields_incoming).(stackLeaseSlot)
        call.(InstallComponent.task_install_fields_incoming).(stackLeaseGeneration)) /\
  (InstallComponent.task_install_fields_installed_owner environment local sg call ** frame) after.
Proof.
  intros environment critical local sg observer stored_origin frame call before after sp Hactual segment primitive step run.
  split.
  - apply SemPendCSequenceCallAtom; split; [constructor|].
    eapply SemPendObservedInstall; try reflexivity; exact segment.
  - exact (proj2 (InstallComponent.task_install_c_segment_resources
      environment local sg frame call before after sp Hactual segment)).
Qed.
