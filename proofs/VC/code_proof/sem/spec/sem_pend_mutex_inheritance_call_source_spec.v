Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_c_segment_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The existing complete inheritance segment owns both concrete heaps.
    Its original source is the receipt for this same literal C atom. *)
Lemma sem_pend_mutex_inheritance_call_certificate :
  forall environment critical local sg observer stored_origin origin frame call before after
    (segment : PendComponent.mutex_pend_inheritance_c_segment environment critical local sg frame call before after),
  let step := @KernelProgramCMutexPend environment critical sg observer stored_origin
    local frame call before after segment in
  let run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step in
  sem_pend_c_sequence_call_certificate _
    (fun state heap input stopped current output_heap output actual first last =>
      sem_pend_program_c_step_receipt environment critical sg observer stored_origin
        state heap input stopped current output_heap output actual /\
      sem_pend_observed_client_trace environment.(task_stack_call_external)
        environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
        first state stopped last current)
    _ _ _ _ _ _ _ run origin origin /\
  (PendComponent.mutex_pend_inheritance_c_owner environment critical local sg call
    call.(PendComponent.mutex_pend_inheritance_returned) ** frame) after.
Proof.
  intros environment critical local sg observer stored_origin origin frame call before after segment step run.
  split.
  - apply SemPendCSequenceCallAtom; split; [constructor|].
    eapply SemPendObservedMutexInheritance; try reflexivity; exact segment.
  - exact (PendComponent.mutex_pend_inheritance_segment_output _ _ _ _ _ _ _ _ segment).
Qed.

(** The actual busy-branch post, including its no-Mutex caller fact,
    supplies owner/current distinction. No observation or desired Sem
    endpoint is an input to this factory. *)
Lemma sem_pend_mutex_inheritance_busy_call_certificate :
  forall environment critical local sg observer stored_origin origin frame call before after eid event mutex current,
  call.(PendComponent.mutex_pend_inheritance_entry).(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some call.(PendComponent.mutex_pend_inheritance_owner) ->
  call.(PendComponent.mutex_pend_inheritance_entry).(SchedState).(curTaskID) = Some current ->
  task_holds_no_mutex call.(PendComponent.mutex_pend_inheritance_entry).(EventState) current ->
  call.(PendComponent.mutex_pend_inheritance_entry).(TskState).(inUsedTaskStates)
    call.(PendComponent.mutex_pend_inheritance_owner) = Some call.(PendComponent.mutex_pend_inheritance_node) ->
  (PendComponent.mutex_pend_inheritance_c_owner environment critical local sg call
    call.(PendComponent.mutex_pend_inheritance_entry) ** frame) before ->
  (coq_prop (mutex_pend_inherit_step sg call.(PendComponent.mutex_pend_inheritance_entry)
      call.(PendComponent.mutex_pend_inheritance_owner) call.(PendComponent.mutex_pend_inheritance_node)
      call.(PendComponent.mutex_pend_inheritance_base) call.(PendComponent.mutex_pend_inheritance_waiter)
      call.(PendComponent.mutex_pend_inheritance_ceiling) call.(PendComponent.mutex_pend_inheritance_returned)) &&
    (PendComponent.mutex_pend_inheritance_c_owner environment critical local sg call
      call.(PendComponent.mutex_pend_inheritance_returned) ** frame)) after ->
  exists segment : PendComponent.mutex_pend_inheritance_c_segment environment critical local sg frame call before after,
    let step := @KernelProgramCMutexPend environment critical sg observer stored_origin
      local frame call before after segment in
    let run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step in
    sem_pend_c_sequence_call_certificate _
      (fun state heap input stopped current_state output_heap output actual first last =>
        sem_pend_program_c_step_receipt environment critical sg observer stored_origin
          state heap input stopped current_state output_heap output actual /\
        sem_pend_observed_client_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
          first state stopped last current_state)
      _ _ _ _ _ _ _ run origin origin /\
    (PendComponent.mutex_pend_inheritance_c_owner environment critical local sg call
      call.(PendComponent.mutex_pend_inheritance_returned) ** frame) after.
Proof.
  intros environment critical local sg observer stored_origin origin frame call before after eid event mutex current
    Hlookup Htype Hmutex Howner Hcurrent Hholds Hnode Hpre Hpost.
  pose (segment := PendComponent.mutex_pend_inheritance_busy_c_post_segment
    environment critical local sg frame call before after eid event mutex current
    Hlookup Htype Hmutex Howner Hcurrent Hholds Hnode Hpre Hpost).
  exists segment; apply sem_pend_mutex_inheritance_call_certificate.
Qed.
