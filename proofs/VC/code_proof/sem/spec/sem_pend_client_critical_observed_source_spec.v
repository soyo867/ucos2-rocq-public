Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.error_codes Ucos2Verify.lib.event.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_environment_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_selected_restore_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_critical_restore_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations CriticalComponent.
Import SelectedReturnPrimitive SelectedCompletionSource SelectedCProgram SelectedCSource.
Import SelectedIRQWrapperSegment SelectedIRQWrapperSource SelectedReturnedCProgram SelectedReturnedCSource.
Import SelectedEnvironmentCProgram SelectedEnvironmentCSource.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actor is the original call's actor even for a Generic handler whose
    numeric label collides with the observer. The narrow observer frames
    are proved from this exact step by the lower source interpreter. *)
Lemma sem_pend_critical_completion_observed_trace :
  forall environment critical local sg frame call before after observer origin,
  critical.(critical_region_clients) (sem_pend_critical_call_action call) ->
  kernel_critical_c_completion environment critical local sg frame call before after ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer None origin (kernel_critical_c_entry call)
    false origin (kernel_critical_c_returned call).
Proof.
  intros environment critical local sg frame call before after observer origin Hmember Hcompletion.
  destruct (sem_pend_critical_completion_observations _ _ _ _ _ _ _ _ Hcompletion)
    as [Hstep [Hparked Hcurrent]].
  assert (Htyped : sem_pend_framed_critical_client (sem_pend_critical_call_action call))
    by (destruct call; constructor).
  assert (Hstop : kernel_client_stops (sem_pend_critical_call_action call) observer = false)
    by (destruct call; reflexivity).
  rewrite <- Hstop.
  eapply SemPendObservedCritical.
  - exact Hmember.
  - exact Htyped.
  - intros invocation Hnone; discriminate.
  - exact Hstep.
  - eapply TaskExecutionClientFrame; eassumption.
  - apply TmrTaskCallCritical; [destruct call; constructor|exact Hstep].
Qed.

Section SemPendObservedCriticalCalls.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (observer : nat) (origin : TaskInvocationOrigin).
Let segment := kernel_program_c_step environment critical sg observer origin.

Inductive sem_pend_critical_observed_call_receipt :
  forall state before input stopped current after output,
  segment state before input stopped current after output -> TaskInvocationOrigin -> TaskInvocationOrigin -> Prop :=
| SemPendCriticalObservedCall : forall local frame call before after
    (completion : kernel_critical_c_completion environment critical local sg frame call before after) first,
    critical.(critical_region_clients) (sem_pend_critical_call_action call) ->
    sem_pend_critical_observed_call_receipt _ _ _ _ _ _ _
      (@KernelProgramCCritical environment critical sg observer origin local frame call before after
        (kernel_critical_c_completion_segment environment critical local sg frame call before after completion)) first first.

Lemma sem_pend_critical_call_receipt_observed_trace : forall state before input stopped current after output step first last,
  sem_pend_critical_observed_call_receipt state before input stopped current after output step first last ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer None first state stopped last current.
Proof.
  intros until last; intro Hreceipt; destruct Hreceipt.
  eapply sem_pend_critical_completion_observed_trace; eassumption.
Qed.

Lemma sem_pend_critical_observed_environment_source : forall state before input stopped current after output run first last,
  sem_pend_c_sequence_call_certificate segment sem_pend_critical_observed_call_receipt
    state before input stopped current after output run first last ->
  kernel_program_environment_c_sequence_source environment critical sg observer origin None _ _ _ _ _ _ _
    (sem_pend_selected_environment_sequence environment critical sg observer origin _ _ _ _ _ _ _ run).
Proof.
  intros until last; intro Hcertificate; induction Hcertificate;
    cbn [sem_pend_selected_environment_sequence sem_pend_selected_sequence
      kernel_program_environment_sequence_include kernel_program_returned_sequence_include
      kernel_program_wrapper_sequence_include].
  - constructor.
  - destruct H.
    apply KernelCSourceAtom, KernelProgramEnvironmentBodySource, KernelProgramReturnedWrapperSource,
      KernelProgramWrapperOriginalSource, KernelSelectedProgramReturnSource, KernelProgramReturnOriginalSource.
    right; constructor.
  - econstructor; eassumption.
  - econstructor; eassumption.
Qed.
End SemPendObservedCriticalCalls.

Definition sem_pend_critical_observed_call_result
  (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (local : Armv7aContinuation -> Assertion) (sg : StableGlobVars) (frame : Assertion)
  (call : KernelCriticalCCall) (before after : model) (observed : OsSchedCallContext) : Prop :=
  exists run : kernel_c_sequence (kernel_program_c_step environment critical sg
      observed.(os_sched_call_invocation) observed.(os_sched_call_origin))
    (kernel_critical_c_entry call) before
    (kernel_critical_c_owner environment critical local sg call (kernel_critical_c_entry call) ** frame)
    false (kernel_critical_c_returned call) after
    (kernel_critical_c_owner environment critical local sg call (kernel_critical_c_returned call) ** frame),
    sem_pend_c_sequence_call_certificate _
      (sem_pend_critical_observed_call_receipt environment critical sg observed.(os_sched_call_invocation) observed.(os_sched_call_origin))
      _ _ _ _ _ _ _ run observed.(os_sched_call_origin) observed.(os_sched_call_origin) /\
    let included := sem_pend_selected_environment_sequence environment critical sg
      observed.(os_sched_call_invocation) observed.(os_sched_call_origin) _ _ _ _ _ _ _ run in
    kernel_program_environment_c_sequence_source environment critical sg
      observed.(os_sched_call_invocation) observed.(os_sched_call_origin) None _ _ _ _ _ _ _ included /\
    sem_pend_c_sequence_call_certificate _
      (sem_pend_environment_call_receipt environment critical sg observed.(os_sched_call_invocation) observed.(os_sched_call_origin)
        (sem_pend_critical_observed_call_receipt environment critical sg observed.(os_sched_call_invocation) observed.(os_sched_call_origin)))
      _ _ _ _ _ _ _ included observed.(os_sched_call_origin) observed.(os_sched_call_origin) /\
    sem_pend_client_return_source environment critical sg observed (kernel_critical_c_entry call)
      observed (kernel_critical_c_returned call) /\
    (kernel_critical_c_owner environment critical local sg call (kernel_critical_c_returned call) ** frame) after.

Lemma sem_pend_critical_completion_observed_source :
  forall environment critical local sg frame call before after observed,
  critical.(critical_region_clients) (sem_pend_critical_call_action call) ->
  kernel_critical_c_completion environment critical local sg frame call before after ->
  sem_pend_critical_observed_call_result environment critical local sg frame call before after observed.
Proof.
  intros environment critical local sg frame call before after observed Hmember completion.
  pose (actual := kernel_critical_c_completion_segment environment critical local sg frame call before after completion).
  pose (step := @KernelProgramCCritical environment critical sg observed.(os_sched_call_invocation)
    observed.(os_sched_call_origin) local frame call before after actual).
  pose (run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step).
  assert (Hcertificate : sem_pend_c_sequence_call_certificate _
    (sem_pend_critical_observed_call_receipt environment critical sg observed.(os_sched_call_invocation) observed.(os_sched_call_origin))
    _ _ _ _ _ _ _ run observed.(os_sched_call_origin) observed.(os_sched_call_origin)).
  { unfold run, step, actual; apply SemPendCSequenceCallAtom, SemPendCriticalObservedCall; exact Hmember. }
  exists run; split; [exact Hcertificate|]. split.
  - eapply sem_pend_critical_observed_environment_source; exact Hcertificate.
  - split.
    + apply sem_pend_selected_environment_sequence_certificate; exact Hcertificate.
    + split.
      * split.
        -- eapply sem_pend_critical_completion_observed_trace; eassumption.
        -- eapply sem_pend_critical_completion_normal_return; exact completion.
      * exact (proj2 (kernel_critical_c_segment_resources _ _ _ _ _ _ _ _ actual)).
Qed.

(** Actual C post factories retain all original execution-view alternatives
    and return codes. Registration is the actual caller's existing fact;
    no arbitrary public region is identified with a literal extension. *)
Lemma sem_pend_change_prio_post_observed_source :
  forall environment critical local sg frame actual observed before after,
  critical.(critical_region_clients) (sem_pend_critical_call_action (KernelCriticalChangePrio actual)) ->
  task_change_prio_critical_call_guard sg actual.(change_prio_fields_requested)
    actual.(change_prio_fields_priority) actual.(change_prio_fields_entry) ->
  (task_change_prio_fields_owner environment critical local sg actual actual.(change_prio_fields_entry) ** frame) before ->
  (coq_prop (task_change_prio_critical_code sg actual.(change_prio_fields_requested)
      actual.(change_prio_fields_priority) actual.(change_prio_fields_entry)
      actual.(change_prio_fields_result) actual.(change_prio_fields_released)) &&
    (task_change_prio_fields_owner environment critical local sg actual actual.(change_prio_fields_released) ** frame)) after ->
  sem_pend_critical_observed_call_result environment critical local sg frame
    (KernelCriticalChangePrio actual) before after observed.
Proof.
  intros environment critical local sg frame actual observed before after Hmember Hguard Hpre Hpost.
  apply sem_pend_critical_completion_observed_source; [exact Hmember|].
  exact (task_change_prio_fields_completion_from_c_post environment critical local frame sg actual
    before after Hguard Hpre Hpost).
Qed.

Lemma sem_pend_mutex_del_post_observed_source :
  forall environment critical local sg frame actual event mutex observed before after,
  let call := actual.(mutex_del_critical_fields_base) in
  critical.(critical_region_clients) (sem_pend_critical_call_action (KernelCriticalMutexDel actual)) ->
  mutex_del_parent_layout sg ->
  mutex_del_parent_entry sg call.(mutex_del_fields_eid) call.(mutex_del_fields_entry) event mutex ->
  (mutex_del_fields_owner environment critical local sg call call.(mutex_del_fields_entry) ** frame) before ->
  (coq_prop (mutex_del_parent_critical_observation sg call.(mutex_del_fields_eid)
      actual.(mutex_del_critical_fields_option) call.(mutex_del_fields_result) call.(mutex_del_fields_code)
      call.(mutex_del_fields_request) call.(mutex_del_fields_entry) call.(mutex_del_fields_checkpoint)) &&
    (mutex_del_fields_owner environment critical local sg call call.(mutex_del_fields_checkpoint) ** frame)) after ->
  sem_pend_critical_observed_call_result environment critical local sg frame
    (KernelCriticalMutexDel actual) before after observed.
Proof.
  intros environment critical local sg frame actual event mutex observed before after call Hmember Hlayout Hentry Hpre Hpost.
  apply sem_pend_critical_completion_observed_source; [exact Hmember|].
  exact (mutex_del_critical_fields_completion_from_c_post environment critical local frame sg actual
    event mutex before after Hlayout Hentry Hpre Hpost).
Qed.

Lemma sem_pend_mutex_del_type_error_observed_source :
  forall environment critical local sg frame call option kind observed before after,
  let actual := mutex_del_critical_fields_result call option (event_addr sg call.(mutex_del_fields_eid))
    (encode_os_err_code OS_ERR_EVENT_TYPE) 0 call.(mutex_del_fields_entry) in
  critical.(critical_region_clients) (sem_pend_critical_call_action (KernelCriticalMutexDel actual)) ->
  (mutex_del_fields_owner environment critical local sg call call.(mutex_del_fields_entry) ** frame) before ->
  (coq_prop (mutex_del_runtime_type_observation sg call.(mutex_del_fields_eid)
      call.(mutex_del_fields_entry) kind /\ kind <> 4) &&
    (mutex_del_fields_owner environment critical local sg call call.(mutex_del_fields_entry) ** frame)) after ->
  sem_pend_critical_observed_call_result environment critical local sg frame
    (KernelCriticalMutexDel actual) before after observed.
Proof.
  intros environment critical local sg frame call option kind observed before after actual Hmember Hpre Hpost.
  apply sem_pend_critical_completion_observed_source; [exact Hmember|].
  exact (mutex_del_critical_fields_type_error_from_c_post environment critical local frame sg call
    option kind before after Hpre Hpost).
Qed.
