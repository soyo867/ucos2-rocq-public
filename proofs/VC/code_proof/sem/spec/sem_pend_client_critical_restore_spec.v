Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
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
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_api_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_c_segment_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_selected_restore_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_receipt_producer_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations CriticalComponent.
Import SelectedReturnPrimitive SelectedCompletionSource SelectedCProgram SelectedCSource.
Import SelectedIRQWrapperSegment SelectedIRQWrapperSource SelectedReturnedCProgram SelectedReturnedCSource.
Import SelectedEnvironmentCProgram SelectedEnvironmentCSource.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The action names the actual execution descriptor's invocation. This
    does not replace a caller by None to manufacture a foreign action. *)
Definition sem_pend_critical_call_action (call : KernelCriticalCCall) : KernelClientAction :=
  match call with
  | KernelCriticalChangePrio actual =>
      task_change_prio_critical_call_client
        (Some (task_change_prio_view actual.(change_prio_fields_execution)).(os_execution_invocation))
        actual.(change_prio_fields_requested) actual.(change_prio_fields_priority)
  | KernelCriticalMutexDel actual =>
      mutex_del_critical_call_client (mutex_del_fields_actor actual.(mutex_del_critical_fields_base))
        actual.(mutex_del_critical_fields_base).(mutex_del_fields_eid) actual.(mutex_del_critical_fields_option)
  end.

Lemma sem_pend_change_prio_parked_stacks : forall sg requested priority before error after,
  task_change_prio_critical sg requested priority before error after ->
  after.(TskState).(parkedTaskStacks) = before.(TskState).(parkedTaskStacks).
Proof.
  intros sg requested priority before error after Hcritical.
  unfold task_change_prio_critical in Hcritical.
  destruct (before.(TskState).(prioTbl) priority).
  - destruct Hcritical as [selected [Hselected Hcritical]].
    unfold task_change_prio_selected_effect in Hcritical.
    destruct (Z.eqb selected sg.(osLowestPrio)).
    + destruct Hcritical as [_ ->]; reflexivity.
    + destruct (before.(TskState).(prioTbl) selected).
      * destruct Hcritical as [_ ->]; reflexivity.
      * destruct Hcritical as [_ ->]; reflexivity.
      * destruct Hcritical as [node [Hnode [_ ->]]]; reflexivity.
  - destruct Hcritical as [_ ->]; reflexivity.
  - destruct Hcritical as [_ ->]; reflexivity.
Qed.

(** Every original ChangePrio result and both MutexDel observation
    constructors remain covered. Output ownership stays in the same C
    completion; the registered-action facts are derived from its source. *)
Lemma sem_pend_critical_completion_observations :
  forall environment critical local sg frame call before after,
  kernel_critical_c_completion environment critical local sg frame call before after ->
  kernel_client_step (sem_pend_critical_call_action call) sg
    (kernel_critical_c_entry call) (kernel_critical_c_returned call) /\
  (kernel_critical_c_returned call).(TskState).(parkedTaskStacks) =
    (kernel_critical_c_entry call).(TskState).(parkedTaskStacks) /\
  (kernel_critical_c_entry call).(SchedState).(curTaskID) =
    (kernel_critical_c_returned call).(SchedState).(curTaskID).
Proof.
  intros environment critical local sg frame [call|call] before after Hcompletion;
    cbn [kernel_critical_c_completion] in Hcompletion;
    cbn [sem_pend_critical_call_action kernel_critical_c_entry kernel_critical_c_returned].
  - destruct Hcompletion as [Hguard [error [Hcritical Hcode]] Hpre Hpost].
    split.
    + split; [exact Hguard|exists error; exact Hcritical].
    + split.
      * eapply sem_pend_change_prio_parked_stacks; exact Hcritical.
      * symmetry; exact (proj1 (task_change_prio_critical_current_timer_frame _ _ _ _ _ _ Hcritical)).
  - destruct Hcompletion as [Hobservation Hpre Hpost].
    pose proof (mutex_del_critical_call_observation_fields _ _ _ _ _ _ _ _ Hobservation)
      as [[Hnodes [Hparked [Hlife [Hcurrent Hprivate]]]] Hframes].
    split.
    + exists call.(mutex_del_critical_fields_base).(mutex_del_fields_result),
        call.(mutex_del_critical_fields_base).(mutex_del_fields_code),
        call.(mutex_del_critical_fields_base).(mutex_del_fields_request); exact Hobservation.
    + split; [exact Hparked|symmetry; exact Hcurrent].
Qed.

Lemma sem_pend_critical_completion_normal_return :
  forall environment critical local sg frame call before after observed,
  kernel_critical_c_completion environment critical local sg frame call before after ->
  kernel_call_normal_return observed (kernel_critical_c_entry call)
    observed (kernel_critical_c_returned call).
Proof.
  intros environment critical local sg frame call before after observed Hcompletion.
  destruct (sem_pend_critical_completion_observations _ _ _ _ _ _ _ _ Hcompletion)
    as [_ [Hparked Hcurrent]].
  split; [unfold task_tcb_init_stack_same_call; auto|].
  unfold kernel_call_stack_available; rewrite Hparked; auto.
Qed.

Lemma sem_pend_critical_completion_client_calls :
  forall environment critical local sg frame call before after observer origin,
  critical.(critical_region_clients) (sem_pend_critical_call_action call) ->
  kernel_client_actor (sem_pend_critical_call_action call) <> Some observer ->
  kernel_critical_c_completion environment critical local sg frame call before after ->
  exists trace : kernel_client_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
      origin (kernel_critical_c_entry call) false origin (kernel_critical_c_returned call),
    sem_pend_client_source_calls environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical.(critical_region_clients) sg observer None origin (kernel_critical_c_entry call)
      false origin (kernel_critical_c_returned call) trace.
Proof.
  intros environment critical local sg frame call before after observer origin Hmember Hforeign Hcompletion.
  destruct (sem_pend_critical_completion_observations _ _ _ _ _ _ _ _ Hcompletion)
    as [Hstep [Hparked Hcurrent]].
  assert (Htyped : tmr_task_critical_source_client (sem_pend_critical_call_action call))
    by (destruct call; constructor).
  assert (Hevent : forall invocation, None = Some invocation ->
      kernel_client_event_actor (sem_pend_critical_call_action call) <> Some invocation)
    by (intros; discriminate).
  pose (Hexecution := @TaskExecutionClientFrame environment.(task_stack_call_external)
    environment.(task_stack_call_port) sg (sem_pend_critical_call_action call) origin
    (kernel_critical_c_entry call) (kernel_critical_c_returned call) Hstep Hcurrent).
  assert (Hstop : kernel_client_stops (sem_pend_critical_call_action call) observer = false)
    by (destruct call; reflexivity).
  replace false with (orb (kernel_client_stops (sem_pend_critical_call_action call) observer) false)
    by (rewrite Hstop; reflexivity).
  exists (@KernelClientTaskSourceStep environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer None (sem_pend_critical_call_action call)
    origin (kernel_critical_c_entry call) origin (kernel_critical_c_returned call) origin
    (kernel_critical_c_returned call) false Hmember Hforeign Hevent Hstep Hexecution
    (@KernelClientTaskSourceNil environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical.(critical_region_clients) sg observer None origin (kernel_critical_c_returned call))).
  apply SemPendClientSourceCallsStep; [apply TmrTaskCallCritical; assumption|constructor].
Qed.


Section SemPendCriticalCertificate.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (observer : nat) (origin : TaskInvocationOrigin).
Let segment := kernel_program_c_step environment critical sg observer origin.

Inductive sem_pend_critical_c_step_certificate :
  forall state before input stopped current after output,
  segment state before input stopped current after output -> TaskInvocationOrigin -> TaskInvocationOrigin -> Prop :=
| SemPendCriticalCStepCertificate : forall local frame call before after
    (completion : kernel_critical_c_completion environment critical local sg frame call before after) first,
    critical.(critical_region_clients) (sem_pend_critical_call_action call) ->
    kernel_client_actor (sem_pend_critical_call_action call) <> Some observer ->
    sem_pend_critical_c_step_certificate _ _ _ _ _ _ _
      (@KernelProgramCCritical environment critical sg observer origin local frame call before after
        (kernel_critical_c_completion_segment environment critical local sg frame call before after completion)) first first.

Lemma sem_pend_critical_c_step_client_calls : forall state before input stopped current after output step first last,
  sem_pend_critical_c_step_certificate state before input stopped current after output step first last ->
  exists trace : kernel_client_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None first state stopped last current,
    sem_pend_client_source_calls environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical.(critical_region_clients) sg observer None first state stopped last current trace.
Proof.
  intros until last; intro Hcertificate; destruct Hcertificate.
  eapply sem_pend_critical_completion_client_calls; eassumption.
Qed.

Lemma sem_pend_critical_c_sequence_parked_stacks : forall state before input stopped current after output run first last,
  sem_pend_c_sequence_call_certificate segment sem_pend_critical_c_step_certificate
    state before input stopped current after output run first last ->
  current.(TskState).(parkedTaskStacks) = state.(TskState).(parkedTaskStacks).
Proof.
  intros until last; intro Hcertificate; induction Hcertificate.
  - reflexivity.
  - destruct H; exact (proj1 (proj2 (sem_pend_critical_completion_observations _ _ _ _ _ _ _ _ completion))).
  - etransitivity; [exact IHHcertificate2|exact IHHcertificate1].
  - exact IHHcertificate.
Qed.

Lemma sem_pend_critical_environment_source : forall state before input stopped current after output run first last,
  sem_pend_c_sequence_call_certificate segment sem_pend_critical_c_step_certificate
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
End SemPendCriticalCertificate.

(** Direct consumer of an actual critical C completion. Membership and
    foreignness are the existing registered-client protocol, not a new
    public Require. The unregistered/local completion is not discarded. *)
Lemma sem_pend_critical_completion_selected_source :
  forall environment critical local sg frame call before after observed,
  critical.(critical_region_clients) (sem_pend_critical_call_action call) ->
  kernel_client_actor (sem_pend_critical_call_action call) <> Some observed.(os_sched_call_invocation) ->
  forall completion : kernel_critical_c_completion environment critical local sg frame call before after,
  exists run : kernel_c_sequence (kernel_program_c_step environment critical sg
      observed.(os_sched_call_invocation) observed.(os_sched_call_origin))
    (kernel_critical_c_entry call) before
    (kernel_critical_c_owner environment critical local sg call (kernel_critical_c_entry call) ** frame)
    false (kernel_critical_c_returned call) after
    (kernel_critical_c_owner environment critical local sg call (kernel_critical_c_returned call) ** frame),
    sem_pend_c_sequence_call_certificate _
      (sem_pend_critical_c_step_certificate environment critical sg observed.(os_sched_call_invocation) observed.(os_sched_call_origin))
      _ _ _ _ _ _ _ run observed.(os_sched_call_origin) observed.(os_sched_call_origin) /\
    let included := sem_pend_selected_environment_sequence environment critical sg
      observed.(os_sched_call_invocation) observed.(os_sched_call_origin) _ _ _ _ _ _ _ run in
    kernel_program_environment_c_sequence_source environment critical sg
      observed.(os_sched_call_invocation) observed.(os_sched_call_origin) None _ _ _ _ _ _ _ included /\
    sem_pend_c_sequence_call_certificate _
      (sem_pend_environment_call_receipt environment critical sg observed.(os_sched_call_invocation) observed.(os_sched_call_origin)
        (sem_pend_critical_c_step_certificate environment critical sg observed.(os_sched_call_invocation) observed.(os_sched_call_origin)))
      _ _ _ _ _ _ _ included observed.(os_sched_call_origin) observed.(os_sched_call_origin) /\
    sem_pend_client_return_source environment critical sg observed (kernel_critical_c_entry call)
      observed (kernel_critical_c_returned call) /\
    (kernel_critical_c_owner environment critical local sg call (kernel_critical_c_returned call) ** frame) after.
Proof.
  intros environment critical local sg frame call before after observed Hmember Hforeign completion.
  pose (actual := kernel_critical_c_completion_segment environment critical local sg frame call before after completion).
  pose (step := @KernelProgramCCritical environment critical sg observed.(os_sched_call_invocation)
    observed.(os_sched_call_origin) local frame call before after actual).
  pose (run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step).
  assert (Hcertificate : sem_pend_c_sequence_call_certificate _
    (sem_pend_critical_c_step_certificate environment critical sg observed.(os_sched_call_invocation) observed.(os_sched_call_origin))
    _ _ _ _ _ _ _ run observed.(os_sched_call_origin) observed.(os_sched_call_origin)).
  { unfold run, step, actual; apply SemPendCSequenceCallAtom, SemPendCriticalCStepCertificate; assumption. }
  exists run; split; [exact Hcertificate|]. split.
  - eapply sem_pend_critical_environment_source; exact Hcertificate.
  - split.
    + apply sem_pend_selected_environment_sequence_certificate; exact Hcertificate.
    + split.
      * destruct (sem_pend_critical_completion_client_calls environment critical local sg frame call before after
          observed.(os_sched_call_invocation) observed.(os_sched_call_origin) Hmember Hforeign completion)
          as [trace Htrace].
        eapply sem_pend_client_return_source_from_legacy; [exact Htrace|].
        eapply sem_pend_critical_completion_normal_return; exact completion.
      * exact (proj2 (kernel_critical_c_segment_resources _ _ _ _ _ _ _ _ actual)).
Qed.

Lemma sem_pend_mutex_post_segment_normal_return :
  forall source_env environment critical local sg frame call before after observed,
  PostComponent.mutex_post_critical_c_segment source_env environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical local sg frame call before after ->
  kernel_call_normal_return observed call.(PostComponent.mutex_post_critical_entry)
    observed call.(PostComponent.mutex_post_critical_checkpoint).
Proof.
  intros source_env environment critical local sg frame call before after observed Hsegment.
  destruct Hsegment as [[Hnative Hcritical] Hinput Houtput].
  pose proof (mutex_post_critical_call_fields_eq _ _ _ _ _ _ _ Hcritical)
    as [Hnodes [Hparked Hrest]].
  split; [unfold task_tcb_init_stack_same_call; auto|].
  unfold kernel_call_stack_available; rewrite Hparked; auto.
Qed.

(** The literal EventReady post and the following count/count/table/owner
    memory fragment produce the checkpoint owner. No final owner premise
    is accepted by this producer. The acquired caller support remains in
    the same physical frame throughout the fragment. *)
Lemma sem_pend_mutex_post_handover_committed_owner :
  forall environment critical source_env local sg frame context saved entry eid caller caller_node
    event mutex prepared selected old priority prepared_heap prepared_frame helper_heap after,
  let wake := event_wake_state sg prepared eid event selected old PendMutex 0 PendOK in
  let found := event_set_wait_list event (remove_Z_eqb selected event.(waitList)) in
  let checkpoint := mutex_post_owner_state wake eid found mutex (Some selected) (Some priority) in
  let call := {| PostComponent.mutex_post_critical_context := context;
    PostComponent.mutex_post_critical_saved := saved;
    PostComponent.mutex_post_critical_entry := entry;
    PostComponent.mutex_post_critical_checkpoint := checkpoint;
    PostComponent.mutex_post_critical_eid := eid;
    PostComponent.mutex_post_critical_caller := caller;
    PostComponent.mutex_post_critical_node := caller_node;
    PostComponent.mutex_post_critical_result := mutex_post_handover_error sg mutex priority;
    PostComponent.mutex_post_critical_schedule := true |} in
  let retained := critical_region_masked environment.(task_stack_call_platform) critical sg
    context.(os_sched_call_invocation) context.(os_sched_call_origin) saved entry **
    mutex_del_continuation_acquired source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) local sg context entry ** frame in
  (UCOS2_inv sg prepared ** prepared_frame) prepared_heap ->
  prepared.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ prepared.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved) ->
  event_task_rdy_entry sg prepared.(TskState) eid event selected old ->
  ((event_task_rdy_post sg prepared.(TskState) eid event selected old 0 16 0
      (encode_ready_grp prepared.(SchedState).(readyList) prepared.(TskState))
      (sched_row_values prepared.(TskState) prepared.(SchedState).(readyList)) priority **
    mutex_del_wake_frame sg prepared eid selected) ** retained) helper_heap ->
  mutex_post_handover_store_fragment sg eid priority helper_heap after ->
  (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical local sg call checkpoint ** frame) after.
Proof.
  intros environment critical source_env local sg frame context saved entry eid caller caller_node
    event mutex prepared selected old priority prepared_heap prepared_frame helper_heap after
    wake found checkpoint call retained Hprepared Hlookup Htype Hfields Hslot Hentry Hhelper Hstores.
  assert (Hvalid : UCOS2_state_inv sg prepared).
  { assert (Hopen : UCOS2_inv sg prepared ** prepared_frame |--
      coq_prop (UCOS2_state_inv sg prepared) && (UCOS2_inv sg prepared ** prepared_frame))
      by (unfold UCOS2_inv; entailer!).
    exact (proj1 (Hopen prepared_heap Hprepared)). }
  pose proof (mutex_post_wake_fragment_preserves_resources sg prepared eid event mutex selected old priority
    retained helper_heap after Hvalid Hlookup Htype Hfields Hslot Hentry Hhelper Hstores) as Hafter.
  assert (Hreorder : (UCOS2_inv sg checkpoint ** unmap_table_rep sg) ** retained |--
    PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg call checkpoint ** frame).
  { change ((UCOS2_inv sg checkpoint ** unmap_table_rep sg) **
      (critical_region_masked environment.(task_stack_call_platform) critical sg
        context.(os_sched_call_invocation) context.(os_sched_call_origin) saved entry **
       mutex_del_continuation_acquired source_env environment.(task_stack_call_external)
         environment.(task_stack_call_platform) local sg context entry ** frame) |--
      (critical_region_masked environment.(task_stack_call_platform) critical sg
        context.(os_sched_call_invocation) context.(os_sched_call_origin) saved entry **
       UCOS2_inv sg checkpoint ** unmap_table_rep sg **
       mutex_del_continuation_acquired source_env environment.(task_stack_call_external)
         environment.(task_stack_call_platform) local sg context entry) ** frame).
    entailer!. }
  exact (Hreorder after Hafter).
Qed.

Lemma sem_pend_mutex_post_handover_selected_source :
  forall environment critical source_env local sg frame context saved entry eid caller caller_node
    event mutex prepared selected old priority prepared_heap prepared_frame before helper_heap after observed,
  let wake := event_wake_state sg prepared eid event selected old PendMutex 0 PendOK in
  let found := event_set_wait_list event (remove_Z_eqb selected event.(waitList)) in
  let checkpoint := mutex_post_owner_state wake eid found mutex (Some selected) (Some priority) in
  let call := {| PostComponent.mutex_post_critical_context := context;
    PostComponent.mutex_post_critical_saved := saved;
    PostComponent.mutex_post_critical_entry := entry;
    PostComponent.mutex_post_critical_checkpoint := checkpoint;
    PostComponent.mutex_post_critical_eid := eid;
    PostComponent.mutex_post_critical_caller := caller;
    PostComponent.mutex_post_critical_node := caller_node;
    PostComponent.mutex_post_critical_result := mutex_post_handover_error sg mutex priority;
    PostComponent.mutex_post_critical_schedule := true |} in
  let retained := critical_region_masked environment.(task_stack_call_platform) critical sg
    context.(os_sched_call_invocation) context.(os_sched_call_origin) saved entry **
    mutex_del_continuation_acquired source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) local sg context entry ** frame in
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some caller -> mutex_post_prepare sg mutex caller entry prepared ->
  encode_event_wait_grp event.(waitList) prepared.(TskState) <> 0 ->
  mutex_post_native_caller sg context.(os_sched_call_invocation) context.(os_sched_call_origin)
    entry context caller caller_node ->
  (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical local sg call entry ** frame) before ->
  (UCOS2_inv sg prepared ** prepared_frame) prepared_heap ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ prepared.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved) ->
  event_task_rdy_entry sg prepared.(TskState) eid event selected old ->
  ((event_task_rdy_post sg prepared.(TskState) eid event selected old 0 16 0
      (encode_ready_grp prepared.(SchedState).(readyList) prepared.(TskState))
      (sched_row_values prepared.(TskState) prepared.(SchedState).(readyList)) priority **
    mutex_del_wake_frame sg prepared eid selected) ** retained) helper_heap ->
  mutex_post_handover_store_fragment sg eid priority helper_heap after ->
  exists segment : PostComponent.mutex_post_critical_c_segment source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg frame call before after,
    let step := @KernelProgramCMutexPost environment critical sg observed.(os_sched_call_invocation)
      observed.(os_sched_call_origin) source_env local frame call before after segment in
    let run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step in
    sem_pend_program_c_step_receipt environment critical sg observed.(os_sched_call_invocation)
      observed.(os_sched_call_origin) _ _ _ _ _ _ _ step /\
    sem_pend_selected_c_sequence_receipt environment critical sg observed.(os_sched_call_invocation)
      observed.(os_sched_call_origin) _ _ _ _ _ _ _
      (sem_pend_selected_sequence environment critical sg observed.(os_sched_call_invocation)
        observed.(os_sched_call_origin) _ _ _ _ _ _ _ run) /\
    kernel_program_environment_c_sequence_source environment critical sg observed.(os_sched_call_invocation)
      observed.(os_sched_call_origin) None _ _ _ _ _ _ _
      (sem_pend_selected_environment_sequence environment critical sg observed.(os_sched_call_invocation)
        observed.(os_sched_call_origin) _ _ _ _ _ _ _ run) /\
    kernel_call_normal_return observed entry observed checkpoint /\
    (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg call checkpoint ** frame) after.
Proof.
  intros environment critical source_env local sg frame context saved entry eid caller caller_node
    event mutex prepared selected old priority prepared_heap prepared_frame before helper_heap after observed
    wake found checkpoint call retained Hlookup Htype Hfields Howner Hprepare Hnonempty Hnative Hinput
    Hprepared Hslot Hentry Hhelper Hstores.
  assert (Hvalid : UCOS2_state_inv sg prepared).
  { assert (Hopen : UCOS2_inv sg prepared ** prepared_frame |--
      coq_prop (UCOS2_state_inv sg prepared) && (UCOS2_inv sg prepared ** prepared_frame))
      by (unfold UCOS2_inv; entailer!).
    exact (proj1 (Hopen prepared_heap Hprepared)). }
  assert (Hprepared_lookup : prepared.(EventState).(inUsedEventStates) eid = Some event).
  { rewrite (mutex_post_prepare_event_state_eq _ _ _ _ _ Hprepare); exact Hlookup. }
  assert (Hreturn : priority = old.(curPrio)).
  { destruct Hhelper as [callee [rest [Hjoin [Hcore Hretained]]]].
    destruct Hcore as [owned [residual [Hjoin' [Hpost Hresidual]]]].
    exact (proj2 (proj1 Hpost)). }
  assert (Hwake : event_task_rdy sg prepared eid PendMutex 0 PendOK = Some (priority, wake)).
  { destruct Hhelper as [callee [rest [Hjoin [Hpost Hretained]]]].
    exact (proj1 (mutex_post_wake_merge_inv sg eid prepared event selected old priority
      Hvalid Hprepared_lookup Htype Hentry callee Hpost)). }
  assert (Hfound : wake.(EventState).(inUsedEventStates) eid = Some found).
  { unfold wake, found; cbn [event_wake_state replace_SchedS replace_EventS replace_TskS EventState
      inUsedEventStates update_event_field_raw]; rewrite Z.eqb_refl; reflexivity. }
  pose proof (proj1 (mutex_post_wake_owner_selection sg prepared eid event selected old priority Hentry Hreturn)) as Htable.
  pose proof (sem_pend_mutex_post_handover_committed_owner environment critical source_env local sg frame
    context saved entry eid caller caller_node event mutex prepared selected old priority prepared_heap prepared_frame
    helper_heap after Hprepared Hprepared_lookup Htype Hfields Hslot Hentry Hhelper Hstores) as Houtput.
  destruct (sem_pend_mutex_post_handover_segment_receipt environment critical source_env local sg
    observed.(os_sched_call_invocation) observed.(os_sched_call_origin) frame context saved entry eid caller caller_node
    event mutex prepared priority wake found selected before after prepared_heap prepared_frame
    Hlookup Htype Hfields Howner Hprepare Hnonempty Hwake Hfound Htable Hnative Hinput Hprepared Houtput)
    as [segment [Hreceipt Hsource]].
  exists segment; split; [exact Hreceipt|]. split.
  - cbn [sem_pend_selected_sequence].
    apply KernelCSourceAtom, SemPendSelectedReturnReceipt, SemPendReturnOriginalReceipt; exact Hreceipt.
  - split.
    + cbn [sem_pend_selected_environment_sequence sem_pend_selected_sequence
        kernel_program_environment_sequence_include kernel_program_returned_sequence_include
        kernel_program_wrapper_sequence_include].
      apply KernelCSourceAtom, KernelProgramEnvironmentBodySource, KernelProgramReturnedWrapperSource,
        KernelProgramWrapperOriginalSource, KernelSelectedProgramReturnSource, KernelProgramReturnOriginalSource.
      right; constructor.
    + split.
      * exact (sem_pend_mutex_post_segment_normal_return source_env environment critical local sg
          frame call before after observed segment).
      * exact Houtput.
Qed.
