Require Import Coq.ZArith.ZArith.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.event Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_c_segment_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_resource_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_api_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_receipt_producer_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_critical_restore_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_typed_call_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Coq.ZArith.ZArith Coq.Bool.Bool.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_phase_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_c_sequence_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_clear_status_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_sched_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_c_call_connection_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_mutex_post_call_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_mutex_inheritance_call_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_builtin_call_source_spec.
Import UCOS2_C_Rules TaskStateDef.
Import SelectedCProgram SelectedCSource SelectedIRQWrapperSegment SelectedIRQWrapperSource.
Import SelectedReturnedCProgram SelectedReturnedCSource.
Import SelectedEnvironmentCProgram SelectedEnvironmentCSource SelectedEnvironmentScopedEnvironment.
Import SelectedEnvironmentPhaseEffects SelectedEnvironmentPhaseProperties.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A consequence of an actual modular call, indexed by its original C run.
    The observation may cover a complete stable segment (including Delete's
    two windows); it is not a requirement on every internal raw atom. *)
Definition sem_pend_client_module_run environment critical sg observer stored_origin
  state before input stopped current after output
  (run : kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer stored_origin)
    state before input stopped current after output) first last : Prop :=
  kernel_program_environment_c_sequence_source environment critical sg observer stored_origin None
    state before input stopped current after output run /\
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer None first state stopped last current.

(** Literal inclusions preserve the source proof on the very injected tree. *)
Lemma sem_pend_module_injected_source :
  forall source target inject source_marker target_marker,
  (forall state before input stopped current after output step,
    source_marker state before input stopped current after output step ->
    target_marker state before input stopped current after output
      (inject state before input stopped current after output step)) ->
  forall state before input stopped current after output run,
  kernel_c_sequence_has_source source source_marker state before input stopped current after output run ->
  kernel_c_sequence_has_source target target_marker state before input stopped current after output
    (sem_pend_injected_c_sequence source target inject _ _ _ _ _ _ _ run).
Proof.
  intros source target inject source_marker target_marker Hinject
    state before input stopped current after output run Hsource.
  induction Hsource; cbn [sem_pend_injected_c_sequence].
  - constructor.
  - constructor; apply Hinject; assumption.
  - apply KernelCSourceThen; assumption.
  - apply KernelCSourceAdapt; assumption.
Qed.

Definition sem_pend_module_selected_sequence environment critical sg observer stored_origin
  state before input stopped current after output
  (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer stored_origin)
    state before input stopped current after output) :=
  sem_pend_injected_c_sequence _ _ (sem_pend_environment_body_step environment critical sg observer stored_origin)
    _ _ _ _ _ _ _
    (sem_pend_injected_c_sequence _ _ (sem_pend_returned_wrapper_step environment critical sg observer stored_origin)
      _ _ _ _ _ _ _
      (sem_pend_injected_c_sequence _ _ (sem_pend_wrapper_original_step environment critical sg observer stored_origin)
        _ _ _ _ _ _ _ run)).

Definition sem_pend_module_program_sequence environment critical sg observer stored_origin
  state before input stopped current after output
  (run : kernel_c_sequence (kernel_program_c_step environment critical sg observer stored_origin)
    state before input stopped current after output) :=
  sem_pend_module_selected_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _
    (sem_pend_injected_c_sequence _ _ (sem_pend_selected_return_step environment critical sg observer stored_origin)
      _ _ _ _ _ _ _
      (sem_pend_injected_c_sequence _ _ (sem_pend_return_original_step environment critical sg observer stored_origin)
        _ _ _ _ _ _ _ run)).

Lemma sem_pend_module_selected_sequence_source :
  forall environment critical sg observer stored_origin state before input stopped current after output run,
  kernel_program_selected_c_sequence_source environment critical sg observer stored_origin None
    state before input stopped current after output run ->
  kernel_program_environment_c_sequence_source environment critical sg observer stored_origin None
    _ _ _ _ _ _ _
    (sem_pend_module_selected_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ run).
Proof.
  intros until run; intro Hsource.
  unfold sem_pend_module_selected_sequence, kernel_program_environment_c_sequence_source.
  eapply sem_pend_module_injected_source; [intros; constructor; eassumption|].
  eapply sem_pend_module_injected_source; [intros; constructor; eassumption|].
  eapply sem_pend_module_injected_source; [intros; constructor; eassumption|].
  exact Hsource.
Qed.

Lemma sem_pend_module_program_sequence_source :
  forall environment critical sg observer stored_origin state before input stopped current after output run,
  kernel_program_c_sequence_call_source environment critical sg observer stored_origin None
    state before input stopped current after output run ->
  kernel_program_environment_c_sequence_source environment critical sg observer stored_origin None
    _ _ _ _ _ _ _
    (sem_pend_module_program_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ run).
Proof.
  intros until run; intro Hsource.
  unfold sem_pend_module_program_sequence.
  apply sem_pend_module_selected_sequence_source.
  unfold kernel_program_selected_c_sequence_source.
  eapply sem_pend_module_injected_source; [intros; constructor; eassumption|].
  eapply sem_pend_module_injected_source; [intros; constructor; eassumption|].
  exact Hsource.
Qed.

Lemma sem_pend_module_program_observation :
  forall environment critical sg observer stored_origin state before input stopped current after output run first last,
  kernel_program_c_sequence_call_source environment critical sg observer stored_origin None
    state before input stopped current after output run ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer None first state stopped last current ->
  sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
    (sem_pend_module_program_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ run) first last.
Proof. intros; split; [apply sem_pend_module_program_sequence_source|]; assumption. Qed.

Lemma sem_pend_module_selected_observation :
  forall environment critical sg observer stored_origin state before input stopped current after output run first last,
  kernel_program_selected_c_sequence_source environment critical sg observer stored_origin None
    state before input stopped current after output run ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer None first state stopped last current ->
  sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
    (sem_pend_module_selected_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ run) first last.
Proof. intros; split; [apply sem_pend_module_selected_sequence_source|]; assumption. Qed.

(** These two interfaces consume the existing factory certificates; no
    independent observation or decoder is supplied by their caller. *)
Lemma sem_pend_module_program_certificate :
  forall environment critical sg observer stored_origin state before input stopped current after output run first last,
  kernel_program_c_sequence_call_source environment critical sg observer stored_origin None
    state before input stopped current after output run ->
  sem_pend_c_sequence_call_certificate _
    (sem_pend_client_program_call_observation environment critical sg observer stored_origin)
    state before input stopped current after output run first last ->
  sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
    (sem_pend_module_program_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ run) first last.
Proof.
  intros until last; intros Hsource Hcalls.
  apply sem_pend_module_program_observation; [exact Hsource|].
  eapply sem_pend_observed_c_sequence_trace; [|exact Hcalls].
  intros; eapply sem_pend_client_program_call_observation_trace; eassumption.
Qed.

Lemma sem_pend_module_selected_certificate :
  forall environment critical sg observer stored_origin state before input stopped current after output run first last,
  kernel_program_selected_c_sequence_source environment critical sg observer stored_origin None
    state before input stopped current after output run ->
  sem_pend_c_sequence_call_certificate _
    (fun state heap input stopped current output_heap output actual first last =>
      sem_pend_selected_c_step_receipt environment critical sg observer stored_origin
        state heap input stopped current output_heap output actual /\
      sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
        critical.(critical_region_clients) sg observer None first state stopped last current)
    state before input stopped current after output run first last ->
  sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
    (sem_pend_module_selected_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ run) first last.
Proof.
  intros until last; intros Hsource Hcalls.
  apply sem_pend_module_selected_observation; [exact Hsource|].
  eapply sem_pend_observed_c_sequence_trace; [|exact Hcalls].
  intros; exact (proj2 H).
Qed.

Lemma sem_pend_client_module_refl :
  forall environment critical sg observer stored_origin state heap owner (owned : owner heap) origin,
  sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
    (KernelCSequenceRefl _ state heap owner owned) origin origin.
Proof. intros; split; [constructor|apply sem_pend_observed_client_trace_refl]. Qed.

Lemma sem_pend_client_module_then :
  forall environment critical sg observer stored_origin state before input stopped1 middle middle_heap
    first_output next_input stopped2 current after output first bridge last origin transient returned,
  sem_pend_client_module_run environment critical sg observer stored_origin
    state before input stopped1 middle middle_heap first_output first origin transient ->
  sem_pend_client_module_run environment critical sg observer stored_origin
    middle middle_heap next_input stopped2 current after output last transient returned ->
  sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
    (KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ first bridge last) origin returned.
Proof.
  intros until returned; intros [Hfirst Hfirst_trace] [Hlast Hlast_trace].
  split; [apply KernelCSourceThen|eapply SemPendObservedThen]; eassumption.
Qed.

Lemma sem_pend_client_module_adapt :
  forall environment critical sg observer stored_origin state before input inner_input stopped current after
    inner_output output owned open_input inner close_output first last,
  sem_pend_client_module_run environment critical sg observer stored_origin
    state before inner_input stopped current after inner_output inner first last ->
  sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
    (KernelCSequenceAdapt _ _ _ input inner_input _ _ _ inner_output output owned open_input inner close_output) first last.
Proof. intros until last; intros [Hsource Htrace]; split; [apply KernelCSourceAdapt|]; assumption. Qed.

Lemma sem_pend_module_mutex_post_not_owner :
  forall environment critical source_env local sg observer stored_origin origin
    frame context saved entry eid caller caller_node event mutex before,
  let call := {| PostComponent.mutex_post_critical_context := context;
    PostComponent.mutex_post_critical_saved := saved;
    PostComponent.mutex_post_critical_entry := entry;
    PostComponent.mutex_post_critical_checkpoint := entry;
    PostComponent.mutex_post_critical_eid := eid;
    PostComponent.mutex_post_critical_caller := caller;
    PostComponent.mutex_post_critical_node := caller_node;
    PostComponent.mutex_post_critical_result := OS_ERR_NOT_MUTEX_OWNER;
    PostComponent.mutex_post_critical_schedule := false |} in
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) <> Some caller ->
  mutex_post_native_caller sg context.(os_sched_call_invocation) context.(os_sched_call_origin)
    entry context caller caller_node ->
  (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical local sg call entry ** frame) before ->
  exists segment : PostComponent.mutex_post_critical_c_segment source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg frame call before before,
    let step := @KernelProgramCMutexPost environment critical sg observer stored_origin
      source_env local frame call before before segment in
    let run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step in
    sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
      (sem_pend_module_program_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ run) origin origin /\
    (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg call entry ** frame) before.
Proof.
  intros environment critical source_env local sg observer stored_origin origin
    frame context saved entry eid caller caller_node event mutex before call
    Hlookup Htype Hmutex Hnotowner Hcaller Hinput.
  edestruct (sem_pend_mutex_post_not_owner_call_certificate environment critical source_env local sg observer stored_origin origin
    frame context saved entry eid caller caller_node event mutex before) as [segment [Hcalls Hmodule_owner]]; try eassumption.
  exists segment; cbn zeta; split; [|exact Hmodule_owner].
  eapply sem_pend_module_program_certificate; [apply KernelCSourceAtom; right; constructor|exact Hcalls].
Qed.

Lemma sem_pend_module_mutex_post_empty :
  forall environment critical source_env local sg observer stored_origin origin frame context saved
    entry eid caller caller_node event mutex prepared before prepared_heap after,
  let checkpoint := mutex_post_owner_state prepared eid event mutex None None in
  let call := {| PostComponent.mutex_post_critical_context := context;
    PostComponent.mutex_post_critical_saved := saved;
    PostComponent.mutex_post_critical_entry := entry;
    PostComponent.mutex_post_critical_checkpoint := checkpoint;
    PostComponent.mutex_post_critical_eid := eid;
    PostComponent.mutex_post_critical_caller := caller;
    PostComponent.mutex_post_critical_node := caller_node;
    PostComponent.mutex_post_critical_result := OS_ERR_NONE;
    PostComponent.mutex_post_critical_schedule := false |} in
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some caller -> mutex_post_prepare sg mutex caller entry prepared ->
  encode_event_wait_grp event.(waitList) prepared.(TskState) = 0 ->
  mutex_post_native_caller sg context.(os_sched_call_invocation) context.(os_sched_call_origin)
    entry context caller caller_node ->
  (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical local sg call entry ** frame) before ->
  (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical local sg call prepared ** frame) prepared_heap ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ prepared.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved) ->
  mutex_post_empty_store_fragment sg eid prepared_heap after ->
  exists segment : PostComponent.mutex_post_critical_c_segment source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg frame call before after,
    let step := @KernelProgramCMutexPost environment critical sg observer stored_origin
      source_env local frame call before after segment in
    let run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step in
    sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
      (sem_pend_module_program_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ run) origin origin /\
    (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg call checkpoint ** frame) after.
Proof.
  intros environment critical source_env local sg observer stored_origin origin frame context saved
    entry eid caller caller_node event mutex prepared before prepared_heap after checkpoint call
    Hlookup Htype Hfields Howner Hprepare Hempty Hnative Hinput Hprepared Hslot Hstores.
  edestruct (sem_pend_mutex_post_empty_call_certificate environment critical source_env local sg observer stored_origin origin frame context saved
    entry eid caller caller_node event mutex prepared before prepared_heap after) as [segment [Hcalls Hmodule_owner]]; try eassumption.
  exists segment; cbn zeta; split; [|exact Hmodule_owner].
  eapply sem_pend_module_program_certificate; [apply KernelCSourceAtom; right; constructor|exact Hcalls].
Qed.

Lemma sem_pend_module_mutex_post_handover :
  forall environment critical source_env local sg observer stored_origin origin frame context saved entry eid caller caller_node
    event mutex prepared selected old priority prepared_heap prepared_frame before helper_heap after,
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
    let step := @KernelProgramCMutexPost environment critical sg observer stored_origin
      source_env local frame call before after segment in
    let run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step in
    sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
      (sem_pend_module_program_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ run) origin origin /\
    (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg call checkpoint ** frame) after.
Proof.
  intros environment critical source_env local sg observer stored_origin origin frame context saved entry eid caller caller_node
    event mutex prepared selected old priority prepared_heap prepared_frame before helper_heap after
    wake found checkpoint call retained Hlookup Htype Hfields Howner Hprepare Hnonempty Hnative Hinput
    Hprepared Hslot Hentry Hhelper Hstores.
  edestruct (sem_pend_mutex_post_handover_call_certificate environment critical source_env local sg observer stored_origin origin frame context saved entry eid caller caller_node
    event mutex prepared selected old priority prepared_heap prepared_frame before helper_heap after) as [segment [Hcalls Hmodule_owner]]; try eassumption.
  exists segment; cbn zeta; split; [|exact Hmodule_owner].
  eapply sem_pend_module_program_certificate; [apply KernelCSourceAtom; right; constructor|exact Hcalls].
Qed.

Lemma sem_pend_module_mutex_inheritance_busy :
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
    sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
      (sem_pend_module_program_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ run) origin origin /\
    (PendComponent.mutex_pend_inheritance_c_owner environment critical local sg call
      call.(PendComponent.mutex_pend_inheritance_returned) ** frame) after.
Proof.
  intros environment critical local sg observer stored_origin origin frame call before after eid event mutex current
    Hlookup Htype Hmutex Howner Hcurrent Hholds Hnode Hpre Hpost.
  edestruct (sem_pend_mutex_inheritance_busy_call_certificate environment critical local sg observer stored_origin origin frame call before after eid event mutex current) as [segment [Hcalls Hmodule_owner]]; try eassumption.
  exists segment; cbn zeta; split; [|exact Hmodule_owner].
  eapply sem_pend_module_program_certificate; [apply KernelCSourceAtom; right; constructor|exact Hcalls].
Qed.

Lemma sem_pend_module_masked_suspend :
  forall environment critical saved_local sg observer stored_origin origin caller saved call frame before after
    (completion : TaskSuspendMaskedC.task_suspend_masked_completion
      environment critical saved_local sg caller saved call frame before after),
  let primitive := TaskSuspendMaskedC.TaskSuspendMaskedCStep environment critical sg
    saved_local caller saved call frame before after completion in
  let step := @SelectedCProgram.KernelSelectedProgramSuspend critical sg observer stored_origin environment
    _ _ _ _ _ _ _ primitive in
  let run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step in
  sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
    (sem_pend_module_selected_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ run) origin origin /\
  (task_suspend_masked environment critical saved_local sg caller saved
    call.(TaskSuspendActualC.suspend_actual_entry) call.(TaskSuspendActualC.suspend_actual_checkpoint) ** frame) after.
Proof.
  intros environment critical saved_local sg observer stored_origin origin caller saved call frame before after
    completion primitive step run.
  destruct (sem_pend_masked_suspend_call_certificate environment critical saved_local sg observer stored_origin origin caller saved call frame before after completion) as [Hcalls Howner].
  split; [|exact Howner].
  eapply sem_pend_module_selected_certificate; [apply KernelCSourceAtom; constructor|exact Hcalls].
Qed.

Lemma sem_pend_module_install :
  forall environment critical local sg observer stored_origin frame call before after sp Hactual
    (segment : InstallComponent.task_install_c_segment environment local sg frame call before after sp Hactual),
  let primitive := InstallComponent.TaskInstallCStep environment local sg frame call before after sp Hactual segment in
  let step := @KernelProgramCInstall environment critical sg observer stored_origin local _ _ _ _ _ _ _ primitive in
  let run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step in
  sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
    (sem_pend_module_program_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ run) call.(InstallComponent.task_install_fields_context).(os_sched_call_origin)
      (RunningInvocation call.(InstallComponent.task_install_fields_incoming).(stackLeaseSlot)
        call.(InstallComponent.task_install_fields_incoming).(stackLeaseGeneration)) /\
  (InstallComponent.task_install_fields_installed_owner environment local sg call ** frame) after.
Proof.
  intros environment critical local sg observer stored_origin frame call before after sp Hactual segment primitive step run.
  destruct (sem_pend_install_call_certificate environment critical local sg observer stored_origin frame call before after sp Hactual segment) as [Hcalls Howner].
  split; [|exact Howner].
  eapply sem_pend_module_program_certificate; [apply KernelCSourceAtom; right; constructor|exact Hcalls].
Qed.

(** The original scoped producer consumes the assembled source before its
    existential macro is hidden. Its existing C/ABI contract supplies the
    actual suffix and spatial return; the same assembled trace supplies the
    Sem observation. local and next_local are never equated. *)
Lemma sem_pend_module_save_phase_output :
  forall phase environment critical local next_local active sg mask call before first_heap
    private_input private_output private_before whole_before returned current environment_heap arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers final_registers whole_after
    (run : flag_pend_scoped_environment_run environment critical local next_local active sg
      call mask before whole_before private_input false returned current environment_heap private_output),
  sem_pend_clear_status_phase_save_pre phase environment critical sg call mask before ->
  sem_pend_client_module_run environment critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin)
    _ _ _ _ _ _ _ run call.(os_sched_call_origin) returned.(os_sched_call_origin) ->
  flag_pend_caller_save_input environment critical local active sg (FlagPendTaskCaller call)
    call mask before first_heap ->
  private_input private_before -> join first_heap private_before whole_before ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current environment_heap
    final_registers current whole_after ->
  exists last_heap (actual : os_sched_continuation_c_save_execution environment critical local next_local active sg
    call mask before first_heap final_registers.(kernel_save_r0) false returned current last_heap),
  (sem_pend_clear_status_phase_save_output phase environment next_local critical sg call mask
    final_registers.(kernel_save_r0) before ** active returned current) last_heap.
Proof.
  intros phase environment critical local next_local active sg mask call before first_heap
    private_input private_output private_before whole_before returned current environment_heap arch save
    registers final_registers whole_after run Hpre [Hsource Htrace] Hinput Hprivate Hjoin Hword Hvalid Hmask Hsuffix.
  destruct (os_sched_continuation_c_save_execution_from_environment environment critical local next_local active sg
    call mask before first_heap private_input private_output private_before whole_before false returned current
    environment_heap arch save registers final_registers whole_after run Hsource Hinput Hprivate Hjoin Hword Hvalid
    Hmask Hsuffix) as [last_heap actual].
  exists last_heap, actual.
  eapply sem_pend_completed_save_phase_output; eassumption.
Qed.

Lemma sem_pend_module_restore_phase_output :
  forall phase mask environment critical local next_local active sg original saved acquired before first_heap
    private_input private_output private_before whole_before returned current environment_heap arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written prefix_heap final_cursor whole_after
    (run : flag_pend_scoped_environment_run environment critical local next_local active sg
      original (armv7a_irq_fiq_mask saved) before prefix_heap private_input
      false returned current environment_heap private_output),
  sem_pend_client_phase_context sg original before ->
  sem_pend_clear_status_phase_restore_pre phase environment critical sg original mask before ->
  interrupt_saved_value mask saved ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before first_heap ->
  private_input private_before -> join first_heap private_before whole_before ->
  armv7a_restore_prefix_transition restore cursor whole_before written prefix_heap ->
  sem_pend_client_module_run environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin)
    _ _ _ _ _ _ _ run original.(os_sched_call_origin) returned.(os_sched_call_origin) ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor whole_after ->
  exists last_heap (actual : os_sched_continuation_c_restore_execution environment critical local next_local active sg
    original saved acquired before first_heap false returned current last_heap),
  (sem_pend_clear_status_phase_restore_output phase environment next_local critical sg original mask before **
    active returned current) last_heap.
Proof.
  intros phase mask environment critical local next_local active sg original saved acquired before first_heap
    private_input private_output private_before whole_before returned current environment_heap arch restore
    cursor written prefix_heap final_cursor whole_after run Hcontext Hpre Hsaved Hr0 Hmask Hinput Hprivate Hjoin
    Hprefix [Hsource Htrace] Hsuffix.
  destruct (os_sched_continuation_c_restore_execution_from_environment environment critical local next_local active sg
    original saved acquired before first_heap private_input private_output private_before whole_before false returned
    current environment_heap arch restore cursor written prefix_heap final_cursor whole_after run Hr0 Hmask Hinput
    Hprivate Hjoin Hprefix Hsource Hsuffix) as [last_heap actual].
  exists last_heap, actual.
  eapply sem_pend_completed_restore_phase_output; eassumption.
Qed.

Lemma sem_pend_module_waiting_restore_sched_input :
  forall environment critical local next_local active sg original mask initial observed eid timeout waiting
    call saved acquired before first_heap private_input private_output private_before whole_before returned current
    environment_heap arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written prefix_heap final_cursor whole_after
    (run : flag_pend_scoped_environment_run environment critical local next_local active sg
      call (armv7a_irq_fiq_mask saved) before prefix_heap private_input
      false returned current environment_heap private_output),
  sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting call before ->
  interrupt_saved_value mask saved ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller call) call saved acquired before first_heap ->
  private_input private_before -> join first_heap private_before whole_before ->
  armv7a_restore_prefix_transition restore cursor whole_before written prefix_heap ->
  sem_pend_client_module_run environment critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin)
    _ _ _ _ _ _ _ run call.(os_sched_call_origin) returned.(os_sched_call_origin) ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor whole_after ->
  exists last_heap (actual : os_sched_continuation_c_restore_execution environment critical local next_local active sg
    call saved acquired before first_heap false returned current last_heap),
  ((coq_prop (sem_pend_client_return_source environment critical sg call before returned current /\
      kernel_call_control_rely sg before current) &&
    sem_pend_client_sched_input environment next_local critical sg original mask initial observed eid timeout
      waiting returned current) ** active returned current) last_heap.
Proof.
  intros environment critical local next_local active sg original mask initial observed eid timeout waiting
    call saved acquired before first_heap private_input private_output private_before whole_before returned current
    environment_heap arch restore cursor written prefix_heap final_cursor whole_after run Hentry Hsaved Hr0 Hmask
    Hinput Hprivate Hjoin Hprefix [Hsource Htrace] Hsuffix.
  destruct (os_sched_continuation_c_restore_execution_from_environment environment critical local next_local active sg
    call saved acquired before first_heap private_input private_output private_before whole_before false returned
    current environment_heap arch restore cursor written prefix_heap final_cursor whole_after run Hr0 Hmask Hinput
    Hprivate Hjoin Hprefix Hsource Hsuffix) as [last_heap actual].
  exists last_heap, actual.
  eapply sem_pend_completed_waiting_restore_sched_input; eassumption.
Qed.
