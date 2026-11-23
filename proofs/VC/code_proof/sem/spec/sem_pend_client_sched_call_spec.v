Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.flag_fields_resources Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_phase_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_event_ready_source_receipt_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_sched_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_program_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_clear_status_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_selected_restore_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_restore_body_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_ready_endpoint_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_task_client_annotation_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_return_fields_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Import SchedulerPhaseCandidate SelectedEnvironmentPhaseEffects SelectedEnvironmentPhaseProperties.
Import SelectedEnvironmentScopedEnvironment SelectedEnvironmentCProgram SelectedEnvironmentCSource.
Import SemPendEventReadySource.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** This completed-call observation is already part of the actual scoped C
    Save/Restore execution. A blocked Task is still a Task caller; no Flag
    Fresh/Waiting protocol or ready premise is used to obtain control. *)
Lemma sem_pend_task_endpoint_control : forall environment sg call before returned current,
  kernel_call_task_source call before ->
  flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller call)
    call before returned current ->
  kernel_call_normal_return call before returned current /\
  kernel_call_control_rely sg before current.
Proof.
  intros environment sg call before returned current Hsource
    [_ [_ [_ [Hnormal Hcontrol]]]].
  split; [exact Hnormal|]. apply Hcontrol.
  rewrite (proj1 Hsource); discriminate.
Qed.

Lemma sem_pend_control_selection_enabled : forall sg before current,
  kernel_call_control_rely sg before current ->
  os_sched_selection_enabled before = true -> os_sched_selection_enabled current = true.
Proof.
  intros sg before current [_ Hcounters] Henabled.
  unfold os_sched_selection_enabled in *; rewrite Hcounters; exact Henabled.
Qed.

Lemma sem_pend_actual_restore_control : forall environment critical local next_local active sg call saved acquired
  before first_heap stopped returned current last_heap,
  os_sched_continuation_c_restore_execution environment critical local next_local active sg
    call saved acquired before first_heap stopped returned current last_heap ->
  kernel_call_task_source call before ->
  kernel_call_normal_return call before returned current /\
  kernel_call_control_rely sg before current /\
  (os_sched_selection_enabled before = true -> os_sched_selection_enabled current = true) /\
  flag_pend_caller_save_input environment critical next_local active sg
    (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current last_heap.
Proof.
  intros until last_heap; intros Hactual Hsource.
  destruct (proj2 (os_sched_continuation_c_restore_execution_resources _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual))
    as [Hendpoint Howner].
  destruct (sem_pend_task_endpoint_control environment sg call before returned current Hsource Hendpoint) as [Hnormal Hcontrol].
  exact (conj Hnormal (conj Hcontrol
    (conj (sem_pend_control_selection_enabled _ _ _ Hcontrol) Howner))).
Qed.

Lemma sem_pend_actual_save_control : forall environment critical local next_local active sg call mask
  before first_heap saved stopped returned current last_heap,
  os_sched_continuation_c_save_execution environment critical local next_local active sg
    call mask before first_heap saved stopped returned current last_heap ->
  kernel_call_task_source call before ->
  kernel_call_normal_return call before returned current /\
  kernel_call_control_rely sg before current /\
  (os_sched_selection_enabled before = true -> os_sched_selection_enabled current = true) /\
  flag_pend_caller_restore_input environment critical next_local active sg
    (FlagPendTaskCaller returned) returned saved current current last_heap.
Proof.
  intros until last_heap; intros Hactual Hsource.
  destruct (proj2 (os_sched_continuation_c_save_execution_resources _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual))
    as [Hendpoint Howner].
  destruct (sem_pend_task_endpoint_control environment sg call before returned current Hsource Hendpoint) as [Hnormal Hcontrol].
  exact (conj Hnormal (conj Hcontrol
    (conj (sem_pend_control_selection_enabled _ _ _ Hcontrol) Howner))).
Qed.

(** The counter fact starts at the actual first Save observation. The wait
    writes only Task/Event/Scheduler fields, including the suspended case. *)
Lemma sem_pend_acquire_wait_selection_enabled : forall environment critical sg call returned mask saved before acquired
  pevent eid observed event tid old timeout,
  sem_pend_clear_status_phase_save_observation (SemPendAcquirePhase pevent eid observed)
    environment critical sg call returned mask saved before acquired ->
  os_sched_selection_enabled (event_pend_state sg acquired eid event tid old PendSem timeout) = true.
Proof.
  intros until timeout; intros [_ [current [_ [_ [_ [_ [Hint Hlock]]]]]]].
  change ((Z.eqb acquired.(IntrState).(intNesting) 0 && Z.eqb acquired.(IntrState).(lockNesting) 0)%bool = true).
  rewrite Hint, Hlock; reflexivity.
Qed.

Lemma sem_pend_task_caller_closed : forall environment critical local active sg call mask current,
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller call) call mask current |--
  sem_pend_fields_closed environment local sg call mask current ** active call current.
Proof.
  intros; cbn [flag_pend_caller_save_input]; apply coq_prop_andp_left; intro Heq.
  unfold flag_pend_active_save_input, sem_pend_fields_closed.
  rewrite <- (os_sched_fields_save_input_closed_world environment critical local sg call mask current).
  entailer!.
Qed.

Lemma sem_pend_task_caller_masked : forall environment critical local active sg call saved acquired current,
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller call) call saved acquired current |--
  sem_pend_fields_masked environment local critical sg call saved acquired current ** active call current.
Proof.
  intros; cbn [flag_pend_caller_restore_input]; apply coq_prop_andp_left; intro Heq.
  unfold flag_pend_active_restore_input, sem_pend_fields_masked.
  rewrite <- (os_sched_fields_restore_input_masked_world environment critical local sg call saved acquired current).
  entailer!.
Qed.

(** Exactly the two caller-field facts already required separately by the
    checked Sem header. Only its live slot and generation are retained. *)
Definition sem_pend_client_sched_caller_fields sg original current : Prop :=
  flag_pend_non_idle_at sg original current /\
  exists node, current.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
    node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) /\ node.(tcbEventMultiPtr) = 0.

Lemma sem_pend_sched_client_return_caller_fields : forall environment critical sg call before returned after original,
  sem_pend_client_return_source environment critical sg call before returned after ->
  UCOS2_state_inv sg before -> before.(SchedState).(isRunning) = true ->
  kernel_call_task_source call before -> kernel_stack_call_same_call call original ->
  sem_pend_client_sched_caller_fields sg original before -> sem_pend_client_sched_caller_fields sg original after.
Proof.
  intros environment critical sg call before returned after original Hsource Hvalid Hrunning
    Htask Hsame [Hnonidle [old [Hold [Hgen Hzero]]]].
  split.
  - eapply sem_pend_task_client_return_preserves_non_idle; eassumption.
  - assert (Hold_call : before.(TskState).(inUsedTaskStates)
      call.(os_sched_call_stack).(stackLeaseSlot) = Some old).
    { rewrite (proj2 (proj2 Hsame)); exact Hold. }
    assert (Hgen_call : old.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration)).
    { rewrite (proj2 (proj2 Hsame)); exact Hgen. }
    destruct (tmr_task_client_return_multi_zero environment critical sg call before returned after old
      Hsource Hvalid Htask Hold_call Hgen_call Hzero) as [node [Hnode [Hgeneration [Hpointer Hall]]]].
    pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hsource) as Hreturned.
    rewrite (proj2 (proj2 Hreturned)), (proj2 (proj2 Hsame)) in Hnode, Hgeneration.
    exists node; exact (conj Hnode (conj Hgeneration Hpointer)).
Qed.

Definition sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting
  call current : Prop :=
  sem_pend_client_phase_context sg call current /\
  sem_pend_clear_status_phase_wait_at environment critical sg original mask initial observed eid timeout
    waiting call current /\ os_sched_selection_enabled current = true /\
  sem_pend_client_sched_caller_fields sg original current.

Definition sem_pend_client_sched_input environment local critical sg original mask initial observed eid timeout
  waiting call current : Assertion :=
  coq_prop (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout
    waiting call current) && sem_pend_fields_closed environment local sg call mask current.

Definition sem_pend_client_sched_save_output environment critical sg original mask initial observed eid timeout
  waiting call before saved : Assertion :=
  EX scheduled acquired next_local,
    coq_prop (sem_pend_client_return_source environment critical sg call before scheduled acquired /\
      kernel_call_control_rely sg before acquired /\ interrupt_saved_value mask saved /\
      sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout
        waiting scheduled acquired) &&
    sem_pend_fields_masked environment next_local critical sg scheduled saved acquired acquired.

Definition sem_pend_client_sched_body_output environment critical sg original mask initial observed eid timeout
  waiting scheduled saved acquired : Assertion :=
  EX returned current next_local,
    coq_prop (os_sched_task_body_observation environment critical sg scheduled acquired returned current /\
      sem_pend_client_phase_context sg returned current /\
      sem_pend_clear_status_phase_selected_at environment critical sg original mask initial observed eid timeout
        waiting returned current /\ os_sched_selection_enabled current = true /\
      sem_pend_client_sched_caller_fields sg original current) &&
    sem_pend_fields_masked environment next_local critical sg returned saved acquired current.

Definition sem_pend_client_sched_output environment critical sg original mask initial observed eid timeout
  waiting call before : Assertion :=
  EX returned current next_local,
    coq_prop (kernel_stack_call_same_call returned call /\ kernel_call_control_rely sg before current /\
      sem_pend_client_sched_caller_fields sg original current) &&
    sem_pend_clear_status_phase_save_input
      (SemPendWaitPhase original mask initial observed eid timeout waiting)
      environment next_local critical sg returned mask current.

Definition sem_pend_client_sched_restore_input environment local critical sg original mask initial observed eid timeout
  waiting call saved acquired released : Assertion :=
  coq_prop (interrupt_saved_value mask saved /\ sem_pend_client_phase_context sg call released /\
    sem_pend_clear_status_phase_selected_at environment critical sg original mask initial observed eid timeout
      waiting call released /\ sem_pend_client_sched_caller_fields sg original released) &&
  sem_pend_fields_masked environment local critical sg call saved acquired released.

Definition sem_pend_client_sched_restore_output environment critical sg original mask initial observed eid timeout
  waiting call released : Assertion :=
  EX returned current next_local,
    coq_prop (sem_pend_client_return_source environment critical sg call released returned current /\
      kernel_call_control_rely sg released current /\ sem_pend_client_sched_caller_fields sg original current) &&
    sem_pend_clear_status_phase_save_input (SemPendWaitPhase original mask initial observed eid timeout waiting)
      environment next_local critical sg returned mask current.

Lemma sem_pend_sched_entry_return : forall environment critical sg original mask initial observed eid timeout
  waiting call before returned current,
  sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting call before ->
  sem_pend_client_return_source environment critical sg call before returned current ->
  kernel_call_control_rely sg before current ->
  sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting returned current.
Proof.
  intros environment critical sg original mask initial observed eid timeout waiting call before returned current
    [Hcontext [Hwait [Henabled Hfields]]] Hreturn Hcontrol.
  pose proof (sem_pend_client_phase_context_return _ _ _ _ _ _ _ Hreturn Hcontext) as Hafter.
  split; [exact Hafter|]. split.
  - eapply sem_pend_clear_status_phase_wait_at_return;
      [exact Hwait|exact (proj1 Hcontext)|exact Hreturn|
       exact (proj1 (proj2 Hcontext))|exact (proj1 (proj2 Hafter))].
  - split; [eapply sem_pend_control_selection_enabled; eassumption|].
    eapply sem_pend_sched_client_return_caller_fields;
      [exact Hreturn|exact (proj1 Hcontext)|exact (proj1 (proj2 (proj2 Hcontext)))|
       exact (proj1 (proj2 Hcontext))|exact (proj1 Hwait)|exact Hfields].
Qed.

(** The C run is supplied by the checked literal SemPost body factory or
    its finite original-run composition. This producer keeps that exact
    run in the actual Save constructor and uses the actual Save suffix. *)
Lemma sem_pend_sched_save_from_scoped_run :
  forall environment critical local next_local active sg original mask initial observed eid timeout waiting
    call before first_heap private_input private_output private_before whole_before returned current environment_heap arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers final_registers whole_after
    (run : flag_pend_scoped_environment_run environment critical local next_local active sg
      call mask before whole_before private_input false returned current environment_heap private_output),
  sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting call before ->
  flag_pend_scoped_environment_source environment critical local next_local active sg None
    call mask before whole_before private_input false returned current environment_heap private_output run ->
  sem_pend_c_sequence_call_certificate
    (kernel_program_environment_c_step environment critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin))
    (sem_pend_environment_call_receipt environment critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin)
      (sem_pend_sem_post_c_step_certificate environment critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin)))
    _ _ _ _ _ _ _ run call.(os_sched_call_origin) returned.(os_sched_call_origin) ->
  flag_pend_caller_save_input environment critical local active sg (FlagPendTaskCaller call) call mask before first_heap ->
  private_input private_before -> join first_heap private_before whole_before ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current environment_heap
    final_registers current whole_after ->
  exists last_heap (actual : os_sched_continuation_c_save_execution environment critical local next_local active sg
    call mask before first_heap final_registers.(kernel_save_r0) false returned current last_heap),
    ((coq_prop (sem_pend_client_return_source environment critical sg call before returned current /\
        kernel_call_control_rely sg before current /\ interrupt_saved_value mask final_registers.(kernel_save_r0) /\
        sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting returned current) &&
      sem_pend_fields_masked environment next_local critical sg returned final_registers.(kernel_save_r0) current current) **
      active returned current) last_heap.
Proof.
  intros environment critical local next_local active sg original mask initial observed eid timeout waiting
    call before first_heap private_input private_output private_before whole_before returned current environment_heap
    arch save registers final_registers whole_after run Hentry Hsource Hcalls Hinput Hprivate Hjoin Hreturn_word
    Hvalid_word Hmask Hsuffix.
  destruct (flag_pend_scoped_environment_save_sequence environment critical local next_local active sg None
    call mask before whole_before private_input false returned current environment_heap private_output
    arch save registers final_registers whole_after run Hsource Hreturn_word Hvalid_word Hmask Hsuffix)
    as [Hsaved [completed Hcompleted]].
  pose proof (proj2 (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ completed)) as Houtput.
  destruct Houtput as [last_heap [private_after [Hjoin_after [Hcaller Hprivate_after]]]].
  pose (actual := @OsSchedContinuationCSave environment critical local next_local active sg call mask before first_heap
    private_input private_output private_before whole_before false returned current environment_heap arch save
    registers final_registers whole_after private_after last_heap run Hsource Hinput Hprivate Hjoin Hreturn_word
    Hvalid_word Hmask Hsuffix Hcaller Hprivate_after Hjoin_after).
  destruct (sem_pend_actual_save_control _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ actual
    (proj1 (proj2 (proj1 Hentry)))) as [Hnormal [Hcontrol [Henabled Howner]]].
  destruct (sem_pend_c_sequence_client_calls _ _ _ _ _ _ _ _
    (sem_pend_environment_call_receipt_client_calls environment critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin))
    _ _ _ _ _ _ _ run _ _ Hcalls) as [trace Htrace].
  assert (Hreturn : sem_pend_client_return_source environment critical sg call before returned current).
  { eapply sem_pend_client_return_source_from_legacy; eassumption. }
  pose proof (sem_pend_sched_entry_return _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hentry Hreturn Hcontrol) as Hentry'.
  pose proof (sem_pend_task_caller_masked _ _ _ _ _ _ _ _ _ last_heap Howner) as Hmasked.
  destruct Hmasked as [owned [rest [Hseparate [Hclosed Hactive]]]].
  exists last_heap, actual, owned, rest.
  exact (conj Hseparate (conj (conj (conj Hreturn (conj Hcontrol (conj Hsaved Hentry'))) Hclosed) Hactive)).
Qed.

(** The receipt is indexed by this actual Restore constructor and its inner
    run. The source is never selected again by matching its endpoints. *)
Lemma sem_pend_actual_restore_receipt_source : forall environment critical local next_local active sg call saved acquired
  before first_heap returned current last_heap actual,
  sem_pend_sem_post_restore_receipt environment critical local next_local active sg
    call saved acquired before first_heap false returned current last_heap actual ->
  kernel_call_task_source call before ->
  sem_pend_client_return_source environment critical sg call before returned current /\
  kernel_call_control_rely sg before current /\
  flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller call) call before returned current /\
  (sem_pend_fields_closed environment next_local sg returned (armv7a_irq_fiq_mask saved) current **
    active returned current) last_heap.
Proof.
  intros until actual; intros Hreceipt Hsource.
  destruct (sem_pend_restore_call_receipt_trace_resources _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hreceipt)
    as [trace [Hcalls [Hendpoint Howner]]].
  destruct (sem_pend_task_endpoint_control environment sg call before returned current Hsource Hendpoint) as [Hnormal Hcontrol].
  split.
  - eapply sem_pend_client_return_source_from_legacy; eassumption.
  - split; [exact Hcontrol|]. split; [exact Hendpoint|].
    exact (sem_pend_task_caller_closed _ _ _ _ _ _ _ _ last_heap Howner).
Qed.

Lemma sem_pend_waiting_restore_sched_input : forall environment critical local next_local active sg original mask
  initial observed eid timeout waiting call saved acquired before first_heap returned current last_heap actual,
  sem_pend_sem_post_restore_receipt environment critical local next_local active sg
    call saved acquired before first_heap false returned current last_heap actual ->
  sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting call before ->
  interrupt_saved_value mask saved ->
  ((coq_prop (sem_pend_client_return_source environment critical sg call before returned current /\
      kernel_call_control_rely sg before current) &&
    sem_pend_client_sched_input environment next_local critical sg original mask initial observed eid timeout
      waiting returned current) ** active returned current) last_heap.
Proof.
  intros until actual; intros Hreceipt [Hcontext [Hwait [Henabled Hfields]]] Hsaved.
  destruct (sem_pend_actual_restore_receipt_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hreceipt
    (proj1 (proj2 Hcontext))) as [Hreturn [Hcontrol [Hendpoint Howner]]].
  rewrite (proj2 Hsaved) in Howner.
  pose proof (sem_pend_client_phase_context_return _ _ _ _ _ _ _ Hreturn Hcontext) as Hafter.
  assert (Hentry : sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout
    waiting returned current).
  { split; [exact Hafter|]. split.
    - eapply sem_pend_clear_status_phase_wait_at_return;
        [exact Hwait|exact (proj1 Hcontext)|exact Hreturn|
         exact (proj1 (proj2 Hcontext))|exact (proj1 (proj2 Hafter))].
    - split; [eapply sem_pend_control_selection_enabled; eassumption|].
      eapply sem_pend_sched_client_return_caller_fields;
        [exact Hreturn|exact (proj1 Hcontext)|exact (proj1 (proj2 (proj2 Hcontext)))|
         exact (proj1 (proj2 Hcontext))|exact (proj1 Hwait)|exact Hfields]. }
  destruct Howner as [owned [rest [Hjoin [Hclosed Hactive]]]].
  exists owned, rest; exact (conj Hjoin (conj (conj (conj Hreturn Hcontrol) (conj Hentry Hclosed)) Hactive)).
Qed.

(** All four Scheduler body constructors remain inside the existing body
    observation. The concrete timeout association is supplied at its actual
    endpoint; no whole history receipt is added to the callee post. *)
Lemma sem_pend_sched_body_selected_endpoint : forall environment critical sg original mask initial observed eid timeout
  waiting call entry returned current,
  sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting call entry ->
  os_sched_task_body_observation environment critical sg call entry returned current ->
  UCOS2_state_inv sg current -> task_idle_ready sg current.(TskState) ->
  (forall node,
    current.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
    node.(statPend) = PendTimeout -> node.(eventPtr) = Some eid) ->
  sem_pend_client_phase_context sg returned current /\
  sem_pend_clear_status_phase_selected_at environment critical sg original mask initial observed eid timeout
    waiting returned current /\ os_sched_selection_enabled current = true.
Proof.
  intros environment critical sg original mask initial observed eid timeout waiting call entry returned current
    [Hcontext [Hwait [Henabled Hfields]]] [Hbody [Hready [Hnormal [Hcontrol Hsource]]]] Hvalid Hidle Htimeout.
  destruct Hcontext as [Hvalid_before [Hcall [Hrunning [Hidle_before [Havailable Hcache]]]]].
  specialize (Hsource Hcall).
  assert (Hsame : kernel_stack_call_same_call returned original).
  { pose proof (proj1 Hnormal) as Hreturn_same; pose proof (proj1 Hwait) as Hentry_same.
    unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence. }
  assert (Hmember : In original.(os_sched_call_stack).(stackLeaseSlot) current.(SchedState).(readyList)).
  { destruct Hready as [node [[Hnode [Hcur [Hpriority [Hmember Heffective]]]] Hgeneration]].
    rewrite <- (proj2 (proj2 Hsame)); exact Hmember. }
  destruct (sem_pend_returned_ready_waiter sg original returned current eid Hvalid Hsource Hsame Hmember Htimeout)
    as [node [Hresume [Hgeneration Hcont]]].
  assert (Hafter : sem_pend_client_phase_context sg returned current).
  { split; [exact Hvalid|]. split; [exact Hsource|]. split.
    - rewrite (proj1 Hcontrol); exact Hrunning.
    - split; [intro; exact Hidle|]. split; [exact (proj2 Hnormal Havailable)|].
      eapply os_sched_task_current_ready_current_consistency; exact Hready. }
  split; [exact Hafter|]. split; [|eapply sem_pend_control_selection_enabled; eassumption].
  split; [|exists node; exact Hresume].
  destruct Hwait as [Hsame_before [Hhistory [Hpath Hprevious]]].
  split; [exact Hsame|]. split; [exact Hhistory|]. split.
  - eapply SemPendClientWaitTrans; [exact Hpath|].
    eapply SemPendClientWaitScheduler; [exact Hsame_before|exact Hbody].
  - exists node; split; [exact (proj1 (proj2 (proj2 Hresume)))|exact Hcont].
Qed.

Lemma sem_pend_selected_current_ready : forall environment critical sg original mask initial observed eid timeout
  waiting call current,
  sem_pend_client_phase_context sg call current ->
  sem_pend_clear_status_phase_selected_at environment critical sg original mask initial observed eid timeout
    waiting call current -> flag_pend_current_ready call current.
Proof.
  intros environment critical sg original mask initial observed eid timeout waiting call current
    [Hvalid [Hsource [Hrunning [Hidle [Havailable Hcache]]]]] [Hwait [node Hresume]].
  destruct (kernel_call_task_source_current_at call current Hsource)
    as [Hcurrent [found [Hfound Hgen]]].
  assert (Hmember : In call.(os_sched_call_stack).(stackLeaseSlot) current.(SchedState).(readyList)).
  { rewrite (proj2 (proj2 (proj1 Hwait))); exact (proj2 (proj2 (proj2 (proj2 Hresume)))). }
  assert (Heffective : is_effectively_ready found.(stat) found.(dly) = true).
  { eapply sem_pend_ready_effective; eassumption. }
  unfold sched_current_consistency in Hcache; rewrite Hcurrent in Hcache.
  destruct Hcache as [same [Hsame Hpriority]]; assert (same = found) by congruence; subst same.
  exists found; exact (conj (conj Hfound (conj Hcurrent (conj Hpriority (conj Hmember Heffective)))) Hgen).
Qed.

Lemma sem_pend_sched_final_restore_output : forall environment critical local next_local active sg original mask initial
  observed eid timeout waiting call saved acquired released first_heap returned current last_heap actual,
  sem_pend_sem_post_restore_receipt environment critical local next_local active sg
    call saved acquired released first_heap false returned current last_heap actual ->
  sem_pend_client_phase_context sg call released ->
  sem_pend_clear_status_phase_selected_at environment critical sg original mask initial observed eid timeout
    waiting call released ->
  sem_pend_client_sched_caller_fields sg original released ->
  interrupt_saved_value mask saved ->
  ((coq_prop (sem_pend_client_return_source environment critical sg call released returned current /\
      kernel_call_control_rely sg released current /\ sem_pend_client_sched_caller_fields sg original current) &&
    sem_pend_clear_status_phase_save_input (SemPendWaitPhase original mask initial observed eid timeout waiting)
      environment next_local critical sg returned mask current) ** active returned current) last_heap.
Proof.
  intros until actual; intros Hreceipt Hcontext Hselected Hfields Hsaved.
  pose proof Hselected as [Hwait Hresume].
  destruct (sem_pend_actual_restore_receipt_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hreceipt
    (proj1 (proj2 Hcontext))) as [Hreturn [Hcontrol [Hendpoint Howner]]].
  rewrite (proj2 Hsaved) in Howner.
  pose proof (sem_pend_client_phase_context_return _ _ _ _ _ _ _ Hreturn Hcontext) as Hafter.
  pose proof (sem_pend_clear_status_phase_wait_at_return _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hwait (proj1 Hcontext) Hreturn (proj1 (proj2 Hcontext)) (proj1 (proj2 Hafter))) as Hwait'.
  pose proof (sem_pend_selected_current_ready _ _ _ _ _ _ _ _ _ _ _ _ Hcontext Hselected) as Hready_before.
  pose proof (proj1 Hendpoint (conj (proj1 (proj2 Hcontext)) Hready_before)) as Hready_after.
  assert (Hmember : In original.(os_sched_call_stack).(stackLeaseSlot) current.(SchedState).(readyList)).
  { destruct Hready_after as [node [[Hnode [Hcur [Hpriority [Hmember Heffective]]]] Hgen]].
    rewrite <- (proj2 (proj2 (proj1 Hwait'))); exact Hmember. }
  pose proof (sem_pend_clear_status_phase_selected_from_member _ _ _ _ _ _ _ _ _ _ _ _ Hwait' Hafter Hmember)
    as Hselected'.
  assert (Hpre : sem_pend_clear_status_phase_save_pre
    (SemPendWaitPhase original mask initial observed eid timeout waiting)
    environment critical sg returned mask current).
  { exact (conj Hafter (conj eq_refl Hselected')). }
  assert (Hfields' : sem_pend_client_sched_caller_fields sg original current).
  { eapply sem_pend_sched_client_return_caller_fields;
      [exact Hreturn|exact (proj1 Hcontext)|exact (proj1 (proj2 (proj2 Hcontext)))|
       exact (proj1 (proj2 Hcontext))|exact (proj1 Hwait)|exact Hfields]. }
  destruct Howner as [owned [rest [Hjoin [Hclosed Hactive]]]].
  exists owned, rest; exact (conj Hjoin (conj (conj (conj Hreturn (conj Hcontrol Hfields')) (conj Hpre Hclosed)) Hactive)).
Qed.

(** An actual literal SemPost between the Restore prefix and suffix supplies
    the receipt consumed here. No final phase, source or output owner is an
    input. The caller may still be blocked or suspended at this boundary. *)
Lemma sem_pend_sem_post_waiting_restore :
  forall environment critical local sg original mask initial observed eid timeout waiting
    call saved acquired entry first_heap (frame private : Assertion)
    private_before whole_before actor event node helper_returned environment_heap arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written prefix_heap final_cursor whole_after,
  sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting call entry ->
  interrupt_saved_value mask saved ->
  critical.(critical_region_clients) (sem_pend_post_source_client actor event) ->
  actor <> call.(os_sched_call_invocation) ->
  sem_post_lookup entry event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group entry node <> 0 -> event_object_layout_prop sg event ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical local (fun _ _ => frame) sg
    (FlagPendTaskCaller call) call saved acquired entry first_heap ->
  private private_before -> join first_heap private_before whole_before ->
  armv7a_restore_prefix_transition restore cursor whole_before written prefix_heap ->
  sem_post_waiter_execution sg (event_addr sg event) helper_returned prefix_heap environment_heap ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor whole_after ->
  exists selected old,
    let current := event_wake_state sg entry event node selected old PendSem 0 PendOK in
    exists last_heap (actual : os_sched_continuation_c_restore_execution environment critical local local (fun _ _ => frame) sg
      call saved acquired entry first_heap false call current last_heap),
    sem_pend_sem_post_restore_receipt environment critical local local (fun _ _ => frame) sg
      call saved acquired entry first_heap false call current last_heap actual /\
    ((coq_prop (sem_pend_client_return_source environment critical sg call entry call current /\
        kernel_call_control_rely sg entry current) &&
      sem_pend_client_sched_input environment local critical sg original mask initial observed eid timeout
        waiting call current) ** frame) last_heap /\
    (sem_pend_clear_status_phase_selected_at environment critical sg original mask initial observed eid timeout
      waiting call entry ->
      ((coq_prop (sem_pend_client_return_source environment critical sg call entry call current /\
          kernel_call_control_rely sg entry current /\ sem_pend_client_sched_caller_fields sg original current) &&
        sem_pend_clear_status_phase_save_input (SemPendWaitPhase original mask initial observed eid timeout waiting)
          environment local critical sg call mask current) ** frame) last_heap).
Proof.
  intros environment critical local sg original mask initial observed eid timeout waiting call saved acquired entry first_heap
    frame private private_before whole_before actor event node helper_returned environment_heap arch restore
    cursor written prefix_heap final_cursor whole_after Hentry Hsaved Hmember Hforeign Hlookup Htype Hgroup Hlayout
    Hr0 Hmask Hinput Hprivate Hjoin Hprefix Hstep Hsuffix.
  destruct (sem_pend_sem_post_selected_restore environment critical local sg call saved acquired entry first_heap
    frame private private_before whole_before actor event node helper_returned environment_heap arch restore
    cursor written prefix_heap final_cursor whole_after Hmember Hforeign Hlookup Htype Hgroup Hlayout
    Hr0 Hmask Hinput Hprivate Hjoin Hprefix Hstep Hsuffix)
    as [selected [old [last_heap [actual [Hreceipt Hpost]]]]].
  exists selected, old, last_heap, actual; split; [exact Hreceipt|]. split.
  - exact (sem_pend_waiting_restore_sched_input environment critical local local (fun _ _ => frame) sg
      original mask initial observed eid timeout waiting call saved acquired entry first_heap call
      (event_wake_state sg entry event node selected old PendSem 0 PendOK) last_heap actual
      Hreceipt Hentry Hsaved).
  - intro Hselected.
    exact (sem_pend_sched_final_restore_output environment critical local local (fun _ _ => frame) sg
      original mask initial observed eid timeout waiting call saved acquired entry first_heap call
      (event_wake_state sg entry event node selected old PendSem 0 PendOK) last_heap actual
      Hreceipt (proj1 Hentry) Hselected (proj2 (proj2 (proj2 Hentry))) Hsaved).
Qed.

Lemma sem_pend_sched_restore_output_compose : forall environment critical sg original mask initial observed eid timeout
  waiting call before scheduled acquired resumed released,
  sem_pend_client_return_source environment critical sg call before scheduled acquired ->
  kernel_call_control_rely sg before acquired ->
  os_sched_task_body_observation environment critical sg scheduled acquired resumed released ->
  sem_pend_client_sched_restore_output environment critical sg original mask initial observed eid timeout
    waiting resumed released |--
  sem_pend_client_sched_output environment critical sg original mask initial observed eid timeout waiting call before.
Proof.
  intros environment critical sg original mask initial observed eid timeout waiting call before scheduled acquired resumed released
    Hsave Hsave_control [Hbody [Hready [Hbody_normal [Hbody_control Hbody_source]]]] heap
    [returned [current [next_local [[Hrestore [Hrestore_control Hfields]] Hpost]]]].
  exists returned, current, next_local; split; [|exact Hpost].
  split.
  - pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hsave) as Hfirst.
    pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hrestore) as Hlast.
    pose proof (proj1 Hbody_normal) as Hmiddle.
    unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence.
  - split; [|exact Hfields].
    eapply kernel_call_control_rely_trans; [exact Hsave_control|].
    eapply kernel_call_control_rely_trans; eassumption.
Qed.

Lemma sem_pend_uninterrupted_waiting_restore : forall environment local critical sg original mask initial observed eid timeout
  waiting call saved acquired checkpoint arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  cursor before written middle final_cursor after (frame : Assertion),
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  os_sched_selection_enabled checkpoint = true -> sem_pend_client_sched_caller_fields sg original checkpoint ->
  (sem_pend_clear_status_phase_restore_input
    (SemPendWaitPhase original mask initial observed eid timeout waiting)
    environment local critical sg call mask saved acquired checkpoint ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  ((coq_prop (sem_pend_client_return_source environment critical sg call checkpoint call checkpoint /\
      kernel_call_control_rely sg checkpoint checkpoint) &&
    sem_pend_client_sched_input environment local critical sg original mask initial observed eid timeout
      waiting call checkpoint) ** frame) after.
Proof.
  intros environment local critical sg original mask initial observed eid timeout waiting call saved acquired checkpoint
    arch restore cursor before written middle final_cursor after frame Hr0 Hmask Henabled Hfields Hinput Hprefix Hsuffix.
  destruct Hinput as [owned [rest [Hjoin [[Hpure Hmasked] Hframe]]]].
  destruct Hpure as [Hsaved [Hsame_mask [Hcontext Hwait]]].
  assert (Howned : (sem_pend_fields_masked environment local critical sg call saved acquired checkpoint ** frame) before).
  { exists owned, rest; exact (conj Hjoin (conj Hmasked Hframe)). }
  destruct (kernel_continuation_call_uninterrupted_restore _ _ _ _ arch environment.(task_stack_call_continuations)
    restore kernel_program_fields_inv local sg (task_stack_call_active_key call) call saved acquired checkpoint
    cursor before written middle final_cursor after frame Hr0 Hmask Howned Hprefix Hsuffix)
    as [Hexecution [Hvalue Hclosed]].
  rewrite (proj2 Hsaved) in Hclosed.
  destruct Hclosed as [final_owned [final_rest [Hfinal_join [Hfinal Hfinal_frame]]]].
  split; [exact Hexecution|]. split; [exact Hvalue|].
  exists final_owned, final_rest; split; [exact Hfinal_join|]. split; [|exact Hfinal_frame].
  split.
  - split; [apply sem_pend_client_return_source_refl|]. unfold kernel_call_control_rely; auto.
  - exact (conj (conj Hcontext (conj Hwait (conj Henabled Hfields))) Hfinal).
Qed.
