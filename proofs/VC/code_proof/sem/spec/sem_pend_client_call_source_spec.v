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

Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_sched_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_critical_observed_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_critical_restore_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_clear_status_spec.
Import CriticalComponent.

(** Private evidence for the same environment step. The constructors
    retain existing typed modular call outputs; they do not classify every
    member of the wider environment union. No physical owner is relabelled. *)
Section SemPendClientCallAttachments.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (observer : nat) (origin : TaskInvocationOrigin).
Let segment := kernel_program_environment_c_step environment critical sg observer origin.

Inductive sem_pend_client_environment_call_receipt :
  forall state before input stopped current after output,
  segment state before input stopped current after output -> TaskInvocationOrigin -> TaskInvocationOrigin -> Prop :=
| SemPendClientSemPostCall : forall state before input stopped current after output step first last,
  sem_pend_environment_call_receipt environment critical sg observer origin
    (sem_pend_sem_post_c_step_certificate environment critical sg observer origin)
    state before input stopped current after output step first last ->
  sem_pend_client_environment_call_receipt state before input stopped current after output step first last
| SemPendClientCriticalCall : forall state before input stopped current after output step first last,
  sem_pend_environment_call_receipt environment critical sg observer origin
    (sem_pend_critical_observed_call_receipt environment critical sg observer origin)
    state before input stopped current after output step first last ->
  sem_pend_client_environment_call_receipt state before input stopped current after output step first last.

Lemma sem_pend_sem_post_environment_call_certificate : forall state before input stopped current after output run first last,
  sem_pend_c_sequence_call_certificate segment
    (sem_pend_environment_call_receipt environment critical sg observer origin
      (sem_pend_sem_post_c_step_certificate environment critical sg observer origin))
    state before input stopped current after output run first last ->
  sem_pend_c_sequence_call_certificate segment sem_pend_client_environment_call_receipt
    state before input stopped current after output run first last.
Proof.
  intros until last; intro Hcalls; induction Hcalls.
  - constructor.
  - apply SemPendCSequenceCallAtom, SemPendClientSemPostCall; exact H.
  - econstructor; eassumption.
  - econstructor; eassumption.
Qed.

Lemma sem_pend_critical_environment_call_certificate : forall state before input stopped current after output run first last,
  sem_pend_c_sequence_call_certificate segment
    (sem_pend_environment_call_receipt environment critical sg observer origin
      (sem_pend_critical_observed_call_receipt environment critical sg observer origin))
    state before input stopped current after output run first last ->
  sem_pend_c_sequence_call_certificate segment sem_pend_client_environment_call_receipt
    state before input stopped current after output run first last.
Proof.
  intros until last; intro Hcalls; induction Hcalls.
  - constructor.
  - apply SemPendCSequenceCallAtom, SemPendClientCriticalCall; exact H.
  - econstructor; eassumption.
  - econstructor; eassumption.
Qed.

Lemma sem_pend_client_environment_call_trace : forall state before input stopped current after output step first last,
  sem_pend_client_environment_call_receipt state before input stopped current after output step first last ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer None first state stopped last current.
Proof.
  intros until last; intro Hreceipt; destruct Hreceipt.
  - destruct (sem_pend_environment_call_receipt_client_calls _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H)
      as [trace Hcalls].
    eapply SemPendObservedLegacy; exact Hcalls.
  - destruct H; destruct H.
    eapply sem_pend_critical_call_receipt_observed_trace; eassumption.
Qed.

Lemma sem_pend_client_environment_sequence_trace : forall state before input stopped current after output run first last,
  sem_pend_c_sequence_call_certificate segment sem_pend_client_environment_call_receipt
    state before input stopped current after output run first last ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer None first state stopped last current.
Proof.
  intros until last; intro Hcalls.
  eapply sem_pend_observed_c_sequence_trace; [exact sem_pend_client_environment_call_trace|exact Hcalls].
Qed.
End SemPendClientCallAttachments.

(** The actual acquired API completion supplies both its own owner and
    the attachment consumed above. The observer descriptor is unchanged;
    the API owner remains the API owner, including Generic execution views. *)
Lemma sem_pend_critical_completion_call_attachment :
  forall environment critical local sg frame call before after observed,
  critical.(critical_region_clients) (sem_pend_critical_call_action call) ->
  kernel_critical_c_completion environment critical local sg frame call before after ->
  exists run : kernel_c_sequence (kernel_program_c_step environment critical sg
      observed.(os_sched_call_invocation) observed.(os_sched_call_origin))
    (kernel_critical_c_entry call) before
    (kernel_critical_c_owner environment critical local sg call (kernel_critical_c_entry call) ** frame)
    false (kernel_critical_c_returned call) after
    (kernel_critical_c_owner environment critical local sg call (kernel_critical_c_returned call) ** frame),
    let included := sem_pend_selected_environment_sequence environment critical sg
      observed.(os_sched_call_invocation) observed.(os_sched_call_origin) _ _ _ _ _ _ _ run in
    kernel_program_environment_c_sequence_source environment critical sg
      observed.(os_sched_call_invocation) observed.(os_sched_call_origin) None _ _ _ _ _ _ _ included /\
    sem_pend_c_sequence_call_certificate _
      (sem_pend_client_environment_call_receipt environment critical sg
        observed.(os_sched_call_invocation) observed.(os_sched_call_origin))
      _ _ _ _ _ _ _ included observed.(os_sched_call_origin) observed.(os_sched_call_origin) /\
    sem_pend_client_return_source environment critical sg observed (kernel_critical_c_entry call)
      observed (kernel_critical_c_returned call) /\
    (kernel_critical_c_owner environment critical local sg call (kernel_critical_c_returned call) ** frame) after.
Proof.
  intros environment critical local sg frame call before after observed Hmember Hcompletion.
  destruct (sem_pend_critical_completion_observed_source environment critical local sg frame call
    before after observed Hmember Hcompletion)
    as [run [Hbase [Hsource [Hcalls [Hreturn Howner]]]]].
  exists run; split; [exact Hsource|]. split.
  - eapply sem_pend_critical_environment_call_certificate; exact Hcalls.
  - exact (conj Hreturn Howner).
Qed.

(** Save rely is obtained from the completed call's endpoint observation
    and the same client-return trace. In particular it is conditional on
    the caller being ready before Save; suspended callers are not excluded. *)
Lemma sem_pend_client_endpoint_save_rely : forall environment critical sg call before returned current,
  sem_pend_client_phase_context sg call before ->
  sem_pend_client_return_source environment critical sg call before returned current ->
  flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller call) call before returned current ->
  sem_pend_save_rely sg before current.
Proof.
  intros environment critical sg call before returned current Hcontext Hreturn Hendpoint.
  pose proof (sem_pend_client_phase_context_return _ _ _ _ _ _ _ Hreturn Hcontext)
    as Hafter.
  destruct Hcontext as [Hvalid [Hsource [Hrunning [Hidle [Havailable Hcache]]]]].
  destruct Hafter as [Hvalid' [Hsource' [Hrunning' [Hidle' [Havailable' Hcache']]]]].
  destruct (sem_pend_task_endpoint_control _ _ _ _ _ _ Hsource Hendpoint) as [Hnormal Hcontrol].
  unfold sem_pend_save_rely; split; [exact Hcontrol|].
  split; [intros _; exact Hidle'|]. split; [intros _; exact Hcache'|].
  intros tid Hcurrent Hmember.
  destruct (kernel_call_task_source_current_at call before Hsource)
    as [Hcur [node [Hnode Hgen]]].
  assert (tid = call.(os_sched_call_stack).(stackLeaseSlot)) by congruence; subst tid.
  assert (Hready : flag_pend_current_ready call before).
  { unfold sched_current_consistency in Hcache; rewrite Hcur in Hcache.
    destruct Hcache as [same [Hsame Hpriority]]. assert (same = node) by congruence; subst same.
    exists node; split; [|exact Hgen].
    exact (conj Hnode (conj Hcur (conj Hpriority (conj Hmember
      (sem_pend_ready_effective sg before _ node Hvalid Hnode Hmember))))). }
  destruct (proj1 Hendpoint (conj Hsource Hready))
    as [node' [[Hnode' [Hcur' [Hpriority' [Hmember' Heffective']]]] Hgen']].
  pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hreturn) as [_ [_ Hstack]].
  rewrite Hstack in Hmember'; exact Hmember'.
Qed.

Inductive sem_pend_client_restore_call_receipt environment critical local next_local active sg
  original saved acquired before first_heap :
  forall stopped returned current last_heap,
  os_sched_continuation_c_restore_execution environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap -> Prop :=
| SemPendClientRestoreCallReceipt :
  forall private_input private_output private_before whole_before stopped returned current environment_heap arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written prefix_heap final_cursor whole_after private_after last_heap
    (run : flag_pend_scoped_environment_run environment critical local next_local active sg
      original (armv7a_irq_fiq_mask saved) before prefix_heap private_input
      stopped returned current environment_heap private_output),
  forall
    (Hr0 : cursor.(kernel_restore_r0) = saved)
    (Hmask : armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192)
    (Hinput : flag_pend_caller_restore_input environment critical local active sg
      (FlagPendTaskCaller original) original saved acquired before first_heap)
    (Hprivate : private_input private_before)
    (Hjoin : join first_heap private_before whole_before)
    (Hprefix : armv7a_restore_prefix_transition restore cursor whole_before written prefix_heap)
    (Hsource : flag_pend_scoped_environment_source environment critical local next_local active sg None
      original (armv7a_irq_fiq_mask saved) before prefix_heap private_input
      stopped returned current environment_heap private_output run)
    (Hsuffix : armv7a_restore_suffix_transition restore written environment_heap final_cursor whole_after)
    (Houtput : (coq_prop (flag_pend_call_endpoint_observations environment sg
      (FlagPendTaskCaller original) original before returned current) &&
      flag_pend_caller_save_input environment critical next_local active sg
        (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current) last_heap)
    (Hprivate_after : private_output private_after)
    (Hjoin_after : join last_heap private_after whole_after),
  sem_pend_c_sequence_call_certificate
    (kernel_program_environment_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
    (sem_pend_client_environment_call_receipt environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    _ _ _ _ _ _ _ run original.(os_sched_call_origin) returned.(os_sched_call_origin) ->
  sem_pend_client_restore_call_receipt environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap
    (@OsSchedContinuationCRestore environment critical local next_local active sg original saved acquired before first_heap
      private_input private_output private_before whole_before stopped returned current environment_heap arch restore
      cursor written prefix_heap final_cursor whole_after private_after last_heap run
      Hr0 Hmask Hinput Hprivate Hjoin Hprefix Hsource Hsuffix Houtput Hprivate_after Hjoin_after).

Lemma sem_pend_sem_post_restore_call_attachment :
  forall environment critical local next_local active sg original saved acquired before first_heap
    stopped returned current last_heap actual,
  sem_pend_sem_post_restore_receipt environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap actual ->
  sem_pend_client_restore_call_receipt environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap actual.
Proof.
  intros until actual; intro Hreceipt; destruct Hreceipt.
  constructor; eapply sem_pend_sem_post_environment_call_certificate; exact H.
Qed.

Lemma sem_pend_client_restore_from_environment_calls :
  forall environment critical local next_local active sg original saved acquired before first_heap
    private_input private_output private_before whole_before stopped returned current environment_heap arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written prefix_heap final_cursor whole_after
    (run : flag_pend_scoped_environment_run environment critical local next_local active sg
      original (armv7a_irq_fiq_mask saved) before prefix_heap private_input
      stopped returned current environment_heap private_output),
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before first_heap ->
  private_input private_before -> join first_heap private_before whole_before ->
  armv7a_restore_prefix_transition restore cursor whole_before written prefix_heap ->
  flag_pend_scoped_environment_source environment critical local next_local active sg None
    original (armv7a_irq_fiq_mask saved) before prefix_heap private_input
    stopped returned current environment_heap private_output run ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor whole_after ->
  sem_pend_c_sequence_call_certificate
    (kernel_program_environment_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
    (sem_pend_client_environment_call_receipt environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    _ _ _ _ _ _ _ run original.(os_sched_call_origin) returned.(os_sched_call_origin) ->
  exists last_heap (actual : os_sched_continuation_c_restore_execution environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap),
  sem_pend_client_restore_call_receipt environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap actual.
Proof.
  intros environment critical local next_local active sg original saved acquired before first_heap
    private_input private_output private_before whole_before stopped returned current environment_heap arch restore
    cursor written prefix_heap final_cursor whole_after run Hr0 Hmask Hinput Hprivate Hjoin Hprefix Hsource Hsuffix Hcalls.
  assert (Hwhole : (flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before ** private_input) whole_before).
  { exists first_heap, private_before; exact (conj Hjoin (conj Hinput Hprivate)). }
  destruct (flag_pend_scoped_environment_restore_sequence environment critical local next_local active sg None
    original saved acquired before whole_before private_input stopped returned current environment_heap private_output
    arch restore cursor written prefix_heap final_cursor whole_after run Hr0 Hmask Hwhole Hprefix Hsource Hsuffix)
    as [completed Hcompleted_source].
  pose proof (proj2 (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ completed)) as Houtput.
  destruct Houtput as [last_heap [private_after [Hjoin_after [Hcaller_after Hprivate_after]]]].
  exists last_heap, (@OsSchedContinuationCRestore environment critical local next_local active sg
    original saved acquired before first_heap private_input private_output private_before whole_before
    stopped returned current environment_heap arch restore cursor written prefix_heap final_cursor whole_after
    private_after last_heap run Hr0 Hmask Hinput Hprivate Hjoin Hprefix Hsource Hsuffix
    Hcaller_after Hprivate_after Hjoin_after).
  constructor; exact Hcalls.
Qed.

Lemma sem_pend_client_restore_call_trace_resources :
  forall environment critical local next_local active sg original saved acquired before first_heap
    stopped returned current last_heap actual,
  sem_pend_client_restore_call_receipt environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap actual ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    before stopped returned.(os_sched_call_origin) current /\
    (coq_prop (flag_pend_call_endpoint_observations environment sg
      (FlagPendTaskCaller original) original before returned current) &&
      flag_pend_caller_save_input environment critical next_local active sg
        (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current) last_heap.
Proof.
  intros until actual; intro Hreceipt; destruct Hreceipt.
  split; [eapply sem_pend_client_environment_sequence_trace; exact H|exact Houtput].
Qed.

Lemma sem_pend_client_actual_restore_source : forall environment critical local next_local active sg call saved acquired
  before first_heap returned current last_heap actual,
  sem_pend_client_restore_call_receipt environment critical local next_local active sg
    call saved acquired before first_heap false returned current last_heap actual ->
  kernel_call_task_source call before ->
  sem_pend_client_return_source environment critical sg call before returned current /\
  kernel_call_control_rely sg before current /\
  flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller call) call before returned current /\
  (sem_pend_fields_closed environment next_local sg returned (armv7a_irq_fiq_mask saved) current **
    active returned current) last_heap.
Proof.
  intros until actual; intros Hreceipt Hsource.
  destruct (sem_pend_client_restore_call_trace_resources _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hreceipt)
    as [Htrace [Hendpoint Howner]].
  destruct (sem_pend_task_endpoint_control environment sg call before returned current Hsource Hendpoint) as [Hnormal Hcontrol].
  split.
  - exact (conj Htrace Hnormal).
  - split; [exact Hcontrol|]. split; [exact Hendpoint|].
    exact (sem_pend_task_caller_closed _ _ _ _ _ _ _ _ last_heap Howner).
Qed.

Lemma sem_pend_client_waiting_restore_sched_input : forall environment critical local next_local active sg original mask
  initial observed eid timeout waiting call saved acquired before first_heap returned current last_heap actual,
  sem_pend_client_restore_call_receipt environment critical local next_local active sg
    call saved acquired before first_heap false returned current last_heap actual ->
  sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting call before ->
  interrupt_saved_value mask saved ->
  ((coq_prop (sem_pend_client_return_source environment critical sg call before returned current /\
      kernel_call_control_rely sg before current) &&
    sem_pend_client_sched_input environment next_local critical sg original mask initial observed eid timeout
      waiting returned current) ** active returned current) last_heap.
Proof.
  intros until actual; intros Hreceipt [Hcontext [Hwait [Henabled Hfields]]] Hsaved.
  destruct (sem_pend_client_actual_restore_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hreceipt
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

Lemma sem_pend_client_final_restore_save_input : forall environment critical local next_local active sg original mask initial
  observed eid timeout waiting call saved acquired released first_heap returned current last_heap actual,
  sem_pend_client_restore_call_receipt environment critical local next_local active sg
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
  destruct (sem_pend_client_actual_restore_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hreceipt
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

Lemma sem_pend_client_save_from_scoped_calls :
  forall environment critical local next_local active sg mask call before first_heap private_input private_output private_before whole_before returned current environment_heap arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers final_registers whole_after
    (run : flag_pend_scoped_environment_run environment critical local next_local active sg
      call mask before whole_before private_input false returned current environment_heap private_output),
  sem_pend_client_phase_context sg call before ->
  flag_pend_scoped_environment_source environment critical local next_local active sg None
    call mask before whole_before private_input false returned current environment_heap private_output run ->
  sem_pend_c_sequence_call_certificate
    (kernel_program_environment_c_step environment critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin))
    (sem_pend_client_environment_call_receipt environment critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin))
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
        sem_pend_save_rely sg before current) &&
      sem_pend_fields_masked environment next_local critical sg returned final_registers.(kernel_save_r0) current current) **
      active returned current) last_heap.
Proof.
  intros environment critical local next_local active sg mask call before first_heap private_input private_output private_before whole_before returned current environment_heap
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
    (proj1 (proj2 Hentry))) as [Hnormal [Hcontrol [Henabled Howner]]].
  pose proof (sem_pend_client_environment_sequence_trace _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcalls) as Htrace.
  assert (Hreturn : sem_pend_client_return_source environment critical sg call before returned current)
    by exact (conj Htrace Hnormal).
  pose proof (proj1 (proj2 (os_sched_continuation_c_save_execution_resources
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ actual))) as Hendpoint.
  pose proof (sem_pend_client_endpoint_save_rely _ _ _ _ _ _ _ Hentry Hreturn Hendpoint) as Hentry'.
  pose proof (sem_pend_task_caller_masked _ _ _ _ _ _ _ _ _ last_heap Howner) as Hmasked.
  destruct Hmasked as [owned [rest [Hseparate [Hclosed Hactive]]]].
  exists last_heap, actual, owned, rest.
  exact (conj Hseparate (conj (conj (conj Hreturn (conj Hcontrol (conj Hsaved Hentry'))) Hclosed) Hactive)).
Qed.

(** This is the first and second OSSemPend Save consumer. The phase
    parameter retains Acquire/Wait/Return cases; Return has the existing
    impossible input. The post uses the very same returned/acquired/local. *)
Lemma sem_pend_client_saved_phase_output : forall phase environment critical local active sg
  call returned mask saved before acquired heap,
  sem_pend_clear_status_phase_save_pre phase environment critical sg call mask before ->
  ((coq_prop (sem_pend_client_return_source environment critical sg call before returned acquired /\
      kernel_call_control_rely sg before acquired /\ interrupt_saved_value mask saved /\
      sem_pend_save_rely sg before acquired) &&
    sem_pend_fields_masked environment local critical sg returned saved acquired acquired) ** active returned acquired) heap ->
  (sem_pend_clear_status_phase_save_output phase environment local critical sg call mask saved before **
    active returned acquired) heap.
Proof.
  intros phase environment critical local active sg call returned mask saved before acquired heap Hpre
    [owned [rest [Hjoin [[Hfacts Howner] Hactive]]]].
  destruct Hfacts as [Hreturn [Hcontrol [Hsaved Hrely]]].
  exists owned, rest; split; [exact Hjoin|]. split; [|exact Hactive].
  exact (sem_pend_clear_status_phase_save_output_intro _ _ _ _ _ _ _ _ _ _ _
    Hpre Hreturn Hsaved Hrely owned Howner).
Qed.

Lemma sem_pend_client_restore_phase_output : forall phase environment critical local next_local active sg
  call mask saved acquired before first_heap returned current last_heap actual,
  sem_pend_client_restore_call_receipt environment critical local next_local active sg
    call saved acquired before first_heap false returned current last_heap actual ->
  sem_pend_client_phase_context sg call before ->
  sem_pend_clear_status_phase_restore_pre phase environment critical sg call mask before ->
  interrupt_saved_value mask saved ->
  (sem_pend_clear_status_phase_restore_output phase environment next_local critical sg call mask before **
    active returned current) last_heap.
Proof.
  intros until actual; intros Hreceipt Hcontext Hpre Hsaved.
  destruct (sem_pend_client_actual_restore_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hreceipt
    (proj1 (proj2 Hcontext))) as [Hreturn [Hcontrol [Hendpoint Howner]]].
  rewrite (proj2 Hsaved) in Howner.
  assert (Hphase : sem_pend_clear_status_phase_restore_observation phase environment critical sg call before returned current).
  { destruct phase.
    - contradiction.
    - destruct Hpre as [_ [Hcontext' Hwait]].
      eapply sem_pend_clear_status_phase_wait_restore_observation; eassumption.
    - eapply sem_pend_clear_status_phase_return_restore_observation; eassumption. }
  destruct Howner as [owned [rest [Hjoin [Hclosed Hactive]]]].
  exists owned, rest; split; [exact Hjoin|]. split; [|exact Hactive].
  exists returned, current; exact (conj (conj Hreturn Hphase) Hclosed).
Qed.
