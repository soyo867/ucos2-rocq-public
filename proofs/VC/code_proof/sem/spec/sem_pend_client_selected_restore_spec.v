Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt Ucos2Verify.lib.event Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_phase_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_wake_status_idle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_pending_stack_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_event_ready_source_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_restore_body_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations PrimitiveComponent.
Import SelectedReturnPrimitive SelectedCompletionSource SelectedCProgram SelectedCSource.
Import SelectedIRQWrapperSegment SelectedIRQWrapperSource SelectedReturnedCProgram SelectedReturnedCSource.
Import SelectedEnvironmentCProgram SelectedEnvironmentCSource SelectedEnvironmentScopedSource.
Import SelectedEnvironmentScopedEnvironment SelectedEnvironmentScopedPrimitives SelectedEnvironmentPhaseEffects.
Import SelectedLocalRecovery SelectedIdleWakeStatus SemPendEventReadySource.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A receipt for an actual constructor injection. It cannot be attached
    to another target step with merely the same endpoints. *)
Inductive sem_pend_injected_call_receipt (source target : KernelCSegmentRelation)
  (inject : forall state before input stopped current after output,
    source state before input stopped current after output ->
    target state before input stopped current after output)
  (receipt : forall state before input stopped current after output,
    source state before input stopped current after output ->
    TaskInvocationOrigin -> TaskInvocationOrigin -> Prop) :
  forall state before input stopped current after output,
    target state before input stopped current after output ->
    TaskInvocationOrigin -> TaskInvocationOrigin -> Prop :=
| SemPendInjectedCallReceipt : forall state before input stopped current after output step first last,
    receipt state before input stopped current after output step first last ->
    sem_pend_injected_call_receipt source target inject receipt _ _ _ _ _ _ _
      (inject state before input stopped current after output step) first last.

Section SemPendSelectedInjection.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (observer : nat) (origin : TaskInvocationOrigin).
Let base := kernel_program_c_step environment critical sg observer origin.
Let selected := kernel_program_selected_c_step environment critical sg observer origin.
Let scoped := kernel_program_environment_c_step environment critical sg observer origin.
Context (leaf : forall state before input stopped current after output,
  base state before input stopped current after output -> TaskInvocationOrigin -> TaskInvocationOrigin -> Prop).

Definition sem_pend_selected_call_receipt := sem_pend_injected_call_receipt base selected
  (kernel_program_selected_original_step environment critical sg observer origin) leaf.

Definition sem_pend_selected_environment_step state before input stopped current after output
  (step : selected state before input stopped current after output) :
  scoped state before input stopped current after output :=
  @KernelProgramEnvironmentBody environment critical sg observer origin _ _ _ _ _ _ _
    (@KernelProgramReturnedWrapper environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramWrapperOriginal environment critical sg observer origin _ _ _ _ _ _ _ step)).

Definition sem_pend_environment_call_receipt := sem_pend_injected_call_receipt selected scoped
  sem_pend_selected_environment_step sem_pend_selected_call_receipt.

(** A transparent structural map using the existing single-step injection.
    No opaque endpoint-only sequence inclusion is inverted. *)
Definition sem_pend_selected_sequence state before input stopped current after output
  (run : kernel_c_sequence base state before input stopped current after output) :
  kernel_c_sequence selected state before input stopped current after output.
Proof.
  induction run.
  - constructor; exact H.
  - apply KernelCSequenceAtom, kernel_program_selected_original_step; exact H.
  - eapply KernelCSequenceThen; eassumption.
  - eapply KernelCSequenceAdapt; eassumption.
Defined.

Definition sem_pend_selected_environment_sequence state before input stopped current after output
  (run : kernel_c_sequence base state before input stopped current after output) :
  kernel_c_sequence scoped state before input stopped current after output :=
  kernel_program_environment_sequence_include _ _ _ _ _ _ _ _ _ _ _ _
    (kernel_program_returned_sequence_include _ _ _ _ _ _ _ _ _ _ _ _
      (kernel_program_wrapper_sequence_include _ _ _ _ _ _ _ _ _ _ _ _
        (sem_pend_selected_sequence _ _ _ _ _ _ _ run))).

Lemma sem_pend_selected_sequence_certificate : forall state before input stopped current after output run first last,
  sem_pend_c_sequence_call_certificate base leaf state before input stopped current after output run first last ->
  sem_pend_c_sequence_call_certificate selected sem_pend_selected_call_receipt _ _ _ _ _ _ _
    (sem_pend_selected_sequence _ _ _ _ _ _ _ run) first last.
Proof.
  intros until last; intro Hcertificate; induction Hcertificate; cbn [sem_pend_selected_sequence].
  - constructor.
  - apply SemPendCSequenceCallAtom, SemPendInjectedCallReceipt; exact H.
  - econstructor; eassumption.
  - econstructor; eassumption.
Qed.


Lemma sem_pend_selected_environment_sequence_certificate : forall state before input stopped current after output run first last,
  sem_pend_c_sequence_call_certificate base leaf state before input stopped current after output run first last ->
  sem_pend_c_sequence_call_certificate scoped sem_pend_environment_call_receipt _ _ _ _ _ _ _
    (sem_pend_selected_environment_sequence _ _ _ _ _ _ _ run) first last.
Proof.
  intros until last; intro Hcertificate; induction Hcertificate;
    cbn [sem_pend_selected_environment_sequence sem_pend_selected_sequence
      kernel_program_environment_sequence_include kernel_program_returned_sequence_include
      kernel_program_wrapper_sequence_include].
  - constructor.
  - apply SemPendCSequenceCallAtom.
    exact (@SemPendInjectedCallReceipt selected scoped sem_pend_selected_environment_step
      sem_pend_selected_call_receipt state before input stopped returned after output
      (kernel_program_selected_original_step environment critical sg observer origin
        state before input stopped returned after output step) first last
      (@SemPendInjectedCallReceipt base selected
        (kernel_program_selected_original_step environment critical sg observer origin)
        leaf state before input stopped returned after output step first last H)).
  - econstructor; eassumption.
  - econstructor; eassumption.
Qed.
End SemPendSelectedInjection.

Lemma sem_pend_environment_call_receipt_client_calls : forall environment critical sg observer origin
  state before input stopped current after output step first last,
  sem_pend_environment_call_receipt environment critical sg observer origin
    (sem_pend_sem_post_c_step_certificate environment critical sg observer origin)
    state before input stopped current after output step first last ->
  exists trace : kernel_client_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
      first state stopped last current,
    sem_pend_client_source_calls environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical.(critical_region_clients) sg observer None first state stopped last current trace.
Proof.
  intros environment critical sg observer origin state before input stopped current after output step first last Hreceipt.
  destruct Hreceipt; destruct H.
  eapply sem_pend_sem_post_c_step_client_calls; eassumption.
Qed.

Lemma sem_pend_sem_post_environment_source : forall environment critical sg observer origin
  state before input stopped current after output run first last,
  sem_pend_c_sequence_call_certificate (kernel_program_c_step environment critical sg observer origin)
    (sem_pend_sem_post_c_step_certificate environment critical sg observer origin)
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
    left; constructor.
  - econstructor; eassumption.
  - econstructor; eassumption.
Qed.

(** Only the existing Wake component facts are used here. General selected
    Idle markers and their IRQ transport remain in their own module. *)
Lemma sem_pend_sem_post_body_observations : forall environment critical sg observer origin call
  state before input stopped current after output run first last,
  sem_pend_c_sequence_call_certificate (kernel_program_c_step environment critical sg observer origin)
    (sem_pend_sem_post_c_step_certificate environment critical sg observer origin)
    state before input stopped current after output run first last ->
  (flag_pend_current_ready call state -> flag_pend_current_ready call current) /\
  (task_idle_ready sg state.(TskState) -> task_idle_ready sg current.(TskState)) /\
  (flag_pend_non_idle_at sg call state -> flag_pend_non_idle_at sg call current) /\
  kernel_call_control_rely sg state current.
Proof.
  intros until last; intro Hcertificate; induction Hcertificate.
  - unfold kernel_call_control_rely; auto.
  - destruct H as [actor first entry event node tid old returned frame before after
      Hlookup Hentry Hpre Hpost Hmember Hforeign Htype Hgroup Hactual].
    pose proof Hentry as [_ [_ [_ [_ [_ [_ Hold]]]]]].
    pose proof (@WakeComponent.KernelWakeCEventSegment sg entry event node tid old PendSem 0 PendOK
      returned frame before after Hlookup Hentry Hpre Hpost) as Hsegment.
    destruct (kernel_wake_c_segment_idle_non_idle sg call _ _ _ _ _ _ Hsegment) as [Hidle Hnonidle].
    split.
    + intros [caller [Hready Hgeneration]].
      destruct (sem_post_wake_preserves_current_ready sg entry event node tid old
        call.(os_sched_call_stack).(stackLeaseSlot) caller Hold Hready) as [updated [Hready' Hgeneration']].
      exists updated; split; [exact Hready'|congruence].
    + split; [exact Hidle|]. split; [exact Hnonidle|].
      unfold kernel_call_control_rely, event_wake_state;
        cbn [replace_SchedS replace_EventS replace_TskS SchedState IntrState].
      unfold sched_wake_by_status; destruct task_status_is_suspended; split; reflexivity.
  - destruct IHHcertificate1 as [Hr1 [Hi1 [Hn1 [Hrunning1 Hints1]]]].
    destruct IHHcertificate2 as [Hr2 [Hi2 [Hn2 [Hrunning2 Hints2]]]].
    repeat split; try (intro Hfact; auto); unfold kernel_call_control_rely; congruence.
  - exact IHHcertificate.
Qed.

Lemma sem_pend_sem_post_scoped_restore_body : forall environment critical sg original local mask
  actor entry event node returned before after (frame private : Assertion),
  critical.(critical_region_clients) (sem_pend_post_source_client actor event) ->
  actor <> original.(os_sched_call_invocation) ->
  sem_post_lookup entry event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group entry node <> 0 -> event_object_layout_prop sg event ->
  (flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
    (FlagPendTaskCaller original) original mask entry ** private) before ->
  sem_post_waiter_execution sg (event_addr sg event) returned before after ->
  exists selected old,
    let wake := event_wake_state sg entry event node selected old PendSem 0 PendOK in
    exists run : flag_pend_scoped_environment_run environment critical local local (fun _ _ => frame) sg
      original mask entry before private false original wake after private,
      flag_pend_scoped_environment_source environment critical local local (fun _ _ => frame) sg None
        original mask entry before private false original wake after private run /\
      sem_pend_c_sequence_call_certificate
        (kernel_program_environment_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
        (sem_pend_environment_call_receipt environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin)
          (sem_pend_sem_post_c_step_certificate environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin)))
        _ _ _ _ _ _ _ run original.(os_sched_call_origin) original.(os_sched_call_origin) /\
      sem_pend_client_return_source environment critical sg original entry original wake /\
      (coq_prop (flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller original) original entry original wake) &&
        (flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
          (FlagPendTaskCaller original) original mask wake ** private)) after.
Proof.
  intros environment critical sg original local mask actor entry event node returned before after frame private
    Hmember Hforeign Hlookup Htype Hgroup Hlayout Hpre Hactual.
  pose proof (flag_pend_caller_save_input_receipt_frame environment critical local (fun _ _ => frame) sg
    (FlagPendTaskCaller original) original mask entry private) as Hframe_before.
  destruct (sem_pend_sem_post_restore_body environment critical sg original local mask actor entry event node returned
    before after (frame ** private) Hmember Hforeign Hlookup Htype Hgroup Hlayout
    (proj2 Hframe_before before Hpre) Hactual) as [selected [old [body [Hcertificate [Hnormal Howner]]]]].
  pose (included := sem_pend_selected_environment_sequence environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ body).
  pose proof (sem_pend_sem_post_body_observations environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) original _ _ _ _ _ _ _ body _ _ Hcertificate)
    as [Hready [Hidle [Hnonidle Hcontrol]]].
  assert (Hendpoint : flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller original)
    original entry original (event_wake_state sg entry event node selected old PendSem 0 PendOK)).
  { cbn [flag_pend_call_endpoint_observations].
    split; [intros [_ Hr]; exact (Hready Hr)|].
    split; [intros [_ Hi]; exact (Hidle Hi)|].
    split; [intros [_ Hn]; exact (Hnonidle Hn)|].
    split; [exact Hnormal|intro Horigin; exact Hcontrol]. }
  pose proof (flag_pend_caller_save_input_receipt_frame environment critical local (fun _ _ => frame) sg
    (FlagPendTaskCaller original) original mask (event_wake_state sg entry event node selected old PendSem 0 PendOK)
    private) as Hframe_after.
  assert (Hclose : flag_pend_caller_save_input environment critical local (fun _ _ => frame ** private) sg
      (FlagPendTaskCaller original) original mask (event_wake_state sg entry event node selected old PendSem 0 PendOK) |--
    coq_prop (flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller original)
      original entry original (event_wake_state sg entry event node selected old PendSem 0 PendOK)) &&
      (flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
        (FlagPendTaskCaller original) original mask (event_wake_state sg entry event node selected old PendSem 0 PendOK) ** private)).
  { intros heap Hheap; split; [exact Hendpoint|exact (proj1 Hframe_after heap Hheap)]. }
  pose (run := @KernelCSequenceAdapt (kernel_program_environment_c_step environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)) _ _ _ _ _ _ _ _ _
    Hpre (proj2 Hframe_before) included Hclose).
  assert (Hcalls : sem_pend_c_sequence_call_certificate
    (kernel_program_environment_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
    (sem_pend_environment_call_receipt environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin)
      (sem_pend_sem_post_c_step_certificate environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin)))
    _ _ _ _ _ _ _ run original.(os_sched_call_origin) original.(os_sched_call_origin)).
  { unfold run; apply SemPendCSequenceCallAdapt.
    apply sem_pend_selected_environment_sequence_certificate; exact Hcertificate. }
  exists selected, old, run; split.
  - unfold flag_pend_scoped_environment_source, kernel_program_environment_c_sequence_source, run.
    apply KernelCSourceAdapt; eapply sem_pend_sem_post_environment_source; exact Hcertificate.
  - split; [exact Hcalls|]. split.
    + destruct (sem_pend_c_sequence_client_calls _ _ _ _ _ _ _ _
        (sem_pend_environment_call_receipt_client_calls environment critical sg
          original.(os_sched_call_invocation) original.(os_sched_call_origin))
        _ _ _ _ _ _ _ run _ _ Hcalls) as [trace Htrace].
      eapply sem_pend_client_return_source_from_legacy; eassumption.
    + exact (Hclose after Howner).
Qed.

(** This receipt records the environment run used by the actual Restore
    constructor. It is not recoverable from an endpoint-only execution. *)
Inductive sem_pend_sem_post_restore_receipt environment critical local next_local active sg
  original saved acquired before first_heap :
  forall stopped returned current last_heap,
  os_sched_continuation_c_restore_execution environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap -> Prop :=
| SemPendSemPostRestoreReceipt :
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
    (sem_pend_environment_call_receipt environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin)
      (sem_pend_sem_post_c_step_certificate environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin)))
    _ _ _ _ _ _ _ run original.(os_sched_call_origin) returned.(os_sched_call_origin) ->
  sem_pend_sem_post_restore_receipt environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap
    (@OsSchedContinuationCRestore environment critical local next_local active sg original saved acquired before first_heap
      private_input private_output private_before whole_before stopped returned current environment_heap arch restore
      cursor written prefix_heap final_cursor whole_after private_after last_heap run
      Hr0 Hmask Hinput Hprivate Hjoin Hprefix Hsource Hsuffix Houtput Hprivate_after Hjoin_after).

Lemma sem_pend_restore_from_environment_call_receipt :
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
    (sem_pend_environment_call_receipt environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin)
      (sem_pend_sem_post_c_step_certificate environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin)))
    _ _ _ _ _ _ _ run original.(os_sched_call_origin) returned.(os_sched_call_origin) ->
  exists last_heap (actual : os_sched_continuation_c_restore_execution environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap),
  sem_pend_sem_post_restore_receipt environment critical local next_local active sg
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

Lemma sem_pend_restore_call_receipt_trace_resources :
  forall environment critical local next_local active sg original saved acquired before first_heap
    stopped returned current last_heap actual,
  sem_pend_sem_post_restore_receipt environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap actual ->
  exists trace : kernel_client_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None original.(os_sched_call_origin)
      before stopped returned.(os_sched_call_origin) current,
    sem_pend_client_source_calls environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical.(critical_region_clients) sg original.(os_sched_call_invocation) None original.(os_sched_call_origin)
      before stopped returned.(os_sched_call_origin) current trace /\
    (coq_prop (flag_pend_call_endpoint_observations environment sg
      (FlagPendTaskCaller original) original before returned current) &&
      flag_pend_caller_save_input environment critical next_local active sg
        (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current) last_heap.
Proof.
  intros until actual; intro Hreceipt; destruct Hreceipt.
  destruct (sem_pend_c_sequence_client_calls _ _ _ _ _ _ _ _
    (sem_pend_environment_call_receipt_client_calls environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    _ _ _ _ _ _ _ run _ _ H) as [trace Htrace].
  exists trace; split; assumption.
Qed.

(** The nontrivial instance starts with actual Restore input and prefix,
    executes the literal SemPost helper, and uses the actual suffix. The
    certificate and endpoint facts are produced inside this construction. *)
Lemma sem_pend_sem_post_selected_restore :
  forall environment critical local sg original saved acquired entry first_heap
    (frame private : Assertion) private_before whole_before actor event node helper_returned environment_heap arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written prefix_heap final_cursor whole_after,
  critical.(critical_region_clients) (sem_pend_post_source_client actor event) ->
  actor <> original.(os_sched_call_invocation) ->
  sem_post_lookup entry event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group entry node <> 0 -> event_object_layout_prop sg event ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical local (fun _ _ => frame) sg
    (FlagPendTaskCaller original) original saved acquired entry first_heap ->
  private private_before -> join first_heap private_before whole_before ->
  armv7a_restore_prefix_transition restore cursor whole_before written prefix_heap ->
  sem_post_waiter_execution sg (event_addr sg event) helper_returned prefix_heap environment_heap ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor whole_after ->
  exists selected old,
    let wake := event_wake_state sg entry event node selected old PendSem 0 PendOK in
    exists last_heap (actual : os_sched_continuation_c_restore_execution environment critical local local (fun _ _ => frame) sg
      original saved acquired entry first_heap false original wake last_heap),
    sem_pend_sem_post_restore_receipt environment critical local local (fun _ _ => frame) sg
      original saved acquired entry first_heap false original wake last_heap actual /\
    (coq_prop (sem_pend_client_return_source environment critical sg original entry original wake /\
      flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller original) original entry original wake) &&
      flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
        (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) wake) last_heap.
Proof.
  intros environment critical local sg original saved acquired entry first_heap frame private private_before whole_before
    actor event node helper_returned environment_heap arch restore cursor written prefix_heap final_cursor whole_after
    Hmember Hforeign Hlookup Htype Hgroup Hlayout Hr0 Hmask Hinput Hprivate Hjoin Hprefix Hactual Hsuffix.
  assert (Hwhole : (flag_pend_caller_restore_input environment critical local (fun _ _ => frame) sg
    (FlagPendTaskCaller original) original saved acquired entry ** private) whole_before).
  { exists first_heap, private_before; exact (conj Hjoin (conj Hinput Hprivate)). }
  destruct (flag_pend_scoped_restore_prefix_sequence environment critical local (fun _ _ => frame) sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None original saved acquired entry
    private arch restore cursor whole_before written prefix_heap Hr0 Hmask Hwhole Hprefix)
    as [prefix Hprefix_source].
  pose proof (proj2 (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ prefix)) as Hmiddle.
  destruct (sem_pend_sem_post_scoped_restore_body environment critical sg original local (armv7a_irq_fiq_mask saved)
    actor entry event node helper_returned prefix_heap environment_heap frame private
    Hmember Hforeign Hlookup Htype Hgroup Hlayout Hmiddle Hactual)
    as [selected [old [run [Hsource [Hcalls [Hreturn Hclosed]]]]]].
  destruct (sem_pend_restore_from_environment_call_receipt environment critical local local (fun _ _ => frame) sg
    original saved acquired entry first_heap private private private_before whole_before false original
    (event_wake_state sg entry event node selected old PendSem 0 PendOK) environment_heap arch restore
    cursor written prefix_heap final_cursor whole_after run Hr0 Hmask Hinput Hprivate Hjoin Hprefix Hsource Hsuffix Hcalls)
    as [last_heap [actual Hreceipt]].
  destruct (sem_pend_restore_call_receipt_trace_resources _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hreceipt)
    as [trace [Htrace [Hendpoint Howner]]].
  exists selected, old, last_heap, actual; split; [exact Hreceipt|].
  split; [split; [exact Hreturn|exact Hendpoint]|exact Howner].
Qed.
