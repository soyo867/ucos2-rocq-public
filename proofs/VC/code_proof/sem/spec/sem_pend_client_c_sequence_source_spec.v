Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_phase_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_c_segment_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_idle_guard_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_selected_restore_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_critical_observed_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_call_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_sched_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Import CriticalComponent BuiltinComponent PrimitiveComponent DeleteComponent.
Import SelectedReturnPrimitive SelectedCProgram SelectedIRQWrapperSegment SelectedReturnedCProgram.
Import SelectedEnvironmentCProgram SelectedEnvironmentPhaseEffects SelectedEnvironmentScopedEnvironment.
Import SelectedEnvironmentPhaseProperties.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** These consequences use a concrete registered action from the actual
    modular call. Source classification alone is not reversed into registry
    membership. The action, stop bit and execution edge are unchanged. *)
Lemma sem_pend_registered_call_observed_source :
  forall external port clients sg observer event_observer action first before last after,
  clients action -> kernel_client_actor action <> Some observer ->
  (forall invocation, event_observer = Some invocation ->
    kernel_client_event_actor action <> Some invocation) ->
  kernel_client_step action sg before after ->
  task_execution_source_step external port sg first before last after ->
  tmr_task_source_call_receipt external action sg before after ->
  sem_pend_observed_client_trace external port clients sg observer event_observer
    first before (kernel_client_stops action observer) last after.
Proof.
  intros external port clients sg observer event_observer action first before last after
    Hmember Hforeign Hevent Hstep Hcontrol Hreceipt.
  destruct (sem_pend_client_source_calls_single_step external port clients sg observer event_observer
    action first before last after Hmember Hforeign Hevent Hstep Hcontrol Hreceipt)
    as [trace Hcalls].
  exact (SemPendObservedLegacy _ _ _ _ _ _ _ _ _ _ _ trace Hcalls).
Qed.

Lemma sem_pend_registered_framed_call_observed_source :
  forall external port clients sg observer event_observer action origin before after,
  clients action -> kernel_client_actor action <> Some observer ->
  (forall invocation, event_observer = Some invocation ->
    kernel_client_event_actor action <> Some invocation) ->
  kernel_client_step action sg before after ->
  before.(SchedState).(curTaskID) = after.(SchedState).(curTaskID) ->
  tmr_task_source_call_receipt external action sg before after ->
  sem_pend_observed_client_trace external port clients sg observer event_observer
    origin before (kernel_client_stops action observer) origin after.
Proof.
  intros; eapply sem_pend_registered_call_observed_source; try eassumption.
  eapply TaskExecutionClientFrame; eassumption.
Qed.

Lemma sem_pend_profile_call_observed_source :
  forall external port clients sg observer event_observer origin cut before after,
  clients (kernel_full_profile_cut_client cut) ->
  kernel_client_step (kernel_full_profile_cut_client cut) sg before after ->
  sem_pend_observed_client_trace external port clients sg observer event_observer
    origin before false origin after.
Proof.
  intros external port clients sg observer event_observer origin cut before after Hmember Hstep.
  change (sem_pend_observed_client_trace external port clients sg observer event_observer
    origin before (kernel_client_stops (kernel_full_profile_cut_client cut) observer) origin after).
  eapply sem_pend_registered_framed_call_observed_source.
  - exact Hmember.
  - discriminate.
  - intros; discriminate.
  - exact Hstep.
  - destruct Hstep as [_ ->]; destruct cut; reflexivity.
  - apply TmrTaskCallProfile; exact Hstep.
Qed.

Lemma sem_pend_publication_call_observed_source :
  forall external port clients sg observer event_observer origin publication before after,
  clients (task_create_stack_publication_client publication) ->
  publication.(stack_publication_invocation) <> observer ->
  kernel_client_step (task_create_stack_publication_client publication) sg before after ->
  sem_pend_observed_client_trace external port clients sg observer event_observer
    origin before false origin after.
Proof.
  intros external port clients sg observer event_observer origin publication before after Hmember Hforeign Hstep.
  change (sem_pend_observed_client_trace external port clients sg observer event_observer
    origin before (kernel_client_stops (task_create_stack_publication_client publication) observer) origin after).
  eapply sem_pend_registered_framed_call_observed_source.
  - exact Hmember.
  - cbn [task_create_stack_publication_client kernel_client_actor]; congruence.
  - intros; discriminate.
  - exact Hstep.
  - destruct Hstep as [_ ->]; reflexivity.
  - apply TmrTaskCallNontimer; [constructor|exact Hstep].
Qed.

Lemma sem_pend_nontimer_call_current_eq : forall action sg before after,
  tmr_task_nontimer_source_client action -> kernel_client_step action sg before after ->
  before.(SchedState).(curTaskID) = after.(SchedState).(curTaskID).
Proof.
  intros action sg before after Hkind Hstep; destruct Hkind.
  - eapply task_creation_client_current_pointer_eq; exact Hstep.
  - destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [_ [result Hstep]].
    unfold event_create_allocate_critical in Hstep.
    destruct before.(EventState).(unUsedEventStates).
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [image [_ [_ ->]]]; reflexivity.
  - destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [_ [_ ->]]; reflexivity.
  - destruct Hstep as [_ [_ [_ [_ [result [a [Ha Hstep]]]]]]].
    destruct free; destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [_ [_ [_ [_ ->]]]]; reflexivity.
  - destruct Hstep as [_ [result Hstep]]; symmetry.
    eapply StatusComponent.kernel_status_c_source_current_eq.
    eapply StatusComponent.KernelStatusCResumeSource; exact Hstep.
  - destruct Hstep as [event [_ [_ Hstep]]]; symmetry.
    eapply StatusComponent.kernel_status_c_source_current_eq.
    eapply StatusComponent.KernelStatusCSemAcceptSource; exact Hstep.
Qed.

Lemma sem_pend_nontimer_call_observed_source :
  forall external port clients sg observer event_observer action origin before after,
  tmr_task_nontimer_source_client action -> clients action ->
  kernel_client_actor action <> Some observer ->
  (forall invocation, event_observer = Some invocation ->
    kernel_client_event_actor action <> Some invocation) ->
  kernel_client_step action sg before after ->
  sem_pend_observed_client_trace external port clients sg observer event_observer
    origin before (kernel_client_stops action observer) origin after.
Proof.
  intros external port clients sg observer event_observer action origin before after
    Hkind Hmember Hforeign Hevent Hstep.
  eapply sem_pend_registered_framed_call_observed_source; try eassumption.
  - eapply sem_pend_nontimer_call_current_eq; eassumption.
  - apply TmrTaskCallNontimer; assumption.
Qed.

Lemma sem_pend_suspend_call_observed_source :
  forall external port clients sg observer event_observer actor source_sg priority result entry returned
    origin before after,
  clients (tmr_task_suspend_call_client actor source_sg priority result entry returned) ->
  actor <> Some observer ->
  kernel_client_step (tmr_task_suspend_call_client actor source_sg priority result entry returned)
    sg before after ->
  sem_pend_observed_client_trace external port clients sg observer event_observer
    origin before false origin after.
Proof.
  intros external port clients sg observer event_observer actor source_sg priority result entry returned
    origin before after Hmember Hforeign Hstep.
  change (sem_pend_observed_client_trace external port clients sg observer event_observer origin before
    (kernel_client_stops (tmr_task_suspend_call_client actor source_sg priority result entry returned) observer)
    origin after).
  eapply sem_pend_registered_framed_call_observed_source.
  - exact Hmember.
  - exact Hforeign.
  - intros; discriminate.
  - exact Hstep.
  - destruct Hstep as [_ [_ [_ [_ Hguard]]]].
    destruct (task_suspend_idle_guard_original_or_unchanged _ _ _ _ _ Hguard) as [->|Horiginal].
    + reflexivity.
    + symmetry; eapply StatusComponent.kernel_status_c_source_current_eq.
      eapply StatusComponent.KernelStatusCSuspendSource; exact Horiginal.
  - apply TmrTaskCallSuspend; exact Hstep.
Qed.

(** The CPU local segments retain their actual physical transition and
    output owner. Nil concerns only the OS state; it does not identify their
    input and output heaps or change an active continuation key. *)
Lemma sem_pend_delete_primitive_observed_source :
  forall environment critical sg observer event_observer origin state before input stopped current after output,
  task_delete_primitive_c_segment environment critical sg state before input stopped current after output ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer event_observer origin state stopped origin current /\
  input before /\ output after.
Proof.
  intros environment critical sg observer event_observer origin state before input stopped current after output Hstep.
  split; [|eapply task_delete_primitive_c_segment_resources; exact Hstep].
  destruct Hstep; apply sem_pend_observed_client_trace_refl.
Qed.

Lemma sem_pend_paired_primitive_observed_source :
  forall environment critical sg observer event_observer origin state before input stopped current after output,
  flag_pend_task_primitive_c_step environment critical sg state before input stopped current after output ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer event_observer origin state stopped origin current /\
  input before /\ output after.
Proof.
  intros environment critical sg observer event_observer origin state before input stopped current after output Hstep.
  split; [|eapply flag_pend_task_primitive_c_step_resources; exact Hstep].
  destruct Hstep; try apply sem_pend_observed_client_trace_refl.
  destruct H; apply sem_pend_observed_client_trace_refl.
Qed.

Lemma sem_pend_selected_primitive_observed_source :
  forall environment critical sg observer event_observer origin state before input stopped current after output,
  kernel_selected_return_c_step environment state before input stopped current after output ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer event_observer origin state stopped origin current /\
  input before /\ output after.
Proof.
  intros environment critical sg observer event_observer origin state before input stopped current after output Hstep.
  split; [|eapply kernel_selected_return_c_step_resources; exact Hstep].
  destruct (kernel_selected_return_c_step_state_stop _ _ _ _ _ _ _ _ Hstep) as [-> ->].
  apply sem_pend_observed_client_trace_refl.
Qed.

(** The existing certificate is reused at every literal injection. Its
    decoder is independent of the target union, so no new receipt union or
    endpoint-only inverse of an opaque inclusion is needed. *)
Lemma sem_pend_injected_observed_source :
  forall source target inject leaf external port clients sg observer event_observer,
  (forall state before input stopped current after output step first last,
    leaf state before input stopped current after output step first last ->
    sem_pend_observed_client_trace external port clients sg observer event_observer
      first state stopped last current) ->
  forall state before input stopped current after output step first last,
  sem_pend_injected_call_receipt source target inject leaf
    state before input stopped current after output step first last ->
  sem_pend_observed_client_trace external port clients sg observer event_observer
    first state stopped last current.
Proof.
  intros source target inject leaf external port clients sg observer event_observer Hdecode
    state before input stopped current after output step first last Hreceipt.
  destruct Hreceipt; eapply Hdecode; eassumption.
Qed.

Section SemPendLiteralCallInjection.
Context (source target : KernelCSegmentRelation).
Context (inject : forall state before input stopped current after output,
  source state before input stopped current after output -> target state before input stopped current after output).
Context (leaf : forall state before input stopped current after output,
  source state before input stopped current after output -> TaskInvocationOrigin -> TaskInvocationOrigin -> Prop).

Definition sem_pend_injected_c_sequence state before input stopped current after output
  (run : kernel_c_sequence source state before input stopped current after output) :
  kernel_c_sequence target state before input stopped current after output.
Proof.
  induction run.
  - constructor; exact H.
  - apply KernelCSequenceAtom, inject; exact H.
  - eapply KernelCSequenceThen; eassumption.
  - eapply KernelCSequenceAdapt; eassumption.
Defined.

Lemma sem_pend_injected_c_sequence_certificate :
  forall state before input stopped current after output run first last,
  sem_pend_c_sequence_call_certificate source leaf state before input stopped current after output run first last ->
  sem_pend_c_sequence_call_certificate target (sem_pend_injected_call_receipt source target inject leaf)
    _ _ _ _ _ _ _ (sem_pend_injected_c_sequence _ _ _ _ _ _ _ run) first last.
Proof.
  intros until last; intro Hcalls; induction Hcalls; cbn [sem_pend_injected_c_sequence].
  - constructor.
  - apply SemPendCSequenceCallAtom, SemPendInjectedCallReceipt; exact H.
  - econstructor; eassumption.
  - econstructor; eassumption.
Qed.

Lemma sem_pend_c_sequence_calls_observed_resources :
  forall external port clients sg observer event_observer,
  (forall state before input stopped current after output,
    source state before input stopped current after output -> input before /\ output after) ->
  (forall state before input stopped current after output step first last,
    leaf state before input stopped current after output step first last ->
    sem_pend_observed_client_trace external port clients sg observer event_observer
      first state stopped last current) ->
  forall state before input stopped current after output run first last,
  sem_pend_c_sequence_call_certificate source leaf state before input stopped current after output run first last ->
  sem_pend_observed_client_trace external port clients sg observer event_observer
    first state stopped last current /\ input before /\ output after.
Proof.
  intros external port clients sg observer event_observer Hresources Hdecode
    state before input stopped current after output run first last Hcalls.
  split.
  - eapply sem_pend_observed_c_sequence_trace; eassumption.
  - eapply kernel_c_sequence_resources; [exact Hresources|exact run].
Qed.
End SemPendLiteralCallInjection.

(** Attach the actual modular call's past facts at the Atom construction.
    The physical step itself is the indexed value retained by the existing
    certificate; neither another run nor another heap is chosen. *)
Lemma sem_pend_registered_program_c_atom :
  forall environment critical sg observer stored_origin state before input stopped current after output
    (step : kernel_program_c_step environment critical sg observer stored_origin
      state before input stopped current after output)
    action first last,
  critical.(critical_region_clients) action ->
  kernel_client_actor action <> Some observer ->
  kernel_client_step action sg state current ->
  task_execution_source_step environment.(task_stack_call_external) environment.(task_stack_call_port)
    sg first state last current ->
  tmr_task_source_call_receipt environment.(task_stack_call_external) action sg state current ->
  stopped = kernel_client_stops action observer ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer None first state stopped last current /\
  input before /\ output after.
Proof.
  intros environment critical sg observer stored_origin state before input stopped current after output step
    action first last Hmember Hforeign Hstep Hcontrol Hreceipt ->.
  split.
  - eapply sem_pend_registered_call_observed_source; try eassumption.
    intros; discriminate.
  - exact (kernel_program_c_step_resources _ _ _ _ _ _ _ _ _ _ _ _ step).
Qed.

Lemma sem_pend_counter_c_completion_observed_source :
  forall environment critical sg observer origin operation state frame before after code
    (completed : kernel_counter_c_completion operation sg state frame before after code),
  critical.(critical_region_clients)
    (kernel_full_profile_cut_client
      (match operation with KernelCounterCEnter => KernelFullIntEnter
       | KernelCounterCExit running => KernelFullIntExitCounter running end)) ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer None origin state false origin (kernel_counter_c_state operation state) /\
  (UCOS2_fields_raw_rep sg state ** frame) before /\
  (UCOS2_fields_raw_rep sg (kernel_counter_c_state operation state) ** frame) after.
Proof.
  intros environment critical sg observer origin operation state frame before after code completed Hmember.
  split.
  - destruct operation.
    + eapply sem_pend_profile_call_observed_source;
        [exact Hmember|split; [exact I|reflexivity]].
    + eapply sem_pend_profile_call_observed_source;
        [exact Hmember|split; [exact I|reflexivity]].
  - destruct completed; split; assumption.
Qed.

Lemma sem_pend_publication_c_completion_observed_source :
  forall environment critical local sg observer origin publication state frame before after code effect
    (completed : kernel_publication_c_completion environment.(task_stack_call_continuations) local sg
      publication state frame before after code effect),
  critical.(critical_region_clients) (task_create_stack_publication_client publication) ->
  publication.(stack_publication_invocation) <> observer ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer None origin state false origin
      (task_create_stack_publication_state sg publication state) /\
  (kernel_client_continuation_fields_publication environment.(task_stack_call_continuations) local sg
      publication state ** frame) before /\
  (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg
      (task_create_stack_publication_state sg publication state) ** frame) after.
Proof.
  intros environment critical local sg observer origin publication state frame before after code effect
    completed Hmember Hforeign.
  split; [eapply sem_pend_publication_call_observed_source; eassumption|].
  exact (kernel_builtin_c_segment_resources environment critical local sg _ _ _ _ _ _
    (KernelBuiltinCPublication environment critical local sg publication state frame before after code effect completed)).
Qed.

(** Every original layer has the same transparent one-constructor map.
    This does not collapse its other constructors into the original branch. *)
Definition sem_pend_return_original_step environment critical sg observer origin :=
  @KernelProgramReturnOriginal environment critical sg observer origin.
Definition sem_pend_selected_return_step environment critical sg observer origin :=
  @KernelSelectedProgramReturn critical sg observer origin environment.
Definition sem_pend_wrapper_original_step environment critical sg observer origin :=
  @KernelProgramWrapperOriginal environment critical sg observer origin.
Definition sem_pend_returned_wrapper_step environment critical sg observer origin :=
  @KernelProgramReturnedWrapper environment critical sg observer origin.
Definition sem_pend_environment_body_step environment critical sg observer origin :=
  @KernelProgramEnvironmentBody environment critical sg observer origin.

Lemma sem_pend_return_original_call_certificate :
  forall environment critical sg observer origin leaf state before input stopped current after output run first last,
  sem_pend_c_sequence_call_certificate
    (kernel_program_c_step environment critical sg observer origin) leaf
    state before input stopped current after output run first last ->
  sem_pend_c_sequence_call_certificate
    (kernel_program_return_c_step environment critical sg observer origin)
    (sem_pend_injected_call_receipt _ _ (sem_pend_return_original_step environment critical sg observer origin) leaf)
    _ _ _ _ _ _ _
    (sem_pend_injected_c_sequence _ _ (sem_pend_return_original_step environment critical sg observer origin)
      _ _ _ _ _ _ _ run) first last.
Proof. intros; eapply sem_pend_injected_c_sequence_certificate; eassumption. Qed.

Lemma sem_pend_selected_return_call_certificate :
  forall environment critical sg observer origin leaf state before input stopped current after output run first last,
  sem_pend_c_sequence_call_certificate
    (kernel_program_return_c_step environment critical sg observer origin) leaf
    state before input stopped current after output run first last ->
  sem_pend_c_sequence_call_certificate
    (kernel_program_selected_c_step environment critical sg observer origin)
    (sem_pend_injected_call_receipt _ _ (sem_pend_selected_return_step environment critical sg observer origin) leaf)
    _ _ _ _ _ _ _
    (sem_pend_injected_c_sequence _ _ (sem_pend_selected_return_step environment critical sg observer origin)
      _ _ _ _ _ _ _ run) first last.
Proof. intros; eapply sem_pend_injected_c_sequence_certificate; eassumption. Qed.

Lemma sem_pend_wrapper_original_call_certificate :
  forall environment critical sg observer origin leaf state before input stopped current after output run first last,
  sem_pend_c_sequence_call_certificate
    (kernel_program_selected_c_step environment critical sg observer origin) leaf
    state before input stopped current after output run first last ->
  sem_pend_c_sequence_call_certificate
    (kernel_program_wrapper_c_step environment critical sg observer origin)
    (sem_pend_injected_call_receipt _ _ (sem_pend_wrapper_original_step environment critical sg observer origin) leaf)
    _ _ _ _ _ _ _
    (sem_pend_injected_c_sequence _ _ (sem_pend_wrapper_original_step environment critical sg observer origin)
      _ _ _ _ _ _ _ run) first last.
Proof. intros; eapply sem_pend_injected_c_sequence_certificate; eassumption. Qed.

Lemma sem_pend_returned_wrapper_call_certificate :
  forall environment critical sg observer origin leaf state before input stopped current after output run first last,
  sem_pend_c_sequence_call_certificate
    (kernel_program_wrapper_c_step environment critical sg observer origin) leaf
    state before input stopped current after output run first last ->
  sem_pend_c_sequence_call_certificate
    (kernel_program_returned_c_step environment critical sg observer origin)
    (sem_pend_injected_call_receipt _ _ (sem_pend_returned_wrapper_step environment critical sg observer origin) leaf)
    _ _ _ _ _ _ _
    (sem_pend_injected_c_sequence _ _ (sem_pend_returned_wrapper_step environment critical sg observer origin)
      _ _ _ _ _ _ _ run) first last.
Proof. intros; eapply sem_pend_injected_c_sequence_certificate; eassumption. Qed.

Lemma sem_pend_environment_body_call_certificate :
  forall environment critical sg observer origin leaf state before input stopped current after output run first last,
  sem_pend_c_sequence_call_certificate
    (kernel_program_returned_c_step environment critical sg observer origin) leaf
    state before input stopped current after output run first last ->
  sem_pend_c_sequence_call_certificate
    (kernel_program_environment_c_step environment critical sg observer origin)
    (sem_pend_injected_call_receipt _ _ (sem_pend_environment_body_step environment critical sg observer origin) leaf)
    _ _ _ _ _ _ _
    (sem_pend_injected_c_sequence _ _ (sem_pend_environment_body_step environment critical sg observer origin)
      _ _ _ _ _ _ _ run) first last.
Proof. intros; eapply sem_pend_injected_c_sequence_certificate; eassumption. Qed.

(** The typed module post is decoded on its actual step. The existing
    certificate preserves Refl/Atom/Then/Adapt and the CPU constructor
    below consumes that very run before it is hidden. *)
Lemma sem_pend_c_sequence_save_output :
  forall environment critical local next_local active sg mask call before first_heap private_input private_output private_before whole_before returned current environment_heap arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers final_registers whole_after
    (leaf : forall state heap input stopped result output_heap output,
      kernel_program_environment_c_step environment critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin)
        state heap input stopped result output_heap output -> TaskInvocationOrigin -> TaskInvocationOrigin -> Prop)
    (run : flag_pend_scoped_environment_run environment critical local next_local active sg
      call mask before whole_before private_input false returned current environment_heap private_output),
  (forall state heap input stopped result output_heap output step first last,
    leaf state heap input stopped result output_heap output step first last ->
    sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical.(critical_region_clients) sg call.(os_sched_call_invocation) None
      first state stopped last result) ->
  sem_pend_client_phase_context sg call before ->
  flag_pend_scoped_environment_source environment critical local next_local active sg None
    call mask before whole_before private_input false returned current environment_heap private_output run ->
  sem_pend_c_sequence_call_certificate
    (kernel_program_environment_c_step environment critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin))
    leaf
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
    arch save registers final_registers whole_after leaf run Hdecode Hentry Hsource Hcalls Hinput Hprivate Hjoin Hreturn_word
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
  assert (Htrace : sem_pend_observed_client_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    call.(os_sched_call_invocation) None call.(os_sched_call_origin) before false returned.(os_sched_call_origin) current).
  { eapply sem_pend_observed_c_sequence_trace; [exact Hdecode|exact Hcalls]. }
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

Lemma sem_pend_c_sequence_restore_output :
  forall environment critical local next_local active sg original saved acquired before first_heap
    private_input private_output private_before whole_before returned current environment_heap arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written prefix_heap final_cursor whole_after
    (leaf : forall state heap input stopped result output_heap output,
      kernel_program_environment_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin)
        state heap input stopped result output_heap output -> TaskInvocationOrigin -> TaskInvocationOrigin -> Prop)
    (run : flag_pend_scoped_environment_run environment critical local next_local active sg
      original (armv7a_irq_fiq_mask saved) before prefix_heap private_input
      false returned current environment_heap private_output),
  (forall state heap input stopped result output_heap output step first last,
    leaf state heap input stopped result output_heap output step first last ->
    sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical.(critical_region_clients) sg original.(os_sched_call_invocation) None
      first state stopped last result) ->
  kernel_call_task_source original before ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before first_heap ->
  private_input private_before -> join first_heap private_before whole_before ->
  armv7a_restore_prefix_transition restore cursor whole_before written prefix_heap ->
  flag_pend_scoped_environment_source environment critical local next_local active sg None
    original (armv7a_irq_fiq_mask saved) before prefix_heap private_input
    false returned current environment_heap private_output run ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor whole_after ->
  sem_pend_c_sequence_call_certificate
    (kernel_program_environment_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
    leaf _ _ _ _ _ _ _ run original.(os_sched_call_origin) returned.(os_sched_call_origin) ->
  exists last_heap (actual : os_sched_continuation_c_restore_execution environment critical local next_local active sg
    original saved acquired before first_heap false returned current last_heap),
  ((coq_prop (sem_pend_client_return_source environment critical sg original before returned current /\
      kernel_call_control_rely sg before current /\
      flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller original) original before returned current) &&
    sem_pend_fields_closed environment next_local sg returned (armv7a_irq_fiq_mask saved) current) **
    active returned current) last_heap.
Proof.
  intros environment critical local next_local active sg original saved acquired before first_heap
    private_input private_output private_before whole_before returned current environment_heap arch restore
    cursor written prefix_heap final_cursor whole_after leaf run Hdecode Htask Hr0 Hmask Hinput Hprivate
    Hjoin Hprefix Hsource Hsuffix Hcalls.
  assert (Hwhole : (flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before ** private_input) whole_before).
  { exists first_heap, private_before; exact (conj Hjoin (conj Hinput Hprivate)). }
  destruct (flag_pend_scoped_environment_restore_sequence environment critical local next_local active sg None
    original saved acquired before whole_before private_input false returned current environment_heap private_output
    arch restore cursor written prefix_heap final_cursor whole_after run Hr0 Hmask Hwhole Hprefix Hsource Hsuffix)
    as [completed Hcompleted_source].
  pose proof (proj2 (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ completed)) as Houtput.
  destruct Houtput as [last_heap [private_after [Hjoin_after [Hcaller_after Hprivate_after]]]].
  pose (actual := @OsSchedContinuationCRestore environment critical local next_local active sg
    original saved acquired before first_heap private_input private_output private_before whole_before
    false returned current environment_heap arch restore cursor written prefix_heap final_cursor whole_after
    private_after last_heap run Hr0 Hmask Hinput Hprivate Hjoin Hprefix Hsource Hsuffix
    Hcaller_after Hprivate_after Hjoin_after).
  destruct Hcaller_after as [Hendpoint Howner].
  destruct (sem_pend_task_endpoint_control environment sg original before returned current Htask Hendpoint)
    as [Hnormal Hcontrol].
  assert (Hreturn : sem_pend_client_return_source environment critical sg original before returned current).
  { split; [|exact Hnormal]. eapply sem_pend_observed_c_sequence_trace; [exact Hdecode|exact Hcalls]. }
  pose proof (sem_pend_task_caller_closed _ _ _ _ _ _ _ _ last_heap Howner) as Hclosed.
  destruct Hclosed as [owned [rest [Hseparate [Hclosed Hactive]]]].
  exists last_heap, actual, owned, rest.
  exact (conj Hseparate (conj (conj (conj Hreturn (conj Hcontrol Hendpoint)) Hclosed) Hactive)).
Qed.
