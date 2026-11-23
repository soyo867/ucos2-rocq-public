Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_phase_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_selected_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagWaitingEnvironmentConsumer.
Import PrimitiveComponent CriticalComponent.
Import SelectedEnvironmentCProgram SelectedEnvironmentCSource.
Import SelectedEnvironmentPrimitiveSupport SelectedEnvironmentScopedEnvironment.
Import SelectedEnvironmentPhaseEffects CompletedCallerEvents.

(** The terminal ABI transition is appended to this exact ENV run.  The
    original state, caller heap boundary and pure endpoint packet remain
    indexed by the same run; the publication cut is never its new start. *)
Lemma environment_c_sequence_restore_preserves_packet :
  forall environment critical sg observer origin event_observer local active call saved acquired
    initial before input stopped current restored (packet : Prop) arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written middle final_cursor after
    (run : kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer origin)
      initial before input stopped current restored
      (coq_prop packet && flag_pend_caller_restore_input environment critical local active sg
        (FlagPendTaskCaller call) call saved acquired current)),
  kernel_program_environment_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ run ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor restored written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  let event := flag_pend_task_restore_c_event environment critical local active sg call saved acquired current restored after in
  exists (completed : kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer origin)
    initial before input (orb stopped false) current after
    (coq_prop packet && event.(flag_pend_event_output))),
  flag_pend_task_primitive_c_event environment critical sg event /\
  kernel_program_environment_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ completed.
Proof.
  intros environment critical sg observer origin event_observer local active call saved acquired initial before input stopped
    current restored packet arch restore cursor written middle final_cursor after run Hsource Hr0 Hmask Hprefix Hsuffix event.
  destruct (proj2 (kernel_program_environment_c_sequence_resources environment critical sg observer origin
    _ _ _ _ _ _ _ run)) as [Hpacket Hinput].
  assert (Hprimitive : flag_pend_task_primitive_c_event environment critical sg event).
  { unfold event; eapply FlagPendTaskPrimitiveRestore; eassumption. }
  pose (primitive := FlagPendTaskPrimitiveCStep environment critical sg event Hprimitive).
  pose (step := kernel_program_environment_paired_primitive environment critical sg observer origin _ _ _ _ _ _ _ primitive).
  pose (tail := KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput (fun heap Howner => Howner)
    (KernelCSequenceAtom _ _ _ _ _ _ _ _ step) (fun heap Howner => conj Hpacket Howner)).
  exists (KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ run (fun heap Howner => proj2 Howner) tail).
  split; [exact Hprimitive|].
  apply KernelCSourceThen; [exact Hsource|].
  apply KernelCSourceAdapt, KernelCSourceAtom; unfold step; apply kernel_program_environment_paired_primitive_source.
Qed.

(** Hrecover is the actual published receipt-to-active entailment supplied
    by the selected Task/IRQ suffix.  It is applied to that receipt's
    subheap; the independent handler frame remains the private output. *)
Lemma environment_receipt_return_environment :
  forall environment critical initial_local next_local initial_private active receipt frame sg original saved acquired initial first_heap
    stopped returned current restored arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written middle final_cursor after
    (run : kernel_c_sequence (kernel_program_environment_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap
      (flag_pend_caller_save_input environment critical initial_local active sg
        (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial ** initial_private)
      stopped current restored
      (coq_prop (flag_pend_call_endpoint_observations environment sg
        (FlagPendTaskCaller original) original initial returned current) &&
       flag_pend_caller_restore_input environment critical next_local (fun _ _ => receipt ** frame) sg
        (FlagPendTaskCaller returned) returned saved acquired current)),
  kernel_program_environment_c_sequence_source environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ run ->
  (receipt |-- active returned current) ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor restored written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  exists (scoped : flag_pend_scoped_environment_run environment critical initial_local next_local active sg
    original (armv7a_irq_fiq_mask saved) initial first_heap initial_private
    (orb stopped false) returned current after frame),
  flag_pend_scoped_environment_source environment critical initial_local next_local active sg None
    original (armv7a_irq_fiq_mask saved) initial first_heap initial_private
    (orb stopped false) returned current after frame scoped.
Proof.
  intros until run; intros Hsource Hrecover Hr0 Hmask Hprefix Hsuffix.
  destruct (environment_c_sequence_restore_preserves_packet environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None next_local
    (fun _ _ => receipt ** frame) returned saved acquired initial first_heap _ stopped current restored _
    arch restore cursor written middle final_cursor after run Hsource Hr0 Hmask Hprefix Hsuffix)
    as [completed [Hprimitive Hcompleted_source]].
  pose proof (proj1 (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ completed)) as Hinput.
  assert (Hpost :
    coq_prop (flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller original)
      original initial returned current) &&
    (flag_pend_task_restore_c_event environment critical next_local (fun _ _ => receipt ** frame) sg
      returned saved acquired current restored after).(flag_pend_event_output) |--
    coq_prop (flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller original)
      original initial returned current) &&
    (flag_pend_caller_save_input environment critical next_local active sg
      (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current ** frame)).
  { cbn [flag_pend_task_restore_c_event flag_pend_event_output].
    unfold flag_pend_caller_save_input, flag_pend_active_save_input; Intros.
    sep_apply_l_atomic Hrecover; entailer!. }
  exists (KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput (fun heap Howner => Howner) completed Hpost).
  unfold flag_pend_scoped_environment_source, kernel_program_environment_c_sequence_source.
  apply KernelCSourceAdapt; exact Hcompleted_source.
Qed.

(** The caller's heap is the original captured subheap.  Hreturned comes
    from the same actual terminal that produced run's final endpoint. *)
Lemma environment_scoped_save_active_output :
  forall environment critical local next_local active sg original mask before first_heap
    private_input private_output private_before whole_before stopped returned current environment_heap arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers final_registers whole_after
    (run : flag_pend_scoped_environment_run environment critical local next_local active sg
      original mask before whole_before private_input stopped returned current environment_heap private_output),
  flag_pend_scoped_environment_source environment critical local next_local active sg None
    original mask before whole_before private_input stopped returned current environment_heap private_output run ->
  flag_pend_caller_save_input environment critical local active sg
    (FlagPendTaskCaller original) original mask before first_heap ->
  private_input private_before -> join first_heap private_before whole_before ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current environment_heap
    final_registers current whole_after ->
  kernel_call_task_source returned current ->
  exists last_heap,
    CompletedCallerEvents.flag_pend_selected_caller_save_event environment critical local active sg
      (FlagPendTaskCaller original) original mask final_registers.(kernel_save_r0) before
      (FlagPendTaskCaller returned) returned current next_local first_heap last_heap /\
    FlagPendActiveCaller.flag_pend_selected_caller_save_output environment critical local active sg
      (FlagPendTaskCaller original) original mask before first_heap final_registers.(kernel_save_r0) last_heap.
Proof.
  intros environment critical local next_local active sg original mask before first_heap
    private_input private_output private_before whole_before stopped returned current environment_heap arch save
    registers final_registers whole_after run Hsource Hinput Hprivate Hjoin Hreturn Hvalid Hmask Hsuffix Hreturned.
  destruct (os_sched_continuation_c_save_execution_from_environment environment critical local next_local active sg
    original mask before first_heap private_input private_output private_before whole_before stopped returned current environment_heap
    arch save registers final_registers whole_after run Hsource Hinput Hprivate Hjoin Hreturn Hvalid Hmask Hsuffix)
    as [last_heap Hactual].
  pose proof (CompletedCallerEvents.scoped_save_execution_complete_event environment critical local next_local active sg
    original mask before first_heap final_registers.(kernel_save_r0) stopped returned current last_heap Hactual Hreturned) as Hevent.
  exists last_heap; split; [exact Hevent|].
  apply FlagPendActiveCaller.flag_pend_completed_save_output_included.
  eapply CompletedCallerEvents.scoped_save_event_output; exact Hevent.
Qed.

Lemma environment_scoped_restore_active_output :
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
  kernel_call_task_source returned current ->
  exists last_heap,
    CompletedCallerEvents.flag_pend_selected_caller_restore_event environment critical local active sg
      (FlagPendTaskCaller original) original saved acquired before
      (FlagPendTaskCaller returned) returned current next_local first_heap last_heap /\
    FlagPendActiveCaller.flag_pend_selected_caller_restore_output environment critical local active sg
      (FlagPendTaskCaller original) original saved acquired before first_heap last_heap.
Proof.
  intros environment critical local next_local active sg original saved acquired before first_heap
    private_input private_output private_before whole_before stopped returned current environment_heap arch restore
    cursor written prefix_heap final_cursor whole_after run Hr0 Hmask Hinput Hprivate Hjoin Hprefix Hsource Hsuffix Hreturned.
  destruct (os_sched_continuation_c_restore_execution_from_environment environment critical local next_local active sg
    original saved acquired before first_heap private_input private_output private_before whole_before stopped returned current environment_heap
    arch restore cursor written prefix_heap final_cursor whole_after run Hr0 Hmask Hinput Hprivate Hjoin Hprefix Hsource Hsuffix)
    as [last_heap Hactual].
  pose proof (CompletedCallerEvents.scoped_restore_execution_complete_event environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap Hactual Hreturned) as Hevent.
  exists last_heap; split; [exact Hevent|].
  apply FlagPendActiveCaller.flag_pend_completed_restore_output_included.
  eapply CompletedCallerEvents.scoped_restore_event_output; exact Hevent.
Qed.

End FlagWaitingEnvironmentConsumer.
