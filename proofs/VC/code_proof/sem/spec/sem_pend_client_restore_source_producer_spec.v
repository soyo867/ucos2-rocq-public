Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_clear_status_phase_spec.
Import UCOS2_C_Rules PrimitiveComponent.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The body keeps its original C run and leaf evidence.  The extra case is
    an actual local CPU primitive constructor, not an arbitrary same-endpoint
    program.  Such a primitive has no abstract OS-state edge. *)
Section SemPendRestoreCSource.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (original : OsSchedCallContext).
Let segment := kernel_program_c_step environment critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin).
Context (leaf : forall state before input stopped current after output,
  segment state before input stopped current after output ->
  TaskInvocationOrigin -> TaskInvocationOrigin -> Prop).

Inductive sem_pend_restore_c_leaf_certificate :
  forall state before input stopped current after output,
  segment state before input stopped current after output ->
  TaskInvocationOrigin -> TaskInvocationOrigin -> Prop :=
| SemPendRestoreCBody : forall state before input stopped current after output
    (step : segment state before input stopped current after output) first last,
    leaf state before input stopped current after output step first last ->
    sem_pend_restore_c_leaf_certificate _ _ _ _ _ _ _ step first last
| SemPendRestoreCLocalPrimitive : forall state before input after output
    (primitive : flag_pend_task_primitive_c_step environment critical sg
      state before input false state after output) origin,
    sem_pend_restore_c_leaf_certificate _ _ _ _ _ _ _
      (@KernelProgramCPairedPrimitive environment critical sg
        original.(os_sched_call_invocation) original.(os_sched_call_origin)
        state before input false state after output primitive) origin origin.

Lemma sem_pend_restore_c_leaf_client_calls :
  (forall state before input stopped current after output
    (step : segment state before input stopped current after output) first last,
    leaf state before input stopped current after output step first last ->
    exists trace : kernel_client_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None first state stopped last current,
      sem_pend_client_source_calls environment.(task_stack_call_external) environment.(task_stack_call_port)
        critical.(critical_region_clients) sg original.(os_sched_call_invocation) None
        first state stopped last current trace) ->
  forall state before input stopped current after output
    (step : segment state before input stopped current after output) first last,
    sem_pend_restore_c_leaf_certificate state before input stopped current after output step first last ->
    exists trace : kernel_client_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None first state stopped last current,
      sem_pend_client_source_calls environment.(task_stack_call_external) environment.(task_stack_call_port)
        critical.(critical_region_clients) sg original.(os_sched_call_invocation) None
        first state stopped last current trace.
Proof.
  intros Hleaf state before input stopped current after output step first last Hcertificate.
  destruct Hcertificate.
  - eapply Hleaf; eassumption.
  - exists (@KernelClientTaskSourceNil environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None origin state).
    constructor.
Qed.

Lemma sem_pend_restore_c_sequence_lift : forall state before input stopped current after output
  (run : kernel_c_sequence segment state before input stopped current after output) first last,
  sem_pend_c_sequence_call_certificate segment leaf _ _ _ _ _ _ _ run first last ->
  sem_pend_c_sequence_call_certificate segment sem_pend_restore_c_leaf_certificate
    _ _ _ _ _ _ _ run first last.
Proof.
  intros state before input stopped current after output run first last Hcertificate.
  induction Hcertificate; econstructor; eauto using SemPendRestoreCBody.
Qed.

(** This constructs the prefix atom from the actual ABI transition and the
    input heap.  Its resource result is then the precise middle-run input. *)
Lemma sem_pend_client_restore_prefix_c_sequence : forall phase local mask saved acquired checkpoint
  arch (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  cursor before written prefix_heap (frame : Assertion),
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (sem_pend_clear_status_phase_restore_input phase environment local critical sg original
    mask saved acquired checkpoint ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written prefix_heap ->
  exists prefix : kernel_c_sequence segment checkpoint before
    (sem_pend_clear_status_phase_restore_input phase environment local critical sg original
      mask saved acquired checkpoint ** frame) false checkpoint prefix_heap
    (flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
      (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) checkpoint),
    sem_pend_c_sequence_call_certificate segment sem_pend_restore_c_leaf_certificate
      _ _ _ _ _ _ _ prefix original.(os_sched_call_origin) original.(os_sched_call_origin) /\
    flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
      (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) checkpoint prefix_heap /\
    exists word, written.(kernel_restore_msr_word) = Some word /\
      armv7a_irq_fiq_mask word = armv7a_irq_fiq_mask saved.
Proof.
  intros phase local mask saved acquired checkpoint arch restore cursor before written prefix_heap frame
    Hr0 Hmask Hinput Hactual.
  assert (Hopen : sem_pend_clear_status_phase_restore_input phase environment local critical sg original
      mask saved acquired checkpoint ** frame |--
    flag_pend_caller_restore_input environment critical local (fun _ _ => frame) sg
      (FlagPendTaskCaller original) original saved acquired checkpoint).
  { assert (Hforget : sem_pend_clear_status_phase_restore_input phase environment local critical sg original
        mask saved acquired checkpoint ** frame |--
      sem_pend_fields_masked environment local critical sg original saved acquired checkpoint ** frame).
    { intros heap [owned [rest [Hjoin [[Hfact Howner] Hframe]]]].
      exists owned, rest; exact (conj Hjoin (conj Howner Hframe)). }
    intros heap Hheap.
    apply (proj2 (flag_pend_task_restore_input_masked_equiv environment critical local (fun _ _ => frame)
      sg original saved acquired checkpoint)).
    exact (Hforget heap Hheap). }
  pose proof (Hopen before Hinput) as Howned.
  pose (primitive := @FlagPendTaskRestoreCPrefix environment critical sg local (fun _ _ => frame)
    original saved acquired checkpoint arch restore cursor before written prefix_heap Hr0 Hmask Howned Hactual).
  pose (step := @KernelProgramCPairedPrimitive environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ primitive).
  pose (atom := @KernelCSequenceAtom segment _ _ _ _ _ _ _ step).
  pose (prefix := @KernelCSequenceAdapt segment _ _ _ _ _ _ _ _ _ Hinput Hopen atom
    (fun heap Hheap => Hheap)).
  exists prefix; split.
  - unfold prefix; apply SemPendCSequenceCallAdapt.
    unfold atom; apply SemPendCSequenceCallAtom.
    unfold step; apply SemPendRestoreCLocalPrimitive.
  - split.
    + exact (proj2 (kernel_program_c_step_resources environment critical sg
        original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ step)).
    + pose proof (armv7a_restore_prefix_source _ _ _ _ restore _ _ _ _ Hactual) as Hsource.
      pose proof (kernel_call_restore_prefix_cursor _ _ _ _ _ Hsource) as Hwritten.
      exists (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)).
      split; [rewrite Hwritten; reflexivity|].
      rewrite armv7a_cpsr_restore_mask_eq, Hr0; reflexivity.
Qed.

Lemma sem_pend_client_restore_suffix_c_sequence : forall local returned current saved word
  arch (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  written environment_heap final_cursor after (frame : Assertion),
  written.(kernel_restore_msr_word) = Some word ->
  armv7a_irq_fiq_mask word = armv7a_irq_fiq_mask saved ->
  flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
    (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current environment_heap ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor after ->
  exists suffix : kernel_c_sequence segment current environment_heap
    (flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
      (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current)
    false current after
    (flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
      (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current),
    sem_pend_c_sequence_call_certificate segment sem_pend_restore_c_leaf_certificate
      _ _ _ _ _ _ _ suffix returned.(os_sched_call_origin) returned.(os_sched_call_origin).
Proof.
  intros local returned current saved word arch restore written environment_heap final_cursor after frame
    Hword Hmask Howned Hactual.
  assert (Hopen : flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
      (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current |--
    flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
      (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask word) current).
  { rewrite Hmask; intros heap Hheap; exact Hheap. }
  assert (Hclose : flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
      (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask word) current |--
    flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
      (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current).
  { rewrite Hmask; intros heap Hheap; exact Hheap. }
  pose (primitive := @FlagPendTaskRestoreCSuffix environment critical sg local (fun _ _ => frame)
    returned current word arch restore written environment_heap final_cursor after Hword
    (Hopen environment_heap Howned) Hactual).
  pose (step := @KernelProgramCPairedPrimitive environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ primitive).
  pose (atom := @KernelCSequenceAtom segment _ _ _ _ _ _ _ step).
  exists (@KernelCSequenceAdapt segment _ _ _ _ _ _ _ _ _ Howned Hopen atom Hclose).
  apply SemPendCSequenceCallAdapt; unfold atom; apply SemPendCSequenceCallAtom.
  unfold step; apply SemPendRestoreCLocalPrimitive.
Qed.

(** The input body is the original finite C derivation, not a final owner
    hypothesis.  Each primitive and the body keep their actual heap indices.
    The completed run contains this very body and its original bridges. *)
Lemma sem_pend_client_restore_c_sequence :
  (forall state before input stopped current after output
    (step : segment state before input stopped current after output) first last,
    leaf state before input stopped current after output step first last ->
    exists trace : kernel_client_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None first state stopped last current,
      sem_pend_client_source_calls environment.(task_stack_call_external) environment.(task_stack_call_port)
        critical.(critical_region_clients) sg original.(os_sched_call_invocation) None
        first state stopped last current trace) ->
  forall phase local mask saved acquired checkpoint returned current arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor before written prefix_heap environment_heap final_cursor after (frame : Assertion)
    (body : kernel_c_sequence segment checkpoint prefix_heap
      (flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
        (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) checkpoint)
      false current environment_heap
      (flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
        (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current)),
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (sem_pend_clear_status_phase_restore_input phase environment local critical sg original
    mask saved acquired checkpoint ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written prefix_heap ->
  sem_pend_c_sequence_call_certificate segment leaf _ _ _ _ _ _ _ body
    original.(os_sched_call_origin) returned.(os_sched_call_origin) ->
  kernel_call_normal_return original checkpoint returned current ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor after ->
  exists completed : kernel_c_sequence segment checkpoint before
    (sem_pend_clear_status_phase_restore_input phase environment local critical sg original
      mask saved acquired checkpoint ** frame) false current after
    (sem_pend_clear_status_phase_restore_output phase environment local critical sg original mask checkpoint ** frame),
    sem_pend_c_sequence_call_certificate segment sem_pend_restore_c_leaf_certificate
      _ _ _ _ _ _ _ completed original.(os_sched_call_origin) returned.(os_sched_call_origin) /\
    ((coq_prop (sem_pend_client_return_source environment critical sg original checkpoint returned current /\
        sem_pend_clear_status_phase_restore_observation phase environment critical sg original checkpoint returned current) &&
      sem_pend_fields_closed environment local sg returned mask current) ** frame) after /\
    (sem_pend_clear_status_phase_restore_output phase environment local critical sg original mask checkpoint ** frame) after.
Proof.
  intros Hleaf phase local mask saved acquired checkpoint returned current arch restore cursor before written
    prefix_heap environment_heap final_cursor after frame body Hr0 Hmask Hinput Hprefix Hbody Hnormal Hsuffix.
  assert (Hpure : interrupt_saved_value mask saved /\
    sem_pend_clear_status_phase_restore_pre phase environment critical sg original mask checkpoint).
  { assert (Hobserve : sem_pend_clear_status_phase_restore_input phase environment local critical sg original
        mask saved acquired checkpoint ** frame |--
      coq_prop (interrupt_saved_value mask saved /\
        sem_pend_clear_status_phase_restore_pre phase environment critical sg original mask checkpoint)).
    { intros heap [owned [rest [Hjoin [[Hfact Howner] Hframe]]]]; exact Hfact. }
    exact (Hobserve before Hinput). }
  destruct Hpure as [Hsaved Hpre].
  destruct (sem_pend_client_restore_prefix_c_sequence phase local mask saved acquired checkpoint arch restore
    cursor before written prefix_heap frame Hr0 Hmask Hinput Hprefix)
    as [prefix [Hprefix_certificate [Hprefix_owner [word [Hword Hword_mask]]]]].
  pose proof (proj2 (kernel_program_c_sequence_resources environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ body)) as Hmiddle_owner.
  destruct (sem_pend_client_restore_suffix_c_sequence local returned current saved word arch restore
    written environment_heap final_cursor after frame Hword Hword_mask Hmiddle_owner Hsuffix)
    as [suffix Hsuffix_certificate].
  pose (tail := @KernelCSequenceThen segment _ _ _ _ _ _ _ _ _ _ _ _
    body (fun heap Hheap => Hheap) suffix).
  pose (run := @KernelCSequenceThen segment _ _ _ _ _ _ _ _ _ _ _ _
    prefix (fun heap Hheap => Hheap) tail).
  assert (Hcertificate : sem_pend_c_sequence_call_certificate segment sem_pend_restore_c_leaf_certificate
    _ _ _ _ _ _ _ run original.(os_sched_call_origin) returned.(os_sched_call_origin)).
  { unfold run; apply SemPendCSequenceCallThen with (middle_origin := original.(os_sched_call_origin));
      [exact Hprefix_certificate|].
    unfold tail; apply SemPendCSequenceCallThen with (middle_origin := returned.(os_sched_call_origin)).
    - apply sem_pend_restore_c_sequence_lift; exact Hbody.
    - exact Hsuffix_certificate. }
  destruct (sem_pend_c_sequence_client_calls segment sem_pend_restore_c_leaf_certificate
    environment.(task_stack_call_external) environment.(task_stack_call_port) critical.(critical_region_clients)
    sg original.(os_sched_call_invocation) None (sem_pend_restore_c_leaf_client_calls Hleaf)
    _ _ _ _ _ _ _ run _ _ Hcertificate) as [trace Hcalls].
  assert (Hreturn : sem_pend_client_return_source environment critical sg original checkpoint returned current).
  { eapply sem_pend_client_return_source_from_legacy; eassumption. }
  assert (Hphase : sem_pend_clear_status_phase_restore_observation phase environment critical sg
    original checkpoint returned current).
  { destruct phase; cbn [sem_pend_clear_status_phase_restore_pre] in Hpre.
    - contradiction.
    - destruct Hpre as [Hmask_eq [Hcontext Hwait]].
      eapply sem_pend_clear_status_phase_wait_restore_observation; eassumption.
    - exact (sem_pend_clear_status_phase_return_restore_observation
        environment critical sg original mask checkpoint returned current Hpre Hreturn). }
  assert (Hpacket : flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
      (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current |--
    (coq_prop (sem_pend_client_return_source environment critical sg original checkpoint returned current /\
        sem_pend_clear_status_phase_restore_observation phase environment critical sg original checkpoint returned current) &&
      sem_pend_fields_closed environment local sg returned mask current) ** frame).
  { rewrite (proj1 (flag_pend_task_save_input_closed_equiv environment critical local (fun _ _ => frame)
      sg returned (armv7a_irq_fiq_mask saved) current)).
    rewrite (proj2 Hsaved).
    intros heap [owned [rest [Hjoin [Howner Hframe]]]].
    exists owned, rest; split; [exact Hjoin|]. split; [|exact Hframe].
    exact (conj (conj Hreturn Hphase) Howner). }
  assert (Hpack : flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
      (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current |--
    sem_pend_clear_status_phase_restore_output phase environment local critical sg original mask checkpoint ** frame).
  { rewrite (proj1 (flag_pend_task_save_input_closed_equiv environment critical local (fun _ _ => frame)
      sg returned (armv7a_irq_fiq_mask saved) current)).
    rewrite (proj2 Hsaved).
    intros heap [owned [rest [Hjoin [Howner Hframe]]]].
    exists owned, rest; split; [exact Hjoin|]. split; [|exact Hframe].
    exists returned, current; exact (conj (conj Hreturn Hphase) Howner). }
  pose (completed := @KernelCSequenceAdapt segment _ _ _ _ _ _ _ _ _
    Hinput (fun heap Hheap => Hheap) run Hpack).
  exists completed; split.
  - unfold completed; apply SemPendCSequenceCallAdapt; exact Hcertificate.
  - split.
    + apply Hpacket.
      exact (proj2 (kernel_program_c_sequence_resources environment critical sg
        original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ run)).
    + exact (proj2 (kernel_program_c_sequence_resources environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ completed)).
Qed.
End SemPendRestoreCSource.

(** An immediate concrete producer: the middle is the actual reflexive run
    on the prefix's returned owner. No receipt assumption is needed here. *)
Lemma sem_pend_client_restore_uninterrupted_c_sequence :
  forall environment critical sg original phase local mask saved acquired checkpoint arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor before written middle final_cursor after (frame : Assertion),
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (sem_pend_clear_status_phase_restore_input phase environment local critical sg original
    mask saved acquired checkpoint ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  exists completed : kernel_c_sequence
    (kernel_program_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
    checkpoint before
    (sem_pend_clear_status_phase_restore_input phase environment local critical sg original
      mask saved acquired checkpoint ** frame) false checkpoint after
    (sem_pend_clear_status_phase_restore_output phase environment local critical sg original mask checkpoint ** frame),
    sem_pend_c_sequence_call_certificate
      (kernel_program_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
      (sem_pend_restore_c_leaf_certificate environment critical sg original (fun _ _ _ _ _ _ _ _ _ _ => False))
      _ _ _ _ _ _ _ completed original.(os_sched_call_origin) original.(os_sched_call_origin) /\
    ((coq_prop (sem_pend_client_return_source environment critical sg original checkpoint original checkpoint /\
        sem_pend_clear_status_phase_restore_observation phase environment critical sg original checkpoint original checkpoint) &&
      sem_pend_fields_closed environment local sg original mask checkpoint) ** frame) after /\
    (sem_pend_clear_status_phase_restore_output phase environment local critical sg original mask checkpoint ** frame) after.
Proof.
  intros environment critical sg original phase local mask saved acquired checkpoint arch restore cursor before
    written middle final_cursor after frame Hr0 Hmask Hinput Hprefix Hsuffix.
  destruct (sem_pend_client_restore_prefix_c_sequence environment critical sg original
    (fun _ _ _ _ _ _ _ _ _ _ => False) phase local mask saved acquired checkpoint arch restore
    cursor before written middle frame Hr0 Hmask Hinput Hprefix)
    as [prefix [Hprefix_certificate [Hmiddle Hword]]].
  pose (body := @KernelCSequenceRefl
    (kernel_program_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
    checkpoint middle _ Hmiddle).
  eapply (sem_pend_client_restore_c_sequence environment critical sg original
    (fun _ _ _ _ _ _ _ _ _ _ => False)) with (body := body)
      (restore := restore) (cursor := cursor) (written := written) (final_cursor := final_cursor).
  - intros; contradiction.
  - exact Hr0.
  - exact Hmask.
  - exact Hinput.
  - exact Hprefix.
  - unfold body; constructor.
  - apply kernel_call_normal_return_refl.
  - exact Hsuffix.
Qed.
