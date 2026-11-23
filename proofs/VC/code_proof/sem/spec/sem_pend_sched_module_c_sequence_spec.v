Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_module_registry_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_history_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import BuiltinComponent SelectedReturnPrimitive SelectedCompletionSource SelectedCProgram SelectedCSource.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Lift one actual builtin completion.  Both markers describe the same
    constructed atom; no registered-to-critical membership is used. *)
Lemma sem_pend_builtin_selected_c_sequence :
  forall environment critical local sg observer origin event_observer state before current after input output
    (segment : kernel_builtin_c_segment environment critical local sg state before current after input output),
  kernel_builtin_c_segment_source environment critical local sg observer
    state before current after input output segment ->
  exists run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    state before input false current after output,
    kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
      state before input false current after output run /\
    sem_pend_selected_c_sequence_receipt environment critical sg observer origin
      state before input false current after output run.
Proof.
  intros environment critical local sg observer origin event_observer state before current after input output segment Hsource.
  set (original := @KernelProgramCBuiltin environment critical sg observer origin local
    state before current after input output segment).
  set (returned := @KernelProgramReturnOriginal environment critical sg observer origin
    state before input false current after output original).
  set (selected := @KernelSelectedProgramReturn critical sg observer origin environment
    state before input false current after output returned).
  exists (KernelCSequenceAtom _ state before input false current after output selected).
  split.
  - apply KernelCSourceAtom; unfold selected, returned, original.
    apply KernelSelectedProgramReturnSource, KernelProgramReturnOriginalSource.
    right; apply KernelProgramCBuiltinSource; exact Hsource.
  - apply KernelCSourceAtom; unfold selected, returned, original.
    apply SemPendSelectedReturnReceipt, SemPendReturnOriginalReceipt, SemPendProgramBuiltinReceipt.
Qed.

(** Counter framing opens the same fields world.  The actual resource
    producer supplies its new pure invariant at this finite post; the
    parked map, unmap table and caller frame are never discarded. *)
Lemma sem_pend_counter_fields_c_sequence :
  forall environment critical local sg observer origin event_observer operation state before after (frame : Assertion)
    (code : kernel_counter_c_code operation sg before after),
  (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg state ** frame) before ->
  (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg
     (kernel_counter_c_state operation state) ** frame) after ->
  exists run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    state before
    (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg state ** frame)
    false (kernel_counter_c_state operation state) after
    (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg
      (kernel_counter_c_state operation state) ** frame),
    kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
      _ _ _ _ _ _ _ run /\
    sem_pend_selected_c_sequence_receipt environment critical sg observer origin _ _ _ _ _ _ _ run.
Proof.
  intros environment critical local sg observer origin event_observer operation state before after frame code Hpre Hpost.
  set (residual := unmap_table_rep sg **
    store_parked_continuations
      (kernel_saved_continuation_entry environment.(task_stack_call_continuations) state.(TskState) local)
      state.(TskState).(parkedTaskStacks) ** frame).
  assert (Htasks : (kernel_counter_c_state operation state).(TskState) = state.(TskState)).
  { destruct operation; reflexivity. }
  assert (Hfacts_open :
    kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg
      (kernel_counter_c_state operation state) ** frame |--
    coq_prop (UCOS2_state_inv sg (kernel_counter_c_state operation state) /\
      task_stack_live_coverage (kernel_counter_c_state operation state).(TskState) None) && TT).
  { unfold kernel_client_continuation_fields_world, kernel_continuation_inv, kernel_program_fields_inv; entailer!. }
  destruct (proj1 (Hfacts_open after Hpost)) as [Hvalid Hcoverage].
  assert (Hopen : kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg state ** frame |--
    UCOS2_fields_raw_rep sg state ** residual).
  { unfold kernel_client_continuation_fields_world, kernel_continuation_inv,
      kernel_program_fields_inv, kernel_program_fields_rep, residual; entailer!. }
  assert (Hclose : UCOS2_fields_raw_rep sg (kernel_counter_c_state operation state) ** residual |--
    kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg
      (kernel_counter_c_state operation state) ** frame).
  { unfold kernel_client_continuation_fields_world, kernel_continuation_inv,
      kernel_program_fields_inv, kernel_program_fields_rep, residual.
    rewrite Htasks in *; entailer!. }
  pose proof (kernel_counter_c_completion_from_execution operation sg state residual before after code
    (Hopen before Hpre)) as Hcomplete.
  set (segment := @KernelBuiltinCCounter environment critical local sg operation state residual before after code Hcomplete).
  assert (Hsource : kernel_builtin_c_segment_source environment critical local sg observer _ _ _ _ _ _ segment).
  { unfold segment; constructor. }
  destruct (sem_pend_builtin_selected_c_sequence environment critical local sg observer origin event_observer
    _ _ _ _ _ _ segment Hsource) as [inner [Hinner Hreceipt]].
  exists (KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hpre Hopen inner Hclose).
  split; apply KernelCSourceAdapt; assumption.
Qed.

Lemma sem_pend_module_enter_c_sequence :
  forall environment critical local sg observer origin event_observer state before after (frame : Assertion),
  kernel_client_int_enter_fragment sg before after ->
  (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg state ** frame) before ->
  exists run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    state before
    (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg state ** frame)
    false (os_int_enter_state state) after
    (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg (os_int_enter_state state) ** frame),
    kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer _ _ _ _ _ _ _ run /\
    sem_pend_selected_c_sequence_receipt environment critical sg observer origin _ _ _ _ _ _ _ run.
Proof.
  intros environment critical local sg observer origin event_observer state before after frame Hcode Hpre.
  pose proof (kernel_client_int_enter_continuation_fields_resources _ _ _ environment.(task_stack_call_continuations)
    local sg state frame before after Hpre Hcode) as Hpost.
  exact (sem_pend_counter_fields_c_sequence environment critical local sg observer origin event_observer
    KernelCounterCEnter state before after frame Hcode Hpre Hpost).
Qed.

Lemma sem_pend_module_exit_c_sequence :
  forall environment critical local sg observer origin event_observer state before after (frame : Assertion),
  os_int_exit_masked_no_schedule_fragment sg before after ->
  (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg state ** frame) before ->
  exists run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    state before
    (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg state ** frame)
    false (os_int_exit_counter_state state.(SchedState).(isRunning) state) after
    (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg
      (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame),
    kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer _ _ _ _ _ _ _ run /\
    sem_pend_selected_c_sequence_receipt environment critical sg observer origin _ _ _ _ _ _ _ run.
Proof.
  intros environment critical local sg observer origin event_observer state before after frame Hcode Hpre.
  pose proof (kernel_client_int_exit_continuation_fields_resources _ _ _ environment.(task_stack_call_continuations)
    local sg state frame before after Hpre Hcode) as Hpost.
  assert (Hraw : exists residual : Assertion, (UCOS2_fields_raw_rep sg state ** residual) before).
  { set (residual := unmap_table_rep sg **
      store_parked_continuations
        (kernel_saved_continuation_entry environment.(task_stack_call_continuations) state.(TskState) local)
        state.(TskState).(parkedTaskStacks) ** frame).
    assert (Hopen : kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg state ** frame |--
      UCOS2_fields_raw_rep sg state ** residual).
    { unfold kernel_client_continuation_fields_world, kernel_continuation_inv,
        kernel_program_fields_inv, kernel_program_fields_rep, residual; entailer!. }
    exists residual; exact (Hopen before Hpre). }
  destruct Hraw as [residual Hraw].
  assert (Hcounter : os_int_exit_masked_counter_fragment sg before state.(SchedState).(isRunning) after).
  { destruct Hcode as [before after Hcounter|before after nesting Hcounter Hload Hnonzero|before after locks Hcounter Hnest Hlock Hnonzero];
      pose proof (os_int_exit_counter_fields_raw_frame_observation sg state residual before _ after Hraw Hcounter)
        as [Hobserved Hwrites]; rewrite <- Hobserved; exact Hcounter. }
  exact (sem_pend_counter_fields_c_sequence environment critical local sg observer origin event_observer
    (KernelCounterCExit state.(SchedState).(isRunning)) state before after frame Hcounter Hpre Hpost).
Qed.

Lemma sem_pend_module_publication_c_sequence :
  forall environment critical local sg observer origin event_observer publication state before after (frame : Assertion),
  publication.(stack_publication_invocation) <> observer ->
  task_tcb_init_publication_tail_fragment sg (task_create_stack_publication_args publication).(initPrio)
    (task_slot_addr sg publication.(stack_publication_slot)) before after ->
  (kernel_client_continuation_fields_publication environment.(task_stack_call_continuations) local sg publication state ** frame) before ->
  exists run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    state before
    (kernel_client_continuation_fields_publication environment.(task_stack_call_continuations) local sg publication state ** frame)
    false (task_create_stack_publication_state sg publication state) after
    (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg
      (task_create_stack_publication_state sg publication state) ** frame),
    kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer _ _ _ _ _ _ _ run /\
    sem_pend_selected_c_sequence_receipt environment critical sg observer origin _ _ _ _ _ _ _ run.
Proof.
  intros environment critical local sg observer origin event_observer publication state before after frame Hforeign Hcode Hpre.
  destruct (kernel_publication_c_completion_from_execution environment.(task_stack_call_continuations) local
    sg publication state frame before after Hcode Hpre) as [effect Hcomplete].
  set (segment := @KernelBuiltinCPublication environment critical local sg publication state frame before after Hcode effect Hcomplete).
  assert (Hsource : kernel_builtin_c_segment_source environment critical local sg observer _ _ _ _ _ _ segment).
  { unfold segment; constructor; exact Hforeign. }
  exact (sem_pend_builtin_selected_c_sequence environment critical local sg observer origin event_observer
    _ _ _ _ _ _ segment Hsource).
Qed.

(** These consume the literal heap fragments at the original three builtin
    dispatcher cuts. The same run supplies the source, receipt and final
    owner. The open Extra constructor is not represented by these lemmas. *)
Lemma sem_pend_module_enter_c_prefix :
  forall environment critical local sg observer (origin : TaskInvocationOrigin) (event_observer : option nat)
    state before after (frame : Assertion),
  kernel_client_int_enter_fragment sg before after ->
  (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg state ** frame) before ->
  exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer
    state (os_int_enter_state state) after,
    sem_pend_sched_prefix_receipt environment critical sg observer _ _ _ prefix /\
    (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg (os_int_enter_state state) ** frame) after.
Proof.
  intros environment critical local sg observer origin event_observer state before after frame Hcode Hpre.
  destruct (sem_pend_module_enter_c_sequence environment critical local sg observer origin event_observer
    state before after frame Hcode Hpre) as [run [Hsource Hreceipt]].
  exists (@SchedulerPhaseCandidate.OsSchedTaskReturnPrefixCSequence environment critical sg observer
    origin event_observer _ _ _ _ _ _ _ run Hsource).
  split; [constructor; exact Hreceipt|].
  exact (proj2 (kernel_c_sequence_resources _
    (kernel_program_selected_c_step_resources environment critical sg observer origin) _ _ _ _ _ _ _ run)).
Qed.

Lemma sem_pend_module_exit_c_prefix :
  forall environment critical local sg observer (origin : TaskInvocationOrigin) (event_observer : option nat)
    state before after (frame : Assertion),
  os_int_exit_masked_no_schedule_fragment sg before after ->
  (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg state ** frame) before ->
  exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer
    state (os_int_exit_counter_state state.(SchedState).(isRunning) state) after,
    sem_pend_sched_prefix_receipt environment critical sg observer _ _ _ prefix /\
    (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg
      (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame) after.
Proof.
  intros environment critical local sg observer origin event_observer state before after frame Hcode Hpre.
  destruct (sem_pend_module_exit_c_sequence environment critical local sg observer origin event_observer
    state before after frame Hcode Hpre) as [run [Hsource Hreceipt]].
  exists (@SchedulerPhaseCandidate.OsSchedTaskReturnPrefixCSequence environment critical sg observer
    origin event_observer _ _ _ _ _ _ _ run Hsource).
  split; [constructor; exact Hreceipt|].
  exact (proj2 (kernel_c_sequence_resources _
    (kernel_program_selected_c_step_resources environment critical sg observer origin) _ _ _ _ _ _ _ run)).
Qed.

Lemma sem_pend_module_publication_c_prefix :
  forall environment critical local sg observer (origin : TaskInvocationOrigin) (event_observer : option nat)
    publication state before after (frame : Assertion),
  publication.(stack_publication_invocation) <> observer ->
  task_tcb_init_publication_tail_fragment sg (task_create_stack_publication_args publication).(initPrio)
    (task_slot_addr sg publication.(stack_publication_slot)) before after ->
  (kernel_client_continuation_fields_publication environment.(task_stack_call_continuations) local sg publication state ** frame) before ->
  exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer
    state (task_create_stack_publication_state sg publication state) after,
    sem_pend_sched_prefix_receipt environment critical sg observer _ _ _ prefix /\
    (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg
      (task_create_stack_publication_state sg publication state) ** frame) after.
Proof.
  intros environment critical local sg observer origin event_observer publication state before after frame Hforeign Hcode Hpre.
  destruct (sem_pend_module_publication_c_sequence environment critical local sg observer origin event_observer
    publication state before after frame Hforeign Hcode Hpre) as [run [Hsource Hreceipt]].
  exists (@SchedulerPhaseCandidate.OsSchedTaskReturnPrefixCSequence environment critical sg observer
    origin event_observer _ _ _ _ _ _ _ run Hsource).
  split; [constructor; exact Hreceipt|].
  exact (proj2 (kernel_c_sequence_resources _
    (kernel_program_selected_c_step_resources environment critical sg observer origin) _ _ _ _ _ _ _ run)).
Qed.
