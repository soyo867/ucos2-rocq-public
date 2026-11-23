Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_control_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_acquired_fields_prefix_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_wrapper_completion_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations KernelHeapObservation KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module OSIntExitReturnControl.
Import IRQAcquiredCPrefix SelectedCProgram SelectedControlComposition SelectedIRQWrapperCompletion.

Lemma os_int_exit_fields_frame_running_read : forall sg state frame heap value,
  (UCOS2_fields_inv sg state ** frame) heap ->
  uchar_load sg.(g_OSRunning) value heap ->
  value = (if state.(SchedState).(isRunning) then 1 else 0).
Proof.
  intros sg state frame heap value [owned [rest [Hjoin [[Hvalid Hraw] Hframe]]]] Hread.
  eapply uchar_load_deterministic; [exact Hread|].
  eapply uchar_load_frame; [eapply os_int_exit_fields_raw_running_load; exact Hraw|exact Hjoin].
Qed.

Lemma os_int_exit_fields_frame_counter_reads : forall sg state frame heap nesting locks,
  (UCOS2_fields_inv sg state ** frame) heap ->
  uchar_load sg.(g_OSIntNesting) nesting heap ->
  uchar_load sg.(g_OSLockNesting) locks heap ->
  state.(IntrState).(intNesting) = nesting /\ state.(IntrState).(lockNesting) = locks.
Proof.
  intros sg state frame heap nesting locks [owned [rest [Hjoin [[Hvalid Hraw] Hframe]]]] Hnest Hlock.
  split; eapply uchar_load_deterministic.
  - eapply uchar_load_frame; [eapply os_int_exit_fields_raw_nesting_load; exact Hraw|exact Hjoin].
  - exact Hnest.
  - eapply uchar_load_frame; [eapply os_int_exit_fields_raw_lock_load; exact Hraw|exact Hjoin].
  - exact Hlock.
Qed.

(** OSRunning is not reread at this acquired cut.  The supplied execution
    is the actual nesting read/write after the earlier C observation. *)
Lemma os_int_exit_acquired_counter_reads : forall sg entry frame before counted nesting locks,
  (UCOS2_fields_inv sg entry ** frame) before ->
  os_int_exit_acquired_counter_execution sg entry before counted ->
  uchar_load sg.(g_OSIntNesting) nesting counted ->
  uchar_load sg.(g_OSLockNesting) locks counted ->
  (interrupt_exit_state true entry.(IntrState)).(intNesting) = nesting /\
  (interrupt_exit_state true entry.(IntrState)).(lockNesting) = locks.
Proof.
  intros sg entry frame before counted nesting locks Hinput Hcounter Hnest Hlock.
  pose proof (os_int_exit_acquired_counter_fields_frame_preservation
    sg entry frame before counted Hinput Hcounter) as Hcounted.
  exact (os_int_exit_fields_frame_counter_reads sg (os_int_exit_counter_state true entry)
    frame counted nesting locks Hcounted Hnest Hlock).
Qed.

Lemma os_int_exit_wrapper_control_fields : forall observed entry incoming,
  let current := os_int_exit_wrapper_restored_state
    (os_int_exit_ready_checkpoint observed entry) incoming in
  current.(SchedState).(isRunning) = entry.(SchedState).(isRunning) /\
  current.(IntrState) = interrupt_exit_state observed entry.(IntrState).
Proof.
  intros observed entry incoming; cbv zeta; split.
  - exact (proj2 (proj2 (os_int_exit_checkpoint_current_frame observed entry))).
  - exact (os_int_exit_checkpoint_nesting_eq observed entry).
Qed.

Lemma os_int_exit_acquired_enabled_control : forall sg initial entry frame before counted incoming,
  os_sched_selection_enabled initial = true ->
  entry.(SchedState).(isRunning) = initial.(SchedState).(isRunning) ->
  (UCOS2_fields_inv sg entry ** frame) before ->
  os_int_exit_acquired_counter_execution sg entry before counted ->
  uchar_load sg.(g_OSIntNesting) 0 counted ->
  uchar_load sg.(g_OSLockNesting) 0 counted ->
  kernel_call_control_rely sg initial
    (os_int_exit_wrapper_restored_state (os_int_exit_ready_checkpoint true entry) incoming).
Proof.
  intros sg initial entry frame before counted incoming Henabled Hrunning Hinput Hcounter Hnest Hlock.
  unfold os_sched_selection_enabled in Henabled.
  apply Bool.andb_true_iff in Henabled; destruct Henabled as [Hint Hlocks].
  apply Z.eqb_eq in Hint; apply Z.eqb_eq in Hlocks.
  destruct (os_int_exit_acquired_counter_reads sg entry frame before counted 0 0
    Hinput Hcounter Hnest Hlock) as [Hfinal_int Hfinal_lock].
  destruct (os_int_exit_wrapper_control_fields true entry incoming) as [Hrun Hints].
  unfold kernel_call_control_rely; split; [congruence|].
  rewrite Hints.
  destruct (interrupt_exit_state true entry.(IntrState)), initial.(IntrState);
    simpl in *; f_equal; congruence.
Qed.

(** Both prefix pieces below are the supplied actual C sequence, sharing
    the observation heap.  The counter and selector share counted; the
    selector and descriptor completion share middle.  Initial enabled is
    the existing internal call-site observation, not a desired final fact. *)
Lemma os_int_exit_same_priority_wrapper_completion_control :
  forall environment critical sg original initial first_heap input observed read_heap observation_frame
    prefix_stop entry before acquired_frame acquire_stop counted middle priority
    local suspended receipt node handler frame after
    (prefix : kernel_c_sequence (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap input prefix_stop observed read_heap
      (UCOS2_fields_inv sg observed ** observation_frame))
    (acquire : kernel_c_sequence (kernel_program_selected_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      observed read_heap (UCOS2_fields_inv sg observed ** observation_frame)
      acquire_stop entry before (UCOS2_fields_inv sg entry ** acquired_frame)),
  uchar_load sg.(g_OSRunning) 1 read_heap ->
  os_int_exit_full_call environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical sg handler observed (OsIntExitReturned entry) ->
  os_int_exit_acquired_counter_execution sg entry before counted ->
  uchar_load sg.(g_OSIntNesting) 0 counted ->
  uchar_load sg.(g_OSLockNesting) 0 counted ->
  os_int_exit_selection_heap_fragment sg counted middle ->
  uchar_load sg.(g_OSPrioHighRdy) priority middle ->
  uchar_load sg.(g_OSPrioCur) priority middle ->
  irq_wrapper_c_completion environment sg (os_int_exit_ready_checkpoint true entry)
    local suspended receipt original node handler frame middle after ->
  os_sched_selection_enabled initial = true ->
  kernel_call_control_rely sg initial
    (os_int_exit_wrapper_restored_state (os_int_exit_ready_checkpoint true entry)
      suspended.(armv7a_continuation_stack)) /\
  os_int_exit_requests_switch true entry = false /\
  irq_wrapper_c_input environment sg (os_int_exit_ready_checkpoint true entry)
    local suspended receipt handler frame middle /\
  irq_wrapper_c_output environment sg (os_int_exit_ready_checkpoint true entry)
    local suspended receipt original handler frame after.
Proof.
  intros environment critical sg original initial first_heap input observed read_heap observation_frame
    prefix_stop entry before acquired_frame acquire_stop counted middle priority
    local suspended receipt node handler frame after prefix acquire
    Hread Hreturned Hcounter Hnest Hlock Hselect Hhigh Hcur Hcomplete Henabled.
  pose proof (proj2 (kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ prefix))
    as Hobserved.
  pose proof (proj2 (kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ acquire))
    as Hacquired.
  assert (Hobserved_running : observed.(SchedState).(isRunning) = true).
  { pose proof (os_int_exit_fields_frame_running_read sg observed observation_frame read_heap 1
      Hobserved Hread) as Hr; destruct observed.(SchedState).(isRunning); congruence. }
  pose proof (kernel_program_selected_c_sequence_running _ _ _ _ _ _ _ _ _ _ _ _ prefix) as Hp.
  pose proof (kernel_program_selected_c_sequence_running _ _ _ _ _ _ _ _ _ _ _ _ acquire) as Ha.
  split.
  - eapply os_int_exit_acquired_enabled_control;
      [exact Henabled|congruence|exact Hacquired|exact Hcounter|exact Hnest|exact Hlock].
  - split.
    + change (os_int_exit_return_relation critical sg handler observed entry) in Hreturned.
      destruct Hreturned as [_ Hnoswitch]; rewrite Hobserved_running in Hnoswitch; exact Hnoswitch.
    + exact (irq_wrapper_c_completion_resources environment sg (os_int_exit_ready_checkpoint true entry)
        local suspended receipt original node handler frame middle after Hcomplete).
Qed.

(** The real inactive branch does not acquire, decrement or select.  Its
    local control conclusion is relative to the actual OSRunning cut. *)
Lemma os_int_exit_inactive_wrapper_completion_control :
  forall environment critical sg original observed read_heap observation_frame entry
    local suspended receipt node handler frame after,
  (UCOS2_fields_inv sg observed ** observation_frame) read_heap ->
  uchar_load sg.(g_OSRunning) 0 read_heap ->
  os_int_exit_full_call environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical sg handler observed (OsIntExitReturned entry) ->
  irq_wrapper_c_completion environment sg (os_int_exit_ready_checkpoint false entry)
    local suspended receipt original node handler frame read_heap after ->
  kernel_call_control_rely sg observed
    (os_int_exit_wrapper_restored_state (os_int_exit_ready_checkpoint false entry)
      suspended.(armv7a_continuation_stack)) /\
  irq_wrapper_c_output environment sg (os_int_exit_ready_checkpoint false entry)
    local suspended receipt original handler frame after.
Proof.
  intros environment critical sg original observed read_heap observation_frame entry
    local suspended receipt node handler frame after Hobserved Hread Hreturned Hcomplete.
  assert (Hrunning : observed.(SchedState).(isRunning) = false).
  { pose proof (os_int_exit_fields_frame_running_read sg observed observation_frame read_heap 0
      Hobserved Hread) as Hr; destruct observed.(SchedState).(isRunning); congruence. }
  change (os_int_exit_return_relation critical sg handler observed entry) in Hreturned.
  destruct Hreturned as [Hentry Hnoswitch]; rewrite Hrunning in Hentry; subst entry.
  split; [split; reflexivity|].
  exact (proj2 (irq_wrapper_c_completion_resources environment sg (os_int_exit_ready_checkpoint false observed)
    local suspended receipt original node handler frame read_heap after Hcomplete)).
Qed.

End OSIntExitReturnControl.
