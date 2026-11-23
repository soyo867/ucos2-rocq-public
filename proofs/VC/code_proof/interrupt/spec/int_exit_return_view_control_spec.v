Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_execution.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_returned_c_segment_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module OSIntExitReturnView.
Import OSIntExitReturnedC BuiltinComponent.

(** Existing first-level entry computes this very parked state from the
    original C counter cut.  Its checked fields producer supplies the
    corresponding actual heap; this projection adds no resource law. *)
Lemma os_int_exit_first_level_entry_nesting_agrees : forall entry handler sp fragments,
  entry.(SchedState).(isRunning) = true -> entry.(IntrState).(intNesting) = 0 ->
  kernel_interrupt_nesting_agrees true (os_int_exit_execution_view handler).(os_execution_context)
    (armv7a_irq_live_parked_state entry handler.(os_int_exit_interrupted_call) sp fragments).(IntrState).
Proof.
  intros entry handler sp fragments Hrunning Hzero Htrue.
  unfold armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
    os_sched_save_current_sp, armv7a_irq_entry_counter_state.
  rewrite Hrunning; cbn; rewrite Hzero; reflexivity.
Qed.

Lemma os_int_exit_first_level_entry_lock_nesting : forall entry handler sp fragments,
  (armv7a_irq_live_parked_state entry handler.(os_int_exit_interrupted_call) sp fragments).(IntrState).(lockNesting) =
    entry.(IntrState).(lockNesting).
Proof.
  intros; unfold armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
    os_sched_save_current_sp, armv7a_irq_entry_counter_state.
  destruct entry.(SchedState).(isRunning); reflexivity.
Qed.

(** The exact actual OSIntEnter completion/code appears in the statement.
    The documented depth bound concerns entry, including its saturation
    branch; no desired return count is supplied. *)
Lemma kernel_counter_c_enter_context :
  forall sg entry frame before after code handler context,
  kernel_counter_c_completion KernelCounterCEnter sg entry frame before after code ->
  kernel_interrupt_nesting_agrees entry.(SchedState).(isRunning) context entry.(IntrState) ->
  (entry.(SchedState).(isRunning) = true -> (kernel_interrupt_depth context < 255)%nat) ->
  (UCOS2_fields_raw_rep sg entry ** frame) before /\
  (UCOS2_fields_raw_rep sg (kernel_counter_c_state KernelCounterCEnter entry) ** frame) after /\
  kernel_control_step (KernelEnterInterrupt handler entry.(SchedState).(isRunning))
    context entry.(IntrState) (KernelInterrupt handler context)
    (kernel_counter_c_state KernelCounterCEnter entry).(IntrState) false /\
  kernel_interrupt_nesting_agrees entry.(SchedState).(isRunning) (KernelInterrupt handler context)
    (kernel_counter_c_state KernelCounterCEnter entry).(IntrState).
Proof.
  intros sg entry frame before after code handler context Hactual Hagrees Hbound.
  destruct Hactual as [Hbefore Hafter]; split; [exact Hbefore|].
  split; [exact Hafter|]; split; [constructor|].
  apply kernel_interrupt_entry_preserves_nesting_agreement; assumption.
Qed.

(** This identity is obtained from the earlier actual save of the SAME
    descriptor and handler, not from the shape [Some original] alone. *)
Lemma os_int_exit_returned_c_completion_interrupted_call :
  forall environment critical sg observed read_heap observation_frame entry local suspended receipt
    original node handler frame before middle after save_before save_after,
  os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
    entry local suspended receipt original node handler frame before middle after ->
  armv7a_save_transition environment.(task_stack_call_continuations) handler suspended save_before save_after ->
  original = handler.(os_int_exit_interrupted_call).
Proof.
  intros until save_after; intros Hcomplete Hsave.
  pose proof (os_int_exit_returned_saved_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete) as Hcall.
  destruct (armv7a_save_transition_observations _ _ _ environment.(task_stack_call_continuations)
    handler suspended save_before save_after Hsave) as [_ [Hsaved _]].
  congruence.
Qed.

(** This binds the C counter decision to its real return view.  The
    primitive ABI resources still come from the actual macro completion. *)
Lemma os_int_exit_returned_c_completion_context_step :
  forall environment critical sg observed read_heap observation_frame entry local suspended receipt
    original node handler frame before middle after save_before save_after,
  os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
    entry local suspended receipt original node handler frame before middle after ->
  armv7a_save_transition environment.(task_stack_call_continuations) handler suspended save_before save_after ->
  kernel_control_step (KernelExitInterrupt observed.(SchedState).(isRunning))
    (os_int_exit_execution_view handler).(os_execution_context) entry.(IntrState)
    (os_sched_execution_view original).(os_execution_context)
    (os_int_exit_wrapper_restored_state
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
      suspended.(armv7a_continuation_stack)).(IntrState)
    (interrupt_exit_requests_schedule observed.(SchedState).(isRunning) entry.(IntrState)).
Proof.
  intros until save_after; intros Hcomplete Hsave.
  pose proof (os_int_exit_returned_c_completion_interrupted_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hcomplete Hsave) as Horiginal.
  rewrite Horiginal, (os_int_exit_returned_c_completion_intr_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete).
  constructor.
Qed.

Lemma os_int_exit_returned_c_completion_nesting_agrees :
  forall environment critical sg observed read_heap observation_frame entry local suspended receipt
    original node handler frame before middle after save_before save_after,
  os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
    entry local suspended receipt original node handler frame before middle after ->
  armv7a_save_transition environment.(task_stack_call_continuations) handler suspended save_before save_after ->
  kernel_interrupt_nesting_agrees observed.(SchedState).(isRunning)
    (os_int_exit_execution_view handler).(os_execution_context) entry.(IntrState) ->
  kernel_interrupt_nesting_agrees observed.(SchedState).(isRunning)
    (os_sched_execution_view original).(os_execution_context)
    (os_int_exit_wrapper_restored_state
      (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
      suspended.(armv7a_continuation_stack)).(IntrState).
Proof.
  intros until save_after; intros Hcomplete Hsave Hagrees.
  pose proof (os_int_exit_returned_c_completion_interrupted_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hcomplete Hsave) as Horiginal.
  rewrite Horiginal, (os_int_exit_returned_c_completion_intr_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcomplete).
  eapply kernel_interrupt_exit_preserves_nesting_agreement; exact Hagrees.
Qed.

(** Acquired agreement is an incoming source-protocol invariant, to be
    produced by the same entry/body execution.  This adapter does not
    declare it for arbitrary flat C sequences. *)
Lemma os_int_exit_returned_c_completion_task_nesting_zero :
  forall environment critical sg observed read_heap observation_frame entry local suspended receipt
    original node handler frame before middle after save_before save_after,
  os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
    entry local suspended receipt original node handler frame before middle after ->
  armv7a_save_transition environment.(task_stack_call_continuations) handler suspended save_before save_after ->
  kernel_interrupt_nesting_agrees observed.(SchedState).(isRunning)
    (os_int_exit_execution_view handler).(os_execution_context) entry.(IntrState) ->
  observed.(SchedState).(isRunning) = true ->
  (os_int_exit_wrapper_restored_state
    (os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry)
    suspended.(armv7a_continuation_stack)).(IntrState).(intNesting) = 0.
Proof.
  intros until save_after; intros Hcomplete Hsave Hagrees Hrunning.
  pose proof (os_int_exit_returned_c_completion_nesting_agrees _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hcomplete Hsave Hagrees) as Hreturned.
  exact (Hreturned Hrunning).
Qed.

(** Inside a running ISR, the real C lock/unlock guards skip both writes.
    This is independent of the ISR's eventual return and of its caller's
    initial lock count. *)
Lemma kernel_interrupt_sched_lock_counters_eq : forall handler interrupted counters,
  kernel_interrupt_nesting_agrees true (KernelInterrupt handler interrupted) counters ->
  sched_lock_state true counters = counters.
Proof.
  intros handler interrupted counters Hagrees.
  pose proof (kernel_running_interrupt_nesting_positive _ _ _ Hagrees) as Hpositive.
  assert (Hzero : (counters.(intNesting) =? 0) = false) by (apply Z.eqb_neq; lia).
  unfold sched_lock_state; cbn; rewrite Hzero; reflexivity.
Qed.

Lemma kernel_interrupt_sched_unlock_counters_eq : forall handler interrupted counters,
  kernel_interrupt_nesting_agrees true (KernelInterrupt handler interrupted) counters ->
  sched_unlock_state true counters = counters.
Proof.
  intros handler interrupted counters Hagrees.
  pose proof (kernel_running_interrupt_nesting_positive _ _ _ Hagrees) as Hpositive.
  assert (Hzero : (counters.(intNesting) =? 0) = false) by (apply Z.eqb_neq; lia).
  unfold sched_unlock_state; cbn; rewrite Hzero; reflexivity.
Qed.

End OSIntExitReturnView.
