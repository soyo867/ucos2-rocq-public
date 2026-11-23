(* Report candidate: actual module completions; staged only by the parent. *)
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_phase_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_phase_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_selected_c_source_spec.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.

Module SelectedExecutionEvents.
Import SelectedEnvironmentPhaseEffects SelectedEnvironmentPhaseProperties.
Import ContinuationPhaseEffects SelectedEventSources.

Lemma selected_save_execution_program_and_event :
  forall environment critical local next_local active sg original mask before first_heap
    saved stopped returned current last_heap,
  os_sched_continuation_c_save_execution environment critical local next_local active sg
    original mask before first_heap saved stopped returned current last_heap ->
  ContinuationPhaseEffects.os_sched_continuation_phase_save_program environment critical sg original mask
    before (returned, saved) current /\ interrupt_saved_value mask saved /\
  flag_pend_selected_completed_source FlagPendSaveSource environment critical sg
    (FlagPendTaskCaller original) original before
    (flag_pend_caller_save_input environment critical local active sg
      (FlagPendTaskCaller original) original mask before) first_heap
    (FlagPendTaskCaller returned) returned current last_heap
    (flag_pend_caller_restore_input environment critical next_local active sg
      (FlagPendTaskCaller returned) returned saved current current).
Proof.
  intros until last_heap; intro Hactual.
  destruct (SelectedEnvironmentPhaseEffects.os_sched_continuation_c_save_execution_effect_source
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual) as [Heffect [Hsaved Hsource]].
  split.
  - apply ContinuationPhaseEffects.os_sched_scoped_phase_save_effect_implies_phase; exact Heffect.
  - split; [exact Hsaved|]. eapply flag_pend_task_save_source_from_execution; exact Hactual.
Qed.

Lemma selected_restore_execution_program_and_event :
  forall environment critical local next_local active sg original saved acquired before first_heap
    stopped returned current last_heap,
  os_sched_continuation_c_restore_execution environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap ->
  ContinuationPhaseEffects.os_sched_continuation_phase_restore_program environment critical sg original before returned current /\
  flag_pend_selected_completed_source FlagPendRestoreSource environment critical sg
    (FlagPendTaskCaller original) original before
    (flag_pend_caller_restore_input environment critical local active sg
      (FlagPendTaskCaller original) original saved acquired before) first_heap
    (FlagPendTaskCaller returned) returned current last_heap
    (flag_pend_caller_save_input environment critical next_local active sg
      (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current).
Proof.
  intros until last_heap; intro Hactual.
  destruct (SelectedEnvironmentPhaseEffects.os_sched_continuation_c_restore_execution_effect_source
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual) as [Heffect Hsource].
  split.
  - apply ContinuationPhaseEffects.os_sched_scoped_phase_restore_effect_implies_phase; exact Heffect.
  - eapply flag_pend_task_restore_source_from_execution; exact Hactual.
Qed.
End SelectedExecutionEvents.
