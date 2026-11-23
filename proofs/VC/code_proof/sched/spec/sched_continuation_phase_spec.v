Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_boot_primitive_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_phase_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_effect_properties_spec.
Local Open Scope Z_scope.

(** SelectedEnvironmentPhaseEffects is the frozen scoped C implementation.
    This successor reuses that exact execution type. The additional Boot
    alternative contains the approved primitive post and its actual heaps. *)
Module ContinuationPhaseEffects.

Definition os_sched_continuation_phase_save_effect environment critical sg
  original mask saved before returned acquired : Prop :=
  os_sched_continuation_save_effect environment critical sg
    original mask saved before returned acquired \/
  (exists local next_local active first_heap stopped last_heap,
    SelectedEnvironmentPhaseEffects.os_sched_continuation_c_save_execution
      environment critical local next_local active sg
      original mask before first_heap saved stopped returned acquired last_heap) \/
  FlagPendBootPrimitive.flag_pend_boot_save_effect environment critical sg
    original mask saved before returned acquired.

Definition os_sched_continuation_phase_restore_effect environment critical sg
  original released returned current : Prop :=
  os_sched_continuation_restore_effect environment critical sg original released returned current \/
  (exists local next_local active saved acquired first_heap stopped last_heap,
    SelectedEnvironmentPhaseEffects.os_sched_continuation_c_restore_execution
      environment critical local next_local active sg
      original saved acquired released first_heap stopped returned current last_heap) \/
  FlagPendBootPrimitive.flag_pend_boot_restore_effect environment critical sg
    original released returned current.

Definition os_sched_continuation_phase_save_program environment critical sg original mask :
  program UCOS2_Verify_State (OsSchedCallContext * Z) :=
  fun before result acquired => os_sched_continuation_phase_save_effect environment critical sg
    original mask (snd result) before (fst result) acquired.

Definition os_sched_continuation_phase_restore_program environment critical sg resumed :
  program UCOS2_Verify_State OsSchedCallContext :=
  fun released returned current => os_sched_continuation_phase_restore_effect environment critical sg
    resumed released returned current.

Lemma os_sched_continuation_save_effect_implies_phase :
  forall environment critical sg original mask saved before returned acquired,
  os_sched_continuation_save_effect environment critical sg original mask saved before returned acquired ->
  os_sched_continuation_phase_save_effect environment critical sg original mask saved before returned acquired.
Proof. intros; left; assumption. Qed.

Lemma os_sched_continuation_restore_effect_implies_phase :
  forall environment critical sg original released returned current,
  os_sched_continuation_restore_effect environment critical sg original released returned current ->
  os_sched_continuation_phase_restore_effect environment critical sg original released returned current.
Proof. intros; left; assumption. Qed.

Lemma os_sched_continuation_c_save_execution_implies_phase :
  forall environment critical local next_local active sg original mask before first_heap
    saved stopped returned current last_heap,
  SelectedEnvironmentPhaseEffects.os_sched_continuation_c_save_execution
    environment critical local next_local active sg
    original mask before first_heap saved stopped returned current last_heap ->
  os_sched_continuation_phase_save_effect environment critical sg original mask saved before returned current.
Proof.
  intros until last_heap; intro Hactual; right; left.
  exists local, next_local, active, first_heap, stopped, last_heap; exact Hactual.
Qed.

Lemma os_sched_continuation_c_restore_execution_implies_phase :
  forall environment critical local next_local active sg original saved acquired before first_heap
    stopped returned current last_heap,
  SelectedEnvironmentPhaseEffects.os_sched_continuation_c_restore_execution
    environment critical local next_local active sg
    original saved acquired before first_heap stopped returned current last_heap ->
  os_sched_continuation_phase_restore_effect environment critical sg original before returned current.
Proof.
  intros until last_heap; intro Hactual; right; left.
  exists local, next_local, active, saved, acquired, first_heap, stopped, last_heap; exact Hactual.
Qed.

Lemma flag_pend_boot_save_completion_implies_phase :
  forall environment critical local next_local sg original mask saved
    before first_heap returned acquired last_heap,
  FlagPendBootPrimitive.flag_pend_boot_save_completion environment critical local next_local sg
    original mask saved before first_heap returned acquired last_heap ->
  os_sched_continuation_phase_save_effect environment critical sg original mask saved before returned acquired.
Proof.
  intros until last_heap; intro Hcomplete; right; right.
  exact (FlagPendBootPrimitive.flag_pend_boot_save_completion_effect
    environment critical local next_local sg original mask saved before first_heap
    returned acquired last_heap Hcomplete).
Qed.

Lemma flag_pend_boot_restore_completion_implies_phase :
  forall environment critical local next_local sg original saved
    acquired released first_heap returned current last_heap,
  FlagPendBootPrimitive.flag_pend_boot_restore_completion environment critical local next_local sg
    original saved acquired released first_heap returned current last_heap ->
  os_sched_continuation_phase_restore_effect environment critical sg original released returned current.
Proof.
  intros until last_heap; intro Hcomplete; right; right.
  exact (FlagPendBootPrimitive.flag_pend_boot_restore_completion_effect
    environment critical local next_local sg original saved acquired released first_heap
    returned current last_heap Hcomplete).
Qed.

Lemma flag_pend_boot_save_effect_implies_phase :
  forall environment critical sg original mask saved before returned acquired,
  FlagPendBootPrimitive.flag_pend_boot_save_effect environment critical sg
    original mask saved before returned acquired ->
  os_sched_continuation_phase_save_effect environment critical sg original mask saved before returned acquired.
Proof. intros; right; right; assumption. Qed.

Lemma flag_pend_boot_restore_effect_implies_phase :
  forall environment critical sg original released returned current,
  FlagPendBootPrimitive.flag_pend_boot_restore_effect environment critical sg
    original released returned current ->
  os_sched_continuation_phase_restore_effect environment critical sg original released returned current.
Proof. intros; right; right; assumption. Qed.

Lemma os_sched_scoped_phase_save_effect_implies_phase :
  forall environment critical sg original mask saved before returned acquired,
  SelectedEnvironmentPhaseEffects.os_sched_continuation_phase_save_effect
    environment critical sg original mask saved before returned acquired ->
  os_sched_continuation_phase_save_effect environment critical sg original mask saved before returned acquired.
Proof.
  intros environment critical sg original mask saved before returned acquired [Hold|Hactual].
  - left; exact Hold.
  - right; left; exact Hactual.
Qed.

Lemma os_sched_scoped_phase_restore_effect_implies_phase :
  forall environment critical sg original released returned current,
  SelectedEnvironmentPhaseEffects.os_sched_continuation_phase_restore_effect
    environment critical sg original released returned current ->
  os_sched_continuation_phase_restore_effect environment critical sg original released returned current.
Proof.
  intros environment critical sg original released returned current [Hold|Hactual].
  - left; exact Hold.
  - right; left; exact Hactual.
Qed.

Lemma os_sched_continuation_save_program_implies_phase :
  forall environment critical sg original mask before result acquired,
  os_sched_continuation_save_program environment critical sg original mask before result acquired ->
  os_sched_continuation_phase_save_program environment critical sg original mask before result acquired.
Proof. intros; apply os_sched_continuation_save_effect_implies_phase; assumption. Qed.

Lemma os_sched_continuation_restore_program_implies_phase :
  forall environment critical sg resumed released returned current,
  os_sched_continuation_restore_program environment critical sg resumed released returned current ->
  os_sched_continuation_phase_restore_program environment critical sg resumed released returned current.
Proof. intros; apply os_sched_continuation_restore_effect_implies_phase; assumption. Qed.

Lemma os_sched_scoped_phase_save_program_implies_phase :
  forall environment critical sg original mask before result acquired,
  SelectedEnvironmentPhaseEffects.os_sched_continuation_phase_save_program
    environment critical sg original mask before result acquired ->
  os_sched_continuation_phase_save_program environment critical sg original mask before result acquired.
Proof. intros; apply os_sched_scoped_phase_save_effect_implies_phase; assumption. Qed.

Lemma os_sched_scoped_phase_restore_program_implies_phase :
  forall environment critical sg resumed released returned current,
  SelectedEnvironmentPhaseEffects.os_sched_continuation_phase_restore_program
    environment critical sg resumed released returned current ->
  os_sched_continuation_phase_restore_program environment critical sg resumed released returned current.
Proof. intros; apply os_sched_scoped_phase_restore_effect_implies_phase; assumption. Qed.

Lemma os_sched_continuation_phase_save_effect_same_call :
  forall environment critical sg original mask saved before returned acquired,
  os_sched_continuation_phase_save_effect environment critical sg original mask saved before returned acquired ->
  task_tcb_init_stack_same_call returned original.
Proof.
  intros environment critical sg original mask saved before returned acquired [Hold|[Hactual|Hboot]].
  - eapply SelectedEnvironmentPhaseEffects.os_sched_continuation_phase_save_effect_same_call.
    left; exact Hold.
  - eapply SelectedEnvironmentPhaseEffects.os_sched_continuation_phase_save_effect_same_call.
    right; exact Hactual.
  - destruct (FlagPendBootPrimitive.flag_pend_boot_save_effect_observations
      environment critical sg original mask saved before returned acquired Hboot)
      as [_ [Hsame Hrest]]; exact Hsame.
Qed.

Lemma os_sched_continuation_phase_restore_effect_same_call :
  forall environment critical sg original released returned current,
  os_sched_continuation_phase_restore_effect environment critical sg original released returned current ->
  task_tcb_init_stack_same_call returned original.
Proof.
  intros environment critical sg original released returned current [Hold|[Hactual|Hboot]].
  - eapply SelectedEnvironmentPhaseEffects.os_sched_continuation_phase_restore_effect_same_call.
    left; exact Hold.
  - eapply SelectedEnvironmentPhaseEffects.os_sched_continuation_phase_restore_effect_same_call.
    right; exact Hactual.
  - destruct (FlagPendBootPrimitive.flag_pend_boot_restore_effect_observations
      environment critical sg original released returned current Hboot)
      as [_ [Hsame Hrest]]; exact Hsame.
Qed.

Lemma os_sched_continuation_phase_save_effect_saved_value :
  forall environment critical sg original mask saved before returned acquired,
  os_sched_continuation_phase_save_effect environment critical sg original mask saved before returned acquired ->
  interrupt_saved_value mask saved.
Proof.
  intros environment critical sg original mask saved before returned acquired [Hold|[Hactual|Hboot]].
  - eapply SelectedEnvironmentPhaseProperties.os_sched_continuation_phase_save_effect_saved_value.
    left; exact Hold.
  - eapply SelectedEnvironmentPhaseProperties.os_sched_continuation_phase_save_effect_saved_value.
    right; exact Hactual.
  - destruct (FlagPendBootPrimitive.flag_pend_boot_save_effect_observations
      environment critical sg original mask saved before returned acquired Hboot)
      as [_ [_ [_ [_ Hsaved]]]]; exact Hsaved.
Qed.

Lemma os_sched_continuation_phase_save_effect_name_timer :
  forall environment critical sg original mask saved before returned acquired,
  os_sched_continuation_phase_save_effect environment critical sg original mask saved before returned acquired ->
  before.(NameState) = acquired.(NameState) /\
  timer_public_trace sg before.(TimerState) acquired.(TimerState).
Proof.
  intros environment critical sg original mask saved before returned acquired [Hold|[Hactual|Hboot]].
  - eapply SelectedEnvironmentPhaseProperties.os_sched_continuation_phase_save_effect_name_timer.
    left; exact Hold.
  - eapply SelectedEnvironmentPhaseProperties.os_sched_continuation_phase_save_effect_name_timer.
    right; exact Hactual.
  - destruct (FlagPendBootPrimitive.flag_pend_boot_save_effect_observations
      environment critical sg original mask saved before returned acquired Hboot)
      as [_ [_ [_ [Hinterval Hsaved]]]].
    split.
    + exact (critical_region_interval_preserves_name_state critical sg
        original.(os_sched_call_invocation) before acquired Hinterval).
    + exact (critical_region_interval_timer_public_trace critical sg
        original.(os_sched_call_invocation) before acquired Hinterval).
Qed.

Lemma os_sched_continuation_phase_restore_effect_name_timer :
  forall environment critical sg original released returned current,
  os_sched_continuation_phase_restore_effect environment critical sg original released returned current ->
  released.(NameState) = current.(NameState) /\
  timer_public_trace sg released.(TimerState) current.(TimerState).
Proof.
  intros environment critical sg original released returned current [Hold|[Hactual|Hboot]].
  - eapply SelectedEnvironmentPhaseProperties.os_sched_continuation_phase_restore_effect_name_timer.
    left; exact Hold.
  - eapply SelectedEnvironmentPhaseProperties.os_sched_continuation_phase_restore_effect_name_timer.
    right; exact Hactual.
  - destruct (FlagPendBootPrimitive.flag_pend_boot_restore_effect_observations
      environment critical sg original released returned current Hboot)
      as [_ [_ [_ [Hinterval Hcall]]]].
    split.
    + exact (critical_region_interval_preserves_name_state critical sg
        original.(os_sched_call_invocation) released current Hinterval).
    + exact (critical_region_interval_timer_public_trace critical sg
        original.(os_sched_call_invocation) released current Hinterval).
Qed.

End ContinuationPhaseEffects.
