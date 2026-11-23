Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_client_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Owned Task-call specialization of the existing SemPend phase interface.
    The resource family is the ACTUAL local returned by the previous callee.
    It is not wrapped with task_create_continuation_local and does not own
    Flag padding. The optional None public interface remains independent. *)
Definition sem_pend_fields_closed environment local sg call mask state : Assertion :=
  kernel_continuation_call_closed environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg (task_stack_call_active_key call) call mask state.

Definition sem_pend_fields_masked environment local critical sg call saved acquired state : Assertion :=
  kernel_continuation_call_masked environment.(task_stack_call_continuations)
    kernel_program_fields_inv local critical sg (task_stack_call_active_key call)
    call saved acquired state.

Definition sem_pend_fields_phase_save_input phase environment local critical sg call mask before : Assertion :=
  coq_prop (sem_pend_save_phase_pre phase (Some environment) critical sg call mask before) &&
  sem_pend_fields_closed environment local sg call mask before.

Definition sem_pend_fields_phase_save_output phase environment local critical sg call mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (kernel_call_save_source environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical sg call returned mask saved before acquired /\
      kernel_call_normal_return call before returned acquired /\
      sem_pend_save_rely sg before acquired /\
      sem_pend_stack_save_observation critical sg call returned (Some environment) mask saved before acquired /\
      sem_pend_save_phase_observation phase (Some environment) critical sg call returned mask saved before acquired) &&
    sem_pend_fields_masked environment local critical sg returned saved acquired acquired.

Definition sem_pend_fields_phase_restore_input phase environment local critical
  sg call mask saved acquired checkpoint : Assertion :=
  coq_prop (interrupt_saved_value mask saved /\
    sem_pend_restore_phase_pre phase (Some environment) critical sg call mask checkpoint) &&
  sem_pend_fields_masked environment local critical sg call saved acquired checkpoint.

Definition sem_pend_fields_phase_restore_output phase environment local critical
  sg call mask checkpoint : Assertion :=
  EX returned current,
    coq_prop (sem_pend_modular_call_history environment critical sg call checkpoint returned current /\
      sem_pend_stack_restore_observation sg call returned (Some environment) checkpoint current /\
      sem_pend_restore_phase_pre phase (Some environment) critical sg returned mask current) &&
    sem_pend_fields_closed environment local sg returned mask current.

(** Interrupt byte ranges are still owned by the original Interrupt module.
    Removing Flag padding changes neither that owner nor the pure invariant. *)
Lemma sem_pend_fields_inv_observations : forall sg state,
  kernel_program_fields_inv sg state |--
  coq_prop (UCOS2_state_inv sg state /\ interrupt_in_range state.(IntrState)).
Proof.
  intros; rewrite kernel_program_fields_inv_split_unmap,
    (UCOS2_fields_inv_split_module sg state InterruptModule ltac:(discriminate)).
  cbn [UCOS2_module_rep].
  unfold interrupt_inv; entailer!.
Qed.

Lemma sem_pend_fields_masked_observations : forall environment local critical sg call saved acquired state,
  sem_pend_fields_masked environment local critical sg call saved acquired state |--
  coq_prop (UCOS2_state_inv sg state /\ interrupt_in_range state.(IntrState)).
Proof.
  intros; unfold sem_pend_fields_masked, kernel_continuation_call_masked,
    kernel_continuation_inv.
  rewrite kernel_program_fields_inv_split_unmap,
    (UCOS2_fields_inv_split_module sg state InterruptModule ltac:(discriminate)).
  cbn [UCOS2_module_rep].
  unfold interrupt_inv; entailer!.
Qed.

(** Same-state compatibility only. The reverse direction requires exactly
    the current padding; neither direction transports a map across a call. *)
Lemma sem_pend_fields_native_input_equiv : forall environment critical saved_local sg call mask state,
  sem_pend_continuation_save_input environment.(task_stack_call_external)
    environment.(task_stack_call_platform) (Some environment) critical saved_local
    sg call mask state ** unmap_table_rep sg --||--
  (sem_pend_fields_closed environment (task_create_continuation_local saved_local)
    sg call mask state ** flag_configured_padding_rep sg state.(FlagState)).
Proof.
  intros; rewrite sem_pend_continuation_save_input_owned,
    task_tcb_init_continuation_save_input_closed_world.
  unfold sem_pend_fields_closed, kernel_continuation_call_closed, kernel_continuation_inv.
  rewrite kernel_program_inv_fields_padding; split; entailer!.
Qed.

Lemma sem_pend_fields_modular_save_acquire_output : forall environment local critical sg call
  pevent eid observed mask saved before,
  (forall action, critical.(critical_region_clients) action -> sem_pend_projected_source_client action) ->
  UCOS2_state_inv sg before ->
  sem_pend_save_phase_pre (SemPendAcquirePhase pevent eid observed)
    (Some environment) critical sg call mask before ->
  kernel_call_modular_save_post environment.(task_stack_call_continuations)
    kernel_program_fields_inv local critical sem_pend_save_rely sg call mask saved before |--
  sem_pend_fields_phase_save_output (SemPendAcquirePhase pevent eid observed)
    environment local critical sg call mask saved before.
Proof.
  intros * Hclients Hvalid Hpre.
  unfold kernel_call_modular_save_post; Intros returned acquired.
  assert (Hsave : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call returned mask saved before acquired) by tauto.
  assert (Hnormal : kernel_call_normal_return call before returned acquired) by tauto.
  assert (Hrely : sem_pend_save_rely sg before acquired) by tauto.
  prop_apply_p (sem_pend_fields_masked_observations environment local critical sg
    returned saved acquired acquired); Intros.
  assert (Hrange : interrupt_in_range acquired.(IntrState)) by tauto.
  pose proof (sem_pend_modular_acquire_phase_observation environment critical sg call returned
    pevent eid observed mask saved before acquired Hclients Hvalid Hrange Hpre Hsave Hnormal Hrely)
    as Hphase.
  pose proof Hsave as [_ [Hi [Ho [Hs Hsaved]]]].
  assert (Hstack : sem_pend_stack_save_observation critical sg call returned
    (Some environment) mask saved before acquired).
  { unfold sem_pend_stack_save_observation; split; [exact (proj1 Hnormal)|].
    split; [exact Hsaved|discriminate]. }
  unfold sem_pend_fields_phase_save_output; Exists returned acquired.
  unfold sem_pend_fields_masked; entailer!.
Qed.

Lemma sem_pend_fields_modular_save_wait_output : forall environment local critical sg original
  initial_mask initial observed eid timeout waiting call mask saved before,
  (forall action, critical.(critical_region_clients) action -> sem_pend_projected_source_client action) ->
  sem_pend_save_phase_pre
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    (Some environment) critical sg call mask before ->
  kernel_call_modular_save_post environment.(task_stack_call_continuations)
    kernel_program_fields_inv local critical sem_pend_save_rely sg call mask saved before |--
  sem_pend_fields_phase_save_output
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment local critical sg call mask saved before.
Proof.
  intros * Hclients [Hmask Hselected].
  unfold kernel_call_modular_save_post; Intros returned acquired.
  assert (Hsave : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call returned mask saved before acquired) by tauto.
  assert (Hnormal : kernel_call_normal_return call before returned acquired) by tauto.
  assert (Hhistory : sem_pend_modular_call_history environment critical sg call before returned acquired)
    by (split; [exact (proj1 Hsave)|exact Hnormal]).
  assert (Hrely : sem_pend_save_rely sg before acquired) by tauto.
  pose proof (sem_pend_wait_selected_modular_return environment critical sg original initial_mask
    initial observed eid timeout waiting call before returned acquired Hclients Hselected Hhistory Hrely)
    as Hselected'.
  pose proof Hsave as [_ [Hi [Ho [Hs Hsaved]]]].
  assert (Hstack : sem_pend_stack_save_observation critical sg call returned
    (Some environment) mask saved before acquired).
  { unfold sem_pend_stack_save_observation; split; [exact (proj1 Hnormal)|].
    split; [exact Hsaved|discriminate]. }
  unfold sem_pend_fields_phase_save_output; Exists returned acquired.
  cbn [sem_pend_save_phase_observation]; unfold sem_pend_fields_masked; entailer!.
Qed.

Lemma sem_pend_fields_modular_restore_observation : forall environment critical sg call checkpoint returned current,
  sem_pend_modular_call_history environment critical sg call checkpoint returned current ->
  sem_pend_stack_restore_observation sg call returned (Some environment) checkpoint current.
Proof.
  intros environment critical sg call checkpoint returned current [Htrace [Hsame Havailable]].
  split; [exact Hsame|]. intros Hvalid Hsource.
  apply (proj2 (task_tcb_init_stack_same_call_source_iff returned call current Hsame)).
  exact (task_tcb_init_stack_registered_source_preserved environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call returned checkpoint current
    Hvalid Hsame Htrace Hsource).
Qed.

(** The ordinary return phase needs no ready/Idle/wait assertion. The exact
    generic resource return is sufficient for immediate and cleanup exits. *)
Lemma sem_pend_fields_modular_restore_return_output : forall environment local critical rely
  sg call mask checkpoint,
  kernel_call_modular_restore_post environment.(task_stack_call_continuations)
    kernel_program_fields_inv local critical rely sg call mask checkpoint |--
  sem_pend_fields_phase_restore_output SemPendReturnPhase environment local critical sg call mask checkpoint.
Proof.
  intros; unfold kernel_call_modular_restore_post; Intros returned current.
  assert (Hhistory : sem_pend_modular_call_history environment critical sg call checkpoint returned current)
    by (unfold sem_pend_modular_call_history; tauto).
  pose proof (sem_pend_fields_modular_restore_observation environment critical sg
    call checkpoint returned current Hhistory) as Hobservation.
  unfold sem_pend_fields_phase_restore_output; Exists returned current.
  cbn [sem_pend_restore_phase_pre]; unfold sem_pend_fields_closed; entailer!.
Qed.

(** The actual registered C clients and blocking rely provide the Wait
    phase observations. The generic platform post alone does not do so. *)
Lemma sem_pend_fields_modular_restore_wait_output : forall environment local critical sg original
  initial_mask initial observed eid timeout waiting call mask checkpoint,
  kernel_tcb_stack_field_layout sg -> UCOS2_state_inv sg checkpoint ->
  (forall action, critical.(critical_region_clients) action -> sem_pend_projected_source_client action) ->
  sem_pend_restore_phase_pre
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    (Some environment) critical sg call mask checkpoint ->
  kernel_call_modular_restore_post environment.(task_stack_call_continuations)
    kernel_program_fields_inv local critical sem_pend_blocking_rely sg call mask checkpoint |--
  sem_pend_fields_phase_restore_output
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment local critical sg call mask checkpoint.
Proof.
  intros * Hlayout Hvalid Hclients [Hmask [Hwait Hentry]].
  unfold kernel_call_modular_restore_post; Intros returned current.
  assert (Hhistory : sem_pend_modular_call_history environment critical sg call checkpoint returned current)
    by (unfold sem_pend_modular_call_history; tauto).
  assert (Hrely : sem_pend_blocking_rely sg checkpoint current) by tauto.
  pose proof (sem_pend_wait_at_modular_return environment critical sg original initial_mask initial observed
    eid timeout waiting call checkpoint returned current Hclients Hwait Hhistory) as Hwait'.
  pose proof (sem_pend_wait_sched_entry_modular_return environment critical sg call checkpoint returned
    current Hlayout Hvalid (proj1 (proj2 (proj2 Hentry))) Hentry Hhistory Hrely) as Hentry'.
  pose proof (sem_pend_fields_modular_restore_observation environment critical sg
    call checkpoint returned current Hhistory) as Hobservation.
  unfold sem_pend_fields_phase_restore_output; Exists returned current.
  cbn [sem_pend_restore_phase_pre]; unfold sem_pend_fields_closed; entailer!.
Qed.
