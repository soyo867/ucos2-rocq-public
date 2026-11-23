Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Relations.Relation_Operators.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_context Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_environment_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_envelope_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_completion_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** This name only exposes the endpoint of the existing entry C contract.
    The proofs below use its exported consequences, not its implementation. *)
Definition sem_pend_irq_entry_state initial handler suspended :=
  armv7a_irq_live_parked_state initial handler.(os_int_exit_interrupted_call)
    suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments).

(** A concrete consumer proves closure for the same actual entry completion.
    This is separate from the unchanged post-acquired IRQ tail frame. *)
Definition sem_pend_irq_entry_preserves (property : UCOS2_Verify_State -> Prop) : Prop :=
  forall environment sg initial node handler suspended publication local frame before saved_heap body_heap,
  OSIntExitCCallEnvelope.os_int_exit_first_level_entry_c_completion environment sg
    initial node handler suspended publication local frame before saved_heap body_heap ->
  property initial -> property (sem_pend_irq_entry_state initial handler suspended).

(** Zero is a projection used for equality; no state is written with zero. *)
Lemma sem_pend_irq_entry_tasks :
  forall environment sg initial node handler suspended publication local frame before saved_heap body_heap,
  OSIntExitCCallEnvelope.os_int_exit_first_level_entry_c_completion environment sg
    initial node handler suspended publication local frame before saved_heap body_heap ->
  forall slot,
  option_map (fun task => task_set_saved_sp task 0)
    ((sem_pend_irq_entry_state initial handler suspended).(TskState).(inUsedTaskStates) slot) =
  option_map (fun task => task_set_saved_sp task 0) (initial.(TskState).(inUsedTaskStates) slot).
Proof.
  intros until body_heap; intros Hentry slot.
  pose proof (OSIntExitCCallEnvelope.os_int_exit_first_level_entry_task_fields
    _ _ _ _ _ _ _ _ _ _ _ _ Hentry) as Htasks.
  unfold sem_pend_irq_entry_state; rewrite Htasks.
  cbn [glob_task_set_parked_stacks glob_task_set_usedtask inUsedTaskStates].
  destruct (Z.eqb slot handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot)) eqn:Hslot.
  - apply Z.eqb_eq in Hslot; subst slot.
    rewrite (OSIntExitCCallEnvelope.os_int_exit_entry_node _ _ _ _ _ _ _ _ _ _ _ _ Hentry).
    cbn [option_map]; rewrite task_set_saved_sp_last_write; reflexivity.
  - reflexivity.
Qed.

Lemma sem_pend_irq_entry_task_at :
  forall environment sg initial node handler suspended publication local frame before saved_heap body_heap,
  OSIntExitCCallEnvelope.os_int_exit_first_level_entry_c_completion environment sg
    initial node handler suspended publication local frame before saved_heap body_heap ->
  forall slot old, initial.(TskState).(inUsedTaskStates) slot = Some old ->
  exists current,
    (sem_pend_irq_entry_state initial handler suspended).(TskState).(inUsedTaskStates) slot = Some current /\
    task_set_saved_sp current 0 = task_set_saved_sp old 0.
Proof.
  intros until body_heap; intros Hentry slot old Hold.
  pose proof (sem_pend_irq_entry_tasks _ _ _ _ _ _ _ _ _ _ _ _ Hentry slot) as Hfields.
  rewrite Hold in Hfields.
  destruct ((sem_pend_irq_entry_state initial handler suspended).(TskState).(inUsedTaskStates) slot)
    as [current|] eqn:Hcurrent; [|discriminate].
  pose proof (f_equal (fun found : option TaskAbstractState =>
    match found with Some task => task | None => old end) Hfields) as Hnode_fields.
  exists current; split; [reflexivity|exact Hnode_fields].
Qed.

Lemma sem_pend_saved_sp_fields_update : forall old current,
  task_set_saved_sp current 0 = task_set_saved_sp old 0 ->
  current = task_set_saved_sp old current.(tcbStkPtr).
Proof.
  intros old current Hfields.
  refine (eq_trans (eq_sym (task_set_saved_sp_put_back current)) _).
  refine (eq_trans (eq_sym (task_set_saved_sp_last_write current 0 current.(tcbStkPtr))) _).
  refine (eq_trans (f_equal (fun task => task_set_saved_sp task current.(tcbStkPtr)) Hfields) _).
  apply task_set_saved_sp_last_write.
Qed.

Lemma sem_pend_irq_entry_frames :
  forall environment sg initial node handler suspended publication local frame before saved_heap body_heap,
  OSIntExitCCallEnvelope.os_int_exit_first_level_entry_c_completion environment sg
    initial node handler suspended publication local frame before saved_heap body_heap ->
  let parked := sem_pend_irq_entry_state initial handler suspended in
  parked.(TskState).(taskLifecycle) = initial.(TskState).(taskLifecycle) /\
  parked.(EventState) = initial.(EventState) /\
  parked.(NameState) = initial.(NameState) /\
  parked.(TimerState) = initial.(TimerState) /\ parked.(SchedState) = initial.(SchedState).
Proof.
  intros until body_heap; intros Hentry parked.
  destruct (OSIntExitCCallCompletion.os_int_exit_first_level_entry_source_frames
    _ _ _ _ _ _ _ _ _ _ _ _ Hentry) as [_ [Hevents [Hnames Htimers]]].
  split.
  - exact (proj1 (OSIntExitCCallCompletion.os_int_exit_first_level_entry_lifecycle_generation
      _ _ _ _ _ _ _ _ _ _ _ _ Hentry)).
  - split; [exact Hevents|]. split; [exact Hnames|]. split; [exact Htimers|].
    exact (ReturnedIRQCallSource.os_int_exit_entry_sched_state _ _ _ _ _ _ _ _ _ _ _ _ Hentry).
Qed.

Lemma sem_pend_irq_entry_preserves_validity :
  forall environment sg initial node handler suspended publication local frame before saved_heap body_heap,
  OSIntExitCCallEnvelope.os_int_exit_first_level_entry_c_completion environment sg
    initial node handler suspended publication local frame before saved_heap body_heap ->
  UCOS2_state_inv sg (sem_pend_irq_entry_state initial handler suspended).
Proof.
  intros until body_heap; intro Hentry.
  pose proof (proj2 (OSIntExitCCallEnvelope.os_int_exit_first_level_entry_c_resources
    _ _ _ _ _ _ _ _ _ _ _ _ Hentry)) as Howned.
  unfold OSIntExitCCallEnvelope.os_int_exit_first_level_entry_output in Howned.
  destruct Howned as (fields_heap & remaining_heap & Hjoin & Hfields & Hremaining).
  destruct Hfields as (state_heap & parked_heap & Hstate_join & Hstate & Hparked).
  exact (proj1 Hstate).
Qed.

Lemma sem_pend_irq_entry_preserves_current :
  forall environment sg initial node handler suspended publication local frame before saved_heap body_heap,
  OSIntExitCCallEnvelope.os_int_exit_first_level_entry_c_completion environment sg
    initial node handler suspended publication local frame before saved_heap body_heap ->
  forall origin, task_execution_current origin initial ->
  task_execution_current origin (sem_pend_irq_entry_state initial handler suspended).
Proof.
  intros until body_heap; intros Hentry origin Hcurrent.
  pose proof (ReturnedIRQCallSource.os_int_exit_entry_sched_state _ _ _ _ _ _ _ _ _ _ _ _ Hentry) as Hsched.
  unfold task_execution_current, sem_pend_irq_entry_state in *; rewrite Hsched; exact Hcurrent.
Qed.

Lemma sem_pend_irq_entry_preserves_active :
  forall environment sg initial node handler suspended publication local frame before saved_heap body_heap,
  OSIntExitCCallEnvelope.os_int_exit_first_level_entry_c_completion environment sg
    initial node handler suspended publication local frame before saved_heap body_heap ->
  forall observer origin, task_invocation_active initial.(TskState) observer origin ->
  task_invocation_active (sem_pend_irq_entry_state initial handler suspended).(TskState) observer origin.
Proof.
  intros until body_heap; intros Hentry observer origin Hactive.
  eapply ReturnedIRQEntryResources.os_int_exit_first_level_entry_preserves_active; eassumption.
Qed.

Lemma sem_pend_irq_entry_waiter_projection :
  forall environment sg initial node handler suspended publication local frame before saved_heap body_heap,
  OSIntExitCCallEnvelope.os_int_exit_first_level_entry_c_completion environment sg
    initial node handler suspended publication local frame before saved_heap body_heap ->
  forall slot old, initial.(TskState).(inUsedTaskStates) slot = Some old ->
  sem_pend_task_projection initial.(TskState)
    (sem_pend_irq_entry_state initial handler suspended).(TskState) slot old.
Proof.
  intros until body_heap; intros Hentry slot old Hold.
  destruct (sem_pend_irq_entry_task_at _ _ _ _ _ _ _ _ _ _ _ _ Hentry slot old Hold)
    as [current [Hcurrent Hfields]].
  exists current; split; [exact Hcurrent|].
  rewrite (sem_pend_saved_sp_fields_update old current Hfields).
  apply rt_step, SemPendWaitSaveStack.
Qed.
