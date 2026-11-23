Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_client_sched_call_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_clear_status_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_callee_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_proof_helpers.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.kernel_runtime_inv.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.kernel_program_storage.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Export SchedulerPhaseCandidate.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Private precondition of the actual switch call after the Scheduler C
    prefix stores. The Sem waiter retains its own protocol and local family. *)
Definition sem_client_sched_switch_input environment local critical sg original mask initial observed eid timeout
  waiting call saved entry : Assertion :=
  coq_prop (sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout
    waiting call entry) &&
  os_sched_fields_switch_pre environment critical local kernel_program_fields_inv sg call saved entry entry.

Lemma sem_client_sched_entry_cut : forall environment critical sg original mask initial observed eid timeout
  waiting call current,
  kernel_tcb_stack_field_layout sg ->
  sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout
    waiting call current -> os_sched_call_cut sg call current.
Proof.
  intros environment critical sg original mask initial observed eid timeout waiting call current Hlayout
    [[Hvalid [Hsource [Hrunning [Hidle [Havailable Hcache]]]]] Hrest].
  apply os_sched_call_cut_from_source; try assumption.
  - eapply sched_idle_ready_nonempty.
    + exact (proj1 (proj1 (proj2 (proj2 Hvalid)))).
    + apply Hidle; exact Hrunning.
  - eapply kernel_call_task_source_stack_field_address; eassumption.
Qed.

Lemma sem_client_sched_selected_cells_masked : forall environment critical local sg call saved entry,
  UCOS2_state_inv sg entry -> os_sched_selection_enabled entry = true ->
  entry.(SchedState).(readyList) <> nil ->
  task_stack_live_coverage entry.(TskState) (task_stack_call_active_key call) ->
  critical_region_masked environment.(task_stack_call_platform) critical sg
    call.(os_sched_call_invocation) call.(os_sched_call_origin) saved entry **
  task_tcb_init_stack_context environment call ** os_sched_fields_capsules environment local entry **
  os_sched_fields_work_cells sg entry (os_sched_selected entry) (os_sched_selected_tcb sg entry)
    (if os_sched_requests_switch entry
     then (os_sched_counter entry + 1) mod 4294967296 else os_sched_counter entry) |--
  sem_pend_fields_masked environment local critical sg call saved entry (os_sched_prefix_state entry).
Proof.
  intros environment critical local sg call saved entry Hvalid Henabled Hnonempty Hcoverage.
  assert (Hstable : os_sched_active_local_stable (fun _ _ => emp)).
  { unfold os_sched_active_local_stable; intros; split; reflexivity. }
  pose proof (sched_task_return_proof_helpers.os_sched_selected_work_cells_masked
    environment critical local (fun _ _ => emp) sg call saved entry entry
    Hvalid Henabled Hnonempty Hcoverage Hstable) as Hmasked.
  unfold sem_pend_fields_masked.
  match type of Hmasked with ?P |-- ?Q =>
    match goal with |- ?L |-- ?R =>
      assert (Hpre : L |-- P) by entailer!;
      assert (Hpost : Q |-- R) by entailer!;
      intros heap Howned; exact (Hpost heap (Hmasked heap (Hpre heap Howned)))
    end
  end.
Qed.

(** The equal-priority branch consumes the actual selector observation. Its
    prefix leaves the waiter's fields unchanged, including the Timeout eid. *)
Lemma sem_client_sched_nonswitch_observation : forall environment critical sg original mask initial observed eid timeout
  waiting call entry,
  sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting call entry ->
  os_sched_requests_switch entry = false ->
  os_sched_task_body_observation environment critical sg call entry call (os_sched_prefix_state entry) /\
  sem_pend_client_phase_context sg call (os_sched_prefix_state entry) /\
  sem_pend_clear_status_phase_selected_at environment critical sg original mask initial observed eid timeout
    waiting call (os_sched_prefix_state entry) /\
  sem_pend_client_sched_caller_fields sg original (os_sched_prefix_state entry).
Proof.
  intros environment critical sg original mask initial observed eid timeout waiting call entry Hentry Hnoswitch.
  pose proof Hentry as [Hcontext [Hwait [Henabled Hfields]]].
  destruct Hcontext as [Hvalid [Hsource [Hrunning [Hidle [Havailable Hcache]]]]].
  assert (Hnonempty : entry.(SchedState).(readyList) <> []).
  { eapply sched_idle_ready_nonempty;
      [exact (proj1 (proj1 (proj2 (proj2 Hvalid))))|exact (Hidle Hrunning)]. }
  pose proof (SchedulerPhaseCandidate.os_sched_task_nonswitch_body_observation
    environment critical sg call entry Hvalid Hsource Hcache Henabled Hnoswitch Hnonempty) as Hbody.
  pose proof (os_sched_ready_checkpoint_preserves_validity sg entry Hvalid) as Hvalid_after.
  assert (Hidle_after : task_idle_ready sg (os_sched_prefix_state entry).(TskState))
    by exact (Hidle Hrunning).
  assert (Htimeout : forall node,
    (os_sched_prefix_state entry).(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
    node.(statPend) = PendTimeout -> node.(eventPtr) = Some eid).
  { intros node Hnode Hstatus.
    destruct Hwait as [_ [_ [_ [previous [Hprevious Hcontinuation]]]]].
    change (entry.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node) in Hnode.
    assert (node = previous) by congruence; subst node.
    unfold sem_pend_wait_continuation in Hcontinuation; tauto. }
  destruct (sem_pend_sched_body_selected_endpoint environment critical sg original mask initial observed eid timeout
    waiting call entry call (os_sched_prefix_state entry) Hentry Hbody Hvalid_after Hidle_after Htimeout)
    as [Hcontext_after [Hselected Henabled_after]].
  split; [exact Hbody|]. split; [exact Hcontext_after|]. split; [exact Hselected|exact Hfields].
Qed.
