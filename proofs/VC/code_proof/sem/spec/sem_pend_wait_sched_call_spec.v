Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_task_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_checkpoint_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Facts required only after a zero-count acquisition by an owned Task
    call. Idle readiness is a C/RG module invariant; availability is an
    observation at the completed call boundary; the two zero counters
    come from the real early guards and balanced returning interference.
    None of these is a new ARM implementation promise. *)
Definition sem_pend_blocking_call_stage sg call state : Prop :=
  task_idle_ready sg state.(TskState) /\
  kernel_call_stack_available call state /\
  state.(IntrState).(intNesting) = 0 /\ state.(IntrState).(lockNesting) = 0.

Definition sem_pend_optional_blocking_call_stage
  (environment : option TaskStackCallEnvironment) sg call state : Prop :=
  match environment with
  | Some _ => sem_pend_blocking_call_stage sg call state
  | None => True
  end.

(** The blocking caller needs selection to be enabled. The general
    Scheduler contract also admits disabled no-switch calls; that branch
    cannot justify resuming this caller after its own wait. *)
Definition sem_pend_wait_sched_entry sg call state : Prop :=
  os_sched_call_cut sg call state /\ os_sched_selection_enabled state = true /\
  kernel_call_task_source call state /\ sem_pend_blocking_call_stage sg call state /\
  sched_current_consistency state.(TskState) state.(SchedState).

(** The actual C wait removes this non-Idle caller from the ready set.
    Its existing entry predicate already excludes Idle. Thus the proven
    Idle fact is retained by the Task update and yields a nonempty ready
    set through the existing cross-module invariant. No readiness is
    demanded of the now blocked caller. The same C writes leave its
    parked-map key untouched; a completed entry's availability is retained.

    Idle-ready and key absence must have been established by their real
    entry/registered-module producers. They are not new public Require
    clauses, external platform promises, or conclusions of raw ownership.
    This is the kernel C effect used by the canonical EventTaskWait call. *)
Lemma sem_pend_wait_sched_call_cut : forall sg call entry eid event tid node timeout,
  sem_pend_wait_entry sg entry eid event tid node ->
  kernel_call_task_source call entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  task_idle_ready sg entry.(TskState) -> kernel_call_stack_available call entry ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  let waiting := event_pend_state sg entry eid event tid node PendSem timeout in
  kernel_sched_ready_inv sg waiting /\ kernel_call_task_source call waiting /\
  sched_current_consistency waiting.(TskState) waiting.(SchedState) /\
  kernel_call_stack_available call waiting /\ os_sched_call_cut sg call waiting.
Proof.
  intros sg call entry eid event tid node timeout Hentry Hsource Hcache Hidle Havailable Hlayout waiting.
  pose proof Hentry as [_ [_ [_ [Hnode [_ [_ [Hnonidle _]]]]]]].
  destruct (sem_pend_wait_preserves_call_source sg call entry eid event tid node timeout
    Hentry Hsource Hcache) as [Hvalid [Hcurrent Hcurrent_cache]].
  fold waiting in Hvalid, Hcurrent, Hcurrent_cache.
  assert (Hidle_after : task_idle_ready sg waiting.(TskState)).
  { change (task_idle_ready sg
      (glob_task_set_usedtask entry.(TskState) tid
        (task_set_event_ptr (task_prepare_event_wait node PendSem timeout) (Some eid)))).
    eapply task_update_non_idle_preserves_idle_ready; eassumption. }
  assert (Hready : waiting.(SchedState).(readyList) <> []).
  { eapply sched_idle_ready_nonempty;
      [exact (proj1 (proj1 (proj2 (proj2 Hvalid))))|exact Hidle_after]. }
  assert (Havailable_after : kernel_call_stack_available call waiting).
  { exact Havailable. }
  split; [split; assumption|]. split; [exact Hcurrent|].
  split; [exact Hcurrent_cache|]. split; [exact Havailable_after|].
  eapply os_sched_call_cut_from_source; eassumption.
Qed.

Lemma sem_pend_blocking_wait_sched_call_cut : forall sg original call entry eid event tid node timeout,
  sem_pend_wait_entry sg entry eid event tid node ->
  kernel_call_task_source original entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  kernel_stack_call_same_call call original ->
  sem_pend_blocking_call_stage sg original entry ->
  kernel_tcb_stack_field_layout sg ->
  sem_pend_wait_sched_entry sg call (event_pend_state sg entry eid event tid node PendSem timeout).
Proof.
  intros sg original call entry eid event tid node timeout Hentry Hsource Hcache Hsame
    [Hidle [Havailable [Hints Hlocks]]] Hconfiguration.
  pose proof (kernel_call_task_source_stack_field_address sg original entry
    Hconfiguration (proj1 Hentry) Hsource) as Hlayout.
  destruct (sem_pend_wait_sched_call_cut sg original entry eid event tid node timeout
    Hentry Hsource Hcache Hidle Havailable Hlayout)
    as [Hready [Hcurrent_after [Hcurrent_cache [Hfree Hcut]]]].
  assert (Hidle_after : task_idle_ready sg
    (event_pend_state sg entry eid event tid node PendSem timeout).(TskState)).
  { change (task_idle_ready sg
      (glob_task_set_usedtask entry.(TskState) tid
        (task_set_event_ptr (task_prepare_event_wait node PendSem timeout) (Some eid)))).
    pose proof Hentry as [_ [_ [_ [Hnode [_ [_ [Hnonidle _]]]]]]].
    eapply task_update_non_idle_preserves_idle_ready; eassumption. }
  destruct Hsame as [Hi [Ho Hstack]].
  split.
  - unfold os_sched_call_cut, os_sched_current_storage_binding in *.
    rewrite Ho, Hstack; exact Hcut.
  - split; [apply os_sched_selection_enabled_iff; split; assumption|].
    split.
    { unfold kernel_call_task_source in *; rewrite Hi, Ho, Hstack; exact Hcurrent_after. }
    split; [|exact Hcurrent_cache].
    unfold sem_pend_blocking_call_stage; split; [exact Hidle_after|].
    split; [unfold kernel_call_stack_available in *; rewrite Ho; exact Hfree|].
    split; assumption.
Qed.
