Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.timer Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.kernel_start Ucos2Verify.lib.kernel_runtime_inv.
Require Import Ucos2Verify.VC.code.core.spec.kernel_idle_ready_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Reuse the existing completed Start storage endpoint.  Idle's witness
    comes from its real TCB publication; this rule does not assume that
    structural validity alone establishes it.  The OSRunning store keeps
    the previously declared port boundary of kernel_start.v. *)
Lemma kernel_start_establishes_runtime_inv : forall sg state,
  UCOS2_state_inv sg state -> task_idle_tail sg state.(TskState) ->
  task_idle_ready sg state.(TskState) ->
  (sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized state.(TimerState)) ->
  let post := kernel_running_store (kernel_start_ready_state state) in
  sched_raw_rep sg post.(TskState) post.(SchedState) **
    (UCOS2_raw_rep_missing_sched sg state ** unmap_table_rep sg) |--
  kernel_runtime_inv sg post.
Proof.
  intros sg state Hvalid Htail Hidle Htimer post.
  assert (Hruntime : kernel_running_idle_ready sg post).
  { intros _; exact Hidle. }
  unfold kernel_runtime_inv; rewrite kernel_program_inv_split_unmap.
  pose proof (kernel_start_running_resources_merge sg state Hvalid Htail Htimer) as Hmerge.
  cbn zeta in Hmerge.
  fold post in Hmerge.
  sep_apply_l_atomic Hmerge.
  entailer!.
Qed.

(** Publication changes links and the parked map, retaining the old
    Idle priority/status/delay.  Consume the actual publication input. *)
Lemma task_create_stack_publication_preserves_running_idle : forall sg publication state,
  UCOS2_state_inv sg state -> task_create_stack_publication_input sg publication state ->
  kernel_running_idle_ready sg state ->
  kernel_running_idle_ready sg (task_create_stack_publication_state sg publication state).
Proof.
  intros sg publication state Hvalid Hinput Hruntime Hrunning.
  change (state.(SchedState).(isRunning) = true) in Hrunning.
  change (task_idle_ready sg
    (task_tcb_init_published_state sg (task_create_stack_publication_args publication)
      publication.(stack_publication_invocation) publication.(stack_publication_acquired)
      state publication.(stack_publication_slot) publication.(stack_publication_image)).(TskState)).
  eapply task_tcb_init_publication_preserves_idle_ready with
    (origin := publication.(stack_publication_origin)).
  - exact Hvalid.
  - exact (proj1 (proj2 (proj2 Hinput))).
  - exact (Hruntime Hrunning).
Qed.

Lemma event_pend_preserves_running_idle : forall sg state eid event tid node kind timeout,
  state.(TskState).(inUsedTaskStates) tid = Some node ->
  valid_task_prio sg node.(curPrio) -> kernel_running_idle_ready sg state ->
  kernel_running_idle_ready sg (event_pend_state sg state eid event tid node kind timeout).
Proof.
  intros sg state eid event tid node kind timeout Hnode Hpriority Hruntime Hrunning.
  change (state.(SchedState).(isRunning) = true) in Hrunning.
  eapply event_pend_preserves_idle_ready;
    [exact Hnode|exact Hpriority|exact (Hruntime Hrunning)].
Qed.

(** The real take removes the selected key.  This observation belongs at
    the completed call entry, not inside the global interrupt invariant. *)
Lemma kernel_call_take_establishes_available : forall call state lease,
  call.(os_sched_call_origin) = RunningInvocation
    lease.(stackLeaseSlot) lease.(stackLeaseGeneration) ->
  kernel_call_stack_available call
    (replace_TskS (glob_task_set_parked_stacks state.(TskState)
      (task_stack_take state.(TskState).(parkedTaskStacks) lease)) state).
Proof.
  intros call state lease Horigin; unfold kernel_call_stack_available; rewrite Horigin.
  change (task_stack_take state.(TskState).(parkedTaskStacks) lease (task_stack_key lease) = None).
  apply task_stack_take_lookup.
Qed.

(** Starting the next API invocation only changes its registration.  The
    same established global protocol and actual available key are kept. *)
Lemma kernel_sequential_entry_preserves_running_idle : forall sg call state,
  kernel_running_idle_ready sg state ->
  kernel_running_idle_ready sg
    (replace_TskS (task_begin_invocation call.(os_sched_call_origin) state.(TskState)) state).
Proof. intros sg call state Hruntime Hrunning; exact (Hruntime Hrunning). Qed.

Lemma kernel_sequential_entry_preserves_available : forall call state invocation,
  kernel_call_stack_available call state ->
  kernel_call_stack_available (kernel_sequential_call call invocation)
    (replace_TskS (task_begin_invocation call.(os_sched_call_origin) state.(TskState)) state).
Proof.
  intros call state invocation Havailable.
  unfold kernel_call_stack_available in *.
  cbn [kernel_sequential_call os_sched_call_origin].
  destruct (os_sched_call_origin call); exact Havailable.
Qed.
