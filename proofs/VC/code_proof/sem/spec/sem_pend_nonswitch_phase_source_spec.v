Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_client_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Carry the same original wait through the actual C no-switch prefix.
    Its guard branches are identity; its enabled branch only updates the
    Scheduler's high-ready cache. This relation asserts no readiness. *)
Lemma sem_pend_wait_at_nonswitch_source : forall environment critical sg original mask initial
  observed eid timeout waiting call state before after,
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout
    waiting call state ->
  os_sched_requests_switch state = false ->
  os_sched_source_nonswitch_prefix_execution sg before after ->
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout
    waiting call (os_sched_prefix_state state).
Proof.
  intros * [owned [Henv [Hsame [Hwait Hpath]]]] Hnoswitch Hprefix.
  inversion Henv; subst owned.
  exists environment; split; [reflexivity|]. split; [exact Hsame|]. split; [exact Hwait|].
  eapply SemPendWaitSourceTrans; [exact Hpath|].
  eapply SemPendWaitSourceNonswitch; eassumption.
Qed.

(** The enabled equal-priority branch obtains readiness from the actual
    selected priority and the source's current-priority cache binding.
    Source consumers must establish that binding at this very entry cut.
    Guarded no-selection paths do not satisfy these hypotheses. *)
Lemma sem_pend_enabled_nonswitch_wait_selected : forall environment critical sg original mask initial
  observed eid timeout waiting call state,
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout
    waiting call (os_sched_prefix_state state) ->
  UCOS2_state_inv sg state -> kernel_call_task_source call state ->
  sched_current_consistency state.(TskState) state.(SchedState) ->
  os_sched_selection_enabled state = true -> os_sched_requests_switch state = false ->
  state.(SchedState).(readyList) <> [] ->
  sem_pend_wait_selected_at (Some environment) critical sg original mask initial observed eid timeout
    waiting call (os_sched_prefix_state state).
Proof.
  intros * Hwait Hvalid Hsource Hcache Hen Hnoswitch Hnonempty.
  split; [exact Hwait|].
  pose proof Hwait as [owned [Henv [Hsame [Hinitial Hpath]]]].
  destruct (os_sched_nonswitch_current_ready_at sg call state Hvalid Hsource Hcache Hen Hnoswitch Hnonempty)
    as [node [Hready Hgeneration]].
  pose proof (proj2 (proj2 Hsame)) as Hstack.
  rewrite Hstack in Hready.
  destruct (sem_pend_observed_wait_history_waiter _ _ _ _ _ _ _ _ _ _ Hinitial)
    as [first [Hfirst Hfirst_wait]].
  destruct (sem_pend_wait_source_history_preserves_waiter _ _ _ _ _ _ _ _ Hpath
    first Hfirst Hfirst_wait) as [last [Hlast Hlast_wait]].
  destruct Hready as [Hnode [Hcurrent [Hpriority [Hmember Heffective]]]].
  assert (last = node) by congruence; subst last.
  destruct (sem_pend_wait_ready_resume_registration _ _ _ Hlast_wait Heffective)
    as [Hregistration Hrest].
  exists node; unfold sem_pend_resume_entry.
  split; [apply os_sched_ready_checkpoint_preserves_validity; exact Hvalid|].
  split; [exact Hcurrent|]. split; [exact Hnode|]. split; assumption.
Qed.

(** One actual heap chain, including both nesting/lock early exits and
    the equal-priority selection branch. The common result retains this
    wait and the current stack world. Only the enabled branch additionally
    produces the canonical Scheduler Ensure. No hidden lock/readiness
    precondition is added to OSSemPend or to its caller protocol. *)
Lemma sem_pend_nonswitch_scheduler_phase_source : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg original mask initial observed eid timeout waiting call state registers before
  final_registers acquired saved_heap (frame : Assertion),
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout
    waiting call state ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  os_sched_requests_switch state = false ->
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  (task_tcb_init_stack_covered_save_input environment critical sg call mask state **
    unmap_table_rep sg ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired saved_heap /\
  acquired = state /\ exists prefix_heap,
    os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
    forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
      sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout
        waiting call (os_sched_prefix_state state) /\
      (task_tcb_init_stack_covered_save_input environment critical sg call mask
        (os_sched_prefix_state state) ** unmap_table_rep sg ** frame) after /\
      (kernel_call_task_source call state ->
        sched_current_consistency state.(TskState) state.(SchedState) ->
        os_sched_selection_enabled state = true ->
        (sem_pend_phase_sched_output (SemPendWaitPhase original mask initial observed eid timeout waiting)
          environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
          critical sg call mask state ** frame) after).
Proof.
  intros environment critical arch save restore sg original mask initial observed eid timeout waiting call
    state registers before final_registers acquired saved_heap frame Hwait Hreturn Hcpsr Hmask
    Hnoswitch Hnonempty Hpre Hsave.
  assert (Hvalid : UCOS2_state_inv sg state).
  { assert (Hfacts : task_tcb_init_stack_covered_save_input environment critical sg call mask state **
      unmap_table_rep sg ** frame |-- coq_prop (UCOS2_state_inv sg state) && TT).
    { unfold task_tcb_init_stack_covered_save_input; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hfacts before Hpre)). }
  destruct (os_sched_source_uninterrupted_nonswitch_call_resources environment critical arch save restore
    sg call mask state registers before final_registers acquired saved_heap frame Hreturn Hcpsr Hmask
    Hnoswitch Hnonempty Hpre Hsave) as [Hsave_run [Hstate [prefix_heap [Hprefix Hrestore]]]].
  split; [exact Hsave_run|]. split; [exact Hstate|]. exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor after Hr0 Hmasked Hrestore_prefix Hrestore_suffix.
  destruct (Hrestore cursor written middle final_cursor after Hr0 Hmasked Hrestore_prefix Hrestore_suffix)
    as [Hrun Hafter].
  assert (Hwait_after : sem_pend_wait_at (Some environment) critical sg original mask initial observed
    eid timeout waiting call (os_sched_prefix_state state)).
  { eapply sem_pend_wait_at_nonswitch_source; eassumption. }
  split; [exact Hrun|]. split; [exact Hwait_after|]. split; [exact Hafter|].
  intros Hsource Hcache Hen.
  pose proof (sem_pend_enabled_nonswitch_wait_selected environment critical sg original mask initial
    observed eid timeout waiting call state Hwait_after Hvalid Hsource Hcache Hen Hnoswitch
    (Hnonempty Hen)) as Hselected.
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { cbn [sem_pend_phase_sched_output]; Exists call (os_sched_prefix_state state).
    rewrite sem_pend_stack_save_input_owned.
    unfold task_tcb_init_stack_covered_save_input, task_tcb_init_stack_save_input,
      task_tcb_init_stack_covered_capsules, task_tcb_init_stack_capsules, kernel_stack_call_same_call;
      entailer!. }
  exact (Hclose after Hafter).
Qed.
