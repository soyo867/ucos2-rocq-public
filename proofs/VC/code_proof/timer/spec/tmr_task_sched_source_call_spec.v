From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_sw_hook_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_callee_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_idle_factory_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_registered_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_registered_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_signal_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_return_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_sched_entry_call_spec.
Import UCOS2_C_Rules TaskStateDef SchedulerPhaseCandidate SchedulerCalleePhaseComponent.
Local Open Scope sac_scope.

(** The actual Scheduler caller consumes this same returned tuple. Its
    body observation includes the original source, readiness, normal return,
    control relation and Task-source observation. The Sem waiter's separate
    proof certificate is not an obligation of this Task call interface. *)
Definition tmr_task_sched_body_entry_post environment critical active sg
  original saved acquired entry : Assertion :=
  EX returned current next_local,
    coq_prop (os_sched_task_body_observation environment critical sg original entry returned current /\
      task_idle_ready sg current.(TskState) /\ flag_pend_non_idle_at sg returned current) &&
    (kernel_continuation_call_masked environment.(task_stack_call_continuations)
      kernel_program_fields_inv next_local critical sg (task_stack_call_active_key returned)
      returned saved acquired current ** active returned current).

Definition tmr_task_sched_switch_source_post environment critical local active sg
  original saved acquired entry initial_heap : Assertion :=
  fun returned_heap =>
    os_sched_task_switch_pre environment critical local active sg
      original saved acquired entry initial_heap /\
    tmr_task_sched_body_entry_post environment critical active sg
      original saved acquired entry returned_heap.

Lemma tmr_task_actual_body_idle_post_entry :
  forall environment critical active sg original saved acquired entry,
  tmr_task_actual_body_idle_post environment critical active sg original saved acquired entry |--
  tmr_task_sched_body_entry_post environment critical active sg original saved acquired entry.
Proof.
  intros environment critical active sg original saved acquired entry heap
    [returned [current [next_local [[body [Hreceipt [Hbody Hentry]]] Howner]]]].
  exists returned, current, next_local; exact (conj (conj Hbody Hentry) Howner).
Qed.

Lemma tmr_task_sched_body_entry_post_switch :
  forall environment critical local active sg original saved acquired entry initial_heap,
  os_sched_task_switch_pre environment critical local active sg
    original saved acquired entry initial_heap ->
  tmr_task_sched_body_entry_post environment critical active sg original saved acquired entry |--
  tmr_task_sched_switch_source_post environment critical local active sg
    original saved acquired entry initial_heap.
Proof.
  intros environment critical local active sg original saved acquired entry initial_heap Hpre heap Hpost.
  exact (conj Hpre Hpost).
Qed.

Lemma tmr_task_sched_switch_source_post_entry :
  forall environment critical local active sg original saved acquired entry initial_heap,
  let configured := task_sw_hook_call_environment environment in
  tmr_task_registered_source_coverage environment.(task_stack_call_external) critical ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) entry ->
  tmr_task_sched_switch_source_post configured critical local active sg
    original saved acquired entry initial_heap |--
  tmr_task_sched_switch_entry_output configured critical local active sg
    original saved acquired entry initial_heap.
Proof.
  intros environment critical local active sg original saved acquired entry initial_heap configured
    Hcoverage Hlife heap [Hpre [returned [current [next_local [[Hbody Hentry] Howner]]]]].
  pose proof (proj1 (tmr_task_switch_pre_event_pool configured critical local active sg original
    saved acquired entry initial_heap Hpre)) as Hpool.
  assert (Hconfigured : tmr_task_registered_source_coverage configured.(task_stack_call_external) critical).
  { apply tmr_task_registered_source_coverage_task_sw_hook; exact Hcoverage. }
  assert (Hsignal : tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) current).
  { eapply tmr_task_registered_body_source_preserves_signal_lifetime;
      [exact Hconfigured|apply task_sw_hook_call_environment_source_binding|
       exact Hpool|exact Hlife|exact (proj1 Hbody)]. }
  split; [exact Hpre|]. exists returned, current, next_local.
  exact (conj (conj (conj Hbody Hsignal) Hentry) Howner).
Qed.
