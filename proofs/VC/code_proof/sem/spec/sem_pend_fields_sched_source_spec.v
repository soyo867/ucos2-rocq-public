Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.task_stack.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_fields_sched_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_modular_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_sched_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The source is the actual completed Scheduler body, including its last
    selected C call or interrupt return. The returned fields owner supplies
    the invariant at that same endpoint. No ready-return condition or new
    physical-instruction witness is assumed here. *)
Lemma sem_pend_fields_sched_ready_from_source : forall environment local critical sg
  entered entry returned released saved acquired,
  UCOS2_state_inv sg entry ->
  sem_pend_wait_sched_entry sg entered entry ->
  SchedulerPhaseCandidate.os_sched_task_body_source
    (task_sw_hook_call_environment environment) critical sg entry entered returned released ->
  sem_pend_fields_masked (task_sw_hook_call_environment environment) local critical sg
    returned saved acquired released |--
  coq_prop (os_sched_task_current_ready returned released) &&
    sem_pend_fields_masked (task_sw_hook_call_environment environment) local critical sg
      returned saved acquired released.
Proof.
  intros environment local critical sg entered entry returned released saved acquired
    Hvalid Hentry Hsource heap Howned.
  pose proof (sem_pend_fields_masked_observations
    (task_sw_hook_call_environment environment) local critical sg returned saved acquired
    released heap Howned) as [Hvalid_current Hrange].
  destruct Hentry as [Hcut [Henabled [Hcaller [Hblocking Hcache]]]].
  split; [|exact Howned].
  exact (SchedulerPhaseCandidate.os_sched_task_body_source_current_ready environment
    critical sg entry entered returned released Hvalid Hvalid_current Hcaller Hcache
    Henabled Hcut Hsource).
Qed.

(** Retain SemPend's original wait history and returned-call relation.
    The additional actual C source above discharges the old switch-ready
    premise for this endpoint. A Sem waiter is never classified as Fresh
    or as a Flag waiter. Source classification itself remains a callee
    producer obligation; the old broad return relation alone does not imply
    that classification. *)
Lemma sem_pend_fields_sched_selected_from_source : forall environment local critical sg
  original initial_mask initial observed eid timeout waiting
  entered entry returned released saved acquired,
  sem_pend_sched_clients (task_sw_hook_call_environment environment) critical ->
  UCOS2_state_inv sg entry ->
  sem_pend_wait_at (Some (task_sw_hook_call_environment environment)) critical sg
    original initial_mask initial observed eid timeout waiting entered entry ->
  sem_pend_wait_sched_entry sg entered entry ->
  os_sched_c_return (task_sw_hook_call_environment environment).(task_stack_call_external)
    critical sg entry entered returned released ->
  SchedulerPhaseCandidate.os_sched_task_body_source
    (task_sw_hook_call_environment environment) critical sg entry entered returned released ->
  sem_pend_fields_masked (task_sw_hook_call_environment environment) local critical sg
    returned saved acquired released |--
  coq_prop (sem_pend_wait_selected_at (Some (task_sw_hook_call_environment environment))
    critical sg original initial_mask initial observed eid timeout waiting returned released) &&
    sem_pend_fields_masked (task_sw_hook_call_environment environment) local critical sg
      returned saved acquired released.
Proof.
  intros environment local critical sg original initial_mask initial observed eid timeout waiting
    entered entry returned released saved acquired Hclients Hvalid Hwait Hentry Hreturn Hsource
    heap Howned.
  pose proof (sem_pend_fields_sched_ready_from_source environment local critical sg
    entered entry returned released saved acquired Hvalid Hentry Hsource heap Howned)
    as [Hready Hretained].
  pose proof (os_sched_c_return_execution_identity
    (task_sw_hook_call_environment environment).(task_stack_call_external) critical sg
    entry entered returned released Hreturn) as Hsame.
  destruct Hready as [node [[Hnode [Hcurrent [Hcache [Hmember Heffective]]]] Hgeneration]].
  rewrite (proj2 (proj2 Hsame)) in Hmember.
  exact (sem_pend_fields_sched_body_selected (task_sw_hook_call_environment environment)
    local critical sg original initial_mask initial observed eid timeout waiting
    entered entry returned released saved acquired Hclients Hvalid Hwait Hentry Hreturn
    (fun _ => Hmember) heap Hretained).
Qed.
