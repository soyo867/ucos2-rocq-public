From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_modular_call_spec.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.

(** The generic declaration used by OSSemPend is an instance consequence
    of the checked OS_Sched C contract. Only the actual Wait/Some case
    satisfies its input. The selected-program global-address proposition
    is identical on both declarations and is framed unchanged. *)
Lemma sem_pend_sched_call_input_instance : forall phase external platform environment
  critical saved_local sg call mask before,
  sem_pend_continuation_phase_sched_input phase external platform environment
    critical saved_local sg call mask before |--
  EX original initial_mask initial observed eid timeout waiting owned,
    coq_prop (phase = SemPendWaitPhase original initial_mask initial observed eid timeout waiting /\
      environment = Some owned /\ owned.(task_stack_call_external) = external /\
      owned.(task_stack_call_platform) = platform) &&
    sem_pend_continuation_phase_sched_input
      (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
      owned.(task_stack_call_external) owned.(task_stack_call_platform) (Some owned)
      critical saved_local sg call mask before.
Proof.
  intros [pevent eid observed | original initial_mask initial observed eid timeout waiting |]
    external platform environment critical saved_local sg call mask before.
  - cbn [sem_pend_continuation_phase_sched_input]; entailer!.
  - sep_apply_l_atomic (sem_pend_sched_input_environment external platform environment
      critical saved_local sg original initial_mask initial observed eid timeout waiting call mask before).
    Intros owned.
    Exists original initial_mask initial observed eid timeout waiting owned; entailer!.
  - cbn [sem_pend_continuation_phase_sched_input]; entailer!.
Qed.

Lemma sem_pend_sched_call_output_instance : forall phase external platform environment
  critical saved_local sg call mask before original initial_mask initial observed eid timeout waiting owned,
  phase = SemPendWaitPhase original initial_mask initial observed eid timeout waiting ->
  environment = Some owned -> owned.(task_stack_call_external) = external ->
  owned.(task_stack_call_platform) = platform ->
  sem_pend_continuation_phase_sched_output
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    owned.(task_stack_call_external) owned.(task_stack_call_platform) (Some owned)
    critical saved_local sg call mask before |--
  sem_pend_continuation_phase_sched_output phase external platform environment
    critical saved_local sg call mask before.
Proof.
  intros; subst phase environment external platform; reflexivity.
Qed.
