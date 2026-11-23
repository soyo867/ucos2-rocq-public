Require Import Coq.Lists.List Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.

(** Source families whose actual updates leave the Timer projection alone.
    Membership identifies existing operations, not a desired postcondition.
    A registered client's validity/ownership certificate is still required
    separately by the shared region.  In particular this list does not
    register arbitrary payloads as valid Event/Queue publications, or make
    the listed critical stages into whole-function correctness theorems. *)
Inductive kernel_nontimer_source_client : KernelClientAction -> Prop :=
| KernelSourceTaskLifecycle : forall action,
    kernel_nontimer_source_client (task_creation_client action)
| KernelSourceTaskStackPublication : forall publication,
    kernel_nontimer_source_client (task_create_stack_publication_client publication)
| KernelSourceTaskBegin : forall origin,
    kernel_nontimer_source_client (task_create_begin_client origin)
| KernelSourceTaskReserve : forall prio invocation origin,
    kernel_nontimer_source_client (task_create_reserve_client prio invocation origin)
| KernelSourceTaskRollback : forall prio invocation,
    kernel_nontimer_source_client (task_create_rollback_client prio invocation)
| KernelSourceEventAllocate : forall actor invocation,
    kernel_nontimer_source_client (event_create_allocate_client actor invocation)
| KernelSourceEventStore : forall actor eid allocation field value,
    kernel_nontimer_source_client
      (event_create_private_store_client actor eid allocation field value)
| KernelSourceEventPublish : forall actor eid allocation node,
    kernel_nontimer_source_client (event_create_publication_client actor eid allocation node)
| KernelSourceQueueReserve : forall actor eid allocation free,
    kernel_nontimer_source_client (q_create_reserve_client actor eid allocation free)
| KernelSourceQueuePublish : forall actor eid allocation qid start size slots name,
    kernel_nontimer_source_client
      (q_create_publication_client actor eid allocation qid start size slots name)
| KernelSourceTaskSuspend : forall actor prio,
    kernel_nontimer_source_client (task_suspend_critical_client actor prio)
| KernelSourceTaskResume : forall actor prio,
    kernel_nontimer_source_client (task_resume_critical_client actor prio)
| KernelSourceSemAccept : forall invocation eid count,
    kernel_nontimer_source_client (sem_accept_critical_client invocation eid count).

Lemma kernel_nontimer_source_client_timer_state_eq : forall action sg before after,
  kernel_nontimer_source_client action ->
  kernel_client_step action sg before after ->
  after.(TimerState) = before.(TimerState).
Proof.
  intros action sg before after Hsource; destruct Hsource.
  - apply task_creation_client_timer_state_eq.
  - apply task_create_stack_publication_timer_state_eq.
  - intros [_ ->]; reflexivity.
  - intros [_ ->]; reflexivity.
  - intros [_ ->]; reflexivity.
  - intros [_ [result Hstep]].
    unfold event_create_allocate_critical in Hstep.
    destruct before.(EventState).(unUsedEventStates).
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [image [_ [_ ->]]]; reflexivity.
  - intros [_ ->]; reflexivity.
  - intros [_ [_ ->]]; reflexivity.
  - intros [_ [_ [_ [_ [result [a [Ha Hstep]]]]]]].
    destruct free; destruct Hstep as [_ ->]; reflexivity.
  - intros [_ [_ [_ [_ ->]]]]; reflexivity.
  - intros [_ [result [current_id [current [_ [_ [_ Hstep]]]]]]].
    destruct (before.(TskState).(prioTbl)
      (fst (task_suspend_selection sg prio current))).
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [t [_ [_ ->]]]; reflexivity.
  - intros [_ [result [_ Hstep]]].
    destruct (before.(TskState).(prioTbl) prio).
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [t [_ Hstep]].
      destruct (task_is_suspended t.(stat)); destruct Hstep as [_ ->]; reflexivity.
  - intros [e [_ [_ [node [fields [_ [_ [_ ->]]]]]]]].
    destruct (Z.ltb 0 fields.(semCount)); reflexivity.
Qed.

(** The generic family above retains the raw TaskPublish projection; its
    membership is not a stack-coverage certificate.  This concrete source
    cut instead registers the stack-aware action and consumes its physical
    publication owners.  The resulting trace and continuation map therefore
    describe the same publication, including the initialized frame. *)
Lemma task_create_stack_publication_source_resumption :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg publication current observer event_observer,
  UCOS2_state_inv sg current ->
  task_create_stack_publication_input sg publication current ->
  publication.(stack_publication_invocation) <> observer ->
  let after := task_create_stack_publication_state sg publication current in
  task_create_stack_publication_resources external platform port abi sg publication current |--
  coq_prop (kernel_resumption_resource_trace kernel_nontimer_source_client sg observer event_observer
    current false after) &&
  (UCOS2_inv sg after ** armv7a_task_continuations abi after.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi sg publication current observer event_observer
    Hvalid Hinput Hforeign after.
  pose proof (task_create_stack_publication_source_post external platform port abi
    sg publication current Hvalid Hinput) as Hpost.
  cbv zeta in Hpost; fold after in Hpost; sep_apply_l_atomic Hpost.
  Intros.
  apply _derivable1_andp_intros; [apply derivable1s_coq_prop_r|reflexivity].
  change (kernel_resumption_resource_trace kernel_nontimer_source_client sg observer event_observer
    current (orb (kernel_client_stops (task_create_stack_publication_client publication) observer) false) after).
  eapply KernelResumptionTraceStep with
    (action := task_create_stack_publication_client publication) (middle := after).
  - constructor.
  - change (Some publication.(stack_publication_invocation) <> Some observer); congruence.
  - intros; discriminate.
  - assumption.
  - rewrite (task_create_stack_publication_timer_state_eq sg publication current after) by assumption.
    constructor.
  - constructor.
Qed.

(** Reuse the existing certificates and raw source trace.  The additional
    Timer segment is derived from the operations above, rather than assumed
    in a new platform/certificate field.  The stopped bit and both private
    allocation observers are preserved exactly, including retirement. *)
Lemma kernel_nontimer_source_trace_resumption :
  forall clients sg observer event_observer before stopped after,
  (forall action, clients action -> KernelClientCertificate action) ->
  (forall action, clients action -> kernel_nontimer_source_client action) ->
  kernel_client_resource_trace clients sg observer event_observer before stopped after ->
  UCOS2_state_inv sg before ->
  kernel_resumption_resource_trace clients sg observer event_observer before stopped after.
Proof.
  intros clients sg observer event_observer before stopped after Hcert Hsource Htrace Hvalid.
  eapply kernel_client_trace_timer_unchanged_resumption; try eassumption.
  intros action initial final Hin _ Hstep.
  eapply kernel_nontimer_source_client_timer_state_eq; [apply Hsource; exact Hin|exact Hstep].
Qed.

Lemma critical_region_nontimer_source_interval :
  forall critical sg observer before after,
  (forall action, critical.(critical_region_clients) action ->
    kernel_nontimer_source_client action) ->
  kernel_client_trace critical.(critical_region_clients) sg observer before false after ->
  UCOS2_state_inv sg before ->
  critical_region_interval critical sg observer before after.
Proof.
  intros critical sg observer before after Hsource Htrace Hvalid.
  eapply kernel_nontimer_source_trace_resumption; try eassumption.
  exact critical.(critical_region_client_certificates).
Qed.

Lemma critical_region_nontimer_source_event_interval :
  forall critical sg observer event_observer before after,
  (forall action, critical.(critical_region_clients) action ->
    kernel_nontimer_source_client action) ->
  kernel_client_resource_trace critical.(critical_region_clients) sg observer
    (Some event_observer) before false after ->
  UCOS2_state_inv sg before ->
  critical_region_event_interval critical sg observer event_observer before after.
Proof.
  intros critical sg observer event_observer before after Hsource Htrace Hvalid.
  eapply kernel_nontimer_source_trace_resumption; try eassumption.
  exact critical.(critical_region_client_certificates).
Qed.

Lemma task_creation_client_family_resumption :
  forall sg observer event_observer before stopped after,
  kernel_client_resource_trace task_creation_client_family sg observer event_observer
    before stopped after ->
  UCOS2_state_inv sg before ->
  kernel_resumption_resource_trace task_creation_client_family sg observer event_observer
    before stopped after.
Proof.
  intros sg observer event_observer before stopped after Htrace Hvalid.
  eapply kernel_nontimer_source_trace_resumption; try eassumption.
  - exact task_creation_client_family_certificates.
  - intros client [action ->]; constructor.
Qed.
