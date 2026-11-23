Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.lib.atomic_ops_lib Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.event Ucos2Verify.lib.event_pool Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_clients_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_publication_environment_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Import TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.

(** Kernel operations, not ghost postconditions. Normal call-point and
    no-held-Mutex requirements below are the previously approved external
    application protocol. They apply exactly where acquisition or a new
    blocking registration occurs; neither is required of every ready or
    suspended TCB. Result/error alternatives remain in the raw relations. *)
Inductive MutexProgramOperation : Type :=
| MutexProgramAcquire (eid tid priority : Z)
| MutexProgramRelease (eid : Z)
| MutexProgramHandover (eid tid : Z)
| MutexProgramDelete (eid option : Z)
| MutexProgramWait (eid tid : Z) (event : OSEventAbstractState)
    (old : TaskAbstractState) (kind : PendType) (timeout : Z)
| MutexProgramCleanup (tid : Z) (old : TaskAbstractState) (multi clear_message : bool).

Definition mutex_program_operation (operation : MutexProgramOperation)
  (sg : StableGlobVars) (before after : UCOS2_Verify_State) : Prop :=
  match operation with
  | MutexProgramAcquire eid tid priority =>
      mutex_task_call_point before.(TskState) tid /\ atomic_mutex_acquire eid tid priority before tt after
  | MutexProgramRelease eid => atomic_mutex_release sg eid before tt after
  | MutexProgramHandover eid tid => atomic_mutex_release_with_handover sg eid before tid after
  | MutexProgramDelete eid option => exists result, mutex_del_critical sg eid option before result after
  | MutexProgramWait eid tid event old kind timeout =>
      before.(EventState).(inUsedEventStates) eid = Some event /\
      before.(TskState).(inUsedTaskStates) tid = Some old /\
      task_holds_no_mutex before.(EventState) tid /\
      after = event_pend_state sg before eid event tid old kind timeout
  | MutexProgramCleanup tid old multi clear_message =>
      before.(TskState).(inUsedTaskStates) tid = Some old /\
      after = replace_TskS
        (glob_task_set_usedtask before.(TskState) tid (task_event_pend_cleanup multi clear_message old)) before
  end.

Definition mutex_program_operation_client (actor : option nat) (operation : MutexProgramOperation)
  : KernelClientAction :=
  {| kernel_client_actor := actor; kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false; kernel_client_step := mutex_program_operation operation |}.

Lemma mutex_program_operation_source : forall operation sg before after,
  UCOS2_state_inv sg before -> mutex_program_operation operation sg before after ->
  mutex_owner_source_history sg before after.
Proof.
  intros operation sg before after Hvalid Hstep; destruct operation; cbn in Hstep.
  - destruct Hstep; apply mutex_owner_source_step_history; eapply MutexOwnerSourceAcquire; eassumption.
  - apply mutex_owner_source_step_history; eapply MutexOwnerSourceRelease; eassumption.
  - apply mutex_owner_source_step_history; eapply MutexOwnerSourceHandover; eassumption.
  - destruct Hstep as [result Hstep]; eapply mutex_program_del_critical_source; eassumption.
  - destruct Hstep as [He [Hold [Hfree ->]]].
    apply mutex_owner_source_step_history; apply MutexOwnerSourceWait; assumption.
  - destruct Hstep as [Hold ->].
    apply mutex_owner_source_step_history; apply MutexOwnerSourceCleanup; assumption.
Qed.

(** Extension by a proved write footprint, not by assuming owner-use at
    the endpoint. This covers a real Memory/Timer/Interrupt/Scheduler or
    other source fragment ONLY when it leaves both maps unchanged. An
    actual task/Event mutation must use its own source case below instead;
    arbitrary ISR/callback implementations are not classified by default. *)
Definition mutex_program_other_fields_client (action : KernelClientAction) : Prop :=
  forall sg before after, kernel_client_step action sg before after ->
    after.(TskState).(inUsedTaskStates) = before.(TskState).(inUsedTaskStates) /\
    after.(EventState).(inUsedEventStates) = before.(EventState).(inUsedEventStates).

Inductive mutex_program_source_client : KernelClientAction -> Prop :=
| MutexProgramSourceOtherFields : forall action,
    mutex_program_other_fields_client action -> mutex_program_source_client action
| MutexProgramSourceTaskLifecycle : forall action,
    mutex_program_source_client (task_creation_client action)
| MutexProgramSourceTaskPublication : forall publication,
    mutex_program_source_client (task_create_stack_publication_client publication)
| MutexProgramSourceMutexCreate : forall actor priority,
    mutex_program_source_client (mutex_del_publication_client actor priority)
| MutexProgramSourceProjected : forall action,
    sem_pend_projected_source_client action -> mutex_program_source_client action
| MutexProgramSourceSemAccept : forall actor eid count,
    mutex_program_source_client (sem_accept_critical_client actor eid count)
| MutexProgramSourceOperation : forall actor operation,
    mutex_program_source_client (mutex_program_operation_client actor operation)
| MutexProgramSourceNonMutexPublication : forall actor eid allocation event,
    event.(eventType) <> OS_EVENT_TYPE_MUTEX ->
    mutex_program_source_client (event_create_publication_client actor eid allocation event)
| MutexProgramSourceProfileCut : forall cut,
    mutex_program_source_client (kernel_full_profile_cut_client cut)
| MutexProgramSourceReachable : forall initial action,
    mutex_program_source_client action ->
    mutex_program_source_client (mutex_program_reachable_client initial action).

Lemma mutex_program_source_client_history : forall action sg before after,
  mutex_program_source_client action -> UCOS2_state_inv sg before ->
  kernel_client_step action sg before after -> mutex_owner_source_history sg before after.
Proof.
  intros action sg before after Hclient; revert sg before after.
  induction Hclient; intros sg before after Hvalid Hstep.
  - destruct (H sg before after Hstep) as [Htasks Hevents].
    apply mutex_owner_source_step_history; apply MutexOwnerSourceFrame; assumption.
  - apply mutex_owner_source_step_history; eapply MutexOwnerSourceTaskLifecycle; eassumption.
  - apply mutex_owner_source_step_history; eapply MutexOwnerSourceTaskPublication; eassumption.
  - destruct Hstep as [_ [result Hstep]].
    apply mutex_owner_source_step_history; eapply MutexOwnerSourceCreate; eassumption.
  - eapply mutex_program_projected_client_source; eassumption.
  - eapply mutex_program_sem_accept_source; eassumption.
  - exact (mutex_program_operation_source operation sg before after Hvalid Hstep).
  - destruct Hstep as [_ [_ ->]].
    apply mutex_owner_source_step_history; apply MutexOwnerSourceNonMutexPublication; exact H.
  - destruct Hstep as [Hinput ->]; destruct cut as [|observed|slot node].
    + apply mutex_owner_source_step_history; apply MutexOwnerSourceFrame; reflexivity.
    + apply mutex_owner_source_step_history; apply MutexOwnerSourceFrame; reflexivity.
    + destruct Hinput as [_ Hnode].
      eapply mutex_program_task_fields_source with (old := node) (new := task_record_context_switch node);
        [exact Hnode|reflexivity|reflexivity|reflexivity|reflexivity].
  - destruct Hstep as [_ Hstep]; eapply IHHclient; eassumption.
Qed.

Lemma mutex_program_task_begin_registered : forall origin,
  mutex_program_source_client (task_create_begin_client origin).
Proof.
  intros; apply MutexProgramSourceOtherFields.
  intros sg before after [_ ->]; split; reflexivity.
Qed.

Lemma mutex_program_task_reserve_registered : forall priority invocation origin,
  mutex_program_source_client (task_create_reserve_client priority invocation origin).
Proof.
  intros; apply MutexProgramSourceOtherFields.
  intros sg before after [_ ->]; split; reflexivity.
Qed.

Lemma mutex_program_task_rollback_registered : forall priority invocation,
  mutex_program_source_client (task_create_rollback_client priority invocation).
Proof.
  intros; apply MutexProgramSourceOtherFields.
  intros sg before after [_ ->]; split; reflexivity.
Qed.

Lemma mutex_program_event_allocate_registered : forall actor invocation,
  mutex_program_source_client (event_create_allocate_client actor invocation).
Proof.
  intros; apply MutexProgramSourceOtherFields.
  intros sg before after [_ [result Hstep]].
  unfold event_create_allocate_critical in Hstep.
  destruct before.(EventState).(unUsedEventStates).
  - destruct Hstep as [_ ->]; split; reflexivity.
  - destruct Hstep as [image [_ [_ ->]]]; split; reflexivity.
Qed.

Lemma mutex_program_event_private_store_registered : forall actor eid allocation field stored,
  mutex_program_source_client (event_create_private_store_client actor eid allocation field stored).
Proof.
  intros; apply MutexProgramSourceOtherFields.
  intros sg before after [_ ->]; split; reflexivity.
Qed.

(** The configuration is a subtype of the EXISTING region contract, not
    a kernel-state Record or an altered generic global invariant. Every
    registered action needs a proved source classification. In particular
    constructing it cannot silently filter an unknown registered client.
    Its ordinary resource/name proofs remain those of the same region. *)
Definition MutexProgramConfiguration : Type :=
  { critical : CriticalRegionResources |
    forall action, critical.(critical_region_clients) action -> mutex_program_source_client action }.

Definition mutex_program_region (configuration : MutexProgramConfiguration) : CriticalRegionResources :=
  proj1_sig configuration.

Definition mutex_program_configure (critical : CriticalRegionResources)
  (sources : forall action, critical.(critical_region_clients) action -> mutex_program_source_client action)
  : MutexProgramConfiguration := exist _ critical sources.

Lemma mutex_program_region_preserves_registration : forall critical sources action,
  critical_region_clients (mutex_program_region (mutex_program_configure critical sources)) action <->
  critical_region_clients critical action.
Proof. intros; reflexivity. Qed.

Lemma mutex_program_region_protocol : forall configuration sg,
  mutex_owner_region_source_protocol (mutex_program_region configuration) sg.
Proof.
  intros [critical Hsources] sg action before after Hin Hvalid Hstep.
  eapply mutex_program_source_client_history; [apply Hsources; exact Hin|exact Hvalid|exact Hstep].
Qed.

Lemma mutex_program_region_client_resources : forall configuration initial action,
  critical_region_clients (mutex_program_region configuration) action ->
  kernel_client_preserves_resources (mutex_program_state_inv UCOS2_state_inv initial) action.
Proof.
  intros [critical Hsources] initial action Hin.
  apply mutex_program_client_preserves_resources.
  - apply kernel_client_certificate_preserves_selected_resources.
    exact (critical_region_client_certificates critical action Hin).
  - intros; eapply mutex_program_source_client_history; [apply Hsources; exact Hin|eassumption|eassumption].
Qed.

Lemma mutex_program_region_interval_reachable : forall configuration initial sg invocation before after,
  mutex_program_state_inv UCOS2_state_inv initial sg before ->
  critical_region_interval (mutex_program_region configuration) sg invocation before after ->
  mutex_program_state_inv UCOS2_state_inv initial sg after.
Proof.
  intros configuration initial sg invocation before after Hbefore Hinterval.
  assert (Hclients : forall action,
    critical_region_clients (mutex_program_region configuration) action ->
    kernel_client_preserves_resources (mutex_program_state_inv UCOS2_state_inv initial) action).
  { intros; eapply mutex_program_region_client_resources; eassumption. }
  exact (proj1 (critical_region_interval_transports_invariant
    (mutex_program_state_inv UCOS2_state_inv initial) (mutex_program_region configuration)
    sg invocation before after Hclients Hinterval Hbefore)).
Qed.
