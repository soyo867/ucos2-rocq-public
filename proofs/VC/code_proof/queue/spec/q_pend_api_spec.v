Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Export Ucos2Verify.VC.code.queue.spec.q_pend_call_spec.
Require Export Ucos2Verify.VC.code.queue.spec.q_pend_spec.
Require Export Ucos2Verify.VC.code.queue.spec.q_pend_sched_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Export Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Export Ucos2Verify.VC.code.queue.spec.q_accept_proof_helpers.
Require Import Ucos2Verify.VC.code.queue.spec.q_query_proof_helpers.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_entry_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_entry_return_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_idle_protocol_spec.
Require Import Ucos2Verify.lib.kernel_runtime_inv.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_sched_call_spec.
Import UCOS2_C_Rules ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** All four precritical tests occur before the nonempty fast path. A zero
    message is a successful message, not an empty/error discriminator. *)
Definition q_pend_precritical_error (pevent type_byte int_nesting lock_nesting : Z)
  : option OSErrCode :=
  if Z.eqb pevent 0 then Some OS_ERR_PEVENT_NULL
  else q_pend_context_error type_byte int_nesting lock_nesting.

Lemma q_pend_precritical_null : forall type_byte int_nesting lock_nesting,
  q_pend_precritical_error 0 type_byte int_nesting lock_nesting = Some OS_ERR_PEVENT_NULL.
Proof. reflexivity. Qed.

Lemma q_pend_precritical_type : forall pevent type_byte int_nesting lock_nesting,
  pevent <> 0 -> type_byte <> 2 ->
  q_pend_precritical_error pevent type_byte int_nesting lock_nesting = Some OS_ERR_EVENT_TYPE.
Proof.
  intros; unfold q_pend_precritical_error; rewrite (proj2 (Z.eqb_neq _ _) H).
  apply q_pend_context_error_type_first; assumption.
Qed.

Definition q_pend_entry_handle_protocol critical sg invocation before eid observed : Prop :=
  forall entry, critical_region_interval critical sg invocation before entry ->
    exists current, mutex_query_lookup entry eid current /\
      current.(eventGeneration) = observed.(eventGeneration) /\
      current.(eventType) = observed.(eventType).

Definition q_pend_api_input critical sg invocation pe before eid observed : Prop :=
  pe = 0 \/ (pe <> 0 /\ pe = event_addr sg eid /\ valid_event_id sg eid /\
    q_query_public_slot before eid observed /\
    (event_slot_type_value before.(EventState) eid = 2 ->
      before.(IntrState).(intNesting) <= 0 -> before.(IntrState).(lockNesting) <= 0 ->
      q_pend_entry_handle_protocol critical sg invocation before eid observed)).

Definition q_pend_api_prefix pe before eid : Prop :=
  q_pend_precritical_error pe (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None /\
  before.(IntrState).(intNesting) = 0 /\ before.(IntrState).(lockNesting) = 0.

(** Only the first acquisition is protected by the handle protocol. A
    Delete-ALWAYS while waiting is admitted by the separate wait history.
    The source obligations below reuse the checked Task entry/Idle
    preservation interfaces, not a new list of allowed foreign APIs. *)
Definition q_pend_entry_source_protocol critical sg call before : Prop :=
  (forall action, critical.(critical_region_clients) action ->
    mutex_pend_entry_source_client call.(os_sched_call_invocation)
      call.(os_sched_call_stack).(stackLeaseSlot)
      call.(os_sched_call_stack).(stackLeaseGeneration) action) /\
  (forall idle, mutex_idle_slot before.(TskState) idle ->
    mutex_idle_region_source_protocol critical sg idle).

Definition q_pend_nonblocking_acquire critical sg call before eid : Prop :=
  forall entry current queue,
    critical_region_interval critical sg call.(os_sched_call_invocation) before entry ->
    mutex_query_lookup entry eid current -> current.(eventType) = OS_EVENT_TYPE_Q ->
    current.(queueFields) = Some queue -> 0 < queue_entries queue.

Definition q_pend_api_admission (environment : option TaskStackCallEnvironment)
  critical sg call pe before eid : Prop :=
  q_pend_api_prefix pe before eid ->
  ((exists owned, environment = Some owned /\ q_pend_sched_clients owned critical) /\
    sem_pend_task_call_stage sg call before /\
    kernel_running_idle_ready sg before /\ kernel_call_stack_available call before /\
    q_pend_entry_source_protocol critical sg call before) \/
  q_pend_nonblocking_acquire critical sg call before eid.

Lemma q_pend_api_admission_early_error : forall environment critical sg call pe before eid error,
  q_pend_precritical_error pe (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = Some error ->
  q_pend_api_admission environment critical sg call pe before eid.
Proof. intros * Herror [Hclear _]; congruence. Qed.

Lemma q_pend_api_admission_nonblocking : forall environment critical sg call pe before eid,
  q_pend_nonblocking_acquire critical sg call before eid ->
  q_pend_api_admission environment critical sg call pe before eid.
Proof. intros * Hpositive _; right; exact Hpositive. Qed.

Lemma q_pend_api_admission_task : forall owned critical sg call pe before eid,
  sem_pend_task_call_stage sg call before -> kernel_running_idle_ready sg before ->
  kernel_call_stack_available call before -> q_pend_entry_source_protocol critical sg call before ->
  q_pend_sched_clients owned critical ->
  q_pend_api_admission (Some owned) critical sg call pe before eid.
Proof. intros * Hstage Hidle Havailable Hsource Hclients _; left; split; [eauto|]; auto. Qed.

Lemma q_pend_precritical_isr : forall pevent int_nesting lock_nesting,
  pevent <> 0 -> 0 < int_nesting ->
  q_pend_precritical_error pevent 2 int_nesting lock_nesting = Some OS_ERR_PEND_ISR.
Proof.
  intros; unfold q_pend_precritical_error; rewrite (proj2 (Z.eqb_neq _ _) H).
  apply q_pend_context_error_isr_before_lock; assumption.
Qed.

Lemma q_pend_precritical_locked : forall pevent lock_nesting,
  pevent <> 0 -> 0 < lock_nesting ->
  q_pend_precritical_error pevent 2 0 lock_nesting = Some OS_ERR_PEND_LOCKED.
Proof.
  intros; unfold q_pend_precritical_error, q_pend_context_error.
  rewrite (proj2 (Z.eqb_neq _ _) H); cbn [encode_event_type Z.eqb negb Z.ltb].
  rewrite (proj2 (Z.ltb_lt _ _) H0); reflexivity.
Qed.

Lemma q_pend_precritical_clear : forall pevent,
  pevent <> 0 -> q_pend_precritical_error pevent 2 0 0 = None.
Proof.
  intros; unfold q_pend_precritical_error; rewrite (proj2 (Z.eqb_neq _ _) H); reflexivity.
Qed.

(** The C-level completed-call history is the existing source relation,
    with the existing normal-return observation. The no-capsule arm does
    not invent a Task environment for a legal nonblocking call. These pure
    histories never produce ownership or promise that a blocked call returns. *)
Definition q_pend_call_history external (environment : option TaskStackCallEnvironment)
  critical sg original before returned after : Prop :=
  match environment with
  | Some owned => sem_pend_modular_call_history owned critical sg original before returned after
  | None => exists port,
      kernel_resumption_task_source_trace external port critical.(critical_region_clients) sg
        original.(os_sched_call_invocation) None original.(os_sched_call_origin)
        before false returned.(os_sched_call_origin) after /\
      kernel_call_normal_return original before returned after
  end.

Lemma q_pend_call_history_same_call : forall external environment critical sg original before returned after,
  q_pend_call_history external environment critical sg original before returned after ->
  kernel_stack_call_same_call returned original.
Proof.
  intros external [owned|] critical sg original before returned after Hhistory.
  - exact (proj1 (proj2 Hhistory)).
  - destruct Hhistory as [port [_ [Hsame _]]]; exact Hsame.
Qed.

(** This is the Queue instance of the actual Scheduler's Save/body/Restore
    history. The selected-return observation is proved at that C endpoint;
    no eventual-return obligation is encoded in this partial relation. *)
Definition q_pend_schedule_program (environment : option TaskStackCallEnvironment)
  critical sg original (mask : Z) : program UCOS2_Verify_State OsSchedCallContext :=
  fun before returned after => q_pend_sched_return environment critical sg original before returned after.

Definition q_pend_call_program external environment critical sg original
  : program UCOS2_Verify_State OsSchedCallContext :=
  fun before returned after => q_pend_call_history external environment critical sg original before returned after.

Definition q_pend_finish_program external environment critical sg original
  (result : addr * OSErrCode) : program UCOS2_Verify_State (OSErrCode * addr) :=
  bind (q_pend_call_program external environment critical sg original)
    (fun _ => StateRelMonad.ret (snd result, fst result)).

(** Each bind corresponds to a real source boundary: first Save, first
    critical work, and either final Restore or Restore/Sched/Save/resume/
    Restore. In particular the protected checkpoint is not the returned
    current state. The same original call is retained by the call histories. *)
Definition q_pend_started_program external environment critical sg entered eid (timeout mask : Z)
  (start : QueuePendStart) : program UCOS2_Verify_State (OSErrCode * addr) :=
  match start with
  | QueuePendImmediate message =>
      q_pend_finish_program external environment critical sg entered (message, OS_ERR_NONE)
  | QueuePendWaiting tid generation =>
      bind (q_pend_call_program external environment critical sg entered)
        (fun released => bind (q_pend_schedule_program environment critical sg released mask)
          (fun scheduled => bind (q_pend_call_program external environment critical sg scheduled)
            (fun resumed => bind (q_pend_resume_critical sg eid)
              (q_pend_finish_program external environment critical sg resumed))))
  end.

Definition q_pend_api_program external environment critical sg original pevent eid timeout mask
  : program UCOS2_Verify_State (OSErrCode * addr) :=
  bind (get eq) (fun before =>
    match q_pend_precritical_error pevent (event_slot_type_value before.(EventState) eid)
      before.(IntrState).(intNesting) before.(IntrState).(lockNesting) with
    | Some error => StateRelMonad.ret (error, 0)
    | None => bind (q_pend_call_program external environment critical sg original)
        (fun entered => bind (q_pend_first_critical sg eid timeout)
          (q_pend_started_program external environment critical sg entered eid timeout mask))
    end).

Definition q_pend_api_safe external environment critical sg original pevent eid timeout mask before
  (X : OSErrCode * addr -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before)
    (q_pend_api_program external environment critical sg original pevent eid timeout mask) X.

Definition q_pend_return_safe current message error
  (X : OSErrCode * addr -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq current) (StateRelMonad.ret (error, message)) X.

Lemma q_pend_api_early_return : forall external environment critical sg original pevent eid timeout mask before error,
  q_pend_precritical_error pevent (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = Some error ->
  q_pend_api_program external environment critical sg original pevent eid timeout mask
    before (error, 0) before.
Proof.
  intros; unfold q_pend_api_program, StateRelMonad.bind, get.
  exists before, before; split; [split; reflexivity|]. rewrite H; split; reflexivity.
Qed.

Lemma q_pend_api_immediate_return : forall external environment critical sg original pevent eid timeout mask
  before entered entry checkpoint returned current message,
  q_pend_precritical_error pevent (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  q_pend_call_history external environment critical sg original before entered entry ->
  q_pend_first_critical sg eid timeout entry (QueuePendImmediate message) checkpoint ->
  q_pend_call_history external environment critical sg entered checkpoint returned current ->
  q_pend_api_program external environment critical sg original pevent eid timeout mask
    before (OS_ERR_NONE, message) current.
Proof.
  intros * Hprefix Hsave Hstep Hrestore.
  unfold q_pend_api_program, StateRelMonad.bind, get.
  exists before, before; split; [split; reflexivity|]. rewrite Hprefix.
  exists entered, entry; split; [exact Hsave|].
  exists (QueuePendImmediate message), checkpoint; split; [exact Hstep|].
  cbn [q_pend_started_program q_pend_finish_program StateRelMonad.bind].
  exists returned, current; split; [exact Hrestore|]. split; reflexivity.
Qed.

Lemma q_pend_api_waiting_return : forall external owned critical sg original pevent eid timeout mask
  before entered entry tid generation waiting released unmasked scheduled selected resumed resume_entry
  message error cleaned returned current,
  q_pend_precritical_error pevent (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  q_pend_call_history external (Some owned) critical sg original before entered entry ->
  q_pend_first_critical sg eid timeout entry (QueuePendWaiting tid generation) waiting ->
  q_pend_call_history external (Some owned) critical sg entered waiting released unmasked ->
  q_pend_sched_return (Some owned) critical sg released unmasked scheduled selected ->
  q_pend_call_history external (Some owned) critical sg scheduled selected resumed resume_entry ->
  q_pend_resume_critical sg eid resume_entry (message, error) cleaned ->
  q_pend_call_history external (Some owned) critical sg resumed cleaned returned current ->
  q_pend_api_program external (Some owned) critical sg original pevent eid timeout mask
    before (error, message) current.
Proof.
  intros * Hprefix Hsave Hstart Hrelease Hschedule Hresume Hcleanup Hreturn.
  unfold q_pend_api_program, StateRelMonad.bind, get.
  exists before, before; split; [split; reflexivity|]. rewrite Hprefix.
  exists entered, entry; split; [exact Hsave|].
  exists (QueuePendWaiting tid generation), waiting; split; [exact Hstart|].
  cbn [q_pend_started_program StateRelMonad.bind].
  exists released, unmasked; split; [exact Hrelease|].
  exists scheduled, selected; split.
  - exact Hschedule.
  - exists resumed, resume_entry; split; [exact Hresume|].
    exists (message, error), cleaned; split; [exact Hcleanup|].
    unfold q_pend_finish_program, StateRelMonad.bind.
    exists returned, current; split; [exact Hreturn|]. split; reflexivity.
Qed.

Lemma q_pend_api_safe_return : forall external environment critical sg original pevent eid timeout mask
  before message error current X,
  q_pend_api_program external environment critical sg original pevent eid timeout mask
    before (error, message) current ->
  q_pend_api_safe external environment critical sg original pevent eid timeout mask before X ->
  q_pend_return_safe current message error X.
Proof.
  intros * Hprogram Hsafe; unfold q_pend_api_safe in Hsafe; unfold q_pend_return_safe.
  eapply (highstependret_derive
    (q_pend_api_program external environment critical sg original pevent eid timeout mask)
    (eq before) (error, message) (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; auto.
Qed.

Lemma q_pend_prefix_guards : forall pe before eid,
  q_pend_api_prefix pe before eid ->
  pe <> 0 /\ event_slot_type_value before.(EventState) eid = 2 /\
  before.(IntrState).(intNesting) <= 0 /\ before.(IntrState).(lockNesting) <= 0.
Proof.
  intros pe before eid [H Hcounters]; unfold q_pend_precritical_error,
    q_pend_context_error in H; cbn [encode_event_type] in H.
  destruct (Z.eqb pe 0) eqn:Hpe; [discriminate|].
  destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 2) eqn:Htype;
    cbn [negb] in H; [|discriminate].
  destruct (Z.ltb 0 before.(IntrState).(intNesting)) eqn:Hint; [discriminate|].
  destruct (Z.ltb 0 before.(IntrState).(lockNesting)) eqn:Hlock; [discriminate|].
  apply Z.eqb_neq in Hpe; apply Z.eqb_eq in Htype;
    apply Z.ltb_ge in Hint; apply Z.ltb_ge in Hlock; auto.
Qed.

Lemma q_pend_save_acquire_facts : forall external port critical sg original returned
  pe eid observed mask saved before acquired,
  UCOS2_state_inv sg before ->
  q_pend_api_input critical sg original.(os_sched_call_invocation) pe before eid observed ->
  q_pend_api_prefix pe before eid ->
  kernel_call_save_source external port critical sg original returned mask saved before acquired ->
  exists current, q_accept_acquire_facts critical sg original.(os_sched_call_invocation)
    eid mask saved before acquired observed current.
Proof.
  intros * Hvalid Hinput Hprefix Hsave.
  destruct (q_pend_prefix_guards _ _ _ Hprefix) as [Hnonnull [Htype [Hint Hlock]]].
  destruct Hinput as [Hzero|[_ [Haddress [Hid [Hslot Hprotocol]]]]]; [contradiction|].
  destruct (q_query_public_slot_is_queue before eid observed Hslot Htype) as [Hlookup Hqueue].
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsave) as Hinterval.
  destruct (Hprotocol Htype Hint Hlock acquired Hinterval) as [current [Hcurrent [Hg Hkind]]].
  pose proof (proj1 (critical_region_interval_transports_resources _ _ _ _ _ Hinterval Hvalid)) as Hvalid'.
  pose proof (proj2 (proj2 (proj2 (proj2 Hsave)))) as Hsaved.
  exists current; unfold q_accept_acquire_facts, q_query_acquire_facts.
  repeat first [assumption | split | congruence].
Qed.

Lemma q_pend_empty_acquire_owned : forall environment critical sg original pe before eid
  entry current queue,
  q_pend_api_admission environment critical sg original pe before eid ->
  q_pend_api_prefix pe before eid ->
  critical_region_interval critical sg original.(os_sched_call_invocation) before entry ->
  mutex_query_lookup entry eid current -> current.(eventType) = OS_EVENT_TYPE_Q ->
  current.(queueFields) = Some queue -> queue_entries queue <= 0 ->
  exists owned, environment = Some owned /\ q_pend_sched_clients owned critical.
Proof.
  intros * Hadmit Hprefix Hinterval Hlookup Htype Hfields Hempty.
  destruct (Hadmit Hprefix) as [[[owned [Howned Hclients]] _]|Hpositive]; [eauto|].
  specialize (Hpositive entry current queue Hinterval Hlookup Htype Hfields); lia.
Qed.


Lemma q_pend_empty_acquire_stage : forall owned critical sg original entered pe before eid
  entry current queue,
  UCOS2_state_inv sg before -> UCOS2_state_inv sg entry ->
  q_pend_api_admission (Some owned) critical sg original pe before eid ->
  q_pend_api_prefix pe before eid ->
  sem_pend_modular_call_history owned critical sg original before entered entry ->
  sem_pend_save_rely sg before entry ->
  mutex_query_lookup entry eid current -> current.(eventType) = OS_EVENT_TYPE_Q ->
  current.(queueFields) = Some queue -> queue_entries queue <= 0 ->
  sem_pend_task_call_stage sg entered entry /\ sem_pend_blocking_call_stage sg entered entry.
Proof.
  intros * Hvalid Hentry Hadmit Hprefix Hhistory Hrely Hlookup Htype Hfields Hempty.
  pose proof Hhistory as [Htrace [Hsame Havailable_return]].
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)
    as [Hinterval Hcontrol].
  destruct (Hadmit Hprefix) as [[Howned [Hstage [Hruntime [Havailable [Hclients Hidle_clients]]]]]|Hpositive].
  2: { specialize (Hpositive entry current queue Hinterval Hlookup Htype Hfields); lia. }
  destruct Hstage as [Hsource [Hrunning [old [Hready [Hg [Hnonidle [He [Hm Hf]]]]]]]].
  destruct (mutex_pend_modular_history_preserves_ready_entry owned critical sg original entered
    before entry old Hclients Hvalid Hsource Hrunning Hready
    ltac:(unfold sem_pend_task_unregistered; auto) Hhistory Hrely)
    as [Hsource' [Hrunning' [node [Hready' [Hg' [He' [Hm' Hf']]]]]]].
  pose proof Hvalid as [_ [_ [_ [_ [_ [Htail _]]]]]].
  destruct (Htail Hrunning) as [prefix [idle [idle_node [Horder [Hidle_node [Hidleprio Hothers]]]]]].
  assert (Hslot : mutex_idle_slot before.(TskState) idle) by (exists prefix; exact Horder).
  assert (Hdifferent : original.(os_sched_call_stack).(stackLeaseSlot) <> idle).
  { intro Hequal; pose proof (proj1 Hready) as Hold; rewrite Hequal in Hold.
    assert (old = idle_node) by congruence; subst old; contradiction. }
  assert (Hslot' : mutex_idle_slot entry.(TskState) idle).
  { eapply (mutex_idle_region_interval_preserves_slot critical sg idle
      original.(os_sched_call_invocation) before entry);
      [apply Hidle_clients; exact Hslot|exact Hvalid|exact Hinterval|exact Hslot]. }
  assert (Hnonidle' : node.(curPrio) <> sg.(osLowestPrio)).
  { eapply mutex_non_idle_priority; [exact (proj1 (proj2 Hentry))| |exact (proj1 Hready')|].
    - eapply mutex_running_idle_slot_task; eassumption.
    - rewrite (proj2 (proj2 Hsame)); exact Hdifferent. }
  split.
  - unfold sem_pend_task_call_stage; split; [exact Hsource'|]. split; [exact Hrunning'|].
    exists node; split; [exact Hready'|]. repeat split; assumption.
  - destruct Hrely as [[Hrun Hcounters] [Hruntime_return [Hcache Hready_return]]].
    pose proof (proj2 Hprefix) as [Hint Hlock].
    unfold sem_pend_blocking_call_stage; split.
    + apply (Hruntime_return Hruntime); exact Hrunning'.
    + split; [apply Havailable_return; exact Havailable|].
      rewrite Hcounters; auto.
Qed.

(** Literal CPU-call indices. Only an actual empty observation demands
    Task resources; the ordinary nonblocking and all early-error arms
    retain the no-capsule domain. *)
Inductive QueuePendSavePhase : Type :=
| QueuePendAcquirePhase (pe : addr) (eid : EventID) (observed : OSEventAbstractState)
| QueuePendResumePhase (phase : QueuePendCallPhase).

Definition q_pend_save_phase_pre phase environment critical sg call mask before : Prop :=
  match phase with
  | QueuePendAcquirePhase pe eid observed =>
      q_pend_api_input critical sg call.(os_sched_call_invocation) pe before eid observed /\
      q_pend_api_prefix pe before eid /\ q_pend_api_admission environment critical sg call pe before eid
  | QueuePendResumePhase (QueuePendWaitPhase original initial_mask initial observed eid timeout waiting) =>
      mask = initial_mask /\
      (exists owned, environment = Some owned /\ q_pend_sched_clients owned critical) /\
      q_pend_wait_selected_at sg original initial observed eid timeout waiting call before
  end.

Definition q_pend_save_phase_observation phase external environment critical sg call returned
  mask saved before acquired : Prop :=
  q_pend_call_history external environment critical sg call before returned acquired /\
  interrupt_saved_value mask saved /\
  match phase with
  | QueuePendAcquirePhase pe eid observed =>
      exists current, q_accept_acquire_facts critical sg call.(os_sched_call_invocation)
        eid mask saved before acquired observed current /\
        (forall queue, current.(queueFields) = Some queue -> queue_entries queue <= 0 ->
          (exists owned, environment = Some owned /\ q_pend_sched_clients owned critical) /\
          sem_pend_task_call_stage sg returned acquired /\ sem_pend_blocking_call_stage sg returned acquired)
  | QueuePendResumePhase (QueuePendWaitPhase original initial_mask initial observed eid timeout waiting) =>
      (exists owned, environment = Some owned /\ q_pend_sched_clients owned critical) /\
      q_pend_wait_selected_at sg original initial observed eid timeout waiting returned acquired
  end.

Definition q_pend_save_input phase external platform environment critical saved_local
  sg call mask before : Assertion :=
  coq_prop (q_pend_save_phase_pre phase environment critical sg call mask before) &&
  (sem_pend_continuation_save_input external platform environment critical saved_local sg call mask before **
    unmap_table_rep sg).

Definition q_pend_masked_frame external platform environment critical saved_local
  sg call saved acquired current : Assertion :=
  critical_region_masked platform critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) saved acquired ** os_sched_context_resources external call **
  sem_pend_optional_continuation_resources external platform environment saved_local call current **
  unmap_table_rep sg.

Definition q_pend_save_output phase external platform environment critical saved_local
  sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (q_pend_save_phase_observation phase external environment critical sg original returned
      mask saved before acquired) &&
    (q_pend_masked_frame external platform environment critical saved_local sg returned saved acquired acquired **
      UCOS2_inv sg acquired).

Definition q_pend_restore_input (phase : option QueuePendCallPhase) external platform environment critical saved_local
  sg call mask saved acquired released : Assertion :=
  coq_prop (interrupt_saved_value mask saved /\
    match phase with None => True | Some waiting =>
      (exists owned, environment = Some owned /\ q_pend_sched_clients owned critical) /\
      q_pend_restore_phase_pre waiting environment critical sg call mask released end) &&
  (q_pend_masked_frame external platform environment critical saved_local sg call saved acquired released ** UCOS2_inv sg released).

Definition q_pend_restore_output (phase : option QueuePendCallPhase) external platform environment critical saved_local
  sg original mask released : Assertion :=
  EX returned current,
    coq_prop (q_pend_call_history external environment critical sg original released returned current /\
      match phase with None => True | Some waiting =>
        (exists owned, environment = Some owned /\ q_pend_sched_clients owned critical) /\
        q_pend_restore_phase_pre waiting environment critical sg returned mask current end) &&
    (sem_pend_continuation_save_input external platform environment critical saved_local sg returned mask current **
      unmap_table_rep sg).

Definition q_pend_api_post external platform environment critical saved_local sg original
  mask pe eid timeout perr before message X : Assertion :=
  EX returned after error,
    coq_prop (q_pend_api_program external environment critical sg original pe eid timeout mask
      before (error, message) after /\ q_pend_return_safe after message error X /\
      kernel_stack_call_same_call returned original) &&
    (perr # UChar |-> encode_os_err_code error **
      sem_pend_continuation_save_input external platform environment critical saved_local sg returned mask after **
      unmap_table_rep sg).

(** Pure cut observations record only source edges already traversed by
    this call. No continuation assertion entails that a future edge exists. *)
Definition q_pend_immediate_checkpoint external environment critical sg original before entered entry
  eid timeout message checkpoint : Prop :=
  q_pend_call_history external environment critical sg original before entered entry /\
  q_pend_first_critical sg eid timeout entry (QueuePendImmediate message) checkpoint.

Definition q_pend_first_wait_checkpoint external environment critical sg original before entered entry
  eid timeout waiting : Prop :=
  q_pend_call_history external environment critical sg original before entered entry /\
  q_pend_first_critical sg eid timeout entry
    (QueuePendWaiting original.(os_sched_call_stack).(stackLeaseSlot)
      original.(os_sched_call_stack).(stackLeaseGeneration)) waiting.

Definition q_pend_released_checkpoint external environment critical sg original before entered entry
  eid timeout waiting released unmasked : Prop :=
  q_pend_first_wait_checkpoint external environment critical sg original before entered entry eid timeout waiting /\
  q_pend_call_history external environment critical sg entered waiting released unmasked.

Definition q_pend_scheduling_checkpoint external environment critical sg original before entry
  eid timeout waiting released unmasked : Prop :=
  exists entered, q_pend_released_checkpoint external environment critical sg original before entered entry
    eid timeout waiting released unmasked.

Definition q_pend_sched_admitted (environment : option TaskStackCallEnvironment) critical : Prop :=
  exists owned, environment = Some owned /\ q_pend_sched_clients owned critical.

Definition q_pend_scheduled_checkpoint external environment critical sg original before eid timeout scheduled selected : Prop :=
  exists entered entry waiting released unmasked,
    q_pend_released_checkpoint external environment critical sg original before entered entry
      eid timeout waiting released unmasked /\
    q_pend_sched_return environment critical sg released unmasked scheduled selected.

Definition q_pend_resume_checkpoint external environment critical sg original before eid timeout resumed resume_entry : Prop :=
  exists scheduled selected,
    q_pend_scheduled_checkpoint external environment critical sg original before eid timeout scheduled selected /\
    q_pend_call_history external environment critical sg scheduled selected resumed resume_entry.

Definition q_pend_first_owner external platform environment critical saved_local sg original entered
  mask saved pe before entry eid observed : Assertion :=
  coq_prop (q_pend_save_phase_observation (QueuePendAcquirePhase pe eid observed)
    external environment critical sg original entered mask saved before entry) &&
  (os_sched_context_resources external entered **
    sem_pend_optional_continuation_resources external platform environment saved_local entered entry **
    unmap_table_rep sg).

Definition q_pend_empty_snapshot external environment critical sg original entered
  mask saved pe before entry eid observed current tid old : Prop :=
  q_pend_save_phase_observation (QueuePendAcquirePhase pe eid observed)
    external environment critical sg original entered mask saved before entry /\
  q_pend_wait_entry sg entry eid current tid old /\
  kernel_call_task_source entered entry /\
  sched_current_consistency entry.(TskState) entry.(SchedState) /\
  sem_pend_blocking_call_stage sg entered entry /\
  (exists owned, environment = Some owned /\ q_pend_sched_clients owned critical).

Lemma q_pend_resume_checkpoint_owned : forall external environment critical sg original before eid timeout resumed resume_entry,
  q_pend_resume_checkpoint external environment critical sg original before eid timeout resumed resume_entry ->
  exists owned, environment = Some owned.
Proof.
  intros * [scheduled [selected [[entered [entry [waiting [released [unmasked [Hreleased Hschedule]]]]]] Hresume]]].
  destruct environment as [owned|]; [eauto|contradiction].
Qed.

Lemma q_pend_immediate_checkpoint_return : forall external environment critical sg original pe eid timeout mask
  before entered entry message checkpoint returned current,
  q_pend_api_prefix pe before eid ->
  q_pend_immediate_checkpoint external environment critical sg original before entered entry eid timeout message checkpoint ->
  q_pend_call_history external environment critical sg entered checkpoint returned current ->
  q_pend_api_program external environment critical sg original pe eid timeout mask before (OS_ERR_NONE, message) current.
Proof. intros * [Hprefix _] [Hsave Hfirst] Hrestore; eapply q_pend_api_immediate_return; eassumption. Qed.

Lemma q_pend_resume_checkpoint_return : forall external environment critical sg original pe eid timeout mask
  before resumed resume_entry message error cleaned returned current,
  q_pend_api_prefix pe before eid ->
  q_pend_resume_checkpoint external environment critical sg original before eid timeout resumed resume_entry ->
  q_pend_resume_critical sg eid resume_entry (message, error) cleaned ->
  q_pend_call_history external environment critical sg resumed cleaned returned current ->
  q_pend_api_program external environment critical sg original pe eid timeout mask before (error, message) current.
Proof.
  intros * [Hprefix _] Hcheckpoint Hcleanup Hreturn.
  destruct (q_pend_resume_checkpoint_owned _ _ _ _ _ _ _ _ _ _ Hcheckpoint) as [owned ->].
  destruct Hcheckpoint as [scheduled [selected [[entered [entry [waiting [released [unmasked
    [[[Hfirst_save Hfirst] Hrelease] Hschedule]]]]]] Hresume]]].
  eapply q_pend_api_waiting_return; eassumption.
Qed.

(** These consequences consume the common C-modular producers. The
    selected rely is an existing C-environment obligation, not a new
    promise of the CPU port; in the unowned arm only a real nonblocking
    acquisition can reach the Queue data path. *)
Lemma q_pend_modular_save_acquire_observation : forall environment critical sg call returned
  pe eid observed mask saved before acquired,
  UCOS2_state_inv sg before ->
  q_pend_save_phase_pre (QueuePendAcquirePhase pe eid observed)
    (Some environment) critical sg call mask before ->
  kernel_call_save_source environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical sg call returned mask saved before acquired ->
  kernel_call_normal_return call before returned acquired ->
  sem_pend_save_rely sg before acquired ->
  q_pend_save_phase_observation (QueuePendAcquirePhase pe eid observed)
    environment.(task_stack_call_external) (Some environment) critical sg call returned mask saved before acquired.
Proof.
  intros * Hvalid [Hinput [Hprefix Hadmit]] Hsave Hnormal Hrely.
  destruct (q_pend_save_acquire_facts _ _ _ _ _ _ _ _ _ _ _ _ _
    Hvalid Hinput Hprefix Hsave) as [current Hfacts].
  pose proof Hfacts as [Hinterval [Hvalid' [Hsaved [Hlookup [Hcurrent [Htype [Htype' Hgen]]]]]]].
  assert (Hhistory : sem_pend_modular_call_history environment critical sg call before returned acquired)
    by (split; [exact (proj1 Hsave)|exact Hnormal]).
  split; [exact Hhistory|]. split; [exact Hsaved|]. exists current; split; [exact Hfacts|].
  intros queue Hfields Hempty; split.
  - eapply q_pend_empty_acquire_owned; eassumption.
  - exact (q_pend_empty_acquire_stage environment critical sg call returned pe before eid
      acquired current queue Hvalid Hvalid' Hadmit Hprefix Hhistory Hrely Hcurrent Htype' Hfields Hempty).
Qed.

Lemma q_pend_masked_frame_owned : forall environment critical saved_local sg call saved acquired current,
  q_pend_masked_frame environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg call saved acquired current ** UCOS2_inv sg current --||--
  task_tcb_init_continuation_restore_input environment critical saved_local sg call saved acquired current **
    unmap_table_rep sg.
Proof.
  intros; unfold q_pend_masked_frame, sem_pend_optional_continuation_resources,
    task_tcb_init_continuation_restore_input; split; entailer!.
Qed.

Lemma q_pend_modular_save_acquire_output : forall environment critical saved_local sg call
  pe eid observed mask saved before,
  UCOS2_state_inv sg before ->
  q_pend_save_phase_pre (QueuePendAcquirePhase pe eid observed)
    (Some environment) critical sg call mask before ->
  kernel_call_modular_save_post environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) critical sem_pend_save_rely
    sg call mask saved before |--
  q_pend_save_output (QueuePendAcquirePhase pe eid observed)
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg call mask saved before.
Proof.
  intros * Hvalid Hpre.
  unfold kernel_call_modular_save_post; Intros returned acquired.
  assert (Hsave : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call returned mask saved before acquired) by tauto.
  assert (Hnormal : kernel_call_normal_return call before returned acquired) by tauto.
  assert (Hrely : sem_pend_save_rely sg before acquired) by tauto.
  pose proof (q_pend_modular_save_acquire_observation environment critical sg call returned
    pe eid observed mask saved before acquired Hvalid Hpre Hsave Hnormal Hrely) as Hphase.
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_restore_input_masked_world
    environment critical saved_local sg returned saved acquired acquired)).
  sep_apply_l_atomic (proj2 (q_pend_masked_frame_owned
    environment critical saved_local sg returned saved acquired acquired)).
  unfold q_pend_save_output; Exists returned acquired; entailer!.
Qed.

Lemma q_pend_modular_save_resume_output : forall environment critical saved_local sg original initial_mask
  initial observed eid timeout waiting call mask saved before,
  q_pend_save_phase_pre
    (QueuePendResumePhase (QueuePendWaitPhase original initial_mask initial observed eid timeout waiting))
    (Some environment) critical sg call mask before ->
  kernel_call_modular_save_post environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) critical sem_pend_save_rely
    sg call mask saved before |--
  q_pend_save_output
    (QueuePendResumePhase (QueuePendWaitPhase original initial_mask initial observed eid timeout waiting))
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg call mask saved before.
Proof.
  intros * [Hmask [[owned [Howned Hclients]] Hselected]]; injection Howned as <-.
  unfold kernel_call_modular_save_post; Intros returned acquired.
  assert (Hsave : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call returned mask saved before acquired) by tauto.
  assert (Hhistory : sem_pend_modular_call_history environment critical sg call before returned acquired)
    by (split; [exact (proj1 Hsave)|tauto]).
  assert (Hrely : sem_pend_save_rely sg before acquired) by tauto.
  pose proof (q_pend_wait_selected_modular_return environment critical sg original initial observed eid
    timeout waiting call before returned acquired (proj1 Hclients) Hselected Hhistory Hrely) as Hselected'.
  pose proof (proj2 (proj2 (proj2 (proj2 Hsave)))) as Hsaved.
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_restore_input_masked_world
    environment critical saved_local sg returned saved acquired acquired)).
  sep_apply_l_atomic (proj2 (q_pend_masked_frame_owned
    environment critical saved_local sg returned saved acquired acquired)).
  unfold q_pend_save_output; Exists returned acquired; entailer!.
  split; [exact Hhistory|]. split; [exact Hsaved|]. split; [eauto|exact Hselected'].
Qed.

Lemma q_pend_modular_save_unowned_acquire_output : forall external platform port critical saved_local
  sg call returned pe eid observed mask saved before acquired,
  UCOS2_state_inv sg before ->
  q_pend_save_phase_pre (QueuePendAcquirePhase pe eid observed) None critical sg call mask before ->
  kernel_call_save_source external port critical sg call returned mask saved before acquired ->
  kernel_call_normal_return call before returned acquired ->
  critical_region_masked platform critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) saved acquired ** os_sched_context_resources external returned **
    UCOS2_inv sg acquired ** unmap_table_rep sg |--
  q_pend_save_output (QueuePendAcquirePhase pe eid observed)
    external platform None critical saved_local sg call mask saved before.
Proof.
  intros * Hvalid [Hinput [Hprefix Hadmit]] Hsave Hnormal.
  destruct (q_pend_save_acquire_facts _ _ _ _ _ _ _ _ _ _ _ _ _
    Hvalid Hinput Hprefix Hsave) as [current Hfacts].
  pose proof Hfacts as [Hinterval [Hvalid' [Hsaved [Hlookup [Hcurrent [Htype [Htype' Hgen]]]]]]].
  assert (Hphase : q_pend_save_phase_observation (QueuePendAcquirePhase pe eid observed)
    external None critical sg call returned mask saved before acquired).
  { split; [exists port; split; [exact (proj1 Hsave)|exact Hnormal]|].
    split; [exact Hsaved|]. exists current; split; [exact Hfacts|].
    intros queue Hfields Hempty.
    destruct (q_pend_empty_acquire_owned None critical sg call pe before eid acquired current queue
      Hadmit Hprefix Hinterval Hcurrent Htype' Hfields Hempty) as [owned [Howned _]]; discriminate. }
  pose proof (proj1 Hnormal) as [Hi [Ho Hs]].
  unfold q_pend_save_output; Exists returned acquired.
  unfold q_pend_masked_frame, sem_pend_optional_continuation_resources; rewrite Hi, Ho; entailer!.
Qed.

Lemma q_pend_modular_restore_return_output : forall environment critical saved_local rely sg call mask released,
  kernel_call_modular_restore_post environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) critical rely
    sg call mask released |--
  q_pend_restore_output None environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg call mask released.
Proof.
  intros; unfold kernel_call_modular_restore_post; Intros returned current.
  assert (Hhistory : sem_pend_modular_call_history environment critical sg call released returned current)
    by (unfold sem_pend_modular_call_history; tauto).
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_save_input_closed_world
    environment critical saved_local sg returned mask current)).
  sep_apply_l_atomic (proj2 (sem_pend_continuation_save_input_owned
    environment critical saved_local sg returned mask current)).
  unfold q_pend_restore_output; Exists returned current; entailer!.
Qed.

Lemma q_pend_modular_restore_wait_output : forall environment critical saved_local sg original initial_mask
  initial observed eid timeout waiting call mask released,
  kernel_tcb_stack_field_layout sg -> UCOS2_state_inv sg released ->
  q_pend_sched_clients environment critical ->
  q_pend_restore_phase_pre (QueuePendWaitPhase original initial_mask initial observed eid timeout waiting)
    (Some environment) critical sg call mask released ->
  kernel_call_modular_restore_post environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) critical sem_pend_blocking_rely
    sg call mask released |--
  q_pend_restore_output (Some (QueuePendWaitPhase original initial_mask initial observed eid timeout waiting))
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg call mask released.
Proof.
  intros * Hlayout Hvalid Hclients [Hmask [Hwait Hentry]].
  unfold kernel_call_modular_restore_post; Intros returned current.
  assert (Hhistory : sem_pend_modular_call_history environment critical sg call released returned current)
    by (unfold sem_pend_modular_call_history; tauto).
  assert (Hrely : sem_pend_blocking_rely sg released current) by tauto.
  pose proof (q_pend_wait_at_modular_return environment critical sg original initial observed eid timeout
    waiting call released returned current (proj1 Hclients) Hvalid Hwait Hhistory) as Hwait'.
  pose proof (sem_pend_wait_sched_entry_modular_return environment critical sg call released returned current
    Hlayout Hvalid (proj1 (proj2 (proj2 Hentry))) Hentry Hhistory Hrely) as Hentry'.
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_save_input_closed_world
    environment critical saved_local sg returned mask current)).
  sep_apply_l_atomic (proj2 (sem_pend_continuation_save_input_owned
    environment critical saved_local sg returned mask current)).
  assert (Hphase : q_pend_restore_phase_pre
    (QueuePendWaitPhase original initial_mask initial observed eid timeout waiting)
    (Some environment) critical sg returned mask current) by (unfold q_pend_restore_phase_pre; auto).
  assert (Howned : exists owned, Some environment = Some owned /\ q_pend_sched_clients owned critical)
    by (exists environment; auto).
  unfold q_pend_restore_output; Exists returned current; entailer!.
Qed.

Lemma q_pend_modular_restore_unowned_output : forall external platform port critical saved_local
  sg call returned mask released current,
  kernel_resumption_task_source_trace external port critical.(critical_region_clients) sg
    call.(os_sched_call_invocation) None call.(os_sched_call_origin) released false
    returned.(os_sched_call_origin) current ->
  kernel_call_normal_return call released returned current ->
  mutex_query_closed platform critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) mask current ** os_sched_context_resources external returned ** unmap_table_rep sg |--
  q_pend_restore_output None external platform None critical saved_local sg call mask released.
Proof.
  intros * Htrace Hnormal; pose proof (proj1 Hnormal) as [Hi [Ho Hs]].
  assert (Hhistory : q_pend_call_history external None critical sg call released returned current)
    by (exists port; auto).
  unfold q_pend_restore_output; Exists returned current.
  unfold sem_pend_continuation_save_input, sem_pend_optional_continuation_resources.
  rewrite Hi, Ho; entailer!.
Qed.
