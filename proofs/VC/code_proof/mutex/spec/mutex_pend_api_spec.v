Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_pend_call_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_pend_wait_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_pend_caller_field_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_pend_entry_source_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_pend_entry_return_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_pend_tail_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_accept_modular_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_idle_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.kernel_runtime_inv.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** A local annotation fact is logically pure and has empty footprint.
    QCP can use this spatial carrier to infer ghost parameters without
    leaving the arbitrary heap permitted by standalone [coq_prop].
    Public/callee resources and their internal pure conjunctions are
    unchanged. *)
Definition mutex_pend_fact (P : Prop) : Assertion := coq_prop P && emp.

(** The caller protects the observed handle up to this invocation's first
    protected observation. The initial world is fixed here: this is not
    a requirement that every registered client preserve the handle from
    every state, in particular from the later blocked checkpoint.
    Applications must establish this lifetime protocol; Save itself does
    not supply it. The stronger non-deleting client protocol is one
    sufficient instance, proved below. *)
Definition mutex_pend_entry_handle_protocol critical sg invocation before eid observed : Prop :=
  forall entry,
    critical_region_interval critical sg invocation before entry ->
    exists current, mutex_accept_lookup entry eid current /\
      current.(eventGeneration) = observed.(eventGeneration) /\
      current.(eventType) = observed.(eventType).

Lemma mutex_pend_entry_handle_from_client_protocol :
  forall critical sg invocation before eid observed,
  mutex_accept_handle_protocol critical sg invocation eid ->
  UCOS2_state_inv sg before -> mutex_accept_lookup before eid observed ->
  mutex_pend_entry_handle_protocol critical sg invocation before eid observed.
Proof.
  intros critical sg invocation before eid observed Hclients Hvalid Hlookup entry Hinterval.
  eapply mutex_accept_handle_interval_preserves_identity; eassumption.
Qed.

(** The original ordered guard domain, including NULL and recycled FREE
    slots. The handle lifetime protocol is needed only until the first
    protected observation, never throughout the blocking interval. *)
Definition mutex_pend_api_input critical sg invocation pe before eid observed : Prop :=
  pe = 0 \/ (pe <> 0 /\ pe = event_addr sg eid /\ valid_event_id sg eid /\
    sem_query_public_slot before eid observed /\
    (event_slot_type_value before.(EventState) eid = 4 ->
      before.(IntrState).(intNesting) <= 0 -> before.(IntrState).(lockNesting) <= 0 ->
      mutex_pend_entry_handle_protocol critical sg invocation before eid observed)).

Definition mutex_pend_api_prefix pe before eid : Prop :=
  mutex_pend_precritical_error pe (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None.

(** Ordinary application entry. Non-Idle identity is the explicitly
    selected empty-Idle-hook scope; priority is NOT assumed here. The
    actual initialized Idle slot and task invariant derive its priority
    consequence at the later EventTaskWait cut. *)
Definition mutex_pend_task_entry idle call state : Prop :=
  kernel_call_task_source call state /\ state.(SchedState).(isRunning) = true /\
  mutex_call_non_idle idle call.(os_sched_call_origin) /\
  exists node,
    sched_current_ready_at state.(TskState) state.(SchedState)
      call.(os_sched_call_stack).(stackLeaseSlot) node /\
    node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) /\
    node.(eventPtr) = None /\ node.(eventMultiWaitEvents) = [] /\ node.(tcbFlagNode) = 0.

Definition mutex_pend_api_admission (environment : option TaskStackCallEnvironment)
  idle call pe before eid : Prop :=
  mutex_pend_api_prefix pe before eid ->
  (exists owned, environment = Some owned) /\ kernel_call_task_source call before /\
  mutex_call_non_idle idle call.(os_sched_call_origin).

(** Source-variant obligation 3 permits immediate nested acquisition, but
    an owner must not register another Event wait. The ordinary ready
    call point is likewise consumed only at the actual busy observation.
    This is a source/application call protocol, not a new postcondition
    of Save or a global restriction on the early/immediate return arms. *)
Definition mutex_pend_wait_call_protocol environment critical sg idle original before eid : Prop :=
  forall entered entry event mutex,
    sem_pend_modular_call_history environment critical sg original before entered entry ->
    entry.(EventState).(inUsedEventStates) eid = Some event ->
    event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
    mutex.(mfOwner) <> None ->
    mutex_pend_task_entry idle original before /\
    kernel_running_idle_ready sg before /\
    kernel_call_stack_available original before /\
    task_holds_no_mutex entry.(EventState) entered.(os_sched_call_stack).(stackLeaseSlot).

Definition mutex_pend_api_scope environment critical sg idle original pe before eid : Prop :=
  mutex_pend_api_prefix pe before eid ->
  mutex_owner_event_unlinked before.(TskState) before.(EventState) /\
  mutex_idle_slot before.(TskState) idle /\ mutex_idle_excluded idle before.(EventState) /\
  mutex_owner_region_source_protocol critical sg /\ mutex_idle_region_source_protocol critical sg idle /\
  (forall action, critical.(critical_region_clients) action ->
    mutex_pend_entry_source_client original.(os_sched_call_invocation)
      original.(os_sched_call_stack).(stackLeaseSlot)
      original.(os_sched_call_stack).(stackLeaseGeneration) action) /\
  (forall action, critical.(critical_region_clients) action -> mutex_pend_projected_source_client action) /\
  (forall owned, environment = Some owned ->
    mutex_pend_wait_call_protocol owned critical sg idle original before eid).

Definition mutex_pend_masked_frame environment critical saved_local sg call saved acquired current : Assertion :=
  coq_prop (task_stack_live_coverage current.(TskState) (task_stack_call_active_key call)) &&
  (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved acquired **
   os_sched_context_resources environment.(task_stack_call_external) call **
   task_tcb_init_continuation_capsules environment saved_local current ** unmap_table_rep sg).

Definition mutex_pend_first_snapshot environment critical sg idle original entered mask saved
  before entry eid observed current mutex tid caller : Prop :=
  sem_pend_modular_call_history environment critical sg original before entered entry /\
  interrupt_saved_value mask saved /\ sem_pend_save_rely sg before entry /\
  mutex_accept_acquire_facts critical sg original.(os_sched_call_invocation) eid mask saved
    before entry observed current /\
  kernel_call_task_source entered entry /\ mutex_call_non_idle idle entered.(os_sched_call_origin) /\
  mutex_owner_event_unlinked entry.(TskState) entry.(EventState) /\
  mutex_idle_slot entry.(TskState) idle /\ mutex_idle_excluded idle entry.(EventState) /\
  mutex_accept_event_snapshot sg entry eid current mutex
    (encode_event_cnt_value current) (encode_event_ptr_value sg current) /\
  mutex_accept_current_task sg entry tid caller.

(** The C annotation uses the encoded byte, keeping macro identifiers out
    of the Rocq error-code constructor namespace. *)
Definition mutex_pend_first_acquired sg eid timeout entry code checkpoint : Prop :=
  exists error, code = encode_os_err_code error /\
    mutex_pend_first_critical sg eid timeout entry (MutexPendAcquired error) checkpoint.

Definition mutex_pend_inherited_snapshot sg entry eid current mutex tid caller inherited : Prop :=
  exists owner,
    mutex.(mfOwner) = Some owner /\
    ((mutex.(mfPCP) = sg.(osPrioMutexCeilDis) /\ inherited = entry) \/
     (mutex.(mfPCP) <> sg.(osPrioMutexCeilDis) /\ exists node base,
       entry.(TskState).(inUsedTaskStates) owner = Some node /\
       task_base_priority sg entry.(TskState).(prioTbl) owner base /\
       mutex_pend_inherit_step sg entry owner node base caller.(curPrio) mutex.(mfPCP) inherited)) /\
    mutex_pend_wait_entry sg inherited eid current tid caller.

Definition mutex_pend_inheritance_output sg entry eid current mutex tid caller : Assertion :=
  EX inherited, coq_prop (mutex_pend_inherited_snapshot sg entry eid current mutex tid caller inherited) &&
    UCOS2_inv sg inherited.

Definition mutex_pend_owner_snapshot sg entry eid current mutex tid caller owner node : Prop :=
  mutex_pend_wait_entry sg entry eid current tid caller /\
  current.(mutexFields) = Some mutex /\ mutex.(mfOwner) = Some owner /\
  entry.(TskState).(inUsedTaskStates) owner = Some node /\
  owner <> tid /\ node.(eventPtr) = None /\
  (entry.(SchedState).(isRunning) = true -> node.(curPrio) <> sg.(osLowestPrio)) /\
  mutex_owner_event_unlinked entry.(TskState) entry.(EventState).

Definition mutex_pend_owner_fields_rest pointer image : Assertion :=
  tcb64_fields_rep pointer (remove TCBField_eq_dec TCBEventPtr mutex_priority_unchanged_fields) image.

(** This is a finite composition of the real call relations, not another
    scheduler history or a promise of eventual wake/return. In particular
    [after] is the world returned by the final Restore. The old Mutex may
    have been deleted/reused while blocked; only the timeout branch of
    [mutex_pend_resume_critical] requires its real linked ECB. *)
Definition mutex_pend_api_execution environment critical sg original eid timeout
  before code after : Prop :=
  exists entered entry start checkpoint returned,
    sem_pend_modular_call_history environment critical sg original before entered entry /\
    mutex_pend_first_critical sg eid timeout entry start checkpoint /\
    match start with
    | MutexPendAcquired result =>
        code = encode_os_err_code result /\
        sem_pend_modular_call_history environment critical sg entered checkpoint returned after
    | MutexPendWaiting tid generation =>
        tid = original.(os_sched_call_stack).(stackLeaseSlot) /\
        generation = original.(os_sched_call_stack).(stackLeaseGeneration) /\
        exists released unmasked scheduled selected resumed resume_entry result cleaned,
          sem_pend_modular_call_history environment critical sg entered checkpoint released unmasked /\
          mutex_pend_sched_return (Some environment) critical sg released unmasked scheduled selected /\
          sem_pend_modular_call_history environment critical sg scheduled selected resumed resume_entry /\
          mutex_pend_resume_critical sg eid resume_entry result cleaned /\
          code = encode_os_err_code result /\
          sem_pend_modular_call_history environment critical sg resumed cleaned returned after
    end.

Definition mutex_pend_api_program (environment : option TaskStackCallEnvironment)
  critical sg original pe eid timeout : program UCOS2_Verify_State Z :=
  fun before code after =>
    match mutex_pend_precritical_error pe (event_slot_type_value before.(EventState) eid)
      before.(IntrState).(intNesting) before.(IntrState).(lockNesting) with
    | Some error => code = encode_os_err_code error /\ after = before
    | None => match environment with
        | Some owned => mutex_pend_api_execution owned critical sg original eid timeout before code after
        | None => False
        end
    end.

Definition mutex_pend_api_post external platform environment critical saved_local
  sg original mask pe eid timeout perr before X : Assertion :=
  EX returned after code,
    coq_prop (mutex_pend_api_program environment critical sg original pe eid timeout before code after /\
      safeExec (LastSeen after) (@StateRelMonad.ret (UCOS2_Verify_State -> Prop) Z code) X /\
      kernel_stack_call_same_call returned original) &&
    (perr # UChar |-> code **
      sem_pend_continuation_save_input external platform environment critical saved_local sg returned mask after **
      unmap_table_rep sg).

Lemma mutex_pend_api_early_result : forall environment critical sg original pe eid timeout before error,
  mutex_pend_precritical_error pe (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = Some error ->
  mutex_pend_api_program environment critical sg original pe eid timeout before
    (encode_os_err_code error) before.
Proof. intros; unfold mutex_pend_api_program; rewrite H; auto. Qed.

Lemma mutex_pend_api_safe_return :
  forall environment critical sg original pe eid timeout before code after X,
  mutex_pend_api_program environment critical sg original pe eid timeout before code after ->
  safeExec (LastSeen before)
    (bind (atomic_cmd (mutex_pend_api_program environment critical sg original pe eid timeout))
      sem_query_observe_error) X ->
  safeExec (LastSeen after) (@StateRelMonad.ret (UCOS2_Verify_State -> Prop) Z code) X.
Proof.
  intros * Hsem Hexec.
  assert (Hatomic : hs_eval
    (atomic_cmd (mutex_pend_api_program environment critical sg original pe eid timeout))
    (LastSeen before) (LastSeen after) code).
  { unfold hs_eval, LastSeen, atomic_cmd; intros P HP.
    exists (RTrans_Abs after); split; [|intro state; split; trivial].
    exists before, after; split; [apply HP; exact I|].
    split; [exact Hsem|intro state; split; trivial]. }
  pose proof (highstepbind_derive _ _ _ code (LastSeen after) Hatomic X Hexec) as Hobs.
  eapply (highstependret_derive (sem_query_observe_error code) (LastSeen after) code
    (fun _ => LastSeen after)); [|exact Hobs].
  unfold hs_eval, LastSeen; intros P HP; exists P; split; [split; reflexivity|exact HP].
Qed.

Lemma mutex_pend_task_entry_sem_stage : forall sg idle call state,
  UCOS2_state_inv sg state -> mutex_idle_slot state.(TskState) idle ->
  mutex_pend_task_entry idle call state -> sem_pend_task_call_stage sg call state.
Proof.
  intros sg idle call state Hvalid Hslot [Hsource [Hrunning [Hnonidle
    [node [Hcurrent [Hgeneration [Hptr [Hmulti Hflag]]]]]]]].
  split; [exact Hsource|]. split; [exact Hrunning|]. exists node.
  split; [exact Hcurrent|]. split; [exact Hgeneration|]. split; [|auto].
  destruct Hcurrent as [Hnode [Hcur Hready]].
  eapply mutex_non_idle_priority; [exact (proj1 (proj2 Hvalid))| |exact Hnode|].
  - eapply mutex_running_idle_slot_task; eassumption.
  - eapply mutex_call_source_non_idle; eassumption.
Qed.

(** These are projections of the shared modular C-call contract. The
    completed-call rely below is an existing C-environment obligation,
    not an ARM promise. The actual source trace is retained in both posts.
    The blocking Restore never gains a ready-caller premise. *)
Definition mutex_pend_api_save_output environment critical saved_local sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (sem_pend_modular_call_history environment critical sg original before returned acquired /\
      interrupt_saved_value mask saved /\ sem_pend_save_rely sg before acquired /\
      (UCOS2_state_inv sg before -> task_tcb_init_stack_source_preserved original before acquired)) &&
    (task_tcb_init_continuation_restore_input environment critical saved_local sg returned saved acquired acquired **
      unmap_table_rep sg).

Definition mutex_pend_api_restore_rely (blocking : bool) :=
  if blocking then sem_pend_blocking_rely else sem_pend_save_rely.

Definition mutex_pend_api_restore_input (_ : bool) environment critical saved_local
  sg call saved acquired released : Assertion :=
  task_tcb_init_continuation_restore_input environment critical saved_local sg call saved acquired released **
    unmap_table_rep sg.

Definition mutex_pend_api_restore_output blocking environment critical saved_local
  sg original saved released : Assertion :=
  EX returned current,
    coq_prop (sem_pend_modular_call_history environment critical sg original released returned current /\
      mutex_pend_api_restore_rely blocking sg released current) &&
    (task_tcb_init_continuation_save_input environment critical saved_local sg returned
       (armv7a_irq_fiq_mask saved) current ** unmap_table_rep sg).

Lemma mutex_pend_api_modular_save_output : forall environment critical saved_local sg original mask saved before,
  kernel_call_modular_save_post environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) critical sem_pend_save_rely
    sg original mask saved before |--
  mutex_pend_api_save_output environment critical saved_local sg original mask saved before.
Proof.
  intros; unfold kernel_call_modular_save_post; Intros returned acquired.
  assert (Hsave : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original returned mask saved before acquired) by tauto.
  assert (Hnormal : kernel_call_normal_return original before returned acquired) by tauto.
  destruct Hsave as [Hsource [Hi [Ho [Hs Hsaved]]]].
  assert (Hhistory : sem_pend_modular_call_history environment critical sg original before returned acquired)
    by (split; assumption).
  assert (Hpreserved : UCOS2_state_inv sg before -> task_tcb_init_stack_source_preserved original before acquired).
  { intro Hvalid; eapply task_tcb_init_stack_registered_source_preserved;
      [exact Hvalid|exact (proj1 Hnormal)|exact Hsource]. }
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_restore_input_masked_world
    environment critical saved_local sg returned saved acquired acquired)).
  unfold mutex_pend_api_save_output; Exists returned acquired; entailer!.
Qed.

Lemma mutex_pend_api_modular_restore_output : forall blocking environment critical saved_local
  sg original saved released,
  kernel_call_modular_restore_post environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) critical
    (mutex_pend_api_restore_rely blocking) sg original (armv7a_irq_fiq_mask saved) released |--
  mutex_pend_api_restore_output blocking environment critical saved_local sg original saved released.
Proof.
  intros; unfold kernel_call_modular_restore_post; Intros returned current.
  assert (Hhistory : sem_pend_modular_call_history environment critical sg original released returned current)
    by (unfold sem_pend_modular_call_history; tauto).
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_save_input_closed_world
    environment critical saved_local sg returned (armv7a_irq_fiq_mask saved) current)).
  unfold mutex_pend_api_restore_output; Exists returned current; entailer!.
Qed.
