Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_wait_sched_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cleanup_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** A logical index for the two literal Save calls and the three Restore
    calls in OSSemPend. It is neither a C field nor a new platform state.
    The waiting index keeps the very first wait and invocation throughout
    Restore, Scheduler and Save, so a different legal wait cannot be used
    to justify this call's eventual result. *)
Inductive SemPendCallPhase : Type :=
| SemPendAcquirePhase (pevent : Z) (eid : EventID) (observed : OSEventAbstractState)
| SemPendWaitPhase (original : OsSchedCallContext) (mask : Z)
    (before : UCOS2_Verify_State) (observed : OSEventAbstractState)
    (eid : EventID) (timeout : Z) (waiting : UCOS2_Verify_State)
| SemPendReturnPhase.

Definition sem_pend_has_stack (environment : option TaskStackCallEnvironment) : Prop :=
  exists owned, environment = Some owned.

Lemma sem_pend_observed_zero_count_owned : forall environment critical sg original returned mask saved
  pevent before acquired eid observed current,
  sem_pend_runtime_nonblocking critical sg original environment pevent before eid ->
  sem_pend_precritical_error pevent (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  sem_pend_optional_acquire_observation environment critical sg original returned mask saved
    before acquired eid observed current ->
  encode_event_cnt_value current = 0 -> sem_pend_has_stack environment.
Proof.
  intros [owned|] critical sg original returned mask saved pevent before acquired eid observed current
    Hnonblocking Hclear Hacquire Hzero; [exists owned; reflexivity|].
  destruct Hacquire as [Hsame [Hinterval [_ [_ [_ [Hlookup [_ [Htype _]]]]]]]].
  specialize (Hnonblocking eq_refl Hclear acquired current Hinterval Hlookup Htype); lia.
Qed.

Lemma sem_pend_observed_cleanup_return_merge : forall environment critical sg context mask before observed eid
  pevent timeout error cleaning tid node,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  sem_pend_observed_cleanup_origin environment critical sg context mask before observed eid timeout error cleaning tid node ->
  sem_pend_cleanup_cells sg cleaning tid node |--
  coq_prop (sem_pend_checkpoint_result environment critical sg context pevent timeout before error
    (event_pend_cleanup_state sg false cleaning tid node)) &&
  UCOS2_inv sg (event_pend_cleanup_state sg false cleaning tid node).
Proof.
  intros * Hnonnull Haddress Hid Hslot Hordered Horigin.
  pose proof (sem_pend_observed_cleanup_result environment critical sg context mask before observed eid
    pevent timeout error cleaning tid node Hnonnull Haddress Hid Hslot Hordered Horigin) as Hresult.
  unfold sem_pend_cleanup_cells.
  sep_apply_l_atomic (sem_pend_cleanup_merge sg cleaning tid node (proj1 Horigin)); entailer!.
Qed.

Lemma sem_pend_observed_timeout_remove_cleanup : forall environment critical sg context mask before observed eid
  timeout resumed tid old current,
  sem_pend_observed_resume_origin environment critical sg context mask before observed eid timeout resumed tid old ->
  old.(statPend) = PendTimeout -> mutex_query_lookup resumed eid current -> event_object_layout_prop sg eid ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  event_task_remove_post (task_slot_addr sg tid)
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl")
    (old.(curPrio) / 8) (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
    (encode_event_wait_tbl_at_or current.(waitList) resumed.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) resumed.(TskState)) **
  sem_pend_remove_call_frame sg resumed eid current tid old |--
  coq_prop (sem_pend_observed_cleanup_origin environment critical sg context mask before observed eid timeout 10
    (event_task_remove_state resumed eid current tid old) tid (task_set_event_ptr old None)) &&
  UCOS2_inv sg (event_task_remove_state resumed eid current tid old).
Proof.
  intros * Horigin Htimeout Hlookup Hlayout.
  pose proof (sem_pend_observed_resume_cleanup_timeout environment critical sg context mask before observed eid
    timeout resumed tid old current Horigin Htimeout Hlookup) as Hcleanup.
  sep_apply_l_atomic (sem_pend_remove_call_merge sg resumed eid current tid old
    (proj1 Horigin) Htimeout Hlookup Hlayout); entailer!.
Qed.

Definition sem_pend_wait_at environment critical sg original mask before observed eid timeout
  waiting call current : Prop :=
  exists owned,
    environment = Some owned /\ kernel_stack_call_same_call call original /\
    sem_pend_observed_wait_history environment critical sg original mask before observed eid timeout waiting /\
    sem_pend_wait_source_history owned critical sg original eid
      original.(os_sched_call_stack).(stackLeaseGeneration) waiting current.

Definition sem_pend_wait_selected_at environment critical sg original mask before observed eid timeout
  waiting call current : Prop :=
  sem_pend_wait_at environment critical sg original mask before observed eid timeout waiting call current /\
  exists node, sem_pend_resume_entry sg current eid original.(os_sched_call_stack).(stackLeaseSlot) node.

Lemma sem_pend_wait_at_waiting : forall environment critical sg original mask before observed eid timeout
  waiting call,
  sem_pend_has_stack environment ->
  kernel_stack_call_same_call call original ->
  sem_pend_observed_wait_history environment critical sg original mask before observed eid timeout waiting ->
  sem_pend_wait_at environment critical sg original mask before observed eid timeout waiting call waiting.
Proof.
  intros * [owned Howned] Hsame Hhistory.
  exists owned; split; [exact Howned|]. split; [exact Hsame|]. split; [exact Hhistory|constructor].
Qed.

Lemma sem_pend_wait_selected_resume_origin : forall environment critical sg original mask before observed
  eid timeout waiting call current,
  sem_pend_wait_selected_at environment critical sg original mask before observed eid timeout waiting call current ->
  exists node,
    sem_pend_observed_resume_origin environment critical sg original mask before observed eid timeout current
      original.(os_sched_call_stack).(stackLeaseSlot) node.
Proof.
  intros * [[owned [Howned [Hsame [Hhistory Hpath]]]] [node Hresume]].
  destruct (sem_pend_observed_wait_history_waiter _ _ _ _ _ _ _ _ _ _ Hhistory)
    as [first [Hfirst Hcontinuation]].
  destruct (sem_pend_wait_source_history_preserves_waiter _ _ _ _ _ _ _ _ Hpath
    first Hfirst Hcontinuation) as [last [Hlast Hlast_continuation]].
  pose proof Hresume as [_ [_ [Hnode _]]].
  assert (last = node) by congruence; subst last.
  exists node; split; [exact Hresume|].
  pose proof Hhistory as [_ [[Horigin _] _]].
  split.
  - rewrite (proj1 Hlast_continuation); exact Horigin.
  - exists owned, waiting; split; [exact Howned|]. split; [exact Hhistory|].
    rewrite (proj1 Hlast_continuation); exact Hpath.
Qed.

Definition sem_pend_save_phase_pre phase environment critical sg call mask before : Prop :=
  match phase with
  | SemPendAcquirePhase pevent eid observed =>
      sem_pend_call_input critical sg call.(os_sched_call_invocation) pevent before eid observed /\
      pevent <> 0 /\
      sem_pend_context_error (event_slot_type_value before.(EventState) eid)
        before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None /\
      sem_pend_observed_admission environment critical sg call pevent before eid /\
      sem_pend_runtime_nonblocking critical sg call environment pevent before eid
  | SemPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      mask = initial_mask /\
      sem_pend_wait_selected_at environment critical sg original initial_mask initial observed eid timeout
        waiting call before
  | SemPendReturnPhase => False
  end.

Definition sem_pend_save_phase_observation phase environment critical sg call returned mask saved before acquired : Prop :=
  match phase with
  | SemPendAcquirePhase pevent eid observed =>
      exists current,
        sem_pend_optional_acquire_observation environment critical sg call returned mask saved
          before acquired eid observed current /\
        (encode_event_cnt_value current = 0 ->
          sem_pend_task_call_stage sg call acquired /\
          sem_pend_optional_blocking_call_stage environment sg call acquired)
  | SemPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      sem_pend_wait_selected_at environment critical sg original initial_mask initial observed eid timeout
        waiting returned acquired
  | SemPendReturnPhase => False
  end.

Definition sem_pend_phase_save_input phase external platform environment critical sg call mask before : Assertion :=
  coq_prop (sem_pend_save_phase_pre phase environment critical sg call mask before) &&
  sem_pend_stack_save_input external platform environment critical sg call mask before.

Definition sem_pend_phase_save_output phase external platform environment critical sg call mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (sem_pend_stack_save_observation critical sg call returned environment mask saved before acquired /\
      sem_pend_save_phase_observation phase environment critical sg call returned mask saved before acquired) &&
    (critical_region_masked platform critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) saved acquired **
     os_sched_context_resources external returned ** UCOS2_inv sg acquired **
     sem_pend_optional_stack_resources external platform environment returned acquired).

Definition sem_pend_restore_phase_pre phase environment critical sg call mask checkpoint : Prop :=
  match phase with
  | SemPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      mask = initial_mask /\
      sem_pend_wait_at environment critical sg original initial_mask initial observed eid timeout waiting call checkpoint /\
      sem_pend_wait_sched_entry sg call checkpoint
  | SemPendReturnPhase => True
  | SemPendAcquirePhase _ _ _ => False
  end.

Definition sem_pend_phase_restore_input phase external platform environment critical sg call mask saved entry checkpoint : Assertion :=
  coq_prop (sem_pend_restore_phase_pre phase environment critical sg call mask checkpoint) &&
  sem_pend_stack_restore_input external platform environment critical sg call mask saved entry checkpoint.

Definition sem_pend_phase_restore_output phase external platform environment critical sg call mask checkpoint : Assertion :=
  EX returned current,
    coq_prop (sem_pend_optional_restore_history external platform environment critical sg call checkpoint returned current /\
      sem_pend_stack_restore_observation sg call returned environment checkpoint current /\
      sem_pend_restore_phase_pre phase environment critical sg returned mask current) &&
    (mutex_query_closed platform critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) mask current **
     os_sched_context_resources external returned **
     sem_pend_optional_stack_resources external platform environment returned current).

Lemma sem_pend_phase_restore_return_output : forall external platform environment critical sg call mask checkpoint,
  sem_pend_stack_restore_source_output external platform environment critical sg call mask checkpoint --||--
  sem_pend_phase_restore_output SemPendReturnPhase external platform environment critical sg call mask checkpoint.
Proof.
  intros; unfold sem_pend_stack_restore_source_output, sem_pend_phase_restore_output,
    sem_pend_restore_phase_pre; split; Intros returned current; Exists returned current; entailer!.
Qed.

Definition sem_pend_phase_sched_input phase external platform environment critical sg call mask before : Assertion :=
  match phase with
  | SemPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      coq_prop (mask = initial_mask /\
        sem_pend_wait_at environment critical sg original initial_mask initial observed eid timeout waiting call before) &&
      sem_pend_stack_sched_input external platform environment sg call mask before
  | _ => coq_prop False && emp
  end.

Definition sem_pend_phase_sched_output phase external platform environment critical sg call mask
  (before : UCOS2_Verify_State) : Assertion :=
  match phase with
  | SemPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      EX returned current,
        coq_prop (kernel_stack_call_same_call returned call /\
          sem_pend_wait_selected_at environment critical sg original initial_mask initial observed eid timeout
            waiting returned current) &&
        (sem_pend_stack_save_input external platform environment critical sg returned mask current **
          unmap_table_rep sg)
  | _ => coq_prop False && emp
  end.

(** The source producer must supply the same checked Restore edge and its
    field preservation. This lemma appends that edge to the existing wait;
    it cannot manufacture a path from an unrelated ready task. *)
Lemma sem_pend_wait_at_restore_source : forall owned critical sg original mask before observed eid timeout
  waiting call checkpoint returned current,
  sem_pend_wait_at (Some owned) critical sg original mask before observed eid timeout waiting call checkpoint ->
  kernel_call_restore_history owned critical sg call checkpoint returned current ->
  (forall node,
    checkpoint.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
    sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) node ->
    exists next,
      current.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some next /\
      sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) next) ->
  sem_pend_wait_at (Some owned) critical sg original mask before observed eid timeout waiting returned current.
Proof.
  intros * [environment [Howned [Hsame [Hwait Hpath]]]] Hrestore Hfields.
  inversion Howned; subst environment.
  pose proof (kernel_call_restore_history_same_call _ _ _ _ _ _ _ Hrestore) as Hreturned.
  exists owned; split; [reflexivity|]. split.
  - unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence.
  - split; [exact Hwait|]. eapply SemPendWaitSourceTrans; [exact Hpath|].
    eapply SemPendWaitSourceRestore; eassumption.
Qed.

(** An actual selected post, reached by the same source path, supplies the
    current ready entry. The registered trace proof supplies the wait
    continuation before this final selection. *)
Lemma sem_pend_wait_at_selected_source : forall owned critical sg original mask before observed eid timeout
  waiting call current focus incoming selected node,
  sem_pend_wait_at (Some owned) critical sg original mask before observed eid timeout waiting call current ->
  incoming = original.(os_sched_call_stack) ->
  os_sched_source_selected_post owned.(task_stack_call_external) owned.(task_stack_call_platform)
    owned.(task_stack_call_port) owned.(task_stack_call_continuations)
    sg focus incoming selected node current |--
  coq_prop (sem_pend_wait_selected_at (Some owned) critical sg original mask before observed eid timeout
    waiting call current) && TT.
Proof.
  intros * Hwait Hincoming.
  pose proof Hwait as [environment [Howned [Hsame [Hhistory Hpath]]]].
  inversion Howned; subst environment.
  destruct (sem_pend_observed_wait_history_waiter _ _ _ _ _ _ _ _ _ _ Hhistory)
    as [first [Hfirst Hcontinuation]].
  destruct (sem_pend_wait_source_history_preserves_waiter _ _ _ _ _ _ _ _ Hpath
    first Hfirst Hcontinuation) as [waiter [Hnode Hcontinuation']].
  subst incoming.
  pose proof (sem_pend_selected_source_resume_entry _ _ _ owned.(task_stack_call_continuations)
    sg focus original.(os_sched_call_stack) selected node current eid
    original.(os_sched_call_stack).(stackLeaseGeneration) waiter Hnode Hcontinuation') as Hresume.
  intros heap Hheap; split; [split; [exact Hwait|exists waiter; exact (proj1 (Hresume heap Hheap))]|exact I].
Qed.

(** The canonical phase index and all pure observations are unchanged.
    Only the same already-owned continuation-local family is threaded
    through the literal Save, Restore and Scheduler calls. *)
Definition sem_pend_continuation_phase_save_input phase external platform environment critical saved_local sg call mask before : Assertion :=
  coq_prop (sem_pend_save_phase_pre phase environment critical sg call mask before) &&
  sem_pend_continuation_save_input external platform environment critical saved_local sg call mask before.

Definition sem_pend_continuation_phase_save_output phase external platform environment critical saved_local sg call mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (sem_pend_stack_save_observation critical sg call returned environment mask saved before acquired /\
      sem_pend_save_phase_observation phase environment critical sg call returned mask saved before acquired) &&
    (critical_region_masked platform critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) saved acquired **
     os_sched_context_resources external returned ** UCOS2_inv sg acquired **
     sem_pend_optional_continuation_resources external platform environment saved_local returned acquired).

Definition sem_pend_continuation_phase_restore_input phase external platform environment critical saved_local sg call mask saved entry checkpoint : Assertion :=
  coq_prop (sem_pend_restore_phase_pre phase environment critical sg call mask checkpoint) &&
  sem_pend_continuation_restore_input external platform environment critical saved_local sg call mask saved entry checkpoint.

Definition sem_pend_continuation_phase_restore_output phase external platform environment critical saved_local sg call mask checkpoint : Assertion :=
  EX returned current,
    coq_prop (sem_pend_optional_restore_history external platform environment critical sg call checkpoint returned current /\
      sem_pend_stack_restore_observation sg call returned environment checkpoint current /\
      sem_pend_restore_phase_pre phase environment critical sg returned mask current) &&
    (mutex_query_closed platform critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) mask current **
     os_sched_context_resources external returned **
     sem_pend_optional_continuation_resources external platform environment saved_local returned current).

Lemma sem_pend_continuation_phase_restore_return_output : forall external platform environment critical saved_local sg call mask checkpoint,
  sem_pend_continuation_restore_source_output external platform environment critical saved_local sg call mask checkpoint --||--
  sem_pend_continuation_phase_restore_output SemPendReturnPhase external platform environment critical saved_local sg call mask checkpoint.
Proof.
  intros; unfold sem_pend_continuation_restore_source_output, sem_pend_continuation_phase_restore_output,
    sem_pend_restore_phase_pre; split; Intros returned current; Exists returned current; entailer!.
Qed.

Definition sem_pend_continuation_phase_sched_input phase external platform environment critical saved_local sg call mask before : Assertion :=
  match phase with
  | SemPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      coq_prop (mask = initial_mask /\
        sem_pend_wait_at environment critical sg original initial_mask initial observed eid timeout waiting call before /\
        sem_pend_wait_sched_entry sg call before) &&
      sem_pend_continuation_sched_input external platform environment saved_local sg call mask before
  | _ => coq_prop False && emp
  end.

Definition sem_pend_continuation_phase_sched_output phase external platform environment critical saved_local sg call mask
  (before : UCOS2_Verify_State) : Assertion :=
  match phase with
  | SemPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      EX returned current,
        coq_prop (kernel_stack_call_same_call returned call /\
          sem_pend_wait_selected_at environment critical sg original initial_mask initial observed eid timeout
            waiting returned current) &&
        (sem_pend_continuation_save_input external platform environment critical saved_local sg returned mask current **
          unmap_table_rep sg)
  | _ => coq_prop False && emp
  end.

(** The actual blocking call consumes the common C Scheduler precondition,
    while retaining its own wait history and enabled-selection fact.
    Restore's C/RG return certificate supplies this cut at the returned
    state; the source wait is not identified with that later state. *)
Lemma sem_pend_continuation_phase_sched_call_pre : forall environment critical saved_local
  sg original initial_mask initial observed eid timeout waiting call mask state,
  sem_pend_continuation_phase_sched_input
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg call mask state |--
  coq_prop (mask = initial_mask /\
    sem_pend_wait_at (Some environment) critical sg original initial_mask initial observed
      eid timeout waiting call state /\ os_sched_selection_enabled state = true) &&
  os_sched_continuation_call_pre environment saved_local kernel_program_inv sg call mask state.
Proof.
  intros; cbn [sem_pend_continuation_phase_sched_input sem_pend_continuation_sched_input].
  unfold sem_pend_wait_sched_entry, os_sched_continuation_call_pre; entailer!.
Qed.

Lemma sem_pend_continuation_phase_save_input_emp_equiv :
  forall phase external platform environment critical sg call mask before,
  sem_pend_continuation_phase_save_input phase external platform environment critical
    (fun _ => emp) sg call mask before --||--
  sem_pend_phase_save_input phase external platform environment critical sg call mask before.
Proof.
  intros; unfold sem_pend_continuation_phase_save_input, sem_pend_phase_save_input,
    sem_pend_continuation_save_input, sem_pend_stack_save_input.
  rewrite sem_pend_optional_continuation_resources_emp_equiv; split; reflexivity.
Qed.
