Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.event_wait Ucos2Verify.lib.event Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.tick.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_wait_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_remove_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_call_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The same native registration stages as EventTaskWait/Remove, now with
    the source's PendMutex bit. In particular expiry does NOT remove the
    ECB link; a real Post/Del wake may still overwrite its pending result.
    No future return, ownership transfer, or readiness is asserted here. *)
Definition mutex_pend_wait_continuation eid generation (node : TaskAbstractState) : Prop :=
  node.(taskGeneration) = generation /\ node.(eventMultiWaitEvents) = [] /\
  node.(tcbFlagNode) = 0 /\
  ((node.(eventPtr) = Some eid /\ task_linked_wait_phase node PendMutex) \/
   (node.(eventPtr) = None /\ task_non_suspension_bits node.(stat) = 0 /\
    node.(statPend) <> PendTimeout)).

Lemma mutex_pend_wait_establishes_continuation : forall eid node timeout,
  is_effectively_ready node.(stat) node.(dly) = true ->
  node.(eventMultiWaitEvents) = [] -> node.(tcbFlagNode) = 0 ->
  mutex_pend_wait_continuation eid node.(taskGeneration)
    (task_set_event_ptr (task_prepare_event_wait node PendMutex timeout) (Some eid)).
Proof.
  intros eid node timeout Hready Hmulti Hflag.
  split; [reflexivity|]. split; [exact Hmulti|]. split; [exact Hflag|].
  left; split; [reflexivity|]. left.
  apply task_prepare_event_wait_pending_bits.
  apply task_effectively_ready_has_no_pending; exact Hready.
Qed.

Lemma mutex_pend_wait_fields_preserve_continuation : forall eid generation before after,
  sem_pend_wait_fields_equal before after ->
  mutex_pend_wait_continuation eid generation before ->
  mutex_pend_wait_continuation eid generation after.
Proof.
  intros eid generation before after [Hid [Hg [Hs [Hp [Hd [He [Hm Hf]]]]]]].
  unfold mutex_pend_wait_continuation, task_linked_wait_phase.
  rewrite Hg, Hs, Hp, Hd, He, Hm, Hf; trivial.
Qed.

Lemma mutex_pend_tick_preserves_continuation : forall eid generation node,
  mutex_pend_wait_continuation eid generation node ->
  mutex_pend_wait_continuation eid generation (tick_task_update node).
Proof.
  intros eid generation node [Hg [Hm [Hf Hphase]]].
  pose proof (tick_task_preserves_non_timeout_fields node) as Hfields; cbn zeta in Hfields.
  split; [intuition congruence|]. split; [intuition congruence|]. split; [intuition congruence|].
  destruct Hphase as [[Hptr Hlinked]|[Hptr [Hclear Hresult]]].
  - left; split; [intuition congruence|]. apply tick_preserves_linked_phase; exact Hlinked.
  - right; split; [intuition congruence|].
    unfold tick_task_update; destruct (Z.eqb node.(dly) 0); [auto|].
    destruct (Z.eqb (node.(dly) - 1) 0); [|auto].
    cbn [stat statPend].
    rewrite (task_status_single_of_mask node.(stat) None Hclear).
    destruct (task_is_suspended node.(stat)); split; reflexivity || discriminate.
Qed.

Lemma mutex_pend_wake_preserves_continuation : forall eid generation node result,
  result <> PendTimeout -> mutex_pend_wait_continuation eid generation node ->
  mutex_pend_wait_continuation eid generation (task_event_wake_single node PendMutex 0 result).
Proof.
  intros eid generation node result Hresult [Hg [Hm [Hf Hphase]]].
  split; [exact Hg|]. split; [exact Hm|]. split; [exact Hf|].
  right; split; [reflexivity|]. split; [|exact Hresult].
  destruct Hphase as [[Hptr Hlinked]|[Hptr [Hclear Hprevious]]].
  - exact (proj2 (task_event_wake_single_clears_registration node PendMutex 0 result Hlinked)).
  - change (task_non_suspension_bits (task_clear_pending_status node.(stat) PendMutex) = 0).
    rewrite task_clear_pending_status_none by exact Hclear; exact Hclear.
Qed.

Lemma mutex_pend_ready_resume_registration : forall eid generation node,
  mutex_pend_wait_continuation eid generation node ->
  is_effectively_ready node.(stat) node.(dly) = true ->
  sem_pend_resume_registration eid node /\ node.(taskGeneration) = generation.
Proof.
  intros eid generation node [Hg [Hm [Hf Hphase]]] Hready.
  split; [|exact Hg]. split; [exact Hm|]. split; [exact Hf|].
  destruct Hphase as [[Hptr [Hpending|[Hclear [Htimeout Hdelay]]]]|[Hptr [Hclear Hresult]]].
  - pose proof (task_effectively_ready_has_no_pending node Hready) as Hnone.
    rewrite Hnone in Hpending; discriminate.
  - rewrite Htimeout; exact Hptr.
  - destruct node.(statPend); exact Hptr || contradiction.
Qed.

Definition mutex_pend_wait_state original eid (state : UCOS2_Verify_State) : Prop :=
  exists node,
    state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
    mutex_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) node.

(** A checked C-module obligation for the EXISTING registry, not another
    registry or platform axiom. Each actual action must prove its own TCB
    effect. Returning same-instance executions exclude retirement; an
    arbitrary application or hook is not admitted by registration alone. *)
Definition mutex_pend_projected_source_client (action : KernelClientAction) : Prop :=
  forall sg before after original eid,
    kernel_client_step action sg before after -> mutex_pend_wait_state original eid before ->
    mutex_pend_wait_state original eid after.

Lemma mutex_pend_task_frame_preserves_wait_state : forall original eid before after,
  after.(TskState).(inUsedTaskStates) = before.(TskState).(inUsedTaskStates) ->
  mutex_pend_wait_state original eid before -> mutex_pend_wait_state original eid after.
Proof. intros original eid before after Hmap [node [Hnode Hwait]]; exists node; rewrite Hmap; auto. Qed.

Lemma mutex_pend_task_update_preserves_wait_state : forall original eid before selected previous next,
  before.(TskState).(inUsedTaskStates) selected = Some previous ->
  (mutex_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) previous ->
   mutex_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) next) ->
  mutex_pend_wait_state original eid before ->
  mutex_pend_wait_state original eid (replace_TskS (glob_task_set_usedtask before.(TskState) selected next) before).
Proof.
  intros original eid before selected previous next Hprevious Hstep [node [Hnode Hwait]].
  unfold mutex_pend_wait_state; cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
  destruct (Z.eqb original.(os_sched_call_stack).(stackLeaseSlot) selected) eqn:E.
  - apply Z.eqb_eq in E; rewrite E in Hnode; assert (node = previous) by congruence; subst node.
    exists next; split; [reflexivity|apply Hstep; exact Hwait].
  - exists node; auto.
Qed.

Lemma mutex_pend_event_wake_preserves_wait_state : forall sg original eid before event_id event selected previous result,
  before.(TskState).(inUsedTaskStates) selected = Some previous -> result <> PendTimeout ->
  mutex_pend_wait_state original eid before ->
  mutex_pend_wait_state original eid (event_wake_state sg before event_id event selected previous PendMutex 0 result).
Proof.
  intros; eapply mutex_pend_task_update_preserves_wait_state; try eassumption.
  apply mutex_pend_wake_preserves_continuation; assumption.
Qed.

Lemma mutex_pend_tick_step_preserves_wait_state : forall sg original eid before selected previous,
  before.(TskState).(inUsedTaskStates) selected = Some previous ->
  mutex_pend_wait_state original eid before ->
  mutex_pend_wait_state original eid (tick_task_step sg selected previous before).
Proof.
  intros; unfold mutex_pend_wait_state in *; rewrite tick_task_step_task_state_eq by assumption.
  change (mutex_pend_wait_state original eid
    (replace_TskS (glob_task_set_usedtask before.(TskState) selected (tick_task_update previous)) before)).
  eapply mutex_pend_task_update_preserves_wait_state; [eassumption| |eassumption].
  apply mutex_pend_tick_preserves_continuation.
Qed.

Lemma mutex_pend_save_sp_preserves_wait_state : forall original eid before selected sp,
  mutex_pend_wait_state original eid before ->
  mutex_pend_wait_state original eid (os_sched_save_current_sp before selected sp).
Proof.
  intros original eid before selected sp Hwait; unfold os_sched_save_current_sp.
  destruct (before.(TskState).(inUsedTaskStates) selected) as [previous|] eqn:Hprevious.
  - eapply mutex_pend_task_update_preserves_wait_state; [exact Hprevious| |exact Hwait].
    apply mutex_pend_wait_fields_preserve_continuation; repeat split; reflexivity.
  - exact Hwait.
Qed.

Lemma mutex_pend_client_trace_preserves_wait_state : forall clients sg observer event_observer before stopped after,
  (forall action, clients action -> mutex_pend_projected_source_client action) ->
  kernel_client_resource_trace clients sg observer event_observer before stopped after ->
  forall original eid, mutex_pend_wait_state original eid before -> mutex_pend_wait_state original eid after.
Proof.
  intros clients sg observer event_observer before stopped after Hclients Htrace.
  induction Htrace as [entry|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intros original eid Hwait; [exact Hwait|].
  apply IH; eapply Hclients; eassumption.
Qed.

Lemma mutex_pend_source_trace_preserves_wait_state : forall external port clients sg observer event_observer
  first before stopped last after,
  (forall action, clients action -> mutex_pend_projected_source_client action) ->
  kernel_resumption_task_source_trace external port clients sg observer event_observer first before stopped last after ->
  forall original eid, mutex_pend_wait_state original eid before -> mutex_pend_wait_state original eid after.
Proof.
  intros * Hclients Htrace original eid Hwait.
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace) as [Hresources _].
  eapply mutex_pend_client_trace_preserves_wait_state; [exact Hclients| |exact Hwait].
  apply kernel_resumption_resource_trace_erases; exact Hresources.
Qed.

Definition mutex_pend_sched_clients environment critical : Prop :=
  (forall action, critical.(critical_region_clients) action -> mutex_pend_projected_source_client action) /\
  mutex_pend_projected_source_client environment.(task_stack_call_external).(os_sched_hook_action).

Lemma mutex_pend_event_task_rdy_preserves_wait_state : forall sg original eid state event_id result priority after,
  event_task_rdy sg state event_id PendMutex 0 result = Some (priority, after) -> result <> PendTimeout ->
  mutex_pend_wait_state original eid state -> mutex_pend_wait_state original eid after.
Proof.
  intros * Hstep Hresult Hwait; unfold event_task_rdy in Hstep.
  destruct (state.(EventState).(inUsedEventStates) event_id) as [event|]; [|discriminate].
  destruct (state.(TskState).(prioTbl) (event_wait_priority state.(TskState) event)) as [| |selected]; try discriminate.
  destruct (state.(TskState).(inUsedTaskStates) selected) as [previous|] eqn:Hselected; [|discriminate].
  injection Hstep as Hpriority Hafter; subst after.
  eapply mutex_pend_event_wake_preserves_wait_state; eassumption.
Qed.

Lemma mutex_pend_event_broadcast_preserves_wait_state : forall sg original eid event_id result state priorities after,
  event_broadcast sg event_id PendMutex 0 result state priorities after -> result <> PendTimeout ->
  mutex_pend_wait_state original eid state -> mutex_pend_wait_state original eid after.
Proof.
  intros sg original eid event_id result state priorities after Hloop Hresult.
  induction Hloop as [state event He Hempty|
    state event priority middle priorities after He Hnonempty Hstep Htail IH]; intros Hwait.
  - exact Hwait.
  - apply IH; eapply mutex_pend_event_task_rdy_preserves_wait_state; eassumption.
Qed.

(** This is a consequence of the actual EventTaskWait transformer and
    the old ready/Idle facts, not a new public Pend precondition. The
    non-Idle priority fact is supplied by the selected Idle call protocol.
    The blocked outgoing caller is deliberately not required to be ready. *)
Lemma mutex_pend_event_wait_call_cut : forall sg call state eid event tid node timeout,
  UCOS2_state_inv sg state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  state.(SchedState).(curTaskID) = Some tid ->
  state.(TskState).(inUsedTaskStates) tid = Some node -> valid_task_prio sg node.(curPrio) ->
  node.(eventPtr) = None -> node.(eventMultiWaitEvents) = [] -> node.(tcbFlagNode) = 0 ->
  In tid state.(SchedState).(readyList) ->
  event_type_to_pend_type event.(eventType) = Some PendMutex -> event_wait_resource_unavailable event ->
  (forall mutex, event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex -> mutex.(mfOwner) <> Some tid) ->
  kernel_call_task_source call state -> sched_current_consistency state.(TskState) state.(SchedState) ->
  sem_pend_blocking_call_stage sg call state -> kernel_tcb_stack_field_layout sg ->
  let waiting := event_pend_state sg state eid event tid node PendMutex timeout in
  UCOS2_state_inv sg waiting /\ sem_pend_wait_sched_entry sg call waiting /\
  mutex_pend_wait_state call eid waiting.
Proof.
  intros sg call state eid event tid node timeout Hvalid He Hcurrent Hnode Hprio
    Hnull Hmulti Hflag Hready Hkind Hunavailable Hnotowner Hsource Hcache
    [Hidle [Havailable [Hint Hlock]]] Hlayout waiting.
  assert (Hvalid' : UCOS2_state_inv sg waiting).
  { eapply UCOS2_event_pend_preserves_validity; eassumption. }
  assert (Hsource' : kernel_call_task_source call waiting).
  { destruct Hsource as [Hlease [Hactive Hcur]].
    split; [exact Hlease|]. split.
    - unfold waiting; cbn [event_pend_state event_wait_state replace_TskS replace_SchedS replace_EventS TskState].
      eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hnode|reflexivity|exact Hactive].
    - exact Hcur. }
  assert (Hcache' : sched_current_consistency waiting.(TskState) waiting.(SchedState)).
  { unfold sched_current_consistency in Hcache; rewrite Hcurrent in Hcache.
    destruct Hcache as [current [Hlookup Hpriority]]; assert (current = node) by congruence; subst current.
    unfold sched_current_consistency.
    change (match state.(SchedState).(curTaskID) with
      | None => state.(SchedState).(curSchedPrio) = None
      | Some selected => exists current,
          (if Z.eqb selected tid then Some (task_set_event_ptr (task_prepare_event_wait node PendMutex timeout) (Some eid))
           else state.(TskState).(inUsedTaskStates) selected) = Some current /\
          state.(SchedState).(curSchedPrio) = Some current.(curPrio)
      end).
    rewrite Hcurrent; exists (task_set_event_ptr (task_prepare_event_wait node PendMutex timeout) (Some eid)).
    split; [rewrite Z.eqb_refl; reflexivity|exact Hpriority]. }
  assert (Hidle' : task_idle_ready sg waiting.(TskState)).
  { eapply event_pend_preserves_idle_ready; eassumption. }
  assert (Hready' : waiting.(SchedState).(readyList) <> []).
  { eapply sched_idle_ready_nonempty; [exact (proj1 (proj1 (proj2 (proj2 Hvalid'))))|exact Hidle']. }
  assert (Havailable' : kernel_call_stack_available call waiting) by exact Havailable.
  assert (Hcut : os_sched_call_cut sg call waiting).
  { eapply os_sched_call_cut_from_source; try eassumption.
    eapply kernel_call_task_source_stack_field_address; eassumption. }
  split; [exact Hvalid'|]. split.
  - split; [exact Hcut|]. split.
    + apply os_sched_selection_enabled_iff; split; assumption.
    + split; [exact Hsource'|]. split; [unfold sem_pend_blocking_call_stage; auto|exact Hcache'].
  - pose proof (kernel_call_task_source_current_at call state Hsource)
      as [Hslot [current [Hlookup Hgeneration]]].
    assert (Htid : tid = call.(os_sched_call_stack).(stackLeaseSlot)) by congruence.
    assert (current = node) by (rewrite <- Htid in Hlookup; congruence); subst current.
    unfold mutex_pend_wait_state; exists (task_set_event_ptr (task_prepare_event_wait node PendMutex timeout) (Some eid)).
    split.
    + unfold waiting; cbn [event_pend_state event_wait_state replace_TskS replace_SchedS replace_EventS TskState
        glob_task_set_usedtask inUsedTaskStates]; rewrite <- Htid, Z.eqb_refl; reflexivity.
    + rewrite <- Hgeneration; apply mutex_pend_wait_establishes_continuation; try assumption.
      pose proof Hvalid as [_ [_ [[Hready_inv _] _]]].
      destruct (proj1 Hready_inv _ Hready) as [current [Hready_lookup [_ Heffective]]].
      assert (current = node) by congruence; subst current; exact Heffective.
Qed.

Lemma mutex_pend_sched_return_preserves_wait_state : forall environment critical sg entry call returned after original eid,
  mutex_pend_sched_clients environment critical ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry call returned after ->
  mutex_pend_wait_state original eid entry -> mutex_pend_wait_state original eid after.
Proof.
  intros * [Hclients Hhook] Hreturn Hwait; unfold os_sched_c_return in Hreturn.
  destruct (os_sched_requests_switch entry).
  - destruct Hreturn as [installed [Hsource [[stopped [Htrace Hnormal]] Hreturned]]].
    destruct Hsource as [_ [sp [saved [hooked [incoming [resumed [Hsave [Hstep [_ ->]]]]]]]]].
    eapply mutex_pend_client_trace_preserves_wait_state; [exact Hclients|exact Htrace|].
    eapply mutex_pend_task_frame_preserves_wait_state with (before := hooked); [reflexivity|].
    eapply Hhook; [exact Hstep|].
    eapply mutex_pend_save_sp_preserves_wait_state; exact Hwait.
  - destruct Hreturn as [_ ->]; exact Hwait.
Qed.

(** The index is a pure observation of this real first protected Pend
    result. It is not a second kernel object or a Sem phase relabelled.
    The current continuation is transported at each actual C source edge;
    it is never obtained from the original snapshot by equality. *)
Inductive MutexPendCallPhase : Type :=
| MutexPendWaitPhase (original : OsSchedCallContext) (mask : Z)
    (before : UCOS2_Verify_State) (observed : OSEventAbstractState)
    (eid : EventID) (timeout : Z) (waiting : UCOS2_Verify_State).

Definition mutex_pend_wait_at sg original initial observed eid timeout waiting call current : Prop :=
  kernel_stack_call_same_call call original /\
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) /\
  initial.(EventState).(inUsedEventStates) eid = Some observed /\
  mutex_pend_first_critical sg eid timeout initial
    (MutexPendWaiting original.(os_sched_call_stack).(stackLeaseSlot)
      original.(os_sched_call_stack).(stackLeaseGeneration)) waiting /\
  mutex_pend_wait_state original eid current.

Definition mutex_pend_wait_selected_at sg original initial observed eid timeout waiting call current : Prop :=
  mutex_pend_wait_at sg original initial observed eid timeout waiting call current /\
  exists node, sem_pend_resume_entry sg current eid original.(os_sched_call_stack).(stackLeaseSlot) node.

Definition mutex_pend_restore_phase_pre phase (_ : option TaskStackCallEnvironment)
  (_ : CriticalRegionResources) sg call mask state : Prop :=
  match phase with
  | MutexPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      mask = initial_mask /\
      mutex_pend_wait_at sg original initial observed eid timeout waiting call state /\
      sem_pend_wait_sched_entry sg call state
  end.

Lemma mutex_pend_wait_at_modular_return : forall environment critical sg original initial observed eid timeout waiting
  call before returned after,
  (forall action, critical.(critical_region_clients) action -> mutex_pend_projected_source_client action) ->
  mutex_pend_wait_at sg original initial observed eid timeout waiting call before ->
  sem_pend_modular_call_history environment critical sg call before returned after ->
  mutex_pend_wait_at sg original initial observed eid timeout waiting returned after.
Proof.
  intros * Hclients [Hsame [Horigin [Hobserved [Hfirst Hwait]]]] [Htrace [Hreturned Havailable]].
  split.
  - unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence.
  - split; [exact Horigin|]. split; [exact Hobserved|]. split; [exact Hfirst|].
    eapply mutex_pend_source_trace_preserves_wait_state; eassumption.
Qed.

Lemma mutex_pend_selected_from_ready_current : forall sg original initial observed eid timeout waiting call current,
  mutex_pend_wait_at sg original initial observed eid timeout waiting call current ->
  UCOS2_state_inv sg current ->
  current.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  In original.(os_sched_call_stack).(stackLeaseSlot) current.(SchedState).(readyList) ->
  mutex_pend_wait_selected_at sg original initial observed eid timeout waiting call current.
Proof.
  intros * Hwait Hvalid Hcurrent Hready; split; [exact Hwait|].
  destruct Hwait as [_ [_ [_ [_ [old [Hold Hcontinuation]]]]]].
  pose proof Hvalid as [_ [_ [[Hready_inv _] _]]].
  destruct (proj1 Hready_inv _ Hready) as [node [Hnode [Hpriority Heffective]]].
  assert (node = old) by congruence; subst node.
  destruct (mutex_pend_ready_resume_registration _ _ _ Hcontinuation Heffective) as [Hregistration Hgeneration].
  exists old; unfold sem_pend_resume_entry; auto.
Qed.

Lemma mutex_pend_sched_body_selected : forall environment critical sg original initial observed eid timeout waiting
  entered entry returned released,
  mutex_pend_sched_clients environment critical ->
  mutex_pend_wait_at sg original initial observed eid timeout waiting entered entry ->
  sem_pend_wait_sched_entry sg entered entry ->
  UCOS2_state_inv sg entry -> UCOS2_state_inv sg released ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry entered returned released ->
  (os_sched_requests_switch entry = true ->
    In entered.(os_sched_call_stack).(stackLeaseSlot) released.(SchedState).(readyList)) ->
  mutex_pend_wait_selected_at sg original initial observed eid timeout waiting returned released.
Proof.
  intros * Hclients Hwait [Hcut [Henabled [Hsource [Hblocking Hcache]]]] Hvalid Hvalid' Hbody Hswitch_ready.
  pose proof Hwait as [Hsame [Horigin [Hobserved [Hfirst Hcontinued]]]].
  pose proof (os_sched_c_return_execution_identity _ _ _ _ _ _ _ Hbody) as Hreturned.
  assert (Hwait' : mutex_pend_wait_at sg original initial observed eid timeout waiting returned released).
  { split; [unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence|].
    split; [exact Horigin|]. split; [exact Hobserved|]. split; [exact Hfirst|].
    eapply mutex_pend_sched_return_preserves_wait_state; eassumption. }
  assert (Hreturned_source : kernel_call_task_source returned released).
  { eapply os_sched_continuation_c_return_source; [|exact Hbody|exact Hsource].
    intro Hswitch; exact (proj1 (proj2 Hcut Hswitch)). }
  pose proof (kernel_call_task_source_current_at returned released Hreturned_source) as [Hcurrent Hnode].
  assert (Hready : In entered.(os_sched_call_stack).(stackLeaseSlot) released.(SchedState).(readyList)).
  { destruct (os_sched_requests_switch entry) eqn:Hswitch; [apply Hswitch_ready; reflexivity|].
    pose proof Hbody as Hnonswitch; unfold os_sched_c_return in Hnonswitch; rewrite Hswitch in Hnonswitch.
    destruct Hnonswitch as [-> ->].
    destruct (os_sched_nonswitch_current_ready_at sg entered entry Hvalid Hsource Hcache Henabled
      Hswitch (proj1 Hcut Henabled)) as [node [[Hlookup [Hcur [Hprio [Hin Hnode_ready]]]] Hgen]].
    exact Hin. }
  eapply mutex_pend_selected_from_ready_current; [exact Hwait'|exact Hvalid'| |].
  - rewrite (proj2 (proj2 Hreturned)), (proj2 (proj2 Hsame)) in Hcurrent; exact Hcurrent.
  - rewrite (proj2 (proj2 Hsame)) in Hready; exact Hready.
Qed.

Lemma mutex_pend_selected_source_resume_entry : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg focus incoming selected node state eid generation waiting,
  state.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some waiting ->
  mutex_pend_wait_continuation eid generation waiting ->
  os_sched_source_selected_post external platform port abi
    sg focus incoming selected node state |--
  coq_prop (sem_pend_resume_entry sg state eid incoming.(stackLeaseSlot) waiting) && TT.
Proof.
  intros * Hwaiting Hwait; unfold os_sched_source_selected_post; Intros.
  assert (Hready : sched_current_ready_at state.(TskState) state.(SchedState)
    incoming.(stackLeaseSlot) node) by tauto.
  destruct Hready as [Hnode [Hcurrent [Hpriority [Hmember Heffective]]]].
  assert (node = waiting) by congruence; subst node.
  destruct (mutex_pend_ready_resume_registration eid generation waiting Hwait Heffective)
    as [Hregistration _].
  unfold UCOS2_inv; Intros.
  unfold sem_pend_resume_entry; entailer!; intros ? ?; exact I.
Qed.

Lemma mutex_pend_wait_selected_modular_return : forall environment critical sg original initial
  observed eid timeout waiting call before returned after,
  (forall action, critical.(critical_region_clients) action -> mutex_pend_projected_source_client action) ->
  mutex_pend_wait_selected_at sg original initial observed eid timeout waiting call before ->
  sem_pend_modular_call_history environment critical sg call before returned after ->
  sem_pend_save_rely sg before after ->
  mutex_pend_wait_selected_at sg original initial observed eid timeout waiting returned after.
Proof.
  intros * Hclients [Hwait [old [Hvalid [Hcurrent [Hold [Hregistration Hready]]]]]]
    Hhistory [_ [_ [_ Hready_rely]]].
  pose proof (mutex_pend_wait_at_modular_return environment critical sg original initial
    observed eid timeout waiting call before returned after Hclients Hwait Hhistory) as Hwait'.
  pose proof Hwait as [Hsame [Horigin Hrest]].
  pose proof Hhistory as [Htrace [Hreturned Havailable]].
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)
    as [Hresources Hcontrol].
  destruct (critical_region_interval_transports_resources critical sg
    call.(os_sched_call_invocation) before after Hresources Hvalid) as [Hvalid' _].
  assert (Hcaller_origin : call.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration)).
  { rewrite (proj1 (proj2 Hsame)); exact Horigin. }
  assert (Hcurrent' : after.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot)).
  { assert (Hbefore : task_execution_current call.(os_sched_call_origin) before).
    { rewrite Hcaller_origin; exact Hcurrent. }
    pose proof (task_execution_source_trace_preserves_current _ _ _ _ _ _ _ Hcontrol Hbefore) as Hafter.
    rewrite (proj1 (proj2 Hreturned)), Hcaller_origin in Hafter; exact Hafter. }
  eapply mutex_pend_selected_from_ready_current; [exact Hwait'|exact Hvalid'|exact Hcurrent'|].
  apply Hready_rely; assumption.
Qed.

(** Only the pure wait index is Mutex-specific. The owned world, saved
    local family, active stack lease, unmap table, and normal-return
    platform observation are exactly the established generic interfaces.
    The sem_pend_* resource/rely names below do not contain PendSem. *)
Definition mutex_pend_sched_save_observation environment critical sg original before returned acquired : Prop :=
  task_tcb_init_stack_source_preserved original before acquired /\
  sem_pend_modular_call_history environment critical sg original before returned acquired.

(** The actual three call edges of this Scheduler instance. This is only
    an observation of the already established modular Save/body/Restore
    relations, not another execution history or a promise of return. *)
Definition mutex_pend_sched_return (environment : option TaskStackCallEnvironment)
  critical sg original before returned after : Prop :=
  match environment with
  | None => False
  | Some owned => exists entered acquired resumed released,
      sem_pend_modular_call_history owned critical sg original before entered acquired /\
      os_sched_c_return owned.(task_stack_call_external) critical sg acquired entered resumed released /\
      sem_pend_modular_call_history owned critical sg resumed released returned after
  end.

Definition mutex_pend_continuation_phase_sched_input phase external platform environment critical saved_local
  sg call mask before : Assertion :=
  coq_prop (mutex_pend_restore_phase_pre phase environment critical sg call mask before) &&
  sem_pend_continuation_sched_input external platform environment saved_local sg call mask before.

Definition mutex_pend_continuation_phase_sched_output phase external platform environment critical saved_local
  sg call mask (before : UCOS2_Verify_State) : Assertion :=
  match phase with
  | MutexPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      EX returned current,
        coq_prop (kernel_stack_call_same_call returned call /\
          mutex_pend_wait_selected_at sg original initial observed eid timeout waiting returned current /\
          mutex_pend_sched_return environment critical sg call before returned current) &&
        (sem_pend_continuation_save_input external platform environment critical saved_local sg returned mask current **
          unmap_table_rep sg)
  end.

Definition mutex_pend_sched_save_input phase environment critical saved_local sg call mask state : Assertion :=
  coq_prop (mutex_pend_restore_phase_pre phase (Some environment) critical sg call mask state) &&
  (task_tcb_init_continuation_save_input environment critical saved_local sg call mask state ** unmap_table_rep sg).

Definition mutex_pend_sched_save_output phase environment critical saved_local sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (task_tcb_init_stack_same_call returned original /\ interrupt_saved_value mask saved /\
      mutex_pend_sched_save_observation environment critical sg original before returned acquired /\
      mutex_pend_sched_clients environment critical /\
      mutex_pend_restore_phase_pre phase (Some environment) critical sg returned mask acquired) &&
    (task_tcb_init_continuation_restore_input environment critical saved_local sg returned saved acquired acquired **
      unmap_table_rep sg).

Definition mutex_pend_sched_restore_input phase environment critical saved_local sg call saved acquired released : Assertion :=
  match phase with
  | MutexPendWaitPhase original mask initial observed eid timeout waiting =>
      coq_prop (mutex_pend_wait_selected_at sg original initial observed eid timeout waiting call released) &&
      (task_tcb_init_continuation_restore_input environment critical saved_local sg call saved acquired released **
        unmap_table_rep sg)
  end.

Definition mutex_pend_sched_restore_output phase environment critical saved_local sg call saved
  (released : UCOS2_Verify_State) : Assertion :=
  match phase with
  | MutexPendWaitPhase original mask initial observed eid timeout waiting =>
      EX returned current,
        coq_prop (kernel_stack_call_same_call returned call /\
          mutex_pend_wait_selected_at sg original initial observed eid timeout waiting returned current /\
          sem_pend_modular_call_history environment critical sg call released returned current) &&
        (task_tcb_init_continuation_save_input environment critical saved_local sg returned
          (armv7a_irq_fiq_mask saved) current ** unmap_table_rep sg)
  end.

Definition mutex_pend_sched_switch_output phase environment critical saved_local sg call saved acquired entry : Assertion :=
  EX returned current,
    coq_prop (os_sched_c_return environment.(task_stack_call_external) critical sg entry call returned current /\
      UCOS2_state_inv sg current) &&
    mutex_pend_sched_restore_input phase environment critical saved_local sg returned saved acquired current.

Definition mutex_pend_sched_switch_input phase environment critical saved_local sg call mask saved acquired entry : Assertion :=
  coq_prop (mutex_pend_sched_clients environment critical /\ interrupt_saved_value mask saved /\
    UCOS2_state_inv sg entry /\
    mutex_pend_restore_phase_pre phase (Some environment) critical sg call mask entry) &&
  os_sched_continuation_switch_pre environment critical saved_local kernel_program_inv sg call saved acquired entry.

Lemma mutex_pend_sched_call_save_input : forall environment critical saved_local sg original initial_mask initial
  observed eid timeout waiting call mask before,
  mutex_pend_continuation_phase_sched_input (MutexPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
    critical saved_local sg call mask before |--
  coq_prop (os_sched_call_cut sg call before) &&
  mutex_pend_sched_save_input (MutexPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment critical saved_local sg call mask before.
Proof.
  intros; unfold mutex_pend_continuation_phase_sched_input.
  cbn [sem_pend_continuation_sched_input].
  unfold os_sched_continuation_pre; Intros.
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_save_input_closed_world
    environment critical saved_local sg call mask before)).
  unfold mutex_pend_sched_save_input; unfold mutex_pend_restore_phase_pre in *.
  unfold sem_pend_wait_sched_entry in *; entailer!.
Qed.

Lemma mutex_pend_sched_modular_save_output : forall environment critical saved_local sg original initial_mask initial
  observed eid timeout waiting call mask saved before,
  mutex_pend_sched_clients environment critical -> kernel_tcb_stack_field_layout sg -> UCOS2_state_inv sg before ->
  mutex_pend_restore_phase_pre (MutexPendWaitPhase original initial_mask initial observed eid timeout waiting)
    (Some environment) critical sg call mask before ->
  kernel_call_modular_save_post environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) critical sem_pend_blocking_rely
    sg call mask saved before |--
  mutex_pend_sched_save_output (MutexPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment critical saved_local sg call mask saved before.
Proof.
  intros * Hclients Hlayout Hvalid [Hmask [Hwait Hentry]].
  unfold kernel_call_modular_save_post; Intros returned acquired.
  assert (Hsave : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call returned mask saved before acquired) by tauto.
  assert (Hnormal : kernel_call_normal_return call before returned acquired) by tauto.
  pose proof (proj1 Hnormal) as Hsame.
  assert (Hrely : sem_pend_blocking_rely sg before acquired) by tauto.
  pose proof Hsave as [Htrace [Hi [Ho [Hs Hsaved]]]].
  assert (Hhistory : sem_pend_modular_call_history environment critical sg call before returned acquired)
    by (split; assumption).
  pose proof (mutex_pend_wait_at_modular_return _ _ _ _ _ _ _ _ _ _ _ _ _
    (proj1 Hclients) Hwait Hhistory) as Hwait'.
  pose proof (sem_pend_wait_sched_entry_modular_return environment critical sg call before returned acquired
    Hlayout Hvalid (proj1 (proj2 (proj2 Hentry))) Hentry Hhistory Hrely) as Hentry'.
  assert (Hpreserved : task_tcb_init_stack_source_preserved call before acquired).
  { eapply task_tcb_init_stack_registered_source_preserved; [exact Hvalid|exact (proj1 Hnormal)|exact Htrace]. }
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_restore_input_masked_world
    environment critical saved_local sg returned saved acquired acquired)).
  unfold mutex_pend_sched_save_output; Exists returned acquired.
  unfold mutex_pend_restore_phase_pre, mutex_pend_sched_save_observation; entailer!.
Qed.

(** Readiness on the switching branch must be supplied by the ACTUAL
    selected C endpoint (see mutex_pend_selected_source_resume_entry), not
    by the architecture token or by promising that the call will return.
    This same endpoint condition is used by the already delivered Sem
    Scheduler; the common body/resource interface is left unchanged. *)
Lemma mutex_pend_sched_modular_switch_output : forall environment critical saved_local sg original initial_mask initial
  observed eid timeout waiting call mask saved acquired entry,
  mutex_pend_sched_clients environment critical -> UCOS2_state_inv sg entry ->
  mutex_pend_restore_phase_pre (MutexPendWaitPhase original initial_mask initial observed eid timeout waiting)
    (Some environment) critical sg call mask entry ->
  (forall returned current,
    os_sched_c_return environment.(task_stack_call_external) critical sg entry call returned current ->
    os_sched_requests_switch entry = true -> In call.(os_sched_call_stack).(stackLeaseSlot) current.(SchedState).(readyList)) ->
  os_sched_continuation_body_post environment critical saved_local kernel_program_inv sg call saved acquired entry |--
  mutex_pend_sched_switch_output (MutexPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment critical saved_local sg call saved acquired entry.
Proof.
  intros * Hclients Hvalid [Hmask [Hwait Hentry]] Hready.
  sep_apply_l_atomic (os_sched_continuation_body_restore_input environment critical saved_local sg call saved acquired entry).
  Intros returned current.
  assert (Hbody : os_sched_c_return environment.(task_stack_call_external) critical sg entry call returned current) by tauto.
  assert (Hvalid' : UCOS2_state_inv sg current) by tauto.
  pose proof (mutex_pend_sched_body_selected _ _ _ _ _ _ _ _ _ _ _ _ _
    Hclients Hwait Hentry Hvalid Hvalid' Hbody (Hready returned current Hbody)) as Hselected.
  unfold mutex_pend_sched_switch_output; Exists returned current.
  cbn [mutex_pend_sched_restore_input]; entailer!.
Qed.

Lemma mutex_pend_sched_nonswitch_selected : forall environment critical sg original initial_mask initial
  observed eid timeout waiting call mask entry,
  mutex_pend_sched_clients environment critical -> UCOS2_state_inv sg entry ->
  mutex_pend_restore_phase_pre (MutexPendWaitPhase original initial_mask initial observed eid timeout waiting)
    (Some environment) critical sg call mask entry ->
  os_sched_requests_switch entry = false ->
  mutex_pend_wait_selected_at sg original initial observed eid timeout waiting call (os_sched_prefix_state entry).
Proof.
  intros * Hclients Hvalid [Hmask [Hwait Hentry]] Hswitch.
  eapply mutex_pend_sched_body_selected; try eassumption.
  - apply os_sched_ready_checkpoint_preserves_validity; exact Hvalid.
  - unfold os_sched_c_return; rewrite Hswitch; auto.
  - congruence.
Qed.

Lemma mutex_pend_sched_modular_restore_output : forall environment critical saved_local sg original initial_mask initial
  observed eid timeout waiting call saved released,
  mutex_pend_sched_clients environment critical ->
  mutex_pend_wait_selected_at sg original initial observed eid timeout waiting call released ->
  kernel_call_modular_restore_post environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) critical sem_pend_save_rely
    sg call (armv7a_irq_fiq_mask saved) released |--
  mutex_pend_sched_restore_output (MutexPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment critical saved_local sg call saved released.
Proof.
  intros * Hclients Hselected.
  unfold kernel_call_modular_restore_post; Intros returned current.
  assert (Hhistory : sem_pend_modular_call_history environment critical sg call released returned current)
    by (unfold sem_pend_modular_call_history; tauto).
  pose proof (proj1 (proj2 Hhistory)) as Hsame.
  assert (Hrely : sem_pend_save_rely sg released current) by tauto.
  pose proof (mutex_pend_wait_selected_modular_return _ _ _ _ _ _ _ _ _ _ _ _ _
    (proj1 Hclients) Hselected Hhistory Hrely) as Hselected'.
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_save_input_closed_world
    environment critical saved_local sg returned (armv7a_irq_fiq_mask saved) current)).
  cbn [mutex_pend_sched_restore_output]; Exists returned current; entailer!.
Qed.

Lemma mutex_pend_sched_restore_output_return : forall environment critical saved_local sg original initial_mask initial
  observed eid timeout waiting context scheduled returned mask saved before entry released,
  task_tcb_init_stack_same_call scheduled context ->
  mutex_pend_sched_save_observation environment critical sg context before scheduled entry ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry scheduled returned released ->
  interrupt_saved_value mask saved ->
  mutex_pend_sched_restore_output (MutexPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment critical saved_local sg returned saved released |--
  mutex_pend_continuation_phase_sched_output (MutexPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
    critical saved_local sg context mask before.
Proof.
  intros * Hscheduled [Hpreserved Hsave_history] Hbody Hsaved.
  pose proof (os_sched_c_return_execution_identity _ _ _ _ _ _ _ Hbody) as Hreturned.
  cbn [mutex_pend_sched_restore_output]; Intros final current.
  assert (Hsame : kernel_stack_call_same_call final context).
  { assert (Hfinal : kernel_stack_call_same_call final returned) by tauto.
    unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence. }
  assert (Htrace : mutex_pend_sched_return (Some environment) critical sg context before final current).
  { exists scheduled, entry, returned, released.
    split; [exact Hsave_history|]. split; [exact Hbody|tauto]. }
  rewrite (proj2 Hsaved).
  sep_apply_l_atomic (proj2 (sem_pend_continuation_save_input_owned environment critical saved_local sg final mask current)).
  cbn [mutex_pend_continuation_phase_sched_output]; Exists final current; entailer!.
Qed.
