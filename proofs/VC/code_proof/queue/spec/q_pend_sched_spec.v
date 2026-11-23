Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.event_wait Ucos2Verify.lib.event Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.tick.
Require Import Ucos2Verify.VC.code.queue.spec.q_pend_spec.
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
Require Export Ucos2Verify.VC.code.queue.spec.q_pend_call_spec.
Require Export Ucos2Verify.VC.code.queue.spec.q_pend_spec.
Require Export Ucos2Verify.VC.code.queue.spec.q_pend_proof_helpers.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** This is a consequence of the actual EventTaskWait transformer and
    the old ready/Idle facts, not a new public Pend precondition. The
    non-Idle priority fact is supplied by the selected Idle call protocol.
    The blocked outgoing caller is deliberately not required to be ready. *)
Lemma q_pend_event_wait_call_cut : forall sg call state eid event tid node timeout,
  UCOS2_state_inv sg state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  state.(SchedState).(curTaskID) = Some tid ->
  state.(TskState).(inUsedTaskStates) tid = Some node -> valid_task_prio sg node.(curPrio) ->
  node.(eventPtr) = None -> node.(eventMultiWaitEvents) = [] -> node.(tcbFlagNode) = 0 ->
  In tid state.(SchedState).(readyList) ->
  event_type_to_pend_type event.(eventType) = Some PendQ -> event_wait_resource_unavailable event ->
  (forall mutex, event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex -> mutex.(mfOwner) <> Some tid) ->
  kernel_call_task_source call state -> sched_current_consistency state.(TskState) state.(SchedState) ->
  sem_pend_blocking_call_stage sg call state -> kernel_tcb_stack_field_layout sg ->
  let waiting := event_pend_state sg state eid event tid node PendQ timeout in
  UCOS2_state_inv sg waiting /\ sem_pend_wait_sched_entry sg call waiting /\
  q_pend_wait_state call eid waiting.
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
          (if Z.eqb selected tid then Some (task_set_event_ptr (task_prepare_event_wait node PendQ timeout) (Some eid))
           else state.(TskState).(inUsedTaskStates) selected) = Some current /\
          state.(SchedState).(curSchedPrio) = Some current.(curPrio)
      end).
    rewrite Hcurrent; exists (task_set_event_ptr (task_prepare_event_wait node PendQ timeout) (Some eid)).
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
    unfold q_pend_wait_state; exists (task_set_event_ptr (task_prepare_event_wait node PendQ timeout) (Some eid)).
    split.
    + unfold waiting; cbn [event_pend_state event_wait_state replace_TskS replace_SchedS replace_EventS TskState
        glob_task_set_usedtask inUsedTaskStates]; rewrite <- Htid, Z.eqb_refl; reflexivity.
    + rewrite <- Hgeneration; apply q_pend_wait_establishes_continuation; try assumption.
      pose proof Hvalid as [_ [_ [[Hready_inv _] _]]].
      destruct (proj1 Hready_inv _ Hready) as [current [Hready_lookup [_ Heffective]]].
      assert (current = node) by congruence; subst current; exact Heffective.
Qed.

(** The actual returning source trace transports this invocation only.
    Its starting validity/active owner comes from the actual installed
    resource producer; the weaker pure os_sched_c_return is not used to
    manufacture that cut. *)
Lemma q_pend_returning_clients_preserve_wait_state : forall environment critical sg original eid
  event_observer before after,
  q_pend_sched_clients environment critical ->
  UCOS2_state_inv sg before ->
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active before.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  q_pend_wait_state original eid before ->
  kernel_client_resource_trace critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) event_observer before false after ->
  UCOS2_state_inv sg after /\
  task_invocation_active after.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
  q_pend_wait_state original eid after.
Proof.
  intros * [Hclients Hhook] Hvalid Horigin Hactive Hwait Htrace.
  eapply q_pend_client_trace_preserves_wait_state; try eassumption.
  - exact critical.(critical_region_client_certificates).
  - reflexivity.
Qed.

(** The index is a pure observation of this real first protected Pend
    result. It is not a second kernel object or a Sem phase relabelled.
    The current continuation is transported at each actual C source edge;
    it is never obtained from the original snapshot by equality. *)
Inductive QueuePendCallPhase : Type :=
| QueuePendWaitPhase (original : OsSchedCallContext) (mask : Z)
    (before : UCOS2_Verify_State) (observed : OSEventAbstractState)
    (eid : EventID) (timeout : Z) (waiting : UCOS2_Verify_State).

Definition q_pend_wait_at sg original initial observed eid timeout waiting call current : Prop :=
  kernel_stack_call_same_call call original /\
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) /\
  initial.(EventState).(inUsedEventStates) eid = Some observed /\
  q_pend_first_critical sg eid timeout initial
    (QueuePendWaiting original.(os_sched_call_stack).(stackLeaseSlot)
      original.(os_sched_call_stack).(stackLeaseGeneration)) waiting /\
  task_invocation_active current.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
  q_pend_wait_state original eid current.

Definition q_pend_wait_selected_at sg original initial observed eid timeout waiting call current : Prop :=
  q_pend_wait_at sg original initial observed eid timeout waiting call current /\
  exists node, sem_pend_resume_entry sg current eid original.(os_sched_call_stack).(stackLeaseSlot) node.

Definition q_pend_restore_phase_pre phase (_ : option TaskStackCallEnvironment)
  (_ : CriticalRegionResources) sg call mask state : Prop :=
  match phase with
  | QueuePendWaitPhase original initial_mask initial observed eid timeout waiting =>
      mask = initial_mask /\
      q_pend_wait_at sg original initial observed eid timeout waiting call state /\
      sem_pend_wait_sched_entry sg call state
  end.

Lemma q_pend_wait_at_modular_return : forall environment critical sg original initial observed eid timeout waiting
  call before returned after,
  (forall action, critical.(critical_region_clients) action -> q_pend_projected_source_client action) ->
  UCOS2_state_inv sg before ->
  q_pend_wait_at sg original initial observed eid timeout waiting call before ->
  sem_pend_modular_call_history environment critical sg call before returned after ->
  q_pend_wait_at sg original initial observed eid timeout waiting returned after.
Proof.
  intros * Hclients Hvalid [Hsame [Horigin [Hobserved [Hfirst [Hactive Hwait]]]]] [Htrace [Hreturned Havailable]].
  split.
  - unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence.
  - split; [exact Horigin|]. split; [exact Hobserved|]. split; [exact Hfirst|].
    rewrite (proj1 Hsame) in Htrace.
    destruct (q_pend_source_trace_preserves_wait_state _ _ critical sg original eid _ _ _ _ _ _
      Hclients Htrace eq_refl Hvalid Horigin Hactive Hwait) as [_ Hafter]; exact Hafter.
Qed.

Lemma q_pend_selected_from_ready_current : forall sg original initial observed eid timeout waiting call current,
  q_pend_wait_at sg original initial observed eid timeout waiting call current ->
  UCOS2_state_inv sg current ->
  current.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  In original.(os_sched_call_stack).(stackLeaseSlot) current.(SchedState).(readyList) ->
  q_pend_wait_selected_at sg original initial observed eid timeout waiting call current.
Proof.
  intros * Hwait Hvalid Hcurrent Hready; split; [exact Hwait|].
  destruct Hwait as [_ [_ [_ [_ [_ [old [Hold Hcontinuation]]]]]]].
  pose proof Hvalid as [_ [_ [[Hready_inv _] _]]].
  destruct (proj1 Hready_inv _ Hready) as [node [Hnode [Hpriority Heffective]]].
  assert (node = old) by congruence; subst node.
  destruct (q_pend_ready_resume_registration _ _ _ Hcontinuation Heffective) as [Hregistration Hgeneration].
  exists old; unfold sem_pend_resume_entry; auto.
Qed.

Lemma q_pend_sched_body_selected : forall environment critical sg original initial observed eid timeout waiting
  entered entry returned released,
  q_pend_sched_clients environment critical ->
  q_pend_wait_at sg original initial observed eid timeout waiting entered entry ->
  sem_pend_wait_sched_entry sg entered entry ->
  UCOS2_state_inv sg entry -> UCOS2_state_inv sg released ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry entered returned released ->
  (os_sched_requests_switch entry = true ->
    q_pend_wait_state original eid released /\
    In entered.(os_sched_call_stack).(stackLeaseSlot) released.(SchedState).(readyList)) ->
  q_pend_wait_selected_at sg original initial observed eid timeout waiting returned released.
Proof.
  intros * Hclients Hwait [Hcut [Henabled [Hsource [Hblocking Hcache]]]] Hvalid Hvalid' Hbody Hswitch_ready.
  pose proof Hwait as [Hsame [Horigin [Hobserved [Hfirst [Hactive Hcontinued]]]]].
  pose proof (os_sched_c_return_execution_identity _ _ _ _ _ _ _ Hbody) as Hreturned.
  assert (Hwait' : q_pend_wait_at sg original initial observed eid timeout waiting returned released).
  { split; [unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence|].
    split; [exact Horigin|]. split; [exact Hobserved|]. split; [exact Hfirst|].
    split.
    - pose proof (os_sched_continuation_c_return_source _ _ _ _ _ _ _
        ltac:(intro Hswitch; exact (proj1 (proj2 Hcut Hswitch))) Hbody Hsource) as Hreturned_source.
      destruct Hreturned_source as [_ [Hreturned_active _]].
      rewrite (proj1 Hreturned), (proj1 (proj2 Hreturned)),
        (proj1 Hsame), (proj1 (proj2 Hsame)) in Hreturned_active; exact Hreturned_active.
    - destruct (os_sched_requests_switch entry) eqn:Hswitch.
      + exact (proj1 (Hswitch_ready eq_refl)).
      + unfold os_sched_c_return in Hbody; rewrite Hswitch in Hbody.
        destruct Hbody as [-> ->]; exact Hcontinued. }
  assert (Hreturned_source : kernel_call_task_source returned released).
  { eapply os_sched_continuation_c_return_source; [|exact Hbody|exact Hsource].
    intro Hswitch; exact (proj1 (proj2 Hcut Hswitch)). }
  pose proof (kernel_call_task_source_current_at returned released Hreturned_source) as [Hcurrent Hnode].
  assert (Hready : In entered.(os_sched_call_stack).(stackLeaseSlot) released.(SchedState).(readyList)).
  { destruct (os_sched_requests_switch entry) eqn:Hswitch; [exact (proj2 (Hswitch_ready eq_refl))|].
    pose proof Hbody as Hnonswitch; unfold os_sched_c_return in Hnonswitch; rewrite Hswitch in Hnonswitch.
    destruct Hnonswitch as [-> ->].
    destruct (os_sched_nonswitch_current_ready_at sg entered entry Hvalid Hsource Hcache Henabled
      Hswitch (proj1 Hcut Henabled)) as [node [[Hlookup [Hcur [Hprio [Hin Hnode_ready]]]] Hgen]].
    exact Hin. }
  eapply q_pend_selected_from_ready_current; [exact Hwait'|exact Hvalid'| |].
  - rewrite (proj2 (proj2 Hreturned)), (proj2 (proj2 Hsame)) in Hcurrent; exact Hcurrent.
  - rewrite (proj2 (proj2 Hsame)) in Hready; exact Hready.
Qed.

Lemma q_pend_selected_source_resume_entry : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg focus incoming selected node state eid generation waiting,
  state.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some waiting ->
  q_pend_wait_continuation eid generation waiting ->
  os_sched_source_selected_post external platform port abi
    sg focus incoming selected node state |--
  coq_prop (sem_pend_resume_entry sg state eid incoming.(stackLeaseSlot) waiting) && TT.
Proof.
  intros * Hwaiting Hwait; unfold os_sched_source_selected_post; Intros.
  assert (Hready : sched_current_ready_at state.(TskState) state.(SchedState)
    incoming.(stackLeaseSlot) node) by tauto.
  destruct Hready as [Hnode [Hcurrent [Hpriority [Hmember Heffective]]]].
  assert (node = waiting) by congruence; subst node.
  destruct (q_pend_ready_resume_registration eid generation waiting Hwait Heffective)
    as [Hregistration _].
  unfold UCOS2_inv; Intros.
  unfold sem_pend_resume_entry; entailer!; intros ? ?; exact I.
Qed.

Lemma q_pend_wait_selected_modular_return : forall environment critical sg original initial
  observed eid timeout waiting call before returned after,
  (forall action, critical.(critical_region_clients) action -> q_pend_projected_source_client action) ->
  q_pend_wait_selected_at sg original initial observed eid timeout waiting call before ->
  sem_pend_modular_call_history environment critical sg call before returned after ->
  sem_pend_save_rely sg before after ->
  q_pend_wait_selected_at sg original initial observed eid timeout waiting returned after.
Proof.
  intros * Hclients [Hwait [old [Hvalid [Hcurrent [Hold [Hregistration Hready]]]]]]
    Hhistory [_ [_ [_ Hready_rely]]].
  pose proof (q_pend_wait_at_modular_return environment critical sg original initial
    observed eid timeout waiting call before returned after Hclients Hvalid Hwait Hhistory) as Hwait'.
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
  eapply q_pend_selected_from_ready_current; [exact Hwait'|exact Hvalid'|exact Hcurrent'|].
  apply Hready_rely; assumption.
Qed.

(** Only the pure wait index is Queue-specific. The owned world, saved
    local family, active stack lease, unmap table, and normal-return
    platform observation are exactly the established generic interfaces.
    The sem_pend_* resource/rely names below do not contain PendSem. *)
Definition q_pend_sched_save_observation environment critical sg original before returned acquired : Prop :=
  task_tcb_init_stack_source_preserved original before acquired /\
  sem_pend_modular_call_history environment critical sg original before returned acquired.

(** The actual three call edges of this Scheduler instance. This is only
    an observation of the already established modular Save/body/Restore
    relations, not another execution history or a promise of return. *)
Definition q_pend_sched_return (environment : option TaskStackCallEnvironment)
  critical sg original before returned after : Prop :=
  match environment with
  | None => False
  | Some owned => exists entered acquired resumed released,
      sem_pend_modular_call_history owned critical sg original before entered acquired /\
      os_sched_c_return owned.(task_stack_call_external) critical sg acquired entered resumed released /\
      sem_pend_modular_call_history owned critical sg resumed released returned after
  end.

Definition q_pend_continuation_phase_sched_input phase external platform environment critical saved_local
  sg call mask before : Assertion :=
  coq_prop (q_pend_restore_phase_pre phase environment critical sg call mask before /\
    match environment with None => True | Some owned => q_pend_sched_clients owned critical end) &&
  sem_pend_continuation_sched_input external platform environment saved_local sg call mask before.

Definition q_pend_continuation_phase_sched_output phase external platform environment critical saved_local
  sg call mask (before : UCOS2_Verify_State) : Assertion :=
  match phase with
  | QueuePendWaitPhase original initial_mask initial observed eid timeout waiting =>
      EX returned current,
        coq_prop (kernel_stack_call_same_call returned call /\
          q_pend_wait_selected_at sg original initial observed eid timeout waiting returned current /\
          q_pend_sched_return environment critical sg call before returned current) &&
        (sem_pend_continuation_save_input external platform environment critical saved_local sg returned mask current **
          unmap_table_rep sg)
  end.

Definition q_pend_sched_save_input phase environment critical saved_local sg call mask state : Assertion :=
  coq_prop (q_pend_sched_clients environment critical /\
    q_pend_restore_phase_pre phase (Some environment) critical sg call mask state) &&
  (task_tcb_init_continuation_save_input environment critical saved_local sg call mask state ** unmap_table_rep sg).

Definition q_pend_sched_save_output phase environment critical saved_local sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (task_tcb_init_stack_same_call returned original /\ interrupt_saved_value mask saved /\
      q_pend_sched_save_observation environment critical sg original before returned acquired /\
      q_pend_sched_clients environment critical /\
      q_pend_restore_phase_pre phase (Some environment) critical sg returned mask acquired) &&
    (task_tcb_init_continuation_restore_input environment critical saved_local sg returned saved acquired acquired **
      unmap_table_rep sg).

Definition q_pend_sched_restore_input phase environment critical saved_local sg call saved acquired released : Assertion :=
  match phase with
  | QueuePendWaitPhase original mask initial observed eid timeout waiting =>
      coq_prop (q_pend_wait_selected_at sg original initial observed eid timeout waiting call released) &&
      (task_tcb_init_continuation_restore_input environment critical saved_local sg call saved acquired released **
        unmap_table_rep sg)
  end.

Definition q_pend_sched_restore_output phase environment critical saved_local sg call saved
  (released : UCOS2_Verify_State) : Assertion :=
  match phase with
  | QueuePendWaitPhase original mask initial observed eid timeout waiting =>
      EX returned current,
        coq_prop (kernel_stack_call_same_call returned call /\
          q_pend_wait_selected_at sg original initial observed eid timeout waiting returned current /\
          sem_pend_modular_call_history environment critical sg call released returned current) &&
        (task_tcb_init_continuation_save_input environment critical saved_local sg returned
          (armv7a_irq_fiq_mask saved) current ** unmap_table_rep sg)
  end.

Definition q_pend_sched_switch_output phase environment critical saved_local sg call saved acquired entry : Assertion :=
  EX returned current,
    coq_prop (os_sched_c_return environment.(task_stack_call_external) critical sg entry call returned current /\
      UCOS2_state_inv sg current) &&
    q_pend_sched_restore_input phase environment critical saved_local sg returned saved acquired current.

Definition q_pend_sched_switch_input phase environment critical saved_local sg call mask saved acquired entry : Assertion :=
  coq_prop (q_pend_sched_clients environment critical /\ interrupt_saved_value mask saved /\
    UCOS2_state_inv sg entry /\
    q_pend_restore_phase_pre phase (Some environment) critical sg call mask entry) &&
  os_sched_continuation_switch_pre environment critical saved_local kernel_program_inv sg call saved acquired entry.

Lemma q_pend_sched_call_save_input : forall environment critical saved_local sg original initial_mask initial
  observed eid timeout waiting call mask before,
  q_pend_continuation_phase_sched_input (QueuePendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
    critical saved_local sg call mask before |--
  coq_prop (os_sched_call_cut sg call before) &&
  q_pend_sched_save_input (QueuePendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment critical saved_local sg call mask before.
Proof.
  intros; unfold q_pend_continuation_phase_sched_input.
  cbn [sem_pend_continuation_sched_input].
  unfold os_sched_continuation_pre; Intros.
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_save_input_closed_world
    environment critical saved_local sg call mask before)).
  unfold q_pend_sched_save_input; unfold q_pend_restore_phase_pre in *.
  unfold sem_pend_wait_sched_entry in *; entailer!.
Qed.

Lemma q_pend_sched_modular_save_output : forall environment critical saved_local sg original initial_mask initial
  observed eid timeout waiting call mask saved before,
  q_pend_sched_clients environment critical -> kernel_tcb_stack_field_layout sg -> UCOS2_state_inv sg before ->
  q_pend_restore_phase_pre (QueuePendWaitPhase original initial_mask initial observed eid timeout waiting)
    (Some environment) critical sg call mask before ->
  kernel_call_modular_save_post environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) critical sem_pend_blocking_rely
    sg call mask saved before |--
  q_pend_sched_save_output (QueuePendWaitPhase original initial_mask initial observed eid timeout waiting)
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
  pose proof (q_pend_wait_at_modular_return _ _ _ _ _ _ _ _ _ _ _ _ _
    (proj1 Hclients) Hvalid Hwait Hhistory) as Hwait'.
  pose proof (sem_pend_wait_sched_entry_modular_return environment critical sg call before returned acquired
    Hlayout Hvalid (proj1 (proj2 (proj2 Hentry))) Hentry Hhistory Hrely) as Hentry'.
  assert (Hpreserved : task_tcb_init_stack_source_preserved call before acquired).
  { eapply task_tcb_init_stack_registered_source_preserved; [exact Hvalid|exact (proj1 Hnormal)|exact Htrace]. }
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_restore_input_masked_world
    environment critical saved_local sg returned saved acquired acquired)).
  unfold q_pend_sched_save_output; Exists returned acquired.
  unfold q_pend_restore_phase_pre, q_pend_sched_save_observation; entailer!.
Qed.

(** Readiness on the switching branch must be supplied by the ACTUAL
    selected C endpoint (see q_pend_selected_source_resume_entry), not
    by the architecture token or by promising that the call will return.
    This same endpoint condition is used by the already delivered Sem
    Scheduler; the common body/resource interface is left unchanged. *)
Lemma q_pend_sched_modular_switch_output : forall environment critical saved_local sg original initial_mask initial
  observed eid timeout waiting call mask saved acquired entry,
  q_pend_sched_clients environment critical -> UCOS2_state_inv sg entry ->
  q_pend_restore_phase_pre (QueuePendWaitPhase original initial_mask initial observed eid timeout waiting)
    (Some environment) critical sg call mask entry ->
  (forall returned current,
    os_sched_c_return environment.(task_stack_call_external) critical sg entry call returned current ->
    os_sched_requests_switch entry = true ->
    q_pend_wait_state original eid current /\
    In call.(os_sched_call_stack).(stackLeaseSlot) current.(SchedState).(readyList)) ->
  os_sched_continuation_body_post environment critical saved_local kernel_program_inv sg call saved acquired entry |--
  q_pend_sched_switch_output (QueuePendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment critical saved_local sg call saved acquired entry.
Proof.
  intros * Hclients Hvalid [Hmask [Hwait Hentry]] Hready.
  sep_apply_l_atomic (os_sched_continuation_body_restore_input environment critical saved_local sg call saved acquired entry).
  Intros returned current.
  assert (Hbody : os_sched_c_return environment.(task_stack_call_external) critical sg entry call returned current) by tauto.
  assert (Hvalid' : UCOS2_state_inv sg current) by tauto.
  pose proof (q_pend_sched_body_selected _ _ _ _ _ _ _ _ _ _ _ _ _
    Hclients Hwait Hentry Hvalid Hvalid' Hbody (Hready returned current Hbody)) as Hselected.
  unfold q_pend_sched_switch_output; Exists returned current.
  cbn [q_pend_sched_restore_input]; entailer!.
Qed.

Lemma q_pend_sched_nonswitch_selected : forall environment critical sg original initial_mask initial
  observed eid timeout waiting call mask entry,
  q_pend_sched_clients environment critical -> UCOS2_state_inv sg entry ->
  q_pend_restore_phase_pre (QueuePendWaitPhase original initial_mask initial observed eid timeout waiting)
    (Some environment) critical sg call mask entry ->
  os_sched_requests_switch entry = false ->
  q_pend_wait_selected_at sg original initial observed eid timeout waiting call (os_sched_prefix_state entry).
Proof.
  intros * Hclients Hvalid [Hmask [Hwait Hentry]] Hswitch.
  eapply q_pend_sched_body_selected; try eassumption.
  - apply os_sched_ready_checkpoint_preserves_validity; exact Hvalid.
  - unfold os_sched_c_return; rewrite Hswitch; auto.
  - congruence.
Qed.

Lemma q_pend_sched_modular_restore_output : forall environment critical saved_local sg original initial_mask initial
  observed eid timeout waiting call saved released,
  q_pend_sched_clients environment critical ->
  q_pend_wait_selected_at sg original initial observed eid timeout waiting call released ->
  kernel_call_modular_restore_post environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) critical sem_pend_save_rely
    sg call (armv7a_irq_fiq_mask saved) released |--
  q_pend_sched_restore_output (QueuePendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment critical saved_local sg call saved released.
Proof.
  intros * Hclients Hselected.
  unfold kernel_call_modular_restore_post; Intros returned current.
  assert (Hhistory : sem_pend_modular_call_history environment critical sg call released returned current)
    by (unfold sem_pend_modular_call_history; tauto).
  pose proof (proj1 (proj2 Hhistory)) as Hsame.
  assert (Hrely : sem_pend_save_rely sg released current) by tauto.
  pose proof (q_pend_wait_selected_modular_return _ _ _ _ _ _ _ _ _ _ _ _ _
    (proj1 Hclients) Hselected Hhistory Hrely) as Hselected'.
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_save_input_closed_world
    environment critical saved_local sg returned (armv7a_irq_fiq_mask saved) current)).
  cbn [q_pend_sched_restore_output]; Exists returned current; entailer!.
Qed.

Lemma q_pend_sched_restore_output_return : forall environment critical saved_local sg original initial_mask initial
  observed eid timeout waiting context scheduled returned mask saved before entry released,
  task_tcb_init_stack_same_call scheduled context ->
  q_pend_sched_save_observation environment critical sg context before scheduled entry ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry scheduled returned released ->
  interrupt_saved_value mask saved ->
  q_pend_sched_restore_output (QueuePendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment critical saved_local sg returned saved released |--
  q_pend_continuation_phase_sched_output (QueuePendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
    critical saved_local sg context mask before.
Proof.
  intros * Hscheduled [Hpreserved Hsave_history] Hbody Hsaved.
  pose proof (os_sched_c_return_execution_identity _ _ _ _ _ _ _ Hbody) as Hreturned.
  cbn [q_pend_sched_restore_output]; Intros final current.
  assert (Hsame : kernel_stack_call_same_call final context).
  { assert (Hfinal : kernel_stack_call_same_call final returned) by tauto.
    unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence. }
  assert (Htrace : q_pend_sched_return (Some environment) critical sg context before final current).
  { exists scheduled, entry, returned, released.
    split; [exact Hsave_history|]. split; [exact Hbody|tauto]. }
  rewrite (proj2 Hsaved).
  sep_apply_l_atomic (proj2 (sem_pend_continuation_save_input_owned environment critical saved_local sg final mask current)).
  cbn [q_pend_continuation_phase_sched_output]; Exists final current; entailer!.
Qed.

(** The actual last selector of a saved Queue caller. The shared checked
    install/restore producer returns BOTH its current world and its local
    saved-SR/inside pair on one heap. Readiness is the consequence of the
    actual high-ready selector at that same cut, not a law of c_return.

    The registered C modules supply the observed [hooked] world and the
    source-transported waiter/local map. This theorem neither replays their
    code nor asserts that such a selection eventually occurs. The pure
    c_return observation in the result must describe this produced endpoint.
    No new property of ARM/BSP or arbitrary foreign clients is assumed. *)
Lemma q_pend_saved_call_selected_output : forall environment critical saved_local
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg original initial_mask initial observed eid timeout waiting call entry saved acquired
  outgoing_call outgoing hooked resumed before (frame : Assertion),
  let local := kernel_sched_saved_local_at environment.(task_stack_call_platform) critical sg
    hooked.(TskState) call saved acquired (task_create_continuation_local saved_local) in
  let resource := kernel_saved_continuation_entry environment.(task_stack_call_continuations)
    hooked.(TskState) local in
  let current := os_sched_install_context outgoing_call outgoing call.(os_sched_call_stack) hooked in
  q_pend_wait_at sg original initial observed eid timeout waiting call hooked ->
  os_sched_saved_stack_binding outgoing_call outgoing hooked ->
  os_sched_destination_binding environment.(task_stack_call_external) outgoing_call outgoing hooked
    call.(os_sched_call_stack) resumed ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key outgoing_call.(os_sched_call_stack))) ->
  (UCOS2_inv sg hooked ** task_stack_fragments_rep outgoing_call.(os_sched_call_stack).(stackLeaseRegion) outgoing **
    resource (task_stack_key outgoing_call.(os_sched_call_stack))
      (outgoing_call.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
    store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
    (armv7a_task_switch_control task_abi outgoing_call ** unmap_table_rep sg ** frame)) before ->
  exists installed selected,
    sched_install_heap_fragment sg before installed (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_stack) = call.(os_sched_call_stack) /\
    (forall restored,
      armv7a_task_restore_transition task_abi outgoing_call selected installed restored ->
      let returned := kernel_selected_call selected current in
      selected.(armv7a_continuation_call) = Some call /\ kernel_stack_call_same_call returned call /\
      (os_sched_c_return environment.(task_stack_call_external) critical sg entry call returned current ->
        (q_pend_sched_switch_output
          (QueuePendWaitPhase original initial_mask initial observed eid timeout waiting)
          environment critical saved_local sg call saved acquired entry ** frame) restored)).
Proof.
  intros environment critical saved_local task_abi sg original initial_mask initial observed eid timeout waiting
    call entry saved acquired outgoing_call outgoing hooked resumed before frame local resource current
    Hwait Hsaved Hdestination Hhigh Haddress Hcoverage Hpre.
  assert (Hvalid_hooked : UCOS2_state_inv sg hooked).
  { match type of Hpre with ?P before => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg hooked) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hpre)). }
  pose proof Hdestination as [Hhigh_slot [[node [Hnode [Hgeneration [Hhigh_priority Hrestore_source]]]] Hbinding]].
  assert (Hin : In call.(os_sched_call_stack).(stackLeaseSlot) hooked.(SchedState).(readyList)).
  { unfold sched_high_ready_consistency in Hhigh.
    destruct hooked.(SchedState).(readyList) as [|head tail]; [destruct Hhigh; congruence|].
    destruct Hhigh as [Hhead Hrest]; assert (head = call.(os_sched_call_stack).(stackLeaseSlot)) by congruence.
    subst head; left; reflexivity. }
  destruct (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid_hooked)))) _ Hin)
    as [ready_node [Hready_node [Hpriority Heffective]]].
  assert (ready_node = node) by congruence; subst ready_node.
  assert (Hready : sched_current_ready_at current.(TskState) current.(SchedState)
    call.(os_sched_call_stack).(stackLeaseSlot) node).
  { unfold sched_current_ready_at, current; change
      (hooked.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
       hooked.(SchedState).(highRdyTid) = Some call.(os_sched_call_stack).(stackLeaseSlot) /\
       hooked.(SchedState).(highRdyPrio) = Some node.(curPrio) /\
       In call.(os_sched_call_stack).(stackLeaseSlot) hooked.(SchedState).(readyList) /\
       is_effectively_ready node.(stat) node.(dly) = true); auto. }
  destruct (kernel_saved_continuation_install_source _ _ _ environment.(task_stack_call_continuations)
    task_abi sg outgoing_call outgoing hooked call.(os_sched_call_stack) resumed local before frame
    Hsaved Hdestination Haddress Hcoverage Hpre)
    as [installed [selected [Hinstall [Hreads [Hdescriptor [Hlease [Hfragments [Hcurrent [Hcovered Hrestore]]]]]]]]].
  fold current in Hcurrent, Hcovered, Hrestore.
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hlease|].
  intros restored Htask_restore returned.
  destruct (Hrestore restored Htask_restore) as [Hmemory [Hsource Howned]].
  assert (Hlocal : local selected = kernel_sched_saved_local environment.(task_stack_call_platform)
    critical sg hooked.(TskState) call saved acquired selected).
  { unfold local; apply kernel_sched_saved_local_at_selected; exact Hlease. }
  rewrite Hlocal in Howned.
  assert (Hfacts : selected.(armv7a_continuation_call) = Some call /\
    armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) = 192 /\ UCOS2_state_inv sg current).
  { match type of Howned with ?P restored => assert (Hexpose : P |-- coq_prop
      (selected.(armv7a_continuation_call) = Some call /\
       armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) = 192 /\ UCOS2_state_inv sg current) && TT) end.
    { unfold kernel_sched_saved_local, kernel_program_inv, UCOS2_inv; entailer!; try tauto; intros ? ?; exact I. }
    exact (proj1 (Hexpose restored Howned)). }
  destruct Hfacts as [Hcall [Hmask Hvalid]].
  assert (Hreturned : returned = armv7a_continuation_resumed_call selected call).
  { unfold returned, kernel_selected_call; rewrite Hcall; reflexivity. }
  assert (Hsame : kernel_stack_call_same_call returned call).
  { rewrite Hreturned; unfold kernel_stack_call_same_call, armv7a_continuation_resumed_call;
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack]; auto. }
  assert (Hwait_returned : q_pend_wait_at sg original initial observed eid timeout waiting returned current).
  { destruct Hwait as [Hsame_original [Horigin [Hobserved [Hfirst [Hactive Hwait_state]]]]].
    split; [unfold kernel_stack_call_same_call in *; intuition congruence|].
    split; [exact Horigin|]. split; [exact Hobserved|]. split; [exact Hfirst|]. split; assumption. }
  assert (Hselected : q_pend_wait_selected_at sg original initial observed eid timeout waiting returned current).
  { eapply q_pend_selected_from_ready_current; [exact Hwait_returned|exact Hvalid| |].
    - rewrite <- (proj2 (proj2 (proj1 Hwait))); exact (proj1 (proj2 Hready)).
    - rewrite <- (proj2 (proj2 (proj1 Hwait))); exact (proj1 (proj2 (proj2 (proj2 Hready)))). }
  assert (Habsent : current.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None)
    by apply task_stack_take_lookup.
  assert (Hunfocus : store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations) current.(TskState) local)
    current.(TskState).(parkedTaskStacks) |--
    store_parked_continuations (kernel_saved_continuation_entry environment.(task_stack_call_continuations)
      current.(TskState) (task_create_continuation_local saved_local)) current.(TskState).(parkedTaskStacks)).
  { unfold local; apply kernel_saved_continuation_map_unfocus_absent; exact Habsent. }
  split; [exact Hcall|]. split; [exact Hsame|]. intro Hbody.
  match type of Howned with ?P restored => assert (Hmasked : P |--
    kernel_continuation_call_masked environment.(task_stack_call_continuations)
      kernel_program_inv (task_create_continuation_local saved_local) critical sg
      (task_stack_call_active_key returned) returned saved acquired current ** frame) end.
  { sep_apply_l_atomic Hunfocus.
    unfold kernel_continuation_call_masked, kernel_continuation_inv,
      armv7a_task_restored_execution; rewrite Hcall, Hmask, Hreturned.
    unfold kernel_sched_saved_local, kernel_call_execution_owned, critical_region_masked,
      armv7a_continuation_resumed_call;
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack]; rewrite Hlease.
    entailer!.
    unfold task_stack_call_active_key; cbn [os_sched_call_origin os_sched_call_stack].
    rewrite (proj1 (proj2 (proj1 Hwait))), (proj1 (proj2 Hwait)).
    rewrite <- (proj2 (proj2 (proj1 Hwait))); exact Hcovered. }
  assert (Hclose : kernel_continuation_call_masked environment.(task_stack_call_continuations)
      kernel_program_inv (task_create_continuation_local saved_local) critical sg
      (task_stack_call_active_key returned) returned saved acquired current ** frame |--
    q_pend_sched_switch_output
      (QueuePendWaitPhase original initial_mask initial observed eid timeout waiting)
      environment critical saved_local sg call saved acquired entry ** frame).
  { sep_apply_l_atomic (proj2 (task_tcb_init_continuation_restore_input_masked_world
      environment critical saved_local sg returned saved acquired current)).
    unfold q_pend_sched_switch_output; Exists returned current.
    cbn [q_pend_sched_restore_input]; entailer!. }
  exact (Hclose restored (Hmasked restored Howned)).
Qed.

