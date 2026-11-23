Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.event_wait Ucos2Verify.lib.event Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.task_retirement.
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
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The same native registration stages as EventTaskWait/Remove, now with
    the source's PendQ bit and actual message. In particular expiry does NOT remove the
    ECB link; a real Post/Del wake may still overwrite its pending result.
    No future return, ownership transfer, or readiness is asserted here. *)
Definition q_pend_wait_continuation eid generation (node : TaskAbstractState) : Prop :=
  node.(taskGeneration) = generation /\ node.(eventMultiWaitEvents) = [] /\
  node.(tcbFlagNode) = 0 /\
  ((node.(eventPtr) = Some eid /\ task_linked_wait_phase node PendQ) \/
   (node.(eventPtr) = None /\ task_non_suspension_bits node.(stat) = 0 /\
    node.(statPend) <> PendTimeout)).

Lemma q_pend_wait_establishes_continuation : forall eid node timeout,
  is_effectively_ready node.(stat) node.(dly) = true ->
  node.(eventMultiWaitEvents) = [] -> node.(tcbFlagNode) = 0 ->
  q_pend_wait_continuation eid node.(taskGeneration)
    (task_set_event_ptr (task_prepare_event_wait node PendQ timeout) (Some eid)).
Proof.
  intros eid node timeout Hready Hmulti Hflag.
  split; [reflexivity|]. split; [exact Hmulti|]. split; [exact Hflag|].
  left; split; [reflexivity|]. left.
  apply task_prepare_event_wait_pending_bits.
  apply task_effectively_ready_has_no_pending; exact Hready.
Qed.

Lemma q_pend_wait_fields_preserve_continuation : forall eid generation before after,
  sem_pend_wait_fields_equal before after ->
  q_pend_wait_continuation eid generation before ->
  q_pend_wait_continuation eid generation after.
Proof.
  intros eid generation before after [Hid [Hg [Hs [Hp [Hd [He [Hm Hf]]]]]]].
  unfold q_pend_wait_continuation, task_linked_wait_phase.
  rewrite Hg, Hs, Hp, Hd, He, Hm, Hf; trivial.
Qed.

Lemma q_pend_tick_preserves_continuation : forall eid generation node,
  q_pend_wait_continuation eid generation node ->
  q_pend_wait_continuation eid generation (tick_task_update node).
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

Lemma q_pend_wake_preserves_continuation : forall eid generation node message result,
  result <> PendTimeout -> q_pend_wait_continuation eid generation node ->
  q_pend_wait_continuation eid generation (task_event_wake_single node PendQ message result).
Proof.
  intros eid generation node message result Hresult [Hg [Hm [Hf Hphase]]].
  split; [exact Hg|]. split; [exact Hm|]. split; [exact Hf|].
  right; split; [reflexivity|]. split; [|exact Hresult].
  destruct Hphase as [[Hptr Hlinked]|[Hptr [Hclear Hprevious]]].
  - exact (proj2 (task_event_wake_single_clears_registration node PendQ message result Hlinked)).
  - change (task_non_suspension_bits (task_clear_pending_status node.(stat) PendQ) = 0).
    rewrite task_clear_pending_status_none by exact Hclear; exact Hclear.
Qed.

Lemma q_pend_ready_resume_registration : forall eid generation node,
  q_pend_wait_continuation eid generation node ->
  is_effectively_ready node.(stat) node.(dly) = true ->
  q_pend_resume_registration eid node /\ node.(taskGeneration) = generation.
Proof.
  intros eid generation node [Hg [Hm [Hf Hphase]]] Hready.
  split; [|exact Hg]. split; [exact Hm|]. split; [exact Hf|].
  destruct Hphase as [[Hptr [Hpending|[Hclear [Htimeout Hdelay]]]]|[Hptr [Hclear Hresult]]].
  - pose proof (task_effectively_ready_has_no_pending node Hready) as Hnone.
    rewrite Hnone in Hpending; discriminate.
  - rewrite Htimeout; exact Hptr.
  - destruct node.(statPend); exact Hptr || contradiction.
Qed.

Definition q_pend_wait_state original eid (state : UCOS2_Verify_State) : Prop :=
  exists node,
    state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
    q_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) node.

(** A checked C-module obligation for the EXISTING registry. Only this
    actual active invocation is observed, on a foreign, nonstopping edge.
    In particular TaskDel may remove another Queue waiter, and may stop
    this invocation on a nonreturning path. Neither case is silently
    excluded by requiring every ghost waiter to survive every action. *)
Definition q_pend_projected_source_client (action : KernelClientAction) : Prop :=
  forall sg before after original eid,
    UCOS2_state_inv sg before ->
    original.(os_sched_call_origin) = RunningInvocation
      original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
    task_invocation_active before.(TskState) original.(os_sched_call_invocation)
      original.(os_sched_call_origin) ->
    kernel_client_actor action <> Some original.(os_sched_call_invocation) ->
    kernel_client_stops action original.(os_sched_call_invocation) = false ->
    kernel_client_step action sg before after -> q_pend_wait_state original eid before ->
    q_pend_wait_state original eid after.

Lemma q_pend_task_frame_preserves_wait_state : forall original eid before after,
  after.(TskState).(inUsedTaskStates) = before.(TskState).(inUsedTaskStates) ->
  q_pend_wait_state original eid before -> q_pend_wait_state original eid after.
Proof. intros original eid before after Hmap [node [Hnode Hwait]]; exists node; rewrite Hmap; auto. Qed.

Lemma q_pend_task_update_preserves_wait_state : forall original eid before selected previous next,
  before.(TskState).(inUsedTaskStates) selected = Some previous ->
  (q_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) previous ->
   q_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) next) ->
  q_pend_wait_state original eid before ->
  q_pend_wait_state original eid (replace_TskS (glob_task_set_usedtask before.(TskState) selected next) before).
Proof.
  intros original eid before selected previous next Hprevious Hstep [node [Hnode Hwait]].
  unfold q_pend_wait_state; cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
  destruct (Z.eqb original.(os_sched_call_stack).(stackLeaseSlot) selected) eqn:E.
  - apply Z.eqb_eq in E; rewrite E in Hnode; assert (node = previous) by congruence; subst node.
    exists next; split; [reflexivity|apply Hstep; exact Hwait].
  - exists node; auto.
Qed.

Lemma q_pend_event_wake_preserves_wait_state : forall sg original eid before event_id event selected previous message result,
  before.(TskState).(inUsedTaskStates) selected = Some previous -> result <> PendTimeout ->
  q_pend_wait_state original eid before ->
  q_pend_wait_state original eid (event_wake_state sg before event_id event selected previous PendQ message result).
Proof.
  intros; eapply q_pend_task_update_preserves_wait_state; try eassumption.
  apply q_pend_wake_preserves_continuation; assumption.
Qed.

Lemma q_pend_tick_step_preserves_wait_state : forall sg original eid before selected previous,
  before.(TskState).(inUsedTaskStates) selected = Some previous ->
  q_pend_wait_state original eid before ->
  q_pend_wait_state original eid (tick_task_step sg selected previous before).
Proof.
  intros; unfold q_pend_wait_state in *; rewrite tick_task_step_task_state_eq by assumption.
  change (q_pend_wait_state original eid
    (replace_TskS (glob_task_set_usedtask before.(TskState) selected (tick_task_update previous)) before)).
  eapply q_pend_task_update_preserves_wait_state; [eassumption| |eassumption].
  apply q_pend_tick_preserves_continuation.
Qed.

Lemma q_pend_save_sp_preserves_wait_state : forall original eid before selected sp,
  q_pend_wait_state original eid before ->
  q_pend_wait_state original eid (os_sched_save_current_sp before selected sp).
Proof.
  intros original eid before selected sp Hwait; unfold os_sched_save_current_sp.
  destruct (before.(TskState).(inUsedTaskStates) selected) as [previous|] eqn:Hprevious.
  - eapply q_pend_task_update_preserves_wait_state; [exact Hprevious| |exact Hwait].
    apply q_pend_wait_fields_preserve_continuation; repeat split; reflexivity.
  - exact Hwait.
Qed.

Lemma q_pend_client_trace_preserves_wait_state : forall clients sg original eid event_observer before stopped after,
  (forall action, clients action -> KernelClientCertificate action) ->
  (forall action, clients action -> q_pend_projected_source_client action) ->
  kernel_client_resource_trace clients sg original.(os_sched_call_invocation) event_observer before stopped after ->
  stopped = false -> UCOS2_state_inv sg before ->
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active before.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  q_pend_wait_state original eid before ->
  UCOS2_state_inv sg after /\
  task_invocation_active after.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
  q_pend_wait_state original eid after.
Proof.
  intros clients sg original eid event_observer before stopped after Hcert Hclients Htrace.
  induction Htrace as [entry|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intros Hnormal Hvalid Horigin Hactive Hwait; [auto|].
  apply Bool.orb_false_iff in Hnormal; destruct Hnormal as [Hstop Htailstop].
  pose proof (Hcert action Hin) as Hcertificate.
  apply IH; [exact Htailstop| |exact Horigin| |].
  - eapply kernel_client_preserves_validity; eassumption.
  - eapply kernel_client_preserves_continuation; eassumption.
  - eapply Hclients; eassumption.
Qed.

Lemma q_pend_source_trace_preserves_wait_state : forall external port critical sg original eid event_observer
  first before stopped last after,
  (forall action, critical.(critical_region_clients) action -> q_pend_projected_source_client action) ->
  kernel_resumption_task_source_trace external port critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) event_observer first before stopped last after ->
  stopped = false -> UCOS2_state_inv sg before ->
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active before.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  q_pend_wait_state original eid before ->
  UCOS2_state_inv sg after /\
  task_invocation_active after.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
  q_pend_wait_state original eid after.
Proof.
  intros * Hclients Htrace Hnormal Hvalid Horigin Hactive Hwait.
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace) as [Hresources _].
  eapply q_pend_client_trace_preserves_wait_state; try eassumption.
  - exact critical.(critical_region_client_certificates).
  - apply kernel_resumption_resource_trace_erases; exact Hresources.
Qed.

Definition q_pend_projected_hook_client (action : KernelClientAction) : Prop :=
  forall sg before after original eid,
    UCOS2_state_inv sg before ->
    original.(os_sched_call_origin) = RunningInvocation
      original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
    task_invocation_active before.(TskState) original.(os_sched_call_invocation)
      original.(os_sched_call_origin) ->
    kernel_client_stops action original.(os_sched_call_invocation) = false ->
    kernel_client_step action sg before after -> q_pend_wait_state original eid before ->
    q_pend_wait_state original eid after.

Definition q_pend_sched_clients environment critical : Prop :=
  (forall action, critical.(critical_region_clients) action -> q_pend_projected_source_client action) /\
  q_pend_projected_hook_client environment.(task_stack_call_external).(os_sched_hook_action).

(** The actual retirement map repairs neighbours' links, but preserves
    every other live waiter's fields. The selected slot is genuinely gone;
    its invocation belongs to the stopped branch, not a normal Pend return. *)
Lemma q_pend_other_task_recycle_preserves_wait_state : forall sg original eid state tid priority node name,
  original.(os_sched_call_stack).(stackLeaseSlot) <> tid ->
  q_pend_wait_state original eid state ->
  q_pend_wait_state original eid
    (replace_TskS (task_recycle sg state.(TskState) tid priority node name) state).
Proof.
  intros * Hdifferent [old [Hold Hwait]].
  destruct (task_unlink_used_map_preserves_other_fields state.(TskState).(inUsedTaskStates)
    tid node original.(os_sched_call_stack).(stackLeaseSlot) old Hdifferent Hold)
    as [current [Hcurrent Hfields]].
  exists current; split; [exact Hcurrent|].
  eapply q_pend_wait_fields_preserve_continuation; [|exact Hwait].
  unfold sem_pend_wait_fields_equal; repeat split;
    match goal with |- ?field current = ?field old => exact (f_equal field Hfields) end.
Qed.

Lemma q_pend_recycled_task_has_no_wait_state : forall sg original eid state priority node name,
  ~ q_pend_wait_state original eid
    (replace_TskS (task_recycle sg state.(TskState)
      original.(os_sched_call_stack).(stackLeaseSlot) priority node name) state).
Proof.
  intros * [current [Hcurrent Hwait]].
  change (task_unlink_used_map state.(TskState).(inUsedTaskStates)
    original.(os_sched_call_stack).(stackLeaseSlot) node
    original.(os_sched_call_stack).(stackLeaseSlot) = Some current) in Hcurrent.
  unfold task_unlink_used_map in Hcurrent; destruct Z.eq_dec; congruence.
Qed.

Lemma q_pend_event_task_rdy_preserves_wait_state : forall sg original eid state event_id message result priority after,
  event_task_rdy sg state event_id PendQ message result = Some (priority, after) -> result <> PendTimeout ->
  q_pend_wait_state original eid state -> q_pend_wait_state original eid after.
Proof.
  intros * Hstep Hresult Hwait; unfold event_task_rdy in Hstep.
  destruct (state.(EventState).(inUsedEventStates) event_id) as [event|]; [|discriminate].
  destruct (state.(TskState).(prioTbl) (event_wait_priority state.(TskState) event)) as [| |selected]; try discriminate.
  destruct (state.(TskState).(inUsedTaskStates) selected) as [previous|] eqn:Hselected; [|discriminate].
  injection Hstep as Hpriority Hafter; subst after.
  eapply q_pend_event_wake_preserves_wait_state; eassumption.
Qed.

Lemma q_pend_event_broadcast_preserves_wait_state : forall sg original eid event_id message result state priorities after,
  event_broadcast sg event_id PendQ message result state priorities after -> result <> PendTimeout ->
  q_pend_wait_state original eid state -> q_pend_wait_state original eid after.
Proof.
  intros sg original eid event_id message result state priorities after Hloop Hresult.
  induction Hloop as [state event He Hempty|
    state event priority middle priorities after He Hnonempty Hstep Htail IH]; intros Hwait.
  - exact Hwait.
  - apply IH; eapply q_pend_event_task_rdy_preserves_wait_state; eassumption.
Qed.

