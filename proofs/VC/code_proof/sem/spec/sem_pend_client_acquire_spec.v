Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.Lists.List Coq.micromega.Lia.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.lib.kernel_runtime_inv.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_acquire_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_sched_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_acquire_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Import TaskStateDef ListNotations.
Local Open Scope Z_scope.

(** Acquisition observations for the actual client-level return. The
    Event incarnation and actual saved word are retained; no public Timer
    image trace or old full Save history is required. This is a new local
    interface and is not identified with the old acquire observation. *)
Definition sem_pend_client_acquire_observation environment critical sg original returned
  mask saved before acquired eid observed current : Prop :=
  sem_pend_client_return_source environment critical sg original before returned acquired /\
  kernel_stack_call_same_call returned original /\ interrupt_saved_value mask saved /\
  UCOS2_state_inv sg acquired /\ mutex_query_lookup before eid observed /\
  mutex_query_lookup acquired eid current /\ observed.(eventType) = OS_EVENT_TYPE_SEM /\
  current.(eventType) = OS_EVENT_TYPE_SEM /\ current.(eventGeneration) = observed.(eventGeneration).

Lemma sem_pend_client_return_source_preserves_task_source :
  forall environment critical sg call before returned after,
  sem_pend_client_return_source environment critical sg call before returned after ->
  UCOS2_state_inv sg before -> kernel_call_task_source call before ->
  kernel_call_task_source call after.
Proof.
  intros environment critical sg call before returned after Hreturn Hvalid [Horigin [Hactive Hcurrent]].
  destruct (sem_pend_client_return_source_traces environment critical sg call before returned after Hreturn)
    as [Hresources Hcontrol].
  destruct (sem_pend_observed_client_trace_resources _ _ _ _ _ _ _ _ _ _ _
    critical.(critical_region_client_certificates) Hresources Hvalid) as [_ [_ [_ Hlive]]].
  destruct (sem_pend_client_return_source_same_call environment critical sg call before returned after Hreturn)
    as [Hi [Ho Hstack]].
  split; [exact Horigin|]. split.
  - exact (Hlive eq_refl call.(os_sched_call_origin) Hactive).
  - rewrite <- Ho; exact (Hcontrol Hcurrent).
Qed.

Lemma sem_pend_client_return_source_save_observation :
  forall environment critical sg call before returned acquired mask saved,
  sem_pend_client_return_source environment critical sg call before returned acquired ->
  interrupt_saved_value mask saved ->
  sem_pend_stack_save_observation critical sg call returned (Some environment) mask saved before acquired.
Proof.
  intros environment critical sg call before returned acquired mask saved Hreturn Hsaved.
  split; [eapply sem_pend_client_return_source_same_call; exact Hreturn|].
  split; [exact Hsaved|intros Hnone; discriminate].
Qed.

Lemma sem_pend_client_return_source_restore_observation :
  forall environment critical sg call released returned current,
  sem_pend_client_return_source environment critical sg call released returned current ->
  sem_pend_stack_restore_observation sg call returned (Some environment) released current.
Proof.
  intros environment critical sg call released returned current Hreturn.
  pose proof (sem_pend_client_return_source_same_call environment critical sg call released returned current Hreturn)
    as Hsame.
  split; [exact Hsame|]. intros Hvalid Hsource.
  apply (proj2 (task_tcb_init_stack_same_call_source_iff returned call current Hsame)).
  eapply sem_pend_client_return_source_preserves_task_source; eassumption.
Qed.

Lemma sem_pend_client_return_source_preserves_sem_handle :
  forall environment critical sg call before returned acquired eid previous,
  sem_pend_client_return_source environment critical sg call before returned acquired ->
  mutex_query_handle_protocol critical sg call.(os_sched_call_invocation) eid ->
  UCOS2_state_inv sg before -> mutex_query_lookup before eid previous ->
  previous.(eventType) = OS_EVENT_TYPE_SEM ->
  exists current, mutex_query_lookup acquired eid current /\
    current.(eventGeneration) = previous.(eventGeneration) /\ current.(eventType) = previous.(eventType).
Proof.
  intros environment critical sg call before returned acquired eid previous [Htrace Hnormal] Hprotocol Hvalid Hlookup Hsem.
  eapply sem_pend_observed_client_trace_sem_handle; eassumption.
Qed.

(** The old handle protocol already ranges over each real registered
    action. Its raw Event projection can be consumed directly, without
    rebuilding a critical_region_interval and its Timer requirement. *)
Lemma sem_pend_client_acquire_observation_from_input :
  forall environment critical sg call returned pevent eid observed mask saved before acquired,
  sem_pend_client_return_source environment critical sg call before returned acquired ->
  UCOS2_state_inv sg before ->
  sem_pend_call_input critical sg call.(os_sched_call_invocation) pevent before eid observed ->
  pevent <> 0 ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  interrupt_saved_value mask saved ->
  exists current, sem_pend_client_acquire_observation environment critical sg call returned
    mask saved before acquired eid observed current.
Proof.
  intros environment critical sg call returned pevent eid observed mask saved before acquired
    Hreturn Hvalid Hinput Hnonnull Hclear Hsaved.
  destruct Hinput as [Hzero|[_ [Haddress [Hid [Hslot Hprotocol]]]]]; [contradiction|].
  assert (Hguards : event_slot_type_value before.(EventState) eid = 3 /\
    before.(IntrState).(intNesting) <= 0 /\ before.(IntrState).(lockNesting) <= 0).
  { change ((if negb (Z.eqb (event_slot_type_value before.(EventState) eid) 3)
      then Some OS_ERR_EVENT_TYPE else
      if Z.ltb 0 before.(IntrState).(intNesting) then Some OS_ERR_PEND_ISR else
      if Z.ltb 0 before.(IntrState).(lockNesting) then Some OS_ERR_PEND_LOCKED else None) = None) in Hclear.
    destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 3) eqn:Htype in Hclear;
      cbn [negb] in Hclear; [|discriminate].
    destruct (Z.ltb 0 before.(IntrState).(intNesting)) eqn:Hint in Hclear; [discriminate|].
    destruct (Z.ltb 0 before.(IntrState).(lockNesting)) eqn:Hlock in Hclear; [discriminate|].
    apply Z.eqb_eq in Htype; apply Z.ltb_ge in Hint; apply Z.ltb_ge in Hlock; auto. }
  destruct Hguards as [Htype [Hint Hlock]].
  specialize (Hprotocol Htype Hint Hlock).
  destruct (sem_query_public_slot_is_sem before eid observed Hslot Htype) as [Hlookup Hsem].
  destruct (sem_pend_client_return_source_preserves_sem_handle environment critical sg call before returned acquired
    eid observed Hreturn Hprotocol Hvalid Hlookup Hsem) as [current [Hcurrent [Hgeneration Htype']]].
  pose proof (sem_pend_client_return_source_preserves_validity environment critical sg call before returned acquired
    Hreturn Hvalid) as Hvalid'.
  pose proof (sem_pend_client_return_source_same_call environment critical sg call before returned acquired Hreturn)
    as Hsame.
  exists current; unfold sem_pend_client_acquire_observation; repeat first [assumption | split | congruence].
Qed.

Lemma sem_pend_client_return_source_preserves_call_stage :
  forall environment critical sg call before returned acquired,
  sem_pend_client_return_source environment critical sg call before returned acquired ->
  UCOS2_state_inv sg before -> sem_pend_task_call_stage sg call before ->
  sem_pend_save_rely sg before acquired -> sem_pend_task_call_stage sg call acquired.
Proof.
  intros environment critical sg call before returned acquired Hreturn Hvalid Hstage
    [Hcontrol [Hruntime [Hcache_rely Hready_rely]]].
  pose proof Hstage as [Hsource [Hrunning [old [Hready [Hg [Hnonidle Hnone]]]]]].
  pose proof (sem_pend_client_return_source_preserves_validity environment critical sg call before returned acquired
    Hreturn Hvalid) as Hvalid'.
  assert (Hfields : sem_pend_source_call_fields sg call before).
  { split; [exact Hrunning|]. split.
    - exists old; split; [exact (proj1 Hready)|]. split; assumption.
    - exists old; split; [exact (proj1 Hready)|exact Hnone]. }
  destruct (sem_pend_client_return_source_preserves_call_fields environment critical sg call before returned acquired
    Hreturn Hvalid Hsource Hfields)
    as [Hrunning' [[nonidle [Hnonidle_node [Hnonidle_gen Hnonidle']]] [node [Hnode Hnone']]]].
  assert (nonidle = node) by congruence; subst nonidle.
  pose proof (sem_pend_client_return_source_preserves_task_source environment critical sg call before returned acquired
    Hreturn Hvalid Hsource) as Hsource'.
  destruct (kernel_call_task_source_current_at call acquired Hsource') as [Hcurrent [found [Hfound Hgen]]].
  assert (found = node) by congruence; subst found.
  assert (Hmember : In call.(os_sched_call_stack).(stackLeaseSlot) acquired.(SchedState).(readyList)).
  { apply Hready_rely; [exact (proj1 (proj2 Hready))|exact (proj1 (proj2 (proj2 (proj2 Hready))))]. }
  pose proof (Hcache_rely (sched_current_ready_at_implies_current_consistency _ _ _ _ Hready)) as Hcache.
  unfold sched_current_consistency in Hcache; rewrite Hcurrent in Hcache.
  destruct Hcache as [cached [Hcached Hpriority]].
  assert (cached = node) by congruence; subst cached.
  destruct (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid')))) _ Hmember)
    as [ready_node [Hready_node [_ Heffective]]].
  assert (ready_node = node) by congruence; subst ready_node.
  assert (Hready' : sched_current_ready_at acquired.(TskState) acquired.(SchedState)
    call.(os_sched_call_stack).(stackLeaseSlot) node) by (repeat split; assumption).
  split; [exact Hsource'|]. split; [exact Hrunning'|]. exists node; auto.
Qed.

(** This is the actual Task alternative of admission. Positive-count
    callers need only the acquired Event fields; they are not required to
    supply this Task stage. The old narrower nonblocking quantifier cannot
    be used to rule out a new client-level zero-count execution. *)
Lemma sem_pend_client_save_blocking_call_stage :
  forall environment critical sg call before returned acquired,
  sem_pend_client_return_source environment critical sg call before returned acquired ->
  UCOS2_state_inv sg before -> sem_pend_task_call_stage sg call before ->
  kernel_running_idle_ready sg before -> kernel_call_stack_available call before ->
  before.(IntrState).(intNesting) <= 0 -> before.(IntrState).(lockNesting) <= 0 ->
  interrupt_in_range acquired.(IntrState) -> sem_pend_save_rely sg before acquired ->
  sem_pend_task_call_stage sg call acquired /\ sem_pend_blocking_call_stage sg call acquired.
Proof.
  intros environment critical sg call before returned acquired Hreturn Hvalid Hstage Hruntime Havailable
    Hint Hlock Hrange Hrely.
  pose proof (sem_pend_client_return_source_preserves_call_stage environment critical sg call before returned acquired
    Hreturn Hvalid Hstage Hrely) as Hstage'.
  split; [exact Hstage'|].
  destruct Hrely as [[Hrunning Hcounters] [Hruntime_rely [Hcache Hready]]].
  assert (Hidle : task_idle_ready sg acquired.(TskState)).
  { apply (Hruntime_rely Hruntime); exact (proj1 (proj2 Hstage')). }
  destruct Hreturn as [Htrace Hnormal].
  assert (Havailable' : kernel_call_stack_available call acquired).
  { pose proof (proj2 Hnormal Havailable) as Hreturned.
    unfold kernel_call_stack_available in *; rewrite (proj1 (proj2 (proj1 Hnormal))) in Hreturned;
      exact Hreturned. }
  unfold sem_pend_blocking_call_stage; split; [exact Hidle|]. split; [exact Havailable'|].
  unfold interrupt_in_range in Hrange; rewrite Hcounters in Hrange.
  rewrite Hcounters; lia.
Qed.

Lemma sem_pend_client_acquire_wait_entry :
  forall environment critical sg call returned mask saved before acquired eid observed current,
  sem_pend_client_acquire_observation environment critical sg call returned
    mask saved before acquired eid observed current ->
  sem_pend_task_call_stage sg call acquired -> encode_event_cnt_value current = 0 ->
  event_object_layout_prop sg eid ->
  exists node,
    sem_pend_wait_entry sg acquired eid current call.(os_sched_call_stack).(stackLeaseSlot) node /\
    call.(os_sched_call_origin) = RunningInvocation call.(os_sched_call_stack).(stackLeaseSlot) node.(taskGeneration) /\
    kernel_call_task_source call acquired /\ sched_current_consistency acquired.(TskState) acquired.(SchedState).
Proof.
  intros environment critical sg call returned mask saved before acquired eid observed current
    [Hreturn [Hsame [Hsaved [Hvalid [Hlookup_before [Hlookup [Htype_before [Htype Hgeneration]]]]]]]]
    Hstage Hzero Hlayout.
  eapply sem_pend_task_stage_wait_entry; eassumption.
Qed.
