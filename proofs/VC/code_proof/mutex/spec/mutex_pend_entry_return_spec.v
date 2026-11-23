Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_entry_source_spec.
Import TaskStateDef ListNotations.
Local Open Scope Z_scope.

(** Same-instance execution identifies the returned node and generation.
    Running, current-priority cache and ready-list membership come from
    the EXISTING completed-call C rely, not from the platform or from a
    Sem-specific source family. Effective readiness follows the returned
    world's ordinary ready-list invariant. No Idle fact is consumed. *)
Lemma mutex_pend_source_preserves_ready_call : forall external port critical sg
  original returned before after old,
  UCOS2_state_inv sg before -> kernel_call_task_source original before ->
  before.(SchedState).(isRunning) = true ->
  sched_current_ready_at before.(TskState) before.(SchedState)
    original.(os_sched_call_stack).(stackLeaseSlot) old ->
  kernel_resumption_task_source_trace external port critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin) before false
    returned.(os_sched_call_origin) after ->
  task_tcb_init_stack_same_call returned original -> sem_pend_save_rely sg before after ->
  kernel_call_task_source returned after /\ after.(SchedState).(isRunning) = true /\
  exists node, sched_current_ready_at after.(TskState) after.(SchedState)
    returned.(os_sched_call_stack).(stackLeaseSlot) node /\
    node.(taskGeneration) = returned.(os_sched_call_stack).(stackLeaseGeneration).
Proof.
  intros external port critical sg original returned before after old Hvalid Hsource Hrunning
    Hready Htrace Hsame [[Hr Hcounters] [Hruntime [Hcache_rely Hready_rely]]].
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)
    as [Hinterval Hcontrol].
  destruct (critical_region_interval_transports_resources critical sg
    original.(os_sched_call_invocation) before after Hinterval Hvalid) as [Hvalid_after _].
  assert (Hsource_after : kernel_call_task_source original after).
  { eapply task_tcb_init_stack_registered_source_preserved;
      [exact Hvalid|exact Hsame|exact Htrace|exact Hsource]. }
  assert (Hreturned : kernel_call_task_source returned after).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff returned original after Hsame));
      exact Hsource_after. }
  destruct (kernel_call_task_source_current_at original after Hsource_after)
    as [Hcurrent [node [Hnode Hgeneration]]].
  assert (Hmember : In original.(os_sched_call_stack).(stackLeaseSlot) after.(SchedState).(readyList)).
  { apply Hready_rely; [exact (proj1 (proj2 Hready))|
      exact (proj1 (proj2 (proj2 (proj2 Hready))))]. }
  pose proof (Hcache_rely (sched_current_ready_at_implies_current_consistency _ _ _ _ Hready)) as Hcache.
  unfold sched_current_consistency in Hcache; rewrite Hcurrent in Hcache.
  destruct Hcache as [cached [Hcached Hpriority]].
  assert (cached = node) by congruence; subst cached.
  destruct (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid_after)))) _ Hmember)
    as [ready_node [Hready_node [_ Heffective]]].
  assert (ready_node = node) by congruence; subst ready_node.
  split; [exact Hreturned|]. split; [congruence|]. exists node.
  rewrite (proj2 (proj2 Hsame)); split; [repeat split; assumption|exact Hgeneration].
Qed.

Lemma mutex_pend_return_source_preserves_ready_call : forall external port critical sg
  original returned before after old,
  UCOS2_state_inv sg before -> kernel_call_task_source original before ->
  before.(SchedState).(isRunning) = true ->
  sched_current_ready_at before.(TskState) before.(SchedState)
    original.(os_sched_call_stack).(stackLeaseSlot) old ->
  kernel_resumption_task_source_trace external port critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin) before false
    returned.(os_sched_call_origin) after ->
  kernel_call_normal_return original before returned after -> sem_pend_save_rely sg before after ->
  kernel_call_task_source returned after /\ after.(SchedState).(isRunning) = true /\
  exists node, sched_current_ready_at after.(TskState) after.(SchedState)
    returned.(os_sched_call_stack).(stackLeaseSlot) node /\
    node.(taskGeneration) = returned.(os_sched_call_stack).(stackLeaseGeneration).
Proof. intros * Hvalid Hsource Hrunning Hready Htrace [Hsame Havailable] Hrely;
  eapply mutex_pend_source_preserves_ready_call; eassumption. Qed.

Lemma mutex_pend_save_source_preserves_ready_call : forall external port critical sg
  original returned mask saved before after old,
  UCOS2_state_inv sg before -> kernel_call_task_source original before ->
  before.(SchedState).(isRunning) = true ->
  sched_current_ready_at before.(TskState) before.(SchedState)
    original.(os_sched_call_stack).(stackLeaseSlot) old ->
  kernel_call_save_source external port critical sg original returned mask saved before after ->
  sem_pend_save_rely sg before after ->
  kernel_call_task_source returned after /\ after.(SchedState).(isRunning) = true /\
  exists node, sched_current_ready_at after.(TskState) after.(SchedState)
    returned.(os_sched_call_stack).(stackLeaseSlot) node /\
    node.(taskGeneration) = returned.(os_sched_call_stack).(stackLeaseGeneration).
Proof.
  intros * Hvalid Hsource Hrunning Hready [Htrace [Hi [Ho [Hs Hsaved]]]] Hrely.
  eapply mutex_pend_source_preserves_ready_call; try eassumption.
  unfold task_tcb_init_stack_same_call; repeat split; assumption.
Qed.

Lemma mutex_pend_modular_history_preserves_ready_call : forall environment critical sg
  original returned before after old,
  UCOS2_state_inv sg before -> kernel_call_task_source original before ->
  before.(SchedState).(isRunning) = true ->
  sched_current_ready_at before.(TskState) before.(SchedState)
    original.(os_sched_call_stack).(stackLeaseSlot) old ->
  sem_pend_modular_call_history environment critical sg original before returned after ->
  sem_pend_save_rely sg before after ->
  kernel_call_task_source returned after /\ after.(SchedState).(isRunning) = true /\
  exists node, sched_current_ready_at after.(TskState) after.(SchedState)
    returned.(os_sched_call_stack).(stackLeaseSlot) node /\
    node.(taskGeneration) = returned.(os_sched_call_stack).(stackLeaseGeneration).
Proof. intros * Hvalid Hsource Hrunning Hready [Htrace Hnormal] Hrely;
  eapply mutex_pend_return_source_preserves_ready_call; eassumption. Qed.

(** Join the separately checked field observation with readiness for the
    SAME returned node. This is not a new call-stage definition: an API
    owner adds its separately justified non-Idle identity when needed. *)
Lemma mutex_pend_modular_history_preserves_ready_entry : forall environment critical sg
  original returned before after old,
  (forall action, critical.(critical_region_clients) action ->
    mutex_pend_entry_source_client original.(os_sched_call_invocation)
      original.(os_sched_call_stack).(stackLeaseSlot)
      original.(os_sched_call_stack).(stackLeaseGeneration) action) ->
  UCOS2_state_inv sg before -> kernel_call_task_source original before ->
  before.(SchedState).(isRunning) = true ->
  sched_current_ready_at before.(TskState) before.(SchedState)
    original.(os_sched_call_stack).(stackLeaseSlot) old -> sem_pend_task_unregistered old ->
  sem_pend_modular_call_history environment critical sg original before returned after ->
  sem_pend_save_rely sg before after ->
  kernel_call_task_source returned after /\ after.(SchedState).(isRunning) = true /\
  exists node, sched_current_ready_at after.(TskState) after.(SchedState)
    returned.(os_sched_call_stack).(stackLeaseSlot) node /\
    node.(taskGeneration) = returned.(os_sched_call_stack).(stackLeaseGeneration) /\
    sem_pend_task_unregistered node.
Proof.
  intros environment critical sg original returned before after old Hclients Hvalid Hsource
    Hrunning Hready Hnone Hhistory Hrely.
  destruct (mutex_pend_modular_history_preserves_ready_call _ _ _ _ _ _ _ _
    Hvalid Hsource Hrunning Hready Hhistory Hrely)
    as [Hreturned [Hrunning_after [node [Hready_after Hgeneration]]]].
  pose proof Hhistory as [Htrace Hnormal].
  assert (Hfields : mutex_pend_entry_fields original.(os_sched_call_stack).(stackLeaseSlot) before).
  { exists old; split; [exact (proj1 Hready)|exact Hnone]. }
  destruct (mutex_pend_return_source_preserves_entry_fields _ _ _ _ _ _ _ _
    Hclients Hvalid Hsource Htrace Hnormal Hfields) as [found [Hfound [Hgen Hfields_after]]].
  pose proof (proj1 Hready_after) as Hnode.
  rewrite (proj2 (proj2 (proj1 Hnormal))) in Hnode.
  assert (found = node) by congruence; subst found.
  split; [exact Hreturned|]. split; [exact Hrunning_after|]. exists node; auto.
Qed.

(** The caller protocol is consumed only when the acquired world has the
    actual busy/wait observation. Before-stage evidence is transported;
    no ready/unlinked acquired stage is inserted as a premise. *)
Lemma mutex_pend_modular_history_preserves_ready_entry_when : forall environment critical sg
  original returned before after (wait_required : UCOS2_Verify_State -> Prop),
  (forall action, critical.(critical_region_clients) action ->
    mutex_pend_entry_source_client original.(os_sched_call_invocation)
      original.(os_sched_call_stack).(stackLeaseSlot)
      original.(os_sched_call_stack).(stackLeaseGeneration) action) ->
  UCOS2_state_inv sg before -> kernel_call_task_source original before ->
  sem_pend_modular_call_history environment critical sg original before returned after ->
  sem_pend_save_rely sg before after ->
  (wait_required after -> before.(SchedState).(isRunning) = true /\
    exists old, sched_current_ready_at before.(TskState) before.(SchedState)
      original.(os_sched_call_stack).(stackLeaseSlot) old /\ sem_pend_task_unregistered old) ->
  wait_required after ->
  kernel_call_task_source returned after /\ after.(SchedState).(isRunning) = true /\
  exists node, sched_current_ready_at after.(TskState) after.(SchedState)
    returned.(os_sched_call_stack).(stackLeaseSlot) node /\
    node.(taskGeneration) = returned.(os_sched_call_stack).(stackLeaseGeneration) /\
    sem_pend_task_unregistered node.
Proof.
  intros * Hclients Hvalid Hsource Hhistory Hrely Hbefore Hwait.
  destruct (Hbefore Hwait) as [Hrunning [old [Hready Hnone]]].
  eapply mutex_pend_modular_history_preserves_ready_entry; eassumption.
Qed.
