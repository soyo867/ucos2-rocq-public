Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.

Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSTaskSuspend, Source/os_task.c:1002--1065, V2.93.01.
    The argument checks precede Save; [task_suspend_critical] starts AFTER
    Save and ends BEFORE Restore.  These are separate source phases, not
    a claim that the entire API is atomic.  The result's boolean records
    the local decision to call OS_Sched after Restore and the trace calls.
    It does not assert that the scheduler switches or that this invocation
    returns.  Platform/trace contracts and the continuation are composed
    separately; no state equality across Restore is assumed here. *)
Definition task_suspend_argument_error (sg : StableGlobVars) (prio : Priority)
  : option OSErrCode :=
  if sg.(osKernelConfig).(cfgArgumentChecks) then
    if Z.eqb prio sg.(osTaskIdlePrio) then Some OS_ERR_TASK_SUSPEND_IDLE else
    if (Z.leb sg.(osLowestPrio) prio && negb (Z.eqb prio sg.(osPrioSelf)))%bool
    then Some OS_ERR_PRIO_INVALID else None
  else None.

(** OSTCBCur->OSTCBPrio, not the possibly stale OSPrioCur cache.
    The idle check above is NOT repeated after resolving OS_PRIO_SELF. *)
Definition task_suspend_selection (sg : StableGlobVars) (prio : Priority)
  (current : TaskAbstractState) : Priority * bool :=
  if Z.eqb prio sg.(osPrioSelf) then (current.(curPrio), true)
  else (prio, Z.eqb prio current.(curPrio)).

Definition task_suspend_critical (sg : StableGlobVars) (prio : Priority)
  : program UCOS2_Verify_State (OSErrCode * bool) :=
  fun entry result post =>
    exists current_id current,
      entry.(SchedState).(curTaskID) = Some current_id /\
      entry.(TskState).(inUsedTaskStates) current_id = Some current /\
      let selection := task_suspend_selection sg prio current in
      (** Read-domain facts, not additional C branches.  Even a non-SELF
          request reads OSTCBCur before the table lookup.  An alias table
          slot may select a TCB with a different current priority. *)
      task_priority_in_range sg (fst selection) /\
      match entry.(TskState).(prioTbl) (fst selection) with
      | PTFree => result = (OS_ERR_TASK_SUSPEND_PRIO, false) /\ post = entry
      | PTReserved => result = (OS_ERR_TASK_NOT_EXIST, false) /\ post = entry
      | PTTask tid => exists t,
          entry.(TskState).(inUsedTaskStates) tid = Some t /\
          result = (OS_ERR_NONE, snd selection) /\
          post = task_suspend_state entry tid t
      end.

Lemma task_suspend_argument_error_checks_disabled : forall sg prio,
  sg.(osKernelConfig).(cfgArgumentChecks) = false ->
  task_suspend_argument_error sg prio = None.
Proof. intros; unfold task_suspend_argument_error; rewrite H; reflexivity. Qed.

Lemma task_suspend_argument_error_idle : forall sg,
  sg.(osKernelConfig).(cfgArgumentChecks) = true ->
  task_suspend_argument_error sg sg.(osTaskIdlePrio) = Some OS_ERR_TASK_SUSPEND_IDLE.
Proof. intros; unfold task_suspend_argument_error; rewrite H, Z.eqb_refl; reflexivity. Qed.

Lemma task_suspend_argument_error_self : forall sg,
  sg.(osPrioSelf) <> sg.(osTaskIdlePrio) ->
  task_suspend_argument_error sg sg.(osPrioSelf) = None.
Proof.
  intros sg H; unfold task_suspend_argument_error.
  destruct sg.(osKernelConfig).(cfgArgumentChecks); [|reflexivity].
  rewrite (proj2 (Z.eqb_neq _ _) H), Z.eqb_refl, Bool.andb_false_r; reflexivity.
Qed.

Lemma task_suspend_selection_self : forall sg current,
  task_suspend_selection sg sg.(osPrioSelf) current = (current.(curPrio), true).
Proof. intros; unfold task_suspend_selection; rewrite Z.eqb_refl; reflexivity. Qed.

Lemma task_suspend_selection_requests_schedule_iff : forall sg prio current,
  snd (task_suspend_selection sg prio current) = true <->
  prio = sg.(osPrioSelf) \/ prio = current.(curPrio).
Proof.
  intros; unfold task_suspend_selection; destruct (Z.eqb prio sg.(osPrioSelf)) eqn:Hself; simpl.
  - apply Z.eqb_eq in Hself; tauto.
  - apply Z.eqb_neq in Hself; rewrite Z.eqb_eq; tauto.
Qed.

Lemma task_suspend_argument_allows_selection_index : forall sg prio current,
  sg.(osKernelConfig).(cfgArgumentChecks) = true ->
  0 <= prio -> task_priority_in_range sg current.(curPrio) ->
  task_suspend_argument_error sg prio = None ->
  task_priority_in_range sg (fst (task_suspend_selection sg prio current)).
Proof.
  intros sg prio current Hchecks Hprio Hcurrent Hguard.
  unfold task_suspend_argument_error in Hguard; rewrite Hchecks in Hguard.
  destruct (Z.eqb prio sg.(osTaskIdlePrio)); [discriminate|].
  unfold task_suspend_selection; destruct (Z.eqb prio sg.(osPrioSelf)) eqn:Hself;
    [exact Hcurrent|].
  simpl in Hguard; rewrite Bool.andb_true_r in Hguard.
  destruct (Z.leb sg.(osLowestPrio) prio) eqn:Hrange; [discriminate|].
  apply Z.leb_gt in Hrange; unfold task_priority_in_range; simpl; lia.
Qed.

Lemma task_suspend_critical_self : forall sg entry cid current,
  UCOS2_state_inv sg entry ->
  entry.(SchedState).(curTaskID) = Some cid ->
  entry.(TskState).(inUsedTaskStates) cid = Some current ->
  task_suspend_critical sg sg.(osPrioSelf) entry (OS_ERR_NONE, true)
    (task_suspend_state entry cid current).
Proof.
  intros sg entry cid current Hvalid Hcurrent Hlookup.
  pose proof (proj1 (proj2 Hvalid)) as Htasks.
  assert (Hregistered : task_current_prio_registered entry.(TskState)).
  { unfold task_in_range in Htasks; tauto. }
  assert (Hpriority : forall tid t, entry.(TskState).(inUsedTaskStates) tid = Some t ->
    task_priority_in_range sg t.(curPrio)).
  { unfold task_in_range in Htasks; tauto. }
  exists cid, current; split; [exact Hcurrent|]; split; [exact Hlookup|].
  rewrite task_suspend_selection_self; simpl; split; [eapply Hpriority; exact Hlookup|].
  rewrite (Hregistered cid current Hlookup); exists current; repeat split; assumption || reflexivity.
Qed.

Lemma task_suspend_critical_error_frame : forall sg prio entry result post,
  task_suspend_critical sg prio entry result post -> fst result <> OS_ERR_NONE ->
  post = entry /\ snd result = false.
Proof.
  intros sg prio entry result post [cid [current [_ [_ [_ Hstep]]]]] Herror.
  destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg prio current))).
  - destruct Hstep as [-> ->]; split; reflexivity.
  - destruct Hstep as [-> ->]; split; reflexivity.
  - destruct Hstep as [t [_ [-> _]]]; contradiction Herror; reflexivity.
Qed.

Lemma task_suspend_critical_deterministic : forall sg prio entry r1 s1 r2 s2,
  task_suspend_critical sg prio entry r1 s1 ->
  task_suspend_critical sg prio entry r2 s2 -> r1 = r2 /\ s1 = s2.
Proof.
  intros sg prio entry r1 s1 r2 s2
    [id1 [t1 [Hid1 [Ht1 [_ H1]]]]] [id2 [t2 [Hid2 [Ht2 [_ H2]]]]].
  assert (id1 = id2) by congruence; subst id2.
  assert (t1 = t2) by congruence; subst t2.
  destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg prio t1))).
  - destruct H1, H2; split; congruence.
  - destruct H1, H2; split; congruence.
  - destruct H1 as [a [Ha [Hr1 Hs1]]], H2 as [b [Hb [Hr2 Hs2]]].
    assert (a = b) by congruence; subst b; split; congruence.
Qed.

Lemma task_suspend_critical_preserves_validity : forall sg prio entry result post,
  UCOS2_state_inv sg entry ->
  task_suspend_critical sg prio entry result post -> UCOS2_state_inv sg post.
Proof.
  intros sg prio entry result post Hvalid [cid [current [_ [_ [_ Hstep]]]]].
  destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg prio current))).
  - destruct Hstep as [_ ->]; exact Hvalid.
  - destruct Hstep as [_ ->]; exact Hvalid.
  - destruct Hstep as [t [Ht [_ ->]]].
    eapply UCOS2_task_suspend_preserves_validity; eassumption.
Qed.

Lemma task_suspend_critical_merge_inv : forall sg prio entry result post,
  UCOS2_state_inv sg entry -> task_suspend_critical sg prio entry result post ->
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg entry |-- UCOS2_inv sg post.
Proof.
  intros sg prio entry result post Hvalid [cid [current [_ [_ [_ Hstep]]]]].
  destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg prio current))).
  - destruct Hstep as [_ ->]; apply UCOS2_inv_merge_updated_task_storage_sched; [exact Hvalid|reflexivity].
  - destruct Hstep as [_ ->]; apply UCOS2_inv_merge_updated_task_storage_sched; [exact Hvalid|reflexivity].
  - destruct Hstep as [t [Ht [_ ->]]]; apply UCOS2_inv_merge_task_suspend; assumption.
Qed.

Lemma task_suspend_critical_lifecycle_frame : forall sg prio entry result post,
  task_suspend_critical sg prio entry result post ->
  post.(TskState).(taskLifecycle) = entry.(TskState).(taskLifecycle) /\
  (forall observer origin, task_invocation_active entry.(TskState) observer origin ->
    task_invocation_active post.(TskState) observer origin).
Proof.
  intros sg prio entry result post [cid [current [_ [_ [_ Hstep]]]]].
  destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg prio current))).
  - destruct Hstep as [_ ->]; split; [reflexivity|auto].
  - destruct Hstep as [_ ->]; split; [reflexivity|auto].
  - destruct Hstep as [t [Ht [_ ->]]]; split; [reflexivity|].
    intros observer origin Hactive.
    eapply glob_task_set_usedtask_preserves_invocation_active;
      [exact Ht|reflexivity|exact Hactive].
Qed.

Lemma task_suspend_critical_event_frame : forall sg prio entry result post,
  task_suspend_critical sg prio entry result post -> post.(EventState) = entry.(EventState).
Proof.
  intros sg prio entry result post [cid [current [_ [_ [_ Hstep]]]]].
  destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg prio current))).
  - destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [t [_ [_ ->]]]; reflexivity.
Qed.

(** An instance of the EXISTING environment-action interface.  The source
    embedding still binds actor/Save/Restore; this certifies only the actual
    critical mutation.  Suspension does not retire an invocation, although
    resuming its execution requires the separate scheduling continuation. *)
Definition task_suspend_critical_client (actor : option nat) (prio : Priority) : KernelClientAction :=
  {| kernel_client_actor := actor;
     kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       task_suspend_argument_error sg prio = None /\
       exists result, task_suspend_critical sg prio before result after |}.

Lemma task_suspend_critical_client_certificate : forall actor prio,
  KernelClientCertificate (task_suspend_critical_client actor prio).
Proof.
  intros actor prio; constructor.
  - intros sg before after Hvalid [_ [result Hstep]].
    eapply task_suspend_critical_preserves_validity; eassumption.
  - intros sg before after observer Hvalid [_ [result Hstep]] Hforeign.
    pose proof (proj1 (task_suspend_critical_lifecycle_frame sg prio before result after Hstep)) as Hframe.
    unfold task_creation_frame, task_creation_view; rewrite Hframe; reflexivity.
  - intros sg before after observer origin Hvalid [_ [result Hstep]] Hstops Hactive.
    exact (proj2 (task_suspend_critical_lifecycle_frame sg prio before result after Hstep)
      observer origin Hactive).
  - intros sg before after observer Hvalid [_ [result Hstep]] Hforeign.
    rewrite (task_suspend_critical_event_frame sg prio before result after Hstep); reflexivity.
Qed.
