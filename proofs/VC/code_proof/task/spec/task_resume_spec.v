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

(** OSTaskResume, Source/os_task.c:846--897, V2.93.01.
    Argument checks are before Save.  The critical relation ends before
    Restore; its boolean records the branch that has just set ready bits.
    OSRunning is subsequently read OUTSIDE the critical section.  Neither
    this boolean nor the resulting schedule request asserts a switch or a
    return of the original invocation.  No whole-call atomicity, trace
    effect, environment stuttering or platform implementation is assumed. *)
Definition task_resume_argument_error (sg : StableGlobVars) (prio : Priority)
  : option OSErrCode :=
  if (sg.(osKernelConfig).(cfgArgumentChecks) && Z.leb sg.(osLowestPrio) prio)%bool
  then Some OS_ERR_PRIO_INVALID else None.

Definition task_resume_critical (sg : StableGlobVars) (prio : Priority)
  : program UCOS2_Verify_State (OSErrCode * bool) :=
  fun entry result post =>
    (** This is the table-read domain, not an invented range-check branch
        when OS_ARG_CHK_EN is disabled.  PTTask lookup is likewise a memory
        interpretation premise, not an additional source error return. *)
    task_priority_in_range sg prio /\
    match entry.(TskState).(prioTbl) prio with
    | PTFree => result = (OS_ERR_TASK_RESUME_PRIO, false) /\ post = entry
    | PTReserved => result = (OS_ERR_TASK_NOT_EXIST, false) /\ post = entry
    | PTTask tid => exists t,
        entry.(TskState).(inUsedTaskStates) tid = Some t /\
        if task_is_suspended t.(stat) then
          result = (OS_ERR_NONE, task_resume_ready_test t) /\
          post = task_resume_state sg entry tid t
        else result = (OS_ERR_TASK_NOT_SUSPENDED, false) /\ post = entry
    end.

(** [ready_path] is a saved local control-flow observation; it must not be
    recomputed from a possibly changed TCB after Restore.  Only OSRunning
    is read at this later source point.  The concrete OS_Sched and trace
    contracts will consume the true branch, not a stale critical snapshot. *)
Definition task_resume_requests_schedule (ready_path : bool)
  (after_restore : UCOS2_Verify_State) : bool :=
  (ready_path && after_restore.(SchedState).(isRunning))%bool.

Lemma task_resume_argument_error_checks_disabled : forall sg prio,
  sg.(osKernelConfig).(cfgArgumentChecks) = false ->
  task_resume_argument_error sg prio = None.
Proof. intros; unfold task_resume_argument_error; rewrite H; reflexivity. Qed.

Lemma task_resume_argument_error_checked_iff : forall sg prio,
  sg.(osKernelConfig).(cfgArgumentChecks) = true ->
  (task_resume_argument_error sg prio = Some OS_ERR_PRIO_INVALID <-> sg.(osLowestPrio) <= prio).
Proof.
  intros sg prio H; unfold task_resume_argument_error; rewrite H; simpl.
  destruct (Z.leb sg.(osLowestPrio) prio) eqn:Hrange.
  - apply Z.leb_le in Hrange; split; auto.
  - apply Z.leb_gt in Hrange; split; [discriminate|lia].
Qed.

Lemma task_resume_argument_allows_index : forall sg prio,
  sg.(osKernelConfig).(cfgArgumentChecks) = true -> 0 <= prio ->
  task_resume_argument_error sg prio = None -> task_priority_in_range sg prio.
Proof.
  intros sg prio Hchecks Hprio Hguard.
  unfold task_resume_argument_error in Hguard; rewrite Hchecks in Hguard; simpl in Hguard.
  destruct (Z.leb sg.(osLowestPrio) prio) eqn:Hrange; [discriminate|].
  apply Z.leb_gt in Hrange; unfold task_priority_in_range; lia.
Qed.

Lemma task_resume_critical_live : forall sg prio entry tid t,
  task_priority_in_range sg prio -> entry.(TskState).(prioTbl) prio = PTTask tid ->
  entry.(TskState).(inUsedTaskStates) tid = Some t ->
  task_resume_critical sg prio entry
    (if task_is_suspended t.(stat) then (OS_ERR_NONE, task_resume_ready_test t)
     else (OS_ERR_TASK_NOT_SUSPENDED, false))
    (if task_is_suspended t.(stat) then task_resume_state sg entry tid t else entry).
Proof.
  intros sg prio entry tid t Hrange Htable Hlookup; split; [exact Hrange|].
  rewrite Htable; exists t; split; [exact Hlookup|].
  destruct (task_is_suspended t.(stat)); split; reflexivity.
Qed.

Lemma task_resume_requests_schedule_iff : forall ready_path after_restore,
  task_resume_requests_schedule ready_path after_restore = true <->
  ready_path = true /\ after_restore.(SchedState).(isRunning) = true.
Proof. intros; apply Bool.andb_true_iff. Qed.

Lemma task_resume_critical_error_frame : forall sg prio entry result post,
  task_resume_critical sg prio entry result post -> fst result <> OS_ERR_NONE ->
  post = entry /\ snd result = false.
Proof.
  intros sg prio entry result post [_ Hstep] Herror.
  destruct (entry.(TskState).(prioTbl) prio).
  - destruct Hstep as [-> ->]; split; reflexivity.
  - destruct Hstep as [-> ->]; split; reflexivity.
  - destruct Hstep as [t [_ Hstep]]; destruct (task_is_suspended t.(stat)).
    + destruct Hstep as [-> _]; contradiction Herror; reflexivity.
    + destruct Hstep as [-> ->]; split; reflexivity.
Qed.

Lemma task_resume_critical_deterministic : forall sg prio entry r1 s1 r2 s2,
  task_resume_critical sg prio entry r1 s1 ->
  task_resume_critical sg prio entry r2 s2 -> r1 = r2 /\ s1 = s2.
Proof.
  intros sg prio entry r1 s1 r2 s2 [_ H1] [_ H2].
  destruct (entry.(TskState).(prioTbl) prio).
  - destruct H1, H2; split; congruence.
  - destruct H1, H2; split; congruence.
  - destruct H1 as [a [Ha H1]], H2 as [b [Hb H2]].
    assert (a = b) by congruence; subst b.
    destruct (task_is_suspended a.(stat)); destruct H1, H2; split; congruence.
Qed.

Lemma task_resume_critical_ready_path_iff : forall sg prio entry result post,
  task_resume_critical sg prio entry result post ->
  (snd result = true <-> exists tid t,
    entry.(TskState).(prioTbl) prio = PTTask tid /\
    entry.(TskState).(inUsedTaskStates) tid = Some t /\
    task_is_suspended t.(stat) = true /\
    Z.land (encode_task_status t.(stat)) task_pend_any_mask = 0 /\ t.(dly) = 0).
Proof.
  intros sg prio entry result post [_ Hstep].
  destruct (entry.(TskState).(prioTbl) prio) as [| |tid] eqn:Htable.
  - destruct Hstep as [-> _]; split; [discriminate|intros [id [t [H _]]]; discriminate].
  - destruct Hstep as [-> _]; split; [discriminate|intros [id [t [H _]]]; discriminate].
  - destruct Hstep as [t [Ht Hstep]]; destruct (task_is_suspended t.(stat)) eqn:Hsusp.
    + destruct Hstep as [-> _]; simpl; rewrite task_resume_ready_test_iff.
      split.
      * intros [Hpending Hdly]; exists tid, t; repeat split; assumption || reflexivity.
      * intros [id [other [Hid [Hother [_ Hready]]]]].
        inversion Hid; subst id; assert (other = t) by congruence; subst other; exact Hready.
    + destruct Hstep as [-> _]; split; [discriminate|].
      intros [id [other [Hid [Hother [Hs _]]]]].
      inversion Hid; subst id; assert (other = t) by congruence; subst other; congruence.
Qed.

Lemma task_resume_critical_preserves_validity : forall sg prio entry result post,
  UCOS2_state_inv sg entry ->
  task_resume_critical sg prio entry result post -> UCOS2_state_inv sg post.
Proof.
  intros sg prio entry result post Hvalid [_ Hstep].
  destruct (entry.(TskState).(prioTbl) prio).
  - destruct Hstep as [_ ->]; exact Hvalid.
  - destruct Hstep as [_ ->]; exact Hvalid.
  - destruct Hstep as [t [Ht Hstep]]; destruct (task_is_suspended t.(stat)) eqn:Hsusp.
    + destruct Hstep as [_ ->]; eapply UCOS2_task_resume_preserves_validity; eassumption.
    + destruct Hstep as [_ ->]; exact Hvalid.
Qed.

Lemma task_resume_critical_merge_inv : forall sg prio entry result post,
  UCOS2_state_inv sg entry -> task_resume_critical sg prio entry result post ->
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg entry |-- UCOS2_inv sg post.
Proof.
  intros sg prio entry result post Hvalid [_ Hstep].
  destruct (entry.(TskState).(prioTbl) prio).
  - destruct Hstep as [_ ->]; apply UCOS2_inv_merge_updated_task_storage_sched; [exact Hvalid|reflexivity].
  - destruct Hstep as [_ ->]; apply UCOS2_inv_merge_updated_task_storage_sched; [exact Hvalid|reflexivity].
  - destruct Hstep as [t [Ht Hstep]]; destruct (task_is_suspended t.(stat)) eqn:Hsusp.
    + destruct Hstep as [_ ->]; apply UCOS2_inv_merge_task_resume; assumption.
    + destruct Hstep as [_ ->]; apply UCOS2_inv_merge_updated_task_storage_sched; [exact Hvalid|reflexivity].
Qed.

Lemma task_resume_critical_lifecycle_frame : forall sg prio entry result post,
  task_resume_critical sg prio entry result post ->
  post.(TskState).(taskLifecycle) = entry.(TskState).(taskLifecycle) /\
  (forall observer origin, task_invocation_active entry.(TskState) observer origin ->
    task_invocation_active post.(TskState) observer origin).
Proof.
  intros sg prio entry result post [_ Hstep].
  destruct (entry.(TskState).(prioTbl) prio).
  - destruct Hstep as [_ ->]; split; [reflexivity|auto].
  - destruct Hstep as [_ ->]; split; [reflexivity|auto].
  - destruct Hstep as [t [Ht Hstep]]; destruct (task_is_suspended t.(stat)).
    + destruct Hstep as [_ ->]; split; [reflexivity|].
      intros observer origin Hactive.
      eapply glob_task_set_usedtask_preserves_invocation_active;
        [exact Ht|reflexivity|exact Hactive].
    + destruct Hstep as [_ ->]; split; [reflexivity|auto].
Qed.

Lemma task_resume_critical_event_frame : forall sg prio entry result post,
  task_resume_critical sg prio entry result post -> post.(EventState) = entry.(EventState).
Proof.
  intros sg prio entry result post [_ Hstep].
  destruct (entry.(TskState).(prioTbl) prio).
  - destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [t [_ Hstep]]; destruct (task_is_suspended t.(stat));
      destruct Hstep as [_ ->]; reflexivity.
Qed.

(** Only the critical action is certified.  In particular the later
    OSRunning observation and OS_Sched/trace contracts are not folded into
    an atomic step or added to the ambient relation without their proofs. *)
Definition task_resume_critical_client (actor : option nat) (prio : Priority) : KernelClientAction :=
  {| kernel_client_actor := actor;
     kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       task_resume_argument_error sg prio = None /\
       exists result, task_resume_critical sg prio before result after |}.

Lemma task_resume_critical_client_certificate : forall actor prio,
  KernelClientCertificate (task_resume_critical_client actor prio).
Proof.
  intros actor prio; constructor.
  - intros sg before after Hvalid [_ [result Hstep]].
    eapply task_resume_critical_preserves_validity; eassumption.
  - intros sg before after observer Hvalid [_ [result Hstep]] Hforeign.
    pose proof (proj1 (task_resume_critical_lifecycle_frame sg prio before result after Hstep)) as Hframe.
    unfold task_creation_frame, task_creation_view; rewrite Hframe; reflexivity.
  - intros sg before after observer origin Hvalid [_ [result Hstep]] Hstops Hactive.
    exact (proj2 (task_resume_critical_lifecycle_frame sg prio before result after Hstep)
      observer origin Hactive).
  - intros sg before after observer Hvalid [_ [result Hstep]] Hforeign.
    rewrite (task_resume_critical_event_frame sg prio before result after Hstep); reflexivity.
Qed.
