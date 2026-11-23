Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.

Import UCOS2_C_Rules TaskStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Bind the logical origin to the CURRENT source-level execution context.
    A live but different TCB is not the caller, and boot origin is unavailable
    once OSRunning is true.  This is not a new runtime test and does not by
    itself own an executing stack: that remains the platform continuation
    contract.  No extra ready/lock condition is inserted here. *)
Definition task_create_call_origin (s : UCOS2_Verify_State)
  (origin : TaskInvocationOrigin) : Prop :=
  match origin with
  | BootInvocation => s.(SchedState).(isRunning) = false
  | RunningInvocation tid generation =>
      s.(SchedState).(isRunning) = true /\
      s.(SchedState).(curTaskID) = Some tid /\
      exists t, s.(TskState).(inUsedTaskStates) tid = Some t /\ t.(taskGeneration) = generation
  end.

Lemma task_create_call_origin_live : forall s origin,
  task_create_call_origin s origin -> task_invocation_origin_live s.(TskState) origin.
Proof. intros s [|tid generation] Horigin; [exact I|exact (proj2 (proj2 Horigin))]. Qed.

Lemma task_create_call_origin_unique : forall s first second,
  task_create_call_origin s first -> task_create_call_origin s second -> first = second.
Proof.
  intros s [|tid gen] [|tid' gen'] Hfirst Hsecond; simpl in Hfirst, Hsecond.
  - reflexivity.
  - destruct Hsecond as [Hr _]; congruence.
  - destruct Hfirst as [Hr _]; congruence.
  - destruct Hfirst as [Hr [Htid [t [Ht Hg]]]];
      destruct Hsecond as [Hr' [Htid' [t' [Ht' Hg']]]].
    assert (tid' = tid) by congruence; subst tid'.
    assert (t' = t) by congruence; subst t'. f_equal; congruence.
Qed.

Lemma task_create_call_origin_exists : forall s,
  s.(SchedState).(isRunning) = false \/ sched_task_call_boundary s.(TskState) s.(SchedState) ->
  exists origin, task_create_call_origin s origin.
Proof.
  intros s [Hboot|[Hrunning [tid [t [Ht [Htid Hrest]]]]]].
  - exists BootInvocation; exact Hboot.
  - exists (RunningInvocation tid t.(taskGeneration)); split; [exact Hrunning|].
    split; [exact Htid|]; exists t; split; [exact Ht|reflexivity].
Qed.

(** The Create wrappers add invocation bookkeeping and a priority-table
    reservation around OS_TCBInit.  The actions below carry source-stage
    ownership bindings; they do not add tests to the raw C branch relation.
    Their certificates are not an implementation of Save/Restore, StackInit,
    trace hooks or the complete kernel environment. *)
Definition task_create_begin_client (origin : TaskInvocationOrigin) : KernelClientAction :=
  {| kernel_client_actor := None;
     kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun _ before after =>
       task_create_call_origin before origin /\
       after = replace_TskS (task_begin_invocation origin before.(TskState)) before |}.

Lemma task_create_begin_client_certificate : forall origin,
  KernelClientCertificate (task_create_begin_client origin).
Proof.
  intro origin; constructor.
  - intros sg before after Hvalid [Horigin ->].
    apply UCOS2_begin_task_invocation_preserves_validity;
      [exact Hvalid|apply task_create_call_origin_live; exact Horigin].
  - intros sg before after observer Hvalid [Horigin ->] Hforeign; reflexivity.
  - intros sg before after observer caller Hvalid [Horigin ->] Hnormal Hactive.
    pose proof (proj1 (proj2 Hvalid)) as Htasks.
    eapply task_begin_invocation_preserves_invocation_active;
      [exact (proj1 (proj2 (proj2 (proj2 (proj2 Htasks)))))|exact Hactive].
  - intros sg before after observer Hvalid [Horigin ->] Hforeign; reflexivity.
Qed.

Definition task_create_reserve_client (p : Priority) (invocation : nat)
  (origin : TaskInvocationOrigin) : KernelClientAction :=
  {| kernel_client_actor := Some invocation;
     kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       task_reserve_guard sg before.(TskState) p invocation origin /\
       after = replace_TskS (task_reserve before.(TskState) p invocation origin) before |}.

Lemma task_create_reserve_client_certificate : forall p invocation origin,
  KernelClientCertificate (task_create_reserve_client p invocation origin).
Proof.
  intros p invocation origin; constructor.
  - intros sg before after Hvalid [Hguard ->].
    apply UCOS2_task_reserve_preserves_validity; assumption.
  - intros sg before after observer Hvalid [Hguard ->] Hforeign.
    apply task_reserve_frames_other_invocation; [|simpl in Hforeign; congruence].
    pose proof (proj1 (proj2 Hvalid)) as Htasks.
    pose proof (proj1 (proj2 (proj2 (proj2 Htasks)))) as Hreservations.
    destruct (before.(TskState).(taskLifecycle).(taskReservations) p) as [entry|] eqn:Hentry;
      [|reflexivity].
    pose proof (proj1 Hreservations p entry Hentry) as [_ [Hreserved _]].
    pose proof (proj1 (proj2 Hguard)) as Hfree; congruence.
  - intros sg before after observer caller Hvalid [Hguard ->] Hnormal Hactive; exact Hactive.
  - intros sg before after observer Hvalid [Hguard ->] Hforeign; reflexivity.
Qed.

Definition task_create_rollback_client (p : Priority) (invocation : nat) : KernelClientAction :=
  {| kernel_client_actor := Some invocation;
     kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun _ before after =>
       task_rollback_guard before.(TskState) p invocation /\
       after = replace_TskS (task_rollback_reservation before.(TskState) p) before |}.

Lemma task_create_rollback_client_certificate : forall p invocation,
  KernelClientCertificate (task_create_rollback_client p invocation).
Proof.
  intros p invocation; constructor.
  - intros sg before after Hvalid [Hguard ->].
    eapply UCOS2_task_rollback_preserves_validity; eassumption.
  - intros sg before after observer Hvalid [Hguard ->] Hforeign.
    eapply task_rollback_frames_other_invocation;
      [exact Hguard|simpl in Hforeign; congruence].
  - intros sg before after observer caller Hvalid [Hguard ->] Hnormal Hactive; exact Hactive.
  - intros sg before after observer Hvalid [Hguard ->] Hforeign; reflexivity.
Qed.

(** The old counter supplies a fresh call identity.  Reservation validity
    follows from the actual free slot, old invariant and live call origin;
    it is not assumed as a new whole-call precondition.  args.initPrio is
    bound to the wrapper's argument by task_create_spec. The name resource
    is separate from reservation bookkeeping: the source writes its static
    question-mark pointer during TCBInit, whose bytes must be registered by
    the startup/caller resource contract. No priority-table write establishes
    readability of an otherwise unconstrained name pointer. *)
Lemma task_create_reservation_establishes_tcb_init_entry : forall sg before args origin,
  UCOS2_state_inv sg before ->
  task_create_call_origin before origin ->
  task_priority_in_range sg args.(initPrio) -> before.(TskState).(prioTbl) args.(initPrio) = PTFree ->
  task_tcb_init_name_valid sg args before ->
  let invocation := before.(TskState).(taskLifecycle).(taskNextInvocation) in
  let started := task_begin_invocation origin before.(TskState) in
  task_tcb_init_entry sg args invocation origin
    (replace_TskS (task_reserve started args.(initPrio) invocation origin) before).
Proof.
  intros sg before args origin Hvalid Hcaller Hpriority Hfree Hname; cbv zeta.
  pose proof (task_create_call_origin_live before origin Hcaller) as Horigin.
  pose proof (task_begin_invocation_reserve_guard sg before.(TskState) origin
    args.(initPrio) (proj1 (proj2 Hvalid)) Horigin Hpriority Hfree) as Hguard.
  pose proof (UCOS2_begin_task_invocation_preserves_validity sg before origin Hvalid Horigin)
    as Hstarted.
  split.
  - exact (UCOS2_task_reserve_preserves_validity sg
      (replace_TskS (task_begin_invocation origin before.(TskState)) before)
      args.(initPrio) before.(TskState).(taskLifecycle).(taskNextInvocation) origin Hstarted Hguard).
  - split; [exact Hpriority|]. split.
    + apply task_begin_invocation_active; exact Horigin.
    + split.
      * unfold task_tcb_init_pending; simpl; destruct Z.eq_dec; congruence.
      * exact Hname.
Qed.

Lemma task_create_critical_establishes_tcb_init_entry : forall sg before args origin after,
  UCOS2_state_inv sg before ->
  task_create_call_origin before origin ->
  task_tcb_init_name_valid sg args before ->
  let invocation := before.(TskState).(taskLifecycle).(taskNextInvocation) in
  let started := replace_TskS (task_begin_invocation origin before.(TskState)) before in
  task_create_critical sg args.(initPrio) invocation origin started None after ->
  task_tcb_init_entry sg args invocation origin after.
Proof.
  intros sg before args origin after Hvalid Hcaller Hname invocation started Hstep.
  apply task_create_critical_continuation_iff in Hstep.
  destruct Hstep as [_ [Hpriority [Hfree Hafter]]].
  subst after; unfold started, invocation in *.
  exact (task_create_reservation_establishes_tcb_init_entry sg before args origin
    Hvalid Hcaller Hpriority Hfree Hname).
Qed.

(** A failed TCBInit returns the SAME empty reservation.  The following
    trace/Save interval must protect that fragment, not restore the global
    snapshot at TCBInit entry.  The caller then clears only its own slot. *)
Lemma task_create_no_free_after_environment :
  forall critical sg args invocation origin initial released resumed,
  task_tcb_init_result critical sg args invocation origin initial 66 released ->
  critical_region_interval critical sg invocation released resumed ->
  task_rollback_guard resumed.(TskState) args.(initPrio) invocation /\
  UCOS2_state_inv sg
    (replace_TskS (task_rollback_reservation resumed.(TskState) args.(initPrio)) resumed).
Proof.
  intros critical sg args invocation origin initial released resumed Hresult Hinterval.
  assert (Hvalid : UCOS2_state_inv sg released) by (inversion Hresult; subst; assumption).
  destruct (critical_region_interval_transports_resources
    critical sg invocation released resumed Hinterval Hvalid) as [Hresumed [Hframe Hactive]].
  destruct (task_tcb_init_no_free_pending_agreement
    critical sg args invocation origin initial released Hresult) as [_ [entry [Hentry [Hinv Hempty]]]].
  assert (Hguard : task_rollback_guard resumed.(TskState) args.(initPrio) invocation).
  { exists entry; split; [|split; assumption].
    eapply task_creation_frame_lookup; eassumption. }
  split; [exact Hguard|]. eapply UCOS2_task_rollback_preserves_validity; eassumption.
Qed.

Lemma task_create_no_free_preserves_continuation :
  forall critical sg args invocation origin initial released resumed,
  task_tcb_init_entry sg args invocation origin initial ->
  task_tcb_init_result critical sg args invocation origin initial 66 released ->
  critical_region_interval critical sg invocation released resumed ->
  task_invocation_active
    (task_rollback_reservation resumed.(TskState) args.(initPrio)) invocation origin.
Proof.
  intros critical sg args invocation origin initial released resumed Hentry Hresult Hinterval.
  assert (Hreleased : task_tcb_init_entry sg args invocation origin released).
  { inversion Hresult; subst; eapply task_tcb_init_acquire_entry; eassumption. }
  pose proof (task_tcb_init_acquire_entry critical sg args invocation origin
    released resumed Hreleased Hinterval) as [_ [_ [Hactive _]]].
  exact Hactive.
Qed.

Lemma task_create_rollback_other_priority : forall tasks p q,
  q <> p ->
  (task_rollback_reservation tasks p).(prioTbl) q = tasks.(prioTbl) q /\
  (task_rollback_reservation tasks p).(taskLifecycle).(taskReservations) q =
    tasks.(taskLifecycle).(taskReservations) q.
Proof. intros; simpl; destruct Z.eq_dec; [contradiction|split; reflexivity]. Qed.

Lemma task_create_rollback_preserves_fresh_counters : forall tasks p,
  (task_rollback_reservation tasks p).(taskLifecycle).(taskNextGeneration) =
    tasks.(taskLifecycle).(taskNextGeneration) /\
  (task_rollback_reservation tasks p).(taskLifecycle).(taskNextInvocation) =
    tasks.(taskLifecycle).(taskNextInvocation).
Proof. intros; split; reflexivity. Qed.
