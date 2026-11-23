Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import compcert.lib.Integers.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Shared source pattern: V2.93.01 OSSemPendAbort (os_sem.c:439--493),
    OSMboxPendAbort (os_mbox.c:440--495), OSQPendAbort (os_q.c:564--620).
    Each public module selects its own Event type and actual wait mask.
    Prefix observations are ordered: safety hook, argument check, type
    read, then Save.  No ISR/lock rejection or trace call is invented.
    If the safety hook returns, the API returns zero without a perr write.
    These separate observations do not assert snapshot equality across
    unmasked reads, Save, Restore, or the later scheduler call. *)
Definition event_pend_abort_safety_exception_requested
  (sg : StableGlobVars) (perr : addr) : bool :=
  (sg.(osKernelConfig).(cfgSafetyCritical) && Z.eqb perr 0)%bool.

Definition event_pend_abort_argument_error
  (sg : StableGlobVars) (pevent : addr) : option OSErrCode :=
  if (sg.(osKernelConfig).(cfgArgumentChecks) && Z.eqb pevent 0)%bool
  then Some OS_ERR_PEVENT_NULL else None.

Definition event_pend_abort_type_error (expected actual : Z) : option OSErrCode :=
  if Z.eqb actual expected then None else Some OS_ERR_EVENT_TYPE.

Lemma event_pend_abort_argument_error_checks_disabled : forall sg pevent,
  sg.(osKernelConfig).(cfgArgumentChecks) = false ->
  event_pend_abort_argument_error sg pevent = None.
Proof. intros; unfold event_pend_abort_argument_error; rewrite H; reflexivity. Qed.

Lemma event_pend_abort_type_error_none_iff : forall expected actual,
  event_pend_abort_type_error expected actual = None <-> actual = expected.
Proof.
  intros; unfold event_pend_abort_type_error; destruct (Z.eqb actual expected) eqn:E;
    [apply Z.eqb_eq in E|apply Z.eqb_neq in E]; split; congruence.
Qed.

(** The ignored priority returns witness the loop length.  The actual
    INT8U counter starts at zero and wraps after each increment.  This is
    not replaced by an unbounded count, even for larger configurations. *)
Definition event_pend_abort_count (priorities : list Priority) : Z :=
  Byte.unsigned (Byte.repr (Z.of_nat (length priorities))).

Lemma event_pend_abort_count_nil : event_pend_abort_count [] = 0.
Proof.
  unfold event_pend_abort_count; apply Byte.unsigned_repr;
    change (0 <= 0 <= 255); lia.
Qed.

Lemma event_pend_abort_count_cons : forall priority priorities,
  event_pend_abort_count (priority :: priorities) =
  Byte.unsigned (Byte.add (Byte.repr (event_pend_abort_count priorities)) Byte.one).
Proof.
  intros; unfold event_pend_abort_count.
  rewrite Byte.repr_unsigned, Byte.add_unsigned, Byte.unsigned_one.
  repeat rewrite Byte.unsigned_repr_eq.
  change (Z.of_nat (S (length priorities)) mod 256 =
    (Z.of_nat (length priorities) mod 256 + 1) mod 256).
  rewrite Z.add_mod_idemp_l by lia.
  rewrite Nat2Z.inj_succ; f_equal; lia.
Qed.

Lemma event_pend_abort_count_in_range : forall priorities,
  0 <= event_pend_abort_count priorities < 256.
Proof. intros; apply Byte.unsigned_range. Qed.

Lemma event_pend_abort_count_snoc : forall priorities priority,
  event_pend_abort_count (priorities ++ [priority]) =
  Byte.unsigned (Byte.add (Byte.repr (event_pend_abort_count priorities)) Byte.one).
Proof.
  intros; rewrite <- event_pend_abort_count_cons with (priority := priority).
  unfold event_pend_abort_count; rewrite length_app; cbn [length].
  rewrite Nat.add_1_r; reflexivity.
Qed.

Lemma event_pend_abort_count_eq_length : forall priorities,
  Z.of_nat (length priorities) <= 255 ->
  event_pend_abort_count priorities = Z.of_nat (length priorities).
Proof.
  intros priorities Hlength; apply Byte.unsigned_repr.
  change (0 <= Z.of_nat (length priorities) <= 255); lia.
Qed.

(** Critical endpoint only.  The result records (count, (error, call_sched)).
    The boolean requests OS_Sched AFTER Restore, not an actual switch or
    successful return of this invocation.  The perr store occurs only
    after that call returns.  An absent Event lookup is an invalid read,
    not a source error branch.  Only opt=1 broadcasts; every other INT8U
    value takes the single-abort default. *)
Definition event_pend_abort_critical (sg : StableGlobVars) (eid : EventID)
  (kind : PendType) (opt : Z) : program UCOS2_Verify_State (Z * (OSErrCode * bool)) :=
  fun s result after => exists e,
    s.(EventState).(inUsedEventStates) eid = Some e /\
    if Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0 then
      result = (0, (OS_ERR_NONE, false)) /\ after = s
    else if Z.eqb opt 1 then
      exists priorities,
        event_broadcast sg eid kind 0 PendAbort s priorities after /\
        result = (event_pend_abort_count priorities, (OS_ERR_PEND_ABORT, true))
    else exists priority,
      event_task_rdy sg s eid kind 0 PendAbort = Some (priority, after) /\
      result = (1, (OS_ERR_PEND_ABORT, true)).

Lemma event_pend_abort_critical_exists : forall sg s eid e kind opt,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  exists result after, event_pend_abort_critical sg eid kind opt s result after.
Proof.
  intros sg s eid e kind opt Hvalid He Hkind.
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0) eqn:Hempty.
  - exists (0, (OS_ERR_NONE, false)), s; exists e; split; [exact He|].
    rewrite Hempty; split; reflexivity.
  - destruct (Z.eqb opt 1) eqn:Hopt.
    + destruct (event_broadcast_exists e.(waitList) sg s eid e kind 0 PendAbort
        Hvalid He Hkind eq_refl) as [priorities [after [Hloop _]]].
      exists (event_pend_abort_count priorities, (OS_ERR_PEND_ABORT, true)), after.
      exists e; split; [exact He|]; rewrite Hempty, Hopt; exists priorities;
        split; [exact Hloop|reflexivity].
    + destruct e.(waitList) as [|head tail] eqn:Hlist; [discriminate Hempty|].
      destruct (event_wake_head sg s eid e head tail kind 0 PendAbort Hvalid He Hkind Hlist)
        as [old [_ [Hstep _]]].
      exists (1, (OS_ERR_PEND_ABORT, true)),
        (event_wake_state sg s eid e head old kind 0 PendAbort).
      exists e; split; [exact He|]; rewrite Hlist, Hempty, Hopt.
      exists old.(curPrio); split; [exact Hstep|reflexivity].
Qed.

Lemma event_pend_abort_critical_deterministic : forall sg eid kind opt s r1 s1 r2 s2,
  event_pend_abort_critical sg eid kind opt s r1 s1 ->
  event_pend_abort_critical sg eid kind opt s r2 s2 -> r1 = r2 /\ s1 = s2.
Proof.
  intros sg eid kind opt s r1 s1 r2 s2 [e [He Hfirst]] [node [Hnode Hsecond]].
  assert (node = e) by congruence; subst node.
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0).
  - destruct Hfirst as [-> ->]; destruct Hsecond as [-> ->]; split; reflexivity.
  - destruct (Z.eqb opt 1).
    + destruct Hfirst as [ps1 [Hloop1 ->]]; destruct Hsecond as [ps2 [Hloop2 ->]].
      destruct (event_broadcast_deterministic sg eid kind 0 PendAbort s ps1 s1 ps2 s2
        Hloop1 Hloop2) as [-> ->]; split; reflexivity.
    + destruct Hfirst as [p1 [Hstep1 ->]]; destruct Hsecond as [p2 [Hstep2 ->]].
      split; congruence.
Qed.

Lemma event_pend_abort_broadcast_count_eq_waiters : forall sg s eid e kind priorities after,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  event_broadcast sg eid kind 0 PendAbort s priorities after ->
  event_pend_abort_count priorities = Z.of_nat (length e.(waitList)).
Proof.
  intros sg s eid e kind priorities after Hvalid He Hkind Hloop.
  pose proof (event_broadcast_result sg s eid e kind 0 PendAbort priorities after
    Hvalid He Hkind Hloop) as [_ [_ [Hlength _]]].
  pose proof (event_waiter_count_le_task_count sg s eid e Hvalid He) as Hwaiters.
  pose proof (task_count_in_pool_range sg s.(TskState)
    (proj1 Hvalid) (proj1 (proj2 Hvalid))) as Hcount.
  rewrite event_pend_abort_count_eq_length; [rewrite Hlength; reflexivity|rewrite Hlength; lia].
Qed.

Lemma event_pend_abort_critical_observation : forall sg s eid e kind opt result after,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  event_pend_abort_critical sg eid kind opt s result after ->
  result =
    if Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0
    then (0, (OS_ERR_NONE, false))
    else (if Z.eqb opt 1 then Z.of_nat (length e.(waitList)) else 1,
          (OS_ERR_PEND_ABORT, true)).
Proof.
  intros sg s eid e kind opt result after Hvalid He Hkind [node [Hnode Hstep]].
  assert (node = e) by congruence; subst node.
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0);
    [exact (proj1 Hstep)|].
  destruct (Z.eqb opt 1).
  - destruct Hstep as [priorities [Hloop ->]].
    rewrite (event_pend_abort_broadcast_count_eq_waiters sg s eid e kind priorities after
      Hvalid He Hkind Hloop); reflexivity.
  - destruct Hstep as [priority [_ Hresult]]; exact Hresult.
Qed.

(** The only Event payload change is the wait-list field: Sem count,
    mailbox payload and Queue fields remain those of the original object. *)
Lemma event_pend_abort_critical_event_result : forall sg s eid e kind opt result after,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  event_pend_abort_critical sg eid kind opt s result after ->
  after.(EventState).(inUsedEventStates) eid =
    Some (event_set_wait_list e (if Z.eqb opt 1 then [] else tl e.(waitList))).
Proof.
  intros sg s eid e kind opt result after Hvalid He Hkind [node [Hnode Hstep]].
  assert (node = e) by congruence; subst node.
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0) eqn:Hempty.
  - destruct Hstep as [_ ->]; apply Z.eqb_eq in Hempty.
    pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [_ [_ Hentries]]]]]] _]]]].
    apply (proj1 (encode_event_wait_grp_zero_iff_empty sg s.(TskState) e.(waitList)
      (proj1 (Hentries eid e He)))) in Hempty.
    rewrite He, Hempty; destruct (Z.eqb opt 1); cbn [tl]; f_equal;
      destruct e; cbn in Hempty |- *; subst; reflexivity.
  - apply Z.eqb_neq in Hempty; destruct (Z.eqb opt 1).
    + destruct Hstep as [priorities [Hloop _]].
      exact (proj1 (proj2 (event_broadcast_result sg s eid e kind 0 PendAbort priorities after
        Hvalid He Hkind Hloop))).
    + destruct Hstep as [priority [Hcall _]].
      destruct (event_wake_decompose sg s eid e kind 0 PendAbort priority after
        Hvalid He Hkind Hempty Hcall)
        as [head [tail [old [Hlist [_ [_ [_ [_ Hlookup]]]]]]]].
      rewrite Hlist; exact Hlookup.
Qed.

Lemma event_pend_abort_critical_preserves_resources : forall sg s eid e kind opt result after,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  event_pend_abort_critical sg eid kind opt s result after ->
  UCOS2_state_inv sg after /\
  after.(EventState).(publishedQueueBytes) = s.(EventState).(publishedQueueBytes) /\
  (UCOS2_raw_rep_missing_task_storage_sched_event sg s |-- UCOS2_raw_rep_missing_task_storage_sched_event sg after).
Proof.
  intros sg s eid e kind opt result after Hvalid He Hkind [node [Hnode Hstep]].
  assert (node = e) by congruence; subst node.
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0) eqn:Hempty.
  - destruct Hstep as [_ ->]; split; [exact Hvalid|]; split; reflexivity.
  - apply Z.eqb_neq in Hempty; destruct (Z.eqb opt 1).
    + destruct Hstep as [priorities [Hloop _]].
      pose proof (event_broadcast_result sg s eid e kind 0 PendAbort priorities after
        Hvalid He Hkind Hloop) as [Hafter [_ [_ Hbytes]]].
      split; [exact Hafter|]; split; [exact Hbytes|].
      exact (event_broadcast_preserves_residual sg eid kind 0 PendAbort s priorities after
        Hloop e Hvalid He Hkind).
    + destruct Hstep as [priority [Hcall _]].
      destruct (event_wake_decompose sg s eid e kind 0 PendAbort priority after
        Hvalid He Hkind Hempty Hcall)
        as [head [tail [old [_ [_ [_ [-> [Hafter _]]]]]]]].
      split; [exact Hafter|]; split; [reflexivity|].
      apply UCOS2_event_wake_preserves_residual; exact He.
Qed.

Lemma event_pend_abort_critical_preserves_invocation : forall sg s eid e kind opt result after
  invocation origin,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  event_pend_abort_critical sg eid kind opt s result after ->
  task_invocation_active s.(TskState) invocation origin ->
  task_invocation_active after.(TskState) invocation origin.
Proof.
  intros sg s eid e kind opt result after invocation origin Hvalid He Hkind
    [node [Hnode Hstep]] Hactive.
  assert (node = e) by congruence; subst node.
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0) eqn:Hempty.
  - destruct Hstep as [_ ->]; exact Hactive.
  - apply Z.eqb_neq in Hempty; destruct (Z.eqb opt 1).
    + destruct Hstep as [priorities [Hloop _]].
      exact (event_broadcast_preserves_invocation sg eid kind 0 PendAbort s priorities after
        Hloop e invocation origin Hvalid He Hkind Hactive).
    + destruct Hstep as [priority [Hcall _]].
      destruct (event_wake_decompose sg s eid e kind 0 PendAbort priority after
        Hvalid He Hkind Hempty Hcall)
        as [head [tail [old [_ [Hold [_ [-> _]]]]]]].
      eapply glob_task_set_usedtask_preserves_invocation_active;
        [exact Hold|reflexivity|exact Hactive].
Qed.

Lemma event_pend_abort_critical_task_frame : forall sg s eid e kind opt result after tid,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  event_pend_abort_critical sg eid kind opt s result after -> ~ In tid e.(waitList) ->
  after.(TskState).(inUsedTaskStates) tid = s.(TskState).(inUsedTaskStates) tid.
Proof.
  intros sg s eid e kind opt result after tid Hvalid He Hkind [node [Hnode Hstep]] Habsent.
  assert (node = e) by congruence; subst node.
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0) eqn:Hempty.
  - destruct Hstep as [_ ->]; reflexivity.
  - apply Z.eqb_neq in Hempty; destruct (Z.eqb opt 1).
    + destruct Hstep as [priorities [Hloop _]].
      exact (event_broadcast_task_frame sg eid kind 0 PendAbort s priorities after
        Hloop e tid Hvalid He Hkind Habsent).
    + destruct Hstep as [priority [Hcall _]].
      destruct (event_wake_decompose sg s eid e kind 0 PendAbort priority after
        Hvalid He Hkind Hempty Hcall)
        as [head [tail [old [Hlist [_ [_ [-> _]]]]]]].
      assert (Hne : tid <> head) by
        (intro E; subst tid; apply Habsent; rewrite Hlist; left; reflexivity).
      cbn [event_wake_state replace_SchedS replace_EventS replace_TskS TskState
        glob_task_set_usedtask inUsedTaskStates].
      rewrite (proj2 (Z.eqb_neq _ _) Hne); reflexivity.
Qed.

Lemma event_pend_abort_broadcast_updates_waiter : forall sg s eid e kind result after tid old,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  event_pend_abort_critical sg eid kind 1 s result after ->
  In tid e.(waitList) -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  after.(TskState).(inUsedTaskStates) tid = Some (task_event_wake_single old kind 0 PendAbort).
Proof.
  intros sg s eid e kind result after tid old Hvalid He Hkind [node [Hnode Hstep]] Hin Hold.
  assert (node = e) by congruence; subst node.
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0) eqn:Hempty.
  - apply Z.eqb_eq in Hempty.
    pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [_ [_ Hentries]]]]]] _]]]].
    apply (proj1 (encode_event_wait_grp_zero_iff_empty sg s.(TskState) e.(waitList)
      (proj1 (Hentries eid e He)))) in Hempty; rewrite Hempty in Hin; contradiction.
  - destruct Hstep as [priorities [Hloop _]].
    exact (event_broadcast_updates_waiter sg eid kind 0 PendAbort s priorities after
      Hloop e tid old Hvalid He Hkind Hin Hold).
Qed.

(** Count refers to aborted waits, not necessarily newly runnable tasks:
    the existing wake operation preserves suspension.  In the single
    branch the whole endpoint identifies exactly the selected head TCB. *)
Lemma event_pend_abort_single_result : forall sg s eid e kind opt result after,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e ->
  event_type_to_pend_type e.(eventType) = Some kind -> opt <> 1 ->
  encode_event_wait_grp e.(waitList) s.(TskState) <> 0 ->
  event_pend_abort_critical sg eid kind opt s result after ->
  exists head tail old,
    e.(waitList) = head :: tail /\ s.(TskState).(inUsedTaskStates) head = Some old /\
    result = (1, (OS_ERR_PEND_ABORT, true)) /\
    after = event_wake_state sg s eid e head old kind 0 PendAbort.
Proof.
  intros sg s eid e kind opt result after Hvalid He Hkind Hopt Hnonzero [node [Hnode Hstep]].
  assert (node = e) by congruence; subst node.
  rewrite (proj2 (Z.eqb_neq _ _) Hnonzero), (proj2 (Z.eqb_neq _ _) Hopt) in Hstep.
  destruct Hstep as [priority [Hcall Hresult]].
  destruct (event_wake_decompose sg s eid e kind 0 PendAbort priority after
    Hvalid He Hkind Hnonzero Hcall)
    as [head [tail [old [Hlist [Hold [_ [Hafter _]]]]]]].
  exists head, tail, old; repeat split; assumption.
Qed.

Lemma event_pend_abort_critical_merge_global : forall sg s eid e kind opt result after,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  event_pend_abort_critical sg eid kind opt s result after ->
  task_public_storage sg after.(TskState) **
  sched_raw_rep sg after.(TskState) after.(SchedState) **
  event_raw_rep sg after.(TskState) after.(EventState) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |-- UCOS2_inv sg after.
Proof.
  intros sg s eid e kind opt result after Hvalid He Hkind Hstep.
  destruct (event_pend_abort_critical_preserves_resources sg s eid e kind opt result after
    Hvalid He Hkind Hstep) as [Hafter [_ Hresidual]].
  sep_apply_l_atomic Hresidual.
  unfold UCOS2_inv, UCOS2_raw_rep, task_shared_rep,
    UCOS2_raw_rep_missing_task_storage_sched, UCOS2_raw_rep_missing_task_storage_sched_event; entailer!.
Qed.
