Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Shared SINGLE-EVENT wake loop used by Queue Post/PendAbort and other
    Event-family callers.  The kind/message/result are the actual arguments
    to OS_EventTaskRdy; the caller must establish the Event kind.
    Every iteration tests the current bitmap and selects through the
    current priority table.  No environment step occurs inside this masked
    loop.  The priority log is proof data, not a second OS state or a C
    accumulator.  A counted API separately models its machine-width counter.
    The selected global profile does not yet cover Multi-enabled calls. *)
Inductive event_broadcast (sg : StableGlobVars) (eid : EventID)
  (kind : PendType) (message : addr) (result : PendStatus)
  : UCOS2_Verify_State -> list Priority -> UCOS2_Verify_State -> Prop :=
| event_broadcast_done : forall s e,
    s.(EventState).(inUsedEventStates) eid = Some e ->
    encode_event_wait_grp e.(waitList) s.(TskState) = 0 ->
    event_broadcast sg eid kind message result s [] s
| event_broadcast_next : forall s e priority mid priorities after,
    s.(EventState).(inUsedEventStates) eid = Some e ->
    encode_event_wait_grp e.(waitList) s.(TskState) <> 0 ->
    event_task_rdy sg s eid kind message result = Some (priority, mid) ->
    event_broadcast sg eid kind message result mid priorities after ->
    event_broadcast sg eid kind message result s (priority :: priorities) after.

Lemma event_wake_head : forall sg s eid e head tail kind message result,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e ->
  event_type_to_pend_type e.(eventType) = Some kind -> e.(waitList) = head :: tail ->
  exists old,
    s.(TskState).(inUsedTaskStates) head = Some old /\
    event_task_rdy sg s eid kind message result =
      Some (old.(curPrio), event_wake_state sg s eid e head old kind message result) /\
    UCOS2_state_inv sg
      (event_wake_state sg s eid e head old kind message result) /\
    (event_wake_state sg s eid e head old kind message result).(EventState).(inUsedEventStates) eid =
      Some (event_set_wait_list e tail).
Proof.
  intros sg s eid e head tail kind message result Hvalid He Htype Hlist.
  pose proof Hvalid as [Hprofile [Htasks [_ [Hevents _]]]].
  assert (Hsg : valid_stable_glob_vars sg) by
    (unfold selected_kernel_profile in Hprofile; tauto).
  pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  pose proof (Hentries eid e He) as Hentry.
  destruct (event_waiter_task_fields sg s.(TskState) eid e head Hentry
    ltac:(rewrite Hlist; left; reflexivity)) as [old [actual [Hold Hfields]]].
  exists old; split; [exact Hold|]; split.
  - eapply event_task_rdy_selects_waiter; eauto.
  - split.
    + eapply UCOS2_event_wake_preserves_validity;
        [exact Hvalid|exact He|rewrite Hlist; left; reflexivity|exact Hold|].
      rewrite Htype; reflexivity.
    + pose proof Hentry as [[Hnd _] _]; rewrite Hlist in Hnd.
      inversion Hnd as [|? ? Habsent Htail]; subst.
      cbn [event_wake_state replace_SchedS replace_EventS replace_TskS
        EventState update_event_field_raw inUsedEventStates].
      rewrite Z.eqb_refl, Hlist, remove_Z_eqb_x_cons_x,
        remove_Z_eqb_notin_eq by exact Habsent; reflexivity.
Qed.

Lemma event_broadcast_exists : forall waiters sg s eid e kind message result,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e ->
  event_type_to_pend_type e.(eventType) = Some kind -> e.(waitList) = waiters ->
  exists priorities after,
    event_broadcast sg eid kind message result s priorities after /\
    UCOS2_state_inv sg after /\
    after.(EventState).(inUsedEventStates) eid = Some (event_set_wait_list e []) /\
    length priorities = length waiters /\
    after.(EventState).(publishedQueueBytes) = s.(EventState).(publishedQueueBytes).
Proof.
  induction waiters as [|head tail IH]; intros sg s eid e kind message result Hvalid He Htype Hlist.
  - exists [], s; split.
    + eapply event_broadcast_done; [exact He|rewrite Hlist; reflexivity].
    + split; [exact Hvalid|]; split.
      * rewrite He; f_equal; destruct e; cbn in Hlist |- *; subst; reflexivity.
      * split; reflexivity.
  - destruct (event_wake_head sg s eid e head tail kind message result Hvalid He Htype Hlist)
      as [old [Hold [Hstep [Hmid Hlookup]]]].
    set (mid := event_wake_state sg s eid e head old kind message result) in *.
    destruct (IH sg mid eid (event_set_wait_list e tail) kind message result Hmid Hlookup Htype eq_refl)
      as [priorities [after [Hloop [Hafter [Hlast [Hlength Hbytes]]]]]].
    exists (old.(curPrio) :: priorities), after; split.
    + eapply event_broadcast_next; [exact He| |exact Hstep|exact Hloop].
      pose proof Hvalid as [_ [_ [_ [Hevents _]]]].
      pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
      intro Hzero; apply (proj1 (encode_event_wait_grp_zero_iff_empty sg s.(TskState)
        e.(waitList) (proj1 (Hentries eid e He)))) in Hzero; congruence.
    + split; [exact Hafter|]; split; [exact Hlast|].
      split; [simpl; congruence|exact Hbytes].
Qed.

Lemma event_broadcast_deterministic : forall sg eid kind message result s ps1 s1 ps2 s2,
  event_broadcast sg eid kind message result s ps1 s1 ->
  event_broadcast sg eid kind message result s ps2 s2 -> ps1 = ps2 /\ s1 = s2.
Proof.
  intros sg eid kind message result s ps1 s1 ps2 s2 Hfirst; revert ps2 s2.
  induction Hfirst as [s e He Hzero|s e p mid ps after He Hnonzero Hstep Hloop IH];
    intros ps2 s2 Hsecond;
    inversion Hsecond as [other node Hnode Hzero'|
      other node p' mid' ps' after' Hnode Hnonzero' Hstep' Hloop']; subst.
  - split; reflexivity.
  - assert (node = e) by congruence; subst node; contradiction.
  - assert (node = e) by congruence; subst node; contradiction.
  - assert (Hpairs : (p, mid) = (p', mid')) by congruence.
    injection Hpairs as Hp Hmid; subst p' mid'.
    destruct (IH _ _ Hloop') as [-> ->]; split; reflexivity.
Qed.

Lemma event_broadcast_result : forall sg s eid e kind message result priorities after,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> event_type_to_pend_type e.(eventType) = Some kind ->
  event_broadcast sg eid kind message result s priorities after ->
  UCOS2_state_inv sg after /\
  after.(EventState).(inUsedEventStates) eid = Some (event_set_wait_list e []) /\
  length priorities = length e.(waitList) /\
  after.(EventState).(publishedQueueBytes) = s.(EventState).(publishedQueueBytes).
Proof.
  intros sg s eid e kind message result priorities after Hvalid He Htype Hloop.
  destruct (event_broadcast_exists e.(waitList) sg s eid e kind message result Hvalid He Htype eq_refl)
    as [ps [post [Hrun Hpost]]].
  destruct (event_broadcast_deterministic sg eid kind message result s ps post priorities after Hrun Hloop)
    as [-> ->]; exact Hpost.
Qed.

Lemma event_wake_decompose : forall sg s eid e kind message result priority after,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> event_type_to_pend_type e.(eventType) = Some kind ->
  encode_event_wait_grp e.(waitList) s.(TskState) <> 0 ->
  event_task_rdy sg s eid kind message result = Some (priority, after) ->
  exists head tail old,
    e.(waitList) = head :: tail /\ s.(TskState).(inUsedTaskStates) head = Some old /\
    priority = old.(curPrio) /\
    after = event_wake_state sg s eid e head old kind message result /\
    UCOS2_state_inv sg after /\
    after.(EventState).(inUsedEventStates) eid = Some (event_set_wait_list e tail).
Proof.
  intros sg s eid e kind message result priority after Hvalid He Htype Hnonzero Hstep.
  destruct e.(waitList) as [|head tail] eqn:Hlist; [contradiction Hnonzero; reflexivity|].
  destruct (event_wake_head sg s eid e head tail kind message result Hvalid He Htype Hlist)
    as [old [Hold [Hcall [Hpost Hlookup]]]].
  rewrite Hcall in Hstep; injection Hstep as Hp Hafter; subst priority after.
  exists head, tail, old; split; [reflexivity|]; split; [exact Hold|].
  split; [reflexivity|]; split; [reflexivity|]; split; assumption.
Qed.

Lemma event_broadcast_preserves_residual : forall sg eid kind message result s priorities after,
  event_broadcast sg eid kind message result s priorities after ->
  forall e, UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> event_type_to_pend_type e.(eventType) = Some kind ->
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |--
    UCOS2_raw_rep_missing_task_storage_sched_event sg after.
Proof.
  intros sg eid kind message result s priorities after Hloop.
  induction Hloop as [s node Hnode Hzero|s node p mid ps after Hnode Hnonzero Hstep Hloop IH];
    intros e Hvalid He Htype; [reflexivity|].
  assert (node = e) by congruence; subst node.
  destruct (event_wake_decompose sg s eid e kind message result p mid Hvalid He Htype Hnonzero Hstep)
    as [head [tail [old [Hlist [Hold [Hp [Hmid [HvalidMid Hlookup]]]]]]]].
  pose proof (UCOS2_event_wake_preserves_residual
    sg s eid e head old kind message result He) as Hframe.
  rewrite <- Hmid in Hframe.
  eapply derivable1_trans.
  - exact Hframe.
  - exact (IH (event_set_wait_list e tail) HvalidMid Hlookup Htype).
Qed.

Lemma event_broadcast_task_frame : forall sg eid kind message result s priorities after,
  event_broadcast sg eid kind message result s priorities after ->
  forall e tid, UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> event_type_to_pend_type e.(eventType) = Some kind ->
  ~ In tid e.(waitList) -> after.(TskState).(inUsedTaskStates) tid = s.(TskState).(inUsedTaskStates) tid.
Proof.
  intros sg eid kind message result s priorities after Hloop.
  induction Hloop as [s node Hnode Hzero|s node p mid ps after Hnode Hnonzero Hstep Hloop IH];
    intros e tid Hvalid He Htype Habsent; [reflexivity|].
  assert (node = e) by congruence; subst node.
  destruct (event_wake_decompose sg s eid e kind message result p mid Hvalid He Htype Hnonzero Hstep)
    as [head [tail [old [Hlist [Hold [Hp [Hmid [HvalidMid Hlookup]]]]]]]].
  rewrite Hlist in Habsent.
  assert (Hne : tid <> head) by (intro E; subst tid; apply Habsent; left; reflexivity).
  assert (Htail : ~ In tid tail) by (intro Hin; apply Habsent; right; exact Hin).
  rewrite (IH (event_set_wait_list e tail) tid HvalidMid Hlookup Htype Htail), Hmid.
  cbn [event_wake_state replace_SchedS replace_EventS replace_TskS TskState
    glob_task_set_usedtask inUsedTaskStates].
  rewrite (proj2 (Z.eqb_neq _ _) Hne); reflexivity.
Qed.

Lemma event_broadcast_updates_waiter : forall sg eid kind message result s priorities after,
  event_broadcast sg eid kind message result s priorities after ->
  forall e tid old, UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> event_type_to_pend_type e.(eventType) = Some kind ->
  In tid e.(waitList) -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  after.(TskState).(inUsedTaskStates) tid = Some (task_event_wake_single old kind message result).
Proof.
  intros sg eid kind message result s priorities after Hloop.
  induction Hloop as [s node Hnode Hzero|s node p mid ps after Hnode Hnonzero Hstep Hloop IH];
    intros e tid old Hvalid He Htype Hin Hold;
    assert (node = e) by congruence; subst node.
  - pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [_ [_ Hentries]]]]]] _]]]].
    apply (proj1 (encode_event_wait_grp_zero_iff_empty sg s.(TskState) e.(waitList)
      (proj1 (Hentries eid e He)))) in Hzero.
    rewrite Hzero in Hin; contradiction.
  - destruct (event_wake_decompose sg s eid e kind message result p mid Hvalid He Htype Hnonzero Hstep)
      as [head [tail [selected [Hlist [Hselected [Hp [Hmid [HvalidMid Hlookup]]]]]]]].
    pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [_ [_ Hentries]]]]]] _]]]].
    pose proof (proj1 (proj1 (Hentries eid e He))) as Hnd.
    rewrite Hlist in Hnd; inversion Hnd as [|? ? HheadAbsent HtailNd].
    rewrite Hlist in Hin; destruct Hin as [E|Hin].
    + subst tid; assert (old = selected) by congruence; subst old.
      rewrite (event_broadcast_task_frame sg eid kind message result mid ps after Hloop
        (event_set_wait_list e tail) head HvalidMid Hlookup Htype HheadAbsent), Hmid.
      cbn [event_wake_state replace_SchedS replace_EventS replace_TskS TskState
        glob_task_set_usedtask inUsedTaskStates].
      rewrite Z.eqb_refl; reflexivity.
    + assert (Hne : tid <> head) by (intro E; subst tid; contradiction).
      eapply IH; [exact HvalidMid|exact Hlookup|exact Htype|exact Hin|].
      rewrite Hmid; cbn [event_wake_state replace_SchedS replace_EventS replace_TskS TskState
        glob_task_set_usedtask inUsedTaskStates].
      rewrite (proj2 (Z.eqb_neq _ _) Hne); exact Hold.
Qed.

Lemma event_broadcast_preserves_invocation : forall sg eid kind message result s priorities after,
  event_broadcast sg eid kind message result s priorities after ->
  forall e invocation origin, UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  task_invocation_active s.(TskState) invocation origin ->
  task_invocation_active after.(TskState) invocation origin.
Proof.
  intros sg eid kind message result s priorities after Hloop.
  induction Hloop as [s node Hnode Hzero|s node p mid ps after Hnode Hnonzero Hstep Hloop IH];
    intros e invocation origin Hvalid He Hkind Hactive; [exact Hactive|].
  assert (node = e) by congruence; subst node.
  destruct (event_wake_decompose sg s eid e kind message result p mid Hvalid He Hkind Hnonzero Hstep)
    as [head [tail [old [Hlist [Hold [Hp [Hmid [HvalidMid Hlookup]]]]]]]].
  eapply IH; [exact HvalidMid|exact Hlookup|exact Hkind|].
  rewrite Hmid; eapply glob_task_set_usedtask_preserves_invocation_active;
    [exact Hold|reflexivity|exact Hactive].
Qed.

(** Counted callers use this existing Task-pool bound, rather than assuming
    that a source-width loop counter can never overflow. *)
Lemma event_waiter_count_le_task_count : forall sg s eid e,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  0 <= Z.of_nat (length e.(waitList)) <= s.(TskState).(taskCount).
Proof.
  intros sg s eid e Hvalid He.
  pose proof Hvalid as [_ [Htasks [_ [Hevents _]]]].
  pose proof Htasks as [_ [[HtaskNd [_ [Hcount [Hactive _]]]] _]].
  pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  destruct (proj1 (Hentries eid e He)) as [HwaitNd [_ Hmembers]].
  assert (Hincl : incl e.(waitList) s.(TskState).(taskLifecycle).(taskActiveOrder)).
  { intros tid Hin; apply (proj2 (Hactive tid)).
    destruct (Hmembers tid Hin) as [t [Ht Hprio]]; exists t; exact Ht. }
  pose proof (NoDup_incl_length HwaitNd Hincl) as Hlength.
  rewrite Hcount; lia.
Qed.

(** The caller supplies the real final TCB/ready/ECB storage.  Pure loop
    execution only transports the residual and proves validity; it does
    not manufacture the cells written by OS_EventTaskRdy. *)
Lemma event_broadcast_merge_global : forall sg s eid e kind message result priorities after,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  event_broadcast sg eid kind message result s priorities after ->
  task_public_storage sg after.(TskState) **
  sched_raw_rep sg after.(TskState) after.(SchedState) **
  event_raw_rep sg after.(TskState) after.(EventState) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |-- UCOS2_inv sg after.
Proof.
  intros sg s eid e kind message result priorities after Hvalid He Hkind Hloop.
  pose proof (proj1 (event_broadcast_result sg s eid e kind message result priorities after
    Hvalid He Hkind Hloop)) as Hafter.
  sep_apply_l_atomic (event_broadcast_preserves_residual
    sg eid kind message result s priorities after Hloop e Hvalid He Hkind).
  unfold UCOS2_inv, UCOS2_raw_rep, task_shared_rep,
    UCOS2_raw_rep_missing_task_storage_sched, UCOS2_raw_rep_missing_task_storage_sched_event; entailer!.
Qed.
