Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
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
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Shared V2.93.01 Sem/Mbox Delete flow.  The public functions bind
    their actual Event type and Pend mask.  Queue shares the entry checks
    but has its own QCB/buffer recycling; Mutex has a different owner/PCP
    protocol and must not use the ECB-only global recycling rule.
    These source-time observations are separate from the masked body:
    safety, IEC runtime, argument, ENTER trace, type, ISR, then Save.
    A returning null-perr safety hook returns NULL without a perr write;
    a returning IEC hook writes ILLEGAL_DEL_RUN_TIME then returns NULL. *)
Definition event_delete_safety_exception_requested (sg : StableGlobVars) (perr : addr) : bool :=
  (sg.(osKernelConfig).(cfgSafetyCritical) && Z.eqb perr 0)%bool.

Definition event_delete_runtime_exception_requested (sg : StableGlobVars) (started_byte : Z) : bool :=
  (sg.(osKernelConfig).(cfgSafetyCriticalIEC) && Z.eqb started_byte 1)%bool.

Definition event_delete_argument_error (sg : StableGlobVars) (pevent : addr) : option OSErrCode :=
  if (sg.(osKernelConfig).(cfgArgumentChecks) && Z.eqb pevent 0)%bool
  then Some OS_ERR_PEVENT_NULL else None.

Definition event_delete_context_error (expected_type type_byte int_nesting : Z) : option OSErrCode :=
  if negb (Z.eqb type_byte expected_type) then Some OS_ERR_EVENT_TYPE
  else if Z.ltb 0 int_nesting then Some OS_ERR_DEL_ISR else None.

Lemma event_delete_context_error_type_first : forall expected ty nesting,
  ty <> expected -> event_delete_context_error expected ty nesting = Some OS_ERR_EVENT_TYPE.
Proof.
  intros; unfold event_delete_context_error; rewrite (proj2 (Z.eqb_neq _ _) H); reflexivity.
Qed.

Lemma event_delete_context_error_isr : forall expected nesting,
  0 < nesting -> event_delete_context_error expected expected nesting = Some OS_ERR_DEL_ISR.
Proof.
  intros; unfold event_delete_context_error; rewrite Z.eqb_refl, (proj2 (Z.ltb_lt _ _) H); reflexivity.
Qed.

(** The selected names-disabled tail writes Type=UNUSED, Ptr=free-root,
    Cnt=0 and then publishes the new free root.  The image is taken AFTER
    any abort loop, so untouched ECB bytes are not reset or guessed.
    Mbox deletion overwrites its stored message pointer, but does not
    free or acquire ownership of the memory to which that pointer led. *)
Definition event_delete_recycle_state (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState) : UCOS2_Verify_State :=
  replace_EventS (event_recycle sg s.(EventState) eid (event_image sg s.(TskState) e)) s.

(** Result = (pointer, (perr value, request OS_Sched)).  The initial
    OSEventGrp read is retained through the loop.  Only opt=0/1 are valid;
    ALWAYS loops on the current bitmap, not a precomputed waiter count.
    Every perr write and requested OS_Sched call occurs after Restore;
    their storage/call/trace continuation is not performed by this body. *)
Definition event_delete_critical (sg : StableGlobVars) (eid : EventID) (kind : PendType) (opt : Z)
  : program UCOS2_Verify_State (addr * (OSErrCode * bool)) :=
  fun s result after => exists e,
    s.(EventState).(inUsedEventStates) eid = Some e /\
    let waiting := negb (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0) in
    if Z.eqb opt 0 then
      if waiting then result = (event_addr sg eid, (OS_ERR_TASK_WAITING, false)) /\ after = s
      else result = (0, (OS_ERR_NONE, false)) /\ after = event_delete_recycle_state sg s eid e
    else if Z.eqb opt 1 then
      exists priorities ready node,
        event_broadcast sg eid kind 0 PendAbort s priorities ready /\
        ready.(EventState).(inUsedEventStates) eid = Some node /\
        result = (0, (OS_ERR_NONE, waiting)) /\ after = event_delete_recycle_state sg ready eid node
    else result = (event_addr sg eid, (OS_ERR_INVALID_OPT, false)) /\ after = s.

Lemma event_delete_critical_exists : forall sg s eid e kind opt,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  exists result after, event_delete_critical sg eid kind opt s result after.
Proof.
  intros sg s eid e kind opt Hvalid He Hkind.
  set (waiting := negb (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0)).
  destruct (Z.eqb opt 0) eqn:Hnone.
  - destruct waiting eqn:Hwaiting.
    + exists (event_addr sg eid, (OS_ERR_TASK_WAITING, false)), s.
      exists e; split; [exact He|]; rewrite Hnone; fold waiting; rewrite Hwaiting; split; reflexivity.
    + exists (0, (OS_ERR_NONE, false)), (event_delete_recycle_state sg s eid e).
      exists e; split; [exact He|]; rewrite Hnone; fold waiting; rewrite Hwaiting; split; reflexivity.
  - destruct (Z.eqb opt 1) eqn:Halways.
    + destruct (event_broadcast_exists e.(waitList) sg s eid e kind 0 PendAbort
        Hvalid He Hkind eq_refl) as [priorities [ready [Hloop [_ [Hnode _]]]]].
      exists (0, (OS_ERR_NONE, waiting)), (event_delete_recycle_state sg ready eid (event_set_wait_list e [])).
      exists e; split; [exact He|]; rewrite Hnone, Halways; fold waiting.
      exists priorities, ready, (event_set_wait_list e []); repeat split; assumption || reflexivity.
    + exists (event_addr sg eid, (OS_ERR_INVALID_OPT, false)), s.
      exists e; split; [exact He|]; rewrite Hnone, Halways; split; reflexivity.
Qed.

Lemma event_delete_critical_deterministic : forall sg eid kind opt s r1 s1 r2 s2,
  event_delete_critical sg eid kind opt s r1 s1 -> event_delete_critical sg eid kind opt s r2 s2 ->
  r1 = r2 /\ s1 = s2.
Proof.
  intros sg eid kind opt s r1 s1 r2 s2 [e [He Hfirst]] [other [Hother Hsecond]].
  assert (other = e) by congruence; subst other.
  destruct (Z.eqb opt 0).
  - destruct (negb (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0));
      destruct Hfirst as [-> ->]; destruct Hsecond as [-> ->]; split; reflexivity.
  - destruct (Z.eqb opt 1).
    + destruct Hfirst as [ps1 [ready1 [node1 [Hloop1 [Hnode1 [-> ->]]]]]].
      destruct Hsecond as [ps2 [ready2 [node2 [Hloop2 [Hnode2 [-> ->]]]]]].
      destruct (event_broadcast_deterministic sg eid kind 0 PendAbort s ps1 ready1 ps2 ready2
        Hloop1 Hloop2) as [-> ->].
      assert (node1 = node2) by congruence; subst node2; split; reflexivity.
    + destruct Hfirst as [-> ->]; destruct Hsecond as [-> ->]; split; reflexivity.
Qed.

Lemma event_delete_critical_error_frame : forall sg s eid kind opt result after,
  event_delete_critical sg eid kind opt s result after -> fst (snd result) <> OS_ERR_NONE ->
  after = s /\
    (result = (event_addr sg eid, (OS_ERR_TASK_WAITING, false)) \/
     result = (event_addr sg eid, (OS_ERR_INVALID_OPT, false))).
Proof.
  intros sg s eid kind opt result after [e [He Hstep]] Herror.
  destruct (Z.eqb opt 0).
  - destruct (negb (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0)).
    + destruct Hstep as [-> ->]; split; [reflexivity|left; reflexivity].
    + destruct Hstep as [-> _]; contradiction Herror; reflexivity.
  - destruct (Z.eqb opt 1).
    + destruct Hstep as [ps [ready [node [_ [_ [-> _]]]]]]; contradiction Herror; reflexivity.
    + destruct Hstep as [-> ->]; split; [reflexivity|right; reflexivity].
Qed.

Lemma event_delete_recycle_removes_event : forall sg s eid e,
  (event_delete_recycle_state sg s eid e).(EventState).(inUsedEventStates) eid = None.
Proof. intros; apply kernel_map_set_same. Qed.

Lemma event_delete_recycle_preserves_buffers : forall sg s eid e,
  (event_delete_recycle_state sg s eid e).(EventState).(publishedQueueBytes) =
    s.(EventState).(publishedQueueBytes).
Proof. reflexivity. Qed.

Lemma event_delete_critical_success_removes_event : forall sg s eid kind opt result after,
  event_delete_critical sg eid kind opt s result after -> fst (snd result) = OS_ERR_NONE ->
  fst result = 0 /\ after.(EventState).(inUsedEventStates) eid = None.
Proof.
  intros sg s eid kind opt result after [e [He Hstep]] Hsuccess.
  destruct (Z.eqb opt 0).
  - destruct (negb (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0)).
    + destruct Hstep as [-> _]; discriminate Hsuccess.
    + destruct Hstep as [-> ->]; split; [reflexivity|apply event_delete_recycle_removes_event].
  - destruct (Z.eqb opt 1).
    + destruct Hstep as [ps [ready [node [_ [_ [-> ->]]]]]];
        split; [reflexivity|apply event_delete_recycle_removes_event].
    + destruct Hstep as [-> _]; discriminate Hsuccess.
Qed.

Lemma event_delete_critical_preserves_validity : forall sg s eid e kind opt result after,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  event_type_to_pend_type e.(eventType) = Some kind -> e.(eventType) <> OS_EVENT_TYPE_MUTEX ->
  event_delete_critical sg eid kind opt s result after -> UCOS2_state_inv sg after.
Proof.
  intros sg s eid e kind opt result after Hvalid He Hkind Hnonmutex [node [Hnode Hstep]].
  assert (node = e) by congruence; subst node.
  destruct (Z.eqb opt 0).
  - destruct (negb (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0)) eqn:Hwaiting.
    + destruct Hstep as [_ ->]; exact Hvalid.
    + destruct Hstep as [_ ->]; apply Bool.negb_false_iff in Hwaiting; apply Z.eqb_eq in Hwaiting.
      pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [_ [_ Hentries]]]]]] _]]]].
      apply (proj1 (encode_event_wait_grp_zero_iff_empty sg s.(TskState) e.(waitList)
        (proj1 (Hentries eid e He)))) in Hwaiting.
      unfold event_delete_recycle_state; eapply UCOS2_event_recycle_preserves_validity;
        [exact Hvalid|exact He|exact Hnonmutex|exact Hwaiting].
  - destruct (Z.eqb opt 1).
    + destruct Hstep as [ps [ready [node [Hloop [HreadyNode [_ ->]]]]]].
      pose proof (event_broadcast_result sg s eid e kind 0 PendAbort ps ready
        Hvalid He Hkind Hloop) as [Hready [Hlast _]].
      assert (node = event_set_wait_list e []) by congruence; subst node.
      unfold event_delete_recycle_state; eapply UCOS2_event_recycle_preserves_validity;
        [exact Hready|exact Hlast|exact Hnonmutex|reflexivity].
    + destruct Hstep as [_ ->]; exact Hvalid.
Qed.

Lemma event_delete_critical_preserves_invocation : forall sg s eid e kind opt result after invocation origin,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  event_delete_critical sg eid kind opt s result after ->
  task_invocation_active s.(TskState) invocation origin ->
  task_invocation_active after.(TskState) invocation origin.
Proof.
  intros sg s eid e kind opt result after invocation origin Hvalid He Hkind [node [Hnode Hstep]] Hactive.
  assert (node = e) by congruence; subst node.
  destruct (Z.eqb opt 0).
  - destruct (negb (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0));
      destruct Hstep as [_ ->]; exact Hactive.
  - destruct (Z.eqb opt 1).
    + destruct Hstep as [ps [ready [node [Hloop [_ [_ ->]]]]]].
      exact (event_broadcast_preserves_invocation sg eid kind 0 PendAbort s ps ready Hloop
        e invocation origin Hvalid He Hkind Hactive).
    + destruct Hstep as [_ ->]; exact Hactive.
Qed.

(** The ECB may already be free before the original Pend invocation
    resumes.  Its TCB receives the exact abort endpoint, not a promise
    of immediate execution or an additional application resource. *)
Lemma event_delete_always_updates_waiter : forall sg s eid e kind result after tid old,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  event_delete_critical sg eid kind 1 s result after ->
  In tid e.(waitList) -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  after.(TskState).(inUsedTaskStates) tid = Some (task_event_wake_single old kind 0 PendAbort).
Proof.
  intros sg s eid e kind result after tid old Hvalid He Hkind [node [Hnode Hstep]] Hin Hold.
  assert (node = e) by congruence; subst node.
  destruct Hstep as [ps [ready [node [Hloop [_ [_ ->]]]]]].
  exact (event_broadcast_updates_waiter sg eid kind 0 PendAbort s ps ready Hloop
    e tid old Hvalid He Hkind Hin Hold).
Qed.

Lemma event_delete_critical_requests_schedule_iff : forall sg s eid e kind opt result after,
  s.(EventState).(inUsedEventStates) eid = Some e -> event_delete_critical sg eid kind opt s result after ->
  (snd (snd result) = true <-> opt = 1 /\ encode_event_wait_grp e.(waitList) s.(TskState) <> 0).
Proof.
  intros sg s eid e kind opt result after He [node [Hnode Hstep]].
  assert (node = e) by congruence; subst node.
  destruct (Z.eqb opt 0) eqn:Hnone.
  - apply Z.eqb_eq in Hnone; subst opt.
    destruct (negb (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0));
      destruct Hstep as [-> _]; simpl; split; [discriminate|intros [H _]; discriminate|
        discriminate|intros [H _]; discriminate].
  - destruct (Z.eqb opt 1) eqn:Halways.
    + apply Z.eqb_eq in Halways; subst opt.
      destruct Hstep as [ps [ready [node [_ [_ [-> _]]]]]]; simpl.
      rewrite Bool.negb_true_iff, Z.eqb_neq; tauto.
    + apply Z.eqb_neq in Halways; destruct Hstep as [-> _]; simpl.
      split; [discriminate|intros [H _]; contradiction].
Qed.

(** The typed Sem/Mbox family excludes Queue; the Event-owned invariant
    then supplies the absent Queue payload.  This is not a new source
    guard or an extra application precondition.  Queue's QCB/buffer
    binding cannot be forgotten by an ECB-only recycling proof. *)
Lemma event_delete_critical_preserves_residual : forall sg s eid e kind opt result after,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  event_type_to_pend_type e.(eventType) = Some kind -> e.(eventType) <> OS_EVENT_TYPE_Q ->
  event_delete_critical sg eid kind opt s result after ->
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |-- UCOS2_raw_rep_missing_task_storage_sched_event sg after.
Proof.
  intros sg s eid e kind opt result after Hvalid He Hkind Hnonqueue [node [Hnode Hstep]].
  assert (Hnone : e.(queueFields) = None).
  { pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [Hfields _]]]] _]]]].
    apply non_queue_event_has_no_queue_fields; [exact (Hfields eid e He)|exact Hnonqueue]. }
  assert (node = e) by congruence; subst node.
  destruct (Z.eqb opt 0).
  - destruct (negb (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0)).
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [_ ->]; apply UCOS2_event_recycle_preserves_residual with (node := e); assumption.
  - destruct (Z.eqb opt 1).
    + destruct Hstep as [ps [ready [node [Hloop [HreadyNode [_ ->]]]]]].
      pose proof (event_broadcast_result sg s eid e kind 0 PendAbort ps ready Hvalid He Hkind Hloop)
        as [Hready [Hlast _]].
      assert (node = event_set_wait_list e []) by congruence; subst node.
      eapply derivable1_trans.
      * exact (event_broadcast_preserves_residual sg eid kind 0 PendAbort s ps ready Hloop e Hvalid He Hkind).
      * apply UCOS2_event_recycle_preserves_residual with (node := event_set_wait_list e []);
          [exact Hlast|exact Hnone].
    + destruct Hstep as [_ ->]; reflexivity.
Qed.

Lemma event_delete_critical_merge_resources : forall sg s eid e kind opt result after,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  event_type_to_pend_type e.(eventType) = Some kind -> e.(eventType) <> OS_EVENT_TYPE_MUTEX ->
  e.(eventType) <> OS_EVENT_TYPE_Q -> event_delete_critical sg eid kind opt s result after ->
  task_public_storage sg after.(TskState) **
  sched_raw_rep sg after.(TskState) after.(SchedState) **
  event_raw_rep sg after.(TskState) after.(EventState) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |-- UCOS2_inv sg after.
Proof.
  intros sg s eid e kind opt result after Hvalid He Hkind Hnonmutex Hnonqueue Hstep.
  pose proof (event_delete_critical_preserves_validity
    sg s eid e kind opt result after Hvalid He Hkind Hnonmutex Hstep) as Hpost.
  sep_apply_l_atomic (event_delete_critical_preserves_residual
    sg s eid e kind opt result after Hvalid He Hkind Hnonqueue Hstep).
  unfold UCOS2_inv, UCOS2_raw_rep, task_shared_rep,
    UCOS2_raw_rep_missing_task_storage_sched, UCOS2_raw_rep_missing_task_storage_sched_event; entailer!.
Qed.
