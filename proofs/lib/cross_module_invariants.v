Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_retirement.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.flag.
Import UCOS2_C_Rules.
Import TaskStateDef.
Import EventStateDef.
Import SchedStateDef.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope list.

(* ================================================================== *)
(* Phase 6 Task 6.2:跨模块不变式(6 条 + 汇总)                          *)
(* ================================================================== *)

(* 7.3.1: OSPrioCur ↔ OSTCBCur.OSTCBPrio 一致性 *)
Definition osprio_cur_consistency (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Prop :=
  match s.(SchedState).(curTaskID) with
  | None => s.(SchedState).(curSchedPrio) = None
  | Some tid =>
      exists t, s.(TskState).(inUsedTaskStates) tid = Some t /\
      s.(SchedState).(curSchedPrio) = Some t.(curPrio)
  end.

(* 7.3.2: OSTCBPrioTbl 一致性 *)
Definition priotbl_consistency (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Prop :=
  forall p,
    match (s.(TskState).(prioTbl)) p with
    | PTFree =>
        ~ (exists tid, In tid s.(SchedState).(readyList) /\
                      exists t, s.(TskState).(inUsedTaskStates) tid = Some t /\
                      t.(curPrio) = p) /\
        ~ (exists mid e m, s.(EventState).(inUsedEventStates) mid = Some e /\
                          e.(eventType) = OS_EVENT_TYPE_MUTEX /\
                          e.(mutexFields) = Some m /\
                          mutex_reserves_priority_slot sg m p)
    | PTReserved =>
        exists mid e m, s.(EventState).(inUsedEventStates) mid = Some e /\
                        e.(eventType) = OS_EVENT_TYPE_MUTEX /\
                        e.(mutexFields) = Some m /\ m.(mfPCP) = p /\
                        (match m.(mfOwner) with
                         | None => True
                         | Some tid =>
                             exists t op,
                               s.(TskState).(inUsedTaskStates) tid = Some t /\
                               m.(mfOwnerOrigPrio) = Some op /\
                               t.(curPrio) = op
                         end)
    | PTTask tid =>
        (* Besides the current-priority and PCP slots, uC/OS-II retains the
           owner's original-priority PTTask slot during inheritance. *)
        (* PTTask 有两种来源:
           - 来源 1(task 注册):curPrio(tid) = p
           - 来源 2(mutex 占用):某 mutex 的 mfPCP = p 且 owner = tid
           µC/OS-II 中同一 task 可同时在多个下标下都是 PTTask
           (例如 prioTbl[curPrio] = task 注册占; prioTbl[mfPCP1] = mutex1 占;
            prioTbl[mfPCP2] = mutex2 占)。 *)
        exists t, s.(TskState).(inUsedTaskStates) tid = Some t /\
        (t.(curPrio) = p \/
         exists mid e m, s.(EventState).(inUsedEventStates) mid = Some e /\
                         e.(eventType) = OS_EVENT_TYPE_MUTEX /\
                         e.(mutexFields) = Some m /\
                         m.(mfOwner) = Some tid /\
                         (m.(mfPCP) = p \/
                          m.(mfOwnerOrigPrio) = Some p))
    end.

(** The real priority table distinguishes creator reservations, mutex
    reservations and live task aliases. No view rewrites a reserved slot to
    PTFree. Task-local validity owns the invocation/reservation ledger; this
    relation states only its interaction with mutex claims and live aliases.
    Table observations range over actual array indices.  Values of the
    total Coq map outside that domain do not represent extra C cells. *)
Definition pending_mutex_priority_claim (events : Glob_EventAbstractState) (p : Priority) : Prop :=
  exists eid queue, event_mutex_lease_view events eid = Some (p, queue).

(** A pending PCP is an invocation-owned private-ECB lease.  Its one real
    table cell is PTReserved; it is disjoint from task-creation leases and
    published mutex claims, and is unique among private ECBs. *)
Definition pending_mutex_consistency (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (events : Glob_EventAbstractState) : Prop :=
  forall eid pcp queue,
    event_mutex_lease_view events eid = Some (pcp, queue) ->
    valid_mutex_pcp sg pcp /\ pcp <> sg.(osPrioMutexCeilDis) /\
    queue = None /\ tasks.(prioTbl) pcp = PTReserved /\
    tasks.(taskLifecycle).(taskReservations) pcp = None /\
    ~ (exists mid e m, events.(inUsedEventStates) mid = Some e /\
        e.(eventType) = OS_EVENT_TYPE_MUTEX /\ e.(mutexFields) = Some m /\
        mutex_reserves_priority_slot sg m pcp) /\
    (forall other other_queue,
      event_mutex_lease_view events other = Some (pcp, other_queue) -> other = eid).

Lemma pending_mutex_priority_claim_view_eq : forall before after,
  event_mutex_lease_view after = event_mutex_lease_view before ->
  forall p, pending_mutex_priority_claim after p <-> pending_mutex_priority_claim before p.
Proof. intros; unfold pending_mutex_priority_claim; rewrite H; reflexivity. Qed.

Lemma pending_mutex_consistency_frame : forall sg tasks events tasks' events',
  tasks'.(prioTbl) = tasks.(prioTbl) ->
  tasks'.(taskLifecycle).(taskReservations) = tasks.(taskLifecycle).(taskReservations) ->
  event_mutex_lease_view events' = event_mutex_lease_view events ->
  (forall p,
    (exists mid e m, events'.(inUsedEventStates) mid = Some e /\
      e.(eventType) = OS_EVENT_TYPE_MUTEX /\ e.(mutexFields) = Some m /\
      mutex_reserves_priority_slot sg m p) ->
    (exists mid e m, events.(inUsedEventStates) mid = Some e /\
      e.(eventType) = OS_EVENT_TYPE_MUTEX /\ e.(mutexFields) = Some m /\
      mutex_reserves_priority_slot sg m p)) ->
  pending_mutex_consistency sg tasks events -> pending_mutex_consistency sg tasks' events'.
Proof.
  intros sg tasks events tasks' events' Htable Hreservations Hview Hclaims Hvalid eid pcp queue Hlease.
  rewrite Hview in Hlease.
  destruct (Hvalid eid pcp queue Hlease)
    as [Hpcp [Henabled [Hqueue [Hreserved [Hnocreator [Hnolive Hunique]]]]]].
  split; [exact Hpcp|]. split; [exact Henabled|]. split; [exact Hqueue|].
  split; [rewrite Htable; exact Hreserved|].
  split; [rewrite Hreservations; exact Hnocreator|].
  split; [intros Hclaim; apply Hnolive; apply Hclaims; exact Hclaim|].
  intros other other_queue Hother; rewrite Hview in Hother; eapply Hunique; exact Hother.
Qed.

Lemma pending_mutex_consistency_free_slot_excludes_claim : forall sg tasks events p,
  pending_mutex_consistency sg tasks events -> tasks.(prioTbl) p = PTFree ->
  ~ pending_mutex_priority_claim events p.
Proof.
  intros sg tasks events p Hvalid Hfree [eid [queue Hlease]].
  destruct (Hvalid eid p queue Hlease) as [_ [_ [_ [Hreserved _]]]]; congruence.
Qed.

Lemma pending_mutex_consistency_task_reservation_excludes_claim : forall sg tasks events p entry,
  pending_mutex_consistency sg tasks events ->
  tasks.(taskLifecycle).(taskReservations) p = Some entry ->
  ~ pending_mutex_priority_claim events p.
Proof.
  intros sg tasks events p entry Hvalid Hentry [eid [queue Hlease]].
  destruct (Hvalid eid p queue Hlease) as [_ [_ [_ [_ [Hnone _]]]]]; congruence.
Qed.

Lemma pending_mutex_consistency_task_slot_excludes_claim : forall sg tasks events p tid,
  pending_mutex_consistency sg tasks events -> tasks.(prioTbl) p = PTTask tid ->
  ~ pending_mutex_priority_claim events p.
Proof.
  intros sg tasks events p tid Hvalid Htask [eid [queue Hlease]].
  destruct (Hvalid eid p queue Hlease) as [_ [_ [_ [Hreserved _]]]]; congruence.
Qed.

Lemma pending_mutex_consistency_table_transport : forall sg tasks tasks' events,
  (forall p, pending_mutex_priority_claim events p -> tasks'.(prioTbl) p = tasks.(prioTbl) p) ->
  (forall p, pending_mutex_priority_claim events p ->
    tasks'.(taskLifecycle).(taskReservations) p = tasks.(taskLifecycle).(taskReservations) p) ->
  pending_mutex_consistency sg tasks events -> pending_mutex_consistency sg tasks' events.
Proof.
  intros sg tasks tasks' events Htable Hreservations Hvalid eid pcp queue Hlease.
  assert (Hclaim : pending_mutex_priority_claim events pcp) by (exists eid, queue; exact Hlease).
  destruct (Hvalid eid pcp queue Hlease) as [Hpcp [Henabled [Hqueue [Hreserved [Hnone Hrest]]]]].
  split; [exact Hpcp|]. split; [exact Henabled|]. split; [exact Hqueue|].
  split; [rewrite Htable by exact Hclaim; exact Hreserved|].
  split; [rewrite Hreservations by exact Hclaim; exact Hnone|exact Hrest].
Qed.

Lemma pending_mutex_consistency_event_transport : forall sg tasks events events',
  event_mutex_lease_view events' = event_mutex_lease_view events ->
  (forall slot node, events'.(inUsedEventStates) slot = Some node ->
    node.(eventType) = OS_EVENT_TYPE_MUTEX ->
    exists old, events.(inUsedEventStates) slot = Some old /\
      old.(eventType) = OS_EVENT_TYPE_MUTEX /\ node.(mutexFields) = old.(mutexFields)) ->
  pending_mutex_consistency sg tasks events -> pending_mutex_consistency sg tasks events'.
Proof.
  intros sg tasks events events' Hview Horigin Hvalid.
  eapply pending_mutex_consistency_frame; [reflexivity|reflexivity|exact Hview| |exact Hvalid].
  intros p [mid [node [m [Hnode [Htype [Hm Hclaim]]]]]].
  destruct (Horigin mid node Hnode Htype) as [old [Hold [HtypeOld Hfields]]].
  exists mid, old, m; split; [exact Hold|]. split; [exact HtypeOld|].
  split; [rewrite <- Hfields; exact Hm|exact Hclaim].
Qed.

Lemma pending_mutex_consistency_private_write : forall sg tasks events eid allocation field stored,
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  pending_mutex_consistency sg tasks events ->
  pending_mutex_consistency sg tasks (event_private_write events eid allocation field stored).
Proof.
  intros; eapply pending_mutex_consistency_frame;
    [reflexivity|reflexivity|apply event_mutex_lease_view_private_write_eq; exact H| |exact H0].
  intros p Hclaim; exact Hclaim.
Qed.

Lemma pending_mutex_consistency_detach_head : forall sg tasks events eid rest image,
  events.(eventLifecycle).(eventPrivate) eid = None ->
  pending_mutex_consistency sg tasks events ->
  pending_mutex_consistency sg tasks (event_detach_head events eid rest image).
Proof.
  intros; eapply pending_mutex_consistency_frame;
    [reflexivity|reflexivity|apply event_mutex_lease_view_detach_head_eq; exact H| |exact H0].
  intros p Hclaim; exact Hclaim.
Qed.

Definition task_mutex_priotbl_consistency (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (events : Glob_EventAbstractState) : Prop :=
  (forall p entry, tasks.(taskLifecycle).(taskReservations) p = Some entry ->
    ~ (exists mid e m, events.(inUsedEventStates) mid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_MUTEX /\ e.(mutexFields) = Some m /\
       mutex_reserves_priority_slot sg m p)) /\
  (forall p, task_priority_in_range sg p -> match tasks.(prioTbl) p with
   | PTFree =>
       ~ (exists mid e m, events.(inUsedEventStates) mid = Some e /\
          e.(eventType) = OS_EVENT_TYPE_MUTEX /\ e.(mutexFields) = Some m /\
          mutex_reserves_priority_slot sg m p)
   | PTReserved =>
       (exists entry, tasks.(taskLifecycle).(taskReservations) p = Some entry) \/
       (exists mid e m, events.(inUsedEventStates) mid = Some e /\
          e.(eventType) = OS_EVENT_TYPE_MUTEX /\ e.(mutexFields) = Some m /\
          mutex_reserves_priority_slot sg m p) \/
       pending_mutex_priority_claim events p
   | PTTask tid => exists t, tasks.(inUsedTaskStates) tid = Some t
   end) /\
  mutex_priority_alias_consistency sg tasks events.

Lemma task_mutex_priotbl_consistency_lifecycle_ext : forall sg before after events,
  after.(inUsedTaskStates) = before.(inUsedTaskStates) ->
  after.(prioTbl) = before.(prioTbl) ->
  (forall p, (exists e, after.(taskLifecycle).(taskReservations) p = Some e) <->
             (exists e, before.(taskLifecycle).(taskReservations) p = Some e)) ->
  task_mutex_priotbl_consistency sg before events ->
  task_mutex_priotbl_consistency sg after events.
Proof.
  intros sg before after events Hused Htable Hdomain [Hcreator [Hslots Halias]].
  split.
  - intros p entry Hentry Hclaim.
    destruct (proj1 (Hdomain p) (ex_intro _ entry Hentry)) as [old Hold].
    exact (Hcreator p old Hold Hclaim).
  - split.
    + intros p Hp; rewrite Htable; specialize (Hslots p Hp).
      destruct (before.(prioTbl) p).
      * exact Hslots.
      * destruct Hslots as [Hreservation | Hmutex].
        -- left; apply Hdomain; exact Hreservation.
        -- right; exact Hmutex.
      * rewrite Hused; exact Hslots.
    + eapply mutex_priority_alias_consistency_ext; eauto.
Qed.

Lemma task_creator_reservation_not_ready : forall sg tasks sched p entry,
  task_in_range sg tasks ->
  tasks.(taskLifecycle).(taskReservations) p = Some entry ->
  ~ (exists tid, In tid sched.(readyList) /\ exists t,
     tasks.(inUsedTaskStates) tid = Some t /\ t.(curPrio) = p).
Proof.
  intros sg tasks sched p entry
    [_ [_ [_ [Hres [_ [Hregistered _]]]]]] Hentry [tid [_ [t [Ht Hp]]]].
  pose proof (proj1 Hres p entry Hentry) as [_ [Hreserved _]].
  specialize (Hregistered tid t Ht); rewrite Hp, Hreserved in Hregistered; discriminate.
Qed.

(* 7.3.3: mutex owner 与 task 一致性 *)
(* The API permits the defensive non-ready-owner path: an owner may be waiting
   on a different kernel object.  It may not, however, occur in the wait list
   of the very mutex it owns.  Keeping this object-local lifecycle fact here
   rules out a self-wait state without excluding the defensive cross-object
   case. *)
Definition mutex_owner_consistency (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Prop :=
  forall mid e m, s.(EventState).(inUsedEventStates) mid = Some e /\
                  e.(eventType) = OS_EVENT_TYPE_MUTEX /\
                  e.(mutexFields) = Some m ->
    match m.(mfOwner) with
    | None => True
    | Some tid =>
        exists t op,
          s.(TskState).(inUsedTaskStates) tid = Some t /\
          m.(mfOwnerOrigPrio) = Some op /\
          (t.(curPrio) = op \/
           (m.(mfPCP) <> sg.(osPrioMutexCeilDis) /\ t.(curPrio) = m.(mfPCP))) /\
          ~ In tid e.(waitList)
    end.

(* 7.3.4: event waitList 与 task eventPtr/eventMultiWaitEvents 双向一致性 *)
(* 7.3.5: ready_list 完整性 *)
Definition ready_list_completeness (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Prop :=
  forall tid t, s.(TskState).(inUsedTaskStates) tid = Some t ->
    is_effectively_ready t.(stat) t.(dly) = true ->
    In tid s.(SchedState).(readyList).

(* 7.3.6: ready_list 排序与唯一性 *)
Definition ready_list_order (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Prop :=
  strictly_sorted_by
    (fun tid => match s.(TskState).(inUsedTaskStates) tid with
                | Some t => t.(curPrio)
                | None => sg.(osLowestPrio) + 1
                end)
    s.(SchedState).(readyList) /\
  NoDup s.(SchedState).(readyList).

(* 7.3.7:OS_PRIO_MUTEX_CEIL_DIS 对应的 total-map observation 必须为
   PTFree。该值是 PCP-disabled tag，不是可被 mutex 预留的真实表下标；
   因此一个 live mutex 可以把它存入 mfPCP，但不能据此占用 priority
   table slot。*)
Definition ceiling_priotbl_free (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Prop :=
  (s.(TskState).(prioTbl)) sg.(osPrioMutexCeilDis) = PTFree.

(* 7.3.8: task_priority_unique — 所有 in-used task 的 curPrio 互不相同。
   µC/OS-II 语义:每个优先级至多对应一个 task。该不变式用于排除
   cross_module_consistency_preserved_by_release_with_handover 和
   cross_module_consistency_preserved_by_task_set_curPrio 中的 curPrio 碰撞
   (嵌套 mutex 场景下 new_owner_t'.curPrio = new_owner_t.curPrio 可能与
   readyList 中其他 task 的 curPrio 相同)。*)
Definition task_priority_unique_prop (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Prop :=
  task_priority_unique (TskState s).

(* 7.3.9: mutex PCP lifecycle ownership.

   For a well-configured live mutex, an enabled PCP slot is either reserved
   or still contains the owning task (the source deliberately retains that
   alias until Post/Del overwrites it).  An owner's saved priority cannot be
   the enabled PCP itself: the slot was reserved before that task acquired the
   mutex.  This deliberately does not require [ownerOrigPrio > PCP], because
   the source can acquire/transfer first and then report PCP_LOWER when the
   configured ceiling is too low. *)
Definition mutex_protocol_consistency (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Prop :=
  forall mid e m,
    s.(EventState).(inUsedEventStates) mid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    valid_mutex_pcp sg m.(mfPCP) /\
    (match m.(mfOwner), m.(mfOwnerOrigPrio) with
     | None, None => True
     | Some _, Some op =>
         task_priority_in_range sg op /\
         (m.(mfPCP) <> sg.(osPrioMutexCeilDis) -> op <> m.(mfPCP))
     | _, _ => False
     end) /\
    (m.(mfPCP) = sg.(osPrioMutexCeilDis) \/
     (m.(mfPCP) <> sg.(osPrioMutexCeilDis) /\
      (s.(TskState).(prioTbl) m.(mfPCP) = PTReserved \/
       exists owner,
         m.(mfOwner) = Some owner /\
         s.(TskState).(prioTbl) m.(mfPCP) = PTTask owner))).

(* 7.3.10: enabled PCP slots are unique among live mutexes.

   OSMutexCreate checks the priority table slot before reserving an enabled
   PCP.  Consequently two simultaneously live mutexes cannot own the same
   enabled PCP.  The disabled value is intentionally excluded: it is a tag,
   not a priority-table slot, and any number of mutexes may store it.

   Promotion record:
   - layer/scope: L3 cross-module lifecycle invariant, mutex operation family;
   - source basis: Create's check-then-reserve of an enabled priority slot;
   - preservation: the transport lemma below plus operation-specific Qed
     instances for wait-list updates, acquire, release, and handover;
   - expected reusers: Create/Post/Delete/RdyAtPrio invariant closure;
   - insufficiency of the old model: mutex_protocol_consistency constrained
     each object separately but did not make the enabled-PCP claimant unique. *)
Definition mutex_enabled_pcp_unique (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Prop :=
  forall mid1 e1 m1 mid2 e2 m2,
    s.(EventState).(inUsedEventStates) mid1 = Some e1 ->
    e1.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e1.(mutexFields) = Some m1 ->
    s.(EventState).(inUsedEventStates) mid2 = Some e2 ->
    e2.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e2.(mutexFields) = Some m2 ->
    m1.(mfPCP) = m2.(mfPCP) ->
    m1.(mfPCP) <> sg.(osPrioMutexCeilDis) ->
    mid1 = mid2.

(* A reusable L3/L4 transport interface: an operation preserves PCP
   uniqueness whenever every live mutex in the post-state can be traced back
   to a live mutex at the same EventID with the same PCP in the pre-state. *)
Lemma mutex_enabled_pcp_unique_transport :
  forall sg lvs1 lvs2,
    (forall mid e2 m2,
      (EventState lvs2).(inUsedEventStates) mid = Some e2 ->
      e2.(eventType) = OS_EVENT_TYPE_MUTEX ->
      e2.(mutexFields) = Some m2 ->
      exists e1 m1,
        (EventState lvs1).(inUsedEventStates) mid = Some e1 /\
        e1.(eventType) = OS_EVENT_TYPE_MUTEX /\
        e1.(mutexFields) = Some m1 /\
        m1.(mfPCP) = m2.(mfPCP)) ->
    mutex_enabled_pcp_unique sg lvs1 ->
    mutex_enabled_pcp_unique sg lvs2.
Proof.
  intros sg lvs1 lvs2 Hback Hunique.
  unfold mutex_enabled_pcp_unique in *.
  intros mid1 e1 m1 mid2 e2 m2
    Hget1 Htype1 Hmf1 Hget2 Htype2 Hmf2 Hpcp Henabled.
  destruct (Hback mid1 e1 m1 Hget1 Htype1 Hmf1)
    as [e1_old [m1_old [Hget1_old [Htype1_old [Hmf1_old Hpcp1]]]]].
  destruct (Hback mid2 e2 m2 Hget2 Htype2 Hmf2)
    as [e2_old [m2_old [Hget2_old [Htype2_old [Hmf2_old Hpcp2]]]]].
  eapply Hunique.
  - exact Hget1_old.
  - exact Htype1_old.
  - exact Hmf1_old.
  - exact Hget2_old.
  - exact Htype2_old.
  - exact Hmf2_old.
  - congruence.
  - congruence.
Qed.

(* 7.3.11: 全局汇总 *)
Definition verification_slice_cross_module_consistency (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Prop :=
  osprio_cur_consistency sg s /\
  priotbl_consistency sg s /\
  mutex_owner_consistency sg s /\
  verification_slice_event_wait_object_consistency sg s /\
  ready_list_completeness sg s /\
  ready_list_order sg s /\
  ceiling_priotbl_free sg s /\
  task_priority_unique_prop sg s /\
  mutex_protocol_consistency sg s /\
  mutex_enabled_pcp_unique sg s.

(** With TaskDelete enabled, OS_FlagBlock publishes the stack node pointer
    in the TCB, and OS_FlagUnlink clears it. The selected TCB64 layout
    has this field. A timed-out task may be ready while the same node stays
    linked until cleanup; registration must still name its original TCB
    generation. Single-wait tasks do not simultaneously register on an
    OS_EVENT, including the timeout-cleanup interval. No stack bytes are
    owned by this pure relationship. *)
Definition task_flag_waiter_consistency (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (flags : GlobFlagState) : Prop :=
  (forall p w, flags.(flagWaitNodes) p = Some w -> p <> 0 /\ exists t,
     tasks.(inUsedTaskStates) w.(flagTask) = Some t /\
     t.(taskGeneration) = w.(flagTaskGeneration) /\
     t.(tcbFlagNode) = p /\
     w.(flagWaitImage).(flagNodeTCB) = task_slot_addr sg w.(flagTask) /\
     task_linked_wait_phase t PendFlag /\
     t.(eventPtr) = None /\ t.(eventMultiWaitEvents) = []) /\
  (forall tid t, tasks.(inUsedTaskStates) tid = Some t ->
     (t.(tcbFlagNode) <> 0 \/ (task_non_suspension_bits t.(stat)) = task_pend_mask PendFlag) ->
     exists w, flags.(flagWaitNodes) t.(tcbFlagNode) = Some w /\
       w.(flagTask) = tid).

Lemma task_flag_waiter_has_live_generation : forall sg tasks flags p w,
  task_flag_waiter_consistency sg tasks flags -> flags.(flagWaitNodes) p = Some w ->
  exists t, tasks.(inUsedTaskStates) w.(flagTask) = Some t /\
    t.(taskGeneration) = w.(flagTaskGeneration).
Proof.
  intros sg tasks flags p w [Hnodes _] Hw.
  destruct (Hnodes p w Hw) as [_ [t [Ht [Hg _]]]]; exists t; auto.
Qed.

Lemma task_flag_waiter_consistency_empty : forall sg tasks flags,
  (forall p, flags.(flagWaitNodes) p = None) ->
  (forall tid t, tasks.(inUsedTaskStates) tid = Some t ->
     t.(tcbFlagNode) = 0 /\ (task_non_suspension_bits t.(stat)) <> task_pend_mask PendFlag) ->
  task_flag_waiter_consistency sg tasks flags.
Proof.
  intros sg tasks flags Hempty Htasks; split.
  - intros p w Hw; rewrite Hempty in Hw; discriminate.
  - intros tid t Ht Hactive; destruct (Htasks tid t Ht); destruct Hactive; congruence.
Qed.

Lemma task_flag_waiter_consistency_nodes_frame : forall sg tasks before after,
  after.(flagWaitNodes) = before.(flagWaitNodes) ->
  task_flag_waiter_consistency sg tasks before -> task_flag_waiter_consistency sg tasks after.
Proof. intros; unfold task_flag_waiter_consistency in *; rewrite H; exact H0. Qed.

Lemma task_flag_waiter_unique_per_task : forall sg tasks flags p q a b,
  task_flag_waiter_consistency sg tasks flags ->
  flags.(flagWaitNodes) p = Some a -> flags.(flagWaitNodes) q = Some b ->
  a.(flagTask) = b.(flagTask) -> p = q.
Proof.
  intros sg tasks flags p q a b [Hnodes _] Ha Hb Htask.
  destruct (Hnodes p a Ha) as [_ [ta [Hta [_ [Hpa _]]]]].
  destruct (Hnodes q b Hb) as [_ [tb [Htb [_ [Hpb _]]]]].
  rewrite Htask in Hta; rewrite Htb in Hta; inversion Hta; congruence.
Qed.

Lemma task_flag_null_pointer_has_no_waiter : forall sg tasks flags tid t,
  task_flag_waiter_consistency sg tasks flags -> tasks.(inUsedTaskStates) tid = Some t ->
  t.(tcbFlagNode) = 0 ->
  ~ exists p w, flags.(flagWaitNodes) p = Some w /\ w.(flagTask) = tid.
Proof.
  intros sg tasks flags tid t [Hnodes _] Ht Hnull [p [w [Hw Htid]]].
  destruct (Hnodes p w Hw) as [Hnonzero [found [Hfound [_ [Hptr _]]]]].
  rewrite Htid, Ht in Hfound; inversion Hfound; subst found; congruence.
Qed.

Lemma task_flag_waiter_consistency_update_task : forall sg tasks flags tid old new,
  tasks.(inUsedTaskStates) tid = Some old ->
  new.(taskGeneration) = old.(taskGeneration) ->
  new.(tcbFlagNode) = old.(tcbFlagNode) ->
  new.(eventPtr) = old.(eventPtr) -> new.(eventMultiWaitEvents) = old.(eventMultiWaitEvents) ->
  (task_linked_wait_phase old PendFlag -> task_linked_wait_phase new PendFlag) ->
  ((task_non_suspension_bits new.(stat)) = task_pend_mask PendFlag -> (task_non_suspension_bits old.(stat)) = task_pend_mask PendFlag) ->
  task_flag_waiter_consistency sg tasks flags ->
  task_flag_waiter_consistency sg (glob_task_set_usedtask tasks tid new) flags.
Proof.
  intros sg tasks flags tid old new Hold Hg Hptr Hevent Hmulti Hphase Hpending [Hnodes Htasks].
  split.
  - intros p w Hw; destruct (Hnodes p w Hw)
      as [Hp [t [Ht [Hgen [Hnode [Haddr [Hwait [Hnoevent Hnomulti]]]]]]]].
    split; [exact Hp|]. cbn [glob_task_set_usedtask inUsedTaskStates].
    destruct (Z.eqb w.(flagTask) tid) eqn:E.
    + apply Z.eqb_eq in E; rewrite E, Hold in Ht; inversion Ht; subst t.
      exists new; split; [reflexivity|]. split; [rewrite Hg; exact Hgen|].
      split; [rewrite Hptr; exact Hnode|]. split; [exact Haddr|].
      split; [apply Hphase; exact Hwait|]. split; [rewrite Hevent|rewrite Hmulti]; assumption.
    + exists t; repeat split; assumption.
  - intros slot t Ht Hactive; cbn [glob_task_set_usedtask inUsedTaskStates] in Ht.
    destruct (Z.eqb slot tid) eqn:E.
    + apply Z.eqb_eq in E; subst slot; inversion Ht; subst t.
      assert (HactiveOld : old.(tcbFlagNode) <> 0 \/
        (task_non_suspension_bits old.(stat)) = task_pend_mask PendFlag).
      { destruct Hactive as [Hnonzero|Hpend]; [left; congruence|right; auto]. }
      destruct (Htasks tid old Hold HactiveOld) as [w [Hw Htid]].
      exists w; rewrite Hptr; auto.
    + exact (Htasks slot t Ht Hactive).
Qed.

Lemma tick_task_preserves_flag_waiter_consistency : forall sg tasks flags tid t,
  tasks.(inUsedTaskStates) tid = Some t -> task_flag_waiter_consistency sg tasks flags ->
  task_flag_waiter_consistency sg
    (glob_task_set_usedtask tasks tid (tick_task_update t)) flags.
Proof.
  intros sg tasks flags tid t Ht Hcross.
  pose proof (tick_task_preserves_non_timeout_fields t) as Hframe.
  cbv zeta in Hframe.
  eapply task_flag_waiter_consistency_update_task; try eassumption;
    try (clear - Hframe; tauto).
  - apply tick_preserves_linked_phase.
  - unfold tick_task_update; destruct (Z.eqb t.(dly) 0); [auto|].
    destruct (Z.eqb (t.(dly) - 1) 0); simpl; [|auto].
    intro Hpending; exfalso.
    exact (task_status_after_timeout_no_single_pending t.(stat) PendFlag
      ltac:(discriminate) Hpending).
Qed.

Lemma task_commit_preserves_flag_waiter_consistency : forall sg tasks flags p invocation node,
  tasks.(inUsedTaskStates) node.(taskID) = None ->
  node.(tcbFlagNode) = 0 -> (task_non_suspension_bits node.(stat)) = 0 ->
  task_flag_waiter_consistency sg tasks flags ->
  task_flag_waiter_consistency sg (task_commit tasks p invocation node) flags.
Proof.
  intros sg tasks flags p invocation node Hnone Hnull Hpending [Hnodes Htasks].
  split.
  - intros q w Hw; destruct (Hnodes q w Hw)
      as [Hq [old [Hold [Hg [Hptr [Haddr [Hphase [Hevent Hmulti]]]]]]]].
    destruct (task_commit_transports_old_fields tasks p invocation node
      w.(flagTask) old Hnone Hold) as [new [Hnew Hfields]].
    pose proof (f_equal taskGeneration Hfields) as Hgen; simpl in Hgen.
    pose proof (f_equal tcbFlagNode Hfields) as HflagNode; simpl in HflagNode.
    pose proof (f_equal stat Hfields) as Hstat; simpl in Hstat.
    pose proof (f_equal statPend Hfields) as Hpend; simpl in Hpend.
    pose proof (f_equal dly Hfields) as Hdly; simpl in Hdly.
    pose proof (f_equal eventPtr Hfields) as HeventFrame; simpl in HeventFrame.
    pose proof (f_equal eventMultiWaitEvents Hfields) as HmultiFrame; simpl in HmultiFrame.
    split; [exact Hq|]. exists new; split; [exact Hnew|].
    split; [rewrite Hgen; exact Hg|]. split; [rewrite HflagNode; exact Hptr|].
    split; [exact Haddr|]. split.
    + unfold task_linked_wait_phase in *; rewrite Hstat, Hpend, Hdly; exact Hphase.
    + split; [rewrite HeventFrame|rewrite HmultiFrame]; assumption.
  - intros tid new Hnew Hactive.
    destruct (Z.eq_dec tid node.(taskID)) as [Heq|Hneq].
    + subst tid; rewrite (proj1 (task_commit_publication_fields_eq
        tasks p invocation node)) in Hnew; inversion Hnew; subst new.
      simpl in Hactive; rewrite Hnull, Hpending in Hactive.
      destruct Hactive; [contradiction|discriminate].
    + destruct (task_commit_lookup_old_fields tasks p invocation node tid new Hneq Hnew)
        as [old [Hold Hfields]].
      pose proof (f_equal tcbFlagNode Hfields) as HflagNode; simpl in HflagNode.
      pose proof (f_equal stat Hfields) as Hstat; simpl in Hstat.
      rewrite HflagNode, Hstat in Hactive.
      destruct (Htasks tid old Hold Hactive) as [w [Hw Htid]].
      exists w; rewrite HflagNode; auto.
Qed.

Lemma task_flag_waiter_event_pointers_null : forall sg tasks flags p w t,
  task_flag_waiter_consistency sg tasks flags -> flags.(flagWaitNodes) p = Some w ->
  tasks.(inUsedTaskStates) w.(flagTask) = Some t ->
  t.(eventPtr) = None /\ t.(eventMultiWaitEvents) = [].
Proof.
  intros sg tasks flags p w t [Hnodes _] Hw Ht.
  destruct (Hnodes p w Hw) as [_ [before [Hbefore [_ [_ [_ [_ Hrefs]]]]]]].
  rewrite Ht in Hbefore; injection Hbefore as Heq; subst before; exact Hrefs.
Qed.

Lemma task_flag_waiter_not_in_event_wait_list : forall sg tasks flags events p w eid e,
  task_flag_waiter_consistency sg tasks flags -> event_in_range sg tasks events ->
  flags.(flagWaitNodes) p = Some w -> events.(inUsedEventStates) eid = Some e ->
  ~ In w.(flagTask) e.(waitList).
Proof.
  intros sg tasks flags events p w eid e Hcross Hvalid Hw He Hin.
  destruct Hvalid as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  destruct (Hentries eid e He) as [_ Hphase].
  destruct (event_type_to_pend_type e.(eventType)) as [pty|].
  - destruct (Hphase w.(flagTask) Hin) as [t [Ht [Hptr _]]].
    destruct (task_flag_waiter_event_pointers_null sg tasks flags p w t Hcross Hw Ht); congruence.
  - rewrite Hphase in Hin; contradiction.
Qed.

(** Graph unlink and clearing the registered TCB pointer are one combined
    boundary. The caller must already have cleared FLAG pending status
    (wake/timeout cleanup), or subsequently remove the Task before closing
    the global invariant (TaskDelete). Unlink alone does not wake a Task. *)
Lemma task_flag_unlink_preserves_consistency : forall sg tasks flags p w after new,
  task_flag_waiter_consistency sg tasks flags ->
  flag_unlink_node flags p = Some (w, after) ->
  new.(tcbFlagNode) = 0 -> (task_non_suspension_bits new.(stat)) <> task_pend_mask PendFlag ->
  task_flag_waiter_consistency sg (glob_task_set_usedtask tasks w.(flagTask) new) after.
Proof.
  intros sg tasks flags p w after new Hcross Hstep Hnull Hnopend.
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hstep)) as Hw.
  pose proof Hcross as [Hnodes Htasks]; split.
  - intros q next Hnext.
    destruct (flag_unlink_surviving_node_origin _ _ _ _ _ _ Hstep Hnext)
      as [Hqp [before [Hbefore Hidentity]]].
    assert (Htask : next.(flagTask) = before.(flagTask))
      by (unfold flag_waiter_link_identity in Hidentity; congruence).
    assert (Hgeneration : next.(flagTaskGeneration) = before.(flagTaskGeneration))
      by (unfold flag_waiter_link_identity in Hidentity; congruence).
    assert (Htcb : next.(flagWaitImage).(flagNodeTCB) = before.(flagWaitImage).(flagNodeTCB))
      by (unfold flag_waiter_link_identity in Hidentity; congruence).
    assert (Hother : next.(flagTask) <> w.(flagTask)).
    { rewrite Htask; intro Hsame; apply Hqp.
      eapply task_flag_waiter_unique_per_task; eauto. }
    destruct (Hnodes q before Hbefore) as [Hq0 [t [Ht [Hg [Hptr [Haddr Hphase]]]]]].
    split; [exact Hq0|]. exists t; split.
    + simpl; rewrite Htask.
      destruct (Z.eqb (flagTask before) (flagTask w)) eqn:Hsame.
      * apply Z.eqb_eq in Hsame; exfalso; apply Hother; congruence.
      * exact Ht.
    + split; [congruence|]. split; [exact Hptr|]. split; [congruence|exact Hphase].
  - intros tid t Ht Hactive; simpl in Ht.
    destruct (Z.eqb tid w.(flagTask)) eqn:Htid.
    + injection Ht as Heq; subst t; destruct Hactive; contradiction.
    + destruct (Htasks tid t Ht Hactive) as [before [Hbefore Htask]].
      assert (Hqp : t.(tcbFlagNode) <> p).
      { intro Heq; rewrite Heq, Hw in Hbefore; injection Hbefore as Hbefore; subst before.
        apply Z.eqb_neq in Htid; congruence. }
      pose proof (flag_unlink_frames_waiter_identity _ _ _ _ _ Hstep Hqp) as Hidentity.
      rewrite Hbefore in Hidentity.
      destruct (after.(flagWaitNodes) t.(tcbFlagNode)) as [next|] eqn:Hnext;
        [|discriminate].
      exists next; split; [reflexivity|].
      simpl in Hidentity; injection Hidentity as Hidentity;
        unfold flag_waiter_link_identity in Hidentity; congruence.
Qed.

Lemma task_flag_wake_unlink_preserves_consistency : forall sg tasks flags p w after old bits result,
  task_flag_waiter_consistency sg tasks flags ->
  flag_unlink_node flags p = Some (w, after) -> tasks.(inUsedTaskStates) w.(flagTask) = Some old ->
  task_flag_waiter_consistency sg
    (glob_task_set_usedtask tasks w.(flagTask) (task_flag_wake old bits result)) after.
Proof.
  intros sg tasks flags p w after old bits result Hcross Hstep Hold.
  destruct (task_flag_wake_clears_registration old bits result) as [Hnull Hnopend].
  eapply task_flag_unlink_preserves_consistency; eauto.
Qed.

Lemma task_flag_timeout_unlink_preserves_consistency : forall sg tasks flags p w after old,
  task_flag_waiter_consistency sg tasks flags ->
  flag_unlink_node flags p = Some (w, after) -> tasks.(inUsedTaskStates) w.(flagTask) = Some old ->
  (task_non_suspension_bits old.(stat)) = 0 ->
  task_flag_waiter_consistency sg
    (glob_task_set_usedtask tasks w.(flagTask) (task_set_flag_node old 0)) after.
Proof.
  intros sg tasks flags p w after old Hcross Hstep Hold Hnopend.
  eapply task_flag_unlink_preserves_consistency; [exact Hcross|exact Hstep|reflexivity|].
  simpl; rewrite Hnopend; discriminate.
Qed.

(** OSStart follows the completed OSInit call. Completed initialization
    records attempted Sem/Task creation, not successful return values.
    Disabled Timer has no initialization requirement or physical cells. *)
Definition timer_running_initialization_consistency (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Prop :=
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> s.(SchedState).(isRunning) = true ->
  s.(TimerState).(timerInitPhase) = TimerInitializationFinished.

(** The native cross layer contains only relationships that are not
    already task/scheduler-local validity. In particular it does not repeat
    ready-list ordering, current-priority registration, or the historical
    per-mutex equality between a snapshot and the owner's current priority. *)
(** The waiting protocol is the only configurable clause here. Concrete
    clients fix it to the single-wait or registered-Multi relation. This
    constructor neither proves that relation nor omits other modules. *)
Definition cross_module_consistency_with_wait (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (waiting : Prop) : Prop :=
  task_mutex_priotbl_consistency sg s.(TskState) s.(EventState) /\
  mutex_owner_snapshot_in_range sg s.(TskState) s.(EventState) /\
  waiting /\
  mutex_protocol_consistency sg s /\
  mutex_enabled_pcp_unique sg s /\
  task_flag_waiter_consistency sg s.(TskState) s.(FlagState) /\
  timer_running_initialization_consistency sg s.

Definition cross_module_consistency (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Prop :=
  task_mutex_priotbl_consistency sg s.(TskState) s.(EventState) /\
  mutex_owner_snapshot_in_range sg s.(TskState) s.(EventState) /\
  event_wait_object_consistency sg s /\
  mutex_protocol_consistency sg s /\
  mutex_enabled_pcp_unique sg s /\
  task_flag_waiter_consistency sg s.(TskState) s.(FlagState) /\
  timer_running_initialization_consistency sg s.

Lemma cross_module_consistency_flag_nodes_frame : forall sg s flags,
  flags.(flagWaitNodes) = s.(FlagState).(flagWaitNodes) ->
  cross_module_consistency sg s ->
  cross_module_consistency sg (replace_FlagS flags s).
Proof.
  intros sg s flags Hnodes [Htable [Howners [Hwait [Hprotocol [Hunique [Hflags Htimer]]]]]].
  split; [exact Htable|]. split; [exact Howners|]. split; [exact Hwait|].
  split; [exact Hprotocol|]. split; [exact Hunique|]. split; [|exact Htimer].
  eapply task_flag_waiter_consistency_nodes_frame; eauto.
Qed.

(** Reserving or releasing a creator slot changes no live TCB and no live
    task alias.  The slot must be unclaimed by Mutex; that fact is derived
    from the old free/creator entry, not added as a new C branch. *)
Lemma task_mutex_priotbl_consistency_reservation_update : forall sg before after events p reservation,
  after.(inUsedTaskStates) = before.(inUsedTaskStates) ->
  after.(prioTbl) = update_prio_tbl before.(prioTbl) p
    (match reservation with Some _ => PTReserved | None => PTFree end) ->
  (forall q, after.(taskLifecycle).(taskReservations) q =
    if Z.eq_dec q p then reservation else before.(taskLifecycle).(taskReservations) q) ->
  (forall tid, before.(prioTbl) p <> PTTask tid) ->
  ~ (exists mid e m, events.(inUsedEventStates) mid = Some e /\
     e.(eventType) = OS_EVENT_TYPE_MUTEX /\ e.(mutexFields) = Some m /\
     mutex_reserves_priority_slot sg m p) ->
  task_mutex_priotbl_consistency sg before events ->
  task_mutex_priotbl_consistency sg after events.
Proof.
  intros sg before after events p reservation Hused Htable Hreservation Hnotask Hnomutex
    [Hcreator [Hslots Halias]].
  assert (Haliases : forall tid q,
    task_priority_alias sg before.(prioTbl) tid q <-> task_priority_alias sg after.(prioTbl) tid q).
  { intros; rewrite Htable; symmetry; apply task_priority_alias_foreign_write_iff;
      [apply Hnotask|destruct reservation; discriminate]. }
  split.
  - intros q entry Hentry; rewrite Hreservation in Hentry.
    destruct (Z.eq_dec q p) as [->|Hne].
    + exact Hnomutex.
    + exact (Hcreator q entry Hentry).
  - split.
    + intros q Hq; rewrite Htable; unfold update_prio_tbl.
      destruct (Z.eq_dec q p) as [->|Hne].
      * destruct reservation as [entry|]; [left; exists entry; rewrite Hreservation;
          destruct (Z.eq_dec p p); [reflexivity|contradiction]|exact Hnomutex].
      * specialize (Hslots q Hq); destruct (before.(prioTbl) q).
        -- exact Hslots.
        -- destruct Hslots as [[entry Hentry]|Hmutex]; [left; exists entry|right; exact Hmutex].
           rewrite Hreservation; destruct (Z.eq_dec q p); [contradiction|exact Hentry].
        -- rewrite Hused; exact Hslots.
    + intros tid t Ht; rewrite Hused in Ht.
      destruct (Halias tid t Ht) as [base [Hbase [Heffective Hclaims]]].
      exists base; split.
      * eapply task_base_priority_alias_ext; [apply Haliases|exact Hbase].
      * split; [eapply task_effective_priority_alias_ext; [apply Haliases|exact Heffective]|].
        intros q Hq; apply Hclaims; apply Haliases; exact Hq.
Qed.

Lemma cross_module_consistency_task_table_transport : forall sg s tasks,
  tasks.(inUsedTaskStates) = s.(TskState).(inUsedTaskStates) ->
  task_mutex_priotbl_consistency sg tasks s.(EventState) ->
  (forall tid q, task_priority_alias sg s.(TskState).(prioTbl) tid q <->
    task_priority_alias sg tasks.(prioTbl) tid q) ->
  (forall mid e m, s.(EventState).(inUsedEventStates) mid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m ->
    mutex_pcp_enabled sg m -> tasks.(prioTbl) m.(mfPCP) = s.(TskState).(prioTbl) m.(mfPCP)) ->
  cross_module_consistency sg s ->
  cross_module_consistency sg (replace_TskS tasks s).
Proof.
  intros sg s tasks Hused Htable Haliases Hpcp
    [_ [Howners [Hwait [Hprotocol [Hunique [Hflags Htimer]]]]]].
  split; [exact Htable|]; split.
  - intros mid e m owner He Htype Hm Howner.
    destruct (Howners mid e m owner He Htype Hm Howner)
      as [t [base [snapshot [Ht [Hbase Hrest]]]]].
    exists t, base, snapshot; split; [simpl; rewrite Hused; exact Ht|].
    split; [eapply task_base_priority_alias_ext; [apply Haliases|exact Hbase]|exact Hrest].
  - split.
    + destruct Hwait as [Hentries [Hback Hclosed]]; split.
      * intros eid e He; eapply event_wait_entry_task_lookup_ext;
          [intros; simpl; rewrite Hused; reflexivity|exact (Hentries eid e He)].
      * split.
        -- unfold task_event_reference_backlink_consistency in *; simpl; rewrite Hused; exact Hback.
        -- unfold task_event_reference_closure in *; simpl; rewrite Hused; exact Hclosed.
    + split.
      * intros mid e m He Htype Hm; destruct (Hprotocol mid e m He Htype Hm)
          as [Hrange [Howner [Hdisabled|[Henabled Hslot]]]].
        -- split; [exact Hrange|]; split; [exact Howner|left; exact Hdisabled].
        -- split; [exact Hrange|]; split; [exact Howner|right; split; [exact Henabled|]].
           simpl; rewrite (Hpcp mid e m He Htype Hm Henabled); exact Hslot.
      * split; [exact Hunique|]; split; [|exact Htimer].
        unfold task_flag_waiter_consistency in *; simpl; rewrite Hused; exact Hflags.
Qed.

Lemma task_reserve_preserves_cross_module_consistency : forall sg s p invocation origin,
  task_reserve_guard sg s.(TskState) p invocation origin ->
  cross_module_consistency sg s ->
  cross_module_consistency sg (replace_TskS (task_reserve s.(TskState) p invocation origin) s).
Proof.
  intros sg s p invocation origin [Hp [Hfree Hguard]] Hcross.
  pose proof Hcross as [Htable _].
  pose proof (proj1 (proj2 Htable) p Hp) as Hnomutex; rewrite Hfree in Hnomutex.
  eapply cross_module_consistency_task_table_transport; [reflexivity| | | |exact Hcross].
  - eapply (task_mutex_priotbl_consistency_reservation_update sg s.(TskState)
      (task_reserve s.(TskState) p invocation origin) s.(EventState) p
      (Some {| creationInvocation := invocation; creationOrigin := origin;
        creationAllocation := None |})).
    + reflexivity.
    + reflexivity.
    + intros; reflexivity.
    + intros; rewrite Hfree; discriminate.
    + exact Hnomutex.
    + exact Htable.
  - intros tid q; change (task_priority_alias sg s.(TskState).(prioTbl) tid q <->
      task_priority_alias sg (update_prio_tbl s.(TskState).(prioTbl) p PTReserved) tid q).
    symmetry; apply task_priority_alias_foreign_write_iff; [rewrite Hfree|]; discriminate.
  - intros mid e m He Htype Hm Henabled; simpl.
    destruct (Z.eq_dec m.(mfPCP) p) as [Heq|Hne]; [|reflexivity].
    exfalso; apply Hnomutex; exists mid, e, m; repeat split; assumption.
Qed.

Lemma task_rollback_preserves_cross_module_consistency : forall sg s p invocation,
  task_in_range sg s.(TskState) -> task_rollback_guard s.(TskState) p invocation ->
  cross_module_consistency sg s ->
  cross_module_consistency sg (replace_TskS (task_rollback_reservation s.(TskState) p) s).
Proof.
  intros sg s p invocation Htasks [entry [Hentry [Hinv Hempty]]] Hcross.
  pose proof Hcross as [Htable _].
  pose proof (proj1 Htable p entry Hentry) as Hnomutex.
  pose proof (proj1 (proj1 (proj2 (proj2 (proj2 Htasks)))) p entry Hentry)
    as [_ [Hreserved _]].
  eapply cross_module_consistency_task_table_transport; [reflexivity| | | |exact Hcross].
  - eapply (task_mutex_priotbl_consistency_reservation_update sg s.(TskState)
      (task_rollback_reservation s.(TskState) p) s.(EventState) p None).
    + reflexivity.
    + reflexivity.
    + intros; reflexivity.
    + intros; rewrite Hreserved; discriminate.
    + exact Hnomutex.
    + exact Htable.
  - intros tid q; change (task_priority_alias sg s.(TskState).(prioTbl) tid q <->
      task_priority_alias sg (update_prio_tbl s.(TskState).(prioTbl) p PTFree) tid q).
    symmetry; apply task_priority_alias_foreign_write_iff; [rewrite Hreserved|]; discriminate.
  - intros mid e m He Htype Hm Henabled; simpl.
    destruct (Z.eq_dec m.(mfPCP) p) as [Heq|Hne]; [|reflexivity].
    exfalso; apply Hnomutex; exists mid, e, m; repeat split; assumption.
Qed.

Lemma task_update_private_image_preserves_cross_module_consistency :
  forall sg s p entry allocation image,
    task_in_range sg s.(TskState) ->
    s.(TskState).(taskLifecycle).(taskReservations) p = Some entry ->
    entry.(creationAllocation) = Some allocation ->
    cross_module_consistency sg s ->
    cross_module_consistency sg (replace_TskS
      (task_update_private_image s.(TskState) p entry allocation image) s).
Proof.
  intros sg s p entry allocation image Htasks Hentry Ha [Htable Hrest].
  split; [|exact Hrest].
  eapply task_mutex_priotbl_consistency_lifecycle_ext with (before := s.(TskState));
    [reflexivity|reflexivity| |exact Htable].
  intro q.
  cbn [replace_TskS TskState task_update_private_image glob_task_set_lifecycle
    task_lifecycle_set_reservation taskLifecycle taskReservations].
  destruct (Z.eq_dec q p) as [->|Hneq]; [rewrite Hentry|reflexivity].
  split; intros; eexists; reflexivity.
Qed.

Lemma task_detach_preserves_cross_module_consistency :
  forall sg s p entry tid rest image,
    task_in_range sg s.(TskState) ->
    task_detach_guard s.(TskState) p entry tid rest image ->
    cross_module_consistency sg s ->
    cross_module_consistency sg
      (replace_TskS (task_detach_head s.(TskState) p entry tid rest image) s).
Proof.
  intros sg s p entry tid rest image Htasks [_ [Hentry _]] [Htable Hrest].
  split; [|exact Hrest].
  eapply task_mutex_priotbl_consistency_lifecycle_ext with (before := s.(TskState));
    [reflexivity|reflexivity| |exact Htable].
  intro q; cbn [replace_TskS TskState task_detach_head taskLifecycle taskReservations].
  destruct (Z.eq_dec q p) as [->|Hneq]; [rewrite Hentry|reflexivity].
  split; intros; eexists; reflexivity.
Qed.

Lemma task_commit_preserves_mutex_priority_aliases :
  forall sg tasks events p invocation node,
    task_in_range sg tasks ->
    task_commit_identity tasks p invocation node ->
    (forall q tid, task_priority_in_range sg q -> tasks.(prioTbl) q = PTTask tid ->
       exists t, tasks.(inUsedTaskStates) tid = Some t) ->
    mutex_priority_alias_consistency sg tasks events ->
    mutex_priority_alias_consistency sg (task_commit tasks p invocation node) events.
Proof.
  intros sg tasks events p invocation node Htasks Hidentity Hlive Halias.
  pose proof (task_commit_identity_private _ _ _ _ Hidentity) as Hprivate.
  pose proof (task_private_excludes_public sg tasks node.(taskID) (proj1 Htasks) Hprivate)
    as [Hnone Hnotfree].
  destruct Hidentity as [entry [allocation [Hentry [_ [_ [_ [_ Hp]]]]]]].
  destruct Htasks as [_ [_ [_ [Hres _]]]].
  destruct (proj1 Hres p entry Hentry) as [Hpvalid [Hreserved _]].
  assert (Habsent : forall q, task_priority_in_range sg q -> tasks.(prioTbl) q <> PTTask node.(taskID)).
  { intros q Hrange Hq; destruct (Hlive q node.(taskID) Hrange Hq) as [old Hold]; congruence. }
  intros tid t Hget.
  pose proof (task_commit_observation Z curPrio tasks p invocation node tid
    (fun _ _ _ => eq_refl)) as Hobs; rewrite Hget in Hobs; simpl in Hobs.
  destruct (Z.eq_dec tid node.(taskID)) as [->|Hforeign].
  - injection Hobs as Hprio; rewrite Hprio, Hp.
    assert (HaliasNew : forall q,
      task_priority_alias sg (task_commit tasks p invocation node).(prioTbl) node.(taskID) q <->
      q = p).
    { intro q; apply task_commit_new_priority_alias_iff; assumption. }
    exists p; split.
    + split; [apply HaliasNew; reflexivity|].
      intros q Hq; apply HaliasNew in Hq; lia.
    + split.
      * split; [apply HaliasNew; reflexivity|].
        intros q Hq; apply HaliasNew in Hq; lia.
      * intros q Hq; left; apply HaliasNew; exact Hq.
  - destruct (tasks.(inUsedTaskStates) tid) as [old|] eqn:Hold; [|discriminate].
    simpl in Hobs; injection Hobs as Hprio.
    destruct (Halias tid old Hold) as [base [Hbase [Heffective Hclaims]]].
    assert (HaliasOld : forall q,
      task_priority_alias sg tasks.(prioTbl) tid q <->
      task_priority_alias sg (task_commit tasks p invocation node).(prioTbl) tid q).
    { intro q; symmetry; apply task_commit_old_priority_alias_iff; assumption. }
    exists base; split.
    + eapply task_base_priority_alias_ext; eauto.
    + split.
      * rewrite Hprio; eapply task_effective_priority_alias_ext; eauto.
      * intros q Hq; apply Hclaims; apply HaliasOld; exact Hq.
Qed.

Lemma task_commit_preserves_priotbl_consistency : forall sg s p invocation node,
  task_in_range sg s.(TskState) ->
  task_commit_identity s.(TskState) p invocation node ->
  task_mutex_priotbl_consistency sg s.(TskState) s.(EventState) ->
  task_mutex_priotbl_consistency sg
    (task_commit s.(TskState) p invocation node) s.(EventState).
Proof.
  intros sg s p invocation node Htasks Hidentity [Hcreator [Hslots Halias]].
  pose proof (task_commit_identity_private _ _ _ _ Hidentity) as Hprivate.
  pose proof (task_private_excludes_public sg s.(TskState) node.(taskID) (proj1 Htasks) Hprivate)
    as [Hnone Hnotfree].
  split.
  - intros q entry Hentry; simpl in Hentry.
    destruct (Z.eq_dec q p); [discriminate|]; exact (Hcreator q entry Hentry).
  - split.
    + intros q Hrange; cbn [task_commit prioTbl].
      destruct (Z.eq_dec q p) as [->|Hneq].
      * eexists; exact (proj1 (task_commit_publication_fields_eq s.(TskState) p invocation node)).
      * specialize (Hslots q Hrange); destruct (s.(TskState).(prioTbl) q).
        -- exact Hslots.
        -- destruct Hslots as [[entry Hentry]|Hclaim].
           ++ left; exists entry; simpl; destruct (Z.eq_dec q p); congruence.
           ++ right; exact Hclaim.
        -- destruct Hslots as [old Hold].
           destruct (task_commit_transports_old_priority s.(TskState) p invocation node _ old
             Hnone Hold) as [new [Hnew _]]; exists new; exact Hnew.
    + eapply task_commit_preserves_mutex_priority_aliases; [exact Htasks|exact Hidentity| |exact Halias].
      intros q tid Hrange Hq; specialize (Hslots q Hrange); rewrite Hq in Hslots; exact Hslots.
Qed.

Lemma task_commit_preserves_owner_snapshots : forall sg tasks events p invocation node,
  task_in_range sg tasks -> task_commit_identity tasks p invocation node ->
  mutex_owner_snapshot_in_range sg tasks events ->
  mutex_owner_snapshot_in_range sg (task_commit tasks p invocation node) events.
Proof.
  intros sg tasks events p invocation node Htasks Hidentity Howners.
  pose proof (task_commit_identity_private _ _ _ _ Hidentity) as Hprivate.
  pose proof (task_private_excludes_public sg tasks node.(taskID) (proj1 Htasks) Hprivate)
    as [Hnone Hnotfree].
  destruct Hidentity as [entry [allocation [Hentry Hrest]]].
  destruct Htasks as [_ [_ [_ [Hres _]]]].
  pose proof (proj1 Hres p entry Hentry) as [_ [Hreserved _]].
  intros mid e m owner He Htype Hfields Howner.
  destruct (Howners mid e m owner He Htype Hfields Howner)
    as [old [base [snapshot [Hold [Hbase [Hsnapshot [Hrange [Hle Hnotwait]]]]]]]].
  destruct (task_commit_transports_old_priority tasks p invocation node owner old Hnone Hold)
    as [new [Hnew Hprio]].
  exists new, base, snapshot; split; [exact Hnew|]. split.
  - eapply task_base_priority_alias_ext; [|exact Hbase].
    intro q; symmetry; apply task_commit_old_priority_alias_iff; [exact Hreserved|congruence].
  - exact (conj Hsnapshot (conj Hrange (conj Hle Hnotwait))).
Qed.

Lemma task_commit_preserves_cross_module_consistency :
  forall sg s p invocation node sched',
    task_in_range sg s.(TskState) ->
    task_commit_identity s.(TskState) p invocation node ->
    node.(eventPtr) = None -> node.(eventMultiWaitEvents) = [] ->
    node.(tcbFlagNode) = 0 -> (task_non_suspension_bits node.(stat)) = 0 ->
    sched'.(isRunning) = s.(SchedState).(isRunning) ->
    cross_module_consistency sg s ->
    cross_module_consistency sg
      (replace_SchedS sched' (replace_TskS (task_commit s.(TskState) p invocation node) s)).
Proof.
  intros sg s p invocation node sched' Htasks Hidentity Hnodeptr Hnodemulti Hflagptr Hpending Hrunning
    [Htable [Howners [Hwait [Hprotocol [HpcpUnique [Hflags Htimer]]]]]].
  pose proof (task_commit_identity_private _ _ _ _ Hidentity) as Hprivate.
  pose proof (task_private_excludes_public sg s.(TskState) node.(taskID) (proj1 Htasks) Hprivate)
    as [Hnone Hnotfree].
  destruct Hidentity as [entry [allocation [Hentry [Hinv [Ha [Hid [Hg Hp]]]]]]].
  assert (Hidentity : task_commit_identity s.(TskState) p invocation node).
  { exists entry, allocation; repeat split; assumption. }
  assert (Hpcpnotp : forall mid e m,
    s.(EventState).(inUsedEventStates) mid = Some e -> e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m -> m.(mfPCP) <> sg.(osPrioMutexCeilDis) -> m.(mfPCP) <> p).
  { intros mid e m He Hty Hm Henabled Heq.
    apply (proj1 Htable p entry Hentry).
    exists mid, e, m; repeat split; try assumption. }
  split.
  { exact (task_commit_preserves_priotbl_consistency sg s p invocation node Htasks Hidentity Htable). }
  split.
  { exact (task_commit_preserves_owner_snapshots sg s.(TskState) s.(EventState)
      p invocation node Htasks Hidentity Howners). }
  split.
  { exact (task_commit_preserves_event_wait_object_consistency
      sg s p invocation node sched' Hnone Hnodeptr Hnodemulti Hwait). }
  split.
  2: { split; [exact HpcpUnique|]. split.
       - exact (task_commit_preserves_flag_waiter_consistency sg s.(TskState)
           s.(FlagState) p invocation node Hnone Hflagptr Hpending Hflags).
       - intros Henabled Hr; apply Htimer; [exact Henabled|].
         cbn in Hr; rewrite <- Hrunning; exact Hr. }
  intros mid e m He Hty Hm; specialize (Hprotocol mid e m He Hty Hm).
  destruct Hprotocol as [Hvalid [Howner HtableOld]].
  split; [exact Hvalid|]. split; [exact Howner|].
  destruct HtableOld as [Hdisabled|[Henabled HtableOld]]; [left; exact Hdisabled|].
  right; split; [exact Henabled|].
  pose proof (Hpcpnotp mid e m He Hty Hm Henabled) as Hneq.
  simpl; destruct (Z.eq_dec (mfPCP m) p); [contradiction|exact HtableOld].
Qed.

(* ================================================================== *)
(* 2026-07-02:atomic_event_wait_list_init 完整证明的辅助引理              *)
(* 这 3 个引理论证"与 EventState 无关的子不变式在 EventState 改变时保持"  *)
(* ================================================================== *)

Lemma osprio_cur_consistency_indep_EventState :
  forall sg lvs1 lvs2,
    SchedState lvs2 = SchedState lvs1 ->
    TskState lvs2 = TskState lvs1 ->
    osprio_cur_consistency sg lvs1 ->
    osprio_cur_consistency sg lvs2.
Proof.
  intros sg lvs1 lvs2 HS HT H. unfold osprio_cur_consistency in *. rewrite HS, HT. assumption.
Qed.

Lemma ready_list_completeness_indep_EventState :
  forall sg lvs1 lvs2,
    TskState lvs2 = TskState lvs1 ->
    SchedState lvs2 = SchedState lvs1 ->
    ready_list_completeness sg lvs1 ->
    ready_list_completeness sg lvs2.
Proof.
  intros sg lvs1 lvs2 HT HS H. unfold ready_list_completeness in *. rewrite HS, HT. assumption.
Qed.

Lemma ready_list_order_indep_EventState :
  forall sg lvs1 lvs2,
    TskState lvs2 = TskState lvs1 ->
    SchedState lvs2 = SchedState lvs1 ->
    ready_list_order sg lvs1 ->
    ready_list_order sg lvs2.
Proof.
  intros sg lvs1 lvs2 HT HS H. unfold ready_list_order in *. rewrite HS, HT. assumption.
Qed.

(* ================================================================== *)
(* 2026-07-02:仅改某 event 的 waitList 时,3 条 EventState 相关不变式保持  *)
(* 用 waitlist_only_update / waitlist_only_lookup_eq 转换 record projection *)
(* ================================================================== *)

Definition waitlist_only_update (es : Glob_EventAbstractState)
  (mid : EventID) (e_old : OSEventAbstractState) (wl : list TaskID)
  : Glob_EventAbstractState :=
  update_event_field_raw es mid
    {| eventGeneration := e_old.(eventGeneration);
       eventName := e_old.(eventName);
     eventPadding1 := e_old.(eventPadding1);
     eventPadding2 := e_old.(eventPadding2);
     eventPadding3 := e_old.(eventPadding3);
     eventPadding19 := e_old.(eventPadding19);
       eventType   := e_old.(eventType);
       mutexFields := e_old.(mutexFields);
       semFields   := e_old.(semFields);
       mboxFields  := e_old.(mboxFields);
       queueFields := e_old.(queueFields);
       waitList    := wl; |}.

Lemma waitlist_only_lookup_eq :
  forall (es : Glob_EventAbstractState) mid e_old wl eid,
    es.(inUsedEventStates) mid = Some e_old ->
    (waitlist_only_update es mid e_old wl).(inUsedEventStates) eid =
      (if Z.eqb eid mid
       then Some {| eventGeneration := e_old.(eventGeneration);
                    eventName := e_old.(eventName);
     eventPadding1 := e_old.(eventPadding1);
     eventPadding2 := e_old.(eventPadding2);
     eventPadding3 := e_old.(eventPadding3);
     eventPadding19 := e_old.(eventPadding19);
                    eventType   := e_old.(eventType);
                    mutexFields := e_old.(mutexFields);
                    semFields   := e_old.(semFields);
                    mboxFields  := e_old.(mboxFields);
                    queueFields := e_old.(queueFields);
                    waitList    := wl; |}
       else es.(inUsedEventStates) eid).
Proof.
  intros es mid e_old wl eid Hget.
  unfold waitlist_only_update, update_event_field_raw. simpl. reflexivity.
Qed.

Lemma mutex_enabled_pcp_unique_preserved_by_waitList_only :
  forall sg lvs mid e_old wl,
    (EventState lvs).(inUsedEventStates) mid = Some e_old ->
    mutex_enabled_pcp_unique sg lvs ->
    mutex_enabled_pcp_unique sg
      (replace_EventS
        (waitlist_only_update (EventState lvs) mid e_old wl) lvs).
Proof.
  intros sg lvs mid e_old wl Hget Hunique.
  eapply mutex_enabled_pcp_unique_transport with (lvs1 := lvs).
  - intros midv ev mv Hgetv Htypev Hmfv.
    rewrite replace_EventS_EventState in Hgetv.
    rewrite (waitlist_only_lookup_eq
      (EventState lvs) mid e_old wl midv Hget) in Hgetv.
    destruct (Z.eqb midv mid) eqn:Hmid.
    + apply Z.eqb_eq in Hmid. subst midv.
      inversion Hgetv; subst ev.
      cbn in Htypev, Hmfv.
      exists e_old, mv. repeat split; try assumption; reflexivity.
    + cbn in Hgetv.
      exists ev, mv. repeat split; try assumption; reflexivity.
  - exact Hunique.
Qed.

Lemma EventState_replace_lookup :
  forall lvs es mid,
    (EventState (replace_EventS es lvs)).(inUsedEventStates) mid =
    es.(inUsedEventStates) mid.
Proof. intros. reflexivity. Qed.

Lemma verification_slice_event_wait_entry_consistency_irrelevant_fields :
  forall sg tskSt eid e1 e2,
    e2.(eventType) = e1.(eventType) ->
    e2.(waitList) = e1.(waitList) ->
    verification_slice_event_wait_entry_consistency sg tskSt eid e1 ->
    verification_slice_event_wait_entry_consistency sg tskSt eid e2.
Proof.
  intros sg tskSt eid
         [ty1 mf1 sf1 mb1 q1 wl1]
         [ty2 mf2 sf2 mb2 q2 wl2]
         Hty Hwl Hentry.
  simpl in *. subst ty2 wl2. exact Hentry.
Qed.

Lemma verification_slice_event_wait_entry_consistency_empty_waitlist :
  forall sg tskSt eid e_old,
    verification_slice_event_wait_entry_consistency sg tskSt eid
      {| eventGeneration := e_old.(eventGeneration);
         eventName := e_old.(eventName);
     eventPadding1 := e_old.(eventPadding1);
     eventPadding2 := e_old.(eventPadding2);
     eventPadding3 := e_old.(eventPadding3);
     eventPadding19 := e_old.(eventPadding19);
         eventType   := e_old.(eventType);
         mutexFields := e_old.(mutexFields);
         semFields   := e_old.(semFields);
         mboxFields  := e_old.(mboxFields);
         queueFields := e_old.(queueFields);
         waitList    := []; |}.
Proof.
  intros sg tskSt eid [ty mf sf mb q wl].
  unfold verification_slice_event_wait_entry_consistency, event_waitList_canonical.
  simpl.
  split.
  - split; [constructor| split; [constructor| intros tid Hin; inversion Hin]].
  - destruct (event_type_to_pend_type ty) as [pty |] eqn:Hpty.
    + intros tid Hin. inversion Hin.
    + reflexivity.
Qed.

(* ================================================================== *)
(* 通用 iff 引理:mutex 存在性声明在仅改 waitList 时保持                  *)
(* ================================================================== *)

Definition new_rec (e_old : OSEventAbstractState) (wl : list TaskID)
  : OSEventAbstractState :=
  {| eventGeneration := e_old.(eventGeneration);
     eventName := e_old.(eventName);
     eventPadding1 := e_old.(eventPadding1);
     eventPadding2 := e_old.(eventPadding2);
     eventPadding3 := e_old.(eventPadding3);
     eventPadding19 := e_old.(eventPadding19);
     eventType   := e_old.(eventType);
     mutexFields := e_old.(mutexFields);
     semFields   := e_old.(semFields);
     mboxFields  := e_old.(mboxFields);
     queueFields := e_old.(queueFields);
     waitList    := wl; |}.

Lemma exists_mutex_pred_iff :
  forall (es : Glob_EventAbstractState) mid e_old wl
         (P : OSEventType -> MutexFields -> Prop),
    es.(inUsedEventStates) mid = Some e_old ->
    (exists mid0 e0 m0,
       (waitlist_only_update es mid e_old wl).(inUsedEventStates) mid0 = Some e0 /\
       e0.(mutexFields) = Some m0 /\
       P e0.(eventType) m0) <->
    (exists mid0 e0 m0,
       es.(inUsedEventStates) mid0 = Some e0 /\
       e0.(mutexFields) = Some m0 /\
       P e0.(eventType) m0).
Proof.
  intros es mid e_old wl P Hget. split.
  - intros [mid0 [e0 [m0 [Hget0 [Hmf0 Hp0]]]]].
    rewrite (waitlist_only_lookup_eq es mid e_old wl mid0 Hget) in Hget0.
    destruct (Z.eqb mid0 mid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst mid0.
      inversion Hget0; subst.
      simpl in *. exists mid. exists e_old. exists m0. repeat split; assumption.
    + cbv iota in Hget0. exists mid0. exists e0. exists m0.
      repeat split; assumption.
  - intros [mid0 [e0 [m0 [Hget0 [Hmf0 Hp0]]]]].
    destruct (Z.eqb mid0 mid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst mid0.
      rewrite Hget in Hget0. injection Hget0 as Heq_e0.
      exists mid. exists (new_rec e_old wl). exists m0. repeat split.
      * unfold new_rec. rewrite (waitlist_only_lookup_eq es mid e_old wl mid Hget).
        rewrite Z.eqb_refl. reflexivity.
      * unfold new_rec. simpl. rewrite Heq_e0. exact Hmf0.
      * unfold new_rec. simpl. rewrite Heq_e0. exact Hp0.
    + exists mid0. exists e0. exists m0. repeat split; try assumption.
      rewrite (waitlist_only_lookup_eq es mid e_old wl mid0 Hget). rewrite Heq.
      cbv iota. exact Hget0.
Qed.

Lemma mutex_owner_consistency_preserved_by_waitList_only :
  forall sg lvs mid e_old wl,
    (EventState lvs).(inUsedEventStates) mid = Some e_old ->
    (forall mv tid,
       e_old.(eventType) = OS_EVENT_TYPE_MUTEX ->
       e_old.(mutexFields) = Some mv ->
       mv.(mfOwner) = Some tid ->
       ~ In tid wl) ->
    mutex_owner_consistency sg lvs ->
    mutex_owner_consistency sg
      (replace_EventS (waitlist_only_update (EventState lvs) mid e_old wl) lvs).
Proof.
  intros sg lvs mid e_old wl Hget Howner_notin Hmo.
  unfold mutex_owner_consistency in *.
  intros midv ev mv [Hgetv [Htypev Hmfv]].
  unfold replace_EventS in Hgetv.
  unfold EventState at 1 in Hgetv.
  rewrite (waitlist_only_lookup_eq (EventState lvs) mid e_old wl midv Hget) in Hgetv.
  destruct (Z.eqb midv mid) eqn:Heq.
  - apply Z.eqb_eq in Heq. subst midv.
    inversion Hgetv; subst.
    simpl in Hmfv, Htypev.
    destruct (mv.(mfOwner)) as [tid |] eqn:Howner; [|exact I].
    pose proof (Hmo mid e_old mv
      (conj Hget (conj Htypev Hmfv))) as Hmo_mid.
    rewrite Howner in Hmo_mid. cbv beta iota in Hmo_mid.
    destruct Hmo_mid as [t [op [Ht [Horig [Hprio _]]]]].
    exists t, op. split; [exact Ht|].
    split; [exact Horig|].
    split; [exact Hprio|].
    eapply Howner_notin; eauto.
  - apply Z.eqb_neq in Heq.
    cbv iota in Hgetv.
    apply Hmo with (mid := midv) (e := ev) (m := mv).
    repeat split; [exact Hgetv | exact Htypev | exact Hmfv].
Qed.

Lemma mutex_waitlist_consistency_preserved_by_waitList_empty :
  forall sg lvs mid e_old,
    (EventState lvs).(inUsedEventStates) mid = Some e_old ->
    (forall tid t pty,
        (TskState lvs).(inUsedTaskStates) tid = Some t ->
        t.(eventPtr) = Some mid ->
        (task_non_suspension_bits (t.(stat))) = task_pend_mask pty ->
        event_type_to_pend_type e_old.(eventType) = Some pty ->
        False) ->
    task_event_id_unreferenced_prop lvs mid ->
    verification_slice_event_wait_object_consistency sg lvs ->
    verification_slice_event_wait_object_consistency sg
      (replace_EventS (waitlist_only_update (EventState lvs) mid e_old []) lvs).
Proof.
  intros sg lvs mid e_old Hget Hno_stale Hunreferenced Hmw.
  unfold verification_slice_event_wait_object_consistency in *.
  destruct Hmw as [Hmw_entry [Hmw_total Hmw_closed]].
  split; [| split].
  - intros midv ev Hgetv.
    unfold replace_EventS in Hgetv.
    unfold EventState at 1 in Hgetv.
    rewrite (waitlist_only_lookup_eq (EventState lvs) mid e_old [] midv Hget) in Hgetv.
    destruct (Z.eqb midv mid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst midv.
      inversion Hgetv; subst.
      apply verification_slice_event_wait_entry_consistency_empty_waitlist.
    + cbv iota in Hgetv.
      exact (Hmw_entry midv ev Hgetv).
  - intros tid t midv ev Ht Hgetv Href.
    rewrite replace_EventS_other_Tsk in Ht.
    unfold replace_EventS in Hgetv.
    unfold EventState at 1 in Hgetv.
    rewrite (waitlist_only_lookup_eq (EventState lvs) mid e_old [] midv Hget) in Hgetv.
    destruct (Z.eqb midv mid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst midv.
      specialize (Hunreferenced tid t Ht) as [Hsingle Hmulti].
      destruct Href as [Href | Href]; contradiction.
    + cbv iota in Hgetv.
      exact (Hmw_total tid t midv ev Ht Hgetv Href).
  - eapply task_event_reference_closure_preserved_by_event_extension.
    + intros eid [e He].
      change (exists e0, inUsedEventStates
        (waitlist_only_update (EventState lvs) mid e_old []) eid = Some e0).
      rewrite (waitlist_only_lookup_eq (EventState lvs) mid e_old [] eid Hget).
      destruct (Z.eqb eid mid); [eexists; reflexivity|]. exists e. exact He.
    + exact Hmw_closed.
Qed.

(* ================================================================== *)
(* priotbl_consistency:3 个分支(PTFree/PTReserved/PTTask)              *)
(* 关键:waitList-only 更新不改 eventType/mutexFields,所以 mfPCP/mfOwner  *)
(* 等字段都保持;TskState/SchedState 也不变,故 readyList/inUsedTaskStates *)
(* 相关子句直接复用。                                                       *)
(* ================================================================== *)

Lemma priotbl_consistency_preserved_by_waitList_only :
  forall sg lvs mid e_old wl,
    (EventState lvs).(inUsedEventStates) mid = Some e_old ->
    priotbl_consistency sg lvs ->
    priotbl_consistency sg
      (replace_EventS (waitlist_only_update (EventState lvs) mid e_old wl) lvs).
Proof.
  intros sg lvs mid e_old wl Hget Hpt.
  unfold priotbl_consistency in *.
  intros p.
  assert (Htsk_eq : TskState (replace_EventS (waitlist_only_update (EventState lvs) mid e_old wl) lvs) = TskState lvs) by reflexivity.
  assert (Hsch_eq : SchedState (replace_EventS (waitlist_only_update (EventState lvs) mid e_old wl) lvs) = SchedState lvs) by reflexivity.
  specialize (Hpt p).
  destruct ((TskState lvs).(prioTbl) p) as [| | tid] eqn:Hpt_p.
  - (* PTFree *)
    rewrite Htsk_eq. rewrite Hpt_p. cbv iota.
    destruct Hpt as [Hne_ready Hne_event].
    split.
    + intros Hcontra. apply Hne_ready. rewrite <- Hsch_eq, <- Htsk_eq. exact Hcontra.
    + intros Hcontra. apply Hne_event.
      destruct Hcontra as [mid0 [e0 [m0 [Hget_outer [Htype0 [Hmf0 Hpcp0]]]]]].
      rewrite EventState_replace_lookup in Hget_outer.
      rewrite (waitlist_only_lookup_eq (EventState lvs) mid e_old wl mid0 Hget) in Hget_outer.
      destruct (Z.eqb mid0 mid) eqn:Heq.
      * cbv iota in Hget_outer.
        apply Z.eqb_eq in Heq. subst mid0.
        injection Hget_outer as Heq_e0. subst e0.
        simpl in Htype0, Hmf0.
        exists mid. exists e_old. exists m0.
        split; [exact Hget | split; [exact Htype0 | split; [exact Hmf0 | exact Hpcp0]]].
      * cbv iota in Hget_outer.
        apply Z.eqb_neq in Heq.
        exists mid0. exists e0. exists m0.
        split; [exact Hget_outer | split; [exact Htype0 | split; [exact Hmf0 | exact Hpcp0]]].
  - (* PTReserved *)
    rewrite Htsk_eq. rewrite Hpt_p. cbv iota.
    destruct Hpt as [mid0 [e0 [m0 [Hget0 [Htype0 [Hmf0 [Hpcp0 Hmo_case]]]]]]].
    set (P := fun (ty : OSEventType) (m : MutexFields) =>
                ty = OS_EVENT_TYPE_MUTEX /\ m.(mfPCP) = p /\
                match m.(mfOwner) with
                | None => True
                | Some t =>
                    exists t0 op,
                      (TskState lvs).(inUsedTaskStates) t = Some t0 /\
                      m.(mfOwnerOrigPrio) = Some op /\ t0.(curPrio) = op
                end).
    assert (HPold : exists n0 e_ m_ ,
                      (EventState lvs).(inUsedEventStates) n0 = Some e_ /\
                      e_.(mutexFields) = Some m_ /\
                      P e_.(eventType) m_).
    { exists mid0. exists e0. exists m0. split; [exact Hget0 | split; [exact Hmf0 | ]].
      unfold P. split; [exact Htype0 | split; [exact Hpcp0 | exact Hmo_case]]. }
    apply (proj2 (exists_mutex_pred_iff (EventState lvs) mid e_old wl P Hget)) in HPold.
    destruct HPold as [mid0' [e0' [m0' [Hget0' [Hmf0' HP']]]]].
    unfold P in HP'. destruct HP' as [Htype0' [Hpcp0' Hmo_case']].
    exists mid0'. exists e0'. exists m0'.
    rewrite EventState_replace_lookup.
    split; [exact Hget0' | split; [exact Htype0' | split; [exact Hmf0' | split; [exact Hpcp0' | exact Hmo_case']]]].
  - (* PTTask tid *)
    rewrite Htsk_eq. rewrite Hpt_p. cbv iota.
    destruct Hpt as [t0 [Htst0 Hor]].
    exists t0. split; [exact Htst0 | ].
    destruct Hor as [Htcr0 | [mid0 [e0 [m0 [Hget0 [Htype0 [Hmf0 [Hpcp0 Hown0]]]]]]]].
    + (* 来源 1:curPrio = p *)
      left. exact Htcr0.
    + (* 来源 2:mutex 占用 *)
      right.
      set (P := fun (ty : OSEventType) (m : MutexFields) =>
                  ty = OS_EVENT_TYPE_MUTEX /\
                  m.(mfOwner) = Some tid /\
                  (m.(mfPCP) = p \/ m.(mfOwnerOrigPrio) = Some p)).
      assert (HPold : exists n0 e_ m_ ,
                        (EventState lvs).(inUsedEventStates) n0 = Some e_ /\
                        e_.(mutexFields) = Some m_ /\
                        P e_.(eventType) m_).
      { exists mid0. exists e0. exists m0. split; [exact Hget0 | split; [exact Hmf0 | ]].
        unfold P. split; [exact Htype0 | split; [exact Hpcp0 | exact Hown0]]. }
      apply (proj2 (exists_mutex_pred_iff (EventState lvs) mid e_old wl P Hget)) in HPold.
      destruct HPold as [mid0' [e0' [m0' [Hget0' [Hmf0' HP']]]]].
      unfold P in HP'. destruct HP' as [Htype0' [Howner0' Hsource0']].
      exists mid0'. exists e0'. exists m0'.
      rewrite EventState_replace_lookup.
      split; [exact Hget0' | split; [exact Htype0' | split; [exact Hmf0' | split; [exact Howner0' | exact Hsource0']]]].
Qed.

(* ================================================================== *)
(* 2026-07-02:atomic_mutex_release 完整 Qed 的辅助引理                    *)
(* 释放某 mutex:把 mfOwner / mfOwnerOrigPrio 设为 None(mfPCP 保留)        *)
(* ================================================================== *)

Definition owner_release_update (es : Glob_EventAbstractState)
  (mid : EventID) (e_old : OSEventAbstractState) (pcp : Priority)
  : Glob_EventAbstractState :=
  update_event_field_raw es mid
    {| eventGeneration := e_old.(eventGeneration);
       eventName := e_old.(eventName);
     eventPadding1 := e_old.(eventPadding1);
     eventPadding2 := e_old.(eventPadding2);
     eventPadding3 := e_old.(eventPadding3);
     eventPadding19 := e_old.(eventPadding19);
       eventType   := e_old.(eventType);
       mutexFields := Some {| mfPCP := pcp; mfOwner := None; mfOwnerOrigPrio := None; |};
       semFields   := e_old.(semFields);
       mboxFields  := e_old.(mboxFields);
       queueFields := e_old.(queueFields);
       waitList    := e_old.(waitList); |}.

Lemma owner_release_lookup_eq :
  forall (es : Glob_EventAbstractState) mid e_old pcp eid,
    es.(inUsedEventStates) mid = Some e_old ->
    (owner_release_update es mid e_old pcp).(inUsedEventStates) eid =
      (if Z.eqb eid mid
       then Some {| eventGeneration := e_old.(eventGeneration);
                    eventName := e_old.(eventName);
     eventPadding1 := e_old.(eventPadding1);
     eventPadding2 := e_old.(eventPadding2);
     eventPadding3 := e_old.(eventPadding3);
     eventPadding19 := e_old.(eventPadding19);
                    eventType   := e_old.(eventType);
                    mutexFields := Some {| mfPCP := pcp; mfOwner := None; mfOwnerOrigPrio := None; |};
                    semFields   := e_old.(semFields);
                    mboxFields  := e_old.(mboxFields);
                    queueFields := e_old.(queueFields);
                    waitList    := e_old.(waitList); |}
       else es.(inUsedEventStates) eid).
Proof.
  intros es mid e_old pcp eid Hget.
  unfold owner_release_update, update_event_field_raw. simpl. reflexivity.
Qed.

Lemma mutex_enabled_pcp_unique_preserved_by_release :
  forall sg lvs mid e_old m_old pcp,
    (EventState lvs).(inUsedEventStates) mid = Some e_old ->
    e_old.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e_old.(mutexFields) = Some m_old ->
    m_old.(mfPCP) = pcp ->
    mutex_enabled_pcp_unique sg lvs ->
    mutex_enabled_pcp_unique sg
      (replace_TskS
        {| inUsedTaskStates := (TskState lvs).(inUsedTaskStates);
           unUsedTaskStates := (TskState lvs).(unUsedTaskStates);
           tcbListHead := (TskState lvs).(tcbListHead);
           prioTbl := fun p =>
             if (negb (Z.eqb pcp sg.(osPrioMutexCeilDis)) &&
                 Z.eqb p pcp)%bool
             then PTReserved
             else (TskState lvs).(prioTbl) p;
           taskRegNextID := (TskState lvs).(taskRegNextID);
           parkedTaskStacks := (TskState lvs).(parkedTaskStacks);
           taskLifecycle := (TskState lvs).(taskLifecycle);
     taskCount := (TskState lvs).(taskCount); |}
        (replace_EventS
          (owner_release_update (EventState lvs) mid e_old pcp) lvs)).
Proof.
  intros sg lvs mid e_old m_old pcp Hget Htype Hmf Hpcp Hunique.
  eapply mutex_enabled_pcp_unique_transport with (lvs1 := lvs).
  - intros midv ev mv Hgetv Htypev Hmfv.
    rewrite replace_TskS_other_Event, replace_EventS_EventState in Hgetv.
    rewrite (owner_release_lookup_eq
      (EventState lvs) mid e_old pcp midv Hget) in Hgetv.
    destruct (Z.eqb midv mid) eqn:Hmid.
    + apply Z.eqb_eq in Hmid. subst midv.
      inversion Hgetv; subst ev.
      cbn in Htypev, Hmfv.
      inversion Hmfv; subst mv.
      exists e_old, m_old. repeat split; try assumption; congruence.
    + cbn in Hgetv.
      exists ev, mv. repeat split; try assumption; reflexivity.
  - exact Hunique.
Qed.

(* mutex_owner_consistency 在 mid 处释放 owner 时保持:
   释放后 owner = None,故 None 分支平凡 True *)
Lemma mutex_owner_consistency_preserved_by_release :
  forall sg lvs mid e_old m_old owner_tid pcp,
    (EventState lvs).(inUsedEventStates) mid = Some e_old ->
    e_old.(mutexFields) = Some m_old ->
    m_old.(mfOwner) = Some owner_tid ->
    m_old.(mfPCP) = pcp ->
    mutex_owner_consistency sg lvs ->
    mutex_owner_consistency sg
      (replace_EventS (owner_release_update (EventState lvs) mid e_old pcp) lvs).
Proof.
  intros sg lvs mid e_old m_old owner_tid pcp Hget Hmf1 Howner Hpcp Hmo.
  unfold mutex_owner_consistency in *.
  intros midv ev mv [Hgetv [Htypev Hmfv]].
  unfold replace_EventS in Hgetv.
  unfold EventState at 1 in Hgetv.
  rewrite (owner_release_lookup_eq (EventState lvs) mid e_old pcp midv Hget) in Hgetv.
  destruct (Z.eqb midv mid) eqn:Heq.
  - (* midv = mid:owner = None,trivially True *)
    apply Z.eqb_eq in Heq. subst midv.
    inversion Hgetv; subst. simpl in Hmfv.
    injection Hmfv as Hmf_eq. subst mv.
    simpl. exact I.
  - (* midv <> mid:lookup 给出原 event,直接调用 Hmo *)
    apply Z.eqb_neq in Heq.
    cbv iota in Hgetv.
    apply Hmo with (mid := midv) (e := ev) (m := mv).
    repeat split; [exact Hgetv | exact Htypev | exact Hmfv].
Qed.

(* verification_slice_event_wait_object_consistency 在 mid 处释放 owner 时保持:
   waitList 不变(e_old.waitList 保留),所以原 In 关系保持 *)
Lemma mutex_waitlist_consistency_preserved_by_release :
  forall sg lvs mid e_old m_old owner_tid pcp,
    (EventState lvs).(inUsedEventStates) mid = Some e_old ->
    e_old.(mutexFields) = Some m_old ->
    m_old.(mfOwner) = Some owner_tid ->
    m_old.(mfPCP) = pcp ->
    verification_slice_event_wait_object_consistency sg lvs ->
    verification_slice_event_wait_object_consistency sg
      (replace_EventS (owner_release_update (EventState lvs) mid e_old pcp) lvs).
Proof.
  intros sg lvs mid e_old m_old owner_tid pcp Hget Hmf1 Howner Hpcp Hmw.
  unfold verification_slice_event_wait_object_consistency in *.
  destruct Hmw as [Hmw_entry [Hmw_total Hmw_closed]].
  split; [| split].
  - intros midv ev Hgetv.
    unfold replace_EventS in Hgetv.
    unfold EventState at 1 in Hgetv.
    rewrite (owner_release_lookup_eq (EventState lvs) mid e_old pcp midv Hget) in Hgetv.
    destruct (Z.eqb midv mid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst midv.
      inversion Hgetv; subst.
      eapply verification_slice_event_wait_entry_consistency_irrelevant_fields.
      * reflexivity.
      * reflexivity.
      * exact (Hmw_entry mid e_old Hget).
    + cbv iota in Hgetv.
      exact (Hmw_entry midv ev Hgetv).
  - intros tid t midv ev Ht Hgetv Href.
    rewrite replace_EventS_other_Tsk in Ht.
    unfold replace_EventS in Hgetv.
    unfold EventState at 1 in Hgetv.
    rewrite (owner_release_lookup_eq (EventState lvs) mid e_old pcp midv Hget) in Hgetv.
    destruct (Z.eqb midv mid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst midv.
      inversion Hgetv; subst ev. simpl.
      exact (Hmw_total tid t mid e_old Ht Hget Href).
    + cbv iota in Hgetv.
      exact (Hmw_total tid t midv ev Ht Hgetv Href).
  - eapply task_event_reference_closure_preserved_by_event_extension.
    + intros eid [e He].
      change (exists e0, inUsedEventStates
        (owner_release_update (EventState lvs) mid e_old pcp) eid = Some e0).
      rewrite (owner_release_lookup_eq (EventState lvs) mid e_old pcp eid Hget).
      destruct (Z.eqb eid mid); [eexists; reflexivity|]. exists e. exact He.
    + exact Hmw_closed.
Qed.

(* osprio_cur_consistency 仅依赖 SchedState 与 inUsedTaskStates,
   故 prioTbl 改变 + EventState 改变均不影响 *)
Lemma osprio_cur_consistency_indep_prioTbl_EventState :
  forall sg lvs1 lvs2,
    SchedState lvs2 = SchedState lvs1 ->
    (TskState lvs2).(inUsedTaskStates) = (TskState lvs1).(inUsedTaskStates) ->
    osprio_cur_consistency sg lvs1 ->
    osprio_cur_consistency sg lvs2.
Proof.
  intros sg lvs1 lvs2 HS HI H.
  unfold osprio_cur_consistency in *.
  rewrite HS. rewrite HI. assumption.
Qed.

(* ready_list_completeness 仅依赖 inUsedTaskStates 与 SchedState.readyList,
   release 操作保留两者,故保持 *)
Lemma ready_list_completeness_preserved_by_release :
  forall sg lvs1 lvs2,
    SchedState lvs2 = SchedState lvs1 ->
    (TskState lvs2).(inUsedTaskStates) = (TskState lvs1).(inUsedTaskStates) ->
    ready_list_completeness sg lvs1 ->
    ready_list_completeness sg lvs2.
Proof.
  intros sg lvs1 lvs2 HS HI H.
  unfold ready_list_completeness in *.
  rewrite HS. rewrite HI. assumption.
Qed.

(* ready_list_order 同上 *)
Lemma ready_list_order_preserved_by_release :
  forall sg lvs1 lvs2,
    SchedState lvs2 = SchedState lvs1 ->
    (TskState lvs2).(inUsedTaskStates) = (TskState lvs1).(inUsedTaskStates) ->
    ready_list_order sg lvs1 ->
    ready_list_order sg lvs2.
Proof.
  intros sg lvs1 lvs2 HS HI H.
  unfold ready_list_order in *.
  rewrite HS. rewrite HI. assumption.
Qed.

(* priotbl 投影的简化 helper:为带 inline if-then-else 的 prioTbl 字段提供计算 *)

(* priotbl_consistency 在 release 操作下保持。
   PCP 启用时释放路径把其真实表槽改为 PTReserved；PCP 禁用时
   osPrioMutexCeilDis 只是 event 中的 tag，条件更新不会写 priority table。
   ceiling_priotbl_free 用于排除 total-map 在 tag 位置出现 PTReserved/PTTask
   这类无实现含义的观测。 *)
Lemma priotbl_consistency_preserved_by_release :
  forall sg lvs mid e_old m_old owner_tid owner_t origPrio pcp,
    (EventState lvs).(inUsedEventStates) mid = Some e_old ->
    e_old.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e_old.(mutexFields) = Some m_old ->
    m_old.(mfOwner) = Some owner_tid ->
    (TskState lvs).(inUsedTaskStates) owner_tid = Some owner_t ->
    m_old.(mfOwnerOrigPrio) = Some origPrio ->
    owner_t.(curPrio) = origPrio ->
    m_old.(mfPCP) = pcp ->
    ceiling_priotbl_free sg lvs ->
    priotbl_consistency sg lvs ->
    priotbl_consistency sg
      (replace_TskS
        {| inUsedTaskStates := (TskState lvs).(inUsedTaskStates);
           unUsedTaskStates := (TskState lvs).(unUsedTaskStates);
           tcbListHead := (TskState lvs).(tcbListHead);
           prioTbl := fun p =>
             if (negb (Z.eqb pcp sg.(osPrioMutexCeilDis)) && Z.eqb p pcp)%bool
             then PTReserved
             else (TskState lvs).(prioTbl) p;
           taskRegNextID := (TskState lvs).(taskRegNextID);
           parkedTaskStacks := (TskState lvs).(parkedTaskStacks);
           taskLifecycle := (TskState lvs).(taskLifecycle);
     taskCount := (TskState lvs).(taskCount); |}
        (replace_EventS (owner_release_update (EventState lvs) mid e_old pcp) lvs)).
Proof.
  intros sg lvs mid e_old m_old owner_tid owner_t origPrio pcp
         Hget Htype Hmf Howner Howner_t Horig Howner_prio Hpcp Hceil Hpt.
  unfold priotbl_consistency in *.
  rewrite replace_TskS_TskState.
  rewrite replace_TskS_other_Event.
  rewrite replace_EventS_EventState.
  intros p.
  cbn [prioTbl].
  destruct ((negb (Z.eqb pcp sg.(osPrioMutexCeilDis)) && Z.eqb p pcp)%bool) eqn:Hcond.
  - (* cond=true:p = pcp *)
    exists mid.
    exists {| eventGeneration := e_old.(eventGeneration);
              eventName := e_old.(eventName);
     eventPadding1 := e_old.(eventPadding1);
     eventPadding2 := e_old.(eventPadding2);
     eventPadding3 := e_old.(eventPadding3);
     eventPadding19 := e_old.(eventPadding19);
              eventType   := e_old.(eventType);
             mutexFields := Some {| mfPCP := pcp; mfOwner := None; mfOwnerOrigPrio := None; |};
             semFields   := e_old.(semFields);
             mboxFields  := e_old.(mboxFields);
             queueFields := e_old.(queueFields);
             waitList    := e_old.(waitList); |}.
    exists {| mfPCP := pcp; mfOwner := None; mfOwnerOrigPrio := None; |}.
    rewrite (owner_release_lookup_eq (EventState lvs) mid e_old pcp mid Hget).
    rewrite Z.eqb_refl. cbv iota.
    assert (Hp_eq : p = pcp).
    { apply andb_prop in Hcond as [_ Hpb]. apply Z.eqb_eq in Hpb. exact Hpb. }
    rewrite <- Hp_eq.
    repeat split; try assumption; try reflexivity.
  - (* cond=false:表项不变。这可能因为 p 不是 PCP，也可能因为 PCP
       就是 disabled tag；后一情况不得被强行推成 p <> pcp。 *)
    specialize (Hpt p).
    destruct ((TskState lvs).(prioTbl) p) eqn:Hpttbl.
    + (* 旧 PTFree *)
      destruct Hpt as [HnR HnE].
      split.
      * (* readyList 未变 *)
        intro Habs. apply HnR. exact Habs.
      * (* 不存在 mutex 滀 mfPCP=p *)
        intro Habs.
        destruct Habs as [mid' [e' [m' [Hget' [Htype' [Hmf' Hpcp']]]]]].
        apply HnE.
        exists mid', e', m'.
        unfold replace_TskS in Hget'.
        unfold replace_EventS in Hget'.
        cbv iota in Hget'.
        rewrite (owner_release_lookup_eq (EventState lvs) mid e_old pcp mid' Hget) in Hget'.
        destruct (Z.eqb mid' mid) eqn:Heq.
        -- (* mid' = mid:新 mfPCP=pcp,与 Hpcp'(=p)矛盾 *)
           apply Z.eqb_eq in Heq. subst mid'.
           cbv iota in Hget'. injection Hget' as Hget_eq. subst e'.
           cbv iota in Hmf'. injection Hmf' as Hmf_eq. subst m'.
           unfold mutex_reserves_priority_slot in Hpcp'.
           cbv iota in Hpcp'. destruct Hpcp' as [Henabled Hpcp'].
           assert (Hnb : negb (Z.eqb pcp sg.(osPrioMutexCeilDis)) = true).
           { apply negb_true_iff, Z.eqb_neq. exact Henabled. }
           assert (Hp_eqb : Z.eqb p pcp = true).
           { apply Z.eqb_eq. symmetry. exact Hpcp'. }
           rewrite Hnb, Hp_eqb in Hcond. discriminate.
        -- (* mid' ≠ mid:旧 lookup 不变 *)
           apply Z.eqb_neq in Heq. cbv iota in Hget'.
           split; [exact Hget'|].
           split; [exact Htype'|].
           split; [exact Hmf'|exact Hpcp'].
    + (* 旧 PTReserved *)
      assert (Hp_neq_pcp : p <> pcp).
      { intro Hp.
        destruct (Z.eqb pcp sg.(osPrioMutexCeilDis)) eqn:Htag.
        - apply Z.eqb_eq in Htag.
          unfold ceiling_priotbl_free in Hceil.
          rewrite Hp, Htag, Hceil in Hpttbl. discriminate.
        - apply Z.eqb_neq in Hcond. exact (Hcond Hp). }
      destruct Hpt as [mid' [e' [m' [Hget' [Htype' [Hmf' [Hpcp' Hmfowner']]]]]]].
      destruct (Z.eqb mid' mid) eqn:Heq.
      * (* mid' = mid:Hget' 与 Hget 矛盾 *)
        apply Z.eqb_eq in Heq. subst mid'.
        rewrite Hget in Hget'. injection Hget' as Hget_eq. subst e'.
        rewrite Hmf in Hmf'. injection Hmf' as Hmf_eq. subst m'.
        rewrite Hpcp in Hpcp'. exfalso. apply Hp_neq_pcp. symmetry. exact Hpcp'.
      * (* mid' ≠ mid:新 lookup at mid' 不变 *)
        exists mid', e', m'.
        unfold replace_TskS. unfold replace_EventS. cbv iota.
        rewrite (owner_release_lookup_eq (EventState lvs) mid e_old pcp mid' Hget).
        rewrite Heq. cbv iota.
        repeat split; assumption.
    + (* 旧 PTTask tid *)
      assert (Hp_neq_pcp : p <> pcp).
      { intro Hp.
        destruct (Z.eqb pcp sg.(osPrioMutexCeilDis)) eqn:Htag.
        - apply Z.eqb_eq in Htag.
          unfold ceiling_priotbl_free in Hceil.
          rewrite Hp, Htag, Hceil in Hpttbl. discriminate.
        - apply Z.eqb_neq in Hcond. exact (Hcond Hp). }
      destruct Hpt as [t' [Htget Hsrc]].
      exists t'. split; [exact Htget|].
      destruct Hsrc as [Hcurprio | [mid' [e' [m' [Hget' [Htype' [Hmf' [Hpcp' Hown']]]]]]]].
      * (* 左:来源 1 - curPrio(t') = p *)
        left. exact Hcurprio.
      * (* 右:来源 2 - 存在 mutex mfPCP=p ∧ owner=tid *)
        destruct (Z.eqb mid' mid) eqn:Heq.
        -- (* mid' = mid:旧 mfOwner=Some tid,但旧 mfPCP=p ≠ pcp=mid 的 mfPCP,矛盾 *)
           apply Z.eqb_eq in Heq. subst mid'.
           rewrite Hget in Hget'. injection Hget' as Hget_eq. subst e'.
           rewrite Hmf in Hmf'. injection Hmf' as Hmf_eq. subst m'.
           assert (Htid : tid = owner_tid) by congruence. subst tid.
           rewrite Howner_t in Htget. injection Htget as Ht_eq. subst t'.
           destruct Hown' as [Hpcp_source | Horig_source].
           ++ rewrite Hpcp in Hpcp_source.
              exfalso. apply Hp_neq_pcp. symmetry. exact Hpcp_source.
           ++ left.
              rewrite Horig in Horig_source. injection Horig_source as Hp.
              subst p. exact Howner_prio.
        -- (* mid' ≠ mid:新 lookup 不变 *)
           right. exists mid', e', m'.
           unfold replace_TskS. unfold replace_EventS. cbv iota.
           rewrite (owner_release_lookup_eq (EventState lvs) mid e_old pcp mid' Hget).
           rewrite Heq. cbv iota.
           repeat split; assumption.
Qed.

Lemma mutex_protocol_consistency_preserved_by_release :
  forall sg lvs mid e_old m_old pcp,
    (EventState lvs).(inUsedEventStates) mid = Some e_old ->
    e_old.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e_old.(mutexFields) = Some m_old ->
    m_old.(mfPCP) = pcp ->
    mutex_protocol_consistency sg lvs ->
    mutex_protocol_consistency sg
      (replace_TskS
        {| inUsedTaskStates := (TskState lvs).(inUsedTaskStates);
           unUsedTaskStates := (TskState lvs).(unUsedTaskStates);
           tcbListHead := (TskState lvs).(tcbListHead);
           prioTbl := fun p =>
             if (negb (Z.eqb pcp sg.(osPrioMutexCeilDis)) &&
                 Z.eqb p pcp)%bool
             then PTReserved
             else (TskState lvs).(prioTbl) p;
           taskRegNextID := (TskState lvs).(taskRegNextID);
           parkedTaskStacks := (TskState lvs).(parkedTaskStacks);
           taskLifecycle := (TskState lvs).(taskLifecycle);
     taskCount := (TskState lvs).(taskCount); |}
        (replace_EventS
          (owner_release_update (EventState lvs) mid e_old pcp) lvs)).
Proof.
  intros sg lvs mid e_old m_old pcp Hget Htype Hmf Hpcp Hprotocol.
  unfold mutex_protocol_consistency in *.
  intros midv ev mv Hgetv Htypev Hmfv.
  rewrite replace_TskS_other_Event, replace_EventS_EventState in Hgetv.
  rewrite (owner_release_lookup_eq
    (EventState lvs) mid e_old pcp midv Hget) in Hgetv.
  destruct (Z.eqb midv mid) eqn:Hmid.
  - apply Z.eqb_eq in Hmid. subst midv.
    inversion Hgetv; subst ev.
    cbn in Hmfv. inversion Hmfv; subst mv.
    specialize (Hprotocol mid e_old m_old Hget Htype Hmf).
    destruct Hprotocol as [Hvalid [_ Hslot]].
    split; [now rewrite <- Hpcp |].
    split; [exact I |].
    destruct (Z.eq_dec pcp sg.(osPrioMutexCeilDis)) as [Hdisabled | Henabled].
    + left. exact Hdisabled.
    + right. split; [exact Henabled |].
      left. rewrite replace_TskS_TskState. cbn.
      destruct (Z.eqb pcp sg.(osPrioMutexCeilDis)) eqn:Hdisabled_b.
      * apply Z.eqb_eq in Hdisabled_b. contradiction.
      * rewrite Z.eqb_refl. reflexivity.
  - cbn in Hgetv.
    specialize (Hprotocol midv ev mv Hgetv Htypev Hmfv).
    destruct Hprotocol as [Hvalid [Hfields Hslot]].
    split; [exact Hvalid | split; [exact Hfields |]].
    destruct Hslot as [Hdisabled | [Henabled Hslot]].
    + left. exact Hdisabled.
    + right. split; [exact Henabled |].
      destruct (Z.eq_dec mv.(mfPCP) pcp) as [Heq | Hneq].
      * left. rewrite replace_TskS_TskState. cbn.
        rewrite Heq.
        destruct (Z.eqb pcp sg.(osPrioMutexCeilDis))
          eqn:Hdisabled_b.
        -- apply Z.eqb_eq in Hdisabled_b.
           exfalso. apply Henabled. rewrite Heq. exact Hdisabled_b.
        -- rewrite Z.eqb_refl. reflexivity.
      * rewrite replace_TskS_TskState. cbn.
        assert (Hneqb : Z.eqb mv.(mfPCP) pcp = false).
        { apply Z.eqb_neq. exact Hneq. }
        rewrite Hneqb, Bool.andb_false_r.
        exact Hslot.
Qed.

(* ================================================================== *)
(* 组合 lemma:verification_slice_cross_module_consistency 在 release 操作下整体保持       *)
(* 逐分量组合 release-pattern helpers，包括 PCP lifecycle 与 enabled *)
(* PCP EventID uniqueness，不依赖分支特化假设。                           *)
(* 为 atomic_mutex_release_preserves_inv 提供 cross_module 部分。        *)
(* disabled PCP tag 与 enabled PCP slot 都由同一条件更新语义覆盖。 *)
(* ================================================================== *)
Lemma verification_slice_cross_module_consistency_preserved_by_release :
  forall sg lvs mid e_old m_old owner_tid owner_t origPrio pcp,
    (EventState lvs).(inUsedEventStates) mid = Some e_old ->
    e_old.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e_old.(mutexFields) = Some m_old ->
    m_old.(mfOwner) = Some owner_tid ->
    (TskState lvs).(inUsedTaskStates) owner_tid = Some owner_t ->
    m_old.(mfOwnerOrigPrio) = Some origPrio ->
    owner_t.(curPrio) = origPrio ->
    m_old.(mfPCP) = pcp ->
    verification_slice_cross_module_consistency sg lvs ->
    verification_slice_cross_module_consistency sg
      (replace_TskS
        {| inUsedTaskStates := (TskState lvs).(inUsedTaskStates);
           unUsedTaskStates := (TskState lvs).(unUsedTaskStates);
           tcbListHead      := (TskState lvs).(tcbListHead);
           prioTbl          := fun p =>
             if (negb (Z.eqb pcp sg.(osPrioMutexCeilDis)) && Z.eqb p pcp)%bool
             then PTReserved
             else (TskState lvs).(prioTbl) p;
           taskRegNextID := (TskState lvs).(taskRegNextID);
           parkedTaskStacks := (TskState lvs).(parkedTaskStacks);
           taskLifecycle := (TskState lvs).(taskLifecycle);
     taskCount        := (TskState lvs).(taskCount); |}
        (replace_EventS (owner_release_update (EventState lvs) mid e_old pcp) lvs)).
Proof.
  intros sg lvs mid e_old m_old owner_tid owner_t origPrio pcp
         Hget Htype Hmf Howner Howner_t Horig Howner_prio
         Hpcp Hcm.
  unfold verification_slice_cross_module_consistency in *.
  destruct Hcm as
    [H_osprio [H_pt [H_mo [H_mw [H_rlc [H_rlo
      [H_ceil [H_tpu [H_protocol H_pcp_unique]]]]]]]]].
  split; [| split; [| split; [| split; [| split; [| split;
    [| split; [| split; [| split]]]]]]]].
  - apply osprio_cur_consistency_indep_prioTbl_EventState with (lvs1 := lvs).
    + rewrite replace_TskS_other_Sched, replace_EventS_other_Sched. reflexivity.
    + cbv iota. reflexivity.
    + exact H_osprio.
  - eapply priotbl_consistency_preserved_by_release.
    + exact Hget. + exact Htype. + exact Hmf.
    + exact Howner. + exact Howner_t. + exact Horig.
    + exact Howner_prio. + exact Hpcp. + exact H_ceil. + exact H_pt.
  - eapply mutex_owner_consistency_preserved_by_release.
    + exact Hget. + exact Hmf. + exact Howner. + exact Hpcp. + exact H_mo.
  - eapply mutex_waitlist_consistency_preserved_by_release.
    + exact Hget. + exact Hmf. + exact Howner. + exact Hpcp. + exact H_mw.
  - eapply ready_list_completeness_preserved_by_release with (lvs1 := lvs).
    + rewrite replace_TskS_other_Sched, replace_EventS_other_Sched. reflexivity.
    + cbv iota. reflexivity.
    + exact H_rlc.
  - eapply ready_list_order_preserved_by_release with (lvs1 := lvs).
    + rewrite replace_TskS_other_Sched, replace_EventS_other_Sched. reflexivity.
    + cbv iota. reflexivity.
    + exact H_rlo.
  - unfold ceiling_priotbl_free in *.
    cbn [TskState].
    destruct (Z.eqb pcp sg.(osPrioMutexCeilDis)) eqn:H1.
    + apply Z.eqb_eq in H1. subst pcp.
      simpl. exact H_ceil.
    + simpl.
      destruct (Z.eqb sg.(osPrioMutexCeilDis) pcp) eqn:H2.
      * exfalso. apply Z.eqb_neq in H1. apply Z.eqb_eq in H2. apply H1. symmetry. exact H2.
      * exact H_ceil.
  - unfold task_priority_unique_prop in *.
    rewrite replace_TskS_TskState.
    unfold task_priority_unique in *.
    intros tid1 tid2 t1 t2 Hget1 Hget2 Hcp.
    apply (H_tpu tid1 tid2 t1 t2).
    + cbv iota in Hget1. exact Hget1.
    + cbv iota in Hget2. exact Hget2.
    + exact Hcp.
  - eapply mutex_protocol_consistency_preserved_by_release.
    + exact Hget. + exact Htype. + exact Hmf. + exact Hpcp.
    + exact H_protocol.
  - eapply mutex_enabled_pcp_unique_preserved_by_release.
    + exact Hget. + exact Htype. + exact Hmf. + exact Hpcp.
    + exact H_pcp_unique.
Qed.

(* ================================================================== *)
(* acquire-pattern helpers:atomic_mutex_acquire 改 mfOwner None→Some tid *)
(* (不改 prioTbl/readyList/inUsedTaskStates/waitList,只改 mfOwner/origPrio) *)
(* ================================================================== *)

Definition owner_acquire_update (es : Glob_EventAbstractState)
  (mid : EventID) (e_old : OSEventAbstractState)
  (m_old : MutexFields) (tid : TaskID) (origPrio : Priority)
  : Glob_EventAbstractState :=
  update_event_field_raw es mid
    {| eventGeneration := e_old.(eventGeneration);
       eventName := e_old.(eventName);
     eventPadding1 := e_old.(eventPadding1);
     eventPadding2 := e_old.(eventPadding2);
     eventPadding3 := e_old.(eventPadding3);
     eventPadding19 := e_old.(eventPadding19);
       eventType   := e_old.(eventType);
       mutexFields := Some {| mfPCP := m_old.(mfPCP);
                              mfOwner := Some tid;
                              mfOwnerOrigPrio := Some origPrio; |};
       semFields   := e_old.(semFields);
       mboxFields  := e_old.(mboxFields);
       queueFields := e_old.(queueFields);
       waitList    := e_old.(waitList); |}.

Lemma owner_acquire_lookup_eq :
  forall (es : Glob_EventAbstractState) mid e_old m_old tid origPrio eid,
    es.(inUsedEventStates) mid = Some e_old ->
    e_old.(mutexFields) = Some m_old ->
    (owner_acquire_update es mid e_old m_old tid origPrio).(inUsedEventStates) eid =
      (if Z.eqb eid mid
       then Some {| eventGeneration := e_old.(eventGeneration);
                    eventName := e_old.(eventName);
     eventPadding1 := e_old.(eventPadding1);
     eventPadding2 := e_old.(eventPadding2);
     eventPadding3 := e_old.(eventPadding3);
     eventPadding19 := e_old.(eventPadding19);
                    eventType   := e_old.(eventType);
                    mutexFields := Some {| mfPCP := m_old.(mfPCP);
                                           mfOwner := Some tid;
                                           mfOwnerOrigPrio := Some origPrio; |};
                    semFields   := e_old.(semFields);
                    mboxFields  := e_old.(mboxFields);
                    queueFields := e_old.(queueFields);
                    waitList    := e_old.(waitList); |}
       else es.(inUsedEventStates) eid).
Proof.
  intros es mid e_old m_old tid origPrio eid Hget Hmf.
  unfold owner_acquire_update, update_event_field_raw. simpl. reflexivity.
Qed.

(** Acquisition observes the current effective priority but does not move
    the permanent table slot. The enabled ceiling was reserved while this
    mutex had no owner; hence it cannot be the acquiring task's base, even
    on the source's acquire-then-PCP_LOWER path. *)
Lemma owner_acquire_preserves_owner_snapshots :
  forall sg s mid e m tid t,
    s.(EventState).(inUsedEventStates) mid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m ->
    m.(mfOwner) = None -> s.(TskState).(inUsedTaskStates) tid = Some t ->
    ~ In tid e.(waitList) ->
    mutex_priority_alias_consistency sg s.(TskState) s.(EventState) ->
    mutex_protocol_consistency sg s ->
    mutex_owner_snapshot_in_range sg s.(TskState) s.(EventState) ->
    mutex_owner_snapshot_in_range sg s.(TskState)
      (owner_acquire_update s.(EventState) mid e m tid t.(curPrio)).
Proof.
  intros sg s mid e m tid t He Htype Hm Hnone Htask Hnotwait Halias Hprotocol Hsnapshots.
  destruct (Halias tid t Htask) as [base [Hbase [Hcurrent Hclaims]]].
  assert (HpcpBase : mutex_pcp_enabled sg m -> m.(mfPCP) <> base).
  { intros Henabled Epcp.
    destruct (Hprotocol mid e m He Htype Hm) as [_ [_ Hslot]].
    destruct Hslot as [Hdisabled | [_ [Hreserved | [owner [Howner Hslot]]]]].
    - exact (Henabled Hdisabled).
    - pose proof (proj2 (proj1 Hbase)) as HbaseSlot.
      rewrite <- Epcp, Hreserved in HbaseSlot; discriminate.
    - rewrite Hnone in Howner; discriminate. }
  intros other node fields owner Hnode HnodeType Hfields Howner.
  rewrite (owner_acquire_lookup_eq s.(EventState) mid e m tid t.(curPrio)
    other He Hm) in Hnode.
  destruct (Z.eqb other mid) eqn:Eother.
  - injection Hnode as Enode; subst node.
    cbn in Hfields; injection Hfields as Efields; subst fields.
    cbn in Howner; injection Howner as Eowner; subst owner.
    exists t, base, t.(curPrio); split; [exact Htask|].
    split; [exact Hbase|]. split; [reflexivity|].
    split; [exact (proj1 (proj1 Hcurrent))|].
    split; [exact (task_effective_priority_le_base sg s.(TskState).(prioTbl)
      tid base t.(curPrio) Hbase Hcurrent)|].
    split; [exact Hnotwait|exact HpcpBase].
  - exact (Hsnapshots other node fields owner Hnode HnodeType Hfields Howner).
Qed.

Lemma mutex_enabled_pcp_unique_preserved_by_acquire :
  forall sg lvs mid e_old m_old tid origPrio,
    (EventState lvs).(inUsedEventStates) mid = Some e_old ->
    e_old.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e_old.(mutexFields) = Some m_old ->
    mutex_enabled_pcp_unique sg lvs ->
    mutex_enabled_pcp_unique sg
      (replace_EventS
        (owner_acquire_update
          (EventState lvs) mid e_old m_old tid origPrio) lvs).
Proof.
  intros sg lvs mid e_old m_old tid origPrio Hget Htype Hmf Hunique.
  eapply mutex_enabled_pcp_unique_transport with (lvs1 := lvs).
  - intros midv ev mv Hgetv Htypev Hmfv.
    rewrite replace_EventS_EventState in Hgetv.
    rewrite (owner_acquire_lookup_eq
      (EventState lvs) mid e_old m_old tid origPrio midv Hget Hmf) in Hgetv.
    destruct (Z.eqb midv mid) eqn:Hmid.
    + apply Z.eqb_eq in Hmid. subst midv.
      inversion Hgetv; subst ev.
      cbn in Htypev, Hmfv.
      inversion Hmfv; subst mv.
      exists e_old, m_old. repeat split; try assumption; reflexivity.
    + cbn in Hgetv.
      exists ev, mv. repeat split; try assumption; reflexivity.
  - exact Hunique.
Qed.

Lemma mutex_nonpending_task_not_in_waitlist :
  forall sg lvs mid e tid t,
    (EventState lvs).(inUsedEventStates) mid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    (TskState lvs).(inUsedTaskStates) tid = Some t ->
    (task_non_suspension_bits t.(stat)) = 0 ->
    verification_slice_event_wait_object_consistency sg lvs ->
    ~ In tid e.(waitList).
Proof.
  intros sg lvs mid e tid t Hget Htype Htask Hpend Hmw Hin.
  unfold verification_slice_event_wait_object_consistency in Hmw.
  destruct Hmw as [Hentry _].
  specialize (Hentry mid e Hget) as [_ Hwait].
  rewrite Htype in Hwait. cbn in Hwait.
  specialize (Hwait tid Hin) as [tw [Htw [_ [_ Htw_pend]]]].
  rewrite Htask in Htw. injection Htw as Heq. subst tw.
  rewrite Hpend in Htw_pend. discriminate.
Qed.

(* mutex_owner_consistency 在 acquire 下保持(Qed)。

   协议前提(curTaskID/inUsedTaskStates/curPrio/task_non_suspension_bits)由 caller
   (OSMutexAccept_sem/OSMutexPend_sem)从 atomic_mutex_acquire 传入。
   witness:t_acquire / origPrio。 *)
Lemma mutex_owner_consistency_preserved_by_acquire :
  forall sg lvs mid e_old m_old tid origPrio t_acquire,
    (EventState lvs).(inUsedEventStates) mid = Some e_old ->
    e_old.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e_old.(mutexFields) = Some m_old ->
    m_old.(mfOwner) = None ->
    (lvs.(TskState).(inUsedTaskStates)) tid = Some t_acquire ->
    t_acquire.(curPrio) = origPrio ->
    ~ In tid e_old.(waitList) ->
    mutex_owner_consistency sg lvs ->
    mutex_owner_consistency sg
      (replace_EventS (owner_acquire_update (EventState lvs) mid e_old m_old tid origPrio) lvs).
Proof.
  intros sg lvs mid e_old m_old tid origPrio t_acquire
         Hget Htype Hmf Howner_n Htask Hprio Hnotin Hmo.
  unfold mutex_owner_consistency in *.
  intros midv ev m' [Hgetv [Htypev Hmfv]].
  unfold replace_EventS in Hgetv. unfold EventState at 1 in Hgetv.
  rewrite (owner_acquire_lookup_eq (EventState lvs) mid e_old m_old tid origPrio midv Hget Hmf) in Hgetv.
  destruct (Z.eqb midv mid) eqn:Heq.
  - apply Z.eqb_eq in Heq. subst midv.
    simpl in Hgetv. injection Hgetv as Hget_eq. subst ev.
    simpl in Hmfv. injection Hmfv as Hmf_eq. subst m'.
    cbn.
    exists t_acquire, origPrio.
    split; [exact Htask|]. split; [reflexivity|].
    split; [left; exact Hprio|exact Hnotin].
  - simpl in Hgetv.
    apply (Hmo midv ev m' (conj Hgetv (conj Htypev Hmfv))).
Qed.

(* ready_list_* / mutex_waitlist 在 acquire 下保持(EventState 改但其他不变)*)
Lemma mutex_waitlist_consistency_preserved_by_acquire :
  forall sg lvs mid e_old m_old tid origPrio,
    (EventState lvs).(inUsedEventStates) mid = Some e_old ->
    e_old.(mutexFields) = Some m_old ->
    verification_slice_event_wait_object_consistency sg lvs ->
    verification_slice_event_wait_object_consistency sg
      (replace_EventS (owner_acquire_update (EventState lvs) mid e_old m_old tid origPrio) lvs).
Proof.
  intros sg lvs mid e_old m_old tid origPrio Hget Hmf1 Hmw.
  unfold verification_slice_event_wait_object_consistency in *.
  destruct Hmw as [Hmw_entry [Hmw_total Hmw_closed]].
  split; [| split].
  - intros midv ev Hgetv.
    unfold replace_EventS in Hgetv. unfold EventState at 1 in Hgetv.
    rewrite (owner_acquire_lookup_eq (EventState lvs) mid e_old m_old tid origPrio midv Hget Hmf1) in Hgetv.
    destruct (Z.eqb midv mid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst midv.
      simpl in Hgetv. injection Hgetv as Hget_eq. subst ev.
      eapply verification_slice_event_wait_entry_consistency_irrelevant_fields.
      * reflexivity.
      * reflexivity.
      * exact (Hmw_entry mid e_old Hget).
    + simpl in Hgetv.
      exact (Hmw_entry midv ev Hgetv).
  - intros tidv t midv ev Ht Hgetv Href.
    rewrite replace_EventS_other_Tsk in Ht.
    unfold replace_EventS in Hgetv. unfold EventState at 1 in Hgetv.
    rewrite (owner_acquire_lookup_eq
      (EventState lvs) mid e_old m_old tid origPrio midv Hget Hmf1) in Hgetv.
    destruct (Z.eqb midv mid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst midv.
      simpl in Hgetv. injection Hgetv as Hget_eq. subst ev. simpl.
      exact (Hmw_total tidv t mid e_old Ht Hget Href).
    + simpl in Hgetv.
      exact (Hmw_total tidv t midv ev Ht Hgetv Href).
  - eapply task_event_reference_closure_preserved_by_event_extension.
    + intros eid [e He].
      change (exists e0, inUsedEventStates (owner_acquire_update
        (EventState lvs) mid e_old m_old tid origPrio) eid = Some e0).
      rewrite (owner_acquire_lookup_eq
        (EventState lvs) mid e_old m_old tid origPrio eid Hget Hmf1).
      destruct (Z.eqb eid mid); [eexists; reflexivity|]. exists e. exact He.
    + exact Hmw_closed.
Qed.

(* priotbl_consistency 在 acquire 下保持(Qed)。

   协议前提(curTaskID/inUsedTaskStates/curPrio/task_non_suspension_bits)由 caller
   (OSMutexAccept_sem/OSMutexPend_sem)从 atomic_mutex_acquire 传入。
   证明依赖 PTTask 分支的"来源析取"建模:
   - 来源 1(task 注册):curPrio(tid) = p
   - 来源 2(mutex 占用):某 mutex 的 mfPCP = p 且 owner = tid *)
Lemma priotbl_consistency_preserved_by_acquire :
  forall sg lvs mid e_old m_old tid origPrio t_acquire,
    (EventState lvs).(inUsedEventStates) mid = Some e_old ->
    e_old.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e_old.(mutexFields) = Some m_old ->
    m_old.(mfOwner) = None ->
    (lvs.(TskState).(inUsedTaskStates)) tid = Some t_acquire ->
    t_acquire.(curPrio) = origPrio ->
    priotbl_consistency sg lvs ->
    priotbl_consistency sg
      (replace_EventS (owner_acquire_update (EventState lvs) mid e_old m_old tid origPrio) lvs).
Proof.
  intros sg lvs mid e_old m_old tid origPrio t_acquire
         Hget Htype Hmf Howner_n Htask Hprio Hpt.
  unfold priotbl_consistency in *.
  rewrite replace_EventS_other_Tsk.
  intros p.
  specialize (Hpt p).
  destruct ((lvs.(TskState).(prioTbl)) p) eqn:Hptbl.
  - (* PTFree *)
    destruct Hpt as [HnF1 HnF2]. split; intros Habs.
    + (* 没有 ready task curPrio=p *)
      destruct Habs as [tidv [Hin [t [Ht Hcp]]]].
      apply HnF1. exists tidv. split; [exact Hin |].
      exists t. split; assumption.
    + (* 没有 mutex mfPCP=p *)
      destruct Habs as [midv [ev [mv [Hgetv [Htypev [Hmfv Hpcp]]]]]].
      rewrite (replace_EventS_EventState (owner_acquire_update (EventState lvs) mid e_old m_old tid origPrio) lvs) in Hgetv.
      rewrite (owner_acquire_lookup_eq (EventState lvs) mid e_old m_old tid origPrio midv Hget Hmf) in Hgetv.
      destruct (Z.eqb midv mid) eqn:Heq.
      * apply Z.eqb_eq in Heq. subst midv.
        simpl in Hgetv. injection Hgetv as Hget_eq. subst ev.
        simpl in Hmfv. injection Hmfv as Hmf_eq. subst mv.
        simpl in Hpcp.
        apply HnF2. exists mid, e_old, m_old.
        split; [exact Hget|].
        split; [exact Htype|].
        split; [exact Hmf|].
        unfold mutex_reserves_priority_slot in *; simpl in *.
        exact Hpcp.
      * simpl in Hgetv.
        apply HnF2. exists midv, ev, mv.
        split; [exact Hgetv|].
        split; [exact Htypev|].
        split; [exact Hmfv|exact Hpcp].
  - (* PTReserved *)
    destruct Hpt as [midv [ev [mv [Hgetv [Htypev [Hmfv [Hpcp Hmatch]]]]]]].
    rewrite replace_EventS_EventState.
    destruct (Z.eqb midv mid) eqn:Heq.
    + (* witness 是 mid:acquire 后 mid owner = Some tid,需要 PTReserved 的 Some tid 分支 *)
      apply Z.eqb_eq in Heq. subst midv.
      rewrite Hget in Hgetv. injection Hgetv as Hget_eq. subst ev.
      rewrite Hmf in Hmfv. injection Hmfv as Hmf_eq. subst mv.
      simpl in Hpcp.
      exists mid.
      exists {| eventGeneration := e_old.(eventGeneration);
                eventName := e_old.(eventName);
     eventPadding1 := e_old.(eventPadding1);
     eventPadding2 := e_old.(eventPadding2);
     eventPadding3 := e_old.(eventPadding3);
     eventPadding19 := e_old.(eventPadding19);
                eventType   := e_old.(eventType);
               mutexFields := Some {| mfPCP := m_old.(mfPCP); mfOwner := Some tid; mfOwnerOrigPrio := Some origPrio; |};
               semFields   := e_old.(semFields);
               mboxFields  := e_old.(mboxFields);
               queueFields := e_old.(queueFields);
               waitList    := e_old.(waitList); |}.
      exists {| mfPCP := m_old.(mfPCP); mfOwner := Some tid; mfOwnerOrigPrio := Some origPrio; |}.
      repeat split.
      * rewrite (owner_acquire_lookup_eq (EventState lvs) mid e_old m_old tid origPrio mid Hget Hmf).
        rewrite Z.eqb_refl. reflexivity.
      * exact Htype.
      * exact Hpcp.
      * simpl. exists t_acquire, origPrio. repeat split; auto.
    + (* witness 不是 mid:不变 *)
      exists midv, ev, mv.
      rewrite (owner_acquire_lookup_eq (EventState lvs) mid e_old m_old tid origPrio midv Hget Hmf).
      rewrite Heq. simpl.
      repeat split; assumption.
  - (* PTTask tidv *)
    destruct Hpt as [t_v [Ht_v Hsrc]].
    exists t_v. split; [exact Ht_v |].
    destruct Hsrc as [Hcp | [midv [ev [mv [Hgetv [Htypev [Hmfv [Hpcp Howner_v]]]]]]]].
    + (* 来源 1:curPrio(t_v) = p *)
      left. exact Hcp.
    + (* 来源 2:某 mutex 持有 tidv 且 mfPCP = p *)
      right.
      destruct (Z.eqb midv mid) eqn:Heq.
      * (* midv = mid:矛盾 — m_old.(mfOwner) = None(Howner_n)与 Some tidv(Howner_v)冲突 *)
        apply Z.eqb_eq in Heq. subst midv.
        rewrite Hget in Hgetv. injection Hgetv as Hget_eq. subst ev.
        rewrite Hmf in Hmfv. injection Hmfv as Hmf_eq. subst mv.
        rewrite Howner_n in Hpcp. discriminate.
      * (* midv ≠ mid:witness 不变 *)
        exists midv, ev, mv.
        rewrite replace_EventS_EventState.
        rewrite (owner_acquire_lookup_eq (EventState lvs) mid e_old m_old tid origPrio midv Hget Hmf).
        rewrite Heq. simpl.
        repeat split; assumption.
Qed.

Lemma mutex_protocol_consistency_preserved_by_acquire :
  forall sg lvs mid e_old m_old tid origPrio t_acquire,
    (EventState lvs).(inUsedEventStates) mid = Some e_old ->
    e_old.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e_old.(mutexFields) = Some m_old ->
    m_old.(mfOwner) = None ->
    (TskState lvs).(inUsedTaskStates) tid = Some t_acquire ->
    t_acquire.(curPrio) = origPrio ->
    task_priority_in_range sg origPrio ->
    task_current_prio_registered (TskState lvs) ->
    mutex_protocol_consistency sg lvs ->
    mutex_protocol_consistency sg
      (replace_EventS
        (owner_acquire_update
          (EventState lvs) mid e_old m_old tid origPrio) lvs).
Proof.
  intros sg lvs mid e_old m_old tid origPrio t_acquire
    Hget Htype Hmf Howner_none Htask Hprio Hvalid_orig
    Hregistered Hprotocol.
  unfold mutex_protocol_consistency in *.
  intros midv ev mv Hgetv Htypev Hmfv.
  rewrite replace_EventS_EventState in Hgetv.
  rewrite (owner_acquire_lookup_eq
    (EventState lvs) mid e_old m_old tid origPrio midv Hget Hmf) in Hgetv.
  destruct (Z.eqb midv mid) eqn:Hmid.
  - apply Z.eqb_eq in Hmid. subst midv.
    inversion Hgetv; subst ev.
    cbn in Hmfv. inversion Hmfv; subst mv.
    specialize (Hprotocol mid e_old m_old Hget Htype Hmf).
    destruct Hprotocol as [Hvalid [Hfields Hslot]].
    split; [exact Hvalid |].
    split.
    + cbn. split; [exact Hvalid_orig |].
      intros Henabled Heq_orig.
      destruct Hslot as [Hdisabled | [Henabled_old Hslot]].
      * exact (Henabled Hdisabled).
      * destruct Hslot as [Hreserved | [owner [Howner_some Howner_slot]]].
        -- pose proof (Hregistered tid t_acquire Htask) as Htask_slot.
           rewrite Hprio, Heq_orig, Hreserved in Htask_slot.
           discriminate.
        -- rewrite Howner_none in Howner_some. discriminate.
    + rewrite replace_EventS_other_Tsk. cbn.
      destruct Hslot as [Hdisabled | [Henabled Hslot]].
      * left. exact Hdisabled.
      * right. split; [exact Henabled |].
        destruct Hslot as [Hreserved | [owner [Howner_some Howner_slot]]].
        -- left. exact Hreserved.
        -- rewrite Howner_none in Howner_some. discriminate.
  - cbn in Hgetv.
    specialize (Hprotocol midv ev mv Hgetv Htypev Hmfv).
    rewrite replace_EventS_other_Tsk.
    exact Hprotocol.
Qed.

(* ==================================================================
   verification_slice_cross_module_consistency_preserved_by_acquire:
   结构性 Qed — 把 verification_slice_cross_module_consistency 的合取分量分别处理:
     - osprio_cur_consistency:     SchedState/TskState 不变 → Qed
     - priotbl_consistency:         抽象缝隙 → 聚焦事实
     - mutex_owner_consistency:     抽象缝隙 → 聚焦事实
     - verification_slice_event_wait_object_consistency:  waitList 不变 → Qed
     - ready_list_completeness:     SchedState/TskState 不变 → Qed
     - ready_list_order:            SchedState/TskState 不变 → Qed
     - mutex protocol / PCP uniqueness: owner-only update 保留 PCP。
   所有分量都由本文件的 Qed helper 组合，没有未证明的聚焦假设。     *)
Lemma verification_slice_cross_module_consistency_preserved_by_acquire :
  forall sg lvs mid e_old m_old tid origPrio t_acquire,
    (EventState lvs).(inUsedEventStates) mid = Some e_old ->
    e_old.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e_old.(mutexFields) = Some m_old ->
    m_old.(mfOwner) = None ->
    (lvs.(TskState).(inUsedTaskStates)) tid = Some t_acquire ->
    t_acquire.(curPrio) = origPrio ->
    (task_non_suspension_bits (t_acquire.(stat))) = 0 ->
    valid_task_prio sg origPrio ->
    task_current_prio_registered (TskState lvs) ->
    verification_slice_cross_module_consistency sg lvs ->
    verification_slice_cross_module_consistency sg
      (replace_EventS (owner_acquire_update (EventState lvs) mid e_old m_old tid origPrio) lvs).
Proof.
  intros sg lvs mid e_old m_old tid origPrio t_acquire
         Hget Htype Hmf Howner_n Htask Hprio Hpend Hvalid_orig
         Hregistered Hcm.
  unfold verification_slice_cross_module_consistency in *.
  destruct Hcm as
    [H_osprio [H_pt [H_mo [H_mw [H_rlc [H_rlo
      [H_ceil [H_tpu [H_protocol H_pcp_unique]]]]]]]]].
  split; [| split; [| split; [| split; [| split; [| split;
    [| split; [| split; [| split]]]]]]]].
  - apply osprio_cur_consistency_indep_EventState with (lvs1 := lvs).
    + rewrite replace_EventS_other_Sched. reflexivity.
    + rewrite replace_EventS_other_Tsk. reflexivity.
    + exact H_osprio.
  - eapply priotbl_consistency_preserved_by_acquire.
    + exact Hget. + exact Htype. + exact Hmf. + exact Howner_n.
    + exact Htask. + exact Hprio. + exact H_pt.
  - eapply mutex_owner_consistency_preserved_by_acquire.
    + exact Hget. + exact Htype. + exact Hmf. + exact Howner_n.
    + exact Htask. + exact Hprio.
    + eapply mutex_nonpending_task_not_in_waitlist; eauto.
    + exact H_mo.
  - eapply mutex_waitlist_consistency_preserved_by_acquire.
    + exact Hget. + exact Hmf. + exact H_mw.
  - apply ready_list_completeness_indep_EventState with (lvs1 := lvs).
    + rewrite replace_EventS_other_Tsk. reflexivity.
    + rewrite replace_EventS_other_Sched. reflexivity.
    + exact H_rlc.
  - apply ready_list_order_indep_EventState with (lvs1 := lvs).
    + rewrite replace_EventS_other_Tsk. reflexivity.
    + rewrite replace_EventS_other_Sched. reflexivity.
    + exact H_rlo.
  - exact H_ceil.
  - unfold task_priority_unique_prop in *.
    rewrite replace_EventS_other_Tsk. exact H_tpu.
  - eapply mutex_protocol_consistency_preserved_by_acquire.
    + exact Hget. + exact Htype. + exact Hmf. + exact Howner_n.
    + exact Htask. + exact Hprio.
    + unfold valid_task_prio in Hvalid_orig; unfold task_priority_in_range; lia.
    + exact Hregistered. + exact H_protocol.
  - eapply mutex_enabled_pcp_unique_preserved_by_acquire.
    + exact Hget. + exact Htype. + exact Hmf.
    + exact H_pcp_unique.
Qed.

(* ================================================================== *)
(* 2026-07-08:atomic_mutex_release_with_handover 的 sub-invariant 保持 *)
(*                                                                    *)
(* handover 与 acquire 的差异:mfOwner Some old → Some new(而非 None→Some) *)
(* 与 release 的差异:mfOwner 不变空 + new_owner_t' + 加入 readyList       *)
(*                                                                    *)
(* 关键不变量:new_owner_t'.curPrio = new_owner_t.curPrio(保留),         *)
(* mutex_mfOwnerOrigPrio = Some new_owner_t.curPrio,使                  *)
(* mutex_owner_consistency 的 curPrio = op 自动满足。                   *)
(* ================================================================== *)

Definition handover_event_update (es : Glob_EventAbstractState)
  (mid : EventID) (e_old : OSEventAbstractState)
  (m_old : MutexFields) (new_owner : TaskID) (new_orig_prio : Priority)
  (rest_waitlist : list TaskID)
  : Glob_EventAbstractState :=
  update_event_field_raw es mid
    {| eventGeneration := e_old.(eventGeneration);
       eventName := e_old.(eventName);
     eventPadding1 := e_old.(eventPadding1);
     eventPadding2 := e_old.(eventPadding2);
     eventPadding3 := e_old.(eventPadding3);
     eventPadding19 := e_old.(eventPadding19);
       eventType   := e_old.(eventType);
       mutexFields := Some {| mfPCP := m_old.(mfPCP);
                              mfOwner := Some new_owner;
                              mfOwnerOrigPrio := Some new_orig_prio; |};
       semFields   := e_old.(semFields);
       mboxFields  := e_old.(mboxFields);
       queueFields := e_old.(queueFields);
       waitList    := rest_waitlist; |}.

Lemma handover_event_lookup_eq :
  forall (es : Glob_EventAbstractState) mid e_old m_old
         new_owner new_orig_prio rest_waitlist eid,
    es.(inUsedEventStates) mid = Some e_old ->
    e_old.(mutexFields) = Some m_old ->
    (handover_event_update es mid e_old m_old new_owner new_orig_prio rest_waitlist).(inUsedEventStates) eid =
      (if Z.eqb eid mid
       then Some {| eventGeneration := e_old.(eventGeneration);
                    eventName := e_old.(eventName);
     eventPadding1 := e_old.(eventPadding1);
     eventPadding2 := e_old.(eventPadding2);
     eventPadding3 := e_old.(eventPadding3);
     eventPadding19 := e_old.(eventPadding19);
                    eventType   := e_old.(eventType);
                    mutexFields := Some {| mfPCP := m_old.(mfPCP);
                                           mfOwner := Some new_owner;
                                           mfOwnerOrigPrio := Some new_orig_prio; |};
                    semFields   := e_old.(semFields);
                    mboxFields  := e_old.(mboxFields);
                    queueFields := e_old.(queueFields);
                    waitList    := rest_waitlist; |}
       else es.(inUsedEventStates) eid).
Proof.
  intros es mid e_old m_old new_owner new_orig_prio rest_waitlist eid Hget Hmf.
  unfold handover_event_update, update_event_field_raw. simpl. reflexivity.
Qed.

Lemma mutex_enabled_pcp_unique_preserved_by_handover :
  forall sg lvs mid e_old m_old new_owner new_orig_prio rest_waitlist,
    (EventState lvs).(inUsedEventStates) mid = Some e_old ->
    e_old.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e_old.(mutexFields) = Some m_old ->
    mutex_enabled_pcp_unique sg lvs ->
    mutex_enabled_pcp_unique sg
      (replace_EventS
        (handover_event_update (EventState lvs) mid e_old m_old
          new_owner new_orig_prio rest_waitlist) lvs).
Proof.
  intros sg lvs mid e_old m_old new_owner new_orig_prio rest_waitlist
    Hget Htype Hmf Hunique.
  eapply mutex_enabled_pcp_unique_transport with (lvs1 := lvs).
  - intros midv ev mv Hgetv Htypev Hmfv.
    rewrite replace_EventS_EventState in Hgetv.
    rewrite (handover_event_lookup_eq
      (EventState lvs) mid e_old m_old new_owner new_orig_prio
      rest_waitlist midv Hget Hmf) in Hgetv.
    destruct (Z.eqb midv mid) eqn:Hmid.
    + apply Z.eqb_eq in Hmid. subst midv.
      inversion Hgetv; subst ev.
      cbn in Htypev, Hmfv.
      inversion Hmfv; subst mv.
      exists e_old, m_old. repeat split; try assumption; reflexivity.
    + cbn in Hgetv.
      exists ev, mv. repeat split; try assumption; reflexivity.
  - exact Hunique.
Qed.

(* osprio_cur_consistency 在 handover 下保持:
   curTaskID 不变(atomic step 不改 curTaskID),inU 在 new_owner 处更新但 curPrio 保留。 *)
Lemma osprio_cur_consistency_preserved_by_handover :
  forall sg lvs1 lvs2 new_owner new_owner_t' new_owner_t,
    (TskState lvs2).(inUsedTaskStates) new_owner = Some new_owner_t' ->
    new_owner_t'.(curPrio) = new_owner_t.(curPrio) ->
    (forall tid, (TskState lvs2).(inUsedTaskStates) tid =
      if Z.eqb tid new_owner then Some new_owner_t'
      else (TskState lvs1).(inUsedTaskStates) tid) ->
    (SchedState lvs2).(curTaskID) = (SchedState lvs1).(curTaskID) ->
    (SchedState lvs2).(curSchedPrio) = (SchedState lvs1).(curSchedPrio) ->
    (TskState lvs1).(inUsedTaskStates) new_owner = Some new_owner_t ->
    osprio_cur_consistency sg lvs1 ->
    osprio_cur_consistency sg lvs2.
Proof.
  intros sg lvs1 lvs2 new_owner new_owner_t' new_owner_t
         Hget_new Hnew_prio HinU_lvs2 HcurTaskID HcurSchedPrio HinU1 Hosc.
  unfold osprio_cur_consistency in *.
  rewrite HcurTaskID, HcurSchedPrio.
  destruct ((SchedState lvs1).(curTaskID)) as [curtid |].
  - destruct (Z.eqb curtid new_owner) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst curtid.
      destruct Hosc as [t [HinU Hcp]].
      rewrite HinU1 in HinU. injection HinU as Heq_t. subst t.
      exists new_owner_t'. split.
      * rewrite HinU_lvs2, Z.eqb_refl. reflexivity.
      * rewrite Hnew_prio. exact Hcp.
    + destruct Hosc as [t [HinU Hcp]].
      exists t. split.
      * rewrite HinU_lvs2. rewrite Heq. exact HinU.
      * exact Hcp.
  - simpl. assumption.
Qed.

(* ready_list_completeness 在 handover 下保持:
   - tid = new_owner:new_owner_t' 若 effectively_ready,需在 newReadyList
   - tid ≠ new_owner:state 不变,旧 readyList ⊆ newReadyList *)
Lemma ready_list_completeness_preserved_by_handover :
  forall sg lvs1 lvs2 new_owner new_owner_t' new_owner_t newReadyList,
    (TskState lvs2).(inUsedTaskStates) new_owner = Some new_owner_t' ->
    (task_non_suspension_bits new_owner_t'.(stat)) = 0 ->
    new_owner_t'.(dly) = 0 ->
    (task_is_suspended new_owner_t'.(stat)) = (task_is_suspended new_owner_t.(stat)) ->
    (forall tid, (TskState lvs2).(inUsedTaskStates) tid =
      if Z.eqb tid new_owner then Some new_owner_t'
      else (TskState lvs1).(inUsedTaskStates) tid) ->
    (SchedState lvs2).(readyList) = newReadyList ->
    In new_owner newReadyList ->
    (forall tid, In tid (SchedState lvs1).(readyList) -> In tid newReadyList) ->
    ready_list_completeness sg lvs1 ->
    ready_list_completeness sg lvs2.
Proof.
  intros sg lvs1 lvs2 new_owner new_owner_t' new_owner_t newReadyList
         Hget_new Hpend Hdly Hsusp HinU_lvs2 HreadyList Hin_new Hin_preserved Hrlc.
  unfold ready_list_completeness in *.
  intros tidv t Ht Heff.
  rewrite HinU_lvs2 in Ht.
  destruct (Z.eqb tidv new_owner) eqn:Heq_tidv.
  - (* tidv = new_owner *)
    apply Z.eqb_eq in Heq_tidv. subst tidv.
    injection Ht as Heq_t. subst t.
    unfold is_effectively_ready in Heff.
    rewrite Hpend, Hdly in Heff. simpl in Heff.
    rewrite Hsusp in Heff.
    destruct ((task_is_suspended new_owner_t.(stat))); simpl in Heff.
    + discriminate Heff.
    + rewrite HreadyList. exact Hin_new.
  - (* tidv ≠ new_owner *)
    cbv iota in Ht.
    rewrite HreadyList.
    apply Hin_preserved.
    apply (Hrlc tidv t). exact Ht. exact Heff.
Qed.

Lemma task_mutex_priotbl_consistency_update_task : forall sg tasks events tid old new,
  tasks.(inUsedTaskStates) tid = Some old -> new.(curPrio) = old.(curPrio) ->
  task_mutex_priotbl_consistency sg tasks events ->
  task_mutex_priotbl_consistency sg (glob_task_set_usedtask tasks tid new) events.
Proof.
  intros sg tasks events tid old new Hold Hp [Hreservations [Hslots Halias]].
  split; [exact Hreservations|]. split.
  - intros p Hrange; specialize (Hslots p Hrange); simpl; destruct (tasks.(prioTbl) p); try exact Hslots.
    apply (proj2 (glob_task_set_usedtask_live_iff tasks tid old new _ Hold)); exact Hslots.
  - eapply mutex_priority_alias_consistency_update_task; eauto.
Qed.

(** Shared graph-unlink boundary for wake, timeout cleanup and deletion.
    The actual caller supplies its own TCB writes.  Removing the Flag node
    does not itself clear status, wake the Task or retire its invocation. *)
Lemma flag_unlink_update_task_preserves_cross_module_consistency :
  forall sg s p w after old new,
    cross_module_consistency sg s -> event_in_range sg s.(TskState) s.(EventState) ->
    flag_unlink_node s.(FlagState) p = Some (w, after) ->
    s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old ->
    new.(curPrio) = old.(curPrio) -> new.(eventPtr) = old.(eventPtr) ->
    new.(eventMultiWaitEvents) = old.(eventMultiWaitEvents) ->
    new.(tcbFlagNode) = 0 ->
    task_non_suspension_bits new.(stat) <> task_pend_mask PendFlag ->
    cross_module_consistency sg
      (replace_FlagS after (replace_TskS (glob_task_set_usedtask s.(TskState) w.(flagTask) new) s)).
Proof.
  intros sg s p w after old new
    [Htable [Hsnapshot [Hevent [Hprotocol [Hunique [Hflag Htimer]]]]]]
    Hevents Hstep Hold Hprio Hptr Hmulti Hnull Hpending.
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hstep)) as Hw.
  split.
  - eapply task_mutex_priotbl_consistency_update_task; eassumption.
  - split.
    + eapply mutex_owner_snapshot_update_task; eassumption.
    + split.
      * eapply event_wait_object_update_unlisted_task;
          [exact Hold|exact Hptr|exact Hmulti| |exact Hevent].
        intros eid e He; eapply task_flag_waiter_not_in_event_wait_list; eauto.
      * split; [exact Hprotocol|]. split; [exact Hunique|]. split; [|exact Htimer].
        eapply task_flag_unlink_preserves_consistency; eassumption.
Qed.

(** Complete endpoint after OS_FlagTaskRdy's TCB/ready writes and unlink.
    This transformer does not authorize an unmasked intermediate store. *)
Definition flag_wake_state (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (after : GlobFlagState) (old : TaskAbstractState)
  (bits : Z) (result : PendStatus) : UCOS2_Verify_State :=
  replace_FlagS after
    (replace_SchedS
      (sched_wake_task sg s.(TskState) s.(SchedState) w.(flagTask)
        (task_flag_wake old bits result))
      (replace_TskS
        (glob_task_set_usedtask s.(TskState) w.(flagTask) (task_flag_wake old bits result)) s)).

(** OS_FlagTaskRdy's actual node/TCB selection and BOOLEAN result.  The
    pure unlink result describes final ownership; it does not move the
    C unlink call before the TCB stores.  None is outside the represented
    lookup domain, not an additional C error branch.  A false result still
    performs the TCB update and unlink.  As in flag_wake_state,
    the endpoint uses the TaskDelete-enabled node-pointer cleanup profile. *)
Definition flag_task_rdy (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (p : addr) (bits : Z) (result : PendStatus) : option (bool * UCOS2_Verify_State) :=
  match flag_unlink_node s.(FlagState) p with
  | Some (w, after) =>
      match s.(TskState).(inUsedTaskStates) w.(flagTask) with
      | Some old => Some
          (Z.eqb (encode_task_status (task_flag_wake old bits result).(stat)) 0,
           flag_wake_state sg s w after old bits result)
      | None => None
      end
  | None => None
  end.

(** The literal source test agrees with the scheduler updater's decision.
    True means that the source executes ready writes, not necessarily that
    the task was absent from the ready set before this timeout-linked wake. *)
Lemma flag_task_rdy_result : forall sg s p bits result schedule post,
  flag_task_rdy sg s p bits result = Some (schedule, post) ->
  exists w after old,
    flag_unlink_node s.(FlagState) p = Some (w, after) /\
    s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old /\
    post = flag_wake_state sg s w after old bits result /\
    schedule = is_effectively_ready (task_flag_wake old bits result).(stat)
      (task_flag_wake old bits result).(dly).
Proof.
  intros sg s p bits result schedule post Hstep.
  unfold flag_task_rdy in Hstep.
  destruct (flag_unlink_node s.(FlagState) p) as [[w after]|] eqn:Hunlink;
    [|discriminate].
  destruct (s.(TskState).(inUsedTaskStates) w.(flagTask)) as [old|] eqn:Hold;
    [|discriminate].
  injection Hstep as Hschedule Hpost; subst schedule; subst post.
  exists w, after, old; split; [reflexivity|]; split; [exact Hold|]; split; [reflexivity|].
  change (Z.eqb (encode_task_status (task_flag_wake old bits result).(stat)) 0 =
    is_effectively_ready (task_flag_wake old bits result).(stat) 0).
  symmetry; apply is_effectively_ready_zero_delay_eq.
Qed.

(** A valid linked node cannot fall through the option-valued model's
    missing-lookup cases.  The selected ID names the physical TCB pointer
    stored in that node, not an independently chosen abstract task. *)
Lemma flag_task_rdy_selects_waiter : forall sg s p w bits result,
  valid_flag_configuration sg s.(FlagState) ->
  task_flag_waiter_consistency sg s.(TskState) s.(FlagState) ->
  s.(FlagState).(flagWaitNodes) p = Some w ->
  exists old after,
    s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old /\
    w.(flagWaitImage).(flagNodeTCB) = task_slot_addr sg w.(flagTask) /\
    flag_unlink_node s.(FlagState) p = Some (w, after) /\
    flag_task_rdy sg s p bits result = Some
      (Z.eqb (encode_task_status (task_flag_wake old bits result).(stat)) 0,
       flag_wake_state sg s w after old bits result).
Proof.
  intros sg s p w bits result Hflags [Hnodes _] Hw.
  assert (Hvalid : valid_flag_state sg s.(FlagState)).
  { unfold valid_flag_configuration in Hflags.
    destruct sg.(osKernelConfig).(cfgFlagEnabled);
      [exact Hflags|rewrite Hflags in Hw; discriminate]. }
  destruct (Hnodes p w Hw) as [_ [old [Hold [_ [_ [Haddr _]]]]]].
  destruct (flag_linked_node_unlink_exists sg s.(FlagState) p w Hvalid Hw) as [after Hunlink].
  exists old, after; split; [exact Hold|]; split; [exact Haddr|]; split; [exact Hunlink|].
  unfold flag_task_rdy; rewrite Hunlink, Hold; reflexivity.
Qed.

Lemma flag_wake_preserves_cross_module_consistency : forall sg s p w after old bits result,
  cross_module_consistency sg s -> event_in_range sg s.(TskState) s.(EventState) ->
  flag_unlink_node s.(FlagState) p = Some (w, after) ->
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old ->
  cross_module_consistency sg (flag_wake_state sg s w after old bits result).
Proof.
  intros sg s p w after old bits result Hcross Hevents Hstep Hold.
  destruct (task_flag_wake_clears_registration old bits result) as [Hnull Hpending].
  exact (flag_unlink_update_task_preserves_cross_module_consistency
    sg s p w after old (task_flag_wake old bits result)
    Hcross Hevents Hstep Hold eq_refl eq_refl eq_refl Hnull Hpending).
Qed.

(** Timeout has already cleared the pending bit and performed the ready
    update. This cleanup clears the TCB's node pointer and unlinks its Flag
    node; it does not wake the Task again or change scheduler caches. *)
Definition flag_timeout_cleanup_state (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (after : GlobFlagState) (old : TaskAbstractState) : UCOS2_Verify_State :=
  replace_FlagS after
    (replace_TskS (glob_task_set_usedtask s.(TskState) w.(flagTask) (task_set_flag_node old 0)) s).

Lemma task_flag_waiter_cleared_pending_is_timeout : forall sg tasks flags p w old,
  task_flag_waiter_consistency sg tasks flags -> flags.(flagWaitNodes) p = Some w ->
  tasks.(inUsedTaskStates) w.(flagTask) = Some old -> (task_non_suspension_bits old.(stat)) = 0 ->
  old.(statPend) = PendTimeout /\ old.(dly) = 0.
Proof.
  intros sg tasks flags p w old [Hnodes _] Hw Hold Hp.
  destruct (Hnodes p w Hw) as [_ [t [Ht [_ [_ [_ [Hphase _]]]]]]].
  rewrite Hold in Ht; injection Ht as Heq; subst t.
  destruct Hphase as [Hpending|[_ Htimeout]];
    [rewrite Hp in Hpending; discriminate|exact Htimeout].
Qed.

Lemma flag_timeout_cleanup_preserves_cross_module_consistency : forall sg s p w after old,
  cross_module_consistency sg s -> event_in_range sg s.(TskState) s.(EventState) ->
  flag_unlink_node s.(FlagState) p = Some (w, after) ->
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old -> (task_non_suspension_bits old.(stat)) = 0 ->
  cross_module_consistency sg (flag_timeout_cleanup_state s w after old).
Proof.
  intros sg s p w after old Hcross Hevents Hstep Hold Hp.
  exact (flag_unlink_update_task_preserves_cross_module_consistency
    sg s p w after old (task_set_flag_node old 0)
    Hcross Hevents Hstep Hold eq_refl eq_refl eq_refl eq_refl
    ltac:(change (task_non_suspension_bits old.(stat) <> task_pend_mask PendFlag);
      rewrite Hp; discriminate)).
Qed.

Lemma task_with_event_ptr_has_no_flag_registration : forall sg tasks flags tid t eid,
  task_flag_waiter_consistency sg tasks flags -> tasks.(inUsedTaskStates) tid = Some t ->
  t.(eventPtr) = Some eid ->
  t.(tcbFlagNode) = 0 /\ (task_non_suspension_bits t.(stat)) <> task_pend_mask PendFlag.
Proof.
  intros sg tasks flags tid t eid [Hnodes Htasks] Ht Hevent.
  assert (Hnone : ~ (t.(tcbFlagNode) <> 0 \/ (task_non_suspension_bits t.(stat)) = task_pend_mask PendFlag)).
  { intro Hactive; destruct (Htasks tid t Ht Hactive) as [w [Hw Htid]].
    destruct (Hnodes _ w Hw) as [_ [before [Hbefore [_ [_ [_ [_ [Hnull _]]]]]]]].
    rewrite Htid, Ht in Hbefore; injection Hbefore as Hbefore; subst before; congruence. }
  split; [destruct (Z.eq_dec t.(tcbFlagNode) 0); tauto|tauto].
Qed.

Lemma task_flag_waiter_consistency_update_unregistered_task : forall sg tasks flags tid old new,
  tasks.(inUsedTaskStates) tid = Some old -> old.(tcbFlagNode) = 0 ->
  new.(tcbFlagNode) = 0 -> (task_non_suspension_bits new.(stat)) <> task_pend_mask PendFlag ->
  task_flag_waiter_consistency sg tasks flags ->
  task_flag_waiter_consistency sg (glob_task_set_usedtask tasks tid new) flags.
Proof.
  intros sg tasks flags tid old new Hold Holdnull Hnewnull Hnopend [Hnodes Htasks].
  split.
  - intros p w Hw; destruct (Hnodes p w Hw) as [Hp [t [Ht Hrest]]].
    split; [exact Hp|]; exists t; split; [|exact Hrest].
    simpl; destruct (Z.eqb w.(flagTask) tid) eqn:E; [|exact Ht].
    apply Z.eqb_eq in E; rewrite E, Hold in Ht; injection Ht as Ht; subst t.
    destruct Hrest as [_ [Hptr _]]; congruence.
  - intros slot t Ht Hactive; simpl in Ht; destruct (Z.eqb slot tid) eqn:E.
    + injection Ht as Ht; subst t; destruct Hactive; contradiction.
    + eapply Htasks; eauto.
Qed.

(** Complete single-Event wake endpoint, including the Remove callee.
    The caller supplies the selected waiter; bitmap decoding is a separate
    refinement.  The actual suspension test, not quiescent readiness, guards
    ready writes.  Physical current/high-ready caches are not refreshed. *)
Definition event_wake_state (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState) (tid : TaskID) (old : TaskAbstractState)
  (kind : PendType) (message : addr) (result : PendStatus) : UCOS2_Verify_State :=
  let new := task_event_wake_single old kind message result in
  replace_SchedS (sched_wake_by_status sg s.(TskState) s.(SchedState) tid
      (encode_task_status new.(stat)))
    (replace_EventS
      (update_event_field_raw s.(EventState) eid (event_set_wait_list e (remove_Z_eqb tid e.(waitList))))
      (replace_TskS (glob_task_set_usedtask s.(TskState) tid new) s)).

Lemma event_wake_preserves_task_sched : forall sg s eid e tid old kind message result,
  task_in_range sg s.(TskState) -> sched_in_range sg s.(TskState) s.(SchedState) ->
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  task_linked_wait_phase old kind ->
  let after := event_wake_state sg s eid e tid old kind message result in
  task_in_range sg after.(TskState) /\ sched_in_range sg after.(TskState) after.(SchedState).
Proof.
  intros sg s eid e tid old kind message result Htasks Hsched Hold Hphase; split.
  - eapply task_event_wake_single_preserves_in_range; eauto.
  - change (sched_in_range sg
      (glob_task_set_usedtask s.(TskState) tid (task_event_wake_single old kind message result))
      (sched_wake_by_status sg s.(TskState) s.(SchedState) tid
        (encode_task_status (task_event_wake_single old kind message result).(stat)))).
    rewrite sched_wake_by_status_eq_wake_task with
      (new := task_event_wake_single old kind message result).
    + eapply sched_wake_task_preserves_in_range;
        [exact Htasks|exact Hsched|exact Hold|reflexivity|].
      apply task_event_wake_single_keeps_ready_task_ready.
    + rewrite task_event_wake_single_ready_iff_not_suspended by exact Hphase.
      change (negb (task_is_suspended old.(stat)) =
        negb (task_is_suspended (task_clear_pending_status old.(stat) kind))).
      rewrite task_clear_pending_status_preserves_suspension; reflexivity.
Qed.

Lemma event_wake_preserves_event_in_range : forall sg s eid e tid old kind message result,
  event_in_range sg s.(TskState) s.(EventState) ->
  s.(EventState).(inUsedEventStates) eid = Some e -> In tid e.(waitList) ->
  let after := event_wake_state sg s eid e tid old kind message result in
  event_in_range sg after.(TskState) after.(EventState).
Proof. intros; eapply event_remove_waiter_update_task_preserves_in_range; eauto. Qed.

(** Shared endpoint of single-Event removal and a same-priority TCB update.
    Wake and TaskDelete have different status writes and ready effects, but
    share this unlink argument.  The premises describe the actual updated
    TCB; they are not extra runtime guards or a claim about intermediate
    stores.  Scheduler changes are handled by their own owner. *)
Lemma event_remove_waiter_update_task_preserves_cross_module_consistency :
  forall sg s eid e tid old new,
    cross_module_consistency sg s ->
    s.(EventState).(inUsedEventStates) eid = Some e -> In tid e.(waitList) ->
    s.(TskState).(inUsedTaskStates) tid = Some old ->
    new.(curPrio) = old.(curPrio) -> new.(eventPtr) = None ->
    new.(eventMultiWaitEvents) = [] -> new.(tcbFlagNode) = 0 ->
    task_non_suspension_bits new.(stat) <> task_pend_mask PendFlag ->
    cross_module_consistency sg
      (replace_EventS
        (update_event_field_raw s.(EventState) eid (event_set_wait_list e (remove_Z_eqb tid e.(waitList))))
        (replace_TskS (glob_task_set_usedtask s.(TskState) tid new) s)).
Proof.
  intros sg s eid e tid old new
    [Htable [Hsnapshot [Hwait [Hprotocol [Hunique [Hflag Htimer]]]]]]
    He Hin Hold Hprio Hnull Hmulti Hnewflag Hpending.
  pose proof (proj1 Hwait) as Hentries.
  destruct (event_waiter_task_fields sg s.(TskState) eid e tid (Hentries eid e He) Hin)
    as [found [actual [Hfound [Hactual [Hptr [Hentrymulti Hphase]]]]]].
  assert (found = old) by congruence; subst found.
  pose proof (proj1 (task_with_event_ptr_has_no_flag_registration
    sg s.(TskState) s.(FlagState) tid old eid Hflag Hold Hptr)) as Hflagnull.
  set (events := update_event_field_raw s.(EventState) eid
    (event_set_wait_list e (remove_Z_eqb tid e.(waitList)))).
  assert (Horigin : forall slot node, events.(inUsedEventStates) slot = Some node ->
    exists before, s.(EventState).(inUsedEventStates) slot = Some before /\
      node.(eventType) = before.(eventType) /\ node.(mutexFields) = before.(mutexFields) /\
      (forall member, In member node.(waitList) -> In member before.(waitList))).
  { intros slot node Hnode; unfold events in Hnode; simpl in Hnode.
    destruct (Z.eqb slot eid) eqn:E.
    - apply Z.eqb_eq in E; subst slot; injection Hnode as Hnode; subst node.
      exists e; split; [exact He|]; split; [reflexivity|]; split; [reflexivity|].
      intros member Hmember; eapply remove_Z_eqb_in; exact Hmember.
    - exists node; repeat split; auto. }
  assert (Hforward : forall slot before, s.(EventState).(inUsedEventStates) slot = Some before ->
    exists node, events.(inUsedEventStates) slot = Some node /\
      node.(eventType) = before.(eventType) /\ node.(mutexFields) = before.(mutexFields)).
  { intros slot before Hbefore; unfold events; simpl; destruct (Z.eqb slot eid) eqn:E.
    - apply Z.eqb_eq in E; subst slot; rewrite He in Hbefore; injection Hbefore as Hbefore; subst before.
      eexists; repeat split; reflexivity.
    - exists before; auto. }
  assert (Hclaims : forall p,
    (exists mid node m, events.(inUsedEventStates) mid = Some node /\
      node.(eventType) = OS_EVENT_TYPE_MUTEX /\ node.(mutexFields) = Some m /\
      mutex_reserves_priority_slot sg m p) <->
    (exists mid node m, s.(EventState).(inUsedEventStates) mid = Some node /\
      node.(eventType) = OS_EVENT_TYPE_MUTEX /\ node.(mutexFields) = Some m /\
      mutex_reserves_priority_slot sg m p)).
  { intro p; split; intros [mid [node [m [Hnode [Htype [Hm Hclaim]]]]]].
    - destruct (Horigin mid node Hnode) as [before [Hb [Ht [Hf _]]]].
      exists mid, before, m; split; [exact Hb|]; split; [congruence|]; split; [congruence|exact Hclaim].
    - destruct (Hforward mid node Hnode) as [after [Ha [Ht Hf]]].
      exists mid, after, m; split; [exact Ha|]; split; [congruence|]; split; [congruence|exact Hclaim]. }
  assert (HtableAfter : task_mutex_priotbl_consistency sg
    (glob_task_set_usedtask s.(TskState) tid new) events).
  { pose proof (task_mutex_priotbl_consistency_update_task sg s.(TskState) s.(EventState)
      tid old new Hold Hprio Htable)
      as [Hcreator [Hslots Halias]].
    split.
    - intros p entry Hentry Hclaim; apply (Hcreator p entry Hentry); apply Hclaims; exact Hclaim.
    - split.
      + intros p Hrange; specialize (Hslots p Hrange); simpl in Hslots |- *; destruct (s.(TskState).(prioTbl) p).
        * intro Hclaim; apply Hslots; apply Hclaims; exact Hclaim.
        * destruct Hslots as [Hreserved|[Hclaim|HpcpLease]].
          -- left; exact Hreserved.
          -- right; left; apply Hclaims; exact Hclaim.
          -- right; right; exact HpcpLease.
        * exact Hslots.
      + eapply mutex_priority_alias_consistency_ext; [reflexivity|reflexivity| |exact Halias].
        intros owner p [mid [node [m [Hnode [Htype [Hm Hclaim]]]]]].
        destruct (Hforward mid node Hnode) as [after [Ha [Ht Hf]]].
        exists mid, after, m; split; [exact Ha|]; split; [congruence|]; split; [congruence|exact Hclaim]. }
  unfold cross_module_consistency; split; [exact HtableAfter|]; split.
  - pose proof (mutex_owner_snapshot_update_task sg s.(TskState) s.(EventState)
      tid old new Hold Hsnapshot) as HsnapTask.
    intros mid node m owner Hnode Htype Hm Howner.
    destruct (Horigin mid node Hnode) as [before [Hb [Ht [Hf Hmembers]]]].
    destruct (HsnapTask mid before m owner Hb ltac:(congruence) ltac:(congruence) Howner)
      as [t [base [snapshot [Htcb [Hbase [Hsaved [Hrange [Hbound [Habsent HpcpBase]]]]]]]]].
    exists t, base, snapshot; split; [exact Htcb|]; split; [exact Hbase|];
      split; [exact Hsaved|]; split; [exact Hrange|]; split; [exact Hbound|].
    split; [|exact HpcpBase].
    intro Hmember; apply Habsent; apply Hmembers; exact Hmember.
  - split.
    + eapply event_wait_object_remove_update_task;
        [exact Hwait|exact He|exact Hin|exact Hnull|exact Hmulti].
    + split.
      * intros mid node m Hnode Htype Hm.
        destruct (Horigin mid node Hnode) as [before [Hb [Ht [Hf _]]]].
        exact (Hprotocol mid before m Hb ltac:(congruence) ltac:(congruence)).
      * split.
        -- intros mid1 node1 m1 mid2 node2 m2 Hn1 Ht1 Hm1 Hn2 Ht2 Hm2 Hp Hnonzero.
           destruct (Horigin mid1 node1 Hn1) as [before1 [Hb1 [Ht1' [Hm1' _]]]].
           destruct (Horigin mid2 node2 Hn2) as [before2 [Hb2 [Ht2' [Hm2' _]]]].
           eapply Hunique; [exact Hb1| | |exact Hb2| | |exact Hp|exact Hnonzero]; congruence.
        -- split; [|exact Htimer].
           eapply task_flag_waiter_consistency_update_unregistered_task;
             [exact Hold|exact Hflagnull|exact Hnewflag|exact Hpending|exact Hflag].
Qed.

Lemma event_wake_preserves_cross_module_consistency :
  forall sg s eid e tid old kind message result,
    cross_module_consistency sg s ->
    s.(EventState).(inUsedEventStates) eid = Some e -> In tid e.(waitList) ->
    s.(TskState).(inUsedTaskStates) tid = Some old ->
    event_type_to_pend_type e.(eventType) = Some kind ->
    cross_module_consistency sg (event_wake_state sg s eid e tid old kind message result).
Proof.
  intros sg s eid e tid old kind message result Hcross He Hin Hold Hkind.
  pose proof Hcross as [_ [_ [Hwait [_ [_ [Hflag _]]]]]].
  destruct (event_waiter_task_fields sg s.(TskState) eid e tid
    (proj1 Hwait eid e He) Hin)
    as [found [actual [Hfound [Hactual [Hptr [Hmulti Hphase]]]]]].
  assert (found = old) by congruence; subst found.
  assert (actual = kind) by congruence; subst actual.
  pose proof (proj1 (task_with_event_ptr_has_no_flag_registration
    sg s.(TskState) s.(FlagState) tid old eid Hflag Hold Hptr)) as Hflagnull.
  pose proof (proj2 (task_event_wake_single_clears_registration old kind message result Hphase)) as Hpending.
  pose proof (event_remove_waiter_update_task_preserves_cross_module_consistency
    sg s eid e tid old (task_event_wake_single old kind message result)
    Hcross He Hin Hold eq_refl eq_refl Hmulti Hflagnull
    ltac:(rewrite Hpending; discriminate)) as Hupdated.
  unfold event_wake_state, cross_module_consistency in *.
  cbn [replace_SchedS replace_EventS replace_TskS TskState EventState FlagState TimerState SchedState].
  destruct Hupdated as [Ht [Ho [Hw [Hp [Hu [Hf Htimer]]]]]].
  split; [exact Ht|]; split; [exact Ho|]; split; [exact Hw|]; split; [exact Hp|];
    split; [exact Hu|]; split; [exact Hf|].
  unfold timer_running_initialization_consistency in *.
  cbn [replace_SchedS replace_EventS replace_TskS TimerState SchedState].
  rewrite sched_wake_by_status_running_eq; exact Htimer.
Qed.

(** Model the actual EventGrp/EventTbl decoding and priority-table lookup
    used by OS_EventTaskRdy in the single-Event, eight-row profile.  None
    means that a live object/TCB lookup is outside this model's domain; it
    is not a C error return or an added runtime validation branch. *)
Definition event_task_rdy (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (eid : EventID) (kind : PendType) (message : addr) (result : PendStatus)
  : option (Z * UCOS2_Verify_State) :=
  match s.(EventState).(inUsedEventStates) eid with
  | None => None
  | Some e =>
      let priority := event_wait_priority s.(TskState) e in
      match s.(TskState).(prioTbl) priority with
      | PTTask tid =>
          match s.(TskState).(inUsedTaskStates) tid with
          | Some old => Some (priority, event_wake_state sg s eid e tid old kind message result)
          | None => None
          end
      | _ => None
      end
  end.

Lemma event_task_rdy_selects_waiter : forall sg s eid e head tail old kind message result,
  valid_stable_glob_vars sg -> task_in_range sg s.(TskState) ->
  event_wait_entry_consistency sg s.(TskState) eid e ->
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(waitList) = head :: tail ->
  s.(TskState).(inUsedTaskStates) head = Some old ->
  event_task_rdy sg s eid kind message result =
    Some (old.(curPrio), event_wake_state sg s eid e head old kind message result).
Proof.
  intros sg s eid e head tail old kind message result Hsg Htasks Hentry He Hlist Hold.
  destruct (event_wait_priority_table_entry sg s.(TskState) eid e head tail
    Hsg Htasks Hentry Hlist) as [found [Hfound [Hpriority Htable]]].
  assert (found = old) by congruence; subst found.
  unfold event_task_rdy; rewrite He, Htable, Hold, Hpriority; reflexivity.
Qed.

Lemma event_task_rdy_preserves_invariants : forall sg s eid e head tail kind message result,
  valid_stable_glob_vars sg -> task_in_range sg s.(TskState) ->
  sched_in_range sg s.(TskState) s.(SchedState) ->
  event_in_range sg s.(TskState) s.(EventState) -> cross_module_consistency sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(waitList) = head :: tail ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  exists old after, s.(TskState).(inUsedTaskStates) head = Some old /\
    event_task_rdy sg s eid kind message result = Some (old.(curPrio), after) /\
    task_in_range sg after.(TskState) /\
    sched_in_range sg after.(TskState) after.(SchedState) /\
    event_in_range sg after.(TskState) after.(EventState) /\
    cross_module_consistency sg after.
Proof.
  intros sg s eid e head tail kind message result Hsg Htasks Hsched Hevents Hcross He Hlist Hkind.
  pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  pose proof (Hentries eid e He) as Hentry.
  assert (Hin : In head e.(waitList)) by (rewrite Hlist; left; reflexivity).
  destruct (event_waiter_task_fields sg s.(TskState) eid e head Hentry Hin)
    as [old [actual [Hold [Hactual [Hptr [Hmulti Hphase]]]]]].
  assert (actual = kind) by congruence; subst actual.
  set (after := event_wake_state sg s eid e head old kind message result).
  destruct (event_wake_preserves_task_sched sg s eid e head old kind message result
    Htasks Hsched Hold Hphase) as [HtasksAfter HschedAfter].
  exists old, after; split; [exact Hold|]; split.
  - eapply event_task_rdy_selects_waiter; eauto.
  - split; [exact HtasksAfter|]; split; [exact HschedAfter|]; split.
    + eapply event_wake_preserves_event_in_range; eauto.
    + eapply event_wake_preserves_cross_module_consistency; eauto.
Qed.

(** Endpoint builder for OS_EventTaskWait after observing its TCB.  Only
    EventPtr, the Event bitmap and ready membership are changed.  Neither
    the caller's Stat/StatPend/Dly writes nor scheduler cache refreshes
    belong to this helper. *)
Definition event_wait_state (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState) (tid : TaskID) (old : TaskAbstractState)
  : UCOS2_Verify_State :=
  let tasks := glob_task_set_usedtask s.(TskState) tid (task_set_event_ptr old (Some eid)) in
  replace_SchedS (sched_remove_ready_task s.(SchedState) tid)
    (replace_EventS (update_event_field_raw s.(EventState) eid (event_insert_waiter sg tasks e tid))
      (replace_TskS tasks s)).

(** Fused endpoint of the Pend caller's three TCB stores followed by the
    helper.  Its supplied TCB observation includes those earlier stores;
    it is not the helper's entry contract.  All physical scheduling caches
    remain unchanged until OS_Sched performs its own writes. *)
Definition event_pend_state (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState) (tid : TaskID) (old : TaskAbstractState)
  (kind : PendType) (timeout : Z) : UCOS2_Verify_State :=
  event_wait_state sg s eid e tid (task_prepare_event_wait old kind timeout).

Lemma event_pend_state_source_order : forall sg s eid e tid old kind timeout,
  event_pend_state sg s eid e tid old kind timeout =
    event_wait_state sg
      (replace_TskS (glob_task_set_usedtask s.(TskState) tid (task_prepare_event_wait old kind timeout)) s)
      eid e tid (task_prepare_event_wait old kind timeout).
Proof.
  intros.
  assert (Hlast : forall tasks first last,
    glob_task_set_usedtask (glob_task_set_usedtask tasks tid first) tid last =
      glob_task_set_usedtask tasks tid last).
  { intros; unfold glob_task_set_usedtask; simpl; f_equal.
    apply functional_extensionality; intro slot; destruct (Z.eqb slot tid); reflexivity. }
  unfold event_pend_state, event_wait_state; cbn zeta.
  rewrite replace_TskS_TskState, replace_TskS_other_Sched, replace_TskS_other_Event.
  rewrite Hlast, replace_TskS_last_write; reflexivity.
Qed.

Lemma event_pend_preserves_task_sched : forall sg s eid e tid old kind timeout,
  task_in_range sg s.(TskState) -> sched_in_range sg s.(TskState) s.(SchedState) ->
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  let after := event_pend_state sg s eid e tid old kind timeout in
  task_in_range sg after.(TskState) /\ sched_in_range sg after.(TskState) after.(SchedState).
Proof.
  intros sg s eid e tid old kind timeout Htasks Hsched Hold; split.
  - eapply task_update_preserves_in_range; eauto; reflexivity.
  - eapply sched_remove_ready_task_preserves_in_range;
      [exact Hsched|exact Hold|reflexivity|].
    apply task_prepare_event_wait_not_ready.
Qed.

Lemma event_pend_preserves_event_in_range : forall sg s eid e tid old kind timeout,
  task_in_range sg s.(TskState) -> event_in_range sg s.(TskState) s.(EventState) ->
  s.(EventState).(inUsedEventStates) eid = Some e ->
  s.(TskState).(inUsedTaskStates) tid = Some old -> valid_task_prio sg old.(curPrio) ->
  old.(eventPtr) = None -> old.(eventMultiWaitEvents) = [] ->
  task_non_suspension_bits old.(stat) = 0 ->
  event_type_to_pend_type e.(eventType) = Some kind -> event_wait_resource_unavailable e ->
  let after := event_pend_state sg s eid e tid old kind timeout in
  event_in_range sg after.(TskState) after.(EventState).
Proof.
  intros sg s eid e tid old kind timeout Htasks Hevents He Hold Hprio Hnull Hmulti Hnone Hkind Hunavailable.
  assert (Hupdated : task_in_range sg
    (glob_task_set_usedtask s.(TskState) tid
      (task_set_event_ptr (task_prepare_event_wait old kind timeout) (Some eid)))).
  { eapply task_update_preserves_in_range; eauto; reflexivity. }
  destruct Hupdated as [_ [_ [_ [_ [_ [_ [Hunique _]]]]]]].
  eapply event_insert_waiter_update_task_preserves_in_range;
    [exact Hevents|exact He|exact Hold|exact Hnull|exact Hunique|exact Hprio|
     reflexivity|exact Hmulti| |exact Hkind|exact Hunavailable].
  left; apply task_prepare_event_wait_pending_bits; exact Hnone.
Qed.

Lemma event_pend_preserves_cross_module_consistency : forall sg s eid e tid old kind timeout,
  cross_module_consistency sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  s.(TskState).(inUsedTaskStates) tid = Some old -> valid_task_prio sg old.(curPrio) ->
  old.(eventPtr) = None -> old.(eventMultiWaitEvents) = [] -> old.(tcbFlagNode) = 0 ->
  task_non_suspension_bits old.(stat) = 0 ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  (forall m, e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) <> Some tid) ->
  cross_module_consistency sg (event_pend_state sg s eid e tid old kind timeout).
Proof.
  intros sg s eid e tid old kind timeout
    [Htable [Hsnapshot [Hwait [Hprotocol [Hunique [Hflag Htimer]]]]]]
    He Hold Hprio Hnull Hmulti Hflagnull Hnone Hkind Hnotowner.
  set (new := task_set_event_ptr (task_prepare_event_wait old kind timeout) (Some eid)).
  set (tasks := glob_task_set_usedtask s.(TskState) tid new).
  set (events := update_event_field_raw s.(EventState) eid (event_insert_waiter sg tasks e tid)).
  assert (Horigin : forall slot node, events.(inUsedEventStates) slot = Some node ->
    exists before, s.(EventState).(inUsedEventStates) slot = Some before /\
      node.(eventType) = before.(eventType) /\ node.(mutexFields) = before.(mutexFields)).
  { intros slot node Hnode; unfold events in Hnode; simpl in Hnode; destruct (Z.eqb slot eid) eqn:E.
    - apply Z.eqb_eq in E; subst slot; injection Hnode as Hnode; subst node.
      exists e; split; [exact He|]; split; reflexivity.
    - exists node; auto. }
  assert (Hforward : forall slot before, s.(EventState).(inUsedEventStates) slot = Some before ->
    exists node, events.(inUsedEventStates) slot = Some node /\
      node.(eventType) = before.(eventType) /\ node.(mutexFields) = before.(mutexFields)).
  { intros slot before Hbefore; unfold events; simpl; destruct (Z.eqb slot eid) eqn:E.
    - apply Z.eqb_eq in E; subst slot; rewrite He in Hbefore; injection Hbefore as Hbefore; subst before.
      eexists; repeat split; reflexivity.
    - exists before; auto. }
  assert (Hclaims : forall p,
    (exists mid node m, events.(inUsedEventStates) mid = Some node /\
      node.(eventType) = OS_EVENT_TYPE_MUTEX /\ node.(mutexFields) = Some m /\
      mutex_reserves_priority_slot sg m p) <->
    (exists mid node m, s.(EventState).(inUsedEventStates) mid = Some node /\
      node.(eventType) = OS_EVENT_TYPE_MUTEX /\ node.(mutexFields) = Some m /\
      mutex_reserves_priority_slot sg m p)).
  { intro p; split; intros [mid [node [m [Hnode [Htype [Hm Hclaim]]]]]].
    - destruct (Horigin mid node Hnode) as [before [Hb [Ht Hf]]].
      exists mid, before, m; split; [exact Hb|]; split; [congruence|]; split; [congruence|exact Hclaim].
    - destruct (Hforward mid node Hnode) as [after [Ha [Ht Hf]]].
      exists mid, after, m; split; [exact Ha|]; split; [congruence|]; split; [congruence|exact Hclaim]. }
  pose proof (task_mutex_priotbl_consistency_update_task sg s.(TskState) s.(EventState)
    tid old new Hold eq_refl Htable) as HtableTask.
  assert (Hpriority : task_priority_unique tasks).
  { destruct HtableTask as [_ [_ Halias]].
    eapply mutex_priority_alias_consistency_priority_unique; exact Halias. }
  assert (HtableAfter : task_mutex_priotbl_consistency sg tasks events).
  { destruct HtableTask as [Hcreator [Hslots Halias]].
    split.
    - intros p entry Hentry Hclaim; apply (Hcreator p entry Hentry); apply Hclaims; exact Hclaim.
    - split.
      + intros p Hrange; specialize (Hslots p Hrange); simpl in Hslots |- *; destruct (s.(TskState).(prioTbl) p).
        * intro Hclaim; apply Hslots; apply Hclaims; exact Hclaim.
        * destruct Hslots as [Hreserved|[Hclaim|HpcpLease]].
          -- left; exact Hreserved.
          -- right; left; apply Hclaims; exact Hclaim.
          -- right; right; exact HpcpLease.
        * exact Hslots.
      + eapply mutex_priority_alias_consistency_ext; [reflexivity|reflexivity| |exact Halias].
        intros owner p [mid [node [m [Hnode [Htype [Hm Hclaim]]]]]].
        destruct (Hforward mid node Hnode) as [after [Ha [Ht Hf]]].
        exists mid, after, m; split; [exact Ha|]; split; [congruence|]; split; [congruence|exact Hclaim]. }
  unfold cross_module_consistency; split; [exact HtableAfter|]; split.
  - pose proof (mutex_owner_snapshot_update_task sg s.(TskState) s.(EventState)
      tid old new Hold Hsnapshot) as HsnapTask.
    intros mid node m owner Hnode Htype Hm Howner; simpl in Hnode.
    destruct (Z.eqb mid eid) eqn:Eevent.
    + apply Z.eqb_eq in Eevent; subst mid; injection Hnode as Hnode; subst node.
      destruct (HsnapTask eid e m owner He Htype Hm Howner)
        as [t [base [snapshot [Htcb [Hbase [Hsaved [Hrange [Hbound [Habsent HpcpBase]]]]]]]]].
      exists t, base, snapshot; split; [exact Htcb|]; split; [exact Hbase|];
        split; [exact Hsaved|]; split; [exact Hrange|]; split; [exact Hbound|].
      split; [|exact HpcpBase].
      intro Hmember; apply event_insert_waiter_membership in Hmember; destruct Hmember as [Hsame|Hmember].
      * subst owner; exact (Hnotowner m Htype Hm Howner).
      * exact (Habsent Hmember).
    + exact (HsnapTask mid node m owner Hnode Htype Hm Howner).
  - split.
    + eapply event_wait_object_insert_update_task;
        [exact Hwait|exact He|exact Hold|exact Hnull|exact Hpriority|exact Hprio|
         reflexivity|exact Hmulti| |exact Hkind].
      left; apply task_prepare_event_wait_pending_bits; exact Hnone.
    + split.
      * intros mid node m Hnode Htype Hm.
        destruct (Horigin mid node Hnode) as [before [Hb [Ht Hf]]].
        exact (Hprotocol mid before m Hb ltac:(congruence) ltac:(congruence)).
      * split.
        -- intros mid1 node1 m1 mid2 node2 m2 Hn1 Ht1 Hm1 Hn2 Ht2 Hm2 Hp Hnonzero.
           destruct (Horigin mid1 node1 Hn1) as [before1 [Hb1 [Ht1' Hm1']]].
           destruct (Horigin mid2 node2 Hn2) as [before2 [Hb2 [Ht2' Hm2']]].
           eapply Hunique; [exact Hb1| | |exact Hb2| | |exact Hp|exact Hnonzero]; congruence.
        -- split; [|exact Htimer].
           eapply task_flag_waiter_consistency_update_unregistered_task;
             [exact Hold|exact Hflagnull|exact Hflagnull| |exact Hflag].
           change (task_non_suspension_bits (task_prepare_event_wait old kind timeout).(stat) <>
             task_pend_mask PendFlag).
           rewrite task_prepare_event_wait_pending_bits by exact Hnone.
           intro Hbad; destruct e.(eventType); inversion Hkind; subst kind; discriminate.
Qed.

Lemma cross_module_consistency_sched_frame : forall sg s sched',
  sched'.(isRunning) = s.(SchedState).(isRunning) ->
  cross_module_consistency sg s ->
  cross_module_consistency sg (replace_SchedS sched' s).
Proof.
  intros sg s sched' Hrunning Hcross.
  unfold cross_module_consistency, timer_running_initialization_consistency in *.
  cbn [replace_SchedS TskState EventState FlagState TimerState SchedState].
  rewrite Hrunning; exact Hcross.
Qed.

Lemma task_status_update_preserves_cross_module_consistency : forall sg s tid old status,
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  task_non_suspension_bits status = task_non_suspension_bits old.(stat) ->
  cross_module_consistency sg s ->
  cross_module_consistency sg
    (replace_TskS (glob_task_set_usedtask s.(TskState) tid (task_set_status old status)) s).
Proof.
  intros sg s tid old status Hold Hbits
    [Htable [Hsnapshot [Hwait [Hprotocol [Hunique [Hflag Htimer]]]]]].
  split.
  - eapply task_mutex_priotbl_consistency_update_task; [exact Hold|reflexivity|exact Htable].
  - split; [eapply mutex_owner_snapshot_update_task; eauto|].
    split; [eapply event_wait_object_update_status; eauto|].
    split; [exact Hprotocol|]; split; [exact Hunique|]; split; [|exact Htimer].
    eapply task_flag_waiter_consistency_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|reflexivity| | |exact Hflag].
    + intro Hphase; unfold task_linked_wait_phase; cbn [task_set_status stat statPend dly].
      rewrite Hbits; exact Hphase.
    + cbn [task_set_status stat]; rewrite Hbits; auto.
Qed.

(** Task/Scheduler endpoints live with the cross-owner semantics so both
    global reconstruction and atomic API relations use the same updates. *)
Definition task_suspend_state (entry : UCOS2_Verify_State)
  (tid : TaskID) (t : TaskAbstractState) : UCOS2_Verify_State :=
  replace_TskS (glob_task_set_usedtask entry.(TskState) tid (task_suspend t))
    (replace_SchedS (sched_remove_ready_task entry.(SchedState) tid) entry).

Definition task_resume_state (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (tid : TaskID) (t : TaskAbstractState) : UCOS2_Verify_State :=
  replace_SchedS (sched_resume_task sg entry.(TskState) entry.(SchedState) tid t)
    (replace_TskS (glob_task_set_usedtask entry.(TskState) tid (task_resume t)) entry).

Lemma tick_task_update_preserves_cross_module_consistency : forall sg s tid t,
  s.(TskState).(inUsedTaskStates) tid = Some t -> cross_module_consistency sg s ->
  cross_module_consistency sg
    (replace_TskS (glob_task_set_usedtask s.(TskState) tid (tick_task_update t)) s).
Proof.
  intros sg s tid t Ht [Htable [Hsnapshot [Hwait [Hprotocol [Hunique [Hflag Htimer]]]]]].
  pose proof (tick_task_preserves_non_timeout_fields t) as Hframe.
  cbv zeta in Hframe.
  assert (Hfields :
    (tick_task_update t).(taskID) = t.(taskID) /\
    (tick_task_update t).(taskGeneration) = t.(taskGeneration) /\
    (tick_task_update t).(curPrio) = t.(curPrio) /\
    (tick_task_update t).(eventPtr) = t.(eventPtr) /\
    (tick_task_update t).(eventMultiWaitEvents) = t.(eventMultiWaitEvents))
    by (clear - Hframe; tauto).
  destruct Hfields as [Hid [Hgen [Hprio [Hptr Hmulti]]]].
  split; [eapply task_mutex_priotbl_consistency_update_task; eassumption|].
  split; [eapply mutex_owner_snapshot_update_task; eassumption|].
  split.
  - eapply event_wait_object_update_task;
      [exact Ht|exact Hprio|exact Hptr|exact Hmulti| |exact Hwait].
    apply tick_preserves_linked_phase.
  - split; [exact Hprotocol|]; split; [exact Hunique|]; split; [|exact Htimer].
    apply tick_task_preserves_flag_waiter_consistency; assumption.
Qed.

Lemma tick_task_step_preserves_cross_module_consistency : forall sg s tid t,
  s.(TskState).(inUsedTaskStates) tid = Some t -> cross_module_consistency sg s ->
  cross_module_consistency sg (tick_task_step sg tid t s).
Proof.
  intros sg s tid t Ht Hcross.
  pose proof (tick_task_update_preserves_cross_module_consistency sg s tid t Ht Hcross) as Hupdated.
  unfold tick_task_step; destruct (Z.eqb t.(dly) 0); [exact Hcross|].
  destruct (Z.eqb (tick_task_update t).(dly) 0); [|exact Hupdated].
  change (cross_module_consistency sg
    (replace_SchedS (sched_wake_by_status sg s.(TskState) s.(SchedState)
      tid (encode_task_status (tick_task_update t).(stat)))
      (replace_TskS (glob_task_set_usedtask s.(TskState) tid (tick_task_update t)) s))).
  apply cross_module_consistency_sched_frame; [|exact Hupdated].
  unfold sched_wake_by_status; destruct task_status_is_suspended; reflexivity.
Qed.

Lemma tick_task_step_preserves_event_in_range : forall sg s tid t,
  s.(TskState).(inUsedTaskStates) tid = Some t ->
  event_in_range sg s.(TskState) s.(EventState) ->
  event_in_range sg (tick_task_step sg tid t s).(TskState)
    (tick_task_step sg tid t s).(EventState).
Proof.
  intros sg s tid t Ht Hevents.
  pose proof (f_equal EventState (tick_task_step_non_task_sched_state_eq sg tid t s)) as Heq.
  cbn [replace_TskS replace_SchedS EventState] in Heq.
  rewrite tick_task_step_task_state_eq by exact Ht; rewrite Heq.
  pose proof (tick_task_preserves_non_timeout_fields t) as Hframe.
  cbv zeta in Hframe.
  eapply event_update_task_preserves_in_range;
    [exact Ht| | | | |exact Hevents]; try (clear - Hframe; tauto).
  apply tick_preserves_linked_phase.
Qed.

(** Tick leaves Event bytes untouched, including the bits of timeout-linked
    waiters.  Reindexing their representation uses preserved priorities,
    not equality of all TCB fields and not an assumption that timeout
    already removed the registration. *)
Lemma tick_task_step_event_rep_eq : forall sg s tid t,
  s.(TskState).(inUsedTaskStates) tid = Some t ->
  event_raw_rep sg s.(TskState) s.(EventState) =
  event_raw_rep sg (tick_task_step sg tid t s).(TskState)
    (tick_task_step sg tid t s).(EventState).
Proof.
  intros sg s tid t Ht.
  pose proof (f_equal EventState (tick_task_step_non_task_sched_state_eq sg tid t s)) as Heq.
  cbn [replace_TskS replace_SchedS EventState] in Heq.
  rewrite tick_task_step_task_state_eq by exact Ht; rewrite Heq.
  apply event_raw_rep_change_task_index, event_wait_priority_agreement_encodes.
  intros eid e slot He Hin; symmetry; eapply glob_task_set_usedtask_observation; [exact Ht|].
  unfold tick_task_update; destruct (Z.eqb t.(dly) 0); reflexivity.
Qed.

Lemma task_recycle_preserves_event_wait_entry : forall sg tasks tid priority node name eid e,
  ~ In tid e.(waitList) -> event_wait_entry_consistency sg tasks eid e ->
  event_wait_entry_consistency sg (task_recycle sg tasks tid priority node name) eid e.
Proof.
  intros sg tasks tid priority node name eid e Habsent Hentry.
  eapply event_wait_entry_preserved_by_link_updates; [|exact Hentry].
  intros slot old Hin Hold; apply task_unlink_used_map_preserves_other_fields;
    [intro E; subst slot; contradiction|exact Hold].
Qed.

Lemma task_recycle_preserves_event_in_range : forall sg tasks events tid priority node name,
  (forall eid e, events.(inUsedEventStates) eid = Some e -> ~ In tid e.(waitList)) ->
  event_in_range sg tasks events ->
  event_in_range sg (task_recycle sg tasks tid priority node name) events.
Proof.
  intros sg tasks events tid priority node name Habsent
    [Hpool [Hfree [Hidentity [Hfields [Hpayload [Hqueue Hentries]]]]]].
  split; [exact Hpool|]. split; [exact Hfree|]. split; [exact Hidentity|].
  split; [exact Hfields|]. split; [exact Hpayload|]. split; [exact Hqueue|].
  intros eid e He; apply task_recycle_preserves_event_wait_entry;
    [eapply Habsent|eapply Hentries]; exact He.
Qed.

Lemma task_recycle_preserves_event_priority_agreement : forall sg tasks events tid priority node name,
  (forall eid e, events.(inUsedEventStates) eid = Some e -> ~ In tid e.(waitList)) ->
  event_wait_priority_agreement tasks (task_recycle sg tasks tid priority node name) events.
Proof.
  intros sg tasks events tid priority node name Habsent eid e slot He Hin.
  symmetry; pose proof (task_unlink_used_map_observation Z curPrio
    tasks.(inUsedTaskStates) tid node slot (fun _ _ _ => eq_refl)) as Hobs.
  destruct (Z.eq_dec slot tid) as [->|Hne]; [exfalso; exact (Habsent eid e He Hin)|exact Hobs].
Qed.

(** The source clears one selected table cell, not every possible alias.
    No-held-mutex is therefore a caller/protocol obligation, never an
    invented OSTaskDel branch.  Event/Flag cleanup must already have
    produced the supplied post-callee TCB.  This theorem only covers the
    actual unlink/recycle suffix; it does not prove the preceding Restore
    window, hook effects or the stopping of a self-deleting invocation. *)
Lemma task_recycle_preserves_cross_module_consistency : forall sg s tid priority node name,
  cross_module_consistency sg s -> s.(TskState).(inUsedTaskStates) tid = Some node ->
  task_priority_in_range sg priority -> s.(TskState).(prioTbl) priority = PTTask tid ->
  node.(eventPtr) = None -> node.(tcbFlagNode) = 0 ->
  (forall mid e m, s.(EventState).(inUsedEventStates) mid = Some e ->
     e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) <> Some tid) ->
  cross_module_consistency sg
    (replace_TskS (task_recycle sg s.(TskState) tid priority node name) s).
Proof.
  intros sg s tid priority node name
    [Htable [Howners [Hwait [Hprotocol [Hunique [Hflag Htimer]]]]]]
    Hnode Hrange Hselected Heventnull Hflagnull Hnotowner.
  pose proof Htable as [Hcreator [Hslots Halias]].
  pose proof Hwait as [Hentries [Hback Hclosed]].
  set (tasks := task_recycle sg s.(TskState) tid priority node name).
  assert (Horigin : forall slot after, tasks.(inUsedTaskStates) slot = Some after ->
    slot <> tid /\ exists before, s.(TskState).(inUsedTaskStates) slot = Some before /\
      task_set_links after None None = task_set_links before None None).
  { intros slot after Hafter; eapply task_unlink_used_map_lookup_origin; exact Hafter. }
  assert (Htransport : forall slot before, slot <> tid ->
    s.(TskState).(inUsedTaskStates) slot = Some before -> exists after,
      tasks.(inUsedTaskStates) slot = Some after /\
      task_set_links after None None = task_set_links before None None).
  { intros; apply task_unlink_used_map_preserves_other_fields; assumption. }
  assert (Haliases : forall slot, slot <> tid -> forall p,
    task_priority_alias sg s.(TskState).(prioTbl) slot p <-> task_priority_alias sg tasks.(prioTbl) slot p).
  { intros slot Hne p; symmetry; apply task_priority_alias_foreign_write_iff; congruence. }
  assert (Honly : forall p, task_priority_in_range sg p -> s.(TskState).(prioTbl) p = PTTask tid -> p = priority).
  { intros p Hp Hget.
    pose proof (mutex_unowned_task_alias_eq_current sg s.(TskState) s.(EventState) tid node p
      Halias Hnode Hnotowner (conj Hp Hget)).
    pose proof (mutex_unowned_task_alias_eq_current sg s.(TskState) s.(EventState) tid node priority
      Halias Hnode Hnotowner (conj Hrange Hselected)); congruence. }
  assert (Hpcp : forall mid e m, s.(EventState).(inUsedEventStates) mid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m ->
    m.(mfPCP) <> sg.(osPrioMutexCeilDis) -> m.(mfPCP) <> priority).
  { intros mid e m He Htype Hm Henabled E.
    destruct (Hprotocol mid e m He Htype Hm) as [_ [_ [Hdisabled|[_ [Hreserved|Howner]]]]];
      [contradiction|rewrite E, Hselected in Hreserved; discriminate|].
    destruct Howner as [owner [Howner Hslot]]; rewrite E, Hselected in Hslot.
    injection Hslot as Hslot; subst owner; exact (Hnotowner mid e m He Htype Hm Howner). }
  assert (Habsent : forall eid e, s.(EventState).(inUsedEventStates) eid = Some e -> ~ In tid e.(waitList)).
  { intros eid e He Hin.
    destruct (event_waiter_task_fields sg s.(TskState) eid e tid (Hentries eid e He) Hin)
      as [old [kind [Hold [_ [Href _]]]]].
    assert (old = node) by congruence; subst old; congruence. }
  assert (HtableAfter : task_mutex_priotbl_consistency sg tasks s.(EventState)).
  { split; [exact Hcreator|]. split.
    - intros p Hp; unfold tasks; cbn [task_recycle prioTbl].
      destruct (Z.eq_dec p priority) as [->|Hne].
      + intros [mid [e [m [He [Htype [Hm [Henabled E]]]]]]].
        exact (Hpcp mid e m He Htype Hm Henabled E).
      + specialize (Hslots p Hp); destruct (s.(TskState).(prioTbl) p) as [| |slot] eqn:Hslot;
          [exact Hslots|exact Hslots|].
        destruct Hslots as [old Hold].
        assert (Hother : slot <> tid) by (intro E; subst slot; apply Hne; eapply Honly; eassumption).
        destruct (Htransport slot old Hother Hold) as [after [Hafter _]]; exists after; exact Hafter.
    - intros slot after Hafter; destruct (Horigin slot after Hafter) as [Hne [before [Hbefore Hfields]]].
      pose proof (f_equal curPrio Hfields) as Hprio; simpl in Hprio.
      destruct (Halias slot before Hbefore) as [base [Hbase [Heffective Hclaims]]].
      exists base; split; [eapply task_base_priority_alias_ext; [apply Haliases; exact Hne|exact Hbase]|].
      split.
      + rewrite Hprio; eapply task_effective_priority_alias_ext; [apply Haliases; exact Hne|exact Heffective].
      + intros p Hp; apply Hclaims; apply (Haliases slot Hne p); exact Hp. }
  split; [exact HtableAfter|]. split.
  - intros mid e m owner He Htype Hm Howner.
    assert (Hother : owner <> tid) by (intro E; subst owner; exact (Hnotowner mid e m He Htype Hm Howner)).
    destruct (Howners mid e m owner He Htype Hm Howner)
      as [old [base [snapshot [Hold [Hbase Hrest]]]]].
    destruct (Htransport owner old Hother Hold) as [after [Hafter _]].
    exists after, base, snapshot; split; [exact Hafter|]. split; [|exact Hrest].
    eapply task_base_priority_alias_ext; [apply Haliases; exact Hother|exact Hbase].
  - split.
    + assert (Hrefs : forall slot after, tasks.(inUsedTaskStates) slot = Some after ->
        exists before, s.(TskState).(inUsedTaskStates) slot = Some before /\
          after.(eventPtr) = before.(eventPtr) /\ after.(eventMultiWaitEvents) = before.(eventMultiWaitEvents)).
      { intros slot after Hafter; destruct (Horigin slot after Hafter) as [_ [before [Hbefore Hfields]]].
        exists before; split; [exact Hbefore|].
        exact (conj (f_equal eventPtr Hfields) (f_equal eventMultiWaitEvents Hfields)). }
      split.
      * intros eid e He; apply task_recycle_preserves_event_wait_entry;
          [eapply Habsent|eapply Hentries]; exact He.
      * split.
        -- intros slot after eid e Hafter He Href.
           destruct (Hrefs slot after Hafter) as [before [Hbefore [HptrEq HmultiEq]]].
           eapply Hback; [exact Hbefore|exact He|rewrite <- HptrEq, <- HmultiEq; exact Href].
        -- intros slot after Hafter.
           destruct (Hrefs slot after Hafter) as [before [Hbefore [HptrEq HmultiEq]]].
           destruct (Hclosed slot before Hbefore) as [HsingleClosed HmultiClosed].
           rewrite HptrEq, HmultiEq; exact (conj HsingleClosed HmultiClosed).
    + split.
      * intros mid e m He Htype Hm.
        destruct (Hprotocol mid e m He Htype Hm) as [Hvalid [Howner Hslot]].
        split; [exact Hvalid|]. split; [exact Howner|].
        destruct Hslot as [Hdisabled|[Henabled Hslot]]; [left; exact Hdisabled|].
        right; split; [exact Henabled|].
        unfold tasks; cbn [replace_TskS TskState task_recycle prioTbl].
        destruct (Z.eq_dec m.(mfPCP) priority); [exfalso; eapply Hpcp; eassumption|exact Hslot].
      * split; [exact Hunique|]. split; [|exact Htimer].
        pose proof Hflag as [Hnodes HtaskFlags]; split.
        -- intros p w Hw.
           assert (Hother : w.(flagTask) <> tid).
           { intro E; apply (task_flag_null_pointer_has_no_waiter
               sg s.(TskState) s.(FlagState) tid node Hflag Hnode Hflagnull).
             exists p, w; auto. }
           destruct (Hnodes p w Hw) as [Hp [old [Hold [Hg [Hptr [Haddr [Hphase [Hevent Hmulti]]]]]]]].
           destruct (Htransport w.(flagTask) old Hother Hold) as [after [Hafter Hfields]].
           pose proof (f_equal taskGeneration Hfields) as Hgen; simpl in Hgen.
           pose proof (f_equal tcbFlagNode Hfields) as HflagNode; simpl in HflagNode.
           pose proof (f_equal stat Hfields) as Hstat; simpl in Hstat.
           pose proof (f_equal statPend Hfields) as Hpend; simpl in Hpend.
           pose proof (f_equal dly Hfields) as Hdly; simpl in Hdly.
           pose proof (f_equal eventPtr Hfields) as HeventEq; simpl in HeventEq.
           pose proof (f_equal eventMultiWaitEvents Hfields) as HmultiEq; simpl in HmultiEq.
           split; [exact Hp|]. exists after; split; [exact Hafter|].
           split; [congruence|]. split; [rewrite HflagNode; exact Hptr|]. split; [exact Haddr|].
           split; [unfold task_linked_wait_phase in *; rewrite Hstat, Hpend, Hdly; exact Hphase|].
           split; congruence.
        -- intros slot after Hafter Hactive.
           destruct (Horigin slot after Hafter) as [_ [before [Hbefore Hfields]]].
           pose proof (f_equal tcbFlagNode Hfields) as HflagNode; simpl in HflagNode.
           pose proof (f_equal stat Hfields) as Hstat; simpl in Hstat.
           rewrite HflagNode, Hstat in Hactive.
           destruct (HtaskFlags slot before Hbefore Hactive) as [w [Hw Htid]].
           exists w; rewrite HflagNode; auto.
Qed.

Lemma task_recycle_owned_mutex_invalidates_snapshot : forall sg tasks events tid priority node name mid e m,
  events.(inUsedEventStates) mid = Some e -> e.(eventType) = OS_EVENT_TYPE_MUTEX ->
  e.(mutexFields) = Some m -> m.(mfOwner) = Some tid ->
  ~ mutex_owner_snapshot_in_range sg (task_recycle sg tasks tid priority node name) events.
Proof.
  intros sg tasks events tid priority node name mid e m He Htype Hm Howner Hsnapshot.
  destruct (Hsnapshot mid e m tid He Htype Hm Howner) as [old [_ [_ [Hold _]]]].
  rewrite (proj1 (task_recycle_slot_fields sg tasks tid priority node name)) in Hold; discriminate.
Qed.

(** Exact single OS_EventTaskRemove endpoint.  The bitmap stores precede
    the EventPtr clear; status, delay, message and ready bits are unchanged. *)
Definition event_task_remove_state (s : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState) (tid : TaskID) (old : TaskAbstractState)
  : UCOS2_Verify_State :=
  replace_EventS
    (update_event_field_raw s.(EventState) eid (event_set_wait_list e (remove_Z_eqb tid e.(waitList))))
    (replace_TskS (glob_task_set_usedtask s.(TskState) tid (task_set_event_ptr old None)) s).

Lemma event_task_remove_preserves_cross_module_consistency : forall sg s eid e tid old,
  cross_module_consistency sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> In tid e.(waitList) ->
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  cross_module_consistency sg (event_task_remove_state s eid e tid old).
Proof.
  intros sg s eid e tid old Hcross He Hin Hold.
  pose proof Hcross as [_ [_ [Hwait [_ [_ [Hflag _]]]]]].
  destruct (event_waiter_task_fields sg s.(TskState) eid e tid
    (proj1 Hwait eid e He) Hin) as [found [kind [Hfound [_ [Hptr [Hmulti _]]]]]].
  assert (found = old) by congruence; subst found.
  destruct (task_with_event_ptr_has_no_flag_registration sg s.(TskState) s.(FlagState)
    tid old eid Hflag Hold Hptr) as [Hflagnull Hpending].
  exact (event_remove_waiter_update_task_preserves_cross_module_consistency
    sg s eid e tid old (task_set_event_ptr old None)
    Hcross He Hin Hold eq_refl eq_refl Hmulti Hflagnull Hpending).
Qed.

(** A retained single-Event pointer, together with the existing backlink
    and reference-closure invariant, identifies a live registered Event.
    Timeout callers use this fact before Remove; successful/aborted
    callers do not need to assume that the old Event is still allocated. *)
Lemma task_event_reference_has_waiter : forall sg s tid old eid,
  cross_module_consistency sg s ->
  s.(TskState).(inUsedTaskStates) tid = Some old -> old.(eventPtr) = Some eid ->
  exists e, s.(EventState).(inUsedEventStates) eid = Some e /\ In tid e.(waitList).
Proof.
  intros sg s tid old eid [_ [_ [Hwait _]]] Hold Hptr.
  destruct Hwait as [Hentries [Hback Hclosed]].
  destruct (proj1 (Hclosed tid old Hold) eid Hptr) as [e He].
  exists e; split; [exact He|]; eapply Hback; [exact Hold|exact He|left; exact Hptr].
Qed.

(** Single-Event Pend cleanup after its wait registration has been removed.
    This writes only TCB fields; it neither schedules nor performs the
    timeout caller's preceding EventTaskRemove.  Sem preserves Msg and
    Queue clears it, as selected by their source-family parameter. *)
Definition event_pend_cleanup_state (sg : StableGlobVars) (clear_message : bool)
  (s : UCOS2_Verify_State) (tid : TaskID) (old : TaskAbstractState) : UCOS2_Verify_State :=
  replace_TskS (glob_task_set_usedtask s.(TskState) tid
    (task_event_pend_cleanup sg.(osKernelConfig).(cfgEventMultiEnabled) clear_message old)) s.

Definition message_pend_cleanup_state (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (tid : TaskID) (old : TaskAbstractState) : UCOS2_Verify_State :=
  event_pend_cleanup_state sg true s tid old.

Lemma event_pend_cleanup_preserves_cross_module_consistency : forall sg s tid old clear_message,
  s.(TskState).(inUsedTaskStates) tid = Some old -> old.(eventPtr) = None ->
  old.(eventMultiWaitEvents) = [] -> old.(tcbFlagNode) = 0 ->
  cross_module_consistency sg s ->
  cross_module_consistency sg (event_pend_cleanup_state sg clear_message s tid old).
Proof.
  intros sg s tid old clear_message Hold Hnull Hmulti Hflagnull
    [Htable [Hsnapshot [Hwait [Hprotocol [Hunique [Hflag Htimer]]]]]].
  pose proof (event_unregistered_task_not_waiting sg s.(TskState) s.(EventState)
    tid old (proj1 Hwait) Hold Hnull) as Habsent.
  unfold event_pend_cleanup_state; split.
  - eapply task_mutex_priotbl_consistency_update_task;
      [exact Hold|destruct sg.(osKernelConfig).(cfgEventMultiEnabled); reflexivity|exact Htable].
  - split; [eapply mutex_owner_snapshot_update_task; eauto|].
    split.
    + eapply event_wait_object_update_unlisted_task;
        [exact Hold| | |exact Habsent|exact Hwait].
      * destruct sg.(osKernelConfig).(cfgEventMultiEnabled); simpl; symmetry; exact Hnull.
      * destruct sg.(osKernelConfig).(cfgEventMultiEnabled); simpl; congruence.
    + split; [exact Hprotocol|]; split; [exact Hunique|]; split; [|exact Htimer].
      eapply task_flag_waiter_consistency_update_unregistered_task;
        [exact Hold|exact Hflagnull| | |exact Hflag].
      * destruct sg.(osKernelConfig).(cfgEventMultiEnabled); exact Hflagnull.
      * destruct sg.(osKernelConfig).(cfgEventMultiEnabled); discriminate.
Qed.

Lemma message_pend_cleanup_preserves_cross_module_consistency : forall sg s tid old,
  s.(TskState).(inUsedTaskStates) tid = Some old -> old.(eventPtr) = None ->
  old.(eventMultiWaitEvents) = [] -> old.(tcbFlagNode) = 0 ->
  cross_module_consistency sg s ->
  cross_module_consistency sg (message_pend_cleanup_state sg s tid old).
Proof. intros; eapply event_pend_cleanup_preserves_cross_module_consistency; eassumption. Qed.

(** Payload writes such as Queue ring updates keep the Event's kind,
    Mutex fields and waiter registration.  These are exactly the fields
    read by the current cross-module relations.  Event/Queue ownership,
    payload validity and actual stores remain separate obligations. *)
(** Shared Event-map transport for payload updates and removal of an empty
    non-Mutex object.  Surviving Events retain their wait interpretation;
    every old Mutex remains available to priority aliases.  Reference
    closure is an explicit proved obligation, not inferred from one-way
    membership or hidden in the source transformer. *)
Lemma cross_module_consistency_with_wait_event_mutex_transport : forall sg s events
    (waiting_before waiting_after : Prop),
  (forall slot node, events.(inUsedEventStates) slot = Some node ->
    node.(eventType) = OS_EVENT_TYPE_MUTEX ->
    exists before, s.(EventState).(inUsedEventStates) slot = Some before /\
      node.(eventType) = before.(eventType) /\ node.(mutexFields) = before.(mutexFields) /\
      node.(waitList) = before.(waitList)) ->
  (forall slot before, s.(EventState).(inUsedEventStates) slot = Some before ->
    before.(eventType) = OS_EVENT_TYPE_MUTEX ->
    exists node, events.(inUsedEventStates) slot = Some node /\
      node.(eventType) = before.(eventType) /\ node.(mutexFields) = before.(mutexFields)) ->
  waiting_after ->
  event_mutex_lease_view events = event_mutex_lease_view s.(EventState) ->
  cross_module_consistency_with_wait sg s waiting_before ->
  cross_module_consistency_with_wait sg (replace_EventS events s) waiting_after.
Proof.
  intros sg s events waiting_before waiting_after Horigin Hforward Hwaiting Hleases
    [Htable [Hsnapshot [_ [Hprotocol [Hunique [Hflag Htimer]]]]]].
  assert (Hclaims : forall p,
    (exists mid node m, events.(inUsedEventStates) mid = Some node /\
      node.(eventType) = OS_EVENT_TYPE_MUTEX /\ node.(mutexFields) = Some m /\
      mutex_reserves_priority_slot sg m p) <->
    (exists mid node m, s.(EventState).(inUsedEventStates) mid = Some node /\
      node.(eventType) = OS_EVENT_TYPE_MUTEX /\ node.(mutexFields) = Some m /\
      mutex_reserves_priority_slot sg m p)).
  { intro p; split; intros [mid [node [m [Hnode [Hty [Hm Hclaim]]]]]].
    - destruct (Horigin mid node Hnode Hty) as [before [Hb [Ht [Hf _]]]].
      exists mid, before, m; split; [exact Hb|]; split; [congruence|]; split; [congruence|exact Hclaim].
    - destruct (Hforward mid node Hnode Hty) as [after [Ha [Ht Hf]]].
      exists mid, after, m; split; [exact Ha|]; split; [congruence|]; split; [congruence|exact Hclaim]. }
  change (cross_module_consistency_with_wait sg (replace_EventS events s) waiting_after).
  unfold cross_module_consistency_with_wait; split.
  - destruct Htable as [Hcreator [Hslots Halias]]; split.
    + intros p entry Hentry Hclaim; apply (Hcreator p entry Hentry); apply Hclaims; exact Hclaim.
    + split.
      * intros p Hp; specialize (Hslots p Hp); cbn [replace_EventS TskState EventState].
        destruct (s.(TskState).(prioTbl) p).
        -- intro Hclaim; apply Hslots; apply Hclaims; exact Hclaim.
        -- destruct Hslots as [Hreservation|[Hclaim|Hpending]].
           ++ left; exact Hreservation.
           ++ right; left; apply Hclaims; exact Hclaim.
           ++ right; right; unfold pending_mutex_priority_claim in *; rewrite Hleases; exact Hpending.
        -- exact Hslots.
      * eapply mutex_priority_alias_consistency_ext; [reflexivity|reflexivity| |exact Halias].
        intros owner p [mid [node [m [Hnode [Hty [Hm Hclaim]]]]]].
        destruct (Hforward mid node Hnode Hty) as [after [Ha [Ht Hf]]].
        exists mid, after, m; split; [exact Ha|]; split; [congruence|]; split; [congruence|exact Hclaim].
  - split.
    + intros mid node m owner Hnode Hty Hm Howner.
      destruct (Horigin mid node Hnode Hty) as [before [Hb [Ht [Hf Hw]]]].
      destruct (Hsnapshot mid before m owner Hb ltac:(congruence) ltac:(congruence) Howner)
        as [t [base [saved [Htask [Hbase [Hsaved [Hrange [Hbound Habsent]]]]]]]].
      exists t, base, saved; split; [exact Htask|]; split; [exact Hbase|]; split; [exact Hsaved|];
        split; [exact Hrange|]; split; [exact Hbound|rewrite Hw; exact Habsent].
    + split.
      * exact Hwaiting.
      * split.
        -- intros mid node m Hnode Hty Hm.
           destruct (Horigin mid node Hnode Hty) as [before [Hb [Ht [Hf _]]]].
           exact (Hprotocol mid before m Hb ltac:(congruence) ltac:(congruence)).
        -- split.
           ++ intros mid1 node1 m1 mid2 node2 m2 Hn1 Ht1 Hm1 Hn2 Ht2 Hm2 Hp Hnonzero.
              destruct (Horigin mid1 node1 Hn1 Ht1) as [before1 [Hb1 [Ht1' [Hm1' _]]]].
              destruct (Horigin mid2 node2 Hn2 Ht2) as [before2 [Hb2 [Ht2' [Hm2' _]]]].
              eapply Hunique; [exact Hb1| | |exact Hb2| | |exact Hp|exact Hnonzero]; congruence.
           ++ split; [exact Hflag|exact Htimer].
Qed.

(** The existing single-wait theorem retains its exact statement. *)
Lemma cross_module_consistency_event_mutex_transport : forall sg s events,
  (forall slot node, events.(inUsedEventStates) slot = Some node ->
    node.(eventType) = OS_EVENT_TYPE_MUTEX ->
    exists before, s.(EventState).(inUsedEventStates) slot = Some before /\
      node.(eventType) = before.(eventType) /\ node.(mutexFields) = before.(mutexFields) /\
      node.(waitList) = before.(waitList)) ->
  (forall slot before, s.(EventState).(inUsedEventStates) slot = Some before ->
    before.(eventType) = OS_EVENT_TYPE_MUTEX ->
    exists node, events.(inUsedEventStates) slot = Some node /\
      node.(eventType) = before.(eventType) /\ node.(mutexFields) = before.(mutexFields)) ->
  event_wait_object_consistency sg (replace_EventS events s) ->
  event_mutex_lease_view events = event_mutex_lease_view s.(EventState) ->
  cross_module_consistency sg s ->
  cross_module_consistency sg (replace_EventS events s).
Proof. intros; eapply cross_module_consistency_with_wait_event_mutex_transport; eassumption. Qed.

(** Compatibility interface for updates/removals.  The Mutex transport
    above is shared with creation; waiter transport belongs to Event. *)
Lemma cross_module_consistency_event_transport : forall sg s events,
  (forall slot node, events.(inUsedEventStates) slot = Some node ->
    exists before, s.(EventState).(inUsedEventStates) slot = Some before /\
      node.(eventType) = before.(eventType) /\ node.(mutexFields) = before.(mutexFields) /\
      node.(waitList) = before.(waitList)) ->
  (forall slot before, s.(EventState).(inUsedEventStates) slot = Some before ->
    before.(eventType) = OS_EVENT_TYPE_MUTEX ->
    exists node, events.(inUsedEventStates) slot = Some node /\
      node.(eventType) = before.(eventType) /\ node.(mutexFields) = before.(mutexFields)) ->
  task_event_reference_closure s.(TskState) events ->
  event_mutex_lease_view events = event_mutex_lease_view s.(EventState) ->
  cross_module_consistency sg s ->
  cross_module_consistency sg (replace_EventS events s).
Proof.
  intros sg s events Horigin Hforward Hreferences Hleases Hcross.
  eapply cross_module_consistency_event_mutex_transport;
    [intros slot node Hnode Htype; exact (Horigin slot node Hnode)|exact Hforward| |exact Hleases|exact Hcross].
  pose proof Hcross as [_ [_ [[Hentries [Hback _]] _]]].
  unfold event_wait_object_consistency; cbn [replace_EventS TskState EventState]; split.
  - intros slot node Hnode; destruct (Horigin slot node Hnode) as [before [Hb [Ht [_ Hw]]]].
    unfold event_wait_entry_consistency; rewrite Ht, Hw; exact (Hentries slot before Hb).
  - split.
    + intros tid t slot node Htask Hnode Href.
      destruct (Horigin slot node Hnode) as [before [Hb [_ [_ Hw]]]].
      rewrite Hw; eapply Hback; eassumption.
    + exact Hreferences.
Qed.

Lemma cross_module_consistency_event_map_frame : forall sg s events,
  events.(inUsedEventStates) = s.(EventState).(inUsedEventStates) ->
  event_mutex_lease_view events = event_mutex_lease_view s.(EventState) ->
  cross_module_consistency sg s ->
  cross_module_consistency sg (replace_EventS events s).
Proof.
  intros sg s events Hmap Hleases Hcross; eapply cross_module_consistency_event_transport.
  - intros slot node Hnode; exists node; rewrite Hmap in Hnode; auto.
  - intros slot node Hnode Htype; exists node; rewrite Hmap; auto.
  - pose proof Hcross as [_ [_ [[_ [_ Hclosed]] _]]].
    unfold task_event_reference_closure in *; rewrite Hmap; exact Hclosed.
  - exact Hleases.
  - exact Hcross.
Qed.

Lemma cross_module_consistency_event_publish : forall sg s events eid node,
  s.(EventState).(inUsedEventStates) eid = None ->
  node.(eventType) <> OS_EVENT_TYPE_MUTEX -> node.(waitList) = [] ->
  events.(inUsedEventStates) = kernel_map_set s.(EventState).(inUsedEventStates) eid (Some node) ->
  event_mutex_lease_view events = event_mutex_lease_view s.(EventState) ->
  cross_module_consistency sg s ->
  cross_module_consistency sg (replace_EventS events s).
Proof.
  intros sg s events eid node Hnone Hnonmutex Hempty Hmap Hleases Hcross.
  eapply cross_module_consistency_event_mutex_transport.
  - intros slot after Ha Htype; rewrite Hmap in Ha; unfold kernel_map_set in Ha.
    destruct (Z.eq_dec slot eid) as [->|Hne].
    + injection Ha as Ha; subst after; contradiction.
    + exists after; auto.
  - intros slot before Hb Htype; exists before; rewrite Hmap; unfold kernel_map_set.
    destruct (Z.eq_dec slot eid) as [->|Hne]; [congruence|auto].
  - eapply event_wait_object_consistency_event_publish;
      [exact Hnone|exact Hempty|exact Hmap|exact (proj1 (proj2 (proj2 Hcross)))].
  - exact Hleases.
  - exact Hcross.
Qed.

Lemma cross_module_consistency_event_fields_update : forall sg s eid old new,
  s.(EventState).(inUsedEventStates) eid = Some old ->
  new.(eventType) = old.(eventType) -> new.(mutexFields) = old.(mutexFields) ->
  new.(waitList) = old.(waitList) -> cross_module_consistency sg s ->
  cross_module_consistency sg
    (replace_EventS (update_event_field_raw s.(EventState) eid new) s).
Proof.
  intros sg s eid old new Hold Htype Hmutex Hwait Hcross.
  set (events := update_event_field_raw s.(EventState) eid new).
  assert (Horigin : forall slot node, events.(inUsedEventStates) slot = Some node ->
    exists before, s.(EventState).(inUsedEventStates) slot = Some before /\
      node.(eventType) = before.(eventType) /\ node.(mutexFields) = before.(mutexFields) /\
      node.(waitList) = before.(waitList)).
  { intros slot node Hnode; unfold events in Hnode; cbn in Hnode.
    destruct (Z.eqb slot eid) eqn:E.
    - apply Z.eqb_eq in E; subst slot; injection Hnode as Hnode; subst node.
      exists old; auto.
    - exists node; repeat split; auto. }
  assert (Hforward : forall slot before, s.(EventState).(inUsedEventStates) slot = Some before ->
    exists node, events.(inUsedEventStates) slot = Some node /\
      node.(eventType) = before.(eventType) /\ node.(mutexFields) = before.(mutexFields)).
  { intros slot before Hbefore; unfold events; cbn; destruct (Z.eqb slot eid) eqn:E.
    - apply Z.eqb_eq in E; subst slot; rewrite Hold in Hbefore; injection Hbefore as Hbefore; subst before.
      exists new; auto.
    - exists before; auto. }
  change (cross_module_consistency sg (replace_EventS events s)).
  eapply cross_module_consistency_event_transport.
  - exact Horigin.
  - intros slot before Hb Hty; exact (Hforward slot before Hb).
  - pose proof Hcross as [_ [_ [[_ [_ Hclosed]] _]]].
    eapply task_event_reference_closure_preserved_by_event_extension; [|exact Hclosed].
    intros slot [before Hb]; destruct (Hforward slot before Hb) as [after [Ha _]].
    exists after; exact Ha.
  - reflexivity.
  - exact Hcross.
Qed.

Lemma cross_module_consistency_event_remove : forall sg s eid node events,
  s.(EventState).(inUsedEventStates) eid = Some node ->
  node.(eventType) <> OS_EVENT_TYPE_MUTEX -> node.(waitList) = [] ->
  events.(inUsedEventStates) = kernel_map_set s.(EventState).(inUsedEventStates) eid None ->
  event_mutex_lease_view events = event_mutex_lease_view s.(EventState) ->
  cross_module_consistency sg s ->
  cross_module_consistency sg (replace_EventS events s).
Proof.
  intros sg s eid node events Hnode Hnonmutex Hempty Hmap Hleases Hcross.
  pose proof Hcross as [_ [_ [[_ [Hback Hclosed]] _]]].
  assert (Hsafe : task_event_id_unreferenced_prop s eid).
  { intros tid t Htask; split; intro Href;
      pose proof (Hback tid t eid node Htask Hnode ltac:(auto)) as Hin;
      rewrite Hempty in Hin; contradiction. }
  eapply cross_module_consistency_event_transport.
  - intros slot after Ha; rewrite Hmap in Ha; unfold kernel_map_set in Ha.
    destruct (Z.eq_dec slot eid) as [->|Hne]; [discriminate|].
    exists after; repeat split; assumption || reflexivity.
  - intros slot before Hb Htype.
    assert (Hne : slot <> eid).
    { intro E; subst slot; rewrite Hnode in Hb; injection Hb as Hb; subst before; contradiction. }
    exists before; split.
    + rewrite Hmap; unfold kernel_map_set; destruct (Z.eq_dec slot eid); congruence.
    + split; reflexivity.
  - intros tid t Htask; destruct (Hclosed tid t Htask) as [Hsingle Hmulti].
    destruct (Hsafe tid t Htask) as [HnoSingle HnoMulti]; split.
    + intros slot Hptr; destruct (Hsingle slot Hptr) as [before Hb]; exists before.
      rewrite Hmap; unfold kernel_map_set; destruct (Z.eq_dec slot eid) as [->|Hne];
        [contradiction|exact Hb].
    + intros slot Hin; destruct (Hmulti slot Hin) as [before Hb]; exists before.
      rewrite Hmap; unfold kernel_map_set; destruct (Z.eq_dec slot eid) as [->|Hne];
        [contradiction|exact Hb].
  - exact Hleases.
  - exact Hcross.
Qed.

Lemma pending_mutex_consistency_task_reserve : forall sg tasks events p invocation origin,
  pending_mutex_consistency sg tasks events -> task_reserve_guard sg tasks p invocation origin ->
  pending_mutex_consistency sg (task_reserve tasks p invocation origin) events.
Proof.
  intros sg tasks events p invocation origin Hpending Hguard.
  assert (Hnot : ~ pending_mutex_priority_claim events p).
  { eapply pending_mutex_consistency_free_slot_excludes_claim;
      [exact Hpending|exact (proj1 (proj2 Hguard))]. }
  eapply pending_mutex_consistency_table_transport with (tasks := tasks); [| |exact Hpending].
  - intros q Hq; exact (proj1 (task_reserve_other_priority tasks p q invocation origin ltac:(congruence))).
  - intros q Hq; exact (proj2 (task_reserve_other_priority tasks p q invocation origin ltac:(congruence))).
Qed.

Lemma pending_mutex_consistency_task_rollback : forall sg tasks events p invocation,
  pending_mutex_consistency sg tasks events -> task_rollback_guard tasks p invocation ->
  pending_mutex_consistency sg (task_rollback_reservation tasks p) events.
Proof.
  intros sg tasks events p invocation Hpending [entry [Hentry Hrest]].
  assert (Hnot : ~ pending_mutex_priority_claim events p).
  { eapply pending_mutex_consistency_task_reservation_excludes_claim; eassumption. }
  eapply pending_mutex_consistency_table_transport with (tasks := tasks); [| |exact Hpending].
  - intros q Hq; cbn [task_rollback_reservation prioTbl]; destruct (Z.eq_dec q p); congruence.
  - intros q Hq; cbn [task_rollback_reservation taskLifecycle task_lifecycle_set_reservation taskReservations];
      destruct (Z.eq_dec q p); congruence.
Qed.

Lemma pending_mutex_consistency_task_detach : forall sg tasks events p entry tid rest image,
  pending_mutex_consistency sg tasks events -> task_detach_guard tasks p entry tid rest image ->
  pending_mutex_consistency sg (task_detach_head tasks p entry tid rest image) events.
Proof.
  intros sg tasks events p entry tid rest image Hpending Hguard.
  assert (Hnot : ~ pending_mutex_priority_claim events p).
  { eapply pending_mutex_consistency_task_reservation_excludes_claim;
      [exact Hpending|exact (proj1 (proj2 Hguard))]. }
  eapply pending_mutex_consistency_table_transport with (tasks := tasks); [intros; reflexivity| |exact Hpending].
  intros q Hq; cbn [task_detach_head taskLifecycle taskReservations];
    destruct (Z.eq_dec q p); congruence.
Qed.

Lemma pending_mutex_consistency_task_private_image : forall sg tasks events p entry allocation image,
  pending_mutex_consistency sg tasks events ->
  tasks.(taskLifecycle).(taskReservations) p = Some entry ->
  pending_mutex_consistency sg (task_update_private_image tasks p entry allocation image) events.
Proof.
  intros sg tasks events p entry allocation image Hpending Hentry.
  assert (Hnot : ~ pending_mutex_priority_claim events p).
  { eapply pending_mutex_consistency_task_reservation_excludes_claim; eassumption. }
  eapply pending_mutex_consistency_table_transport with (tasks := tasks); [intros; reflexivity| |exact Hpending].
  intros q Hq; cbn [task_update_private_image glob_task_set_lifecycle taskLifecycle task_lifecycle_set_reservation taskReservations];
    destruct (Z.eq_dec q p); congruence.
Qed.

Lemma pending_mutex_consistency_task_commit : forall sg tasks events p invocation node,
  pending_mutex_consistency sg tasks events -> task_commit_identity tasks p invocation node ->
  pending_mutex_consistency sg (task_commit tasks p invocation node) events.
Proof.
  intros sg tasks events p invocation node Hpending [entry [allocation [Hentry Hrest]]].
  assert (Hnot : ~ pending_mutex_priority_claim events p).
  { eapply pending_mutex_consistency_task_reservation_excludes_claim; eassumption. }
  eapply pending_mutex_consistency_table_transport with (tasks := tasks); [| |exact Hpending].
  - intros q Hq; cbn [task_commit prioTbl]; destruct (Z.eq_dec q p); congruence.
  - intros q Hq; cbn [task_commit taskLifecycle taskReservations]; destruct (Z.eq_dec q p); congruence.
Qed.

Lemma pending_mutex_consistency_event_fields_update : forall sg tasks events eid old node,
  events.(inUsedEventStates) eid = Some old ->
  node.(eventType) = old.(eventType) -> node.(mutexFields) = old.(mutexFields) ->
  pending_mutex_consistency sg tasks events ->
  pending_mutex_consistency sg tasks (update_event_field_raw events eid node).
Proof.
  intros sg tasks events eid old node Hold Htype Hfields Hpending.
  eapply pending_mutex_consistency_event_transport with (events := events);
    [reflexivity| |exact Hpending].
  intros slot after Hafter Hmutex; cbn [update_event_field_raw inUsedEventStates] in Hafter.
  destruct (Z.eqb slot eid) eqn:E.
  - apply Z.eqb_eq in E; subst slot; injection Hafter as Hafter; subst after.
    exists old; split; [exact Hold|]. split; [congruence|exact Hfields].
  - exists after; split; [exact Hafter|]. split; [exact Hmutex|reflexivity].
Qed.
