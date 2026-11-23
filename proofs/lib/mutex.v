Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Import UCOS2_C_Rules.
Import TaskStateDef.
Import EventStateDef.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope list_scope.
Local Open Scope sac_scope.

(* L1/L2 representation-domain distinction.  OS_PRIO_MUTEX_CEIL_DIS is a
   value that may be stored in mfPCP, but it is not a concrete priority-table
   index.  Only enabled PCP values participate in the reservation protocol. *)
Definition mutex_pcp_enabled (sg : StableGlobVars) (m : MutexFields) : Prop :=
  m.(mfPCP) <> sg.(osPrioMutexCeilDis).

Definition mutex_reserves_priority_slot (sg : StableGlobVars)
  (m : MutexFields) (p : Priority) : Prop :=
  mutex_pcp_enabled sg m /\ m.(mfPCP) = p.

(* A task-priority relocation does not itself mutate any OS_EVENT record.
   Consequently, restoring [tid] to [newPrio] preserves the owner side of the
   mutex/task protocol exactly when every mutex still owned by [tid] accepts
   that priority through its recorded owner-original priority or through an
   enabled PCP.  This is a conditional safety fact, not an execution-domain
   restriction: the literal kernel code can still perform a relocation when
   this predicate is false. *)
Definition mutex_task_restore_safe
  (sg : StableGlobVars) (evSt : Glob_EventAbstractState)
  (tid : TaskID) (newPrio : Priority) : Prop :=
  forall mid e m,
    evSt.(inUsedEventStates) mid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    m.(mfOwner) = Some tid ->
    m.(mfOwnerOrigPrio) = Some newPrio \/
    (mutex_pcp_enabled sg m /\ m.(mfPCP) = newPrio).

(* Source-backed target mutex orientation for a real disinherit/restore call.
   The enabled PCP is the task's entry/current priority, while [newPrio] is the
   owner-original priority recorded by the selected mutex. *)
Definition mutex_target_restore_reason
  (sg : StableGlobVars) (evSt : Glob_EventAbstractState)
  (restore_mid : EventID) (tid : TaskID)
  (oldPrio newPrio : Priority) : Prop :=
  exists e m,
    evSt.(inUsedEventStates) restore_mid = Some e /\
    e.(eventType) = OS_EVENT_TYPE_MUTEX /\
    e.(mutexFields) = Some m /\
    m.(mfOwner) = Some tid /\
    mutex_pcp_enabled sg m /\
    m.(mfPCP) = oldPrio /\
    m.(mfOwnerOrigPrio) = Some newPrio.

(* A retained [PTTask tid] priority-table alias is justified by a live mutex
   owned by [tid].  In the source this is either the owner's saved/original
   priority or an enabled PCP currently occupied by the owner. *)
Definition mutex_task_priority_alias_claim
  (sg : StableGlobVars) (evSt : Glob_EventAbstractState)
  (tid : TaskID) (p : Priority) : Prop :=
  exists mid e m,
    evSt.(inUsedEventStates) mid = Some e /\
    e.(eventType) = OS_EVENT_TYPE_MUTEX /\
    e.(mutexFields) = Some m /\
    m.(mfOwner) = Some tid /\
    (m.(mfOwnerOrigPrio) = Some p \/
     (mutex_pcp_enabled sg m /\ m.(mfPCP) = p)).

(* The [PTReserved -> PTTask tid] write performed by inheritance is legal
   only for an enabled PCP of a live mutex already owned by [tid].  Keeping
   this narrower than [mutex_task_priority_alias_claim] prevents an unrelated
   ownerless reservation from being consumed by the generic transformer. *)
Definition mutex_task_enabled_pcp_claim
  (sg : StableGlobVars) (evSt : Glob_EventAbstractState)
  (tid : TaskID) (p : Priority) : Prop :=
  exists mid e m,
    evSt.(inUsedEventStates) mid = Some e /\
    e.(eventType) = OS_EVENT_TYPE_MUTEX /\
    e.(mutexFields) = Some m /\
    m.(mfOwner) = Some tid /\
    mutex_pcp_enabled sg m /\
    m.(mfPCP) = p.

(* Stable-state call domain for the literal task-priority transformer.

   The transformer writes [prioTbl newPrio := PTTask tid] but deliberately
   retains the old slot.  The source has two legitimate destination shapes:

   - restore/disinherit writes an existing [PTTask tid] original-priority
     alias;
   - inheritance consumes the selected mutex's [PTReserved] PCP slot.

   A full-invariant theorem additionally needs every mutex still owned by
   [tid] to accept the new current priority, and (for a real change) a live
   mutex claimant for the retained old alias.  These are preservation facts,
   not extra guards on execution of the literal C helper. *)
Definition task_priority_relocation_legal
  (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (tid : TaskID) (newPrio : Priority) : Prop :=
  exists t,
    s.(TskState).(inUsedTaskStates) tid = Some t /\
    (s.(TskState).(prioTbl) newPrio = PTTask tid \/
     (s.(TskState).(prioTbl) newPrio = PTReserved /\
      mutex_task_enabled_pcp_claim
        sg s.(EventState) tid newPrio)) /\
    mutex_task_restore_safe sg s.(EventState) tid newPrio /\
    (t.(curPrio) = newPrio \/
     mutex_task_priority_alias_claim
       sg s.(EventState) tid t.(curPrio)).

Definition atomic_mutex_inherit_relocation_legal
  (sg : StableGlobVars) (mid : EventID) (s : UCOS2_Verify_State) : Prop :=
  forall e m owner,
    s.(EventState).(inUsedEventStates) mid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    m.(mfOwner) = Some owner ->
    task_priority_relocation_legal sg s owner m.(mfPCP).

Definition atomic_mutex_restore_relocation_legal
  (sg : StableGlobVars) (mid : EventID) (s : UCOS2_Verify_State) : Prop :=
  forall e m owner orig,
    s.(EventState).(inUsedEventStates) mid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    m.(mfOwner) = Some owner ->
    m.(mfOwnerOrigPrio) = Some orig ->
    task_priority_relocation_legal sg s owner orig.

(* Delete receives the already-decoded mutex fields rather than an EventID.
   This wrapper states only the legality of the optional owner restoration;
   it does not claim that the later owner-clear staging state is a full OS
   invariant state. *)
Definition mutex_fields_restore_relocation_legal
  (sg : StableGlobVars) (m : MutexFields) (s : UCOS2_Verify_State) : Prop :=
  forall owner orig,
    m.(mfOwner) = Some owner ->
    m.(mfOwnerOrigPrio) = Some orig ->
    task_priority_relocation_legal sg s owner orig.

(* Conditional classification for rebuilding the full cross-module invariant.
   Equal-priority execution is safe independently of a target mutex because it
   leaves the represented task priority unchanged (while still performing the
   literal priority-table write).  A genuine restore additionally needs both
   a correctly oriented target and compatibility of every still-owned mutex.
   This predicate is never part of the raw helper execution domain. *)
Definition mutex_ready_relocation_safe
  (sg : StableGlobVars) (evSt : Glob_EventAbstractState)
  (restore_mid : EventID) (tid : TaskID)
  (oldPrio newPrio : Priority) : Prop :=
  oldPrio = newPrio \/
  (oldPrio <> newPrio /\
   mutex_target_restore_reason
     sg evSt restore_mid tid oldPrio newPrio /\
   mutex_task_restore_safe sg evSt tid newPrio).

(* Explicit witness form for the reachable complement.  Keeping this relation
   separate from [mutex_task_restore_safe] lets public callers retain their
   real source domain while exposing a mutex record that the unchanged event
   state makes incompatible with the requested restored priority. *)
Definition mutex_task_restore_unsafe
  (sg : StableGlobVars) (evSt : Glob_EventAbstractState)
  (tid : TaskID) (newPrio : Priority) : Prop :=
  exists mid e m,
    evSt.(inUsedEventStates) mid = Some e /\
    e.(eventType) = OS_EVENT_TYPE_MUTEX /\
    e.(mutexFields) = Some m /\
    m.(mfOwner) = Some tid /\
    ~ (m.(mfOwnerOrigPrio) = Some newPrio \/
       (mutex_pcp_enabled sg m /\ m.(mfPCP) = newPrio)).

Lemma mutex_task_restore_unsafe_not_safe :
  forall sg evSt tid newPrio,
    mutex_task_restore_unsafe sg evSt tid newPrio ->
    ~ mutex_task_restore_safe sg evSt tid newPrio.
Proof.
  intros sg evSt tid newPrio
    (mid & e & m & Hget & Htype & Hfields & Howner & Hbad) Hsafe.
  apply Hbad.
  eapply Hsafe; eauto.
Qed.

(* Observable event-state relations used by the OSMutexPost contract. *)
Definition mutex_release_event_prop
  (before after : OSEventAbstractState) : Prop :=
  exists m owner orig,
    before.(eventType) = OS_EVENT_TYPE_MUTEX /\
    before.(mutexFields) = Some m /\
    m.(mfOwner) = Some owner /\
    m.(mfOwnerOrigPrio) = Some orig /\
    before.(waitList) = [] /\
    after =
      {| eventGeneration := before.(eventGeneration);
         eventName := before.(eventName);
     eventPadding1 := before.(eventPadding1);
     eventPadding2 := before.(eventPadding2);
     eventPadding3 := before.(eventPadding3);
     eventPadding19 := before.(eventPadding19);
         eventType   := before.(eventType);
         mutexFields := Some {| mfPCP := m.(mfPCP);
                                mfOwner := None;
                                mfOwnerOrigPrio := None |};
         semFields   := before.(semFields);
         mboxFields  := before.(mboxFields);
         queueFields := before.(queueFields);
         waitList    := [] |}.

Definition mutex_handover_event_prop
  (before after : OSEventAbstractState)
  (new_owner : TaskID) (new_owner_prio : Priority) : Prop :=
  exists m old_owner old_orig rest,
    before.(eventType) = OS_EVENT_TYPE_MUTEX /\
    before.(mutexFields) = Some m /\
    m.(mfOwner) = Some old_owner /\
    m.(mfOwnerOrigPrio) = Some old_orig /\
    before.(waitList) = new_owner :: rest /\
    after =
      {| eventGeneration := before.(eventGeneration);
         eventName := before.(eventName);
     eventPadding1 := before.(eventPadding1);
     eventPadding2 := before.(eventPadding2);
     eventPadding3 := before.(eventPadding3);
     eventPadding19 := before.(eventPadding19);
         eventType   := before.(eventType);
         mutexFields := Some {| mfPCP := m.(mfPCP);
                                mfOwner := Some new_owner;
                                mfOwnerOrigPrio := Some new_owner_prio |};
         semFields   := before.(semFields);
         mboxFields  := before.(mboxFields);
         queueFields := before.(queueFields);
         waitList    := rest |}.

Definition mutex_del_no_pend_owner_safe
  (e : OSEventAbstractState) (tskSt : Glob_TaskAbstractState) : Prop :=
  exists m,
    e.(eventType) = OS_EVENT_TYPE_MUTEX /\
    e.(mutexFields) = Some m /\
    match m.(mfOwner), m.(mfOwnerOrigPrio) with
    | None, None => True
    | Some owner, Some orig =>
        exists owner_t,
          tskSt.(inUsedTaskStates) owner = Some owner_t /\
          owner_t.(curPrio) = orig
    | _, _ => False
    end.

Definition mutex_del_owner_restored_prop
  (e : OSEventAbstractState) (tskSt : Glob_TaskAbstractState) : Prop :=
  exists m,
    e.(eventType) = OS_EVENT_TYPE_MUTEX /\
    e.(mutexFields) = Some m /\
    match m.(mfOwner), m.(mfOwnerOrigPrio) with
    | None, None => True
    | Some owner, Some orig =>
        exists owner_t,
          tskSt.(inUsedTaskStates) owner = Some owner_t /\
          owner_t.(curPrio) = orig
    | _, _ => False
    end.

Definition mutex_del_waiters_aborted_prop
  (e : OSEventAbstractState) (tskSt : Glob_TaskAbstractState)
  (schedSt : SchedAbstractState) : Prop :=
  forall tid,
    In tid e.(waitList) ->
    exists t,
      tskSt.(inUsedTaskStates) tid = Some t /\
      (task_non_suspension_bits (t.(stat))) = 0 /\
      t.(statPend) = PendAbort /\
      t.(dly) = 0 /\
      t.(eventPtr) = None /\
      In tid schedSt.(readyList).

Definition mutex_acquire_event_prop
  (before after : OSEventAbstractState)
  (owner : TaskID) (owner_orig_prio : Priority) : Prop :=
  exists m,
    before.(eventType) = OS_EVENT_TYPE_MUTEX /\
    before.(mutexFields) = Some m /\
    m.(mfOwner) = None /\
    after =
      {| eventGeneration := before.(eventGeneration);
         eventName := before.(eventName);
     eventPadding1 := before.(eventPadding1);
     eventPadding2 := before.(eventPadding2);
     eventPadding3 := before.(eventPadding3);
     eventPadding19 := before.(eventPadding19);
         eventType   := before.(eventType);
         mutexFields := Some {| mfPCP := m.(mfPCP);
                                mfOwner := Some owner;
                                mfOwnerOrigPrio := Some owner_orig_prio |};
         semFields   := before.(semFields);
         mboxFields  := before.(mboxFields);
         queueFields := before.(queueFields);
         waitList    := before.(waitList) |}.

Definition mutex_owned_by_prop
  (e : OSEventAbstractState) (owner : TaskID) (orig_prio : Priority)
  : Prop :=
  exists m,
    e.(eventType) = OS_EVENT_TYPE_MUTEX /\
    e.(mutexFields) = Some m /\
    m.(mfOwner) = Some owner /\
    m.(mfOwnerOrigPrio) = Some orig_prio.

(* Payload/tag observation used by the historical MutexPend contract.
   This is not a frame for generation, name, padding or the complete event;
   their preservation must follow from the actual operation/interference. *)
Definition mutex_event_payload_unchanged_prop
  (before after : OSEventAbstractState) : Prop :=
  after.(eventType) = before.(eventType) /\
  after.(mutexFields) = before.(mutexFields) /\
  after.(semFields) = before.(semFields) /\
  after.(mboxFields) = before.(mboxFields) /\
  after.(queueFields) = before.(queueFields).

Definition mutex_waiter_absent_prop
  (e : OSEventAbstractState) (tid : TaskID) : Prop :=
  ~ In tid e.(waitList).

(* uC/OS-II mutexes are not recursive. A successful acquisition is only
   specified for an available mutex; a held mutex must be owned by another
   task before the caller enters the blocking path. *)
Definition mutex_pend_nonrecursive_prop
  (e : OSEventAbstractState) (cur_tid : TaskID) : Prop :=
  match e.(mutexFields) with
  | Some m => m.(mfOwner) <> Some cur_tid
  | None => True
  end.

Definition mutex_pend_owner_ready_prop
  (e : OSEventAbstractState) (tskSt : Glob_TaskAbstractState)
  (cur_tid owner_tid : TaskID) (owner_t : TaskAbstractState) : Prop :=
  exists m owner_orig,
    e.(eventType) = OS_EVENT_TYPE_MUTEX /\
    e.(mutexFields) = Some m /\
    m.(mfOwner) = Some owner_tid /\
    m.(mfOwnerOrigPrio) = Some owner_orig /\
    mutex_pend_nonrecursive_prop e cur_tid /\
    tskSt.(inUsedTaskStates) owner_tid = Some owner_t /\
    (task_non_suspension_bits (owner_t.(stat))) = 0 /\
    owner_t.(eventPtr) = None /\
    owner_t.(eventMultiWaitEvents) = [] /\
    owner_t.(eventMultiRdy) = None /\
    is_effectively_ready owner_t.(stat) owner_t.(dly) = true.

(* Source path os_mutex.c:544-577: the owner is not ready and its priority
   must be relocated in a distinct single-event wait list.  Multi-event wait
   is excluded because this verification target sets OS_EVENT_MULTI_EN to 0. *)
Definition mutex_pend_owner_waiting_prop
  (mutex_e : OSEventAbstractState) (mutex_eid : EventID)
  (tskSt : Glob_TaskAbstractState) (schedSt : SchedAbstractState)
  (evSt : Glob_EventAbstractState)
  (cur_tid owner_tid : TaskID) (owner_t : TaskAbstractState)
  (wait_eid : EventID) (wait_e : OSEventAbstractState) : Prop :=
  exists m owner_orig pty,
    mutex_e.(eventType) = OS_EVENT_TYPE_MUTEX /\
    mutex_e.(mutexFields) = Some m /\
    m.(mfOwner) = Some owner_tid /\
    m.(mfOwnerOrigPrio) = Some owner_orig /\
    mutex_pend_nonrecursive_prop mutex_e cur_tid /\
    tskSt.(inUsedTaskStates) owner_tid = Some owner_t /\
    ~ In owner_tid schedSt.(readyList) /\
    (task_non_suspension_bits owner_t.(stat)) = task_pend_mask pty /\
    owner_t.(eventPtr) = Some wait_eid /\
    owner_t.(eventMultiWaitEvents) = [] /\
    owner_t.(eventMultiRdy) = None /\
    wait_eid <> mutex_eid /\
    evSt.(inUsedEventStates) wait_eid = Some wait_e /\
    event_type_to_pend_type wait_e.(eventType) = Some pty /\
    In owner_tid wait_e.(waitList) /\
    is_effectively_ready owner_t.(stat) owner_t.(dly) = false.

(* The remaining non-ready source path has no OSTCBEventPtr (for example a
   delayed, suspended, or flag-pending owner), so no event bitmap is moved. *)
Definition mutex_pend_owner_dormant_prop
  (mutex_e : OSEventAbstractState) (tskSt : Glob_TaskAbstractState)
  (schedSt : SchedAbstractState)
  (cur_tid owner_tid : TaskID) (owner_t : TaskAbstractState) : Prop :=
  exists m owner_orig,
    mutex_e.(eventType) = OS_EVENT_TYPE_MUTEX /\
    mutex_e.(mutexFields) = Some m /\
    m.(mfOwner) = Some owner_tid /\
    m.(mfOwnerOrigPrio) = Some owner_orig /\
    mutex_pend_nonrecursive_prop mutex_e cur_tid /\
    tskSt.(inUsedTaskStates) owner_tid = Some owner_t /\
    ~ In owner_tid schedSt.(readyList) /\
    owner_t.(eventPtr) = None /\
    owner_t.(eventMultiWaitEvents) = [] /\
    owner_t.(eventMultiRdy) = None /\
    is_effectively_ready owner_t.(stat) owner_t.(dly) = false.

(** Priority demand in the separately selected nested-priority repair.
    This follows the two actual Pend branches, including demand masked by a
    different mutex. It is a raw branch function: no invariant is a guard. *)
Inductive MutexDemandAction : Type :=
| NoMutexDemand
| RecordMutexDemand
| PromoteMutexOwner.

Definition mutex_pend_demand_action (base current waiter ceiling : Priority)
  : MutexDemandAction :=
  if (Z.ltb ceiling current && Z.ltb waiter base)%bool then PromoteMutexOwner
  else if (Z.ltb waiter base && Z.ltb ceiling base)%bool then RecordMutexDemand
  else NoMutexDemand.

Definition mutex_demand_table (action : MutexDemandAction)
  (table : Priority -> PrioTblEntry) (owner : TaskID) (ceiling : Priority)
  : Priority -> PrioTblEntry :=
  match action with
  | NoMutexDemand => table
  | RecordMutexDemand | PromoteMutexOwner => update_prio_tbl table ceiling (PTTask owner)
  end.

Definition mutex_demand_priority (action : MutexDemandAction)
  (current ceiling : Priority) : Priority :=
  match action with PromoteMutexOwner => ceiling | _ => current end.

Lemma mutex_pend_demand_preserves_priority_extrema :
  forall sg table owner base current waiter ceiling,
  task_base_priority sg table owner base ->
  task_effective_priority sg table owner current ->
  task_priority_in_range sg ceiling ->
  let action := mutex_pend_demand_action base current waiter ceiling in
  task_base_priority sg (mutex_demand_table action table owner ceiling) owner base /\
  task_effective_priority sg (mutex_demand_table action table owner ceiling) owner
    (mutex_demand_priority action current ceiling).
Proof.
  intros sg table owner base current waiter ceiling Hbase Hcurrent Hceiling.
  pose proof (task_effective_priority_le_base sg table owner base current Hbase Hcurrent) as Hbound.
  unfold mutex_pend_demand_action.
  destruct (Z.ltb ceiling current && Z.ltb waiter base)%bool eqn:Hpromote.
  - apply andb_true_iff in Hpromote; destruct Hpromote as [Hlower Hwaiter].
    apply Z.ltb_lt in Hlower; cbn [mutex_demand_table mutex_demand_priority]; split.
    + apply task_alias_add_preserves_base_priority; try assumption; lia.
    + pose proof (task_alias_add_effective_priority sg table owner current ceiling Hcurrent Hceiling) as Hmin.
      rewrite Z.min_r in Hmin by lia; exact Hmin.
  - destruct (Z.ltb waiter base && Z.ltb ceiling base)%bool eqn:Hrecord.
    + apply andb_true_iff in Hrecord; destruct Hrecord as [Hwaiter Hlower].
      rewrite Hwaiter, andb_true_r in Hpromote; apply Z.ltb_ge in Hpromote.
      apply Z.ltb_lt in Hlower; cbn [mutex_demand_table mutex_demand_priority]; split.
      * apply task_alias_add_preserves_base_priority; try assumption; lia.
      * pose proof (task_alias_add_effective_priority sg table owner current ceiling Hcurrent Hceiling) as Hmin.
        rewrite Z.min_l in Hmin by lia; exact Hmin.
    + exact (conj Hbase Hcurrent).
Qed.

(** Outstanding demand is represented by a real PTTask slot, not by the
    current wait list. Timeout therefore need not erase demand. The maximum
    alias identifies the permanent slot, and all additional slots are lower
    enabled ceilings of mutexes currently owned by the same task. *)
Definition mutex_priority_alias_consistency (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (events : Glob_EventAbstractState) : Prop :=
  forall tid t, tasks.(inUsedTaskStates) tid = Some t -> exists base,
    task_base_priority sg tasks.(prioTbl) tid base /\
    task_effective_priority sg tasks.(prioTbl) tid t.(curPrio) /\
    (forall p, task_priority_alias sg tasks.(prioTbl) tid p ->
      p = base \/ (p < base /\ mutex_task_enabled_pcp_claim sg events tid p)).

(** A live owner's acquisition snapshot is bounded by its permanent slot.
    An enabled PCP cannot be that permanent slot: acquisition starts from a
    reserved ceiling, and inheritance adds only lower aliases. This is a
    source lifecycle invariant, not another table cell or a release guard.
    In particular PCP_LOWER does not imply [PCP < base]. *)
Definition mutex_owner_snapshot_in_range (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (events : Glob_EventAbstractState) : Prop :=
  forall mid e m owner,
    events.(inUsedEventStates) mid = Some e -> e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m -> m.(mfOwner) = Some owner ->
    exists t base snapshot,
      tasks.(inUsedTaskStates) owner = Some t /\
      task_base_priority sg tasks.(prioTbl) owner base /\
      m.(mfOwnerOrigPrio) = Some snapshot /\
      task_priority_in_range sg snapshot /\ snapshot <= base /\
      ~ In owner e.(waitList) /\
      (mutex_pcp_enabled sg m -> m.(mfPCP) <> base).

Lemma mutex_owner_pcp_ne_base : forall sg tasks events mid e m owner base,
  mutex_owner_snapshot_in_range sg tasks events ->
  events.(inUsedEventStates) mid = Some e -> e.(eventType) = OS_EVENT_TYPE_MUTEX ->
  e.(mutexFields) = Some m -> m.(mfOwner) = Some owner ->
  task_base_priority sg tasks.(prioTbl) owner base ->
  mutex_pcp_enabled sg m -> m.(mfPCP) <> base.
Proof.
  intros sg tasks events mid e m owner base Hsnapshots He Htype Hm Howner Hbase Henabled.
  destruct (Hsnapshots mid e m owner He Htype Hm Howner)
    as [t [permanent [snapshot [_ [Hpermanent [_ [_ [_ [_ Hneq]]]]]]]]].
  pose proof (task_base_priority_unique sg tasks.(prioTbl) owner permanent base
    Hpermanent Hbase) as Ebase; subst permanent; exact (Hneq Henabled).
Qed.

Lemma mutex_priority_alias_consistency_current_registered : forall sg tasks events,
  mutex_priority_alias_consistency sg tasks events -> task_current_prio_registered tasks.
Proof.
  intros sg tasks events Hconsistent tid t Hget.
  destruct (Hconsistent tid t Hget) as [base [_ [Heffective _]]].
  exact (proj2 (proj1 Heffective)).
Qed.

Lemma mutex_priority_alias_consistency_priority_unique : forall sg tasks events,
  mutex_priority_alias_consistency sg tasks events -> task_priority_unique tasks.
Proof.
  intros; apply task_registration_implies_priority_unique.
  eapply mutex_priority_alias_consistency_current_registered; eauto.
Qed.

(** A task without a held mutex has only its ordinary priority slot.
    This is a consequence of the existing alias protocol, not a new
    runtime test in OSTaskDel or a restriction on out-of-array map keys. *)
Lemma mutex_unowned_task_alias_eq_current : forall sg tasks events tid t p,
  mutex_priority_alias_consistency sg tasks events -> tasks.(inUsedTaskStates) tid = Some t ->
  (forall mid e m, events.(inUsedEventStates) mid = Some e ->
     e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) <> Some tid) ->
  task_priority_alias sg tasks.(prioTbl) tid p -> p = t.(curPrio).
Proof.
  intros sg tasks events tid t p Hconsistent Ht Hnotowner Hp.
  destruct (Hconsistent tid t Ht) as [base [_ [Hcurrent Hclaims]]].
  assert (Honly : forall q, task_priority_alias sg tasks.(prioTbl) tid q -> q = base).
  { intros q Hq; destruct (Hclaims q Hq) as [Heq|[_ Hclaim]]; [exact Heq|].
    destruct Hclaim as [mid [e [m [He [Htype [Hm [Howner _]]]]]]].
    exfalso; exact (Hnotowner mid e m He Htype Hm Howner). }
  pose proof (Honly p Hp); pose proof (Honly t.(curPrio) (proj1 Hcurrent)); congruence.
Qed.

Lemma mutex_priority_alias_consistency_ext : forall sg tasks tasks' events events',
  tasks'.(inUsedTaskStates) = tasks.(inUsedTaskStates) -> tasks'.(prioTbl) = tasks.(prioTbl) ->
  (forall tid p, mutex_task_enabled_pcp_claim sg events tid p ->
     mutex_task_enabled_pcp_claim sg events' tid p) ->
  mutex_priority_alias_consistency sg tasks events ->
  mutex_priority_alias_consistency sg tasks' events'.
Proof.
  intros sg tasks tasks' events events' Hused Htable Hclaims Hconsistent tid t Hget.
  rewrite Hused in Hget; destruct (Hconsistent tid t Hget) as [base [Hbase [Heffective Halias]]].
  exists base; rewrite Htable; split; [exact Hbase|split; [exact Heffective|]].
  intros p Hp; destruct (Halias p Hp) as [->|[Hless Hclaim]]; [left; reflexivity|].
  right; split; [exact Hless|apply Hclaims; exact Hclaim].
Qed.

(** Post overwrites the released ceiling with PTReserved; Delete writes
    PTFree. Removing a nonpermanent alias preserves the permanent slot and
    cannot increase the owner's scheduling urgency. This lemma covers both
    source writes and does not assume the released lock is the last acquired. *)
Lemma mutex_release_slot_preserves_base_priority : forall sg table owner base ceiling entry,
  task_base_priority sg table owner base -> ceiling <> base ->
  (entry = PTReserved \/ entry = PTFree) ->
  task_base_priority sg (update_prio_tbl table ceiling entry) owner base.
Proof.
  intros sg table owner base ceiling entry Hbase Hneq [Hentry | Hentry]; subst entry;
    apply task_alias_remove_preserves_base_priority; try assumption; try lia; discriminate.
Qed.

Lemma mutex_owner_release_preserves_base_priority :
  forall sg tasks events mid e m owner base entry,
  mutex_owner_snapshot_in_range sg tasks events ->
  events.(inUsedEventStates) mid = Some e -> e.(eventType) = OS_EVENT_TYPE_MUTEX ->
  e.(mutexFields) = Some m -> m.(mfOwner) = Some owner ->
  task_base_priority sg tasks.(prioTbl) owner base ->
  mutex_pcp_enabled sg m -> (entry = PTReserved \/ entry = PTFree) ->
  task_base_priority sg (update_prio_tbl tasks.(prioTbl) m.(mfPCP) entry) owner base.
Proof.
  intros sg tasks events mid e m owner base entry Hsnapshots He Htype Hm Howner
    Hbase Henabled Hentry.
  apply mutex_release_slot_preserves_base_priority; [exact Hbase| |exact Hentry].
  exact (mutex_owner_pcp_ne_base sg tasks events mid e m owner base
    Hsnapshots He Htype Hm Howner Hbase Henabled).
Qed.

Lemma mutex_release_slot_effective_priority_monotone :
  forall sg table owner before after ceiling entry,
  task_effective_priority sg table owner before ->
  (entry = PTReserved \/ entry = PTFree) ->
  task_effective_priority sg (update_prio_tbl table ceiling entry) owner after -> before <= after.
Proof.
  intros sg table owner before after ceiling entry Hbefore [Hentry | Hentry] Hafter; subst entry;
    eapply task_alias_remove_effective_priority_monotone; eauto; discriminate.
Qed.

Lemma mutex_priority_alias_consistency_update_task : forall sg tasks events tid old new,
  tasks.(inUsedTaskStates) tid = Some old -> new.(curPrio) = old.(curPrio) ->
  mutex_priority_alias_consistency sg tasks events ->
  mutex_priority_alias_consistency sg (glob_task_set_usedtask tasks tid new) events.
Proof.
  intros sg tasks events tid old new Hold Hprio Hconsistent slot t Ht.
  simpl in Ht; destruct (Z.eqb slot tid) eqn:E.
  - apply Z.eqb_eq in E; subst slot; injection Ht as Heq; subst t.
    destruct (Hconsistent tid old Hold) as [base [Hb [He Ha]]].
    exists base; simpl; rewrite Hprio; auto.
  - exact (Hconsistent slot t Ht).
Qed.

Lemma mutex_owner_snapshot_update_task : forall sg tasks events tid old new,
  tasks.(inUsedTaskStates) tid = Some old ->
  mutex_owner_snapshot_in_range sg tasks events ->
  mutex_owner_snapshot_in_range sg (glob_task_set_usedtask tasks tid new) events.
Proof.
  intros sg tasks events tid old new Hold Hconsistent mid e m owner He Htype Hm Howner.
  destruct (Hconsistent mid e m owner He Htype Hm Howner)
    as [t [base [snapshot [Ht Hrest]]]].
  destruct (proj2 (glob_task_set_usedtask_live_iff tasks tid old new owner Hold)
    (ex_intro _ t Ht)) as [after Hafter].
  exists after, base, snapshot; split; [exact Hafter|exact Hrest].
Qed.
