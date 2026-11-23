Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Import ListNotations.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Ordered guards in the selected OSMutexPend source, before Save.
    In particular a free ECB (type 0) takes the type-error return; no
    runnable-task or live-Mutex condition is attached to that branch. *)
Definition mutex_pend_precritical_error
  (pointer type_byte nesting locked : Z) : option OSErrCode :=
  if Z.eqb pointer 0 then Some OS_ERR_PEVENT_NULL
  else if negb (Z.eqb type_byte 4) then Some OS_ERR_EVENT_TYPE
  else if Z.ltb 0 nesting then Some OS_ERR_PEND_ISR
  else if Z.ltb 0 locked then Some OS_ERR_PEND_LOCKED
  else None.

Lemma mutex_pend_precritical_null : forall ty nesting locked,
  mutex_pend_precritical_error 0 ty nesting locked = Some OS_ERR_PEVENT_NULL.
Proof. reflexivity. Qed.

Lemma mutex_pend_precritical_type : forall pointer ty nesting locked,
  pointer <> 0 -> ty <> 4 ->
  mutex_pend_precritical_error pointer ty nesting locked = Some OS_ERR_EVENT_TYPE.
Proof.
  intros * Hpointer Htype; unfold mutex_pend_precritical_error.
  rewrite (proj2 (Z.eqb_neq _ _) Hpointer), (proj2 (Z.eqb_neq _ _) Htype); reflexivity.
Qed.

Lemma mutex_pend_precritical_free : forall pointer nesting locked,
  pointer <> 0 ->
  mutex_pend_precritical_error pointer 0 nesting locked = Some OS_ERR_EVENT_TYPE.
Proof. intros; apply mutex_pend_precritical_type; lia. Qed.

Lemma mutex_pend_precritical_isr : forall pointer nesting locked,
  pointer <> 0 -> 0 < nesting ->
  mutex_pend_precritical_error pointer 4 nesting locked = Some OS_ERR_PEND_ISR.
Proof.
  intros * Hpointer Hnesting; unfold mutex_pend_precritical_error.
  rewrite (proj2 (Z.eqb_neq _ _) Hpointer), (proj2 (Z.ltb_lt _ _) Hnesting); reflexivity.
Qed.

Lemma mutex_pend_precritical_locked : forall pointer nesting locked,
  pointer <> 0 -> nesting <= 0 -> 0 < locked ->
  mutex_pend_precritical_error pointer 4 nesting locked = Some OS_ERR_PEND_LOCKED.
Proof.
  intros * Hpointer Hnesting Hlocked; unfold mutex_pend_precritical_error.
  rewrite (proj2 (Z.eqb_neq _ _) Hpointer), (proj2 (Z.ltb_ge _ _) Hnesting),
    (proj2 (Z.ltb_lt _ _) Hlocked); reflexivity.
Qed.

Lemma mutex_pend_precritical_continues_iff : forall pointer ty nesting locked,
  mutex_pend_precritical_error pointer ty nesting locked = None <->
  pointer <> 0 /\ ty = 4 /\ nesting <= 0 /\ locked <= 0.
Proof.
  intros; unfold mutex_pend_precritical_error.
  destruct (Z.eqb pointer 0) eqn:Ep; [apply Z.eqb_eq in Ep|apply Z.eqb_neq in Ep];
    destruct (Z.eqb ty 4) eqn:Et; [apply Z.eqb_eq in Et|apply Z.eqb_neq in Et|
      apply Z.eqb_eq in Et|apply Z.eqb_neq in Et];
    destruct (Z.ltb 0 nesting) eqn:En; [apply Z.ltb_lt in En|apply Z.ltb_ge in En|
      apply Z.ltb_lt in En|apply Z.ltb_ge in En|apply Z.ltb_lt in En|apply Z.ltb_ge in En|
      apply Z.ltb_lt in En|apply Z.ltb_ge in En];
    destruct (Z.ltb 0 locked) eqn:El;
    (apply Z.ltb_lt in El || apply Z.ltb_ge in El); cbn;
    split; intros; try discriminate; intuition lia.
Qed.

(** Only the fields written by the inheritance prefix change. Reuse the
    native five-field TCB updater; this function updates the EXISTING task
    record, not a new ghost state. The physical priority table records a
    demand even when another Mutex already supplies a higher priority. *)
Definition mutex_pend_demand_tasks (tasks : Glob_TaskAbstractState)
  (owner : TaskID) (node : TaskAbstractState) (action : MutexDemandAction)
  (ceiling : Priority) : Glob_TaskAbstractState :=
  let nodes := match action with
    | PromoteMutexOwner => glob_task_set_usedtask tasks owner (mutex_priority_task node ceiling)
    | _ => tasks
    end in
  {| inUsedTaskStates := nodes.(inUsedTaskStates);
     unUsedTaskStates := nodes.(unUsedTaskStates);
     tcbListHead := nodes.(tcbListHead);
     prioTbl := mutex_demand_table action tasks.(prioTbl) owner ceiling;
     taskRegNextID := nodes.(taskRegNextID);
     parkedTaskStacks := nodes.(parkedTaskStacks);
     taskLifecycle := nodes.(taskLifecycle);
     taskCount := nodes.(taskCount) |}.

Definition mutex_pend_owner_was_ready (before : UCOS2_Verify_State)
  (node : TaskAbstractState) : bool :=
  mutex_priority_was_ready
    (sched_row_values before.(TskState) before.(SchedState).(readyList))
    (tcb_y_of_prio node.(curPrio)) (tcb_bit_x_of_prio node.(curPrio)).

Definition mutex_pend_promoted_ready (sg : StableGlobVars)
  (before : UCOS2_Verify_State) (owner : TaskID) (node : TaskAbstractState)
  (ceiling : Priority) : list TaskID :=
  if mutex_pend_owner_was_ready before node then
    insert_sorted_by
      (sched_task_key sg (mutex_pend_demand_tasks before.(TskState) owner node
        PromoteMutexOwner ceiling)) owner (remove_Z_eqb owner before.(SchedState).(readyList))
  else before.(SchedState).(readyList).

(** Keep the defensive owner-waits-on-another-Event branch of the actual
    source. Its event pointer must denote real storage; a missing lookup
    has no transition here, rather than being invented as a C no-op.
    The selected owner-use protocol can separately establish that this
    branch is unreachable for its admitted clients. *)
Definition mutex_pend_promoted_events (sg : StableGlobVars)
  (before : UCOS2_Verify_State) (owner : TaskID) (node : TaskAbstractState)
  (ceiling : Priority) (events : Glob_EventAbstractState) : Prop :=
  if mutex_pend_owner_was_ready before node then events = before.(EventState)
  else match node.(eventPtr) with
  | None => events = before.(EventState)
  | Some eid => exists old,
      before.(EventState).(inUsedEventStates) eid = Some old /\
      events = update_event_field_raw before.(EventState) eid
        (event_set_wait_list old
          (insert_sorted_by
            (wait_prio_key sg (mutex_pend_demand_tasks before.(TskState) owner node
              PromoteMutexOwner ceiling)) owner (remove_Z_eqb owner old.(waitList))))
  end.

Definition mutex_pend_inherit_step (sg : StableGlobVars)
  (before : UCOS2_Verify_State) (owner : TaskID) (node : TaskAbstractState)
  (base waiter ceiling : Priority) (after : UCOS2_Verify_State) : Prop :=
  match mutex_pend_inherit_action sg.(osPrioMutexCeilDis) base node.(curPrio) waiter ceiling with
  | NoMutexDemand => after = before
  | RecordMutexDemand => after = replace_TskS
      (mutex_pend_demand_tasks before.(TskState) owner node RecordMutexDemand ceiling) before
  | PromoteMutexOwner => exists events,
      mutex_pend_promoted_events sg before owner node ceiling events /\
      after = replace_EventS events
        (replace_SchedS (sched_set_ready before.(SchedState)
          (mutex_pend_promoted_ready sg before owner node ceiling))
          (replace_TskS
            (mutex_pend_demand_tasks before.(TskState) owner node PromoteMutexOwner ceiling) before))
  end.

Lemma mutex_pend_promoted_events_deterministic : forall sg before owner node ceiling a b,
  mutex_pend_promoted_events sg before owner node ceiling a ->
  mutex_pend_promoted_events sg before owner node ceiling b -> a = b.
Proof.
  intros sg before owner node ceiling a b; unfold mutex_pend_promoted_events.
  destruct (mutex_pend_owner_was_ready before node); [congruence|].
  destruct node.(eventPtr) as [eid|]; [|congruence].
  intros [old [Hold ->]] [other [Hother ->]].
  assert (other = old) by congruence; subst; reflexivity.
Qed.

Lemma mutex_pend_inherit_step_deterministic : forall sg before owner node base waiter ceiling a b,
  mutex_pend_inherit_step sg before owner node base waiter ceiling a ->
  mutex_pend_inherit_step sg before owner node base waiter ceiling b -> a = b.
Proof.
  intros sg before owner node base waiter ceiling a b; unfold mutex_pend_inherit_step.
  destruct (mutex_pend_inherit_action _ _ _ _ _); try congruence.
  intros [ea [Ha ->]] [eb [Hb ->]].
  assert (ea = eb) by (eapply mutex_pend_promoted_events_deterministic; eassumption).
  subst; reflexivity.
Qed.

Lemma mutex_pend_inherit_preserves_scheduler_caches :
  forall sg before owner node base waiter ceiling after,
  mutex_pend_inherit_step sg before owner node base waiter ceiling after ->
  after.(SchedState).(curTaskID) = before.(SchedState).(curTaskID) /\
  after.(SchedState).(curSchedPrio) = before.(SchedState).(curSchedPrio) /\
  after.(SchedState).(highRdyTid) = before.(SchedState).(highRdyTid) /\
  after.(SchedState).(highRdyPrio) = before.(SchedState).(highRdyPrio) /\
  after.(SchedState).(ctxSwCtr) = before.(SchedState).(ctxSwCtr).
Proof.
  intros sg before owner node base waiter ceiling after; unfold mutex_pend_inherit_step.
  destruct (mutex_pend_inherit_action _ _ _ _ _).
  - intros ->; repeat split; reflexivity.
  - intros ->; repeat split; reflexivity.
  - intros [events [_ ->]]; repeat split; reflexivity.
Qed.

Lemma mutex_pend_record_demand_preserves_task_map : forall tasks owner node ceiling,
  (mutex_pend_demand_tasks tasks owner node RecordMutexDemand ceiling).(inUsedTaskStates) =
    tasks.(inUsedTaskStates).
Proof. reflexivity. Qed.

(** Immediate acquisition writes the owner and acquisition-time priority
    BEFORE deciding PCP_LOWER. That error therefore still returns ownership.
    It is distinct from the no-change precritical errors. *)
Definition mutex_pend_acquire_error (sg : StableGlobVars)
  (ceiling priority : Priority) : OSErrCode :=
  if (negb (Z.eqb ceiling sg.(osPrioMutexCeilDis)) && Z.leb priority ceiling)%bool
  then OS_ERR_PCP_LOWER else OS_ERR_NONE.

Inductive MutexPendStart : Type :=
| MutexPendAcquired (code : OSErrCode)
| MutexPendWaiting (tid : TaskID) (generation : nat).

(** End of the FIRST protected interval, before Restore/Sched. The caller's
    Stat/StatPend/Dly writes and the real EventTaskWait are represented by
    the existing generic Event transformer with [PendMutex]. *)
Definition mutex_pend_first_critical (sg : StableGlobVars) (eid : EventID) (timeout : Z)
  : program UCOS2_Verify_State MutexPendStart :=
  fun before result after => exists event mutex tid caller,
    before.(EventState).(inUsedEventStates) eid = Some event /\
    event.(eventType) = OS_EVENT_TYPE_MUTEX /\ event.(mutexFields) = Some mutex /\
    before.(SchedState).(curTaskID) = Some tid /\
    before.(TskState).(inUsedTaskStates) tid = Some caller /\
    match mutex.(mfOwner) with
    | None =>
        result = MutexPendAcquired (mutex_pend_acquire_error sg mutex.(mfPCP) caller.(curPrio)) /\
        after = replace_EventS (owner_acquire_update before.(EventState) eid event mutex
          tid caller.(curPrio)) before
    | Some owner => exists inherited current_event current_caller,
        ((mutex.(mfPCP) = sg.(osPrioMutexCeilDis) /\ inherited = before) \/
         (mutex.(mfPCP) <> sg.(osPrioMutexCeilDis) /\ exists node base,
           before.(TskState).(inUsedTaskStates) owner = Some node /\
           task_base_priority sg before.(TskState).(prioTbl) owner base /\
           mutex_pend_inherit_step sg before owner node base caller.(curPrio) mutex.(mfPCP) inherited)) /\
        inherited.(EventState).(inUsedEventStates) eid = Some current_event /\
        inherited.(TskState).(inUsedTaskStates) tid = Some current_caller /\
        result = MutexPendWaiting tid current_caller.(taskGeneration) /\
        after = event_pend_state sg inherited eid current_event tid current_caller PendMutex timeout
    end.

(** The selected PendMutex suffix has exactly the same switch, timeout
    removal and cleanup stores as the already checked SemPend suffix. Its
    existing semantic relation is primitive-independent: it does not
    assume a Sem type or change a semaphore counter. Reuse it directly,
    retaining success/abort after deletion and timeout registration. *)
Definition mutex_pend_resume_critical := sem_pend_resume_critical.

Lemma mutex_pend_resume_preserves_validity : forall sg before eid tid node result after,
  UCOS2_state_inv sg before -> before.(SchedState).(curTaskID) = Some tid ->
  before.(TskState).(inUsedTaskStates) tid = Some node ->
  sem_pend_resume_registration eid node -> In tid before.(SchedState).(readyList) ->
  mutex_pend_resume_critical sg eid before result after -> UCOS2_state_inv sg after.
Proof. exact sem_pend_resume_critical_preserves_validity. Qed.

(** The masked-demand branch writes just the real ceiling slot.  A lower
    effective priority can already be supplied by another held Mutex;
    retaining this demand must not move that task or its ready bit. *)
Lemma mutex_pend_ceiling_slot_owner : forall sg before eid event mutex owner,
  cross_module_consistency sg before ->
  before.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  before.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved \/
  before.(TskState).(prioTbl) mutex.(mfPCP) = PTTask owner.
Proof.
  intros sg before eid event mutex owner
    [_ [_ [_ [Hprotocol _]]]] He Htype Hm Ho Henabled.
  destruct (Hprotocol eid event mutex He Htype Hm) as [_ [_ [Hdisabled|[_ Hslot]]]].
  - unfold mutex_pcp_enabled in Henabled; contradiction.
  - destruct Hslot as [Hreserved|[tid [Htid Htable]]]; [left; exact Hreserved|].
    right; assert (tid = owner) by congruence; subst; exact Htable.
Qed.

Lemma mutex_pend_record_priority_alias_consistency :
  forall sg tasks events owner node base ceiling,
  tasks.(inUsedTaskStates) owner = Some node ->
  task_base_priority sg tasks.(prioTbl) owner base ->
  node.(curPrio) <= ceiling -> ceiling < base -> task_priority_in_range sg ceiling ->
  (tasks.(prioTbl) ceiling = PTReserved \/ tasks.(prioTbl) ceiling = PTTask owner) ->
  mutex_task_enabled_pcp_claim sg events owner ceiling ->
  mutex_priority_alias_consistency sg tasks events ->
  mutex_priority_alias_consistency sg
    (mutex_pend_demand_tasks tasks owner node RecordMutexDemand ceiling) events.
Proof.
  intros sg tasks events owner node base ceiling Hnode Hbase Hcurrent Hless Hrange
    Hslot Hclaim Halias tid t Ht.
  change (tasks.(inUsedTaskStates) tid = Some t) in Ht.
  destruct (Halias tid t Ht) as [permanent [Hpermanent [Heffective Hclaims]]].
  cbn [mutex_pend_demand_tasks mutex_demand_table inUsedTaskStates prioTbl].
  destruct (Z.eq_dec tid owner) as [->|Hother].
  - rewrite Hnode in Ht; injection Ht as E; subst t.
    assert (permanent = base) by (eapply task_base_priority_unique; eassumption).
    subst permanent; exists base; split.
    + apply task_alias_add_preserves_base_priority; try assumption; lia.
    + split.
      * pose proof (task_alias_add_effective_priority sg tasks.(prioTbl)
          owner node.(curPrio) ceiling Heffective Hrange) as Hmin.
        rewrite Z.min_l in Hmin by exact Hcurrent; exact Hmin.
      * intros p Hp; apply task_priority_alias_add_iff in Hp; [|exact Hrange].
        destruct Hp as [->|Hp]; [right; split; assumption|apply Hclaims; exact Hp].
  - assert (Hforeign : forall p,
      task_priority_alias sg tasks.(prioTbl) tid p <->
      task_priority_alias sg (update_prio_tbl tasks.(prioTbl) ceiling (PTTask owner)) tid p).
    { intro p; symmetry; apply task_priority_alias_foreign_write_iff.
      - destruct Hslot as [Hslot|Hslot]; rewrite Hslot; congruence.
      - congruence. }
    exists permanent; split.
    + eapply task_base_priority_alias_ext; [exact Hforeign|exact Hpermanent].
    + split.
      * eapply task_effective_priority_alias_ext; [exact Hforeign|exact Heffective].
      * intros p Hp; apply Hclaims; apply Hforeign; exact Hp.
Qed.

Lemma mutex_pend_record_cross_module_consistency :
  forall sg before eid event mutex owner node base,
  cross_module_consistency sg before ->
  before.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  before.(TskState).(inUsedTaskStates) owner = Some node ->
  task_base_priority sg before.(TskState).(prioTbl) owner base ->
  node.(curPrio) <= mutex.(mfPCP) -> mutex.(mfPCP) < base ->
  cross_module_consistency sg (replace_TskS
    (mutex_pend_demand_tasks before.(TskState) owner node RecordMutexDemand mutex.(mfPCP)) before).
Proof.
  intros sg before eid event mutex owner node base Hcross He Htype Hm Ho Henabled
    Hnode Hbase Hcurrent Hless.
  pose proof Hcross as [[Hcreator [Hslots Halias]]
    [Hsnapshot [Hwait [Hprotocol [Hunique [Hflags Htimer]]]]]].
  pose proof (mutex_pend_ceiling_slot_owner sg before eid event mutex owner
    Hcross He Htype Hm Ho Henabled) as Hslot.
  assert (Hrange : task_priority_in_range sg mutex.(mfPCP)).
  { destruct (Hprotocol eid event mutex He Htype Hm) as [Hpcp _].
    unfold valid_mutex_pcp in Hpcp; unfold mutex_pcp_enabled in Henabled.
    unfold task_priority_in_range; intuition lia. }
  assert (Hclaim : mutex_task_enabled_pcp_claim sg before.(EventState) owner mutex.(mfPCP)).
  { exists eid, event, mutex; repeat split; assumption || reflexivity. }
  assert (HbaseFrame : forall tid permanent,
    task_base_priority sg before.(TskState).(prioTbl) tid permanent ->
    task_base_priority sg (update_prio_tbl before.(TskState).(prioTbl)
      mutex.(mfPCP) (PTTask owner)) tid permanent).
  { intros tid permanent Hb; destruct (Z.eq_dec tid owner) as [->|Hother].
    - assert (permanent = base) by (eapply task_base_priority_unique; eassumption).
      subst; apply task_alias_add_preserves_base_priority; try assumption; lia.
    - eapply task_base_priority_alias_ext; [|exact Hb].
      intro p; symmetry; apply task_priority_alias_foreign_write_iff;
        [destruct Hslot as [Hs|Hs]; rewrite Hs; congruence|congruence]. }
  split.
  - split; [exact Hcreator|]. split.
    + intros p Hp; cbn [replace_TskS TskState EventState mutex_pend_demand_tasks
        mutex_demand_table prioTbl inUsedTaskStates taskLifecycle].
      unfold update_prio_tbl; destruct (Z.eq_dec p mutex.(mfPCP)) as [->|Hne].
      * exists node; exact Hnode.
      * exact (Hslots p Hp).
    + eapply mutex_pend_record_priority_alias_consistency; eassumption.
  - split.
    + intros mid e m tid Hget Hty Hfields Howner.
      destruct (Hsnapshot mid e m tid Hget Hty Hfields Howner)
        as [t [permanent [snapshot [Ht [Hb Hrest]]]]].
      exists t, permanent, snapshot; split; [exact Ht|].
      split; [apply HbaseFrame; exact Hb|exact Hrest].
    + split; [exact Hwait|]. split.
      * intros mid e m Hget Hty Hfields.
        change (before.(EventState).(inUsedEventStates) mid = Some e) in Hget.
        destruct (Hprotocol mid e m Hget Hty Hfields) as [Hpcp [Howner Hcell]].
        split; [exact Hpcp|]. split; [exact Howner|].
        destruct Hcell as [Hdisabled|[Henabled' Hcell]]; [left; exact Hdisabled|].
        right; split; [exact Henabled'|].
        cbn [replace_TskS TskState mutex_pend_demand_tasks mutex_demand_table prioTbl].
        destruct (Z.eq_dec m.(mfPCP) mutex.(mfPCP)) as [Epcp|Hne].
        -- assert (mid = eid) by (eapply Hunique; eassumption).
           subst mid; assert (e = event) by congruence; subst e.
           assert (m = mutex) by congruence; subst m.
           right; exists owner; split; [exact Ho|apply update_prio_tbl_same].
        -- rewrite update_prio_tbl_other by exact Hne; exact Hcell.
      * split; [exact Hunique|]. split; [exact Hflags|exact Htimer].
Qed.

Lemma mutex_pend_record_preserves_validity :
  forall sg before eid event mutex owner node base,
  UCOS2_state_inv sg before ->
  before.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  before.(TskState).(inUsedTaskStates) owner = Some node ->
  task_base_priority sg before.(TskState).(prioTbl) owner base ->
  node.(curPrio) <= mutex.(mfPCP) -> mutex.(mfPCP) < base ->
  UCOS2_state_inv sg (replace_TskS
    (mutex_pend_demand_tasks before.(TskState) owner node RecordMutexDemand mutex.(mfPCP)) before).
Proof.
  intros sg before eid event mutex owner node base
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus [Hflags
      [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]]]]]]]]]
    He Htype Hm Ho Henabled Hnode Hbase Hcurrent Hless.
  pose proof (mutex_pend_record_cross_module_consistency sg before eid event mutex owner node base
    Hcross He Htype Hm Ho Henabled Hnode Hbase Hcurrent Hless) as HcrossAfter.
  pose proof Hcross as [[Hcreator _] _].
  assert (HliveClaim : exists mid e m,
    before.(EventState).(inUsedEventStates) mid = Some e /\
    e.(eventType) = OS_EVENT_TYPE_MUTEX /\ e.(mutexFields) = Some m /\
    mutex_reserves_priority_slot sg m mutex.(mfPCP)).
  { exists eid, event, mutex; repeat split; assumption || reflexivity. }
  assert (HpendingAfter : pending_mutex_consistency sg
    (mutex_pend_demand_tasks before.(TskState) owner node RecordMutexDemand mutex.(mfPCP))
    before.(EventState)).
  { eapply pending_mutex_consistency_table_transport with (tasks := before.(TskState));
      [|intros; reflexivity|exact Hpending].
    intros p [slot [queue Hlease]].
    cbn [mutex_pend_demand_tasks mutex_demand_table prioTbl].
    apply update_prio_tbl_other; intro E; subst p.
    destruct (Hpending slot mutex.(mfPCP) queue Hlease) as [_ [_ [_ [_ [_ [Hno _]]]]]].
    exact (Hno HliveClaim). }
  split; [exact Hprofile|]. split.
  - destruct Htasks as [Hpool [Hactive [Hfree [Hreservation [Hgeneration
      [Hregistered [Hunique [Hrange Hreuse]]]]]]]].
    split; [exact Hpool|]. split; [exact Hactive|]. split; [exact Hfree|]. split.
    + destruct Hreservation as [Hentries Hdistinct]; split; [|exact Hdistinct].
      intros p reservation Hr; destruct (Hentries p reservation Hr) as [Hp [Hentry Hinv]].
      split; [exact Hp|]. split; [|exact Hinv].
      change (update_prio_tbl before.(TskState).(prioTbl)
        mutex.(mfPCP) (PTTask owner) p = PTReserved).
      rewrite update_prio_tbl_other; [exact Hentry|].
      intro E; subst p; exact (Hcreator mutex.(mfPCP) reservation Hr HliveClaim).
    + split; [exact Hgeneration|]. split.
      * apply mutex_priority_alias_consistency_current_registered with
          (sg := sg) (events := before.(EventState)).
        exact (proj2 (proj2 (proj1 HcrossAfter))).
      * split; [exact Hunique|]. split; [exact Hrange|exact Hreuse].
  - split; [exact Hsched|]. split; [exact Hevents|]. split; [exact HcrossAfter|].
    split; [exact Hidle|]. split; [exact Hstatus|]. split; [exact Hflags|].
    split; [exact Hmemory|]. split; [exact Htimer|]. split; [exact Hstats|].
    split; [exact Hcontrol|]. split; [exact Hnames|]. split; [exact Hreferences|].
    split; [exact Hstacks|exact HpendingAfter].
Qed.

Lemma mutex_pend_record_branch_preserves_validity :
  forall sg before eid event mutex owner node base waiter after,
  UCOS2_state_inv sg before ->
  before.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner ->
  before.(TskState).(inUsedTaskStates) owner = Some node ->
  task_base_priority sg before.(TskState).(prioTbl) owner base ->
  mutex_pend_inherit_action sg.(osPrioMutexCeilDis) base node.(curPrio) waiter mutex.(mfPCP) =
    RecordMutexDemand ->
  mutex_pend_inherit_step sg before owner node base waiter mutex.(mfPCP) after ->
  UCOS2_state_inv sg after.
Proof.
  intros sg before eid event mutex owner node base waiter after Hvalid He Htype Hm Ho
    Hnode Hbase Haction Hstep.
  unfold mutex_pend_inherit_step in Hstep; rewrite Haction in Hstep; subst after.
  apply mutex_pend_inherit_record_iff in Haction.
  destruct Haction as [Henabled [Hcurrent [_ Hless]]].
  eapply mutex_pend_record_preserves_validity; eassumption.
Qed.

Lemma mutex_pend_record_priority_residual_eq : forall sg before owner node ceiling,
  UCOS2_raw_rep_missing_priority_table sg before =
  UCOS2_raw_rep_missing_priority_table sg (replace_TskS
    (mutex_pend_demand_tasks before.(TskState) owner node RecordMutexDemand ceiling) before).
Proof.
  intros; unfold UCOS2_raw_rep_missing_priority_table.
  rewrite (sched_raw_rep_change_task_index sg before.(TskState)
    (mutex_pend_demand_tasks before.(TskState) owner node RecordMutexDemand ceiling)
    before.(SchedState) eq_refl).
  rewrite (UCOS2_raw_rep_missing_task_storage_sched_task_map_frame sg before
    (mutex_pend_demand_tasks before.(TskState) owner node RecordMutexDemand ceiling)
    eq_refl eq_refl).
  reflexivity.
Qed.

(** Consumer at the native [OSTCBPrioTbl[pcp] = ptcb] store in the masked
    branch.  The cell now contains the real owner's address; the residual
    still owns all non-written table entries and every other module byte.
    Its postcondition reconstructs the full invariant, not a historical
    verification slice or an assumed post-state validity premise. *)
Lemma mutex_pend_record_priority_cell_merge :
  forall sg before eid event mutex owner node base,
  UCOS2_state_inv sg before ->
  before.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  before.(TskState).(inUsedTaskStates) owner = Some node ->
  task_base_priority sg before.(TskState).(prioTbl) owner base ->
  node.(curPrio) <= mutex.(mfPCP) -> mutex.(mfPCP) < base ->
  (sg.(g_OSTCBPrioTbl) + mutex.(mfPCP) * sizeof(PTR)) # Ptr |-> task_slot_addr sg owner **
    store_prio_tbl_missing_i sg before.(TskState).(prioTbl) mutex.(mfPCP) **
    UCOS2_raw_rep_missing_priority_table sg before |--
  UCOS2_inv sg (replace_TskS
    (mutex_pend_demand_tasks before.(TskState) owner node RecordMutexDemand mutex.(mfPCP)) before).
Proof.
  intros sg before eid event mutex owner node base Hvalid He Htype Hm Ho Henabled
    Hnode Hbase Hcurrent Hless.
  pose proof (mutex_pend_record_preserves_validity sg before eid event mutex owner node base
    Hvalid He Htype Hm Ho Henabled Hnode Hbase Hcurrent Hless) as Hpost.
  assert (Hp : 0 <= mutex.(mfPCP) < 64).
  { pose proof Hvalid as [_ [_ [_ [_ [Hcross _]]]]].
    destruct Hcross as [_ [_ [_ [Hprotocol _]]]].
    destruct (Hprotocol eid event mutex He Htype Hm) as [Hpcp _].
    pose proof (proj1 (proj1 Hvalid)) as Hsg.
    unfold valid_mutex_pcp in Hpcp; unfold mutex_pcp_enabled in Henabled.
    unfold valid_stable_glob_vars in Hsg; intuition lia. }
  pose proof (store_prio_tbl_merge_updated_cell sg before.(TskState).(prioTbl)
    mutex.(mfPCP) (PTTask owner) Hp) as Hmerge.
  cbn [prio_tbl_entry_to_addr] in Hmerge.
  sep_apply_l_atomic Hmerge.
  unfold UCOS2_inv; rewrite UCOS2_raw_rep_priority_table_equiv.
  rewrite <- mutex_pend_record_priority_residual_eq; entailer!.
Qed.

(** The table-only intermediate state need not satisfy the Mutex minimum
    alias invariant before the five TCB priority stores.  Its ordinary
    task structure is nevertheless preserved, so the existing relocation
    theorem can be reused without assuming a closed intermediate kernel. *)
Lemma mutex_pend_demand_table_preserves_task_range :
  forall sg tasks owner node ceiling,
  task_in_range sg tasks -> tasks.(inUsedTaskStates) owner = Some node ->
  (tasks.(prioTbl) ceiling = PTReserved \/ tasks.(prioTbl) ceiling = PTTask owner) ->
  (forall reservation, tasks.(taskLifecycle).(taskReservations) ceiling <> Some reservation) ->
  task_in_range sg (mutex_pend_demand_tasks tasks owner node RecordMutexDemand ceiling).
Proof.
  intros sg tasks owner node ceiling
    [Hpool [Hactive [Hfree [Hreservations [Hgenerations [Hregistered
      [Hunique [Hpriority Hrest]]]]]]]] Hnode Hslot Hnoreservation.
  split; [exact Hpool|]. split; [exact Hactive|]. split; [exact Hfree|]. split.
  - destruct Hreservations as [Hentries Hdistinct]; split; [|exact Hdistinct].
    intros p reservation Hr; destruct (Hentries p reservation Hr) as [Hp [Hcell Hinv]].
    split; [exact Hp|]. split; [|exact Hinv].
    change (update_prio_tbl tasks.(prioTbl) ceiling (PTTask owner) p = PTReserved).
    rewrite update_prio_tbl_other; [exact Hcell|].
    intro E; subst p; exact (Hnoreservation reservation Hr).
  - split; [exact Hgenerations|]. split.
    + intros tid t Ht; specialize (Hregistered tid t Ht).
      change (update_prio_tbl tasks.(prioTbl) ceiling (PTTask owner) t.(curPrio) = PTTask tid).
      unfold update_prio_tbl; destruct (Z.eq_dec t.(curPrio) ceiling) as [E|Hne]; [|exact Hregistered].
      rewrite E in Hregistered; destruct Hslot as [Hslot|Hslot]; congruence.
    + split; [exact Hunique|]. split; [exact Hpriority|exact Hrest].
Qed.

Lemma mutex_pend_promote_priority_alias_consistency :
  forall sg tasks events owner node base ceiling,
  tasks.(inUsedTaskStates) owner = Some node ->
  task_base_priority sg tasks.(prioTbl) owner base ->
  ceiling < node.(curPrio) -> task_priority_in_range sg ceiling ->
  (tasks.(prioTbl) ceiling = PTReserved \/ tasks.(prioTbl) ceiling = PTTask owner) ->
  mutex_task_enabled_pcp_claim sg events owner ceiling ->
  mutex_priority_alias_consistency sg tasks events ->
  mutex_priority_alias_consistency sg
    (mutex_pend_demand_tasks tasks owner node PromoteMutexOwner ceiling) events.
Proof.
  intros sg tasks events owner node base ceiling Hnode Hbase Hcurrent Hrange
    Hslot Hclaim Halias tid t Ht.
  cbn [mutex_pend_demand_tasks glob_task_set_usedtask inUsedTaskStates] in Ht.
  destruct (Z.eqb tid owner) eqn:E.
  - apply Z.eqb_eq in E; subst tid; injection Ht as Ht; subst t.
    destruct (Halias owner node Hnode) as [permanent [Hpermanent [Heffective Hclaims]]].
    assert (permanent = base) by (eapply task_base_priority_unique; eassumption).
    subst permanent.
    pose proof (task_effective_priority_le_base sg tasks.(prioTbl) owner base node.(curPrio)
      Hbase Heffective) as Hbound.
    cbn [mutex_pend_demand_tasks mutex_demand_table glob_task_set_usedtask prioTbl
      mutex_priority_task curPrio]; exists base; split.
    + apply task_alias_add_preserves_base_priority; try assumption; lia.
    + split.
      * pose proof (task_alias_add_effective_priority sg tasks.(prioTbl) owner node.(curPrio)
          ceiling Heffective Hrange) as Hmin.
        rewrite Z.min_r in Hmin by lia; exact Hmin.
      * intros p Hp; apply task_priority_alias_add_iff in Hp; [|exact Hrange].
        destruct Hp as [->|Hp]; [right; split; [lia|exact Hclaim]|apply Hclaims; exact Hp].
  - apply Z.eqb_neq in E.
    destruct (Halias tid t Ht) as [permanent [Hpermanent [Heffective Hclaims]]].
    assert (Hforeign : forall p,
      task_priority_alias sg tasks.(prioTbl) tid p <->
      task_priority_alias sg (update_prio_tbl tasks.(prioTbl) ceiling (PTTask owner)) tid p).
    { intro p; symmetry; apply task_priority_alias_foreign_write_iff;
        [destruct Hslot as [Hslot|Hslot]; rewrite Hslot; congruence|congruence]. }
    exists permanent; split.
    + eapply task_base_priority_alias_ext; [exact Hforeign|exact Hpermanent].
    + split.
      * eapply task_effective_priority_alias_ext; [exact Hforeign|exact Heffective].
      * intros p Hp; apply Hclaims; apply Hforeign; exact Hp.
Qed.

(** Reuse Del's source-bitmap relocation result for the ready-list part.
    The temporary table-only index supplies its actual destination alias;
    no full invariant is assumed at that intermediate point.  Pend leaves
    every physical scheduler cache unchanged, even when the ready order
    changes. *)
Lemma mutex_pend_promote_sched_in_range : forall sg before owner node ceiling,
  valid_stable_glob_vars sg -> task_in_range sg before.(TskState) ->
  sched_in_range sg before.(TskState) before.(SchedState) ->
  before.(TskState).(inUsedTaskStates) owner = Some node ->
  task_priority_in_range sg ceiling ->
  (before.(TskState).(prioTbl) ceiling = PTReserved \/
   before.(TskState).(prioTbl) ceiling = PTTask owner) ->
  (forall reservation,
    before.(TskState).(taskLifecycle).(taskReservations) ceiling <> Some reservation) ->
  sched_in_range sg
    (mutex_pend_demand_tasks before.(TskState) owner node PromoteMutexOwner ceiling)
    (sched_set_ready before.(SchedState) (mutex_pend_promoted_ready sg before owner node ceiling)).
Proof.
  intros sg before owner node ceiling Hsg Htasks Hsched Hnode Hrange Hslot Hnoreservation.
  set (table_state := replace_TskS
    (mutex_pend_demand_tasks before.(TskState) owner node RecordMutexDemand ceiling) before).
  assert (HtableTasks : task_in_range sg table_state.(TskState)).
  { apply mutex_pend_demand_table_preserves_task_range; assumption. }
  pose proof (mutex_del_relocated_sched_in_range sg table_state ceiling owner node ceiling
    Hsg HtableTasks Hsched Hnode Hrange (update_prio_tbl_same _ _ _)) as Hrelocated.
  split.
  - exact (proj1 Hrelocated).
  - exact (proj2 Hsched).
Qed.

Definition mutex_pend_promoted_state (sg : StableGlobVars)
  (before : UCOS2_Verify_State) (owner : TaskID) (node : TaskAbstractState)
  (ceiling : Priority) : UCOS2_Verify_State :=
  replace_SchedS (sched_set_ready before.(SchedState)
    (mutex_pend_promoted_ready sg before owner node ceiling))
    (replace_TskS
      (mutex_pend_demand_tasks before.(TskState) owner node PromoteMutexOwner ceiling) before).

Lemma mutex_pend_promote_cross_module_consistency :
  forall sg before eid event mutex owner node base,
  cross_module_consistency sg before ->
  before.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  before.(TskState).(inUsedTaskStates) owner = Some node ->
  task_base_priority sg before.(TskState).(prioTbl) owner base ->
  mutex.(mfPCP) < node.(curPrio) ->
  (forall mid e, before.(EventState).(inUsedEventStates) mid = Some e -> ~ In owner e.(waitList)) ->
  cross_module_consistency sg (replace_TskS
    (mutex_pend_demand_tasks before.(TskState) owner node PromoteMutexOwner mutex.(mfPCP)) before).
Proof.
  intros sg before eid event mutex owner node base Hcross He Htype Hm Ho Henabled
    Hnode Hbase Hcurrent Habsent.
  pose proof Hcross as [[Hcreator [Hslots Halias]]
    [Hsnapshot [Hwait [Hprotocol [Hunique [Hflags Htimer]]]]]].
  pose proof (mutex_pend_ceiling_slot_owner sg before eid event mutex owner
    Hcross He Htype Hm Ho Henabled) as Hslot.
  assert (Hrange : task_priority_in_range sg mutex.(mfPCP)).
  { destruct (Hprotocol eid event mutex He Htype Hm) as [Hpcp _].
    unfold valid_mutex_pcp in Hpcp; unfold mutex_pcp_enabled in Henabled.
    unfold task_priority_in_range; intuition lia. }
  assert (Hclaim : mutex_task_enabled_pcp_claim sg before.(EventState) owner mutex.(mfPCP)).
  { exists eid, event, mutex; repeat split; assumption || reflexivity. }
  assert (Hless : mutex.(mfPCP) < base).
  { destruct (Halias owner node Hnode) as [permanent [Hp [Hmin _]]].
    pose proof (task_effective_priority_le_base sg before.(TskState).(prioTbl)
      owner base node.(curPrio) Hbase Hmin); lia. }
  assert (HbaseFrame : forall tid permanent,
    task_base_priority sg before.(TskState).(prioTbl) tid permanent ->
    task_base_priority sg (update_prio_tbl before.(TskState).(prioTbl)
      mutex.(mfPCP) (PTTask owner)) tid permanent).
  { intros tid permanent Hb; destruct (Z.eq_dec tid owner) as [->|Hother].
    - assert (permanent = base) by (eapply task_base_priority_unique; eassumption).
      subst; apply task_alias_add_preserves_base_priority; try assumption; lia.
    - eapply task_base_priority_alias_ext; [|exact Hb].
      intro p; symmetry; apply task_priority_alias_foreign_write_iff;
        [destruct Hslot as [Hs|Hs]; rewrite Hs; congruence|congruence]. }
  split.
  - split; [exact Hcreator|]. split.
    + intros p Hp; cbn [replace_TskS TskState EventState mutex_pend_demand_tasks
        mutex_demand_table glob_task_set_usedtask prioTbl inUsedTaskStates taskLifecycle].
      unfold update_prio_tbl; destruct (Z.eq_dec p mutex.(mfPCP)) as [->|Hne].
      * exists (mutex_priority_task node mutex.(mfPCP)); rewrite Z.eqb_refl; reflexivity.
      * specialize (Hslots p Hp).
        destruct (before.(TskState).(prioTbl) p) as [| |tid]; [exact Hslots|exact Hslots|].
        apply (proj2 (glob_task_set_usedtask_live_iff before.(TskState) owner node
          (mutex_priority_task node mutex.(mfPCP)) tid Hnode)); exact Hslots.
    + eapply mutex_pend_promote_priority_alias_consistency; eassumption.
  - split.
    + intros mid e m tid Hget Hty Hfields Howner.
      destruct (Hsnapshot mid e m tid Hget Hty Hfields Howner)
        as [t [permanent [snapshot [Ht [Hb Hrest]]]]].
      destruct (proj2 (glob_task_set_usedtask_live_iff before.(TskState) owner node
        (mutex_priority_task node mutex.(mfPCP)) tid Hnode) (ex_intro _ t Ht)) as [updated Hupdated].
      exists updated, permanent, snapshot; split; [exact Hupdated|].
      split; [apply HbaseFrame; exact Hb|exact Hrest].
    + split.
      * change (event_wait_object_consistency sg (replace_TskS
          (glob_task_set_usedtask before.(TskState) owner (mutex_priority_task node mutex.(mfPCP))) before)).
        eapply event_wait_object_update_unlisted_task; try eassumption; reflexivity.
      * split.
        -- intros mid e m Hget Hty Hfields.
           change (before.(EventState).(inUsedEventStates) mid = Some e) in Hget.
           destruct (Hprotocol mid e m Hget Hty Hfields) as [Hpcp [Howner Hcell]].
           split; [exact Hpcp|]. split; [exact Howner|].
           destruct Hcell as [Hdisabled|[Henabled' Hcell]]; [left; exact Hdisabled|].
           right; split; [exact Henabled'|].
           cbn [replace_TskS TskState mutex_pend_demand_tasks mutex_demand_table prioTbl].
           destruct (Z.eq_dec m.(mfPCP) mutex.(mfPCP)) as [Epcp|Hne].
           ++ assert (mid = eid) by (eapply Hunique; eassumption).
              subst mid; assert (e = event) by congruence; subst e.
              assert (m = mutex) by congruence; subst m.
              right; exists owner; split; [exact Ho|apply update_prio_tbl_same].
           ++ rewrite update_prio_tbl_other by exact Hne; exact Hcell.
        -- split; [exact Hunique|]. split; [|exact Htimer].
           change (task_flag_waiter_consistency sg
             (glob_task_set_usedtask before.(TskState) owner (mutex_priority_task node mutex.(mfPCP)))
             before.(FlagState)).
           eapply task_flag_waiter_consistency_update_task;
             [exact Hnode|reflexivity|reflexivity|reflexivity|reflexivity| | |exact Hflags];
             intros H; exact H.
Qed.

Lemma mutex_pend_promote_tasks_in_range :
  forall sg before eid event mutex owner node base,
  task_in_range sg before.(TskState) -> cross_module_consistency sg before ->
  before.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  before.(TskState).(inUsedTaskStates) owner = Some node ->
  task_base_priority sg before.(TskState).(prioTbl) owner base ->
  mutex.(mfPCP) < node.(curPrio) ->
  task_in_range sg
    (mutex_pend_demand_tasks before.(TskState) owner node PromoteMutexOwner mutex.(mfPCP)).
Proof.
  intros sg before eid event mutex owner node base
    [Hpool [Hactive [Hfree [Hreservations [Hgenerations [Hregistered
      [Hunique [Hpriority Hrest]]]]]]]] Hcross He Htype Hm Ho Henabled Hnode Hbase Hcurrent.
  pose proof (mutex_pend_ceiling_slot_owner sg before eid event mutex owner
    Hcross He Htype Hm Ho Henabled) as Hslot.
  assert (Hrange : task_priority_in_range sg mutex.(mfPCP)).
  { destruct Hcross as [_ [_ [_ [Hprotocol _]]]].
    destruct (Hprotocol eid event mutex He Htype Hm) as [Hpcp _].
    unfold valid_mutex_pcp in Hpcp; unfold mutex_pcp_enabled in Henabled.
    unfold task_priority_in_range; intuition lia. }
  assert (Hclaim : mutex_task_enabled_pcp_claim sg before.(EventState) owner mutex.(mfPCP)).
  { exists eid, event, mutex; repeat split; assumption || reflexivity. }
  pose proof (mutex_pend_promote_priority_alias_consistency sg before.(TskState)
    before.(EventState) owner node base mutex.(mfPCP) Hnode Hbase Hcurrent Hrange Hslot Hclaim
    (proj2 (proj2 (proj1 Hcross)))) as Halias.
  assert (Hlive : forall slot,
    (exists t, (mutex_pend_demand_tasks before.(TskState) owner node PromoteMutexOwner mutex.(mfPCP))
      .(inUsedTaskStates) slot = Some t) <->
    (exists t, before.(TskState).(inUsedTaskStates) slot = Some t)).
  { intro slot; apply glob_task_set_usedtask_live_iff with (old := node); exact Hnode. }
  assert (Horigin : forall slot t,
    (mutex_pend_demand_tasks before.(TskState) owner node PromoteMutexOwner mutex.(mfPCP))
      .(inUsedTaskStates) slot = Some t ->
    exists old, before.(TskState).(inUsedTaskStates) slot = Some old /\
      t.(taskGeneration) = old.(taskGeneration)).
  { intros slot t Ht; cbn [mutex_pend_demand_tasks glob_task_set_usedtask inUsedTaskStates] in Ht.
    destruct (Z.eqb slot owner) eqn:E.
    - apply Z.eqb_eq in E; subst slot; injection Ht as E; subst t; exists node; auto.
    - exists t; auto. }
  split.
  - destruct Hpool as [Hdomain [Hused [Hprivate [Hnd [Hstorage HreservationUnique]]]]].
    split; [intro slot; rewrite Hlive; exact (Hdomain slot)|]. split.
    + intros slot t Ht; destruct (Horigin slot t Ht) as [old [Hold _]]; exact (Hused slot old Hold).
    + split; [exact Hprivate|]. split; [exact Hnd|]. split; [exact Hstorage|exact HreservationUnique].
  - split.
    + destruct Hactive as [Hnd [Hhead [Hcount [Hcover Hlinks]]]].
      split; [exact Hnd|]. split; [exact Hhead|]. split; [exact Hcount|]. split.
      * intro slot; rewrite Hlive; exact (Hcover slot).
      * eapply task_active_links_update; try eassumption; reflexivity.
    + split; [exact Hfree|]. split.
      * destruct Hreservations as [Hentries Hdistinct]; split; [|exact Hdistinct].
        intros p reservation Hr; destruct (Hentries p reservation Hr) as [Hp [Hcell Hinv]].
        split; [exact Hp|]. split; [|exact Hinv].
        change (update_prio_tbl before.(TskState).(prioTbl) mutex.(mfPCP) (PTTask owner) p = PTReserved).
        rewrite update_prio_tbl_other; [exact Hcell|].
        intro E; subst p; apply (proj1 (proj1 Hcross) mutex.(mfPCP) reservation Hr).
        exists eid, event, mutex; repeat split; assumption || reflexivity.
      * split.
        -- destruct Hgenerations as [Hgenerations Hother]; split; [|exact Hother].
           intros slot t Ht; destruct (Horigin slot t Ht) as [old [Hold Hg]].
           cbn [mutex_pend_demand_tasks glob_task_set_usedtask taskLifecycle]; rewrite Hg.
           exact (Hgenerations slot old Hold).
        -- split; [eapply mutex_priority_alias_consistency_current_registered; exact Halias|].
           split; [eapply mutex_priority_alias_consistency_priority_unique; exact Halias|].
           split; [|exact Hrest]. intros slot t Ht.
           destruct (Halias slot t Ht) as [permanent [_ [[[Hp _] _] _]]]; exact Hp.
Qed.

Lemma mutex_pend_promote_preserves_idle_tail : forall sg tasks owner node ceiling,
  tasks.(inUsedTaskStates) owner = Some node -> node.(curPrio) <> sg.(osLowestPrio) ->
  ceiling < sg.(osLowestPrio) -> task_idle_tail sg tasks ->
  task_idle_tail sg (mutex_pend_demand_tasks tasks owner node PromoteMutexOwner ceiling).
Proof.
  intros sg tasks owner node ceiling Hnode Hnotidle Hceiling
    [prefix [idle [t [Horder [Ht [Hp Hothers]]]]]].
  assert (Hdifferent : idle <> owner).
  { intro E; subst idle; rewrite Hnode in Ht; injection Ht as E; subst t; contradiction. }
  exists prefix, idle, t; split; [exact Horder|]. split.
  - cbn [mutex_pend_demand_tasks glob_task_set_usedtask inUsedTaskStates].
    rewrite (proj2 (Z.eqb_neq _ _) Hdifferent); exact Ht.
  - split; [exact Hp|]. intros slot other Hin Hother.
    cbn [mutex_pend_demand_tasks glob_task_set_usedtask inUsedTaskStates] in Hother.
    destruct (Z.eqb slot owner) eqn:E.
    + injection Hother as Eother; subst other; cbn [mutex_priority_task curPrio]; lia.
    + exact (Hothers slot other Hin Hother).
Qed.

(** The explicit source/client condition below is needed only for the
    Idle-tail clause.  It is not derivable from arbitrary old kernel
    validity or the Event-unlinked owner protocol.  The selected empty
    Idle hook and the separately recorded client protocol must supply it;
    this lemma does not silently install it as a platform guarantee. *)
Lemma mutex_pend_promote_preserves_validity :
  forall sg before eid event mutex owner node base,
  UCOS2_state_inv sg before ->
  before.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  before.(TskState).(inUsedTaskStates) owner = Some node ->
  task_base_priority sg before.(TskState).(prioTbl) owner base ->
  mutex.(mfPCP) < node.(curPrio) ->
  (forall mid e, before.(EventState).(inUsedEventStates) mid = Some e -> ~ In owner e.(waitList)) ->
  (before.(SchedState).(isRunning) = true -> node.(curPrio) <> sg.(osLowestPrio)) ->
  UCOS2_state_inv sg (mutex_pend_promoted_state sg before owner node mutex.(mfPCP)).
Proof.
  intros sg before eid event mutex owner node base
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus [Hflags
      [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]]]]]]]]]
    He Htype Hm Ho Henabled Hnode Hbase Hcurrent Habsent Hnotidle.
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  pose proof (mutex_pend_ceiling_slot_owner sg before eid event mutex owner
    Hcross He Htype Hm Ho Henabled) as Hslot.
  assert (Hceiling : 0 <= mutex.(mfPCP) < sg.(osLowestPrio)).
  { destruct Hcross as [_ [_ [_ [Hprotocol _]]]].
    destruct (Hprotocol eid event mutex He Htype Hm) as [Hpcp _].
    unfold valid_mutex_pcp in Hpcp; unfold mutex_pcp_enabled in Henabled; intuition lia. }
  assert (Hrange : task_priority_in_range sg mutex.(mfPCP))
    by (unfold task_priority_in_range; lia).
  assert (Hclaim : exists mid e m,
    before.(EventState).(inUsedEventStates) mid = Some e /\
    e.(eventType) = OS_EVENT_TYPE_MUTEX /\ e.(mutexFields) = Some m /\
    mutex_reserves_priority_slot sg m mutex.(mfPCP)).
  { exists eid, event, mutex; repeat split; assumption || reflexivity. }
  assert (Hnoreservation : forall reservation,
    before.(TskState).(taskLifecycle).(taskReservations) mutex.(mfPCP) <> Some reservation).
  { intros reservation Hr; exact (proj1 (proj1 Hcross) mutex.(mfPCP) reservation Hr Hclaim). }
  pose proof (mutex_pend_promote_cross_module_consistency sg before eid event mutex owner node base
    Hcross He Htype Hm Ho Henabled Hnode Hbase Hcurrent Habsent) as HcrossAfter.
  assert (HreferencesAfter : kernel_names_valid sg
    (mutex_pend_promoted_state sg before owner node mutex.(mfPCP))).
  { eapply kernel_names_valid_frame with (before := before);
      [exact Hreferences|reflexivity| |intros; assumption|intros; assumption|intros; assumption|intros; assumption].
    apply task_update_name_references with (old := node); [exact Hnode|reflexivity]. }
  assert (HstacksAfter : parked_stacks_consistent
    (mutex_pend_demand_tasks before.(TskState) owner node PromoteMutexOwner mutex.(mfPCP))
    before.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Hnode|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  assert (HpendingAfter : pending_mutex_consistency sg
    (mutex_pend_demand_tasks before.(TskState) owner node PromoteMutexOwner mutex.(mfPCP))
    before.(EventState)).
  { eapply pending_mutex_consistency_table_transport with (tasks := before.(TskState));
      [|intros; reflexivity|exact Hpending].
    intros p [slot [queue Hlease]].
    change (update_prio_tbl before.(TskState).(prioTbl) mutex.(mfPCP) (PTTask owner) p =
      before.(TskState).(prioTbl) p).
    apply update_prio_tbl_other; intro E; subst p.
    destruct (Hpending slot mutex.(mfPCP) queue Hlease) as [_ [_ [_ [_ [_ [Hnomutex _]]]]]].
    exact (Hnomutex Hclaim). }
  split; [exact Hprofile|]. split.
  - eapply mutex_pend_promote_tasks_in_range; eassumption.
  - split.
    + eapply mutex_pend_promote_sched_in_range; eassumption.
    + split.
      * apply event_update_unlisted_task_preserves_in_range; assumption.
      * split.
        -- apply cross_module_consistency_sched_frame; [reflexivity|exact HcrossAfter].
        -- split.
           ++ intro Hrunning; apply mutex_pend_promote_preserves_idle_tail;
                [exact Hnode|apply Hnotidle; exact Hrunning|lia|apply Hidle; exact Hrunning].
           ++ split.
              ** apply task_reserved_bits_clear_update_task; [exact Hstatus|exact (Hstatus owner node Hnode)].
              ** split; [exact Hflags|]. split; [exact Hmemory|]. split; [exact Htimer|].
                 split; [exact Hstats|]. split; [exact Hcontrol|]. split; [exact Hnames|].
                 split; [exact HreferencesAfter|]. split; [exact HstacksAfter|exact HpendingAfter].
Qed.

(** These are the concrete cells touched by the inheritance prefix.  The
    structural residual already used by Delete is reusable verbatim; Pend
    retains both current-task cells, and never performs Delete's release
    store or its current-priority update. *)
Definition mutex_pend_priority_input (sg : StableGlobVars)
  (before : UCOS2_Verify_State) (owner : TaskID) (node : TaskAbstractState) : Assertion :=
  tcb64_storage_rep (task_slot_addr sg owner) (task_tcb64_image sg node) **
  PtrArray.full sg.(g_OSTCBPrioTbl) 64
    (mutex_del_priority_values sg before.(TskState).(prioTbl)) **
  UCharArray.full sg.(g_OSRdyTbl) 8
    (sched_row_values before.(TskState) before.(SchedState).(readyList)) **
  sg.(g_OSRdyGrp) # UChar |->
    encode_ready_grp before.(SchedState).(readyList) before.(TskState) **
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg before.(SchedState).(curTaskID) **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte before.(SchedState).(curSchedPrio).

Definition mutex_pend_priority_output (sg : StableGlobVars)
  (before : UCOS2_Verify_State) (owner : TaskID) (node : TaskAbstractState)
  (ceiling : Priority) : Assertion :=
  tcb64_storage_rep (task_slot_addr sg owner)
    (mutex_priority_image (task_tcb64_image sg node) ceiling) **
  PtrArray.full sg.(g_OSTCBPrioTbl) 64
    (replace_Znth ceiling (task_slot_addr sg owner)
      (mutex_del_priority_values sg before.(TskState).(prioTbl))) **
  UCharArray.full sg.(g_OSRdyTbl) 8
    (mutex_priority_rows (sched_row_values before.(TskState) before.(SchedState).(readyList))
      (tcb_y_of_prio node.(curPrio)) (tcb_bit_x_of_prio node.(curPrio)) ceiling) **
  sg.(g_OSRdyGrp) # UChar |->
    mutex_priority_group (sched_row_values before.(TskState) before.(SchedState).(readyList))
      (encode_ready_grp before.(SchedState).(readyList) before.(TskState))
      (tcb_y_of_prio node.(curPrio)) (tcb_bit_x_of_prio node.(curPrio))
      (tcb_bit_y_of_prio node.(curPrio)) ceiling **
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg before.(SchedState).(curTaskID) **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte before.(SchedState).(curSchedPrio).

Lemma mutex_pend_priority_input_split : forall sg before owner node,
  selected_kernel_profile sg -> before.(TskState).(inUsedTaskStates) owner = Some node ->
  UCOS2_raw_rep sg before |--
    mutex_pend_priority_input sg before owner node ** mutex_del_priority_frame sg before owner.
Proof.
  intros sg before owner node Hprofile Hnode.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  rewrite UCOS2_raw_rep_priority_table_equiv.
  unfold UCOS2_raw_rep_missing_priority_table, task_public_storage_without_prio_tbl,
    store_used_task_map.
  sep_apply_l_atomic (store_map_split (used_task_rep sg) owner node
    before.(TskState).(inUsedTaskStates) Hnode).
  unfold mutex_pend_priority_input, mutex_del_priority_frame, sched_raw_rep, sched_physical_rep.
  rewrite used_task_rep_tcb64, <- task_slot_addr_tcb64 by assumption.
  rewrite sched_rows_array_equiv.
  unfold store_prio_tbl, mutex_del_priority_values; entailer!.
Qed.

Lemma mutex_pend_priority_values_write : forall sg table owner ceiling,
  0 <= ceiling < 64 ->
  replace_Znth ceiling (task_slot_addr sg owner) (mutex_del_priority_values sg table) =
  mutex_del_priority_values sg (update_prio_tbl table ceiling (PTTask owner)).
Proof.
  intros sg table owner ceiling Hrange; unfold mutex_del_priority_values.
  rewrite <- map_Zrange_update by exact Hrange.
  apply map_ext; intro p; unfold update_prio_tbl.
  destruct (Z.eq_dec p ceiling); reflexivity.
Qed.

Lemma mutex_pend_promoted_other_modules_eq : forall sg before owner node ceiling,
  (forall eid event, before.(EventState).(inUsedEventStates) eid = Some event ->
    ~ In owner event.(waitList)) ->
  UCOS2_raw_rep_missing_task_storage_sched sg before =
  UCOS2_raw_rep_missing_task_storage_sched sg
    (mutex_pend_promoted_state sg before owner node ceiling).
Proof.
  intros sg before owner node ceiling Habsent.
  assert (Hencoding : event_raw_encoding_agrees before.(TskState)
    (mutex_pend_demand_tasks before.(TskState) owner node PromoteMutexOwner ceiling)
    before.(EventState)).
  { apply event_wait_priority_agreement_encodes; intros eid event slot Hevent Hin.
    cbn [mutex_pend_demand_tasks glob_task_set_usedtask inUsedTaskStates].
    destruct (Z.eqb slot owner) eqn:E; [|reflexivity].
    apply Z.eqb_eq in E; subst slot; exfalso; exact (Habsent eid event Hevent Hin). }
  unfold UCOS2_raw_rep_missing_task_storage_sched.
  cbn [mutex_pend_promoted_state replace_TskS replace_SchedS
    TskState SchedState IntrState EventState TickState FlagState MemoryState TimerState
    StatsState ControlState NameState mutex_pend_demand_tasks glob_task_set_usedtask parkedTaskStacks].
  rewrite (event_raw_rep_change_task_index sg before.(TskState)
    (mutex_pend_demand_tasks before.(TskState) owner node PromoteMutexOwner ceiling)
    before.(EventState) Hencoding).
  reflexivity.
Qed.

(** Reconstruct the actual post-write heap from the native five-field TCB
    image, replaced priority-table cell and computed ready bitmap.  No
    post-state invariant is assumed, and no scheduler cache is refreshed. *)
Lemma mutex_pend_priority_output_merge_raw : forall sg before owner node ceiling,
  UCOS2_state_inv sg before ->
  before.(TskState).(inUsedTaskStates) owner = Some node -> 0 <= ceiling < 64 ->
  (forall eid event, before.(EventState).(inUsedEventStates) eid = Some event ->
    ~ In owner event.(waitList)) ->
  mutex_pend_priority_output sg before owner node ceiling **
    mutex_del_priority_frame sg before owner |--
  UCOS2_raw_rep sg (mutex_pend_promoted_state sg before owner node ceiling).
Proof.
  intros sg before owner node ceiling Hvalid Hnode Hceiling Habsent.
  pose proof Hvalid as [Hprofile [Htasks [Hsched Hrest]]].
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  destruct (mutex_del_relocated_ready_encoding sg before.(TskState) before.(SchedState)
    owner node ceiling (proj1 Hprofile) Htasks Hsched Hnode Hceiling) as [Hgroup Hrows].
  set (updated := mutex_pend_demand_tasks before.(TskState) owner node PromoteMutexOwner ceiling).
  set (ready := mutex_pend_promoted_ready sg before owner node ceiling).
  destruct (sched_encoding_priority_ext ready updated
    (glob_task_set_usedtask before.(TskState) owner (mutex_priority_task node ceiling))
    ltac:(intros; reflexivity)) as [Hgroup_index Hrows_index].
  assert (Hrow_values : sched_row_values updated ready =
    sched_row_values (glob_task_set_usedtask before.(TskState) owner
      (mutex_priority_task node ceiling)) ready).
  { unfold sched_row_values; apply map_ext; exact Hrows_index. }
  assert (Hready : mutex_del_relocated_ready sg before.(TskState) before.(SchedState)
    owner node ceiling = ready) by reflexivity.
  rewrite Hready in Hgroup, Hrows.
  rewrite <- Hgroup_index in Hgroup; rewrite <- Hrow_values in Hrows.
  pose proof (used_task_rep_tcb64 sg owner (mutex_priority_task node ceiling) Hmulti Hprofiling) as Htcb.
  rewrite <- task_slot_addr_tcb64 in Htcb by assumption.
  assert (Hoff : forall slot, slot <> owner ->
    before.(TskState).(inUsedTaskStates) slot = updated.(inUsedTaskStates) slot).
  { intros slot Hneq; unfold updated;
      cbn [mutex_pend_demand_tasks glob_task_set_usedtask inUsedTaskStates].
    apply Z.eqb_neq in Hneq; rewrite Hneq; reflexivity. }
  assert (Hupdated : updated.(inUsedTaskStates) owner = Some (mutex_priority_task node ceiling)).
  { unfold updated; cbn [mutex_pend_demand_tasks glob_task_set_usedtask inUsedTaskStates].
    rewrite Z.eqb_refl; reflexivity. }
  unfold mutex_pend_priority_output.
  rewrite mutex_priority_image_task_eq, <- Htcb.
  rewrite mutex_pend_priority_values_write by exact Hceiling.
  rewrite <- Hgroup, <- Hrows.
  unfold mutex_del_priority_frame.
  rewrite (mutex_pend_promoted_other_modules_eq sg before owner node ceiling Habsent).
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv (used_task_rep sg)
    before.(TskState).(inUsedTaskStates) updated.(inUsedTaskStates) owner Hoff)).
  sep_apply_l_atomic (store_map_merge (used_task_rep sg) owner (mutex_priority_task node ceiling)
    updated.(inUsedTaskStates) Hupdated).
  match goal with |- ?Pre |-- _ =>
    assert (Hpack : Pre |--
      task_public_storage sg updated **
      sched_raw_rep sg updated (sched_set_ready before.(SchedState) ready) **
      UCOS2_raw_rep_missing_task_storage_sched sg
        (mutex_pend_promoted_state sg before owner node ceiling))
  end.
  { unfold task_public_storage, store_used_task_map, store_prio_tbl, mutex_del_priority_values,
      sched_raw_rep, sched_physical_rep.
    rewrite sched_rows_array_equiv.
    unfold updated, ready, mutex_pend_demand_tasks, mutex_demand_table, sched_set_ready.
    cbn [glob_task_set_usedtask inUsedTaskStates unUsedTaskStates tcbListHead prioTbl
      taskCount taskLifecycle taskRegNextID parkedTaskStacks readyList curTaskID curSchedPrio
      highRdyTid highRdyPrio ctxSwCtr isRunning].
    entailer!. }
  match goal with |- _ |-- ?Post =>
    match type of Hpack with _ |-- ?Packed => assert (Hclose : Packed |-- Post) end
  end.
  { unfold UCOS2_raw_rep, task_shared_rep, UCOS2_raw_rep_missing_task_storage_sched;
    entailer!. }
  intros heap Howned; apply (Hclose heap); exact (Hpack heap Howned).
Qed.

Lemma mutex_pend_promote_branch_eq : forall sg before owner node base waiter ceiling after,
  node.(eventPtr) = None ->
  mutex_pend_inherit_action sg.(osPrioMutexCeilDis) base node.(curPrio) waiter ceiling =
    PromoteMutexOwner ->
  (mutex_pend_inherit_step sg before owner node base waiter ceiling after <->
   after = mutex_pend_promoted_state sg before owner node ceiling).
Proof.
  intros sg before owner node base waiter ceiling after Hptr Haction.
  unfold mutex_pend_inherit_step; rewrite Haction; split.
  - intros [events [Hevents ->]].
    assert (E : events = before.(EventState)).
    { unfold mutex_pend_promoted_events in Hevents.
      destruct (mutex_pend_owner_was_ready before node); [exact Hevents|].
      rewrite Hptr in Hevents; exact Hevents. }
    subst events; unfold mutex_pend_promoted_state; destruct before; reflexivity.
  - intros ->; exists before.(EventState); split.
    + unfold mutex_pend_promoted_events.
      destruct (mutex_pend_owner_was_ready before node); [reflexivity|].
      rewrite Hptr; reflexivity.
    + unfold mutex_pend_promoted_state; destruct before; reflexivity.
Qed.

Lemma mutex_pend_inherit_preserves_owner_unlinked :
  forall sg before eid event mutex owner node base waiter after,
  mutex_owner_event_unlinked before.(TskState) before.(EventState) ->
  before.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> before.(TskState).(inUsedTaskStates) owner = Some node ->
  mutex_pend_inherit_step sg before owner node base waiter mutex.(mfPCP) after ->
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros sg before eid event mutex owner node base waiter after Huse He Htype Hm Ho Hnode Hstep.
  destruct (mutex_pend_inherit_action sg.(osPrioMutexCeilDis) base node.(curPrio)
    waiter mutex.(mfPCP)) eqn:Haction.
  - unfold mutex_pend_inherit_step in Hstep; rewrite Haction in Hstep; subst after; exact Huse.
  - unfold mutex_pend_inherit_step in Hstep; rewrite Haction in Hstep; subst after; exact Huse.
  - assert (Hptr : node.(eventPtr) = None)
      by exact (proj1 (Huse eid event mutex owner node He Htype Hm Ho Hnode)).
    apply (proj1 (mutex_pend_promote_branch_eq sg before owner node base waiter
      mutex.(mfPCP) after Hptr Haction)) in Hstep; subst after.
    change (mutex_owner_event_unlinked
      (glob_task_set_usedtask before.(TskState) owner (mutex_priority_task node mutex.(mfPCP)))
      before.(EventState)).
    eapply mutex_owner_event_unlinked_task_fields_frame;
      [exact Hnode|reflexivity|reflexivity|exact Huse].
Qed.

(** The actual end-of-prefix consumer.  The owner-use protocol supplies
    the unchanged Event bitmap frame.  Idle's source-derived exclusion is
    explicit and is consumed only for the old global Idle-tail invariant. *)
Lemma mutex_pend_priority_output_merge : forall sg before eid event mutex owner node base,
  UCOS2_state_inv sg before ->
  mutex_owner_event_unlinked before.(TskState) before.(EventState) ->
  before.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  before.(TskState).(inUsedTaskStates) owner = Some node ->
  task_base_priority sg before.(TskState).(prioTbl) owner base ->
  mutex.(mfPCP) < node.(curPrio) ->
  (before.(SchedState).(isRunning) = true -> node.(curPrio) <> sg.(osLowestPrio)) ->
  mutex_pend_priority_output sg before owner node mutex.(mfPCP) **
    mutex_del_priority_frame sg before owner |--
  UCOS2_inv sg (mutex_pend_promoted_state sg before owner node mutex.(mfPCP)).
Proof.
  intros sg before eid event mutex owner node base Hvalid Huse He Htype Hm Ho
    Henabled Hnode Hbase Hcurrent Hnotidle.
  pose proof Hvalid as [Hprofile [_ [_ [Hevents [Hcross _]]]]].
  assert (Habsent : forall mid other, before.(EventState).(inUsedEventStates) mid = Some other ->
    ~ In owner other.(waitList)).
  { eapply mutex_owner_event_unlinked_not_waiter; eassumption. }
  assert (Hrange : 0 <= mutex.(mfPCP) < 64).
  { destruct Hcross as [_ [_ [_ [Hprotocol _]]]].
    destruct (Hprotocol eid event mutex He Htype Hm) as [Hpcp _].
    pose proof (proj1 Hprofile) as Hsg.
    unfold valid_mutex_pcp in Hpcp; unfold mutex_pcp_enabled in Henabled.
    unfold valid_stable_glob_vars in Hsg; intuition lia. }
  pose proof (mutex_pend_promote_preserves_validity sg before eid event mutex owner node base
    Hvalid He Htype Hm Ho Henabled Hnode Hbase Hcurrent Habsent Hnotidle) as Hpost.
  eapply derivable1_trans.
  - exact (mutex_pend_priority_output_merge_raw sg before owner node mutex.(mfPCP)
      Hvalid Hnode Hrange Habsent).
  - unfold UCOS2_inv; entailer!.
Qed.

(** Join the three actual inheritance paths before the caller's Stat/Dly
    stores.  The Boolean source guards provide the precise ceiling bounds
    needed by the record/promote branches. *)
Lemma mutex_pend_inherit_preserves_validity :
  forall sg before eid event mutex owner node base waiter after,
  UCOS2_state_inv sg before ->
  mutex_owner_event_unlinked before.(TskState) before.(EventState) ->
  before.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> before.(TskState).(inUsedTaskStates) owner = Some node ->
  task_base_priority sg before.(TskState).(prioTbl) owner base ->
  (before.(SchedState).(isRunning) = true -> node.(curPrio) <> sg.(osLowestPrio)) ->
  mutex_pend_inherit_step sg before owner node base waiter mutex.(mfPCP) after ->
  UCOS2_state_inv sg after.
Proof.
  intros sg before eid event mutex owner node base waiter after Hvalid Huse He Htype Hm Ho
    Hnode Hbase Hnotidle Hstep.
  destruct (mutex_pend_inherit_action sg.(osPrioMutexCeilDis) base node.(curPrio)
    waiter mutex.(mfPCP)) eqn:Haction.
  - unfold mutex_pend_inherit_step in Hstep; rewrite Haction in Hstep; subst after; exact Hvalid.
  - eapply mutex_pend_record_branch_preserves_validity; eassumption.
  - assert (Hptr : node.(eventPtr) = None)
      by exact (proj1 (Huse eid event mutex owner node He Htype Hm Ho Hnode)).
    apply (proj1 (mutex_pend_promote_branch_eq sg before owner node base waiter
      mutex.(mfPCP) after Hptr Haction)) in Hstep; subst after.
    apply mutex_pend_inherit_promote_iff in Haction; destruct Haction as [Henabled [Hcurrent Hwaiter]].
    assert (Habsent : forall mid other, before.(EventState).(inUsedEventStates) mid = Some other ->
      ~ In owner other.(waitList)).
    { pose proof Hvalid as [_ [_ [_ [Hevents _]]]].
      eapply mutex_owner_event_unlinked_not_waiter; eassumption. }
    eapply mutex_pend_promote_preserves_validity; eassumption.
Qed.

Lemma mutex_pend_inherit_observations :
  forall sg before eid event mutex owner node base waiter after,
  UCOS2_state_inv sg before ->
  mutex_owner_event_unlinked before.(TskState) before.(EventState) ->
  before.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> before.(TskState).(inUsedTaskStates) owner = Some node ->
  mutex_pend_inherit_step sg before owner node base waiter mutex.(mfPCP) after ->
  after.(EventState) = before.(EventState) /\
  after.(SchedState).(curTaskID) = before.(SchedState).(curTaskID) /\
  (forall slot, slot <> owner ->
    after.(TskState).(inUsedTaskStates) slot = before.(TskState).(inUsedTaskStates) slot) /\
  (forall slot, In slot after.(SchedState).(readyList) <-> In slot before.(SchedState).(readyList)).
Proof.
  intros sg before eid event mutex owner node base waiter after Hvalid Huse He Htype Hm Ho Hnode Hstep.
  destruct (mutex_pend_inherit_action sg.(osPrioMutexCeilDis) base node.(curPrio)
    waiter mutex.(mfPCP)) eqn:Haction.
  - unfold mutex_pend_inherit_step in Hstep; rewrite Haction in Hstep; subst after.
    split; [reflexivity|]. split; [reflexivity|]. split; intros; reflexivity.
  - unfold mutex_pend_inherit_step in Hstep; rewrite Haction in Hstep; subst after.
    split; [reflexivity|]. split; [reflexivity|]. split; intros; reflexivity.
  - assert (Hptr : node.(eventPtr) = None)
      by exact (proj1 (Huse eid event mutex owner node He Htype Hm Ho Hnode)).
    apply (proj1 (mutex_pend_promote_branch_eq sg before owner node base waiter
      mutex.(mfPCP) after Hptr Haction)) in Hstep; subst after.
    split; [reflexivity|]. split; [reflexivity|]. split.
    + intros slot Hneq.
      cbn [mutex_pend_promoted_state replace_TskS replace_SchedS TskState
        mutex_pend_demand_tasks glob_task_set_usedtask inUsedTaskStates].
      rewrite (proj2 (Z.eqb_neq _ _) Hneq); reflexivity.
    + intro slot; pose proof Hvalid as [Hprofile [Htasks [Hsched _]]].
      assert (Hunique : task_priority_unique before.(TskState))
        by (unfold task_in_range in Htasks; tauto).
      assert (Hpriority : task_priority_in_range sg node.(curPrio)).
      { unfold task_in_range in Htasks; intuition eauto. }
      pose proof (sched_ready_in_range_implies_structure sg before.(TskState) before.(SchedState)
        (proj1 Hsched)) as Hstructure.
      exact (mutex_del_relocated_ready_membership sg before.(TskState) before.(SchedState)
        owner node mutex.(mfPCP) slot (proj1 Hprofile) Hunique Hnode Hpriority Hstructure).
Qed.
