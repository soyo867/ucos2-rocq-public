Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.helpers.
Import UCOS2_C_Rules.
Import TaskStateDef.
Import SchedStateDef.

Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Import ListNotations.
Local Open Scope list.
Local Open Scope sac_scope.

(* ================================================================== *)
(* Phase 4 Task 4.1:SchedAbstractState 已在 state_def 中                *)
(* ================================================================== *)

(* 严格升序辅助 — 复用 helpers.v 中同名定义;此处避免重复,直接引用 *)
(* strictly_sorted_by 见 Ucos2Verify.lib.helpers *)

(* verification_slice_sched_in_range:依赖 task 状态作为参数 *)
Definition sched_high_ready_consistency
  (tskSt : Glob_TaskAbstractState) (s : SchedAbstractState) : Prop :=
  match s.(readyList) with
  | [] => s.(highRdyTid) = None /\ s.(highRdyPrio) = None
  | tid :: _ =>
      s.(highRdyTid) = Some tid /\
      exists t, tskSt.(inUsedTaskStates) tid = Some t /\
                s.(highRdyPrio) = Some t.(curPrio)
  end.

Definition sched_current_consistency
  (tskSt : Glob_TaskAbstractState) (s : SchedAbstractState) : Prop :=
  match s.(curTaskID) with
  | None => s.(curSchedPrio) = None
  | Some tid =>
      exists t, tskSt.(inUsedTaskStates) tid = Some t /\
                s.(curSchedPrio) = Some t.(curPrio)
  end.

(* Stable task-context call boundary.  At a normal task API entry/return the
   scheduler is running and its current-task globals identify a used task
   which is still effectively ready and present in the ready list.  This is
   an operation-family protocol stage, not a permanent scheduler invariant:
   a blocking operation temporarily leaves this stage before OS_Sched. *)
Definition sched_current_ready_at
  (tskSt : Glob_TaskAbstractState) (s : SchedAbstractState)
  (tid : TaskID) (t : TaskAbstractState) : Prop :=
  tskSt.(inUsedTaskStates) tid = Some t /\
  s.(curTaskID) = Some tid /\
  s.(curSchedPrio) = Some t.(curPrio) /\
  In tid s.(readyList) /\
  is_effectively_ready t.(stat) t.(dly) = true.

Definition sched_task_call_boundary
  (tskSt : Glob_TaskAbstractState) (s : SchedAbstractState) : Prop :=
  s.(isRunning) = true /\
  exists tid t, sched_current_ready_at tskSt s tid t.

(* Explicit blocking transient used between the task/ready-list mutation and
   the subsequent scheduler selection.  The scheduler globals still name the
   old current task, but that task is no longer ready or in [readyList].
   Keeping this stage separate is what permits Pend-like operations without
   weakening either the stable call boundary or [verification_slice_sched_in_range]. *)
Definition sched_current_blocked_before_schedule
  (tskSt : Glob_TaskAbstractState) (s : SchedAbstractState)
  (tid : TaskID) (t : TaskAbstractState) : Prop :=
  tskSt.(inUsedTaskStates) tid = Some t /\
  s.(curTaskID) = Some tid /\
  s.(curSchedPrio) = Some t.(curPrio) /\
  ~ In tid s.(readyList) /\
  is_effectively_ready t.(stat) t.(dly) = false.

Definition verification_slice_sched_in_range (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (s : SchedAbstractState) : Prop :=
  (forall tid, In tid s.(readyList) ->
    exists t, tskSt.(inUsedTaskStates) tid = Some t /\
    is_effectively_ready t.(stat) t.(dly) = true) /\
  strictly_sorted_by
    (fun tid => match tskSt.(inUsedTaskStates) tid with
                | Some t => t.(curPrio)
                | None => sg.(osLowestPrio) + 1
                end)
    s.(readyList) /\
  (forall tid t, tskSt.(inUsedTaskStates) tid = Some t ->
    is_effectively_ready t.(stat) t.(dly) = true ->
    In tid s.(readyList)) /\
  NoDup s.(readyList) /\
  0 <= s.(ctxSwCtr) /\
  sched_high_ready_consistency tskSt s /\
  sched_current_consistency tskSt s.

(* Historical verification-slice boundary: this predicate requires a
   refreshed high-ready cache. Native source stages below distinguish that
   cache from the logical minimum of the ready list. *)
Definition sched_logical_high (s : SchedAbstractState) : option TaskID :=
  hd_error s.(readyList).

Definition sched_ready_in_range (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (s : SchedAbstractState) : Prop :=
  (forall tid, In tid s.(readyList) -> exists t,
     tskSt.(inUsedTaskStates) tid = Some t /\
     task_priority_in_range sg t.(curPrio) /\
     is_effectively_ready t.(stat) t.(dly) = true) /\
  strictly_sorted_by
    (fun tid => match tskSt.(inUsedTaskStates) tid with
                | Some t => t.(curPrio) | None => sg.(osLowestPrio) + 1 end)
    s.(readyList) /\
  (forall tid t, tskSt.(inUsedTaskStates) tid = Some t ->
     is_effectively_ready t.(stat) t.(dly) = true -> In tid s.(readyList)) /\
  NoDup s.(readyList).

Definition sched_physical_cache_in_range (sg : StableGlobVars)
  (s : SchedAbstractState) : Prop :=
  (match s.(highRdyTid) with None => True | Some tid => task_slot_in_range sg tid end) /\
  (match s.(highRdyPrio) with
   | None => True
   | Some p => task_priority_in_range sg p \/ p = 255
   end).

(** The repaired MutexDel refresh writes 255/NULL when the ready bitmap is
    empty. This is a physical byte sentinel, not a priority-table index.
    Native initialization still uses None, whose byte encoding is zero;
    the explicit sentinel write uses Some 255. A later table read must get
    its index bound from the actual selection operation, not this cache. *)

(** These are physical caches, not permanent aliases of the latest TCB
    fields. ChangePrio may return while scheduling is locked; Delete may
    unlink the current TCB before the contracted context switch. Public
    task-call boundaries must separately establish a live current task. *)
Definition sched_current_cache_in_range (sg : StableGlobVars)
  (s : SchedAbstractState) : Prop :=
  (match s.(curTaskID) with None => True | Some tid => task_slot_in_range sg tid end) /\
  (match s.(curSchedPrio) with None => True | Some p => task_priority_in_range sg p end).

(** Cache/counter bounds do not depend on which source phase currently
    justifies ready membership.  Stable and deletion-phase invariants use
    the same physical metadata constraints. *)
Definition sched_metadata_in_range (sg : StableGlobVars)
  (s : SchedAbstractState) : Prop :=
  sched_physical_cache_in_range sg s /\
  0 <= s.(ctxSwCtr) < 4294967296 /\
  sched_current_cache_in_range sg s.

Definition sched_in_range (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (s : SchedAbstractState) : Prop :=
  sched_ready_in_range sg tskSt s /\ sched_metadata_in_range sg s.

Definition sched_set_ready (s : SchedAbstractState)
  (ready : list TaskID) : SchedAbstractState :=
  {| readyList := ready; curTaskID := s.(curTaskID);
     curSchedPrio := s.(curSchedPrio); highRdyTid := s.(highRdyTid);
     highRdyPrio := s.(highRdyPrio); ctxSwCtr := s.(ctxSwCtr);
     isRunning := s.(isRunning) |}.

(** A source-indexed phase assertion for the current task's ChangePrio
    interval. The pre-state is the saved observation, and the post-state
    keeps its two current-cache cells while the same task generation has a
    new priority. This is not an execution rule or a post-validity guard. *)
Definition sched_priority_change_pending
  (before_tasks after_tasks : Glob_TaskAbstractState)
  (before after : SchedAbstractState) (tid : TaskID)
  (old new : TaskAbstractState) : Prop :=
  before_tasks.(inUsedTaskStates) tid = Some old /\
  after_tasks.(inUsedTaskStates) tid = Some new /\
  new.(taskGeneration) = old.(taskGeneration) /\
  before.(curTaskID) = Some tid /\ before.(curSchedPrio) = Some old.(curPrio) /\
  after.(curTaskID) = before.(curTaskID) /\
  after.(curSchedPrio) = before.(curSchedPrio) /\ new.(curPrio) <> old.(curPrio).

Lemma sched_priority_change_records_pending :
  forall before_tasks after_tasks s tid old new ready,
  before_tasks.(inUsedTaskStates) tid = Some old ->
  after_tasks.(inUsedTaskStates) tid = Some new ->
  new.(taskGeneration) = old.(taskGeneration) ->
  s.(curTaskID) = Some tid -> s.(curSchedPrio) = Some old.(curPrio) ->
  new.(curPrio) <> old.(curPrio) ->
  sched_priority_change_pending before_tasks after_tasks s
    (sched_set_ready s ready) tid old new.
Proof. intros; repeat split; assumption || reflexivity. Qed.

Lemma sched_priority_change_cache_is_stale :
  forall before_tasks after_tasks before after tid old new,
  sched_priority_change_pending before_tasks after_tasks before after tid old new ->
  ~ sched_current_consistency after_tasks after.
Proof.
  intros before_tasks after_tasks before after tid old new
    (Hbefore & Hafter & Hg & Htid & Hprio & HtidFrame & HprioFrame & Hchanged) Hcurrent.
  unfold sched_current_consistency in Hcurrent; rewrite HtidFrame, Htid in Hcurrent.
  destruct Hcurrent as [t [Ht Htprio]]; rewrite Hafter in Ht; inversion Ht; subst t.
  rewrite HprioFrame, Hprio in Htprio; apply Hchanged; congruence.
Qed.

Lemma sched_priority_change_preserves_cache_ranges : forall sg s ready,
  sched_current_cache_in_range sg s ->
  sched_current_cache_in_range sg (sched_set_ready s ready).
Proof. intros; exact H. Qed.

(** Current-cache assignment promised by the external context-switch
    contract. Source selection writes high-priority and high-task first;
    this transformer does not prove ARM/BSP assembly or invent a C store
    in OSTaskChangePrio. Counter increments are separate source writes. *)
Definition sched_install_selected (s : SchedAbstractState) : SchedAbstractState :=
  {| readyList := s.(readyList); curTaskID := s.(highRdyTid);
     curSchedPrio := s.(highRdyPrio); highRdyTid := s.(highRdyTid);
     highRdyPrio := s.(highRdyPrio); ctxSwCtr := s.(ctxSwCtr);
     isRunning := s.(isRunning) |}.

Lemma sched_install_selected_synchronizes_current : forall tasks s,
  sched_high_ready_consistency tasks s ->
  sched_current_consistency tasks (sched_install_selected s).
Proof.
  intros tasks s Hhigh; unfold sched_high_ready_consistency in Hhigh.
  unfold sched_current_consistency; simpl.
  destruct s.(readyList) as [|tid rest].
  - destruct Hhigh as [Htid Hprio]; rewrite Htid; exact Hprio.
  - destruct Hhigh as [Htid [t [Ht Hp]]]; rewrite Htid; exists t; auto.
Qed.

Lemma sched_install_selected_preserves_in_range : forall sg tasks s,
  sched_in_range sg tasks s ->
  (forall p, s.(highRdyPrio) = Some p -> task_priority_in_range sg p) ->
  sched_in_range sg tasks (sched_install_selected s).
Proof.
  intros sg tasks s [Hready [Hhigh [Hcounter Hcurrent]]] Hindex.
  split; [exact Hready|]. split; [exact Hhigh|]. split; [exact Hcounter|].
  split; [exact (proj1 Hhigh)|].
  change (match s.(highRdyPrio) with
    | None => True | Some p => task_priority_in_range sg p end).
  destruct s.(highRdyPrio) as [p|] eqn:Hp; [apply Hindex; reflexivity|exact I].
Qed.

Lemma sched_install_selected_task_boundary : forall sg tasks s,
  sched_ready_in_range sg tasks s -> sched_high_ready_consistency tasks s ->
  s.(isRunning) = true -> s.(readyList) <> [] ->
  sched_task_call_boundary tasks (sched_install_selected s).
Proof.
  intros sg tasks s [Hmembers _] Hhigh Hrunning Hnonempty.
  unfold sched_high_ready_consistency in Hhigh.
  destruct s.(readyList) as [|tid rest] eqn:Hlist; [contradiction|].
  destruct Hhigh as [Htid [t [Ht Hp]]].
  destruct (Hmembers tid (or_introl eq_refl)) as [found [Hfound [_ Hready]]].
  rewrite Ht in Hfound; inversion Hfound; subst found.
  split; [exact Hrunning|]. exists tid, t.
  unfold sched_current_ready_at; simpl; rewrite Htid, Hp.
  split; [exact Ht|]. split; [reflexivity|]. split; [reflexivity|].
  split; [rewrite Hlist; left; reflexivity|exact Hready].
Qed.

Definition sched_refresh_high (tskSt : Glob_TaskAbstractState)
  (s : SchedAbstractState) : SchedAbstractState :=
  {| readyList := s.(readyList); curTaskID := s.(curTaskID);
     curSchedPrio := s.(curSchedPrio); highRdyTid := hd_error s.(readyList);
     highRdyPrio := match s.(readyList) with
       | [] => None
       | tid :: _ => match tskSt.(inUsedTaskStates) tid with
         | None => None | Some t => Some t.(curPrio) end end;
     ctxSwCtr := s.(ctxSwCtr); isRunning := s.(isRunning) |}.

(** OS_SchedNew writes the priority byte; OS_Sched/OSIntExit then read the
    priority table and write the pointer.  The pair-valued refresh above is
    only a completed logical checkpoint, never one source instruction. *)
Definition sched_write_high_priority (s : SchedAbstractState)
  (priority : option Priority) : SchedAbstractState :=
  {| readyList := s.(readyList); curTaskID := s.(curTaskID);
     curSchedPrio := s.(curSchedPrio); highRdyTid := s.(highRdyTid);
     highRdyPrio := priority; ctxSwCtr := s.(ctxSwCtr);
     isRunning := s.(isRunning) |}.

Definition sched_write_high_pointer (s : SchedAbstractState)
  (tid : option TaskID) : SchedAbstractState :=
  {| readyList := s.(readyList); curTaskID := s.(curTaskID);
     curSchedPrio := s.(curSchedPrio); highRdyTid := tid;
     highRdyPrio := s.(highRdyPrio); ctxSwCtr := s.(ctxSwCtr);
     isRunning := s.(isRunning) |}.

Lemma sched_refresh_is_two_writes : forall tasks s,
  sched_refresh_high tasks s =
    sched_write_high_pointer
      (sched_write_high_priority s
        (sched_refresh_high tasks s).(highRdyPrio))
      (sched_refresh_high tasks s).(highRdyTid).
Proof. reflexivity. Qed.

Lemma sched_priority_write_preserves_pointer : forall s p,
  (sched_write_high_priority s p).(highRdyTid) = s.(highRdyTid).
Proof. reflexivity. Qed.

Lemma sched_write_high_pair_eq : forall s,
  sched_write_high_pointer
    (sched_write_high_priority s s.(highRdyPrio)) s.(highRdyTid) = s.
Proof. intros []; reflexivity. Qed.

Definition sched_task_key (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (tid : TaskID) : Z :=
  match tasks.(inUsedTaskStates) tid with
  | Some t => t.(curPrio) | None => sg.(osLowestPrio) + 1 end.

Definition sched_commit_ready (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (s : SchedAbstractState)
  (p : Priority) (invocation : nat) (node : TaskAbstractState) : SchedAbstractState :=
  sched_set_ready s
    (insert_sorted_by (sched_task_key sg (task_commit tasks p invocation node))
      node.(taskID) s.(readyList)).

Lemma sched_commit_preserves_in_range : forall sg tasks s p invocation node,
  task_in_range sg tasks -> task_commit_identity tasks p invocation node ->
  sched_in_range sg tasks s ->
  is_effectively_ready node.(stat) node.(dly) = true ->
  sched_in_range sg (task_commit tasks p invocation node)
    (sched_commit_ready sg tasks s p invocation node).
Proof.
  intros sg tasks s p invocation node Htasks Hidentity
    [[Hmembers [Hsorted [Hcomplete Hnodup]]] [Hcache [Hcounter Hcurrent]]] Hready.
  pose proof (task_commit_preserves_in_range sg tasks p invocation node Htasks Hidentity)
    as Hpostrange.
  pose proof (task_commit_identity_private _ _ _ _ Hidentity) as Hprivate.
  pose proof (task_private_excludes_public sg tasks node.(taskID) (proj1 Htasks) Hprivate)
    as [Hnone Hnotfree].
  destruct Hpostrange as [_ [_ [_ [_ [_ [Hregpost [Hunique [Hpriopost _]]]]]]]].
  assert (Hfresh : ~ In node.(taskID) s.(readyList)).
  { intro Hin; destruct (Hmembers _ Hin) as [t [Hget _]]; congruence. }
  assert (Hobs : forall tid,
    option_map (fun t => (t.(curPrio), is_effectively_ready t.(stat) t.(dly)))
      ((task_commit tasks p invocation node).(inUsedTaskStates) tid) =
    (if Z.eq_dec tid node.(taskID)
     then Some (node.(curPrio), is_effectively_ready node.(stat) node.(dly))
     else option_map (fun t => (t.(curPrio), is_effectively_ready t.(stat) t.(dly)))
       (tasks.(inUsedTaskStates) tid))).
  { intro tid; apply task_commit_observation; reflexivity. }
  assert (Hnewmembers : forall tid, In tid (node.(taskID) :: s.(readyList)) -> exists t,
    (task_commit tasks p invocation node).(inUsedTaskStates) tid = Some t /\
    task_priority_in_range sg t.(curPrio) /\ is_effectively_ready t.(stat) t.(dly) = true).
  { intros tid Hin; specialize (Hobs tid).
    destruct (Z.eq_dec tid node.(taskID)) as [->|Hneq].
    - rewrite Hready in Hobs.
      destruct ((task_commit tasks p invocation node).(inUsedTaskStates) node.(taskID))
        as [t|] eqn:Hget; [|discriminate].
      simpl in Hobs; injection Hobs as Hprio Hreadyt.
      exists t; split; [reflexivity|]. split; [eapply Hpriopost; eauto|exact Hreadyt].
    - destruct Hin as [Heq|Hin]; [congruence|].
      destruct (Hmembers tid Hin) as [old [Hold [_ Hreadyold]]].
      rewrite Hold in Hobs.
      change (option_map (fun t => (t.(curPrio), is_effectively_ready t.(stat) t.(dly)))
        ((task_commit tasks p invocation node).(inUsedTaskStates) tid) =
        Some (old.(curPrio), is_effectively_ready old.(stat) old.(dly))) in Hobs.
      rewrite Hreadyold in Hobs.
      destruct ((task_commit tasks p invocation node).(inUsedTaskStates) tid)
        as [t|] eqn:Hget; [|discriminate].
      simpl in Hobs; injection Hobs as Hprio Hreadyt.
      exists t; split; [reflexivity|]. split; [eapply Hpriopost; eauto|exact Hreadyt]. }
  assert (Hkey : forall tid, In tid s.(readyList) ->
    sched_task_key sg tasks tid =
    sched_task_key sg (task_commit tasks p invocation node) tid).
  { intros tid Hin; destruct (Hmembers tid Hin) as [old [Hold _]].
    destruct (Hnewmembers tid (or_intror Hin)) as [t [Hget _]].
    specialize (Hobs tid); rewrite Hget in Hobs.
    destruct (Z.eq_dec tid node.(taskID)); [subst; contradiction|].
    rewrite Hold in Hobs; simpl in Hobs; injection Hobs as Hprio Hstatus.
    unfold sched_task_key; rewrite Hold, Hget; symmetry; exact Hprio. }
  unfold sched_in_range; split.
  - unfold sched_ready_in_range, sched_commit_ready; simpl; split.
    + intros tid Hin; apply insert_sorted_by_in in Hin; apply Hnewmembers; exact Hin.
    + split.
      * apply insert_sorted_by_preserves.
        -- eapply strictly_sorted_by_key_eq_on; [exact Hkey|exact Hsorted].
        -- intros tid Hin Heq.
           destruct (Hnewmembers tid (or_intror Hin)) as [t [Hget _]].
           destruct (Hnewmembers node.(taskID) (or_introl eq_refl)) as [new [Hnew _]].
           change (sched_task_key sg (task_commit tasks p invocation node) tid =
             sched_task_key sg (task_commit tasks p invocation node) node.(taskID)) in Heq.
           unfold sched_task_key in Heq; rewrite Hget, Hnew in Heq.
           pose proof (Hunique _ _ _ _ Hget Hnew Heq) as Hid; subst; contradiction.
      * split.
        -- intros tid t Hget Hreadyt; apply insert_sorted_by_in; simpl.
           change ((task_commit tasks p invocation node).(inUsedTaskStates) tid = Some t) in Hget.
           destruct (Z.eq_dec tid node.(taskID)) as [Heq|Hneq]; [left; symmetry; exact Heq|].
           right; specialize (Hobs tid); rewrite Hget in Hobs.
           destruct (Z.eq_dec tid node.(taskID)); [contradiction|].
           destruct (tasks.(inUsedTaskStates) tid) as [old|] eqn:Hold; [|discriminate].
           simpl in Hobs; injection Hobs as Hprio Hstatus.
           eapply Hcomplete; [exact Hold|rewrite <- Hstatus; exact Hreadyt].
        -- apply insert_sorted_by_preserves_NoDup; assumption.
  - split; [exact Hcache|]. split; [exact Hcounter|].
    exact Hcurrent.
Qed.

Lemma sched_set_ready_preserves_physical : forall s ready,
  let post := sched_set_ready s ready in
  post.(highRdyTid) = s.(highRdyTid) /\
  post.(highRdyPrio) = s.(highRdyPrio) /\
  post.(curTaskID) = s.(curTaskID) /\
  post.(curSchedPrio) = s.(curSchedPrio) /\
  post.(ctxSwCtr) = s.(ctxSwCtr) /\ post.(isRunning) = s.(isRunning).
Proof. intros; repeat split; reflexivity. Qed.

Lemma sched_refresh_high_establishes_consistency : forall sg tskSt s,
  sched_ready_in_range sg tskSt s ->
  sched_high_ready_consistency tskSt (sched_refresh_high tskSt s).
Proof.
  intros sg tskSt s [Hmembers _].
  unfold sched_high_ready_consistency, sched_refresh_high; simpl.
  destruct (readyList s) as [|tid rest] eqn:Hready; [split; reflexivity|].
  destruct (Hmembers tid (or_introl eq_refl)) as [t [Hlookup _]].
  rewrite Hlookup; split; [reflexivity | exists t; auto].
Qed.

Lemma sched_refresh_high_current_frame : forall tskSt s,
  (sched_refresh_high tskSt s).(curTaskID) = s.(curTaskID) /\
  (sched_refresh_high tskSt s).(curSchedPrio) = s.(curSchedPrio) /\
  (sched_refresh_high tskSt s).(ctxSwCtr) = s.(ctxSwCtr).
Proof. intros; repeat split; reflexivity. Qed.

Lemma sched_refresh_high_priority_in_range : forall sg tasks s p,
  sched_ready_in_range sg tasks s ->
  (sched_refresh_high tasks s).(highRdyPrio) = Some p ->
  task_priority_in_range sg p.
Proof.
  intros sg tasks s p Hready Hp.
  cbn [sched_refresh_high highRdyPrio] in Hp.
  destruct s.(readyList) as [|head rest] eqn:Hlist; [discriminate|].
  destruct (proj1 Hready head ltac:(rewrite Hlist; left; reflexivity))
    as [node [Hnode [Hrange Hstatus]]].
  rewrite Hnode in Hp; injection Hp as Hp; subst p; exact Hrange.
Qed.

Lemma sched_refresh_high_preserves_in_range : forall sg tasks s,
  task_pool_partition sg tasks -> sched_in_range sg tasks s ->
  sched_in_range sg tasks (sched_refresh_high tasks s).
Proof.
  intros sg tasks s Hpool [Hready [Hhigh [Hcounter Hcurrent]]].
  split; [exact Hready|]; split; [|split; [exact Hcounter|exact Hcurrent]].
  unfold sched_physical_cache_in_range, sched_refresh_high; simpl.
  destruct s.(readyList) as [|head tail] eqn:Hlist; [split; exact I|].
  destruct (proj1 Hready head ltac:(rewrite Hlist; left; reflexivity))
    as [t [Ht [Hprio _]]].
  rewrite Ht; split; [|left; exact Hprio].
  apply (proj2 (proj1 Hpool head)); left; exists t; exact Ht.
Qed.

(** The UInt counter write shared by OS_Sched and OSIntExit.  It precedes
    the external switch; it does not install current-task caches. *)
Definition sched_increment_switch_counter (s : SchedAbstractState) : SchedAbstractState :=
  {| readyList := s.(readyList); curTaskID := s.(curTaskID);
     curSchedPrio := s.(curSchedPrio); highRdyTid := s.(highRdyTid);
     highRdyPrio := s.(highRdyPrio); ctxSwCtr := (s.(ctxSwCtr) + 1) mod 4294967296;
     isRunning := s.(isRunning) |}.

Lemma sched_increment_switch_counter_in_range : forall s,
  0 <= (sched_increment_switch_counter s).(ctxSwCtr) < 4294967296.
Proof. intro s; apply Z.mod_pos_bound; lia. Qed.

Lemma sched_increment_switch_counter_preserves_in_range : forall sg tasks s,
  sched_in_range sg tasks s ->
  sched_in_range sg tasks (sched_increment_switch_counter s).
Proof.
  intros sg tasks s [Hready [Hhigh [Hcounter Hcurrent]]].
  split; [exact Hready|]; split; [exact Hhigh|]; split;
    [apply sched_increment_switch_counter_in_range|exact Hcurrent].
Qed.

Lemma sched_current_ready_at_implies_current_consistency :
  forall tskSt s tid t,
    sched_current_ready_at tskSt s tid t ->
    sched_current_consistency tskSt s.
Proof.
  intros tskSt s tid t Hready.
  unfold sched_current_ready_at in Hready.
  destruct Hready as [Hlookup [Hcurrent [Hprio _]]].
  unfold sched_current_consistency.
  rewrite Hcurrent.
  exists t; split; assumption.
Qed.

Lemma sched_current_blocked_before_schedule_implies_current_consistency :
  forall tskSt s tid t,
    sched_current_blocked_before_schedule tskSt s tid t ->
    sched_current_consistency tskSt s.
Proof.
  intros tskSt s tid t Hblocked.
  unfold sched_current_blocked_before_schedule in Hblocked.
  destruct Hblocked as [Hlookup [Hcurrent [Hprio _]]].
  unfold sched_current_consistency.
  rewrite Hcurrent.
  exists t; split; assumption.
Qed.

Lemma sched_current_ready_at_from_in_range_member :
  forall sg tskSt s tid,
    verification_slice_sched_in_range sg tskSt s ->
    s.(curTaskID) = Some tid ->
    In tid s.(readyList) ->
    exists t, sched_current_ready_at tskSt s tid t.
Proof.
  intros sg tskSt s tid Hrange Hcurrent Hin.
  unfold verification_slice_sched_in_range in Hrange.
  destruct Hrange as
    [Hmembers [_ [_ [_ [_ [_ Hcurrent_consistency]]]]]].
  destruct (Hmembers tid Hin) as [t [Hlookup Heffective]].
  unfold sched_current_consistency in Hcurrent_consistency.
  rewrite Hcurrent in Hcurrent_consistency.
  destruct Hcurrent_consistency as [t' [Hlookup' Hprio]].
  rewrite Hlookup in Hlookup'.
  inversion Hlookup'; subst t'.
  exists t.
  unfold sched_current_ready_at.
  repeat split; assumption.
Qed.

Lemma sched_task_call_boundary_from_in_range_member :
  forall sg tskSt s tid,
    verification_slice_sched_in_range sg tskSt s ->
    s.(isRunning) = true ->
    s.(curTaskID) = Some tid ->
    In tid s.(readyList) ->
    sched_task_call_boundary tskSt s.
Proof.
  intros sg tskSt s tid Hrange Hrunning Hcurrent Hin.
  unfold sched_task_call_boundary.
  split; [exact Hrunning |].
  exists tid.
  apply (sched_current_ready_at_from_in_range_member
    sg tskSt s tid Hrange Hcurrent Hin).
Qed.

Lemma sched_task_call_boundary_implies_current_consistency :
  forall tskSt s,
    sched_task_call_boundary tskSt s ->
    sched_current_consistency tskSt s.
Proof.
  intros tskSt s Hboundary.
  unfold sched_task_call_boundary in Hboundary.
  destruct Hboundary as [_ [tid [t Hready]]].
  eapply sched_current_ready_at_implies_current_consistency; eauto.
Qed.

Lemma sched_current_ready_at_not_blocked_before_schedule :
  forall tskSt s tid t,
    sched_current_ready_at tskSt s tid t ->
    ~ sched_current_blocked_before_schedule tskSt s tid t.
Proof.
  intros tskSt s tid t Hready Hblocked.
  unfold sched_current_ready_at in Hready.
  unfold sched_current_blocked_before_schedule in Hblocked.
  destruct Hready as [_ [_ [_ [Hin _]]]].
  destruct Hblocked as [_ [_ [_ [Hnotin _]]]].
  apply Hnotin; exact Hin.
Qed.

Lemma sched_task_call_boundary_nonvacuous :
  forall (sg : StableGlobVars) (tid : TaskID) (t : TaskAbstractState),
    is_effectively_ready t.(stat) t.(dly) = true ->
    exists tskSt s,
      verification_slice_sched_in_range sg tskSt s /\
      sched_task_call_boundary tskSt s.
Proof.
  intros sg tid t Heffective.
  exists
    {| inUsedTaskStates := fun tid' =>
         if Z.eqb tid' tid then Some t else None;
       unUsedTaskStates := [];
       tcbListHead := Some tid;
       prioTbl := fun _ => PTFree;
       taskRegNextID := 0;
       parkedTaskStacks := fun _ => None;
       taskLifecycle := empty_task_lifecycle;
     taskCount := 1 |}.
  exists
    {| readyList := [tid];
       curTaskID := Some tid;
       curSchedPrio := Some t.(curPrio);
       highRdyTid := Some tid;
       highRdyPrio := Some t.(curPrio);
       ctxSwCtr := 0;
       isRunning := true |}.
  split.
  - unfold verification_slice_sched_in_range.
    split.
    + intros tid' [Heq | Hnil]; [subst tid' | contradiction].
      exists t. cbn. rewrite Z.eqb_refl.
      split; [reflexivity | exact Heffective].
    + split.
      * cbn; exact I.
      * split.
        -- intros tid' t' Hlookup Hready.
           destruct (Z.eqb tid' tid) eqn:Heq; cbn in Hlookup.
           ++ apply Z.eqb_eq in Heq. subst tid'. left; reflexivity.
           ++ rewrite Heq in Hlookup. discriminate.
        -- split.
           ++ constructor.
              ** intros Hin; inversion Hin.
              ** constructor.
           ++ split.
              ** cbn; lia.
              ** split.
                 --- unfold sched_high_ready_consistency. cbn.
                     split; [reflexivity |].
                     exists t. rewrite Z.eqb_refl. split; reflexivity.
                 --- unfold sched_current_consistency. cbn.
                     exists t. rewrite Z.eqb_refl. split; reflexivity.
  - unfold sched_task_call_boundary.
    split; [reflexivity |].
    exists tid, t.
    unfold sched_current_ready_at. cbn. rewrite Z.eqb_refl.
    split; [reflexivity |].
    split; [reflexivity |].
    split; [reflexivity |].
    split; [left; reflexivity | exact Heffective].
Qed.

Lemma sched_current_blocked_before_schedule_nonvacuous :
  forall (sg : StableGlobVars) (tid : TaskID) (t : TaskAbstractState),
    is_effectively_ready t.(stat) t.(dly) = false ->
    exists tskSt s,
      verification_slice_sched_in_range sg tskSt s /\
      sched_current_blocked_before_schedule tskSt s tid t.
Proof.
  intros sg tid t Hblocked_ready.
  exists
    {| inUsedTaskStates := fun tid' =>
         if Z.eqb tid' tid then Some t else None;
       unUsedTaskStates := [];
       tcbListHead := Some tid;
       prioTbl := fun _ => PTFree;
       taskRegNextID := 0;
       parkedTaskStacks := fun _ => None;
       taskLifecycle := empty_task_lifecycle;
     taskCount := 1 |}.
  exists
    {| readyList := [];
       curTaskID := Some tid;
       curSchedPrio := Some t.(curPrio);
       highRdyTid := None;
       highRdyPrio := None;
       ctxSwCtr := 0;
       isRunning := true |}.
  split.
  - unfold verification_slice_sched_in_range.
    split.
    + intros tid' Hin; contradiction.
    + split.
      * cbn; exact I.
      * split.
        -- intros tid' t' Hlookup Heffective.
           destruct (Z.eqb tid' tid) eqn:Heq; cbn in Hlookup.
           ++ rewrite Heq in Hlookup. inversion Hlookup; subst t'.
              rewrite Hblocked_ready in Heffective. discriminate.
           ++ rewrite Heq in Hlookup. discriminate.
        -- split.
           ++ constructor.
           ++ split.
              ** cbn; lia.
              ** split.
                 --- unfold sched_high_ready_consistency. cbn.
                     split; reflexivity.
                 --- unfold sched_current_consistency. cbn.
                     exists t. rewrite Z.eqb_refl. split; reflexivity.
  - unfold sched_current_blocked_before_schedule.
    cbn. rewrite Z.eqb_refl. split; [reflexivity |].
    split; [reflexivity |].
    split; [reflexivity |].
    split.
    + intros Hin; contradiction.
    + exact Hblocked_ready.
Qed.

(* ================================================================== *)
(* Phase 4 Task 4.2:encode_ready_grp / encode_ready_tbl + store       *)
(* ================================================================== *)

(* 位图编码:OSRdyGrp 是 Y 维度位掩码 *)
Fixpoint encode_ready_grp (rl : list TaskID)
  (tskSt : Glob_TaskAbstractState) : Z :=
  match rl with
  | [] => 0
  | tid :: rest =>
      match tskSt.(inUsedTaskStates) tid with
      | Some t => Z.lor (Z.shiftl 1 (t.(curPrio) / 8))
                        (encode_ready_grp rest tskSt)
      | None => encode_ready_grp rest tskSt
      end
  end.

(* OSRdyTbl[Y] 是 X 维度位掩码 *)
Definition encode_ready_tbl_at (rl : list TaskID)
  (tskSt : Glob_TaskAbstractState) (y : Z) : Z :=
  fold_left (fun acc tid =>
    match tskSt.(inUsedTaskStates) tid with
    | Some t => if Z.eqb (t.(curPrio) / 8) y
                then acc + Z.shiftl 1 (t.(curPrio) mod 8)
                else acc
    | None => acc
    end) rl 0.

(* Source-total table encoder.  The concrete kernel sets bitmap cells with
   bitwise OR.  Unlike the stable additive encoder above, this definition
   remains exact if a transient state contains duplicate priority bits. *)
Definition encode_ready_tbl_at_or (rl : list TaskID)
  (tskSt : Glob_TaskAbstractState) (y : Z) : Z :=
  fold_right
    (fun tid acc =>
       match tskSt.(inUsedTaskStates) tid with
       | Some t =>
           if Z.eqb (t.(curPrio) / 8) y
           then Z.lor (Z.shiftl 1 (t.(curPrio) mod 8)) acc
           else acc
       | None => acc
       end)
    0 rl.

(* Exact total OSRdyGrp transition for moving one ready task to a new
   priority.  The old row bit is cleared only when removing the task made its
   ready-table row empty; the new row bit is then set unconditionally.  A
   total function is important here: callers can carry one equation through
   the C branch and reduce it with the branch-local cleared-row fact, without
   cross-producting an unrelated logical disjunction with control flow. *)
Definition ready_group_after_relocation
  (rdyGrp clearedOldRow oldBitY newBitY : Z) : Z :=
  Z.lor
    (if Z.eqb clearedOldRow 0
     then Z.land rdyGrp
            (unsigned_last_nbits (Z.lnot oldBitY) 8)
     else rdyGrp)
    newBitY.

(* verification_slice_store_sched_state:用 addr 直接表达；OSRdyTbl 数组由已证明的表示关系铺开。 *)
Definition verification_slice_store_sched_state (sg : StableGlobVars) (s : SchedAbstractState)
  (tskSt : Glob_TaskAbstractState) : Assertion :=
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp s.(readyList) tskSt **
  (sg.(g_OSRdyTbl) + 0) # UChar |->
    encode_ready_tbl_at s.(readyList) tskSt 0 **
  (sg.(g_OSRdyTbl) + 1) # UChar |->
    encode_ready_tbl_at s.(readyList) tskSt 1 **
  (sg.(g_OSRdyTbl) + 2) # UChar |->
    encode_ready_tbl_at s.(readyList) tskSt 2 **
  (sg.(g_OSRdyTbl) + 3) # UChar |->
    encode_ready_tbl_at s.(readyList) tskSt 3 **
  (sg.(g_OSRdyTbl) + 4) # UChar |->
    encode_ready_tbl_at s.(readyList) tskSt 4 **
  (sg.(g_OSRdyTbl) + 5) # UChar |->
    encode_ready_tbl_at s.(readyList) tskSt 5 **
  (sg.(g_OSRdyTbl) + 6) # UChar |->
    encode_ready_tbl_at s.(readyList) tskSt 6 **
  (sg.(g_OSRdyTbl) + 7) # UChar |->
    encode_ready_tbl_at s.(readyList) tskSt 7 **
  sg.(g_OSPrioCur) # UChar |->
    (match s.(curSchedPrio) with Some p => p | None => 0xFF end) **
  sg.(g_OSPrioHighRdy) # UChar |->
    (match s.(highRdyPrio) with Some p => p | None => 0xFF end) **
  sg.(g_OSTCBCur) # Ptr |->
    (match s.(curTaskID) with Some tid => verification_slice_tcb_addr sg tid | None => 0 end) **
  sg.(g_OSTCBHighRdy) # Ptr |->
    (match s.(highRdyTid) with Some tid => verification_slice_tcb_addr sg tid | None => 0 end) **
  sg.(g_OSCtxSwCtr) # UInt |-> s.(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if s.(isRunning) then 1 else 0).

Definition verification_slice_sched_tcb_cur_snapshot_prop (sg : StableGlobVars)
  (s : SchedAbstractState) (tcbcur : addr) : Prop :=
  tcbcur = match s.(curTaskID) with
           | Some tid => verification_slice_tcb_addr sg tid
           | None => 0
           end.

Definition verification_slice_store_sched_state_no_tcb_cur
  (sg : StableGlobVars) (s : SchedAbstractState)
  (tskSt : Glob_TaskAbstractState) : Assertion :=
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp s.(readyList) tskSt **
  (sg.(g_OSRdyTbl) + 0) # UChar |-> encode_ready_tbl_at s.(readyList) tskSt 0 **
  (sg.(g_OSRdyTbl) + 1) # UChar |-> encode_ready_tbl_at s.(readyList) tskSt 1 **
  (sg.(g_OSRdyTbl) + 2) # UChar |-> encode_ready_tbl_at s.(readyList) tskSt 2 **
  (sg.(g_OSRdyTbl) + 3) # UChar |-> encode_ready_tbl_at s.(readyList) tskSt 3 **
  (sg.(g_OSRdyTbl) + 4) # UChar |-> encode_ready_tbl_at s.(readyList) tskSt 4 **
  (sg.(g_OSRdyTbl) + 5) # UChar |-> encode_ready_tbl_at s.(readyList) tskSt 5 **
  (sg.(g_OSRdyTbl) + 6) # UChar |-> encode_ready_tbl_at s.(readyList) tskSt 6 **
  (sg.(g_OSRdyTbl) + 7) # UChar |-> encode_ready_tbl_at s.(readyList) tskSt 7 **
  sg.(g_OSPrioCur) # UChar |->
    (match s.(curSchedPrio) with Some p => p | None => 0xFF end) **
  sg.(g_OSPrioHighRdy) # UChar |->
    (match s.(highRdyPrio) with Some p => p | None => 0xFF end) **
  sg.(g_OSTCBHighRdy) # Ptr |->
    (match s.(highRdyTid) with Some tid => verification_slice_tcb_addr sg tid | None => 0 end) **
  sg.(g_OSCtxSwCtr) # UInt |-> s.(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if s.(isRunning) then 1 else 0).

Definition verification_slice_store_sched_state_rest_ready_current
  (sg : StableGlobVars) (s : SchedAbstractState) : Assertion :=
  sg.(g_OSPrioHighRdy) # UChar |->
    (match s.(highRdyPrio) with Some p => p | None => 0xFF end) **
  sg.(g_OSTCBHighRdy) # Ptr |->
    (match s.(highRdyTid) with Some tid => verification_slice_tcb_addr sg tid | None => 0 end) **
  sg.(g_OSCtxSwCtr) # UInt |-> s.(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if s.(isRunning) then 1 else 0).

Definition verification_slice_store_sched_state_rest_ready_prio
  (sg : StableGlobVars) (s : SchedAbstractState) : Assertion :=
  sg.(g_OSPrioHighRdy) # UChar |->
    (match s.(highRdyPrio) with Some p => p | None => 0xFF end) **
  sg.(g_OSTCBCur) # Ptr |->
    (match s.(curTaskID) with Some tid => verification_slice_tcb_addr sg tid | None => 0 end) **
  sg.(g_OSTCBHighRdy) # Ptr |->
    (match s.(highRdyTid) with Some tid => verification_slice_tcb_addr sg tid | None => 0 end) **
  sg.(g_OSCtxSwCtr) # UInt |-> s.(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if s.(isRunning) then 1 else 0).

(* A ready-priority relocation is performed while interrupts are disabled.
   The literal helper updates the ready bitmap, the current priority and the
   selected TCB, but deliberately leaves OSPrioHighRdy/OSTCBHighRdy for the
   later scheduler-selection step.  This predicate records that exact
   intermediate representation: every scheduler cell except the high-ready
   pair represents [post], while the untouched high-ready pair still
   represents [pre].  It is a staged representation, not a relaxation of
   [verification_slice_sched_in_range] or [verification_slice_sched_inv]. *)
Definition verification_slice_store_sched_state_ready_prio_stage
  (sg : StableGlobVars) (pre post : SchedAbstractState)
  (postTsk : Glob_TaskAbstractState) : Assertion :=
  sg.(g_OSRdyGrp) # UChar |->
    encode_ready_grp post.(readyList) postTsk **
  (sg.(g_OSRdyTbl) + 0) # UChar |->
    encode_ready_tbl_at post.(readyList) postTsk 0 **
  (sg.(g_OSRdyTbl) + 1) # UChar |->
    encode_ready_tbl_at post.(readyList) postTsk 1 **
  (sg.(g_OSRdyTbl) + 2) # UChar |->
    encode_ready_tbl_at post.(readyList) postTsk 2 **
  (sg.(g_OSRdyTbl) + 3) # UChar |->
    encode_ready_tbl_at post.(readyList) postTsk 3 **
  (sg.(g_OSRdyTbl) + 4) # UChar |->
    encode_ready_tbl_at post.(readyList) postTsk 4 **
  (sg.(g_OSRdyTbl) + 5) # UChar |->
    encode_ready_tbl_at post.(readyList) postTsk 5 **
  (sg.(g_OSRdyTbl) + 6) # UChar |->
    encode_ready_tbl_at post.(readyList) postTsk 6 **
  (sg.(g_OSRdyTbl) + 7) # UChar |->
    encode_ready_tbl_at post.(readyList) postTsk 7 **
  sg.(g_OSPrioCur) # UChar |->
    (match post.(curSchedPrio) with Some p => p | None => 0xFF end) **
  sg.(g_OSPrioHighRdy) # UChar |->
    (match pre.(highRdyPrio) with Some p => p | None => 0xFF end) **
  sg.(g_OSTCBCur) # Ptr |->
    (match post.(curTaskID) with Some tid => verification_slice_tcb_addr sg tid | None => 0 end) **
  sg.(g_OSTCBHighRdy) # Ptr |->
    (match pre.(highRdyTid) with Some tid => verification_slice_tcb_addr sg tid | None => 0 end) **
  sg.(g_OSCtxSwCtr) # UInt |-> post.(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if post.(isRunning) then 1 else 0).

Definition verification_slice_sched_inv_ready_prio_stage
  (sg : StableGlobVars) (pre post : SchedAbstractState)
  (postTsk : Glob_TaskAbstractState) : Assertion :=
  coq_prop (verification_slice_sched_in_range sg postTsk post) &&
  verification_slice_store_sched_state_ready_prio_stage sg pre post postTsk.

(* ================================================================== *)
(* Phase 4 Task 4.3:verification_slice_sched_inv                                         *)
(* ================================================================== *)

Definition verification_slice_sched_inv (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (s : SchedAbstractState) : Assertion :=
  coq_prop (verification_slice_sched_in_range sg tskSt s) && verification_slice_store_sched_state sg s tskSt.

Definition verification_slice_sched_inv_no_tcb_cur (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (s : SchedAbstractState) : Assertion :=
  coq_prop (verification_slice_sched_in_range sg tskSt s) &&
  verification_slice_store_sched_state_no_tcb_cur sg s tskSt.

Definition verification_slice_sched_inv_rest_ready_current (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (s : SchedAbstractState) : Assertion :=
  coq_prop (verification_slice_sched_in_range sg tskSt s) &&
  verification_slice_store_sched_state_rest_ready_current sg s.

Definition verification_slice_sched_inv_rest_ready_prio (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (s : SchedAbstractState) : Assertion :=
  coq_prop (verification_slice_sched_in_range sg tskSt s) &&
  verification_slice_store_sched_state_rest_ready_prio sg s.

(* ================================================================== *)
(* 2026-07-08:扩展性 helper — 证明 verification_slice_sched_inv 在 tskSt 非 inUsedTaskStates *)
(* 字段(如 prioTbl)改变时保持。用于解锁 mutex_func_sem.v 中            *)
(* 跨 event/task 的保持性结论由调用方在完整状态转换上证明。 *)
(* ================================================================== *)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import SumLib.ZRange.

Lemma encode_ready_grp_ext :
  forall rl tskSt1 tskSt2,
    tskSt1.(inUsedTaskStates) = tskSt2.(inUsedTaskStates) ->
    encode_ready_grp rl tskSt1 = encode_ready_grp rl tskSt2.
Proof.
  induction rl; intros tskSt1 tskSt2 HinU.
  - reflexivity.
  - simpl. rewrite HinU.
    destruct (tskSt2.(inUsedTaskStates) a) eqn:E.
    + simpl. f_equal. apply IHrl. exact HinU.
    + simpl. apply IHrl. exact HinU.
Qed.

Lemma fold_left_ext :
  forall (A B : Type) (f1 f2 : B -> A -> B) (rl : list A) (init : B),
    (forall (b : B) (a : A), f1 b a = f2 b a) ->
    fold_left f1 rl init = fold_left f2 rl init.
Proof.
  intros A B f1 f2 rl.
  induction rl; intros init Hin.
  - reflexivity.
  - simpl. rewrite Hin. apply IHrl. exact Hin.
Qed.

Lemma sched_fold_add_as_sum :
  forall (A : Type) (f : A -> Z) l acc,
    fold_left (fun z x => z + f x) l acc =
    acc + fold_right (fun x z => f x + z) 0 l.
Proof.
  intros A f l.
  induction l as [|a rest IH]; intro acc; simpl.
  - lia.
  - rewrite IH. simpl. lia.
Qed.

Lemma sched_land_single_bits_neq :
  forall i j,
    0 <= i -> 0 <= j -> i <> j ->
    Z.land (Z.shiftl 1 i) (Z.shiftl 1 j) = 0.
Proof.
  intros i j Hi Hj Hneq.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, !Z.shiftl_1_l,
    !Z.pow2_bits_eqb by assumption.
  rewrite Z.testbit_0_l.
  destruct (Z.eqb i n) eqn:Hin; destruct (Z.eqb j n) eqn:Hjn;
    try reflexivity.
  apply Z.eqb_eq in Hin, Hjn. congruence.
Qed.

Lemma sched_same_div_mod_priority :
  forall p q,
    0 <= p -> 0 <= q ->
    p / 8 = q / 8 -> p mod 8 = q mod 8 -> p = q.
Proof.
  intros p q Hp Hq Hdiv Hmod.
  pose proof (Z.div_mod p 8 ltac:(lia)) as Hpdm.
  pose proof (Z.div_mod q 8 ltac:(lia)) as Hqdm.
  lia.
Qed.

Lemma sched_bit_disjoint_tbl_or :
  forall l st y p,
    0 <= p ->
    p / 8 = y ->
    (forall tid t, In tid l -> st.(inUsedTaskStates) tid = Some t ->
       0 <= t.(curPrio)) ->
    (forall tid t, In tid l -> st.(inUsedTaskStates) tid = Some t ->
       t.(curPrio) <> p) ->
    Z.land (Z.shiftl 1 (p mod 8))
      (encode_ready_tbl_at_or l st y) = 0.
Proof.
  unfold encode_ready_tbl_at_or.
  induction l as [|a rest IH]; intros st y p Hp Hpy Hrange Hneq; simpl.
  - apply Z.land_0_r.
  - destruct (st.(inUsedTaskStates) a) as [ta|] eqn:Hgeta.
    + destruct (Z.eqb (ta.(curPrio) / 8) y) eqn:Hrow.
      * rewrite Z.land_lor_distr_r.
        rewrite IH with (st := st) (y := y) (p := p).
        2: exact Hp.
        2: exact Hpy.
        2: { intros; eapply Hrange; [right; eassumption | eassumption]. }
        2: { intros; eapply Hneq; [right; eassumption | eassumption]. }
        rewrite Z.lor_0_r.
        apply sched_land_single_bits_neq.
        -- apply Z.mod_pos_bound. lia.
        -- apply Z.mod_pos_bound. lia.
        -- intro Hmods.
           apply (Hneq a ta ltac:(left; reflexivity) Hgeta).
           apply sched_same_div_mod_priority; try eapply Hrange;
             try (left; reflexivity); try eassumption.
           ++ apply Z.eqb_eq in Hrow. lia.
           ++ symmetry. exact Hmods.
      * apply IH with (st := st) (y := y) (p := p); auto.
        -- intros; eapply Hrange; [right; eassumption | eassumption].
        -- intros; eapply Hneq; [right; eassumption | eassumption].
    + apply IH with (st := st) (y := y) (p := p); auto.
      * intros; eapply Hrange; [right; eassumption | eassumption].
      * intros; eapply Hneq; [right; eassumption | eassumption].
Qed.

Lemma encode_ready_tbl_at_eq_or :
  forall l st y,
    NoDup l ->
    task_priority_unique st ->
    (forall tid t, In tid l -> st.(inUsedTaskStates) tid = Some t ->
       0 <= t.(curPrio)) ->
    encode_ready_tbl_at l st y = encode_ready_tbl_at_or l st y.
Proof.
  intros l st y Hnd Hunique Hrange.
  unfold encode_ready_tbl_at.
  set (f := fun tid =>
    match st.(inUsedTaskStates) tid with
    | Some t => if Z.eqb (t.(curPrio) / 8) y
                then Z.shiftl 1 (t.(curPrio) mod 8) else 0
    | None => 0
    end).
  assert (Hconv : forall l0 acc,
    fold_left (fun acc0 tid =>
      match st.(inUsedTaskStates) tid with
      | Some t => if Z.eqb (t.(curPrio) / 8) y
                  then acc0 + Z.shiftl 1 (t.(curPrio) mod 8) else acc0
      | None => acc0
      end) l0 acc =
    fold_left (fun z tid => z + f tid) l0 acc).
  {
    intros l0 acc. apply fold_left_ext.
    intros z tid. unfold f.
    destruct (st.(inUsedTaskStates) tid);
      [destruct (Z.eqb (curPrio t / 8) y)|]; lia.
  }
  rewrite Hconv, sched_fold_add_as_sum. simpl.
  clear Hconv.
  unfold encode_ready_tbl_at_or.
  induction l as [|a rest IH]; simpl; [reflexivity|].
  inversion Hnd as [|? ? Hnotin Hndrest]; subst.
  destruct (st.(inUsedTaskStates) a) as [ta|] eqn:Hgeta.
  - destruct (Z.eqb (ta.(curPrio) / 8) y) eqn:Hrow.
    + rewrite IH.
      2: exact Hndrest.
      2: { intros; eapply Hrange; [right; eassumption | eassumption]. }
      unfold f. rewrite Hgeta, Hrow.
      pose proof
        (sched_bit_disjoint_tbl_or rest st y ta.(curPrio))
        as Hdisj.
      specialize
        (Hdisj ltac:(eapply Hrange; [left; reflexivity | exact Hgeta])).
      specialize (Hdisj ltac:(apply Z.eqb_eq in Hrow; exact Hrow)).
      specialize
        (Hdisj
          (fun tid t Hin Hget => Hrange tid t (or_intror Hin) Hget)).
      assert (Hneqrest : forall tid t,
        In tid rest -> st.(inUsedTaskStates) tid = Some t ->
        t.(curPrio) <> ta.(curPrio)).
      {
        intros tid t Hin Hget Heq.
        assert (tid = a) by (eapply Hunique; eassumption).
        subst tid. contradiction.
      }
      specialize (Hdisj Hneqrest).
      pose proof
        (Z.add_lor_land
          (Z.shiftl 1 (ta.(curPrio) mod 8))
          (encode_ready_tbl_at_or rest st y)) as Hadd.
      rewrite Hdisj, Z.add_0_r in Hadd.
      symmetry. exact Hadd.
    + rewrite IH.
      2: exact Hndrest.
      2: { intros; eapply Hrange; [right; eassumption | eassumption]. }
      unfold f. rewrite Hgeta, Hrow. lia.
  - rewrite IH.
    2: exact Hndrest.
    2: { intros; eapply Hrange; [right; eassumption | eassumption]. }
    unfold f. rewrite Hgeta. lia.
Qed.

(* Raw scheduler ownership uses the source-total OR encoder and deliberately
   omits [verification_slice_sched_in_range]. *)
Definition verification_slice_sched_raw_rep (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (s : SchedAbstractState) : Assertion :=
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp s.(readyList) tskSt **
  (sg.(g_OSRdyTbl) + 0) # UChar |->
    encode_ready_tbl_at_or s.(readyList) tskSt 0 **
  (sg.(g_OSRdyTbl) + 1) # UChar |->
    encode_ready_tbl_at_or s.(readyList) tskSt 1 **
  (sg.(g_OSRdyTbl) + 2) # UChar |->
    encode_ready_tbl_at_or s.(readyList) tskSt 2 **
  (sg.(g_OSRdyTbl) + 3) # UChar |->
    encode_ready_tbl_at_or s.(readyList) tskSt 3 **
  (sg.(g_OSRdyTbl) + 4) # UChar |->
    encode_ready_tbl_at_or s.(readyList) tskSt 4 **
  (sg.(g_OSRdyTbl) + 5) # UChar |->
    encode_ready_tbl_at_or s.(readyList) tskSt 5 **
  (sg.(g_OSRdyTbl) + 6) # UChar |->
    encode_ready_tbl_at_or s.(readyList) tskSt 6 **
  (sg.(g_OSRdyTbl) + 7) # UChar |->
    encode_ready_tbl_at_or s.(readyList) tskSt 7 **
  sg.(g_OSPrioCur) # UChar |->
    (match s.(curSchedPrio) with Some p => p | None => 0xFF end) **
  sg.(g_OSPrioHighRdy) # UChar |->
    (match s.(highRdyPrio) with Some p => p | None => 0xFF end) **
  sg.(g_OSTCBCur) # Ptr |->
    (match s.(curTaskID) with Some tid => verification_slice_tcb_addr sg tid | None => 0 end) **
  sg.(g_OSTCBHighRdy) # Ptr |->
    (match s.(highRdyTid) with Some tid => verification_slice_tcb_addr sg tid | None => 0 end) **
  sg.(g_OSCtxSwCtr) # UInt |-> s.(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if s.(isRunning) then 1 else 0).

(** Native OS_InitRdyList initializes both priority bytes to zero, not the
    verification slice's 255 sentinel.  None records no selected task and
    has this source-selected byte encoding; once selected, Some p owns p.
    A stale cache remains a physical observation, not a logical minimum. *)
Definition sched_priority_byte (p : option Priority) : Z :=
  match p with None => 0 | Some priority => priority end.

Definition sched_physical_rep (sg : StableGlobVars)
  (s : SchedAbstractState) : Assertion :=
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte s.(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte s.(highRdyPrio) **
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg s.(curTaskID) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg s.(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> s.(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if s.(isRunning) then 1 else 0).

Fixpoint sched_rows_rep (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (ready : list TaskID)
  (rows : list Z) : Assertion :=
  match rows with
  | [] => emp
  | y :: rest =>
      (sg.(g_OSRdyTbl) + y) # UChar |-> encode_ready_tbl_at_or ready tasks y **
      sched_rows_rep sg tasks ready rest
  end.

Definition sched_raw_rep (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (s : SchedAbstractState) : Assertion :=
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp s.(readyList) tasks **
  sched_rows_rep sg tasks s.(readyList) [0;1;2;3;4;5;6;7] **
  sched_physical_rep sg s.

(** The real residual of the OSRunning byte, not a second scheduler image
    or a permission to open a shared region. *)
Definition sched_physical_rep_without_running (sg : StableGlobVars)
  (s : SchedAbstractState) : Assertion :=
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte s.(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte s.(highRdyPrio) **
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg s.(curTaskID) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg s.(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> s.(ctxSwCtr).

Definition sched_raw_rep_without_running (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (s : SchedAbstractState) : Assertion :=
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp s.(readyList) tasks **
  sched_rows_rep sg tasks s.(readyList) [0;1;2;3;4;5;6;7] **
  sched_physical_rep_without_running sg s.

Lemma sched_raw_rep_split_running : forall sg tasks s,
  sched_raw_rep sg tasks s --||--
    (sg.(g_OSRunning) # UChar |-> (if s.(isRunning) then 1 else 0) **
     sched_raw_rep_without_running sg tasks s).
Proof.
  intros; unfold sched_raw_rep, sched_physical_rep,
    sched_raw_rep_without_running, sched_physical_rep_without_running.
  split; entailer!.
Qed.

Lemma sched_raw_rep_change_task_index : forall sg before after s,
  before.(inUsedTaskStates) = after.(inUsedTaskStates) ->
  sched_raw_rep sg before s = sched_raw_rep sg after s.
Proof.
  intros sg before after s Hused.
  unfold sched_raw_rep; cbn [sched_rows_rep].
  rewrite (encode_ready_grp_ext s.(readyList) before after Hused).
  unfold encode_ready_tbl_at_or; rewrite Hused; reflexivity.
Qed.

Definition sched_inv (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (s : SchedAbstractState) : Assertion :=
  coq_prop (sched_in_range sg tasks s) && sched_raw_rep sg tasks s.

Definition sched_boot : SchedAbstractState :=
  {| readyList := []; curTaskID := None; curSchedPrio := None;
     highRdyTid := None; highRdyPrio := None; ctxSwCtr := 0; isRunning := false |}.

Lemma sched_boot_in_range : forall sg tasks,
  (forall tid, tasks.(inUsedTaskStates) tid = None) ->
  sched_in_range sg tasks sched_boot.
Proof.
  intros sg tasks Hempty.
  split.
  - split; [intros tid H; contradiction|].
    split; [exact I|].
    split.
    + intros tid t H; rewrite Hempty in H; discriminate.
    + constructor.
  - split; [split; exact I|].
    split; [simpl; lia|split; exact I].
Qed.

Lemma sched_boot_priority_bytes :
  sched_priority_byte sched_boot.(curSchedPrio) = 0 /\
  sched_priority_byte sched_boot.(highRdyPrio) = 0.
Proof. split; reflexivity. Qed.

Lemma sched_ready_update_physical_frame : forall sg s ready,
  sched_physical_rep sg (sched_set_ready s ready) =
    sched_physical_rep sg s.
Proof. reflexivity. Qed.

(** Source-selected OSUnMapTbl (os_core.c, V2.93.01).  The zero byte
    deliberately maps to zero.  The bounded scan's default seven is useful
    only on nonzero input; it is not the semantics of this constant table. *)
Definition first_set8_nonzero (bits : Z) : Z :=
  if negb (Z.eqb (Z.land bits 1) 0) then 0 else
  if negb (Z.eqb (Z.land bits 2) 0) then 1 else
  if negb (Z.eqb (Z.land bits 4) 0) then 2 else
  if negb (Z.eqb (Z.land bits 8) 0) then 3 else
  if negb (Z.eqb (Z.land bits 16) 0) then 4 else
  if negb (Z.eqb (Z.land bits 32) 0) then 5 else
  if negb (Z.eqb (Z.land bits 64) 0) then 6 else 7.

Definition unmap_value (bits : Z) : Z :=
  if Z.eqb bits 0 then 0 else first_set8_nonzero bits.

Definition unmap_table : list Z :=
  map (fun index => unmap_value (Z.of_nat index)) (seq 0 256).

Lemma unmap_table_source_values_eq : unmap_table =
  [0;0;1;0;2;0;1;0;3;0;1;0;2;0;1;0;
   4;0;1;0;2;0;1;0;3;0;1;0;2;0;1;0;
   5;0;1;0;2;0;1;0;3;0;1;0;2;0;1;0;
   4;0;1;0;2;0;1;0;3;0;1;0;2;0;1;0;
   6;0;1;0;2;0;1;0;3;0;1;0;2;0;1;0;
   4;0;1;0;2;0;1;0;3;0;1;0;2;0;1;0;
   5;0;1;0;2;0;1;0;3;0;1;0;2;0;1;0;
   4;0;1;0;2;0;1;0;3;0;1;0;2;0;1;0;
   7;0;1;0;2;0;1;0;3;0;1;0;2;0;1;0;
   4;0;1;0;2;0;1;0;3;0;1;0;2;0;1;0;
   5;0;1;0;2;0;1;0;3;0;1;0;2;0;1;0;
   4;0;1;0;2;0;1;0;3;0;1;0;2;0;1;0;
   6;0;1;0;2;0;1;0;3;0;1;0;2;0;1;0;
   4;0;1;0;2;0;1;0;3;0;1;0;2;0;1;0;
   5;0;1;0;2;0;1;0;3;0;1;0;2;0;1;0;
   4;0;1;0;2;0;1;0;3;0;1;0;2;0;1;0].
Proof. reflexivity. Qed.

Lemma unmap_zero : unmap_value 0 = 0.
Proof. reflexivity. Qed.

Lemma unmap_nonzero_eq : forall bits,
  bits <> 0 -> unmap_value bits = first_set8_nonzero bits.
Proof.
  intros bits H; unfold unmap_value.
  assert (Z.eqb bits 0 = false) as Hzero by (apply Z.eqb_neq; exact H).
  rewrite Hzero; reflexivity.
Qed.

Lemma first_set8_nonzero_in_range : forall bits,
  0 <= first_set8_nonzero bits < 8.
Proof.
  intros bits; unfold first_set8_nonzero.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia.
Qed.

Lemma unmap_in_range : forall bits, 0 <= unmap_value bits < 8.
Proof.
  intros bits; unfold unmap_value; destruct (Z.eqb bits 0);
    [lia|apply first_set8_nonzero_in_range].
Qed.

Definition unmap_table_rep (sg : StableGlobVars) : Assertion :=
  UCharArray.full sg.(g_OSUnMapTbl) 256 unmap_table.

(** Source-total value semantics of OS_SchedNew, before either caller's
    priority-table read.  No nonempty-ready or OSRunning guard is invented. *)
Definition sched_selected_priority
  (tasks : Glob_TaskAbstractState) (s : SchedAbstractState) : Priority :=
  let y := unmap_value (encode_ready_grp s.(readyList) tasks) in
  y * 8 + unmap_value (encode_ready_tbl_at_or s.(readyList) tasks y).

Lemma sched_selected_priority_in_range : forall tasks s,
  0 <= sched_selected_priority tasks s < 64.
Proof.
  intros; unfold sched_selected_priority.
  pose proof (unmap_in_range (encode_ready_grp s.(readyList) tasks)).
  pose proof (unmap_in_range (encode_ready_tbl_at_or s.(readyList) tasks
    (unmap_value (encode_ready_grp s.(readyList) tasks)))); lia.
Qed.

Lemma sched_empty_selected_priority : forall tasks s,
  s.(readyList) = [] -> sched_selected_priority tasks s = 0.
Proof. intros tasks s H; unfold sched_selected_priority; rewrite H; reflexivity. Qed.

Definition sched_priority_write_state
  (tasks : Glob_TaskAbstractState) (s : SchedAbstractState) : SchedAbstractState :=
  sched_write_high_priority s (Some (sched_selected_priority tasks s)).

Definition sched_selected_pointer (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (s : SchedAbstractState) : addr :=
  prio_tbl_entry_to_addr sg (tasks.(prioTbl) (sched_selected_priority tasks s)).

(** The pointer observation is raw: free, reserved and task table cells are
    distinct even when the source caller domain has not yet been proved.
    In particular a reserved pointer is not encoded as a missing TaskID. *)
Record SchedSelection : Type := {
  selectionPriority : Priority;
  selectionPointer : addr;
}.

Definition sched_selection (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (s : SchedAbstractState) : SchedSelection :=
  {| selectionPriority := sched_selected_priority tasks s;
     selectionPointer := sched_selected_pointer sg tasks s |}.

Definition sched_switch_byte_guard (selected current : Z) : bool :=
  negb (Z.eqb selected current).

Lemma sched_switch_byte_guard_iff : forall selected current,
  sched_switch_byte_guard selected current = true <-> selected <> current.
Proof. intros; unfold sched_switch_byte_guard; rewrite Bool.negb_true_iff, Z.eqb_neq; reflexivity. Qed.

Lemma sched_empty_reads_slot_zero : forall sg tasks s,
  s.(readyList) = [] -> sched_selected_pointer sg tasks s =
    prio_tbl_entry_to_addr sg (tasks.(prioTbl) 0).
Proof.
  intros; unfold sched_selected_pointer;
    rewrite sched_empty_selected_priority by assumption; reflexivity.
Qed.

(** The bit-selection lemmas below are shared scheduler mathematics.  They
    were factored from the current Mutex refresh reasoning, but have no
    Mutex or legacy-cache premise. *)
Lemma first_set8_nonzero_min_bit :
  forall bits i,
    0 <= i < 8 ->
    (forall j, 0 <= j < i ->
      Z.land bits (Z.shiftl 1 j) = 0) ->
    Z.land bits (Z.shiftl 1 i) <> 0 ->
    first_set8_nonzero bits = i.
Proof.
  intros bits i Hi Hlower Hhit.
  assert (Hcases :
    i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/
    i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
  - change (Z.land bits 1 <> 0) in Hhit.
    unfold first_set8_nonzero.
    rewrite (proj2 (Z.eqb_neq (Z.land bits 1) 0) Hhit).
    reflexivity.
  - assert (H0 : Z.land bits 1 = 0).
    { change (Z.land bits (Z.shiftl 1 0) = 0).
      apply Hlower; lia. }
    change (Z.land bits 2 <> 0) in Hhit.
    unfold first_set8_nonzero.
    rewrite H0.
    rewrite (proj2 (Z.eqb_neq (Z.land bits 2) 0) Hhit).
    reflexivity.
  - assert (H0 : Z.land bits 1 = 0).
    { change (Z.land bits (Z.shiftl 1 0) = 0).
      apply Hlower; lia. }
    assert (H1 : Z.land bits 2 = 0).
    { change (Z.land bits (Z.shiftl 1 1) = 0).
      apply Hlower; lia. }
    change (Z.land bits 4 <> 0) in Hhit.
    unfold first_set8_nonzero.
    rewrite H0, H1.
    rewrite (proj2 (Z.eqb_neq (Z.land bits 4) 0) Hhit).
    reflexivity.
  - assert (H0 : Z.land bits 1 = 0).
    { change (Z.land bits (Z.shiftl 1 0) = 0).
      apply Hlower; lia. }
    assert (H1 : Z.land bits 2 = 0).
    { change (Z.land bits (Z.shiftl 1 1) = 0).
      apply Hlower; lia. }
    assert (H2 : Z.land bits 4 = 0).
    { change (Z.land bits (Z.shiftl 1 2) = 0).
      apply Hlower; lia. }
    change (Z.land bits 8 <> 0) in Hhit.
    unfold first_set8_nonzero.
    rewrite H0, H1, H2.
    rewrite (proj2 (Z.eqb_neq (Z.land bits 8) 0) Hhit).
    reflexivity.
  - assert (H0 : Z.land bits 1 = 0).
    { change (Z.land bits (Z.shiftl 1 0) = 0).
      apply Hlower; lia. }
    assert (H1 : Z.land bits 2 = 0).
    { change (Z.land bits (Z.shiftl 1 1) = 0).
      apply Hlower; lia. }
    assert (H2 : Z.land bits 4 = 0).
    { change (Z.land bits (Z.shiftl 1 2) = 0).
      apply Hlower; lia. }
    assert (H3 : Z.land bits 8 = 0).
    { change (Z.land bits (Z.shiftl 1 3) = 0).
      apply Hlower; lia. }
    change (Z.land bits 16 <> 0) in Hhit.
    unfold first_set8_nonzero.
    rewrite H0, H1, H2, H3.
    rewrite (proj2 (Z.eqb_neq (Z.land bits 16) 0) Hhit).
    reflexivity.
  - assert (H0 : Z.land bits 1 = 0).
    { change (Z.land bits (Z.shiftl 1 0) = 0).
      apply Hlower; lia. }
    assert (H1 : Z.land bits 2 = 0).
    { change (Z.land bits (Z.shiftl 1 1) = 0).
      apply Hlower; lia. }
    assert (H2 : Z.land bits 4 = 0).
    { change (Z.land bits (Z.shiftl 1 2) = 0).
      apply Hlower; lia. }
    assert (H3 : Z.land bits 8 = 0).
    { change (Z.land bits (Z.shiftl 1 3) = 0).
      apply Hlower; lia. }
    assert (H4 : Z.land bits 16 = 0).
    { change (Z.land bits (Z.shiftl 1 4) = 0).
      apply Hlower; lia. }
    change (Z.land bits 32 <> 0) in Hhit.
    unfold first_set8_nonzero.
    rewrite H0, H1, H2, H3, H4.
    rewrite (proj2 (Z.eqb_neq (Z.land bits 32) 0) Hhit).
    reflexivity.
  - assert (H0 : Z.land bits 1 = 0).
    { change (Z.land bits (Z.shiftl 1 0) = 0).
      apply Hlower; lia. }
    assert (H1 : Z.land bits 2 = 0).
    { change (Z.land bits (Z.shiftl 1 1) = 0).
      apply Hlower; lia. }
    assert (H2 : Z.land bits 4 = 0).
    { change (Z.land bits (Z.shiftl 1 2) = 0).
      apply Hlower; lia. }
    assert (H3 : Z.land bits 8 = 0).
    { change (Z.land bits (Z.shiftl 1 3) = 0).
      apply Hlower; lia. }
    assert (H4 : Z.land bits 16 = 0).
    { change (Z.land bits (Z.shiftl 1 4) = 0).
      apply Hlower; lia. }
    assert (H5 : Z.land bits 32 = 0).
    { change (Z.land bits (Z.shiftl 1 5) = 0).
      apply Hlower; lia. }
    change (Z.land bits 64 <> 0) in Hhit.
    unfold first_set8_nonzero.
    rewrite H0, H1, H2, H3, H4, H5.
    rewrite (proj2 (Z.eqb_neq (Z.land bits 64) 0) Hhit).
    reflexivity.
  - assert (H0 : Z.land bits 1 = 0).
    { change (Z.land bits (Z.shiftl 1 0) = 0).
      apply Hlower; lia. }
    assert (H1 : Z.land bits 2 = 0).
    { change (Z.land bits (Z.shiftl 1 1) = 0).
      apply Hlower; lia. }
    assert (H2 : Z.land bits 4 = 0).
    { change (Z.land bits (Z.shiftl 1 2) = 0).
      apply Hlower; lia. }
    assert (H3 : Z.land bits 8 = 0).
    { change (Z.land bits (Z.shiftl 1 3) = 0).
      apply Hlower; lia. }
    assert (H4 : Z.land bits 16 = 0).
    { change (Z.land bits (Z.shiftl 1 4) = 0).
      apply Hlower; lia. }
    assert (H5 : Z.land bits 32 = 0).
    { change (Z.land bits (Z.shiftl 1 5) = 0).
      apply Hlower; lia. }
    assert (H6 : Z.land bits 64 = 0).
    { change (Z.land bits (Z.shiftl 1 6) = 0).
      apply Hlower; lia. }
    unfold first_set8_nonzero.
    rewrite H0, H1, H2, H3, H4, H5, H6.
    reflexivity.
Qed.

Lemma sched_sorted_head_le :
  forall (A : Type) (key : A -> Z) head tail x,
    Ucos2Verify.lib.helpers.strictly_sorted_by key (head :: tail) ->
    In x (head :: tail) ->
    key head <= key x.
Proof.
  intros A key head tail.
  revert head.
  induction tail as [| next rest IH]; intros head x Hsorted Hin.
  - simpl in Hin. destruct Hin as [-> | []]. lia.
  - simpl in Hsorted. destruct Hsorted as [Hhead Hrest].
    simpl in Hin. destruct Hin as [-> | Hin]; [lia |].
    specialize (IH next x Hrest Hin). lia.
Qed.

Lemma sched_no_group_row :
  forall l st y,
    0 <= y ->
    (forall tid t, In tid l -> st.(inUsedTaskStates) tid = Some t ->
      0 <= t.(curPrio) / 8) ->
    (forall tid t, In tid l -> st.(inUsedTaskStates) tid = Some t ->
      t.(curPrio) / 8 <> y) ->
    Z.land (Z.shiftl 1 y) (encode_ready_grp l st) = 0.
Proof.
  induction l as [| a rest IH]; intros st y Hy Hrange Hnorow; simpl.
  - apply Z.land_0_r.
  - destruct (st.(inUsedTaskStates) a) as [ta |] eqn:Hgeta.
    + rewrite Z.land_lor_distr_r.
      rewrite IH with (st := st) (y := y).
      2: exact Hy.
      2: { intros; eapply Hrange; [right; eassumption | eassumption]. }
      2: { intros; eapply Hnorow; [right; eassumption | eassumption]. }
      rewrite Z.lor_0_r.
      apply sched_land_single_bits_neq.
      * exact Hy.
      * eapply Hrange; [left; reflexivity | exact Hgeta].
      * intro Heq. apply (Hnorow a ta ltac:(left; reflexivity) Hgeta).
        symmetry. exact Heq.
    + apply IH with (st := st) (y := y); auto.
      * intros; eapply Hrange; [right; eassumption | eassumption].
      * intros; eapply Hnorow; [right; eassumption | eassumption].
Qed.

Lemma sched_group_head_bit :
  forall head tail st t,
    st.(inUsedTaskStates) head = Some t ->
    0 <= t.(curPrio) ->
    Z.land (encode_ready_grp (head :: tail) st)
      (Z.shiftl 1 (t.(curPrio) / 8)) <> 0.
Proof.
  intros head tail st t Hlookup Hprio Hzero.
  assert (Hrow : 0 <= t.(curPrio) / 8) by (apply Z.div_pos; lia).
  assert (Hencbit :
    Z.testbit (encode_ready_grp (head :: tail) st)
      (t.(curPrio) / 8) = true).
  {
    simpl. rewrite Hlookup, Z.lor_spec,
      Z.shiftl_1_l, Z.pow2_bits_eqb, Z.eqb_refl by exact Hrow.
    reflexivity.
  }
  assert (Hmaskbit :
    Z.testbit (Z.shiftl 1 (t.(curPrio) / 8))
      (t.(curPrio) / 8) = true).
  { rewrite Z.shiftl_1_l, Z.pow2_bits_eqb, Z.eqb_refl by exact Hrow.
    reflexivity. }
  assert (Hlandbit :
    Z.testbit
      (Z.land (encode_ready_grp (head :: tail) st)
        (Z.shiftl 1 (t.(curPrio) / 8)))
      (t.(curPrio) / 8) = true).
  { rewrite Z.land_spec, Hencbit, Hmaskbit. reflexivity. }
  rewrite Hzero, Z.testbit_0_l in Hlandbit.
  discriminate.
Qed.

Lemma sched_tbl_head_bit :
  forall head tail st t,
    st.(inUsedTaskStates) head = Some t ->
    0 <= t.(curPrio) ->
    Z.land (encode_ready_tbl_at_or (head :: tail) st (t.(curPrio) / 8))
      (Z.shiftl 1 (t.(curPrio) mod 8)) <> 0.
Proof.
  intros head tail st t Hlookup Hprio Hzero.
  assert (Hcol : 0 <= t.(curPrio) mod 8) by (apply Z.mod_pos_bound; lia).
  assert (Hencbit :
    Z.testbit
      (encode_ready_tbl_at_or (head :: tail) st (t.(curPrio) / 8))
      (t.(curPrio) mod 8) = true).
  {
    simpl. rewrite Hlookup, Z.eqb_refl, Z.lor_spec,
      Z.shiftl_1_l, Z.pow2_bits_eqb, Z.eqb_refl by exact Hcol.
    reflexivity.
  }
  assert (Hmaskbit :
    Z.testbit (Z.shiftl 1 (t.(curPrio) mod 8))
      (t.(curPrio) mod 8) = true).
  { rewrite Z.shiftl_1_l, Z.pow2_bits_eqb, Z.eqb_refl by exact Hcol.
    reflexivity. }
  assert (Hlandbit :
    Z.testbit
      (Z.land
        (encode_ready_tbl_at_or (head :: tail) st (t.(curPrio) / 8))
        (Z.shiftl 1 (t.(curPrio) mod 8)))
      (t.(curPrio) mod 8) = true).
  { rewrite Z.land_spec, Hencbit, Hmaskbit. reflexivity. }
  rewrite Hzero, Z.testbit_0_l in Hlandbit.
  discriminate.
Qed.


Lemma unmap_table_Znth : forall bits,
  0 <= bits < 256 -> Znth bits unmap_table 0 = unmap_value bits.
Proof.
  intros bits Hbits; unfold Znth, unmap_table.
  rewrite (map_nth_len nat Z _ _ _ 0 0%nat) by (rewrite length_seq; lia).
  rewrite seq_nth by lia. simpl Nat.add. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma unmap_table_length : Zlength unmap_table = 256.
Proof. reflexivity. Qed.

Lemma unmap_table_split_cell : forall sg bits,
  0 <= bits < 256 ->
  unmap_table_rep sg |--
    (sg.(g_OSUnMapTbl) + bits * sizeof(UCHAR)) # UChar |-> unmap_value bits **
    UCharArray.missing_i sg.(g_OSUnMapTbl) bits 0 256 unmap_table.
Proof.
  intros sg bits Hbits; unfold unmap_table_rep.
  rewrite <- unmap_table_Znth by exact Hbits.
  apply UCharArray.full_split_to_missing_i; exact Hbits.
Qed.

(** A byte-owned bitmap, not a total Z decoder, justifies the 256-entry
    table read.  This keeps invalid abstract states from manufacturing C
    array access permission. *)
Lemma unmap_index_from_byte : forall address bits,
  address # UChar |-> bits |-- coq_prop (0 <= bits < 256).
Proof.
  intros; prop_apply_p (store_uchar_range address bits); Intros_p Hrange.
  apply derivable1s_coq_prop_r; change (0 <= bits <= 255) in Hrange; lia.
Qed.

Lemma unmap_min_bit : forall bits index,
  0 <= index < 8 ->
  (forall j, 0 <= j < index -> Z.land bits (Z.shiftl 1 j) = 0) ->
  Z.land bits (Z.shiftl 1 index) <> 0 ->
  unmap_value bits = index.
Proof.
  intros bits index Hindex Hlower Hhit.
  rewrite unmap_nonzero_eq.
  - apply first_set8_nonzero_min_bit; assumption.
  - intro Hzero; rewrite Hzero, Z.land_0_l in Hhit; contradiction.
Qed.

Lemma sched_unmap_minimum_priority : forall tasks head tail t,
  tasks.(inUsedTaskStates) head = Some t ->
  0 <= t.(curPrio) < 64 ->
  (forall tid other, In tid (head :: tail) ->
    tasks.(inUsedTaskStates) tid = Some other -> 0 <= other.(curPrio)) ->
  (forall tid other, In tid (head :: tail) ->
    tasks.(inUsedTaskStates) tid = Some other -> t.(curPrio) <= other.(curPrio)) ->
  let y := unmap_value (encode_ready_grp (head :: tail) tasks) in
  y * 8 + unmap_value (encode_ready_tbl_at_or (head :: tail) tasks y) = t.(curPrio).
Proof.
  intros tasks head tail t Hhead Hp Hnonneg Hminimum.
  assert (Hy : 0 <= t.(curPrio) / 8 < 8).
  { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
  assert (Hx : 0 <= t.(curPrio) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  assert (Hgroup : unmap_value (encode_ready_grp (head :: tail) tasks) =
    t.(curPrio) / 8).
  { apply unmap_min_bit; [exact Hy| |].
    - intros j Hj; rewrite Z.land_comm; apply sched_no_group_row.
      + lia.
      + intros; apply Z.div_pos; [eapply Hnonneg; eauto|lia].
      + intros tid other Hin Hget Hsame.
        pose proof (Hminimum tid other Hin Hget) as Hmin.
        assert (t.(curPrio) / 8 <= other.(curPrio) / 8) by
          (apply Z.div_le_mono; lia). lia.
    - apply sched_group_head_bit with (t := t); [exact Hhead|lia]. }
  rewrite Hgroup. cbv zeta.
  assert (Hrow : unmap_value
    (encode_ready_tbl_at_or (head :: tail) tasks (t.(curPrio) / 8)) =
      t.(curPrio) mod 8).
  { apply unmap_min_bit; [exact Hx| |].
    - intros j Hj; rewrite Z.land_comm.
      set (candidate := t.(curPrio) / 8 * 8 + j).
      assert (Hcandidate : 0 <= candidate) by (unfold candidate; lia).
      assert (Hdiv : candidate / 8 = t.(curPrio) / 8).
      { unfold candidate; rewrite Z.add_comm, Z.div_add by lia.
        rewrite Z.div_small by lia; lia. }
      assert (Hmod : candidate mod 8 = j).
      { unfold candidate; rewrite Z.add_comm, Z.mod_add by lia.
        apply Z.mod_small; lia. }
      rewrite <- Hmod; apply sched_bit_disjoint_tbl_or.
      + exact Hcandidate.
      + exact Hdiv.
      + exact Hnonneg.
      + intros tid other Hin Hget Heq.
        pose proof (Hminimum tid other Hin Hget).
        pose proof (Z.div_mod t.(curPrio) 8 ltac:(lia)).
        unfold candidate in Heq; lia.
    - apply sched_tbl_head_bit with (t := t); [exact Hhead|lia]. }
  rewrite Hrow. pose proof (Z.div_mod t.(curPrio) 8 ltac:(lia)); lia.
Qed.

Lemma sched_selected_priority_eq_head : forall sg tasks s head tail t,
  valid_stable_glob_vars sg ->
  sched_ready_in_range sg tasks s ->
  s.(readyList) = head :: tail ->
  tasks.(inUsedTaskStates) head = Some t ->
  sched_selected_priority tasks s = t.(curPrio).
Proof.
  intros sg tasks s head tail t Hsg [Hmembers [Hsorted Hrest]] Hready Hhead.
  unfold sched_selected_priority; rewrite Hready.
  assert (Hlowest : sg.(osLowestPrio) = 63).
  { unfold valid_stable_glob_vars in Hsg; tauto. }
  assert (Hrange : forall tid other, In tid (head :: tail) ->
    tasks.(inUsedTaskStates) tid = Some other -> 0 <= other.(curPrio) < 64).
  { intros tid other Hin Hget.
    assert (Hin' : In tid s.(readyList)) by (rewrite Hready; exact Hin).
    destruct (Hmembers tid Hin') as [found [Hfound [Hprio Hrdy]]].
    rewrite Hget in Hfound; inversion Hfound; subst found.
    unfold task_priority_in_range in Hprio; lia. }
  apply sched_unmap_minimum_priority; [exact Hhead| | |].
  - eapply Hrange; [left; reflexivity|exact Hhead].
  - intros; eapply (proj1 (Hrange _ _ H H0)).
  - intros tid other Hin Hget.
    rewrite Hready in Hsorted.
    pose proof (sched_sorted_head_le TaskID
      (fun id => match tasks.(inUsedTaskStates) id with
        | Some node => node.(curPrio) | None => sg.(osLowestPrio) + 1 end)
      head tail tid Hsorted Hin) as Hle.
    cbn beta in Hle. rewrite Hhead, Hget in Hle; exact Hle.
Qed.

Lemma sched_selected_pointer_eq_head : forall sg tasks s head tail t,
  valid_stable_glob_vars sg ->
  sched_ready_in_range sg tasks s ->
  task_current_prio_registered tasks ->
  s.(readyList) = head :: tail ->
  tasks.(inUsedTaskStates) head = Some t ->
  sched_selected_pointer sg tasks s = task_slot_addr sg head.
Proof.
  intros sg tasks s head tail t Hsg Hready Hregistered Hlist Hhead.
  unfold sched_selected_pointer.
  rewrite (sched_selected_priority_eq_head sg tasks s head tail t Hsg Hready Hlist Hhead).
  rewrite (Hregistered head t Hhead); reflexivity.
Qed.

Definition sched_physical_without_high (sg : StableGlobVars)
  (s : SchedAbstractState) : Assertion :=
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte s.(curSchedPrio) **
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg s.(curTaskID) **
  sg.(g_OSCtxSwCtr) # UInt |-> s.(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if s.(isRunning) then 1 else 0).

Definition sched_cache_cells (sg : StableGlobVars) (priority pointer : Z) : Assertion :=
  sg.(g_OSPrioHighRdy) # UChar |-> priority **
  sg.(g_OSTCBHighRdy) # Ptr |-> pointer.

Lemma sched_physical_split_high : forall sg s,
  sched_physical_rep sg s |--
    sched_cache_cells sg (sched_priority_byte s.(highRdyPrio))
      (encode_task_link sg s.(highRdyTid)) **
    sched_physical_without_high sg s.
Proof.
  intros; unfold sched_physical_rep, sched_cache_cells,
    sched_physical_without_high; entailer!.
Qed.

(** The priority byte is written first; the pointer cell still has its old
    physical value.  A later pointer write happens even on a no-switch path.
    A reserved raw address is kept distinct and is not folded into a TaskID. *)
Definition sched_priority_written_rep (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (s : SchedAbstractState) : Assertion :=
  sched_cache_cells sg (sched_selected_priority tasks s)
    (encode_task_link sg s.(highRdyTid)) **
  sched_physical_without_high sg s.

Definition sched_selection_written_rep (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (s : SchedAbstractState) : Assertion :=
  sched_cache_cells sg (sched_selected_priority tasks s)
    (sched_selected_pointer sg tasks s) **
  sched_physical_without_high sg s.

Lemma sched_priority_written_physical_eq : forall sg tasks s,
  sched_priority_written_rep sg tasks s --||--
    sched_physical_rep sg (sched_priority_write_state tasks s).
Proof.
  intros; unfold sched_priority_written_rep, sched_cache_cells,
    sched_physical_without_high, sched_priority_write_state,
    sched_physical_rep, sched_write_high_priority; simpl;
    split; entailer!.
Qed.

Lemma sched_selection_written_head_eq : forall sg tasks s head tail t,
  valid_stable_glob_vars sg -> sched_ready_in_range sg tasks s ->
  task_current_prio_registered tasks -> s.(readyList) = head :: tail ->
  tasks.(inUsedTaskStates) head = Some t ->
  sched_selection_written_rep sg tasks s --||--
    sched_physical_rep sg (sched_refresh_high tasks s).
Proof.
  intros sg tasks s head tail t Hsg Hrdy Hregistered Hlist Hhead.
  unfold sched_selection_written_rep, sched_cache_cells,
    sched_physical_without_high, sched_physical_rep,
    sched_refresh_high; simpl.
  rewrite (sched_selected_priority_eq_head sg tasks s head tail t Hsg Hrdy Hlist Hhead).
  rewrite (sched_selected_pointer_eq_head sg tasks s head tail t Hsg Hrdy Hregistered Hlist Hhead).
  rewrite Hlist; simpl; rewrite Hhead; simpl; split; entailer!.
Qed.

Definition sched_row_values (tasks : Glob_TaskAbstractState)
  (ready : list TaskID) : list Z :=
  map (encode_ready_tbl_at_or ready tasks) [0;1;2;3;4;5;6;7].

Lemma sched_rows_array_equiv : forall sg tasks ready,
  sched_rows_rep sg tasks ready [0;1;2;3;4;5;6;7] --||--
  UCharArray.full sg.(g_OSRdyTbl) 8 (sched_row_values tasks ready).
Proof.
  intros; unfold sched_row_values, UCharArray.full, store_array.
  cbn [map sched_rows_rep store_array_rec StoreUCharAsElement.storeA].
  rewrite sizeof_uchar; simpl. split; entailer!.
Qed.

Lemma sched_row_values_Znth : forall tasks ready y,
  0 <= y < 8 ->
  Znth y (sched_row_values tasks ready) 0 =
    encode_ready_tbl_at_or ready tasks y.
Proof.
  intros tasks ready y Hy.
  assert (y = 0 \/ y = 1 \/ y = 2 \/ y = 3 \/ y = 4 \/ y = 5 \/ y = 6 \/ y = 7) by lia.
  destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; reflexivity.
Qed.

Lemma sched_rows_split_cell : forall sg tasks ready y,
  0 <= y < 8 ->
  sched_rows_rep sg tasks ready [0;1;2;3;4;5;6;7] |--
    (sg.(g_OSRdyTbl) + y * sizeof(UCHAR)) # UChar |->
      encode_ready_tbl_at_or ready tasks y **
    UCharArray.missing_i sg.(g_OSRdyTbl) y 0 8 (sched_row_values tasks ready).
Proof.
  intros sg tasks ready y Hy.
  rewrite sched_rows_array_equiv.
  rewrite <- (sched_row_values_Znth tasks ready y Hy).
  apply UCharArray.full_split_to_missing_i; exact Hy.
Qed.

Lemma prio_table_values_Znth : forall sg table p,
  0 <= p < 64 ->
  Znth p (map (fun q => prio_tbl_entry_to_addr sg (table q))
    (Zrange 0 64)) 0 = prio_tbl_entry_to_addr sg (table p).
Proof.
  intros sg table p Hp.
  assert (Hlen : forall n low, List.length (Zrange_aux low n) = n).
  { induction n; intros; simpl; [reflexivity|rewrite IHn; reflexivity]. }
  assert (Hnth : forall n low i, (i < n)%nat ->
    nth i (Zrange_aux low n) 0 = low + Z.of_nat i).
  { induction n; intros low i Hi; [lia|].
    destruct i; simpl; [lia|rewrite IHn by lia; lia]. }
  unfold Znth, Zrange.
  rewrite (map_nth_len Z Z _ _ _ 0 0) by (rewrite Hlen; lia).
  rewrite Hnth by lia. rewrite Z2Nat.id by lia. simpl. reflexivity.
Qed.

(** The source table has free, reserved and task encodings.  This read rule
    keeps all three outcomes and does not require a nonempty ready set. *)
Lemma store_prio_tbl_split_selection : forall sg tasks s,
  store_prio_tbl sg tasks.(prioTbl) |--
    (sg.(g_OSTCBPrioTbl) + sched_selected_priority tasks s * sizeof(PTR))
      # Ptr |-> sched_selected_pointer sg tasks s **
    PtrArray.missing_i sg.(g_OSTCBPrioTbl) (sched_selected_priority tasks s)
      0 64 (map (fun q => prio_tbl_entry_to_addr sg (tasks.(prioTbl) q))
        (Zrange 0 64)).
Proof.
  intros; unfold store_prio_tbl, sched_selected_pointer.
  rewrite <- prio_table_values_Znth by apply sched_selected_priority_in_range.
  apply PtrArray.full_split_to_missing_i; apply sched_selected_priority_in_range.
Qed.

(** Read-only table focus returns the very same constant bytes. *)
Lemma unmap_table_merge_cell : forall sg bits,
  0 <= bits < 256 ->
  (sg.(g_OSUnMapTbl) + bits * sizeof(UCHAR)) # UChar |->
    unmap_value bits **
  UCharArray.missing_i sg.(g_OSUnMapTbl) bits 0 256 unmap_table |--
  unmap_table_rep sg.
Proof.
  intros sg bits Hbits; unfold unmap_table_rep.
  rewrite <- (unmap_table_Znth bits Hbits).
  eapply derivable1_trans.
  - apply UCharArray.missing_i_merge_to_full; exact Hbits.
  - rewrite replace_Znth_Znth; reflexivity.
Qed.

Lemma sched_rows_merge_cell : forall sg tasks ready y,
  0 <= y < 8 ->
  (sg.(g_OSRdyTbl) + y * sizeof(UCHAR)) # UChar |->
    encode_ready_tbl_at_or ready tasks y **
  UCharArray.missing_i sg.(g_OSRdyTbl) y 0 8 (sched_row_values tasks ready) |--
  sched_rows_rep sg tasks ready [0;1;2;3;4;5;6;7].
Proof.
  intros sg tasks ready y Hy; rewrite sched_rows_array_equiv.
  rewrite <- (sched_row_values_Znth tasks ready y Hy).
  eapply derivable1_trans.
  - apply UCharArray.missing_i_merge_to_full; exact Hy.
  - rewrite replace_Znth_Znth; reflexivity.
Qed.

(** A changed row is rebuilt as an exact array update.  Relating that array
    to a changed ready set is the producer's separate bitmap equation. *)
Lemma sched_rows_merge_updated_array : forall sg tasks ready y value,
  0 <= y < 8 ->
  (sg.(g_OSRdyTbl) + y * sizeof(UCHAR)) # UChar |-> value **
  UCharArray.missing_i sg.(g_OSRdyTbl) y 0 8 (sched_row_values tasks ready) |--
  UCharArray.full sg.(g_OSRdyTbl) 8
    (replace_Znth y value (sched_row_values tasks ready)).
Proof. intros; apply UCharArray.missing_i_merge_to_full; assumption. Qed.

Lemma store_prio_tbl_merge_selection : forall sg tasks s,
  (sg.(g_OSTCBPrioTbl) + sched_selected_priority tasks s * sizeof(PTR))
    # Ptr |-> sched_selected_pointer sg tasks s **
  PtrArray.missing_i sg.(g_OSTCBPrioTbl) (sched_selected_priority tasks s)
    0 64 (map (fun q => prio_tbl_entry_to_addr sg (tasks.(prioTbl) q))
      (Zrange 0 64)) |--
  store_prio_tbl sg tasks.(prioTbl).
Proof.
  intros; unfold store_prio_tbl, sched_selected_pointer.
  rewrite <- prio_table_values_Znth by apply sched_selected_priority_in_range.
  eapply derivable1_trans.
  - apply PtrArray.missing_i_merge_to_full; apply sched_selected_priority_in_range.
  - rewrite replace_Znth_Znth; reflexivity.
Qed.

Lemma store_prio_tbl_merge_updated_array : forall sg tasks s pointer,
  (sg.(g_OSTCBPrioTbl) + sched_selected_priority tasks s * sizeof(PTR))
    # Ptr |-> pointer **
  PtrArray.missing_i sg.(g_OSTCBPrioTbl) (sched_selected_priority tasks s)
    0 64 (map (fun q => prio_tbl_entry_to_addr sg (tasks.(prioTbl) q))
      (Zrange 0 64)) |--
  PtrArray.full sg.(g_OSTCBPrioTbl) 64
    (replace_Znth (sched_selected_priority tasks s) pointer
      (map (fun q => prio_tbl_entry_to_addr sg (tasks.(prioTbl) q))
        (Zrange 0 64))).
Proof.
  intros; apply PtrArray.missing_i_merge_to_full;
    apply sched_selected_priority_in_range.
Qed.

Lemma sched_physical_merge_high : forall sg s,
  sched_cache_cells sg (sched_priority_byte s.(highRdyPrio))
    (encode_task_link sg s.(highRdyTid)) **
  sched_physical_without_high sg s |--
  sched_physical_rep sg s.
Proof.
  intros; unfold sched_cache_cells, sched_physical_without_high,
    sched_physical_rep; entailer!.
Qed.

Lemma sched_physical_merge_high_updated : forall sg s priority tid,
  sched_cache_cells sg (sched_priority_byte priority)
    (encode_task_link sg tid) **
  sched_physical_without_high sg s |--
  sched_physical_rep sg
    (sched_write_high_pointer
      (sched_write_high_priority s priority) tid).
Proof.
  intros; unfold sched_cache_cells, sched_physical_without_high,
    sched_physical_rep, sched_write_high_priority,
    sched_write_high_pointer; simpl; entailer!.
Qed.

Definition sched_physical_without_counter (sg : StableGlobVars)
  (s : SchedAbstractState) : Assertion :=
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte s.(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte s.(highRdyPrio) **
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg s.(curTaskID) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg s.(highRdyTid) **
  sg.(g_OSRunning) # UChar |-> (if s.(isRunning) then 1 else 0).

Lemma sched_physical_split_counter : forall sg s,
  sched_physical_rep sg s |--
  sg.(g_OSCtxSwCtr) # UInt |-> s.(ctxSwCtr) ** sched_physical_without_counter sg s.
Proof.
  intros; unfold sched_physical_rep, sched_physical_without_counter; entailer!.
Qed.

Lemma sched_physical_merge_counter : forall sg s,
  sg.(g_OSCtxSwCtr) # UInt |-> s.(ctxSwCtr) ** sched_physical_without_counter sg s |--
  sched_physical_rep sg s.
Proof.
  intros; unfold sched_physical_rep, sched_physical_without_counter; entailer!.
Qed.

Lemma sched_physical_merge_incremented_counter : forall sg s,
  sg.(g_OSCtxSwCtr) # UInt |-> ((s.(ctxSwCtr) + 1) mod 4294967296) **
  sched_physical_without_counter sg s |--
  sched_physical_rep sg (sched_increment_switch_counter s).
Proof.
  intros; unfold sched_physical_rep, sched_physical_without_counter,
    sched_increment_switch_counter; simpl; entailer!.
Qed.

(** Only established current/head lookups connect the source byte comparison
    to the abstract ready-or-different-task guard.  No OSRunning test or
    source-level nonempty/missing-current fallback is added. *)
Lemma sched_switch_byte_guard_eq_ready_guard :
  forall sg tasks s head tail head_task current current_task,
  valid_stable_glob_vars sg ->
  sched_ready_in_range sg tasks s ->
  task_current_prio_registered tasks ->
  sched_current_consistency tasks s ->
  s.(readyList) = head :: tail ->
  tasks.(inUsedTaskStates) head = Some head_task ->
  s.(curTaskID) = Some current ->
  tasks.(inUsedTaskStates) current = Some current_task ->
  sched_switch_byte_guard (sched_selected_priority tasks s)
    (sched_priority_byte s.(curSchedPrio)) =
  (negb (is_effectively_ready current_task.(stat) current_task.(dly) &&
     existsb (Z.eqb current) s.(readyList)) ||
   negb (Z.eqb head current))%bool.
Proof.
  intros sg tasks s head tail head_task current current_task Hsg Hrdy
    Hregistered Hconsistent Hlist Hhead Hcurrent Hcur.
  rewrite (sched_selected_priority_eq_head sg tasks s head tail
    head_task Hsg Hrdy Hlist Hhead).
  unfold sched_current_consistency in Hconsistent; rewrite Hcurrent in Hconsistent.
  destruct Hconsistent as [found [Hfound Hprio]].
  rewrite Hcur in Hfound; inversion Hfound; subst found.
  rewrite Hprio; cbn [sched_priority_byte].
  unfold sched_switch_byte_guard.
  destruct (Z.eq_dec head current) as [Heq | Hneq].
  - subst current; rewrite Hhead in Hcur; inversion Hcur; subst current_task.
    destruct Hrdy as [Hmembers _].
    assert (Hin : In head s.(readyList)) by (rewrite Hlist; left; reflexivity).
    destruct (Hmembers head Hin) as [ready_task [Hget [_ Hready]]].
    rewrite Hhead in Hget; inversion Hget; subst ready_task.
    rewrite Hready, Hlist; simpl; rewrite !Z.eqb_refl; reflexivity.
  - assert (Hprio_neq : head_task.(curPrio) <> current_task.(curPrio)).
    { intro Heq.
      pose proof (Hregistered head head_task Hhead) as Hhead_registered.
      pose proof (Hregistered current current_task Hcur) as Hcur_registered.
      rewrite Heq, Hcur_registered in Hhead_registered.
      inversion Hhead_registered; congruence. }
    rewrite (proj2 (Z.eqb_neq _ _) Hprio_neq),
      (proj2 (Z.eqb_neq _ _) Hneq).
    simpl; rewrite Bool.orb_true_r; reflexivity.
Qed.

(* Raw relocation stage: every updated scheduler cell represents [post],
   while the high-ready cache pair remains anchored in [pre] until the
   subsequent scheduler-selection step. *)
Definition verification_slice_sched_raw_ready_prio_stage
  (sg : StableGlobVars) (pre post : SchedAbstractState)
  (postTsk : Glob_TaskAbstractState) : Assertion :=
  sg.(g_OSRdyGrp) # UChar |->
    encode_ready_grp post.(readyList) postTsk **
  (sg.(g_OSRdyTbl) + 0) # UChar |->
    encode_ready_tbl_at_or post.(readyList) postTsk 0 **
  (sg.(g_OSRdyTbl) + 1) # UChar |->
    encode_ready_tbl_at_or post.(readyList) postTsk 1 **
  (sg.(g_OSRdyTbl) + 2) # UChar |->
    encode_ready_tbl_at_or post.(readyList) postTsk 2 **
  (sg.(g_OSRdyTbl) + 3) # UChar |->
    encode_ready_tbl_at_or post.(readyList) postTsk 3 **
  (sg.(g_OSRdyTbl) + 4) # UChar |->
    encode_ready_tbl_at_or post.(readyList) postTsk 4 **
  (sg.(g_OSRdyTbl) + 5) # UChar |->
    encode_ready_tbl_at_or post.(readyList) postTsk 5 **
  (sg.(g_OSRdyTbl) + 6) # UChar |->
    encode_ready_tbl_at_or post.(readyList) postTsk 6 **
  (sg.(g_OSRdyTbl) + 7) # UChar |->
    encode_ready_tbl_at_or post.(readyList) postTsk 7 **
  sg.(g_OSPrioCur) # UChar |->
    (match post.(curSchedPrio) with Some p => p | None => 0xFF end) **
  sg.(g_OSPrioHighRdy) # UChar |->
    (match pre.(highRdyPrio) with Some p => p | None => 0xFF end) **
  sg.(g_OSTCBCur) # Ptr |->
    (match post.(curTaskID) with Some tid => verification_slice_tcb_addr sg tid | None => 0 end) **
  sg.(g_OSTCBHighRdy) # Ptr |->
    (match pre.(highRdyTid) with Some tid => verification_slice_tcb_addr sg tid | None => 0 end) **
  sg.(g_OSCtxSwCtr) # UInt |-> post.(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if post.(isRunning) then 1 else 0).

Lemma sched_stable_tbl_eq_or :
  forall sg tskSt s y,
    verification_slice_task_validity sg tskSt ->
    verification_slice_sched_in_range sg tskSt s ->
    encode_ready_tbl_at s.(readyList) tskSt y =
    encode_ready_tbl_at_or s.(readyList) tskSt y.
Proof.
  intros sg tskSt s y Htask Hsched.
  unfold verification_slice_task_validity in Htask.
  destruct Htask as [Htask_valid Htask_fields].
  unfold verification_slice_task_in_range in Htask_valid.
  destruct Htask_valid as [_ [_ [_ [_ [_ [_ Hunique]]]]]].
  unfold verification_slice_sched_in_range in Hsched.
  destruct Hsched as [_ [_ [_ [Hnodup _]]]].
  apply encode_ready_tbl_at_eq_or; try assumption.
  intros tid t Hin Hlookup.
  specialize (Htask_fields tid t Hlookup).
  destruct Htask_fields as [[Hnonneg _] _].
  exact Hnonneg.
Qed.

Lemma verification_slice_sched_inv_split_raw_validity :
  forall sg tskSt s,
    verification_slice_task_validity sg tskSt ->
    verification_slice_sched_inv sg tskSt s |--
      verification_slice_sched_raw_rep sg tskSt s &&
      coq_prop (verification_slice_sched_in_range sg tskSt s).
Proof.
  intros sg tskSt s Htask.
  intros h Hinv.
  unfold verification_slice_sched_inv, andp, coq_prop in Hinv.
  destruct Hinv as [Hrange Hstore].
  split.
  - assert (Heq : forall y,
      encode_ready_tbl_at s.(readyList) tskSt y =
      encode_ready_tbl_at_or s.(readyList) tskSt y).
    {
      intro y.
      apply (sched_stable_tbl_eq_or sg tskSt s y); assumption.
    }
    unfold verification_slice_sched_raw_rep, verification_slice_store_sched_state in *.
    rewrite <- (Heq 0), <- (Heq 1), <- (Heq 2), <- (Heq 3),
      <- (Heq 4), <- (Heq 5), <- (Heq 6), <- (Heq 7).
    exact Hstore.
  - exact Hrange.
Qed.

Lemma encode_ready_tbl_at_ext :
  forall rl tskSt1 tskSt2 y,
    tskSt1.(inUsedTaskStates) = tskSt2.(inUsedTaskStates) ->
    encode_ready_tbl_at rl tskSt1 y = encode_ready_tbl_at rl tskSt2 y.
Proof.
  intros rl tskSt1 tskSt2 y HinU.
  unfold encode_ready_tbl_at.
  apply fold_left_ext.
  intros acc tid.
  rewrite HinU. reflexivity.
Qed.

Lemma verification_slice_sched_in_range_ext :
  forall sg tskSt1 tskSt2 schedSt,
    tskSt1.(inUsedTaskStates) = tskSt2.(inUsedTaskStates) ->
    verification_slice_sched_in_range sg tskSt1 schedSt = verification_slice_sched_in_range sg tskSt2 schedSt.
Proof.
  intros sg tskSt1 tskSt2 schedSt HinU.
  unfold verification_slice_sched_in_range, sched_high_ready_consistency, sched_current_consistency.
  rewrite HinU. reflexivity.
Qed.

Lemma verification_slice_store_sched_state_ext :
  forall sg tskSt1 tskSt2 schedSt,
    tskSt1.(inUsedTaskStates) = tskSt2.(inUsedTaskStates) ->
    verification_slice_store_sched_state sg schedSt tskSt1 = verification_slice_store_sched_state sg schedSt tskSt2.
Proof.
  intros sg tskSt1 tskSt2 schedSt HinU.
  unfold verification_slice_store_sched_state.
  rewrite (encode_ready_grp_ext _ _ _ HinU).
  rewrite (encode_ready_tbl_at_ext _ _ _ 0 HinU).
  rewrite (encode_ready_tbl_at_ext _ _ _ 1 HinU).
  rewrite (encode_ready_tbl_at_ext _ _ _ 2 HinU).
  rewrite (encode_ready_tbl_at_ext _ _ _ 3 HinU).
  rewrite (encode_ready_tbl_at_ext _ _ _ 4 HinU).
  rewrite (encode_ready_tbl_at_ext _ _ _ 5 HinU).
  rewrite (encode_ready_tbl_at_ext _ _ _ 6 HinU).
  rewrite (encode_ready_tbl_at_ext _ _ _ 7 HinU).
  reflexivity.
Qed.

Lemma verification_slice_sched_inv_ext :
  forall sg tskSt1 tskSt2 schedSt,
    tskSt1.(inUsedTaskStates) = tskSt2.(inUsedTaskStates) ->
    verification_slice_sched_inv sg tskSt1 schedSt = verification_slice_sched_inv sg tskSt2 schedSt.
Proof.
  intros sg tskSt1 tskSt2 schedSt HinU.
  unfold verification_slice_sched_inv.
  rewrite (verification_slice_sched_in_range_ext _ _ _ _ HinU).
  rewrite (verification_slice_store_sched_state_ext _ _ _ _ HinU).
  reflexivity.
Qed.

Lemma verification_slice_sched_in_range_preserved_by_tskSt_nonSchedFields_update :
  forall sg tskSt1 tskSt2 schedSt cur_tid t t',
    tskSt1.(inUsedTaskStates) cur_tid = Some t ->
    t'.(curPrio) = t.(curPrio) ->
    t'.(stat) = t.(stat) ->
    t'.(dly) = t.(dly) ->
    tskSt2 = {| inUsedTaskStates := fun tid =>
                  if Z.eqb tid cur_tid then Some t'
                  else tskSt1.(inUsedTaskStates) tid;
                unUsedTaskStates := tskSt1.(unUsedTaskStates);
                tcbListHead      := tskSt1.(tcbListHead);
                prioTbl          := tskSt1.(prioTbl);
                taskRegNextID := tskSt1.(taskRegNextID);
                parkedTaskStacks := tskSt1.(parkedTaskStacks);
                taskLifecycle := tskSt1.(taskLifecycle);
     taskCount        := tskSt1.(taskCount); |} ->
    verification_slice_sched_in_range sg tskSt1 schedSt ->
    verification_slice_sched_in_range sg tskSt2 schedSt.
Proof.
  intros sg tskSt1 tskSt2 schedSt cur_tid t t'
    Hget Hcp' Hstat' Hdly' HtskSt2 [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].
  subst tskSt2.
  split.
  - intros tid_in Hin.
    destruct (H1 tid_in Hin) as [t0 [Hget0 Hready0]].
    destruct (Z.eqb tid_in cur_tid) eqn:Heq_tin.
    { apply Z.eqb_eq in Heq_tin. subst tid_in.
      rewrite Hget0 in Hget. injection Hget as ->.
      exists t'. split.
      - simpl. rewrite Z.eqb_refl. reflexivity.
      - rewrite Hstat', Hdly'. exact Hready0. }
    { exists t0. split.
      - simpl. rewrite Heq_tin. exact Hget0.
      - exact Hready0. }
  - split.
    + assert (Hext : forall x,
        (fun tid => match tskSt1.(inUsedTaskStates) tid with
                    | Some task => task.(curPrio)
                    | None => sg.(osLowestPrio) + 1
                    end) x =
        (fun tid => match ( {| inUsedTaskStates := fun tid => if Z.eqb tid cur_tid then Some t' else tskSt1.(inUsedTaskStates) tid;
                            unUsedTaskStates := tskSt1.(unUsedTaskStates);
                            tcbListHead := tskSt1.(tcbListHead);
                            prioTbl := tskSt1.(prioTbl);
                            taskRegNextID := tskSt1.(taskRegNextID);
                            parkedTaskStacks := tskSt1.(parkedTaskStacks);
                            taskLifecycle := tskSt1.(taskLifecycle);
     taskCount := tskSt1.(taskCount); |} ).(inUsedTaskStates) tid with
                    | Some task => task.(curPrio)
                    | None => sg.(osLowestPrio) + 1
                    end) x).
      { intros x. destruct (Z.eqb x cur_tid) eqn:Heq_x.
        - apply Z.eqb_eq in Heq_x. subst x.
          simpl. rewrite Hget. rewrite Z.eqb_refl. simpl. rewrite Hcp'. reflexivity.
        - simpl. rewrite Heq_x. simpl. reflexivity. }
      exact (strictly_sorted_by_key_ext _ _ _ _ Hext H2).
    + split.
      * intros tid_in t0 Hget0 Hready0.
        destruct (Z.eqb tid_in cur_tid) eqn:Heq_tin.
        { apply Z.eqb_eq in Heq_tin. subst tid_in.
          simpl in Hget0. rewrite Z.eqb_refl in Hget0. inversion Hget0. subst t0.
          apply (H3 cur_tid t Hget).
          rewrite <- Hstat', <- Hdly'. exact Hready0. }
        { simpl in Hget0. rewrite Heq_tin in Hget0.
          apply (H3 tid_in t0 Hget0 Hready0). }
      * split.
        -- exact H4.
        -- split.
           ++ exact H5.
           ++ split.
              ** unfold sched_high_ready_consistency in *.
                 remember (schedSt.(readyList)) as rl in *.
                 destruct rl as [|hd tl].
                +++ exact H6.
                +++ cbv beta iota in H6. destruct H6 as [Hhrt [t0 [Hget0 Hhrp]]].
                    split.
                    --- exact Hhrt.
                    --- destruct (Z.eqb hd cur_tid) eqn:Heq_hd.
                        { apply Z.eqb_eq in Heq_hd. subst hd.
                          simpl. rewrite Hget. rewrite Z.eqb_refl. simpl.
                          rewrite Hget0 in Hget. inversion Hget. subst t0.
                          exists t'. split. reflexivity. rewrite Hcp'. exact Hhrp. }
                        { simpl. rewrite Heq_hd. simpl.
                          exists t0. split. exact Hget0. exact Hhrp. }
              ** unfold sched_current_consistency in *.
                 remember (schedSt.(curTaskID)) as cid in *.
                 destruct cid as [ctid|].
                +++ cbv beta iota in H7. destruct H7 as [t0 [Hget0 Hcsp]].
                    destruct (Z.eqb ctid cur_tid) eqn:Heq_ctid.
                    { apply Z.eqb_eq in Heq_ctid. subst ctid.
                      simpl. rewrite Hget. rewrite Z.eqb_refl. simpl.
                      rewrite Hget0 in Hget. inversion Hget. subst t0.
                      exists t'. split. reflexivity. rewrite Hcp'. exact Hcsp. }
                    { simpl. rewrite Heq_ctid. simpl.
                      exists t0. split. exact Hget0. exact Hcsp. }
                +++ exact H7.
Qed.


(* ================================================================== *)
(* 2026-07-10:make_ready helper — 用于 atomic_event_task_rdy 等场景   *)
(* TskState 变(ready_tid: t -> t',curPrio 不变)                       *)
(* SchedState 变(readyList: 若 t' ready 则 insert_sorted_by 加入 cur_tid, *)
(*                否则不变;highRdyTid/highRdyPrio 重计算)                *)
(* ================================================================== *)

Lemma verification_slice_sched_in_range_preserved_by_make_ready :
  forall sg tskSt1 tskSt2 schedSt1 schedSt2 cur_tid t t' ready_after,
    tskSt1.(inUsedTaskStates) cur_tid = Some t ->
    t'.(curPrio) = t.(curPrio) ->
    tskSt2 = {| inUsedTaskStates := fun tid =>
                  if Z.eqb tid cur_tid then Some t'
                  else tskSt1.(inUsedTaskStates) tid;
                unUsedTaskStates := tskSt1.(unUsedTaskStates);
                tcbListHead      := tskSt1.(tcbListHead);
                prioTbl          := tskSt1.(prioTbl);
                taskRegNextID := tskSt1.(taskRegNextID);
                parkedTaskStacks := tskSt1.(parkedTaskStacks);
                taskLifecycle := tskSt1.(taskLifecycle);
     taskCount        := tskSt1.(taskCount); |} ->
    ready_after = (if is_effectively_ready t'.(stat) t'.(dly) then
                     insert_sorted_by
                       (fun tid => match tskSt1.(inUsedTaskStates) tid with
                                   | Some task => task.(curPrio)
                                   | None => sg.(osLowestPrio) + 1
                                   end)
                       cur_tid (remove_Z_eqb cur_tid schedSt1.(readyList))
                   else schedSt1.(readyList)) ->
    schedSt2 = {| readyList    := ready_after;
                  curTaskID    := schedSt1.(curTaskID);
                  curSchedPrio := schedSt1.(curSchedPrio);
                  highRdyTid   := match ready_after with head :: _ => Some head | [] => None end;
                  highRdyPrio  := match ready_after with
                                  | head :: _ =>
                                      match tskSt1.(inUsedTaskStates) head with
                                      | Some headT => Some headT.(curPrio)
                                      | None => None
                                      end
                                  | [] => None
                                  end;
                  ctxSwCtr     := schedSt1.(ctxSwCtr);
                  isRunning    := schedSt1.(isRunning);
               |} ->
    ~ In cur_tid schedSt1.(readyList) ->
    task_priority_unique tskSt1 ->
    verification_slice_sched_in_range sg tskSt1 schedSt1 ->
    verification_slice_sched_in_range sg tskSt2 schedSt2.
Proof.
  intros sg tskSt1 tskSt2 schedSt1 schedSt2 cur_tid t t' ready_after
    Hget Hcp' HtskSt2 Hready_after HschedSt2 Hnin Hpu
    [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].
  destruct (is_effectively_ready t'.(stat) t'.(dly)) eqn:Hready.
  - (* t' ready: ready_after = insert_sorted_by ... *)
    cbv beta iota in Hready_after. subst ready_after.
    subst tskSt2. subst schedSt2.
    split.
    + (* conjunct 1: In readyList -> exists task, ready *)
      intros tid_in Hin.
      simpl in Hin.
      rewrite insert_sorted_by_in in Hin.
      destruct Hin as [Heq | Hin].
      * subst tid_in. simpl. rewrite Z.eqb_refl.
        exists t'. split. reflexivity. exact Hready.
      * apply remove_Z_eqb_in in Hin.
        destruct (H1 tid_in Hin) as [t0 [Hget0 Hready0]].
        destruct (Z.eqb tid_in cur_tid) eqn:Heq_tin.
        -- apply Z.eqb_eq in Heq_tin. subst tid_in.
           exfalso. apply Hnin. exact Hin.
        -- exists t0. split. simpl. rewrite Heq_tin. exact Hget0. exact Hready0.
    + split.
      * (* conjunct 2: strictly_sorted_by *)
        apply strictly_sorted_by_key_ext with
          (key := fun tid => match tskSt1.(inUsedTaskStates) tid with
                             | Some task => task.(curPrio)
                             | None => sg.(osLowestPrio) + 1
                             end).
        -- intros x. destruct (Z.eqb x cur_tid) eqn:Heq_x.
           +++ apply Z.eqb_eq in Heq_x. subst x.
               simpl. rewrite Hget. rewrite Z.eqb_refl. simpl. rewrite Hcp'. reflexivity.
           +++ simpl. rewrite Heq_x. simpl. reflexivity.
        -- apply insert_sorted_by_preserves.
           ++ apply remove_Z_eqb_strictly_sorted_by. exact H2.
           ++ intros x Hin.
              apply remove_Z_eqb_in in Hin.
              destruct (H1 x Hin) as [t0 [Hget0 _]].
              intro Hkey_eq.
              simpl in Hkey_eq.
              rewrite Hget0 in Hkey_eq. rewrite Hget in Hkey_eq.
              simpl in Hkey_eq.
              apply (Hpu x cur_tid t0 t Hget0 Hget) in Hkey_eq. subst x.
              exfalso. apply Hnin. exact Hin.
      * split.
        -- (* conjunct 3: ready -> In readyList *)
           intros tid_in t0 Hget0 Hready0.
           destruct (Z.eqb tid_in cur_tid) eqn:Heq_tin.
           ++ apply Z.eqb_eq in Heq_tin. subst tid_in.
              simpl in Hget0. rewrite Z.eqb_refl in Hget0. inversion Hget0. subst t0.
              simpl. rewrite insert_sorted_by_in. left. reflexivity.
           ++ simpl in Hget0. rewrite Heq_tin in Hget0.
              simpl. rewrite insert_sorted_by_in. right.
              apply remove_Z_eqb_in_neq.
              ** intro Hneq. subst tid_in. rewrite Z.eqb_refl in Heq_tin. discriminate.
              ** apply (H3 tid_in t0 Hget0 Hready0).
        -- split.
           ++ (* conjunct 4: NoDup *)
              simpl. apply insert_sorted_by_preserves_NoDup.
              ** apply remove_Z_eqb_NoDup. exact H4.
              ** apply remove_Z_eqb_notin.
           ++ split.
              ** (* conjunct 5: 0 <= ctxSwCtr *)
                 simpl. exact H5.
              ** split.
                 --- (* conjunct 6: sched_high_ready_consistency *)
                     cbv beta iota.
                     destruct (insert_sorted_by
                                 (fun tid : TaskID =>
                                    match tskSt1.(inUsedTaskStates) tid with
                                    | Some task => task.(curPrio)
                                    | None => sg.(osLowestPrio) + 1
                                    end)
                                 cur_tid (remove_Z_eqb cur_tid schedSt1.(readyList)))
                       as [|hd tl] eqn:Hrl.
                     +++ (* empty: impossible since cur_tid is inserted *)
                         exfalso.
                         assert (Hin_cur : In cur_tid
                           (insert_sorted_by
                              (fun tid : TaskID =>
                                 match tskSt1.(inUsedTaskStates) tid with
                                 | Some task => task.(curPrio)
                                 | None => sg.(osLowestPrio) + 1
                                 end)
                              cur_tid (remove_Z_eqb cur_tid schedSt1.(readyList)))).
                         { apply insert_sorted_by_in. left. reflexivity. }
                         rewrite Hrl in Hin_cur. simpl in Hin_cur. inversion Hin_cur.
                     +++ (* hd :: tl *)
                         split.
                         { reflexivity. }
                         destruct (Z.eqb hd cur_tid) eqn:Heq_hd.
                         { apply Z.eqb_eq in Heq_hd. subst hd.
                           exists t'. split.
                           { simpl. rewrite Z.eqb_refl. reflexivity. }
                           { simpl. rewrite Hget. rewrite Hcp'. reflexivity. } }
                         assert (Hin_insert : In hd (insert_sorted_by
                              (fun tid : TaskID =>
                                 match tskSt1.(inUsedTaskStates) tid with
                                 | Some task => task.(curPrio)
                                 | None => sg.(osLowestPrio) + 1
                                 end)
                              cur_tid (remove_Z_eqb cur_tid schedSt1.(readyList)))).
                         { rewrite Hrl. simpl. left. reflexivity. }
                         apply insert_sorted_by_in in Hin_insert.
                         simpl in Hin_insert.
                         destruct Hin_insert as [Heq_hd' | Hin_hd].
                         { subst hd. rewrite Z.eqb_refl in Heq_hd. discriminate. }
                         apply remove_Z_eqb_in in Hin_hd.
                         destruct (H1 hd Hin_hd) as [t0 [Hget0 _]].
                         exists t0. split.
                         { simpl. rewrite Heq_hd. exact Hget0. }
                         { simpl. rewrite Hget0. reflexivity. }
                 --- (* conjunct 7: sched_current_consistency *)
                     cbv beta iota.
                     unfold sched_current_consistency in *.
                     remember (schedSt1.(curTaskID)) as cid in *.
                     destruct cid as [ctid|].
                     +++ destruct H7 as [t0 [Hget0 Hcsp]].
                         destruct (Z.eqb ctid cur_tid) eqn:Heq_ctid.
                         { apply Z.eqb_eq in Heq_ctid. subst ctid.
                           rewrite Hget in Hget0. injection Hget0 as Heq_t0t. subst t0.
                           exists t'. split.
                           { simpl. rewrite Z.eqb_refl. reflexivity. }
                           { cbv beta iota. rewrite Hcp'. exact Hcsp. } }
                         { exists t0. split.
                           { simpl. rewrite Heq_ctid. exact Hget0. }
                           { exact Hcsp. } }
                     +++ exact H7.
  - (* t' not ready: ready_after = schedSt1.readyList *)
    cbv beta iota in Hready_after. subst ready_after.
    subst tskSt2. subst schedSt2.
    split.
    + (* conjunct 1: In readyList -> ready *)
      intros tid_in Hin.
      simpl in Hin.
      destruct (H1 tid_in Hin) as [t0 [Hget0 Hready0]].
      destruct (Z.eqb tid_in cur_tid) eqn:Heq_tin.
      * apply Z.eqb_eq in Heq_tin. subst tid_in.
        exfalso. apply Hnin. exact Hin.
      * exists t0. split. simpl. rewrite Heq_tin. exact Hget0. exact Hready0.
    + split.
      * (* conjunct 2: strictly_sorted_by, key change *)
        apply strictly_sorted_by_key_ext with
          (key := fun tid => match tskSt1.(inUsedTaskStates) tid with
                             | Some task => task.(curPrio)
                             | None => sg.(osLowestPrio) + 1
                             end).
        -- intros x. destruct (Z.eqb x cur_tid) eqn:Heq_x.
           +++ apply Z.eqb_eq in Heq_x. subst x.
               simpl. rewrite Hget. rewrite Z.eqb_refl. simpl. rewrite Hcp'. reflexivity.
           +++ simpl. rewrite Heq_x. simpl. reflexivity.
        -- exact H2.
      * split.
        -- (* conjunct 3: ready -> In readyList *)
           intros tid_in t0 Hget0 Hready0.
           destruct (Z.eqb tid_in cur_tid) eqn:Heq_tin.
           ++ (* tid_in = cur_tid, but t' is not ready, contradicts Hready0 *)
              apply Z.eqb_eq in Heq_tin. subst tid_in.
              simpl in Hget0. rewrite Z.eqb_refl in Hget0. simpl in Hget0.
              inversion Hget0. subst t0.
              exfalso. rewrite Hready in Hready0. discriminate.
           ++ simpl in Hget0. rewrite Heq_tin in Hget0.
              exact (H3 tid_in t0 Hget0 Hready0).
        -- split.
           ++ (* conjunct 4: NoDup *)
              simpl. exact H4.
           ++ split.
              ** (* conjunct 5: 0 <= ctxSwCtr *)
                 simpl. exact H5.
              ** split.
                 --- (* conjunct 6: sched_high_ready_consistency *)
                     cbv beta iota.
                     destruct schedSt1.(readyList) as [|hd tl] eqn:Hrl.
                     +++ split; reflexivity.
                     +++ split.
                        { reflexivity. }
                        destruct (Z.eqb hd cur_tid) eqn:Heq_hd.
                        { apply Z.eqb_eq in Heq_hd. subst hd.
                          exfalso. apply Hnin. simpl. left. reflexivity. }
                        destruct (H1 hd (or_introl eq_refl)) as [t0 [Hget0 _]].
                        exists t0. split.
                        { simpl. rewrite Heq_hd. exact Hget0. }
                        { simpl. rewrite Hget0. reflexivity. }
                 --- (* conjunct 7: sched_current_consistency *)
                     cbv beta iota.
                     unfold sched_current_consistency in *.
                     destruct schedSt1.(curTaskID) as [ctid|] eqn:Hcid.
                     +++ destruct H7 as [t0 [Hget0 Hcsp]].
                         destruct (Z.eqb ctid cur_tid) eqn:Heq_ctid.
                         { apply Z.eqb_eq in Heq_ctid. subst ctid.
                           rewrite Hget in Hget0. injection Hget0 as Heq. subst t0.
                           exists t'. split.
                           { simpl. rewrite Z.eqb_refl. reflexivity. }
                           { cbv beta iota. rewrite Hcp'. exact Hcsp. } }
                         { exists t0. split.
                           { simpl. rewrite Heq_ctid. exact Hget0. }
                           { exact Hcsp. } }
                     +++ exact H7.
Qed.

(** Ready insertion is idempotent at the bitmap level: a timeout-linked
    waiter can already be ready. A wake which remains suspended leaves the
    ready list untouched. Neither branch refreshes physical scheduler caches. *)
Definition sched_wake_task (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (s : SchedAbstractState) (tid : TaskID) (new : TaskAbstractState) : SchedAbstractState :=
  sched_set_ready s
    (if is_effectively_ready new.(stat) new.(dly)
     then insert_sorted_by (sched_task_key sg tasks) tid
            (remove_Z_eqb tid s.(readyList))
     else s.(readyList)).

Lemma sched_wake_task_preserves_in_range : forall sg tasks s tid old new,
  task_in_range sg tasks -> sched_in_range sg tasks s ->
  tasks.(inUsedTaskStates) tid = Some old -> new.(curPrio) = old.(curPrio) ->
  (is_effectively_ready old.(stat) old.(dly) = true ->
     is_effectively_ready new.(stat) new.(dly) = true) ->
  sched_in_range sg (glob_task_set_usedtask tasks tid new)
    (sched_wake_task sg tasks s tid new).
Proof.
  intros sg tasks s tid old new Htask
    [[Hmembers [Hsorted [Hcomplete Hnodup]]] [Hcache [Hcounter Hcurrent]]] Hold Hprio Hmonotone.
  destruct Htask as [_ [_ [_ [_ [_ [_ [Hunique [Hprios _]]]]]]]].
  assert (Hkey : forall slot, sched_task_key sg tasks slot =
    sched_task_key sg (glob_task_set_usedtask tasks tid new) slot).
  { intro slot; unfold sched_task_key; simpl.
    destruct (Z.eqb slot tid) eqn:E; [|reflexivity].
    apply Z.eqb_eq in E; subst slot; rewrite Hold; symmetry; exact Hprio. }
  unfold sched_in_range; split; [|split; [exact Hcache|split; assumption]].
  unfold sched_ready_in_range, sched_wake_task; simpl.
  destruct (is_effectively_ready new.(stat) new.(dly)) eqn:Hready.
  - split.
    + intros slot Hin; apply insert_sorted_by_in in Hin; simpl in Hin.
      destruct Hin as [Heq|Hin].
      * subst slot; exists new; rewrite Z.eqb_refl; split; [reflexivity|].
        split; [rewrite Hprio; eapply Hprios; exact Hold|exact Hready].
      * assert (Hneq : slot <> tid).
        { intro E; subst slot; exact (remove_Z_eqb_notin tid s.(readyList) Hin). }
        apply Z.eqb_neq in Hneq; rewrite Hneq.
        apply Hmembers; eapply remove_Z_eqb_in; exact Hin.
    + split.
      * eapply strictly_sorted_by_key_ext; [exact Hkey|].
        apply insert_sorted_by_preserves.
        -- apply remove_Z_eqb_strictly_sorted_by; exact Hsorted.
        -- intros slot Hin Heq; pose proof (remove_Z_eqb_in _ _ _ Hin) as HinOld.
           destruct (Hmembers slot HinOld) as [t [Ht _]].
           unfold sched_task_key in Heq; rewrite Ht, Hold in Heq.
           pose proof (Hunique _ _ _ _ Ht Hold Heq) as Hid; subst slot.
           exact (remove_Z_eqb_notin tid s.(readyList) Hin).
      * split.
        -- intros slot t Ht Htready; apply insert_sorted_by_in; simpl.
           destruct (Z.eqb slot tid) eqn:E.
           ++ apply Z.eqb_eq in E; left; symmetry; exact E.
           ++ right; apply Z.eqb_neq in E.
              apply remove_Z_eqb_in_neq; [exact E|]. eapply Hcomplete; eauto.
        -- apply insert_sorted_by_preserves_NoDup;
             [apply remove_Z_eqb_NoDup; exact Hnodup|apply remove_Z_eqb_notin].
  - split.
    + intros slot Hin; destruct (Hmembers slot Hin) as [t [Ht [Hp Hr]]].
      destruct (Z.eqb slot tid) eqn:E.
      * apply Z.eqb_eq in E; subst slot; rewrite Hold in Ht; injection Ht as Heq; subst t.
        specialize (Hmonotone Hr); congruence.
      * exists t; auto.
    + split.
      * eapply strictly_sorted_by_key_ext; [exact Hkey|exact Hsorted].
      * split; [|exact Hnodup]. intros slot t Ht Hr.
        destruct (Z.eqb slot tid) eqn:E.
        -- injection Ht as Heq; subst t; congruence.
        -- eapply Hcomplete; eauto.
Qed.

Lemma sched_flag_wake_preserves_in_range : forall sg tasks s tid old bits result,
  task_in_range sg tasks -> sched_in_range sg tasks s ->
  tasks.(inUsedTaskStates) tid = Some old ->
  sched_in_range sg (glob_task_set_usedtask tasks tid (task_flag_wake old bits result))
    (sched_wake_task sg tasks s tid (task_flag_wake old bits result)).
Proof.
  intros sg tasks s tid old bits result Htasks Hsched Hold.
  eapply sched_wake_task_preserves_in_range;
    [exact Htasks|exact Hsched|exact Hold|reflexivity|].
  apply task_flag_wake_keeps_ready_task_ready.
Qed.

Lemma encode_ready_grp_fold_lor : forall tasks ids,
  encode_ready_grp ids tasks =
  fold_right (fun tid acc => Z.lor
    (match tasks.(inUsedTaskStates) tid with
     | Some t => Z.shiftl 1 (t.(curPrio) / 8) | None => 0 end) acc) 0 ids.
Proof.
  intros tasks ids; induction ids as [|tid rest IH]; [reflexivity|].
  simpl; destruct (tasks.(inUsedTaskStates) tid); rewrite IH; [reflexivity|].
  rewrite Z.lor_0_l; reflexivity.
Qed.

Lemma encode_ready_tbl_fold_lor : forall tasks ids y,
  encode_ready_tbl_at_or ids tasks y =
  fold_right (fun tid acc => Z.lor
    (match tasks.(inUsedTaskStates) tid with
     | Some t => if Z.eqb (t.(curPrio) / 8) y then Z.shiftl 1 (t.(curPrio) mod 8) else 0
     | None => 0 end) acc) 0 ids.
Proof.
  intros tasks ids y; induction ids as [|tid rest IH]; [reflexivity|].
  unfold encode_ready_tbl_at_or in *; simpl.
  destruct (tasks.(inUsedTaskStates) tid) as [t|]; [destruct (Z.eqb (t.(curPrio) / 8) y)|];
    rewrite IH; try reflexivity; rewrite Z.lor_0_l; reflexivity.
Qed.

Lemma encode_ready_grp_insert_remove : forall tasks key tid ids t,
  tasks.(inUsedTaskStates) tid = Some t ->
  encode_ready_grp (insert_sorted_by key tid (remove_Z_eqb tid ids)) tasks =
  Z.lor (encode_ready_grp ids tasks) (Z.shiftl 1 (t.(curPrio) / 8)).
Proof.
  intros tasks key tid ids t Ht; rewrite !encode_ready_grp_fold_lor.
  rewrite fold_right_lor_insert_sorted_remove, Ht; apply Z.lor_comm.
Qed.

Lemma encode_ready_tbl_insert_remove : forall tasks key tid ids t y,
  tasks.(inUsedTaskStates) tid = Some t ->
  encode_ready_tbl_at_or (insert_sorted_by key tid (remove_Z_eqb tid ids)) tasks y =
  if Z.eqb (t.(curPrio) / 8) y
  then Z.lor (encode_ready_tbl_at_or ids tasks y) (Z.shiftl 1 (t.(curPrio) mod 8))
  else encode_ready_tbl_at_or ids tasks y.
Proof.
  intros tasks key tid ids t y Ht; rewrite !encode_ready_tbl_fold_lor.
  rewrite fold_right_lor_insert_sorted_remove, Ht.
  destruct (Z.eqb (t.(curPrio) / 8) y); [apply Z.lor_comm|apply Z.lor_0_l].
Qed.

Lemma sched_encoding_priority_ext : forall ids before after,
  (forall tid, In tid ids -> option_map curPrio (before.(inUsedTaskStates) tid) =
    option_map curPrio (after.(inUsedTaskStates) tid)) ->
  encode_ready_grp ids before = encode_ready_grp ids after /\
  forall y, encode_ready_tbl_at_or ids before y = encode_ready_tbl_at_or ids after y.
Proof.
  induction ids as [|tid rest IH]; intros before after Heq.
  - split; reflexivity.
  - destruct (IH before after (fun q Hin => Heq q (or_intror Hin))) as [Hgrp Htbl].
    pose proof (Heq tid (or_introl eq_refl)) as Hhead.
    cbn [encode_ready_grp encode_ready_tbl_at_or fold_right].
    destruct (before.(inUsedTaskStates) tid) as [old|];
      destruct (after.(inUsedTaskStates) tid) as [new|]; simpl in Hhead; try discriminate.
    + injection Hhead as Hprio; rewrite Hprio, Hgrp; split; [reflexivity|].
      intro y; fold (encode_ready_tbl_at_or rest before y).
      fold (encode_ready_tbl_at_or rest after y); rewrite Htbl; reflexivity.
    + split; [exact Hgrp|exact Htbl].
Qed.

(** Field/state changes that preserve the priorities of ready members do
    not change any ready-bitmap cell or scheduler cache. *)
Lemma sched_raw_rep_priority_ext : forall sg before after s,
  (forall tid, In tid s.(readyList) ->
    option_map curPrio (before.(inUsedTaskStates) tid) =
    option_map curPrio (after.(inUsedTaskStates) tid)) ->
  sched_raw_rep sg before s = sched_raw_rep sg after s.
Proof.
  intros sg before after s Hprio.
  destruct (sched_encoding_priority_ext s.(readyList) before after Hprio) as [Hgrp Htbl].
  unfold sched_raw_rep; rewrite Hgrp; cbn [sched_rows_rep].
  rewrite !Htbl; reflexivity.
Qed.

(** Exact OR writes, including repeated wake after timeout; no NoDup,
    freshness or not-already-ready premise is needed for the bit equation. *)
Lemma sched_wake_ready_encoding : forall sg tasks s tid old new,
  tasks.(inUsedTaskStates) tid = Some old -> new.(curPrio) = old.(curPrio) ->
  is_effectively_ready new.(stat) new.(dly) = true ->
  let post_tasks := glob_task_set_usedtask tasks tid new in
  let ready := (sched_wake_task sg tasks s tid new).(readyList) in
  encode_ready_grp ready post_tasks =
    Z.lor (encode_ready_grp s.(readyList) tasks) (Z.shiftl 1 (old.(curPrio) / 8)) /\
  forall y, encode_ready_tbl_at_or ready post_tasks y =
    if Z.eqb (old.(curPrio) / 8) y
    then Z.lor (encode_ready_tbl_at_or s.(readyList) tasks y) (Z.shiftl 1 (old.(curPrio) mod 8))
    else encode_ready_tbl_at_or s.(readyList) tasks y.
Proof.
  intros sg tasks s tid old new Hold Hp Hr; cbn zeta.
  unfold sched_wake_task; simpl; rewrite Hr.
  assert (Hobs : forall slot, option_map curPrio
    ((glob_task_set_usedtask tasks tid new).(inUsedTaskStates) slot) =
    option_map curPrio (tasks.(inUsedTaskStates) slot)).
  { intro slot; eapply glob_task_set_usedtask_observation; eauto. }
  destruct (sched_encoding_priority_ext
    (insert_sorted_by (sched_task_key sg tasks) tid (remove_Z_eqb tid s.(readyList)))
    (glob_task_set_usedtask tasks tid new) tasks (fun slot _ => Hobs slot)) as [Hgrp Htbl].
  rewrite Hgrp; split; [eapply encode_ready_grp_insert_remove; exact Hold|].
  intro y; rewrite Htbl; eapply encode_ready_tbl_insert_remove; exact Hold.
Qed.

Lemma sched_wake_not_ready_encoding : forall sg tasks s tid old new,
  tasks.(inUsedTaskStates) tid = Some old -> new.(curPrio) = old.(curPrio) ->
  is_effectively_ready new.(stat) new.(dly) = false ->
  let post_tasks := glob_task_set_usedtask tasks tid new in
  let ready := (sched_wake_task sg tasks s tid new).(readyList) in
  encode_ready_grp ready post_tasks = encode_ready_grp s.(readyList) tasks /\
  forall y, encode_ready_tbl_at_or ready post_tasks y = encode_ready_tbl_at_or s.(readyList) tasks y.
Proof.
  intros sg tasks s tid old new Hold Hp Hr; cbn zeta.
  unfold sched_wake_task; simpl; rewrite Hr.
  apply sched_encoding_priority_ext.
  intros slot Hin; eapply glob_task_set_usedtask_observation; eauto.
Qed.

Lemma sched_wake_row_values : forall sg tasks s tid old new,
  tasks.(inUsedTaskStates) tid = Some old -> new.(curPrio) = old.(curPrio) ->
  is_effectively_ready new.(stat) new.(dly) = true -> 0 <= old.(curPrio) / 8 < 8 ->
  sched_row_values (glob_task_set_usedtask tasks tid new)
    (sched_wake_task sg tasks s tid new).(readyList) =
  replace_Znth (old.(curPrio) / 8)
    (Z.lor (encode_ready_tbl_at_or s.(readyList) tasks (old.(curPrio) / 8))
      (Z.shiftl 1 (old.(curPrio) mod 8)))
    (sched_row_values tasks s.(readyList)).
Proof.
  intros sg tasks s tid old new Hold Hp Hr Hy.
  destruct (sched_wake_ready_encoding sg tasks s tid old new Hold Hp Hr) as [_ Htbl].
  unfold sched_row_values; cbn [map].
  rewrite (Htbl 0), (Htbl 1), (Htbl 2), (Htbl 3), (Htbl 4), (Htbl 5), (Htbl 6), (Htbl 7).
  set (y := old.(curPrio) / 8) in *.
  assert (Hcases : y = 0 \/ y = 1 \/ y = 2 \/ y = 3 \/ y = 4 \/ y = 5 \/ y = 6 \/ y = 7) by lia.
  destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; reflexivity.
Qed.

Lemma sched_rows_merge_wake : forall sg tasks s tid old new,
  tasks.(inUsedTaskStates) tid = Some old -> new.(curPrio) = old.(curPrio) ->
  is_effectively_ready new.(stat) new.(dly) = true -> 0 <= old.(curPrio) / 8 < 8 ->
  (sg.(g_OSRdyTbl) + (old.(curPrio) / 8) * sizeof(UCHAR)) # UChar |->
    Z.lor (encode_ready_tbl_at_or s.(readyList) tasks (old.(curPrio) / 8))
      (Z.shiftl 1 (old.(curPrio) mod 8)) **
  UCharArray.missing_i sg.(g_OSRdyTbl) (old.(curPrio) / 8) 0 8
    (sched_row_values tasks s.(readyList)) |--
  sched_rows_rep sg (glob_task_set_usedtask tasks tid new)
    (sched_wake_task sg tasks s tid new).(readyList) [0;1;2;3;4;5;6;7].
Proof.
  intros sg tasks s tid old new Hold Hp Hr Hy.
  rewrite sched_rows_array_equiv.
  rewrite (sched_wake_row_values sg tasks s tid old new Hold Hp Hr Hy).
  apply sched_rows_merge_updated_array; exact Hy.
Qed.

Lemma sched_update_task_preserves_in_range : forall sg tasks s tid old new,
  sched_in_range sg tasks s -> tasks.(inUsedTaskStates) tid = Some old ->
  new.(curPrio) = old.(curPrio) ->
  is_effectively_ready new.(stat) new.(dly) = is_effectively_ready old.(stat) old.(dly) ->
  sched_in_range sg (glob_task_set_usedtask tasks tid new) s.
Proof.
  intros sg tasks s tid old new
    [[Hmembers [Hsorted [Hcomplete Hnd]]] [Hhigh [Hctr Hcurrent]]] Hold Hp Hr.
  split; [|split; [exact Hhigh|split; assumption]].
  split.
  - intros slot Hin; destruct (Hmembers slot Hin) as [t [Ht [Hprio Hready]]].
    simpl; destruct (Z.eqb slot tid) eqn:E.
    + apply Z.eqb_eq in E; subst slot; rewrite Hold in Ht; injection Ht as Heq; subst t.
      exists new; split; [reflexivity|]; rewrite Hp, Hr; auto.
    + exists t; auto.
  - split.
    + eapply strictly_sorted_by_key_ext; [|exact Hsorted].
      intro slot; simpl; destruct (Z.eqb slot tid) eqn:E; [|reflexivity].
      apply Z.eqb_eq in E; subst slot; rewrite Hold; symmetry; exact Hp.
    + split; [|exact Hnd]. intros slot t Ht Hready; simpl in Ht.
      destruct (Z.eqb slot tid) eqn:E.
      * apply Z.eqb_eq in E; subst slot; injection Ht as Heq; subst t.
        eapply Hcomplete; [exact Hold|rewrite <- Hr; exact Hready].
      * eapply Hcomplete; eauto.
Qed.

(** Shared narrow-bitmap removal equations, using OR encoding and QCP's
    unsigned-cast lemmas.  The caller supplies the live priority relation. *)
Lemma bitmap_single_bit_in_range : forall width index,
  0 <= index < width -> 0 <= Z.shiftl 1 index < 2 ^ width.
Proof.
  intros width index Hindex; rewrite Z.shiftl_1_l; split.
  - apply Z.pow_nonneg; lia.
  - apply Z.pow_lt_mono_r; lia.
Qed.

Lemma bitmap_lor_in_range : forall width a b,
  0 < width -> 0 <= a < 2 ^ width -> 0 <= b < 2 ^ width ->
  0 <= Z.lor a b < 2 ^ width.
Proof.
  intros width a b Hw Ha Hb.
  pose proof (unsigned_Lastnbits_range (Z.lor a b) width ltac:(lia)) as Hrange.
  rewrite unsigned_last_nbits_lor_distr_missing in Hrange by lia; exact Hrange.
Qed.

Lemma bitmap_clear_disjoint_mask : forall width mask rest,
  0 <= width -> 0 <= Z.lor mask rest < 2 ^ width -> Z.land mask rest = 0 ->
  Z.land (Z.lor mask rest) (unsigned_last_nbits (Z.lnot mask) width) = rest.
Proof.
  intros width mask rest Hw Hrange Hdisjoint.
  rewrite <- (unsigned_last_nbits_eq (Z.lor mask rest) width Hrange) at 1.
  rewrite unsigned_last_nbits_land_clear_r by exact Hw.
  rewrite unsigned_last_nbits_eq by exact Hrange; rewrite <- Z.ldiff_land.
  apply Z.bits_inj'; intros n Hn; rewrite Z.ldiff_spec, Z.lor_spec.
  pose proof (f_equal (fun z => Z.testbit z n) Hdisjoint) as Hbit.
  change (Z.testbit (Z.land mask rest) n = Z.testbit 0 n) in Hbit.
  rewrite Z.land_spec, Z.testbit_0_l in Hbit.
  destruct (Z.testbit mask n), (Z.testbit rest n); simpl in *; congruence.
Qed.

Lemma encode_ready_tbl_or_in_range : forall ids tasks row,
  0 <= encode_ready_tbl_at_or ids tasks row < 2 ^ 8.
Proof.
  induction ids as [|tid rest IH]; intros tasks row; simpl; [lia|].
  unfold encode_ready_tbl_at_or in *; simpl.
  destruct (tasks.(inUsedTaskStates) tid) as [t|]; [|apply IH].
  destruct (Z.eqb (t.(curPrio) / 8) row); [|apply IH].
  apply (bitmap_lor_in_range 8); [lia| |apply IH].
  apply (bitmap_single_bit_in_range 8); apply Z.mod_pos_bound; lia.
Qed.

Lemma encode_ready_grp_in_range : forall ids tasks,
  (forall tid t, In tid ids -> tasks.(inUsedTaskStates) tid = Some t ->
    0 <= t.(curPrio) / 8 < 8) ->
  0 <= encode_ready_grp ids tasks < 2 ^ 8.
Proof.
  induction ids as [|tid rest IH]; intros tasks Hrange; simpl; [lia|].
  destruct (tasks.(inUsedTaskStates) tid) as [t|] eqn:Ht.
  - apply (bitmap_lor_in_range 8); [lia| |].
    + apply (bitmap_single_bit_in_range 8); eapply Hrange; [left; reflexivity|exact Ht].
    + apply IH; intros; eapply Hrange; [right; eassumption|eassumption].
  - apply IH; intros; eapply Hrange; [right; eassumption|eassumption].
Qed.

Lemma encode_ready_grp_permutation : forall before after tasks,
  Permutation before after -> encode_ready_grp before tasks = encode_ready_grp after tasks.
Proof.
  intros; rewrite !encode_ready_grp_fold_lor; apply fold_right_lor_permutation; assumption.
Qed.

Lemma encode_ready_tbl_or_permutation : forall before after tasks row,
  Permutation before after ->
  encode_ready_tbl_at_or before tasks row = encode_ready_tbl_at_or after tasks row.
Proof.
  intros; rewrite !encode_ready_tbl_fold_lor; apply fold_right_lor_permutation; assumption.
Qed.

Lemma encode_ready_tbl_or_remove_selected_row : forall ids tasks tid t,
  In tid ids -> NoDup ids -> tasks.(inUsedTaskStates) tid = Some t ->
  task_priority_unique tasks ->
  (forall slot node, In slot ids -> tasks.(inUsedTaskStates) slot = Some node -> 0 <= node.(curPrio)) ->
  encode_ready_tbl_at_or (remove_Z_eqb tid ids) tasks (t.(curPrio) / 8) =
    Z.land (encode_ready_tbl_at_or ids tasks (t.(curPrio) / 8))
      (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (t.(curPrio) mod 8))) 8).
Proof.
  intros ids tasks tid t Hin Hnd Ht Hunique Hrange.
  assert (Hdisjoint : Z.land (Z.shiftl 1 (t.(curPrio) mod 8))
    (encode_ready_tbl_at_or (remove_Z_eqb tid ids) tasks (t.(curPrio) / 8)) = 0).
  { apply sched_bit_disjoint_tbl_or.
    - eapply Hrange; eauto.
    - reflexivity.
    - intros; eapply Hrange; [eapply remove_Z_eqb_in; eassumption|eassumption].
    - intros slot node Hmember Hnode Hsame.
      assert (slot = tid) by (eapply Hunique; eauto); subst slot.
      exact (remove_Z_eqb_notin tid ids Hmember). }
  pose proof (encode_ready_tbl_or_permutation _ _ tasks (t.(curPrio) / 8)
    (remove_Z_eqb_perm_cons tid ids Hin Hnd)) as Hdecompose.
  change (encode_ready_tbl_at_or ids tasks (t.(curPrio) / 8) =
    match tasks.(inUsedTaskStates) tid with
    | Some node => if Z.eqb (node.(curPrio) / 8) (t.(curPrio) / 8)
        then Z.lor (Z.shiftl 1 (node.(curPrio) mod 8))
          (encode_ready_tbl_at_or (remove_Z_eqb tid ids) tasks (t.(curPrio) / 8))
        else encode_ready_tbl_at_or (remove_Z_eqb tid ids) tasks (t.(curPrio) / 8)
    | None => encode_ready_tbl_at_or (remove_Z_eqb tid ids) tasks (t.(curPrio) / 8)
    end) in Hdecompose.
  rewrite Ht, Z.eqb_refl in Hdecompose; rewrite Hdecompose; symmetry.
  apply (bitmap_clear_disjoint_mask 8); [lia| |exact Hdisjoint].
  rewrite <- Hdecompose; apply encode_ready_tbl_or_in_range.
Qed.

Lemma encode_ready_tbl_or_remove_other_row : forall ids tasks tid t row,
  tasks.(inUsedTaskStates) tid = Some t -> t.(curPrio) / 8 <> row ->
  encode_ready_tbl_at_or (remove_Z_eqb tid ids) tasks row = encode_ready_tbl_at_or ids tasks row.
Proof.
  induction ids as [|head rest IH]; intros tasks tid t row Ht Hrow; [reflexivity|].
  simpl; destruct (Z.eqb head tid) eqn:E.
  - apply Z.eqb_eq in E; subst head.
    unfold encode_ready_tbl_at_or; simpl; rewrite Ht.
    destruct (Z.eqb (t.(curPrio) / 8) row) eqn:Ey; [apply Z.eqb_eq in Ey; contradiction|].
    eapply IH; eauto.
  - change ((match tasks.(inUsedTaskStates) head with
      | Some node => if Z.eqb (node.(curPrio) / 8) row
          then Z.lor (Z.shiftl 1 (node.(curPrio) mod 8))
            (encode_ready_tbl_at_or (remove_Z_eqb tid rest) tasks row)
          else encode_ready_tbl_at_or (remove_Z_eqb tid rest) tasks row
      | None => encode_ready_tbl_at_or (remove_Z_eqb tid rest) tasks row end) =
      encode_ready_tbl_at_or (head :: rest) tasks row).
    rewrite IH with (t := t) by assumption; reflexivity.
Qed.

Lemma encode_ready_tbl_or_nonzero_has_row : forall ids tasks row,
  encode_ready_tbl_at_or ids tasks row <> 0 ->
  exists tid t, In tid ids /\ tasks.(inUsedTaskStates) tid = Some t /\ t.(curPrio) / 8 = row.
Proof.
  induction ids as [|tid rest IH]; intros tasks row Hnonzero; [contradiction|].
  change ((match tasks.(inUsedTaskStates) tid with
    | Some t => if Z.eqb (t.(curPrio) / 8) row
        then Z.lor (Z.shiftl 1 (t.(curPrio) mod 8)) (encode_ready_tbl_at_or rest tasks row)
        else encode_ready_tbl_at_or rest tasks row
    | None => encode_ready_tbl_at_or rest tasks row end) <> 0) in Hnonzero.
  destruct (tasks.(inUsedTaskStates) tid) as [t|] eqn:Ht.
  - destruct (Z.eqb (t.(curPrio) / 8) row) eqn:E.
    + exists tid, t; split; [left; reflexivity|]; split; [exact Ht|apply Z.eqb_eq; exact E].
    + destruct (IH tasks row Hnonzero) as [other [node [Hin Hnode]]].
      exists other, node; split; [right; exact Hin|exact Hnode].
  - destruct (IH tasks row Hnonzero) as [other [node [Hin Hnode]]].
    exists other, node; split; [right; exact Hin|exact Hnode].
Qed.

Lemma encode_ready_grp_absorbs_present_row : forall ids tasks tid t,
  In tid ids -> tasks.(inUsedTaskStates) tid = Some t ->
  Z.lor (Z.shiftl 1 (t.(curPrio) / 8)) (encode_ready_grp ids tasks) = encode_ready_grp ids tasks.
Proof.
  induction ids as [|head rest IH]; intros tasks tid t Hin Ht; [contradiction|].
  simpl in Hin |- *; destruct Hin as [->|Hin].
  - rewrite Ht, Z.lor_assoc, Z.lor_diag; reflexivity.
  - destruct (tasks.(inUsedTaskStates) head) as [node|]; [|eapply IH; eauto].
    rewrite Z.lor_assoc, (Z.lor_comm (Z.shiftl 1 (t.(curPrio) / 8))), <- Z.lor_assoc.
    rewrite (IH tasks tid t Hin Ht); reflexivity.
Qed.

Lemma encode_ready_tbl_or_present_row_nonzero : forall ids tasks tid t,
  In tid ids -> tasks.(inUsedTaskStates) tid = Some t ->
  encode_ready_tbl_at_or ids tasks (t.(curPrio) / 8) <> 0.
Proof.
  induction ids as [|head rest IH]; intros tasks tid t Hin Ht; [contradiction|].
  simpl in Hin; unfold encode_ready_tbl_at_or; simpl; destruct Hin as [->|Hin].
  - rewrite Ht, Z.eqb_refl; intro Hzero.
    pose proof (f_equal (fun z => Z.testbit z (t.(curPrio) mod 8)) Hzero) as Hbit.
    cbn beta in Hbit.
    rewrite Z.lor_spec, Z.shiftl_1_l, Z.pow2_bits_eqb, Z.eqb_refl, Z.testbit_0_l in Hbit;
      [discriminate|apply Z.mod_pos_bound; lia].
  - destruct (tasks.(inUsedTaskStates) head) as [node|]; [|eapply IH; eauto].
    destruct (Z.eqb (node.(curPrio) / 8) (t.(curPrio) / 8)); [|eapply IH; eauto].
    intro Hzero; apply Z.lor_eq_0_iff in Hzero.
    eapply IH; [exact Hin|exact Ht|exact (proj2 Hzero)].
Qed.

Lemma encode_ready_grp_remove_waiter : forall ids tasks tid t,
  In tid ids -> NoDup ids -> tasks.(inUsedTaskStates) tid = Some t ->
  task_priority_unique tasks ->
  (forall slot node, In slot ids -> tasks.(inUsedTaskStates) slot = Some node -> 0 <= node.(curPrio)) ->
  (forall slot node, In slot ids -> tasks.(inUsedTaskStates) slot = Some node ->
    0 <= node.(curPrio) / 8 < 8) ->
  encode_ready_grp (remove_Z_eqb tid ids) tasks =
    let cleared := Z.land (encode_ready_tbl_at_or ids tasks (t.(curPrio) / 8))
      (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (t.(curPrio) mod 8))) 8) in
    if Z.eqb cleared 0
    then Z.land (encode_ready_grp ids tasks) (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (t.(curPrio) / 8))) 8)
    else encode_ready_grp ids tasks.
Proof.
  intros ids tasks tid t Hin Hnd Ht Hunique Hrange Hrows.
  rewrite <- (encode_ready_tbl_or_remove_selected_row ids tasks tid t Hin Hnd Ht Hunique Hrange).
  cbn zeta.
  pose proof (encode_ready_grp_permutation _ _ tasks (remove_Z_eqb_perm_cons tid ids Hin Hnd)) as Hdecompose.
  simpl in Hdecompose; rewrite Ht in Hdecompose.
  destruct (Z.eqb (encode_ready_tbl_at_or (remove_Z_eqb tid ids) tasks (t.(curPrio) / 8)) 0) eqn:E.
  - apply Z.eqb_eq in E; rewrite Hdecompose; symmetry.
    apply (bitmap_clear_disjoint_mask 8); [lia| |].
    + rewrite <- Hdecompose; apply encode_ready_grp_in_range; exact Hrows.
    + apply sched_no_group_row.
      * exact (proj1 (Hrows tid t Hin Ht)).
      * intros slot node Hmember Hnode.
        apply (proj1 (Hrows slot node (remove_Z_eqb_in tid slot ids Hmember) Hnode)).
      * intros slot node Hmember Hnode Hsame.
        pose proof (encode_ready_tbl_or_present_row_nonzero (remove_Z_eqb tid ids) tasks slot node Hmember Hnode) as Hnonzero.
        rewrite Hsame, E in Hnonzero; contradiction.
  - apply Z.eqb_neq in E.
    destruct (encode_ready_tbl_or_nonzero_has_row _ _ _ E) as [other [node [Hmember [Hnode Hrow]]]].
    rewrite Hdecompose, <- Hrow.
    symmetry; eapply encode_ready_grp_absorbs_present_row; eauto.
Qed.

(** This operation only removes ready membership.  Pend/delay/status
    stores belong to the caller; current/high caches stay at their real
    pre-schedule values.  It also permits an already non-ready task. *)
Definition sched_remove_ready_task (s : SchedAbstractState)
  (tid : TaskID) : SchedAbstractState :=
  sched_set_ready s (remove_Z_eqb tid s.(readyList)).

Lemma sched_remove_ready_task_preserves_in_range : forall sg tasks s tid old new,
  sched_in_range sg tasks s -> tasks.(inUsedTaskStates) tid = Some old ->
  new.(curPrio) = old.(curPrio) -> is_effectively_ready new.(stat) new.(dly) = false ->
  sched_in_range sg (glob_task_set_usedtask tasks tid new)
    (sched_remove_ready_task s tid).
Proof.
  intros sg tasks s tid old new
    [[Hmembers [Hsorted [Hcomplete Hnodup]]] [Hcache [Hcounter Hcurrent]]] Hold Hprio Hblocked.
  assert (Hkey : forall slot, sched_task_key sg tasks slot =
    sched_task_key sg (glob_task_set_usedtask tasks tid new) slot).
  { intro slot; unfold sched_task_key; simpl; destruct (Z.eqb slot tid) eqn:E; [|reflexivity].
    apply Z.eqb_eq in E; subst slot; rewrite Hold; symmetry; exact Hprio. }
  split; [|split; [exact Hcache|split; assumption]].
  split.
  - intros slot Hin.
    assert (Hne : slot <> tid) by (intro E; subst slot; exact (remove_Z_eqb_notin tid s.(readyList) Hin)).
    destruct (Hmembers slot (remove_Z_eqb_in tid slot s.(readyList) Hin)) as [t [Ht Hfacts]].
    exists t; split; [simpl; rewrite (proj2 (Z.eqb_neq slot tid) Hne); exact Ht|exact Hfacts].
  - split.
    + eapply strictly_sorted_by_key_ext; [exact Hkey|].
      apply remove_Z_eqb_strictly_sorted_by; exact Hsorted.
    + split.
      * intros slot t Ht Hready; simpl in Ht.
        destruct (Z.eqb slot tid) eqn:E.
        -- injection Ht as Ht; subst t; congruence.
        -- apply remove_Z_eqb_in_neq; [apply Z.eqb_neq; exact E|eapply Hcomplete; eauto].
      * apply remove_Z_eqb_NoDup; exact Hnodup.
Qed.

Lemma sched_remove_ready_physical_rep_eq : forall sg s tid,
  sched_physical_rep sg (sched_remove_ready_task s tid) = sched_physical_rep sg s.
Proof. reflexivity. Qed.

(** The caller saves the stable pre-pend observation.  The target TCB
    may already have changed status/delay at the actual bitmap stores;
    removing its ID means its new fields are not used by the encoding. *)
Lemma sched_remove_ready_member_encoding : forall sg tasks s tid old new,
  valid_stable_glob_vars sg -> task_in_range sg tasks -> sched_in_range sg tasks s ->
  tasks.(inUsedTaskStates) tid = Some old -> In tid s.(readyList) ->
  let post_tasks := glob_task_set_usedtask tasks tid new in
  let ready := (sched_remove_ready_task s tid).(readyList) in
  encode_ready_grp ready post_tasks =
    (let cleared := Z.land (encode_ready_tbl_at_or s.(readyList) tasks (old.(curPrio) / 8))
       (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (old.(curPrio) mod 8))) 8) in
     if Z.eqb cleared 0
     then Z.land (encode_ready_grp s.(readyList) tasks)
       (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (old.(curPrio) / 8))) 8)
     else encode_ready_grp s.(readyList) tasks) /\
  forall row, encode_ready_tbl_at_or ready post_tasks row =
    if Z.eqb row (old.(curPrio) / 8)
    then Z.land (encode_ready_tbl_at_or s.(readyList) tasks row)
      (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (old.(curPrio) mod 8))) 8)
    else encode_ready_tbl_at_or s.(readyList) tasks row.
Proof.
  intros sg tasks s tid old new Hsg Htasks [[Hmembers [Hsorted [Hcomplete Hnd]]] Hcache] Hold Hin.
  cbn zeta; unfold sched_remove_ready_task, sched_set_ready; cbn [readyList].
  destruct (sched_encoding_priority_ext (remove_Z_eqb tid s.(readyList))
    (glob_task_set_usedtask tasks tid new) tasks
    ltac:(intros slot Hmember; simpl; destruct (Z.eqb slot tid) eqn:E; [|reflexivity];
      apply Z.eqb_eq in E; subst slot; exfalso; exact (remove_Z_eqb_notin tid s.(readyList) Hmember)))
    as [Hgroup Htable].
  destruct Htasks as [_ [_ [_ [_ [_ [_ [Hunique [Hprios _]]]]]]]].
  assert (Hrange : forall slot node, In slot s.(readyList) ->
    tasks.(inUsedTaskStates) slot = Some node -> 0 <= node.(curPrio)).
  { intros; exact (proj1 (Hprios _ _ H0)). }
  rewrite Hgroup; split.
  - eapply encode_ready_grp_remove_waiter; try eassumption.
    intros slot node Hmember Hnode; pose proof (Hprios slot node Hnode) as Hp.
    destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]]; unfold task_priority_in_range in Hp.
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia.
  - intro row; rewrite Htable.
    destruct (Z.eqb row (old.(curPrio) / 8)) eqn:E.
    + apply Z.eqb_eq in E; subst row; eapply encode_ready_tbl_or_remove_selected_row; eassumption.
    + eapply encode_ready_tbl_or_remove_other_row; [exact Hold|apply Z.eqb_neq in E; congruence].
Qed.

Lemma sched_remove_ready_member_row_values : forall sg tasks s tid old new,
  valid_stable_glob_vars sg -> task_in_range sg tasks -> sched_in_range sg tasks s ->
  tasks.(inUsedTaskStates) tid = Some old -> In tid s.(readyList) -> 0 <= old.(curPrio) / 8 < 8 ->
  sched_row_values (glob_task_set_usedtask tasks tid new)
    (sched_remove_ready_task s tid).(readyList) =
  replace_Znth (old.(curPrio) / 8)
    (Z.land (encode_ready_tbl_at_or s.(readyList) tasks (old.(curPrio) / 8))
      (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (old.(curPrio) mod 8))) 8))
    (sched_row_values tasks s.(readyList)).
Proof.
  intros sg tasks s tid old new Hsg Htasks Hsched Hold Hin Hrow.
  destruct (sched_remove_ready_member_encoding sg tasks s tid old new Hsg Htasks Hsched Hold Hin)
    as [_ Htable].
  unfold sched_row_values; cbn [map].
  rewrite (Htable 0), (Htable 1), (Htable 2), (Htable 3), (Htable 4), (Htable 5), (Htable 6), (Htable 7).
  set (row := old.(curPrio) / 8) in *.
  assert (Hcases : row = 0 \/ row = 1 \/ row = 2 \/ row = 3 \/
    row = 4 \/ row = 5 \/ row = 6 \/ row = 7) by lia.
  repeat destruct Hcases as [Hcases|Hcases]; rewrite Hcases; reflexivity.
Qed.

Lemma sched_rows_merge_removed_ready_member : forall sg tasks s tid old new,
  valid_stable_glob_vars sg -> task_in_range sg tasks -> sched_in_range sg tasks s ->
  tasks.(inUsedTaskStates) tid = Some old -> In tid s.(readyList) -> 0 <= old.(curPrio) / 8 < 8 ->
  (sg.(g_OSRdyTbl) + (old.(curPrio) / 8) * sizeof(UCHAR)) # UChar |->
    Z.land (encode_ready_tbl_at_or s.(readyList) tasks (old.(curPrio) / 8))
      (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (old.(curPrio) mod 8))) 8) **
  UCharArray.missing_i sg.(g_OSRdyTbl) (old.(curPrio) / 8) 0 8
    (sched_row_values tasks s.(readyList)) |--
  sched_rows_rep sg (glob_task_set_usedtask tasks tid new)
    (sched_remove_ready_task s tid).(readyList) [0;1;2;3;4;5;6;7].
Proof.
  intros sg tasks s tid old new Hsg Htasks Hsched Hold Hin Hrow.
  rewrite sched_rows_array_equiv.
  rewrite (sched_remove_ready_member_row_values sg tasks s tid old new Hsg Htasks Hsched Hold Hin Hrow).
  apply sched_rows_merge_updated_array; exact Hrow.
Qed.

Lemma bitmap_clear_absent_mask : forall width mask value,
  0 < width -> 0 <= mask < 2 ^ width -> 0 <= value < 2 ^ width ->
  Z.land mask value = 0 ->
  Z.land value (unsigned_last_nbits (Z.lnot mask) width) = value.
Proof.
  intros width mask value Hw Hmask Hvalue Hdisjoint.
  pose proof (bitmap_clear_disjoint_mask width mask value ltac:(lia)
    (bitmap_lor_in_range width mask value Hw Hmask Hvalue) Hdisjoint) as Hclear.
  rewrite Z.land_lor_distr_l in Hclear.
  assert (Hzero : Z.land mask (unsigned_last_nbits (Z.lnot mask) width) = 0).
  { rewrite <- (unsigned_last_nbits_eq mask width Hmask) at 1.
    rewrite <- unsigned_last_nbits_land_distr by lia; rewrite Z.land_lnot_diag.
    unfold unsigned_last_nbits; apply Z.mod_0_l; apply Z.pow_nonzero; lia. }
  rewrite Hzero, Z.lor_0_l in Hclear; exact Hclear.
Qed.

Lemma encode_ready_tbl_or_remove_selected_row_any : forall ids tasks tid t,
  0 <= t.(curPrio) -> NoDup ids -> tasks.(inUsedTaskStates) tid = Some t ->
  task_priority_unique tasks ->
  (forall slot node, In slot ids -> tasks.(inUsedTaskStates) slot = Some node -> 0 <= node.(curPrio)) ->
  encode_ready_tbl_at_or (remove_Z_eqb tid ids) tasks (t.(curPrio) / 8) =
    Z.land (encode_ready_tbl_at_or ids tasks (t.(curPrio) / 8))
      (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (t.(curPrio) mod 8))) 8).
Proof.
  intros ids tasks tid t Hp Hnd Ht Hunique Hrange.
  destruct (in_dec Z.eq_dec tid ids) as [Hin|Habsent].
  - eapply encode_ready_tbl_or_remove_selected_row; eassumption.
  - rewrite remove_Z_eqb_notin_eq by exact Habsent; symmetry.
    apply (bitmap_clear_absent_mask 8); [lia| |apply encode_ready_tbl_or_in_range|].
    + apply (bitmap_single_bit_in_range 8); apply Z.mod_pos_bound; lia.
    + apply sched_bit_disjoint_tbl_or; [exact Hp|reflexivity|exact Hrange|].
      intros slot node Hin Hnode Hsame.
      assert (slot = tid) by (eapply Hunique; eauto); subst slot; contradiction.
Qed.

Lemma encode_ready_grp_remove_waiter_any : forall ids tasks tid t,
  0 <= t.(curPrio) -> 0 <= t.(curPrio) / 8 < 8 ->
  NoDup ids -> tasks.(inUsedTaskStates) tid = Some t -> task_priority_unique tasks ->
  (forall slot node, In slot ids -> tasks.(inUsedTaskStates) slot = Some node -> 0 <= node.(curPrio)) ->
  (forall slot node, In slot ids -> tasks.(inUsedTaskStates) slot = Some node ->
    0 <= node.(curPrio) / 8 < 8) ->
  encode_ready_grp (remove_Z_eqb tid ids) tasks =
    let cleared := Z.land (encode_ready_tbl_at_or ids tasks (t.(curPrio) / 8))
      (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (t.(curPrio) mod 8))) 8) in
    if Z.eqb cleared 0
    then Z.land (encode_ready_grp ids tasks) (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (t.(curPrio) / 8))) 8)
    else encode_ready_grp ids tasks.
Proof.
  intros ids tasks tid t Hp Hrow Hnd Ht Hunique Hrange Hrows.
  destruct (in_dec Z.eq_dec tid ids) as [Hin|Habsent].
  - eapply encode_ready_grp_remove_waiter; eassumption.
  - pose proof (encode_ready_tbl_or_remove_selected_row_any ids tasks tid t Hp Hnd Ht Hunique Hrange)
      as Hclear.
    rewrite remove_Z_eqb_notin_eq in Hclear |- * by exact Habsent.
    rewrite <- Hclear; cbn zeta.
    destruct (Z.eqb (encode_ready_tbl_at_or ids tasks (t.(curPrio) / 8)) 0) eqn:Hempty;
      [|reflexivity].
    apply Z.eqb_eq in Hempty; symmetry.
    apply (bitmap_clear_absent_mask 8); [lia| |apply encode_ready_grp_in_range; exact Hrows|].
    + apply (bitmap_single_bit_in_range 8); exact Hrow.
    + apply sched_no_group_row; [exact (proj1 Hrow)| |].
      * intros; exact (proj1 (Hrows _ _ H H0)).
      * intros slot node Hin Hnode Hsame.
        pose proof (encode_ready_tbl_or_present_row_nonzero ids tasks slot node Hin Hnode) as Hnonzero.
        rewrite Hsame, Hempty in Hnonzero; contradiction.
Qed.

(** Structural ready-list facts are independent of the old single-wait
    status projection.  The bitmap owns membership; Task/Event wait-phase
    relations must justify when a source operation changes that membership.
    This is a component of scheduler validity, not its replacement. *)
Definition sched_ready_structure (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (s : SchedAbstractState) : Prop :=
  (forall tid, In tid s.(readyList) -> exists t,
    tasks.(inUsedTaskStates) tid = Some t /\ task_priority_in_range sg t.(curPrio)) /\
  strictly_sorted_by (sched_task_key sg tasks) s.(readyList) /\
  NoDup s.(readyList).

Lemma sched_ready_in_range_implies_structure : forall sg tasks s,
  sched_ready_in_range sg tasks s -> sched_ready_structure sg tasks s.
Proof.
  intros sg tasks s [Hmembers [Hsorted [_ Hnd]]].
  split; [|split; assumption].
  intros tid Hin; destruct (Hmembers tid Hin) as [t [Ht [Hp _]]]; exists t; auto.
Qed.

Lemma sched_ready_structure_update_task : forall sg tasks s tid old new,
  tasks.(inUsedTaskStates) tid = Some old -> new.(curPrio) = old.(curPrio) ->
  sched_ready_structure sg tasks s ->
  sched_ready_structure sg (glob_task_set_usedtask tasks tid new) s.
Proof.
  intros sg tasks s tid old new Hold Hprio [Hmembers [Hsorted Hnd]].
  split.
  - intros slot Hin; destruct (Hmembers slot Hin) as [node [Hnode Hp]].
    simpl; destruct (Z.eqb slot tid) eqn:E.
    + apply Z.eqb_eq in E; subst slot; assert (node = old) by congruence; subst node.
      exists new; split; [reflexivity|rewrite Hprio; exact Hp].
    + exists node; auto.
  - split; [|exact Hnd].
    eapply strictly_sorted_by_key_ext; [|exact Hsorted].
    intro slot; unfold sched_task_key; simpl; destruct (Z.eqb slot tid) eqn:E; [|reflexivity].
    apply Z.eqb_eq in E; subst slot; rewrite Hold; symmetry; exact Hprio.
Qed.

Lemma sched_remove_ready_preserves_structure : forall sg tasks s tid,
  sched_ready_structure sg tasks s ->
  sched_ready_structure sg tasks (sched_remove_ready_task s tid).
Proof.
  intros sg tasks s tid [Hmembers [Hsorted Hnd]]; split.
  - intros slot Hin; apply Hmembers; eapply remove_Z_eqb_in; exact Hin.
  - split; [apply remove_Z_eqb_strictly_sorted_by|apply remove_Z_eqb_NoDup]; assumption.
Qed.

(** Exact ready insertion used after EventTaskRdy's status mask and after
    Tick expiration.  A remaining SEM/MBOX/Q/MULTI bit is not a guard in C;
    only the actual suspension bit controls these stores. *)
Definition sched_wake_by_status (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (s : SchedAbstractState) (tid : TaskID) (bits : Z) : SchedAbstractState :=
  if task_status_is_suspended bits then s
  else sched_set_ready s
    (insert_sorted_by (sched_task_key sg tasks) tid (remove_Z_eqb tid s.(readyList))).

Lemma sched_wake_by_status_membership : forall sg tasks s tid bits slot,
  In slot (sched_wake_by_status sg tasks s tid bits).(readyList) <->
  In slot s.(readyList) \/ (slot = tid /\ task_status_is_suspended bits = false).
Proof.
  intros; unfold sched_wake_by_status.
  destruct (task_status_is_suspended bits) eqn:Hsus; [simpl; intuition discriminate|].
  cbn [sched_set_ready readyList]; rewrite insert_sorted_by_in; simpl.
  split.
  - intros [Heq|Hin]; [right; auto|left; eapply remove_Z_eqb_in; exact Hin].
  - intros [Hin|[Heq _]]; [|left; symmetry; exact Heq].
    destruct (Z.eq_dec slot tid) as [->|Hne]; [left; reflexivity|].
    right; apply remove_Z_eqb_in_neq; assumption.
Qed.

Lemma sched_wake_by_status_preserves_structure : forall sg tasks s tid t bits,
  task_priority_unique tasks -> tasks.(inUsedTaskStates) tid = Some t ->
  task_priority_in_range sg t.(curPrio) -> sched_ready_structure sg tasks s ->
  sched_ready_structure sg tasks (sched_wake_by_status sg tasks s tid bits).
Proof.
  intros sg tasks s tid t bits Hunique Ht Hp [Hmembers [Hsorted Hnd]].
  unfold sched_wake_by_status; destruct task_status_is_suspended;
    [split; [exact Hmembers|split; assumption]|].
  split.
  - intros slot Hin; apply insert_sorted_by_in in Hin; simpl in Hin.
    destruct Hin as [<-|Hin]; [exists t; auto|].
    apply Hmembers; eapply remove_Z_eqb_in; exact Hin.
  - split.
    + apply insert_sorted_by_preserves.
      * apply remove_Z_eqb_strictly_sorted_by; exact Hsorted.
      * intros slot Hin Heq.
        destruct (Hmembers slot (remove_Z_eqb_in tid slot s.(readyList) Hin)) as [node [Hnode _]].
        unfold sched_task_key in Heq; rewrite Hnode, Ht in Heq.
        assert (slot = tid) by (eapply Hunique; eauto); subst slot.
        exact (remove_Z_eqb_notin tid s.(readyList) Hin).
    + apply insert_sorted_by_preserves_NoDup;
        [apply remove_Z_eqb_NoDup; exact Hnd|apply remove_Z_eqb_notin].
Qed.

Lemma sched_wake_by_status_physical_rep_eq : forall sg tasks s tid bits,
  sched_physical_rep sg (sched_wake_by_status sg tasks s tid bits) =
    sched_physical_rep sg s.
Proof. intros; unfold sched_wake_by_status; destruct task_status_is_suspended; reflexivity. Qed.

Lemma sched_wake_by_status_eq_wake_task : forall sg tasks s tid bits new,
  is_effectively_ready new.(stat) new.(dly) = negb (task_status_is_suspended bits) ->
  sched_wake_by_status sg tasks s tid bits = sched_wake_task sg tasks s tid new.
Proof.
  intros sg tasks s tid bits new Hready.
  unfold sched_wake_by_status, sched_wake_task; rewrite Hready.
  destruct (task_status_is_suspended bits); [destruct s|]; reflexivity.
Qed.

Lemma sched_wake_by_status_running_eq : forall sg tasks s tid bits,
  (sched_wake_by_status sg tasks s tid bits).(isRunning) = s.(isRunning).
Proof. intros; unfold sched_wake_by_status; destruct task_status_is_suspended; reflexivity. Qed.

Lemma sched_wake_by_status_encoding : forall sg tasks s tid t bits,
  tasks.(inUsedTaskStates) tid = Some t ->
  let ready := (sched_wake_by_status sg tasks s tid bits).(readyList) in
  encode_ready_grp ready tasks =
    (if task_status_is_suspended bits then encode_ready_grp s.(readyList) tasks
     else Z.lor (encode_ready_grp s.(readyList) tasks) (Z.shiftl 1 (t.(curPrio) / 8))) /\
  forall row, encode_ready_tbl_at_or ready tasks row =
    (if task_status_is_suspended bits then encode_ready_tbl_at_or s.(readyList) tasks row
     else if Z.eqb (t.(curPrio) / 8) row
     then Z.lor (encode_ready_tbl_at_or s.(readyList) tasks row) (Z.shiftl 1 (t.(curPrio) mod 8))
     else encode_ready_tbl_at_or s.(readyList) tasks row).
Proof.
  intros sg tasks s tid t bits Ht; cbn zeta; unfold sched_wake_by_status.
  destruct task_status_is_suspended; [split; reflexivity|]; cbn [sched_set_ready readyList].
  split; [eapply encode_ready_grp_insert_remove|intro row; eapply encode_ready_tbl_insert_remove]; exact Ht.
Qed.

(** Ready clearing depends on the priority/bitmap structure, not on a
    one-kind TaskStatus.  In particular it applies after a Multi caller
    has already ORed several pending bits into the TCB. *)
Lemma sched_remove_ready_encoding : forall sg tasks s tid t,
  valid_stable_glob_vars sg -> task_priority_unique tasks ->
  tasks.(inUsedTaskStates) tid = Some t -> task_priority_in_range sg t.(curPrio) ->
  sched_ready_structure sg tasks s ->
  let ready := (sched_remove_ready_task s tid).(readyList) in
  encode_ready_grp ready tasks =
    (let cleared := Z.land (encode_ready_tbl_at_or s.(readyList) tasks (t.(curPrio) / 8))
       (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (t.(curPrio) mod 8))) 8) in
     if Z.eqb cleared 0 then Z.land (encode_ready_grp s.(readyList) tasks)
       (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (t.(curPrio) / 8))) 8)
     else encode_ready_grp s.(readyList) tasks) /\
  forall row, encode_ready_tbl_at_or ready tasks row =
    if Z.eqb row (t.(curPrio) / 8)
    then Z.land (encode_ready_tbl_at_or s.(readyList) tasks row)
      (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (t.(curPrio) mod 8))) 8)
    else encode_ready_tbl_at_or s.(readyList) tasks row.
Proof.
  intros sg tasks s tid t Hsg Hunique Ht Hp [Hmembers [_ Hnd]]; cbn zeta.
  destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]].
  assert (Hrows : forall slot node, In slot s.(readyList) ->
    tasks.(inUsedTaskStates) slot = Some node -> 0 <= node.(curPrio) / 8 < 8).
  { intros slot node Hin Hnode; destruct (Hmembers slot Hin) as [found [Hfound Hprio]].
    assert (found = node) by congruence; subst found; unfold task_priority_in_range in Hprio.
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  assert (Hrange : forall slot node, In slot s.(readyList) ->
    tasks.(inUsedTaskStates) slot = Some node -> 0 <= node.(curPrio)).
  { intros slot node Hin Hnode; destruct (Hmembers slot Hin) as [found [Hfound Hprio]].
    assert (found = node) by congruence; subst found; exact (proj1 Hprio). }
  unfold task_priority_in_range in Hp; split.
  - apply encode_ready_grp_remove_waiter_any; try assumption; [lia|].
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia.
  - intro row; destruct (Z.eqb row (t.(curPrio) / 8)) eqn:E.
    + apply Z.eqb_eq in E; subst row; apply encode_ready_tbl_or_remove_selected_row_any; try assumption; lia.
    + eapply encode_ready_tbl_or_remove_other_row; [exact Ht|apply Z.eqb_neq in E; congruence].
Qed.

(** Resume's source-order ready decision after its status-cell clear.
    It is separate from EventTaskRdy's suspension-only decision. *)
Definition sched_resume_task (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (s : SchedAbstractState) (tid : TaskID) (t : TaskAbstractState) : SchedAbstractState :=
  if task_resume_ready_test t then
    sched_wake_by_status sg tasks s tid (encode_task_status (task_resume t).(stat))
  else s.

Lemma sched_resume_task_ready_membership : forall sg tasks s tid t slot,
  In slot (sched_resume_task sg tasks s tid t).(readyList) <-> In slot s.(readyList) \/
    (slot = tid /\ Z.land (encode_task_status t.(stat)) task_pend_any_mask = 0 /\ t.(dly) = 0).
Proof.
  intros; unfold sched_resume_task; destruct (task_resume_ready_test t) eqn:Hready.
  - apply task_resume_ready_test_iff in Hready.
    rewrite sched_wake_by_status_membership.
    change ((In slot s.(readyList) \/
      (slot = tid /\ task_is_suspended (task_status_resume t.(stat)) = false)) <->
      In slot s.(readyList) \/
      (slot = tid /\ Z.land (encode_task_status t.(stat)) task_pend_any_mask = 0 /\ t.(dly) = 0)).
    rewrite (proj2 (task_status_resume_observations t.(stat))); tauto.
  - assert (Hblocked : ~ (Z.land (encode_task_status t.(stat)) task_pend_any_mask = 0 /\ t.(dly) = 0)).
    { intro H; apply task_resume_ready_test_iff in H; congruence. }
    tauto.
Qed.

Lemma sched_resume_task_eq_wake_task : forall sg tasks s tid t,
  task_status_reserved_bits_clear false t.(stat) ->
  sched_resume_task sg tasks s tid t = sched_wake_task sg tasks s tid (task_resume t).
Proof.
  intros sg tasks s tid t Hbits; unfold sched_resume_task, sched_wake_task.
  rewrite <- (task_resume_effectively_ready_eq_test t Hbits).
  assert (Hclear : task_status_is_suspended (encode_task_status (task_resume t).(stat)) = false)
    by exact (proj2 (task_status_resume_observations t.(stat))).
  unfold sched_wake_by_status; rewrite Hclear.
  destruct (is_effectively_ready (task_resume t).(stat) (task_resume t).(dly));
    [reflexivity|destruct s; reflexivity].
Qed.

Lemma sched_resume_task_preserves_in_range : forall sg tasks s tid t,
  task_in_range sg tasks -> sched_in_range sg tasks s ->
  tasks.(inUsedTaskStates) tid = Some t -> task_is_suspended t.(stat) = true ->
  task_status_reserved_bits_clear false t.(stat) ->
  sched_in_range sg (glob_task_set_usedtask tasks tid (task_resume t))
    (sched_resume_task sg tasks s tid t).
Proof.
  intros sg tasks s tid t Htasks Hsched Ht Hsusp Hbits.
  rewrite sched_resume_task_eq_wake_task by exact Hbits.
  eapply sched_wake_task_preserves_in_range;
    [exact Htasks|exact Hsched|exact Ht|reflexivity|].
  intro Hready; unfold is_effectively_ready in Hready; rewrite Hsusp in Hready.
  destruct (Z.eqb (task_non_suspension_bits t.(stat)) 0); discriminate.
Qed.

Lemma sched_resume_task_physical_rep_eq : forall sg tasks s tid t,
  sched_physical_rep sg (sched_resume_task sg tasks s tid t) = sched_physical_rep sg s.
Proof.
  intros; unfold sched_resume_task; destruct task_resume_ready_test;
    [apply sched_wake_by_status_physical_rep_eq|reflexivity].
Qed.

Lemma sched_resume_task_running_eq : forall sg tasks s tid t,
  (sched_resume_task sg tasks s tid t).(isRunning) = s.(isRunning).
Proof.
  intros; unfold sched_resume_task, sched_wake_by_status.
  destruct task_resume_ready_test; [destruct task_status_is_suspended|]; reflexivity.
Qed.
