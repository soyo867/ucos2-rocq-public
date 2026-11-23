Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From MonadLib Require Import Monad.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.array_abstraction.

Import ListNotations.
Import UCOS2_C_Rules.
Import TaskStateDef.
Import SchedStateDef.
Import EventStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(* Raw source-call domain shared by every ready owner passed to
   OSMutex_RdyAtPrio.  The helper needs only a represented task, membership in
   the ready list, and an in-range destination index.  In particular, neither
   [curTaskID]/[curSchedPrio] agreement nor a destination-slot compatibility
   check is a C execution guard.  Those stronger facts belong to a call-site
   specialization or to invariant-closure theorems. *)
Definition ready_owner_relocation_domain
  (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (schedSt : SchedAbstractState)
  (tid : TaskID)
  (old_t : TaskAbstractState) (newPrio : Priority) : Prop :=
  tskSt.(inUsedTaskStates) tid = Some old_t /\
  In tid schedSt.(readyList) /\
  verification_slice_priority_index sg newPrio.

(* The repaired helper updates the scheduler's current-priority cache exactly
   when the relocated ready owner is the current task.  Keeping this as a
   small mathematical state projection makes the current and non-current
   cases explicit without restricting the public ready-owner domain. *)
Definition ready_owner_cur_prio_after
  (schedSt : SchedAbstractState) (tid : TaskID) (newPrio : Priority)
  : option Priority :=
  match schedSt.(curTaskID) with
  | Some current_tid =>
      if Z.eqb current_tid tid
      then Some newPrio
      else schedSt.(curSchedPrio)
  | None => schedSt.(curSchedPrio)
  end.

Definition ready_owner_cur_prio_value_after
  (schedSt : SchedAbstractState) (tid : TaskID) (newPrio : Priority) : Z :=
  match ready_owner_cur_prio_after schedSt tid newPrio with
  | Some p => p
  | None => 0xFF
  end.

(* Source-call domain of the internal current-ready-task relocation helper.
   It is deliberately task/scheduler-only and mirrors the premises of
   [atomic_task_set_curPrio_ready_literal_exec]: the selected TCB is the
   current used ready task, OSPrioCur agrees with its entry priority, the
   destination is a valid table index, and no condition is imposed on the
   destination entry.  The C helper overwrites [PTFree], [PTReserved],
   [PTTask tid], and [PTTask other] alike.  Destination-slot compatibility,
   priority uniqueness, and ownership of a consumed reservation are
   invariant-closure obligations carried by [task_priority_relocation_legal],
   not raw execution guards.  Likewise this domain contains no event state,
   target-mutex reason, old-slot assumption, or restore-safety premise. *)
Definition ready_task_relocation_domain
  (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (schedSt : SchedAbstractState)
  (tid : TaskID)
  (old_t : TaskAbstractState) (newPrio : Priority) : Prop :=
  tskSt.(inUsedTaskStates) tid = Some old_t /\
  In tid schedSt.(readyList) /\
  schedSt.(curTaskID) = Some tid /\
  schedSt.(curSchedPrio) = Some old_t.(curPrio) /\
  verification_slice_priority_index sg newPrio.

(* Canonical call-contract consequence for the current-owner restore branch.
   OSMutexPost may establish these facts from its focused mutex/task/scheduler
   state and then use the unique exact contract above.  A generalized
   OSMutexDel owner restore that is noncurrent, waiting, or dormant cannot
   discharge the current/ready premises and therefore requires its distinct
   transformer/helper rather than this literal contract. *)
Lemma OSMutex_RdyAtPrio_raw_domain_consequence :
  forall sg tskSt schedSt tid old_t newPrio,
    tskSt.(inUsedTaskStates) tid = Some old_t ->
    In tid schedSt.(readyList) ->
    schedSt.(curTaskID) = Some tid ->
    schedSt.(curSchedPrio) = Some old_t.(curPrio) ->
    verification_slice_priority_index sg newPrio ->
    ready_task_relocation_domain
      sg tskSt schedSt tid old_t newPrio.
Proof.
  intros sg tskSt schedSt tid old_t newPrio
    Hget Hin Hcur Hcurprio Hvalid.
  unfold ready_task_relocation_domain.
  split; [exact Hget|].
  split; [exact Hin|].
  split; [exact Hcur|].
  split; [exact Hcurprio|].
  exact Hvalid.
Qed.

(* The raw domain deliberately says nothing about the destination slot.
   Uniqueness needed to rebuild task/scheduler invariants is instead derived
   from the generic mutex/task relocation-closure predicate.  This keeps a
   [PTTask other] overwrite in raw execution while rejecting it from the
   stable-invariant preservation theorem. *)
Lemma ready_task_relocation_destination_unique_from_closure :
  forall sg ls tid newPrio,
    verification_slice_task_validity sg ls.(TskState) ->
    task_priority_relocation_legal sg ls tid newPrio ->
    forall tid' t',
      ls.(TskState).(inUsedTaskStates) tid' = Some t' ->
      t'.(curPrio) = newPrio ->
      tid' = tid.
Proof.
  intros sg ls tid newPrio Htask Hlegal tid' t'
    Hget Hprio.
  pose proof
    (task_vaild_cond_current_prio_registered sg ls.(TskState) Htask)
    as Hregistered.
  specialize (Hregistered tid' t' Hget).
  rewrite Hprio in Hregistered.
  unfold task_priority_relocation_legal in Hlegal.
  destruct Hlegal as
    (legal_t & Hlegal_get & [Htaskslot | [Hreserved Hclaim]] &
     Hrestore_safe & Hold_alias).
  - rewrite Htaskslot in Hregistered. inversion Hregistered. reflexivity.
  - rewrite Hreserved in Hregistered. discriminate.
Qed.

(* A destination occupied by a different task is excluded exactly by the
   closure classifier.  The raw owner domain and transformer contain no such
   premise, so this lemma cannot suppress the corresponding C execution. *)
Lemma task_priority_relocation_legal_rejects_other_task_slot :
  forall sg ls tid other newPrio,
    task_priority_relocation_legal sg ls tid newPrio ->
    ls.(TskState).(prioTbl) newPrio = PTTask other ->
    other <> tid -> False.
Proof.
  intros sg ls tid other newPrio Hlegal Hslot Hneq.
  unfold task_priority_relocation_legal in Hlegal.
  destruct Hlegal as
    (t & Hget & [Hsame | [Hreserved Hclaim]] & Hsafe & Hold_alias).
  - rewrite Hslot in Hsame. inversion Hsame. contradiction.
  - rewrite Hslot in Hreserved. discriminate.
Qed.

Lemma ready_task_relocation_domain_is_current_ready :
  forall sg tskSt schedSt tid old_t newPrio,
    ready_task_relocation_domain
      sg tskSt schedSt tid old_t newPrio ->
    In tid schedSt.(readyList) /\ schedSt.(curTaskID) = Some tid.
Proof.
  intros sg tskSt schedSt tid old_t newPrio Hdom.
  unfold ready_task_relocation_domain in Hdom.
  tauto.
Qed.

(* A concrete raw-domain family witnesses that an equal-priority literal call
   remains executable.  This lemma claims neither whole-state identity nor a
   global-invariant witness: the total transformer still records the concrete
   priority-table write, and restore safety is classified separately. *)
Lemma ready_task_relocation_domain_same_priority_nonvacuous :
  forall sg tid old_t p,
    old_t.(curPrio) = p ->
    verification_slice_priority_index sg p ->
    exists tskSt schedSt,
      ready_task_relocation_domain
        sg tskSt schedSt tid old_t p.
Proof.
  intros sg tid old_t p Hcur Hvalid.
  exists
    {| inUsedTaskStates := fun tid' =>
         if Z.eqb tid' tid then Some old_t else None;
       unUsedTaskStates := [];
       tcbListHead := Some tid;
       prioTbl := fun _ => PTTask tid;
       taskRegNextID := 0;
       parkedTaskStacks := fun _ => None;
       taskLifecycle := empty_task_lifecycle;
     taskCount := 1 |}.
  exists
    {| readyList := [tid];
       curTaskID := Some tid;
       curSchedPrio := Some old_t.(curPrio);
       highRdyTid := Some tid;
       highRdyPrio := Some old_t.(curPrio);
       ctxSwCtr := 0;
       isRunning := true |}.
  unfold ready_task_relocation_domain.
  cbn.
  rewrite Z.eqb_refl.
  split; [reflexivity|].
  split; [left; reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  exact Hvalid.
Qed.

(* The public ready-owner domain genuinely includes non-current owners.  This
   witness prevents the public contract from collapsing back to the stronger
   current-ready specialization through an accidentally vacuous premise. *)
Lemma ready_owner_relocation_domain_noncurrent_nonvacuous :
  forall sg tid old_t newPrio,
    verification_slice_priority_index sg newPrio ->
    exists tskSt schedSt,
      ready_owner_relocation_domain
        sg tskSt schedSt tid old_t newPrio /\
      schedSt.(curTaskID) = None.
Proof.
  intros sg tid old_t newPrio Hvalid.
  exists
    {| inUsedTaskStates := fun tid' =>
         if Z.eqb tid' tid then Some old_t else None;
       unUsedTaskStates := [];
       tcbListHead := Some tid;
       prioTbl := fun _ => PTTask tid;
       taskRegNextID := 0;
       parkedTaskStacks := fun _ => None;
       taskLifecycle := empty_task_lifecycle;
     taskCount := 1 |}.
  exists
    {| readyList := [tid];
       curTaskID := None;
       curSchedPrio := None;
       highRdyTid := Some tid;
       highRdyPrio := Some old_t.(curPrio);
       ctxSwCtr := 0;
       isRunning := true |}.
  split.
  - unfold ready_owner_relocation_domain. cbn.
    rewrite Z.eqb_refl.
    split; [reflexivity|].
    split; [left; reflexivity|].
    exact Hvalid.
  - reflexivity.
Qed.

(* Exact total abstract effect of the literal ready-task helper.  This shared
   transformer covers equal and unequal priorities and always records the final
   priority-table write; it contains no restore-safety precondition. *)
Definition OSMutex_RdyAtPrio_ready_effect
  (sg : StableGlobVars) (tid : TaskID) (old_t : TaskAbstractState)
  (newPrio : Priority) : program UCOS2_Verify_State unit :=
  atomic_task_set_curPrio_ready_literal_exec sg tid old_t newPrio.

(* Source-exact total transformer for the repaired public helper.  It retains
   the literal task, ready-list and destination-table updates of the old raw
   owner transformer, but models the concrete [ptcb == OSTCBCur] test: the
   current-priority cache is changed only for the current owner. *)
Definition atomic_task_set_curPrio_ready_owner_exec
  (sg : StableGlobVars) (tid : TaskID) (old_t : TaskAbstractState)
  (newPrio : Priority) : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists t',
      In tid lvs1.(SchedState).(readyList) /\
      lvs1.(TskState).(inUsedTaskStates) tid = Some old_t /\
      0 <= newPrio /\ newPrio < sg.(osLowestPrio) /\
      t' = {| taskID        := old_t.(taskID);
     taskGeneration := old_t.(taskGeneration);
     tcbStkPtr := old_t.(tcbStkPtr);
     tcbExtPtr := old_t.(tcbExtPtr);
     tcbStkBottom := old_t.(tcbStkBottom);
     tcbStkSize := old_t.(tcbStkSize);
     tcbOpt := old_t.(tcbOpt);
     tcbPublicId := old_t.(tcbPublicId);
     tcbFlagNode := old_t.(tcbFlagNode);
     tcbFlagsRdy := old_t.(tcbFlagsRdy);
     tcbTaskName := old_t.(tcbTaskName);
     tcbReg0 := old_t.(tcbReg0);
     tcbCtxSwCtr := old_t.(tcbCtxSwCtr);
     tcbCyclesTot := old_t.(tcbCyclesTot);
     tcbCyclesStart := old_t.(tcbCyclesStart);
     tcbStkBase := old_t.(tcbStkBase);
     tcbStkUsed := old_t.(tcbStkUsed);
     tcbPadding42 := old_t.(tcbPadding42);
     tcbPadding43 := old_t.(tcbPadding43);
     tcbEventMultiPtr := old_t.(tcbEventMultiPtr);
              curPrio       := newPrio;
              stat          := old_t.(stat);
              statPend      := old_t.(statPend);
              dly           := old_t.(dly);
              eventPtr      := old_t.(eventPtr);
              eventMultiWaitEvents := old_t.(eventMultiWaitEvents);
              eventMultiRdy := old_t.(eventMultiRdy);
              msg            := old_t.(msg);
              nextTCB        := old_t.(nextTCB);
              prevTCB        := old_t.(prevTCB);
              delReq         := old_t.(delReq)
           |} /\
      (let tskSt2 :=
         {| inUsedTaskStates := fun tid' =>
              if Z.eqb tid' tid then Some t'
              else lvs1.(TskState).(inUsedTaskStates) tid';
            unUsedTaskStates := lvs1.(TskState).(unUsedTaskStates);
            tcbListHead      := lvs1.(TskState).(tcbListHead);
            prioTbl          := fun p =>
              if Z.eqb p newPrio then PTTask tid
              else lvs1.(TskState).(prioTbl) p;
            taskRegNextID := lvs1.(TskState).(taskRegNextID);
            parkedTaskStacks := lvs1.(TskState).(parkedTaskStacks);
            taskLifecycle := lvs1.(TskState).(taskLifecycle);
     taskCount        := lvs1.(TskState).(taskCount)
         |}
       in
       let schedSt1 := lvs1.(SchedState) in
       let filtered := Ucos2Verify.lib.helpers.remove_Z_eqb
                         tid schedSt1.(readyList) in
       let newReadyList := Ucos2Verify.lib.helpers.insert_sorted_by
                             (fun (tid' : TaskID) =>
                               match tskSt2.(inUsedTaskStates) tid' with
                               | Some t'' => t''.(curPrio)
                               | None => sg.(osLowestPrio) + 1
                               end)
                             tid filtered
       in
       let schedSt2 :=
         {| readyList    := newReadyList;
            curTaskID    := schedSt1.(curTaskID);
            curSchedPrio := ready_owner_cur_prio_after
                              schedSt1 tid newPrio;
            highRdyTid   := match newReadyList with
                            | head :: _ => Some head
                            | [] => None
                            end;
            highRdyPrio  := match newReadyList with
                            | head :: _ =>
                                match tskSt2.(inUsedTaskStates) head with
                                | Some t'' => Some t''.(curPrio)
                                | None => None
                                end
                            | [] => None
                            end;
            ctxSwCtr     := schedSt1.(ctxSwCtr);
            isRunning    := schedSt1.(isRunning)
         |}
       in
       lvs2 = {|
         IntrState  := lvs1.(IntrState);
         TskState   := tskSt2;
         SchedState := schedSt2;
         EventState := lvs1.(EventState);
         TickState  := lvs1.(TickState);
         FlagState := lvs1.(FlagState);
         MemoryState := lvs1.(MemoryState);
         TimerState := lvs1.(TimerState);
         StatsState := lvs1.(StatsState);
         ControlState := lvs1.(ControlState);
         NameState := lvs1.(NameState)
       |}).

(* Current-task specialization used by OSMutexPost.  It deliberately retains
   the current-task/current-priority protocol needed by the existing
   preservation proofs; it is not the public helper's full raw call domain. *)
Definition OSMutex_RdyAtPrio_current_ready_sem
  (sg : StableGlobVars) (ptcb : addr) (prio : Priority)
  : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists tid old_t,
      ptcb = verification_slice_tcb_addr sg tid /\
      ready_task_relocation_domain
        sg lvs1.(TskState) lvs1.(SchedState) tid old_t prio /\
      OSMutex_RdyAtPrio_ready_effect sg tid old_t prio lvs1 tt lvs2.

(* Public source-exact L5 semantics.  OSMutexDel may pass a ready owner that is
   not the current task; the repaired helper preserves OSPrioCur on that path
   and updates it only when the owner is current. *)
Definition OSMutex_RdyAtPrio_sem
  (sg : StableGlobVars) (ptcb : addr) (prio : Priority)
  : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists tid old_t,
      ptcb = verification_slice_tcb_addr sg tid /\
      ready_owner_relocation_domain
        sg lvs1.(TskState) lvs1.(SchedState) tid old_t prio /\
      atomic_task_set_curPrio_ready_owner_exec
        sg tid old_t prio lvs1 tt lvs2.

Lemma ready_task_relocation_domain_refines_ready_owner_domain :
  forall sg tskSt schedSt tid old_t newPrio,
    ready_task_relocation_domain
      sg tskSt schedSt tid old_t newPrio ->
    ready_owner_relocation_domain
      sg tskSt schedSt tid old_t newPrio.
Proof.
  intros sg tskSt schedSt tid old_t newPrio Hdom.
  unfold ready_task_relocation_domain in Hdom.
  unfold ready_owner_relocation_domain.
  destruct Hdom as (Hget & Hin & Hcur & Hcurprio & Hvalid).
  split; [exact Hget|].
  split; [exact Hin|].
  exact Hvalid.
Qed.

Lemma current_ready_literal_exec_refines_ready_owner_exec :
  forall sg tid old_t newPrio lvs1 lvs2,
    atomic_task_set_curPrio_ready_literal_exec
      sg tid old_t newPrio lvs1 tt lvs2 ->
    atomic_task_set_curPrio_ready_owner_exec
      sg tid old_t newPrio lvs1 tt lvs2.
Proof.
  intros sg tid old_t newPrio lvs1 lvs2 Hexec.
  unfold atomic_task_set_curPrio_ready_literal_exec in Hexec.
  unfold atomic_task_set_curPrio_ready_owner_exec.
  destruct Hexec as
    (t' & Hin & Hcur & Hcurprio & Hget & Hlo & Hhi & Hnew & Hpost).
  exists t'.
  split; [exact Hin|].
  split; [exact Hget|].
  split; [exact Hlo|].
  split; [exact Hhi|].
  split; [exact Hnew|].
  cbv zeta in Hpost |- *.
  unfold ready_owner_cur_prio_after.
  rewrite Hcur in Hpost |- *.
  rewrite Z.eqb_refl.
  exact Hpost.
Qed.

(* Conversely, once the current-ready call-site facts are supplied, the
   source-exact ready-owner transformer is definitionally the current-ready
   transformer.  This is the bridge used by conditional invariant closure;
   it does not narrow the public execution domain. *)
Lemma ready_owner_exec_current_specialization :
  forall sg tid old_t newPrio lvs1 lvs2,
    ready_task_relocation_domain
      sg lvs1.(TskState) lvs1.(SchedState) tid old_t newPrio ->
    atomic_task_set_curPrio_ready_owner_exec
      sg tid old_t newPrio lvs1 tt lvs2 ->
    atomic_task_set_curPrio_ready_literal_exec
      sg tid old_t newPrio lvs1 tt lvs2.
Proof.
  intros sg tid old_t newPrio lvs1 lvs2 Hdom Hraw.
  unfold ready_task_relocation_domain in Hdom.
  destruct Hdom as (Hget & Hin & Hcur & HcurPrio & Hvalid).
  unfold atomic_task_set_curPrio_ready_owner_exec in Hraw.
  destruct Hraw as
    (new_t & Hin' & Hget' & Hlo & Hhi & Hnew & Hpost).
  unfold atomic_task_set_curPrio_ready_literal_exec.
  exists new_t.
  split; [exact Hin'|].
  split; [exact Hcur|].
  split; [exact HcurPrio|].
  split; [exact Hget'|].
  split; [exact Hlo|].
  split; [exact Hhi|].
  split; [exact Hnew|].
  cbv zeta in Hpost |- *.
  unfold ready_owner_cur_prio_after in Hpost |- *.
  rewrite Hcur in Hpost |- *.
  rewrite Z.eqb_refl in Hpost.
  exact Hpost.
Qed.

(* The stronger Post call-site relation is a genuine specialization of the
   public ready-owner helper, rather than a competing public specification. *)
Lemma OSMutex_RdyAtPrio_current_ready_refines_public :
  forall sg ptcb prio lvs1 lvs2,
    OSMutex_RdyAtPrio_current_ready_sem
      sg ptcb prio lvs1 tt lvs2 ->
    OSMutex_RdyAtPrio_sem sg ptcb prio lvs1 tt lvs2.
Proof.
  intros sg ptcb prio lvs1 lvs2 Hsem.
  unfold OSMutex_RdyAtPrio_current_ready_sem in Hsem.
  unfold OSMutex_RdyAtPrio_sem.
  destruct Hsem as (tid & old_t & Haddr & Hdom & Heffect).
  exists tid, old_t.
  split; [exact Haddr|].
  split.
  - eapply ready_task_relocation_domain_refines_ready_owner_domain.
    exact Hdom.
  - unfold OSMutex_RdyAtPrio_ready_effect in Heffect.
    eapply current_ready_literal_exec_refines_ready_owner_exec.
    exact Heffect.
Qed.

(* Operation-labelled L5 guarantee.  Unlike the ambient [RTrans_Abs], this
   relation keeps both endpoints and admits only the exact ready-owner
   relocation above.  Current-ready invariant preservation is stated
   separately for [OSMutex_RdyAtPrio_current_ready_sem]'s domain/effect. *)
Definition OSMutex_RdyAtPrio_guarantee
  (sg : StableGlobVars) (ptcb : addr) (prio : Priority)
  (ls0 ls_post : UCOS2_Verify_State) : Prop :=
  OSMutex_RdyAtPrio_sem sg ptcb prio ls0 tt ls_post.

(* Exact in-critical representation after the literal helper.  The abstract
   [ls_post] is still the precise ready-only relocation target.  Its task,
   ready bitmap, current-priority, priority-table and all untouched module
   resources are represented exactly.  The only intentionally pending
   scheduler fields are OSPrioHighRdy/OSTCBHighRdy, which the C helper does
   not write and which therefore retain the entry scheduler snapshot.  The
   critical STS token is kept separately at [ls0] by the C contract; it is
   not unsoundly retagged by a plain separation entailment. *)
Definition OSMutex_RdyAtPrio_stage_inv
  (sg : StableGlobVars) (ls0 ls_post : UCOS2_Verify_State) : Assertion :=
  interrupt_inv sg ls_post.(IntrState) **
  verification_slice_task_inv sg ls_post.(TskState) **
  verification_slice_sched_inv_ready_prio_stage
    sg ls0.(SchedState) ls_post.(SchedState) ls_post.(TskState) **
  verification_slice_event_inv sg ls_post.(TskState) ls_post.(EventState) **
  verification_slice_tick_inv sg ls_post.(TickState) **
  coq_prop (verification_slice_cross_module_consistency sg ls_post).

(* Exact concrete ownership immediately after the repaired C helper.  This is
   intentionally a raw stage rather than a post invariant: the source accepts
   every represented ready owner and overwrites the destination priority-table
   slot.  If that slot belongs to another ready task, the concrete bitmap/table
   writes below remain well defined while the abstract ready-list encoding and
   stable task/scheduler invariants need not close.  The selected TCB fields,
   ready bytes, priority table and conditionally updated OSPrioCur are recorded
   literally;
   all untouched ownership stays indexed by the entry state. *)
Definition OSMutex_RdyAtPrio_raw_stage
  (sg : StableGlobVars) (ls0 : UCOS2_Verify_State)
  (tid : TaskID) (old_t : TaskAbstractState)
  (newPrio newX newY newBitX newBitY rdyGrp : Z)
  (rdyTbl : list Z) (prioTbl : list addr) : Assertion :=
  coq_prop (valid_stable_glob_vars sg) **
  interrupt_inv sg ls0.(IntrState) **
  (verification_slice_tcb_addr sg tid + verification_slice_OSTCBPrio_off) # UChar |-> newPrio **
  (verification_slice_tcb_addr sg tid + verification_slice_OSTCBX_off) # UChar |-> newX **
  (verification_slice_tcb_addr sg tid + verification_slice_OSTCBY_off) # UChar |-> newY **
  (verification_slice_tcb_addr sg tid + verification_slice_OSTCBBitX_off) # UChar |-> newBitX **
  (verification_slice_tcb_addr sg tid + verification_slice_OSTCBBitY_off) # UChar |-> newBitY **
  used_task_rdy_rest sg (verification_slice_tcb_addr sg tid) tid old_t **
  verification_slice_task_inv_no_tid_priotbl sg ls0.(TskState) tid **
  verification_slice_store_priotbl_list sg prioTbl **
  sg.(g_OSRdyGrp) # UChar |-> rdyGrp **
  Ucos2Verify.lib.array_abstraction.store_osrdytbl sg rdyTbl **
  sg.(g_OSPrioCur) # UChar |->
    ready_owner_cur_prio_value_after ls0.(SchedState) tid newPrio **
  verification_slice_sched_inv_rest_ready_prio sg ls0.(TskState) ls0.(SchedState) **
  verification_slice_event_inv sg ls0.(TskState) ls0.(EventState) **
  verification_slice_tick_inv sg ls0.(TickState) **
  coq_prop (verification_slice_cross_module_consistency sg ls0).

(* Closure-stage representation after the literal helper.  It retains every
   spatial module invariant and the exact scheduler stage, but deliberately
   does not assert the cross-module fact that the real source can violate on a
   nested out-of-order restore.  Because raw execution also admits a
   [PTTask other] destination, deriving this stage requires the separate
   [task_priority_relocation_legal] closure condition; the assertion itself is
   not part of the raw execution domain. *)
Definition OSMutex_RdyAtPrio_literal_stage
  (sg : StableGlobVars) (ls0 ls_post : UCOS2_Verify_State) : Assertion :=
  interrupt_inv sg ls_post.(IntrState) **
  verification_slice_task_inv sg ls_post.(TskState) **
  verification_slice_sched_inv_ready_prio_stage
    sg ls0.(SchedState) ls_post.(SchedState) ls_post.(TskState) **
  verification_slice_event_inv sg ls_post.(TskState) ls_post.(EventState) **
  verification_slice_tick_inv sg ls_post.(TickState) **
  TT.

(* Conditional cross-module theorem exposed by the helper contract.  The raw
   helper executes for every priority-table destination entry.  Rebuilding the
   full invariant additionally requires the generic relocation-closure
   condition: in particular, a [PTTask other] destination is rejected, and a
   [PTReserved] destination must be the PCP of a mutex owned by [tid], rather
   than an unrelated reservation that the source write would corrupt.  Both
   antecedents are preservation classifiers, never guards in the total
   execution semantics. *)
Definition OSMutex_RdyAtPrio_conditional_cross
  (sg : StableGlobVars) (ls0 : UCOS2_Verify_State)
  (restore_mid : EventID) (tid : TaskID)
  (old_t : TaskAbstractState) (newPrio : Priority)
  (ls_post : UCOS2_Verify_State) : Prop :=
  ready_owner_relocation_domain
      sg ls0.(TskState) ls0.(SchedState) tid old_t newPrio ->
  task_priority_relocation_legal sg ls0 tid newPrio ->
  mutex_ready_relocation_safe
      sg ls0.(EventState) restore_mid tid old_t.(curPrio) newPrio ->
    verification_slice_cross_module_consistency sg ls_post.

(* Re-associating the literal ready bytes with the abstract post readyList is
   a closure theorem, not part of raw execution.  In particular the premise
   rejects a destination occupied by a different task; without it two logical
   ready owners at one priority need not be represented by the source's single
   destination bit. *)
Definition OSMutex_RdyAtPrio_conditional_ready_snapshot
  (sg : StableGlobVars) (ls0 : UCOS2_Verify_State)
  (tid : TaskID) (old_t : TaskAbstractState) (newPrio : Priority)
  (ls_post : UCOS2_Verify_State)
  (rdyGrp : Z) (rdyTbl : list Z) : Prop :=
  ready_owner_relocation_domain
      sg ls0.(TskState) ls0.(SchedState) tid old_t newPrio ->
  task_priority_relocation_legal sg ls0 tid newPrio ->
    sched_ready_prio_snapshot_prop
      sg ls_post.(TskState) ls_post.(SchedState)
      rdyGrp rdyTbl
      (ready_owner_cur_prio_value_after ls0.(SchedState) tid newPrio).

(* Stable task/scheduler/event validity requires relocation legality, but no
   current-owner premise: the repaired transformer preserves the entry
   current-priority cache on the non-current path. *)
Definition OSMutex_RdyAtPrio_conditional_preservation
  (sg : StableGlobVars) (ls0 : UCOS2_Verify_State)
  (tid : TaskID) (old_t : TaskAbstractState) (newPrio : Priority)
  (ls_post : UCOS2_Verify_State) : Prop :=
  ready_owner_relocation_domain
      sg ls0.(TskState) ls0.(SchedState) tid old_t newPrio ->
  task_priority_relocation_legal sg ls0 tid newPrio ->
    verification_slice_task_validity sg ls_post.(TskState) /\
    verification_slice_sched_in_range sg ls_post.(TskState) ls_post.(SchedState) /\
    verification_slice_event_in_range
      sg ls_post.(TskState) ls_post.(EventState).

(* The shared abstract critical STS currently has an intentionally coarse
   rely relation.  This case-local token therefore records the selected post
   state by equality instead of trying to recover it from [RTrans_Abs]. *)
Definition OSMutex_RdyAtPrio_post_token
  (ls_post : UCOS2_Verify_State) : UCOS2_Verify_State -> Prop :=
  fun observed => observed = ls_post.

Lemma OSMutex_RdyAtPrio_post_token_injective :
  forall ls1 ls2,
    OSMutex_RdyAtPrio_post_token ls1 =
    OSMutex_RdyAtPrio_post_token ls2 ->
    ls1 = ls2.
Proof.
  intros ls1 ls2 Heq.
  assert (Hseen : OSMutex_RdyAtPrio_post_token ls2 ls1).
  {
    rewrite <- Heq.
    unfold OSMutex_RdyAtPrio_post_token.
    reflexivity.
  }
  exact Hseen.
Qed.

Definition OSMutex_RdyAtPrio_LastSeen
  (sg : StableGlobVars) (ptcb : addr) (prio : Priority)
  (ls0 ls_post : UCOS2_Verify_State)
  : (UCOS2_Verify_State -> Prop) -> Prop :=
  fun X =>
    OSMutex_RdyAtPrio_guarantee
      sg ptcb prio ls0 ls_post /\
    X = OSMutex_RdyAtPrio_post_token ls_post.

(* Precise lifting of the public ready-owner L5 operation to the continuation
   state.  The input
   endpoint is the explicit [ls0] parameter, and every output carries both
   the exact ready-owner guarantee and the singleton post-state token.  This
   is a local refinement boundary; a future shared-L6 migration can replace
   the coarse ambient STS without changing the ready relocation semantics. *)
Definition OSMutex_RdyAtPrio_atomic_cmd
  (sg : StableGlobVars) (ls0 : UCOS2_Verify_State)
  (ptcb : addr) (prio : Priority)
  : program (UCOS2_Verify_State -> Prop) unit :=
  fun X1 (_ : unit) X2 =>
    LastSeen ls0 X1 /\
    exists ls_post,
      OSMutex_RdyAtPrio_LastSeen
        sg ptcb prio ls0 ls_post X2.

(* The C function returns void; the observer therefore preserves the
   LastSeen continuation state while exposing the exact atomic transition. *)
Definition observe_unit_void (_ : unit)
  : program (UCOS2_Verify_State -> Prop) unit :=
  fun X1 _ X2 => X2 = X1.

(* A continuation reached through the precise command can be resumed at any
   concrete [ls_post] justified by the same operation guarantee.  In
   particular, the proof does not identify states through the coarse
   [RTrans_Abs]; it transports the operation-specific post token. *)
Lemma OSMutex_RdyAtPrio_safe_return :
  forall sg ls0 ptcb prio ls_post
         (X : unit -> (UCOS2_Verify_State -> Prop) -> Prop),
    OSMutex_RdyAtPrio_guarantee
      sg ptcb prio ls0 ls_post ->
    safeExec (LastSeen ls0)
      (bind (OSMutex_RdyAtPrio_atomic_cmd
               sg ls0 ptcb prio)
            observe_unit_void) X ->
    safeExec
      (OSMutex_RdyAtPrio_LastSeen
         sg ptcb prio ls0 ls_post)
      (@StateRelMonad.ret (UCOS2_Verify_State -> Prop) unit tt) X.
Proof.
  intros sg ls0 ptcb prio ls_post X Hguarantee Hexec.
  assert (Hatomic : hs_eval
    (OSMutex_RdyAtPrio_atomic_cmd sg ls0 ptcb prio)
    (LastSeen ls0)
    (OSMutex_RdyAtPrio_LastSeen
       sg ptcb prio ls0 ls_post) tt).
  {
    unfold hs_eval, OSMutex_RdyAtPrio_atomic_cmd.
    intros X1 HX1.
    exists (OSMutex_RdyAtPrio_post_token ls_post).
    split.
    - split.
      + exact HX1.
      + exists ls_post.
        unfold OSMutex_RdyAtPrio_LastSeen.
        split; [exact Hguarantee | reflexivity].
    - unfold OSMutex_RdyAtPrio_LastSeen.
      split; [exact Hguarantee | reflexivity].
  }
  pose proof (highstepbind_derive
    (OSMutex_RdyAtPrio_atomic_cmd sg ls0 ptcb prio)
    observe_unit_void (LastSeen ls0) tt
    (OSMutex_RdyAtPrio_LastSeen
       sg ptcb prio ls0 ls_post)
    Hatomic X Hexec) as Hobserve.
  eapply (highstependret_derive
    (observe_unit_void tt)
    (OSMutex_RdyAtPrio_LastSeen
       sg ptcb prio ls0 ls_post) tt
    (fun _ => OSMutex_RdyAtPrio_LastSeen
       sg ptcb prio ls0 ls_post)).
  2: exact Hobserve.
  unfold hs_eval, observe_unit_void.
  intros X1 HX1.
  exists X1.
  split; [reflexivity | exact HX1].
Qed.

Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Lemma store_array_missing_index_bounds__array_localization :
  forall (A : Type) (storeA : addr -> Z -> A -> Assertion)
         (x i lo hi : Z) (l : list A),
    store_array_missing_i_rec storeA x i lo hi l |--
      “ lo <= i < hi ”.
Proof.
  intros A storeA x i lo hi l.
  revert i lo hi.
  induction l as [| a l IH]; intros i lo hi; simpl.
  - entailer!.
  - Split; Intros.
    + prop_apply (store_array_rec_Zlength A storeA x (lo + 1) hi l).
      Intros_p Hlen.
      rewrite Zlength_correct in Hlen.
      simpl in Hlen.
      entailer!.
    + prop_apply (IH i (lo + 1) hi).
      entailer!.
Qed.
Lemma verification_slice_prioTbl_to_addrs_rec_seq__relocation_semantics :
  forall sg f n acc,
    verification_slice_prioTbl_to_addrs_rec sg f n acc =
      map (fun k => verification_slice_prio_tbl_entry_to_addr sg (f (Z.of_nat k)))
        (seq 0 n) ++ acc.
Proof.
  intros sg f n. induction n as [|n IH]; intro acc.
  - reflexivity.
  - simpl verification_slice_prioTbl_to_addrs_rec.
    rewrite IH, seq_S, map_app. simpl.
    rewrite <- app_assoc. reflexivity.
Qed.
Lemma OSMutex_RdyAtPrio_task_post_valid__relocation_semantics :
  forall sg st tid old_t newPrio new_t st2,
    st.(inUsedTaskStates) tid = Some old_t ->
    new_t =
      {| taskID := old_t.(taskID);
     taskGeneration := old_t.(taskGeneration);
     tcbStkPtr := old_t.(tcbStkPtr);
     tcbExtPtr := old_t.(tcbExtPtr);
     tcbStkBottom := old_t.(tcbStkBottom);
     tcbStkSize := old_t.(tcbStkSize);
     tcbOpt := old_t.(tcbOpt);
     tcbPublicId := old_t.(tcbPublicId);
     tcbFlagNode := old_t.(tcbFlagNode);
     tcbFlagsRdy := old_t.(tcbFlagsRdy);
     tcbTaskName := old_t.(tcbTaskName);
     tcbReg0 := old_t.(tcbReg0);
     tcbCtxSwCtr := old_t.(tcbCtxSwCtr);
     tcbCyclesTot := old_t.(tcbCyclesTot);
     tcbCyclesStart := old_t.(tcbCyclesStart);
     tcbStkBase := old_t.(tcbStkBase);
     tcbStkUsed := old_t.(tcbStkUsed);
     tcbPadding42 := old_t.(tcbPadding42);
     tcbPadding43 := old_t.(tcbPadding43);
     tcbEventMultiPtr := old_t.(tcbEventMultiPtr);
         curPrio := newPrio;
         stat := old_t.(stat);
         statPend := old_t.(statPend);
         dly := old_t.(dly);
         eventPtr := old_t.(eventPtr);
         eventMultiWaitEvents := old_t.(eventMultiWaitEvents);
         eventMultiRdy := old_t.(eventMultiRdy);
         msg := old_t.(msg);
         nextTCB := old_t.(nextTCB);
         prevTCB := old_t.(prevTCB);
         delReq := old_t.(delReq) |} ->
    st2 =
      {| inUsedTaskStates := fun tid' =>
           if Z.eqb tid' tid then Some new_t else st.(inUsedTaskStates) tid';
         unUsedTaskStates := st.(unUsedTaskStates);
         tcbListHead := st.(tcbListHead);
         prioTbl := fun p =>
           if Z.eqb p newPrio then PTTask tid else st.(prioTbl) p;
         taskRegNextID := st.(taskRegNextID);
         parkedTaskStacks := st.(parkedTaskStacks);
         taskLifecycle := st.(taskLifecycle);
     taskCount := st.(taskCount) |} ->
    valid_stable_glob_vars sg ->
    verification_slice_task_validity sg st ->
    verification_slice_priority_index sg newPrio ->
    (forall tid' t',
        st.(inUsedTaskStates) tid' = Some t' ->
        t'.(curPrio) = newPrio ->
        tid' = tid) ->
    verification_slice_task_validity sg st2.
Proof.
  intros sg st tid old_t newPrio new_t st2
    Hget Hnew Hst2 Hsg Hvalid HnewPrio Hunique_new.
  subst st2.
  destruct Hvalid as [Hrange Hderived].
  unfold verification_slice_task_in_range in Hrange.
  destruct Hrange as
    [Hids [Hfree_nodup [Hfree_range
      [Hfree_unused [Hprio [Hregistered Hunique]]]]]].
  assert (Hunique_post :
    task_priority_unique
      {| inUsedTaskStates := fun tid' =>
           if Z.eqb tid' tid then Some new_t else st.(inUsedTaskStates) tid';
         unUsedTaskStates := st.(unUsedTaskStates);
         tcbListHead := st.(tcbListHead);
         prioTbl := fun p =>
           if Z.eqb p newPrio then PTTask tid else st.(prioTbl) p;
         taskRegNextID := st.(taskRegNextID);
         parkedTaskStacks := st.(parkedTaskStacks);
         taskLifecycle := st.(taskLifecycle);
     taskCount := st.(taskCount) |}).
  {
    unfold task_priority_unique. cbn.
    intros tid1 tid2 t1 t2 Hget1 Hget2 Hprio_eq.
    destruct (Z.eqb tid1 tid) eqn:Heq1;
      destruct (Z.eqb tid2 tid) eqn:Heq2.
    - apply Z.eqb_eq in Heq1, Heq2. congruence.
    - apply Z.eqb_eq in Heq1. subst tid1.
      inversion Hget1; subst t1.
      rewrite Hnew in Hprio_eq. cbn in Hprio_eq.
      assert (tid2 = tid).
      { eapply Hunique_new; [exact Hget2 | symmetry; exact Hprio_eq]. }
      subst tid2. rewrite Z.eqb_refl in Heq2. discriminate.
    - apply Z.eqb_eq in Heq2. subst tid2.
      inversion Hget2; subst t2.
      rewrite Hnew in Hprio_eq. cbn in Hprio_eq.
      assert (tid1 = tid).
      { eapply Hunique_new; [exact Hget1 | exact Hprio_eq]. }
      subst tid1. rewrite Z.eqb_refl in Heq1. discriminate.
    - eapply Hunique; eassumption.
  }
  split.
  - unfold verification_slice_task_in_range, verification_slice_task_in_range.
    cbn.
    split.
    + intros tid0 t0 Hget0.
      destruct (Z.eqb tid0 tid) eqn:Heq.
      * apply Z.eqb_eq in Heq. subst tid0.
        inversion Hget0; subst t0.
        exact (Hids tid old_t Hget).
      * exact (Hids tid0 t0 Hget0).
    + split; [exact Hfree_nodup |].
      split; [exact Hfree_range |].
      split.
      * intros tid0 Hin.
        destruct (Z.eqb tid0 tid) eqn:Heq.
        -- apply Z.eqb_eq in Heq. subst tid0.
           specialize (Hfree_unused tid Hin).
           rewrite Hget in Hfree_unused. discriminate.
        -- exact (Hfree_unused tid0 Hin).
      * split.
        -- intros p tid0 Hpt.
           destruct (Z.eqb p newPrio) eqn:Heq_p.
           ++ apply Z.eqb_eq in Heq_p. subst p.
              inversion Hpt; subst tid0.
              split; [exact HnewPrio |].
              eexists. cbn. rewrite Z.eqb_refl. reflexivity.
           ++ destruct (Hprio p tid0 Hpt) as [Hp [t0 Hget0]].
              split; [exact Hp |].
              destruct (Z.eqb tid0 tid) eqn:Heq_tid.
              ** apply Z.eqb_eq in Heq_tid. subst tid0.
                 rewrite Hget in Hget0. inversion Hget0; subst t0.
                 eexists. cbn. reflexivity.
              ** exists t0. cbn. exact Hget0.
        -- split.
           ++ eapply task_current_prio_registered_preserved_by_priority_update
                with (st1 := st) (tid := tid) (t_new := new_t).
              ** exact Hregistered.
              ** exact Hunique_post.
              ** cbn. rewrite Z.eqb_refl. reflexivity.
              ** intros tid' Hne. cbn.
                 rewrite (proj2 (Z.eqb_neq tid' tid) Hne). reflexivity.
              ** intros p Hne. cbn.
                 rewrite Hnew in Hne. cbn in Hne.
                 rewrite (proj2 (Z.eqb_neq p newPrio) Hne). reflexivity.
              ** cbn. rewrite Hnew. cbn. rewrite Z.eqb_refl. reflexivity.
           ++ exact Hunique_post.
  - intros tid0 t0 Hget0.
    cbn in Hget0.
    destruct (Z.eqb tid0 tid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst tid0.
      inversion Hget0; subst t0. rewrite Hnew. cbn.
      split; [exact HnewPrio |].
      unfold valid_derived_fields.
      unfold verification_slice_priority_index in HnewPrio.
      unfold valid_stable_glob_vars in Hsg.
      destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]].
      rewrite Hlowest in HnewPrio.
      pose proof (Z.mod_pos_bound newPrio 8 ltac:(lia)) as Hmod.
      assert (Hdivlo : 0 <= newPrio / 8) by (apply Z.div_pos; lia).
      assert (Hdivhi : newPrio / 8 < 8) by
        (apply Z.div_lt_upper_bound; lia).
      exact (conj (proj1 Hmod)
        (conj (proj2 Hmod) (conj Hdivlo Hdivhi))).
    + exact (Hderived tid0 t0 Hget0).
Qed.
Lemma strictly_sorted_by_key_ext_in__relocation_semantics :
  forall (A : Type) (key1 key2 : A -> Z) (l : list A),
    (forall x, In x l -> key1 x = key2 x) ->
    Ucos2Verify.lib.helpers.strictly_sorted_by key1 l ->
    Ucos2Verify.lib.helpers.strictly_sorted_by key2 l.
Proof.
  intros A key1 key2 l.
  induction l as [|a rest IH]; intros Hkey Hsorted.
  - exact I.
  - destruct rest as [|b rest'].
    + exact I.
    + simpl in Hsorted |- *.
      destruct Hsorted as [Hab Hrest].
      split.
      * rewrite <- (Hkey a ltac:(left; reflexivity)).
        rewrite <- (Hkey b ltac:(right; left; reflexivity)).
        exact Hab.
      * apply IH.
        -- intros x Hin. apply Hkey. right. exact Hin.
        -- exact Hrest.
Qed.
Lemma OSMutex_RdyAtPrio_sched_post_valid__relocation_semantics :
  forall sg st ss tid old_t newPrio
         (new_t : TaskAbstractState)
         (st2 : Glob_TaskAbstractState)
         (ss2 : SchedAbstractState),
    st.(inUsedTaskStates) tid = Some old_t ->
    In tid ss.(readyList) ->
    verification_slice_sched_in_range sg st ss ->
    (forall tid' t',
        st.(inUsedTaskStates) tid' = Some t' ->
        t'.(curPrio) = newPrio ->
        tid' = tid) ->
    new_t =
      {| taskID := old_t.(taskID);
     taskGeneration := old_t.(taskGeneration);
     tcbStkPtr := old_t.(tcbStkPtr);
     tcbExtPtr := old_t.(tcbExtPtr);
     tcbStkBottom := old_t.(tcbStkBottom);
     tcbStkSize := old_t.(tcbStkSize);
     tcbOpt := old_t.(tcbOpt);
     tcbPublicId := old_t.(tcbPublicId);
     tcbFlagNode := old_t.(tcbFlagNode);
     tcbFlagsRdy := old_t.(tcbFlagsRdy);
     tcbTaskName := old_t.(tcbTaskName);
     tcbReg0 := old_t.(tcbReg0);
     tcbCtxSwCtr := old_t.(tcbCtxSwCtr);
     tcbCyclesTot := old_t.(tcbCyclesTot);
     tcbCyclesStart := old_t.(tcbCyclesStart);
     tcbStkBase := old_t.(tcbStkBase);
     tcbStkUsed := old_t.(tcbStkUsed);
     tcbPadding42 := old_t.(tcbPadding42);
     tcbPadding43 := old_t.(tcbPadding43);
     tcbEventMultiPtr := old_t.(tcbEventMultiPtr);
         curPrio := newPrio;
         stat := old_t.(stat);
         statPend := old_t.(statPend);
         dly := old_t.(dly);
         eventPtr := old_t.(eventPtr);
         eventMultiWaitEvents := old_t.(eventMultiWaitEvents);
         eventMultiRdy := old_t.(eventMultiRdy);
         msg := old_t.(msg);
         nextTCB := old_t.(nextTCB);
         prevTCB := old_t.(prevTCB);
         delReq := old_t.(delReq) |} ->
    st2 =
      {| inUsedTaskStates := fun tid' =>
           if Z.eqb tid' tid then Some new_t else st.(inUsedTaskStates) tid';
         unUsedTaskStates := st.(unUsedTaskStates);
         tcbListHead := st.(tcbListHead);
         prioTbl := fun p =>
           if Z.eqb p newPrio then PTTask tid else st.(prioTbl) p;
         taskRegNextID := st.(taskRegNextID);
         parkedTaskStacks := st.(parkedTaskStacks);
         taskLifecycle := st.(taskLifecycle);
     taskCount := st.(taskCount) |} ->
    ss2 =
      (
      let newReadyList :=
        Ucos2Verify.lib.helpers.insert_sorted_by
          (fun tid' =>
             match st2.(inUsedTaskStates) tid' with
             | Some t => t.(curPrio)
             | None => sg.(osLowestPrio) + 1
             end)
          tid (Ucos2Verify.lib.helpers.remove_Z_eqb tid ss.(readyList)) in
      {| readyList := newReadyList;
         curTaskID := ss.(curTaskID);
         curSchedPrio :=
           match ss.(curTaskID) with
           | Some tid' =>
               if Z.eqb tid' tid then Some newPrio else ss.(curSchedPrio)
           | None => ss.(curSchedPrio)
           end;
         highRdyTid :=
           match newReadyList with
           | h :: _ => Some h
           | nil => None
           end;
         highRdyPrio :=
           match newReadyList with
           | h :: _ =>
               match st2.(inUsedTaskStates) h with
               | Some t => Some t.(curPrio)
               | None => None
               end
           | nil => None
           end;
         ctxSwCtr := ss.(ctxSwCtr);
         isRunning := ss.(isRunning) |}) ->
    verification_slice_sched_in_range sg st2 ss2.
Proof.
  intros sg st ss tid old_t newPrio new_t st2 ss2
    Hget Hin Hsched Hunique Hnew Hst2 Hss2.
  subst new_t st2 ss2.
  destruct Hsched as
    [Hall [Hsorted [Hcomplete [Hnodup [Hctx [Hhigh Hcurrent]]]]]].
  pose proof (Hall tid Hin) as [old_t' [Hget' Heffective]].
  rewrite Hget in Hget'. inversion Hget'; subst old_t'.
  set (key_old := fun tid' : TaskID =>
    match st.(inUsedTaskStates) tid' with
    | Some t => t.(curPrio)
    | None => sg.(osLowestPrio) + 1
    end).
  set (key_new := fun tid' : TaskID =>
    match
      (fun tid0 =>
         if Z.eqb tid0 tid then
           Some
             {| taskID := old_t.(taskID);
     taskGeneration := old_t.(taskGeneration);
     tcbStkPtr := old_t.(tcbStkPtr);
     tcbExtPtr := old_t.(tcbExtPtr);
     tcbStkBottom := old_t.(tcbStkBottom);
     tcbStkSize := old_t.(tcbStkSize);
     tcbOpt := old_t.(tcbOpt);
     tcbPublicId := old_t.(tcbPublicId);
     tcbFlagNode := old_t.(tcbFlagNode);
     tcbFlagsRdy := old_t.(tcbFlagsRdy);
     tcbTaskName := old_t.(tcbTaskName);
     tcbReg0 := old_t.(tcbReg0);
     tcbCtxSwCtr := old_t.(tcbCtxSwCtr);
     tcbCyclesTot := old_t.(tcbCyclesTot);
     tcbCyclesStart := old_t.(tcbCyclesStart);
     tcbStkBase := old_t.(tcbStkBase);
     tcbStkUsed := old_t.(tcbStkUsed);
     tcbPadding42 := old_t.(tcbPadding42);
     tcbPadding43 := old_t.(tcbPadding43);
     tcbEventMultiPtr := old_t.(tcbEventMultiPtr); curPrio := newPrio;
                stat := old_t.(stat); statPend := old_t.(statPend);
                dly := old_t.(dly); eventPtr := old_t.(eventPtr);
                eventMultiWaitEvents := old_t.(eventMultiWaitEvents);
                eventMultiRdy := old_t.(eventMultiRdy);
                msg := old_t.(msg); nextTCB := old_t.(nextTCB);
                prevTCB := old_t.(prevTCB); delReq := old_t.(delReq) |}
         else st.(inUsedTaskStates) tid0) tid'
    with
    | Some t => t.(curPrio)
    | None => sg.(osLowestPrio) + 1
    end).
  set (rest := Ucos2Verify.lib.helpers.remove_Z_eqb tid ss.(readyList)).
  set (newReadyList := Ucos2Verify.lib.helpers.insert_sorted_by key_new tid rest).
  assert (Hrest_no_tid : ~ In tid rest).
  { subst rest. apply Ucos2Verify.lib.helpers.remove_Z_eqb_notin. }
  assert (Hrest_in : forall x, In x rest -> In x ss.(readyList)).
  { intros x Hx. subst rest. eapply Ucos2Verify.lib.helpers.remove_Z_eqb_in; eauto. }
  assert (Hkey_rest : forall x, In x rest -> key_old x = key_new x).
  {
    intros x Hx.
    assert (Hne : x <> tid).
    { intro; subst x. exact (Hrest_no_tid Hx). }
    unfold key_old, key_new.
    destruct (Z.eqb x tid) eqn:Heq.
    - apply Z.eqb_eq in Heq. contradiction.
    - reflexivity.
  }
  assert (Hrest_sorted_old : Ucos2Verify.lib.helpers.strictly_sorted_by key_old rest).
  { subst rest key_old. apply Ucos2Verify.lib.helpers.remove_Z_eqb_strictly_sorted_by. exact Hsorted. }
  assert (Hrest_sorted_new : Ucos2Verify.lib.helpers.strictly_sorted_by key_new rest).
  { eapply strictly_sorted_by_key_ext_in__relocation_semantics;
      [exact Hkey_rest | exact Hrest_sorted_old]. }
  assert (Hkey_tid : key_new tid = newPrio).
  { unfold key_new. rewrite Z.eqb_refl. reflexivity. }
  assert (Hkey_unique : forall x, In x rest -> key_new x <> key_new tid).
  {
    intros x Hx Heqkey.
    assert (Hne : x <> tid).
    { intro; subst x. exact (Hrest_no_tid Hx). }
    pose proof (Hall x (Hrest_in x Hx)) as [tx [Hgetx _]].
    unfold key_new in Heqkey.
    rewrite Z.eqb_refl in Heqkey.
    assert (Hex : Z.eqb x tid = false) by
      (apply Z.eqb_neq; exact Hne).
    rewrite Hex in Heqkey.
    rewrite Hgetx in Heqkey.
    exact (Hne (Hunique x tx Hgetx Heqkey)).
  }
  assert (Hnew_sorted : Ucos2Verify.lib.helpers.strictly_sorted_by key_new newReadyList).
  {
    subst newReadyList.
    apply Ucos2Verify.lib.helpers.insert_sorted_by_preserves; assumption.
  }
  assert (Hnew_nodup : NoDup newReadyList).
  {
    subst newReadyList rest.
    apply Ucos2Verify.lib.helpers.insert_sorted_by_preserves_NoDup.
    - apply Ucos2Verify.lib.helpers.remove_Z_eqb_NoDup. exact Hnodup.
    - apply Ucos2Verify.lib.helpers.remove_Z_eqb_notin.
  }
  assert (Hnew_has_tid : In tid newReadyList).
  { subst newReadyList. apply Ucos2Verify.lib.helpers.insert_sorted_by_in. left. reflexivity. }
  assert (Hall_new : forall x, In x newReadyList ->
      exists tx,
        (if Z.eqb x tid then
           Some
             {| taskID := old_t.(taskID);
     taskGeneration := old_t.(taskGeneration);
     tcbStkPtr := old_t.(tcbStkPtr);
     tcbExtPtr := old_t.(tcbExtPtr);
     tcbStkBottom := old_t.(tcbStkBottom);
     tcbStkSize := old_t.(tcbStkSize);
     tcbOpt := old_t.(tcbOpt);
     tcbPublicId := old_t.(tcbPublicId);
     tcbFlagNode := old_t.(tcbFlagNode);
     tcbFlagsRdy := old_t.(tcbFlagsRdy);
     tcbTaskName := old_t.(tcbTaskName);
     tcbReg0 := old_t.(tcbReg0);
     tcbCtxSwCtr := old_t.(tcbCtxSwCtr);
     tcbCyclesTot := old_t.(tcbCyclesTot);
     tcbCyclesStart := old_t.(tcbCyclesStart);
     tcbStkBase := old_t.(tcbStkBase);
     tcbStkUsed := old_t.(tcbStkUsed);
     tcbPadding42 := old_t.(tcbPadding42);
     tcbPadding43 := old_t.(tcbPadding43);
     tcbEventMultiPtr := old_t.(tcbEventMultiPtr); curPrio := newPrio;
                stat := old_t.(stat); statPend := old_t.(statPend);
                dly := old_t.(dly); eventPtr := old_t.(eventPtr);
                eventMultiWaitEvents := old_t.(eventMultiWaitEvents);
                eventMultiRdy := old_t.(eventMultiRdy);
                msg := old_t.(msg); nextTCB := old_t.(nextTCB);
                prevTCB := old_t.(prevTCB); delReq := old_t.(delReq) |}
         else st.(inUsedTaskStates) x) = Some tx /\
        is_effectively_ready tx.(stat) tx.(dly) = true).
  {
    intros x Hx.
    apply Ucos2Verify.lib.helpers.insert_sorted_by_in in Hx.
    destruct Hx as [-> | Hx].
    - eexists. rewrite Z.eqb_refl. split; [reflexivity | exact Heffective].
    - assert (Hne : x <> tid).
      { intro; subst x. exact (Hrest_no_tid Hx). }
      destruct (Hall x (Hrest_in x Hx)) as [tx [Hmap Hready]].
      exists tx. rewrite (proj2 (Z.eqb_neq x tid) Hne). auto.
  }
  assert (Hcomplete_new : forall x tx,
      (if Z.eqb x tid then
         Some
           {| taskID := old_t.(taskID);
     taskGeneration := old_t.(taskGeneration);
     tcbStkPtr := old_t.(tcbStkPtr);
     tcbExtPtr := old_t.(tcbExtPtr);
     tcbStkBottom := old_t.(tcbStkBottom);
     tcbStkSize := old_t.(tcbStkSize);
     tcbOpt := old_t.(tcbOpt);
     tcbPublicId := old_t.(tcbPublicId);
     tcbFlagNode := old_t.(tcbFlagNode);
     tcbFlagsRdy := old_t.(tcbFlagsRdy);
     tcbTaskName := old_t.(tcbTaskName);
     tcbReg0 := old_t.(tcbReg0);
     tcbCtxSwCtr := old_t.(tcbCtxSwCtr);
     tcbCyclesTot := old_t.(tcbCyclesTot);
     tcbCyclesStart := old_t.(tcbCyclesStart);
     tcbStkBase := old_t.(tcbStkBase);
     tcbStkUsed := old_t.(tcbStkUsed);
     tcbPadding42 := old_t.(tcbPadding42);
     tcbPadding43 := old_t.(tcbPadding43);
     tcbEventMultiPtr := old_t.(tcbEventMultiPtr); curPrio := newPrio;
              stat := old_t.(stat); statPend := old_t.(statPend);
              dly := old_t.(dly); eventPtr := old_t.(eventPtr);
              eventMultiWaitEvents := old_t.(eventMultiWaitEvents);
              eventMultiRdy := old_t.(eventMultiRdy);
              msg := old_t.(msg); nextTCB := old_t.(nextTCB);
              prevTCB := old_t.(prevTCB); delReq := old_t.(delReq) |}
       else st.(inUsedTaskStates) x) = Some tx ->
      is_effectively_ready tx.(stat) tx.(dly) = true ->
      In x newReadyList).
  {
    intros x tx Hmap Hready.
    destruct (Z.eqb x tid) eqn:Hex.
    - apply Z.eqb_eq in Hex. subst x. exact Hnew_has_tid.
    - apply Ucos2Verify.lib.helpers.insert_sorted_by_in. right.
      subst rest.
      apply Ucos2Verify.lib.helpers.remove_Z_eqb_in_neq.
      + apply Z.eqb_neq in Hex. exact Hex.
      + apply (Hcomplete x tx); assumption.
  }
  unfold verification_slice_sched_in_range.
  cbn.
  split; [exact Hall_new |].
  split; [exact Hnew_sorted |].
  split; [exact Hcomplete_new |].
  split; [exact Hnew_nodup |].
  split; [exact Hctx |].
  split.
  - unfold sched_high_ready_consistency. cbn.
    lazymatch goal with
    | |- context [match ?rl with | nil => _ | _ :: _ => _ end] =>
        remember rl as rl' eqn:Hrl
    end.
    assert (Hrl_has_tid : In tid rl').
    { rewrite Hrl. exact Hnew_has_tid. }
    assert (Hall_rl : forall x, In x rl' ->
        exists tx,
          (if Z.eqb x tid then
             Some
               {| taskID := old_t.(taskID);
     taskGeneration := old_t.(taskGeneration);
     tcbStkPtr := old_t.(tcbStkPtr);
     tcbExtPtr := old_t.(tcbExtPtr);
     tcbStkBottom := old_t.(tcbStkBottom);
     tcbStkSize := old_t.(tcbStkSize);
     tcbOpt := old_t.(tcbOpt);
     tcbPublicId := old_t.(tcbPublicId);
     tcbFlagNode := old_t.(tcbFlagNode);
     tcbFlagsRdy := old_t.(tcbFlagsRdy);
     tcbTaskName := old_t.(tcbTaskName);
     tcbReg0 := old_t.(tcbReg0);
     tcbCtxSwCtr := old_t.(tcbCtxSwCtr);
     tcbCyclesTot := old_t.(tcbCyclesTot);
     tcbCyclesStart := old_t.(tcbCyclesStart);
     tcbStkBase := old_t.(tcbStkBase);
     tcbStkUsed := old_t.(tcbStkUsed);
     tcbPadding42 := old_t.(tcbPadding42);
     tcbPadding43 := old_t.(tcbPadding43);
     tcbEventMultiPtr := old_t.(tcbEventMultiPtr); curPrio := newPrio;
                  stat := old_t.(stat); statPend := old_t.(statPend);
                  dly := old_t.(dly); eventPtr := old_t.(eventPtr);
                  eventMultiWaitEvents := old_t.(eventMultiWaitEvents);
                  eventMultiRdy := old_t.(eventMultiRdy);
                  msg := old_t.(msg); nextTCB := old_t.(nextTCB);
                  prevTCB := old_t.(prevTCB); delReq := old_t.(delReq) |}
           else st.(inUsedTaskStates) x) = Some tx /\
          is_effectively_ready tx.(stat) tx.(dly) = true).
    {
      intros x Hx. apply Hall_new.
      rewrite Hrl in Hx. exact Hx.
    }
    destruct rl' as [|h tail]; cbn.
    + contradiction.
    + destruct (Hall_rl h ltac:(left; reflexivity))
        as [tx [Hmap _]].
      split; [reflexivity |].
      exists tx. split; [exact Hmap |].
      rewrite Hmap. reflexivity.
  - unfold sched_current_consistency in Hcurrent |- *.
    cbn.
    destruct (curTaskID ss) as [current_tid |] eqn:Hcurrent_tid.
    + destruct Hcurrent as (current_t & Hcurrent_get & Hcurrent_prio).
      destruct (Z.eqb current_tid tid) eqn:Hsame.
      * apply Z.eqb_eq in Hsame. subst current_tid.
        rewrite Hget in Hcurrent_get. inversion Hcurrent_get; subst current_t.
        eexists. split.
        -- reflexivity.
        -- reflexivity.
      * exists current_t. split.
        -- exact Hcurrent_get.
        -- exact Hcurrent_prio.
    + exact Hcurrent.
Qed.


(* Group-local proved bitmap and relocation helpers.  Every declaration added
   below is namespaced by the controller-assigned group suffix. *)
Lemma debug_fold_add_as_sum__relocation_semantics : forall (A : Type) (f : A -> Z) l acc,
  fold_left (fun z x => z + f x) l acc =
  acc + fold_right (fun x z => f x + z) 0 l.
Proof.
  intros A f l. induction l as [|a rest IH]; intro acc; simpl.
  - lia.
  - rewrite IH. simpl. lia.
Qed.
Lemma debug_land_single_bits_neq__relocation_semantics : forall i j,
  0 <= i -> 0 <= j -> i <> j ->
  Z.land (Z.shiftl 1 i) (Z.shiftl 1 j) = 0.
Proof.
  intros i j Hi Hj Hneq.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, !Z.shiftl_1_l,
    !Z.pow2_bits_eqb by assumption.
  rewrite Z.testbit_0_l.
  destruct (i =? n) eqn:Hin; destruct (j =? n) eqn:Hjn;
    try reflexivity.
  apply Z.eqb_eq in Hin, Hjn. congruence.
Qed.
Lemma debug_same_div_mod_priority__relocation_semantics : forall p q,
  0 <= p -> 0 <= q ->
  p / 8 = q / 8 -> p mod 8 = q mod 8 -> p = q.
Proof.
  intros p q Hp Hq Hdiv Hmod.
  pose proof (Z.div_mod p 8 ltac:(lia)) as Hpdm.
  pose proof (Z.div_mod q 8 ltac:(lia)) as Hqdm.
  lia.
Qed.
Lemma debug_bit_disjoint_tbl_lor__relocation_semantics :
  forall l st y p,
    0 <= p ->
    p / 8 = y ->
    (forall tid t, In tid l -> st.(inUsedTaskStates) tid = Some t ->
       0 <= t.(curPrio)) ->
    (forall tid t, In tid l -> st.(inUsedTaskStates) tid = Some t ->
       t.(curPrio) <> p) ->
    Z.land (Z.shiftl 1 (p mod 8))
      (fold_right
        (fun tid acc =>
           match st.(inUsedTaskStates) tid with
           | Some t =>
               if Z.eqb (t.(curPrio) / 8) y
               then Z.lor (Z.shiftl 1 (t.(curPrio) mod 8)) acc
               else acc
           | None => acc
           end) 0 l) = 0.
Proof.
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
        apply debug_land_single_bits_neq__relocation_semantics.
        -- apply Z.mod_pos_bound. lia.
        -- apply Z.mod_pos_bound. lia.
        -- intro Hmods.
           apply (Hneq a ta ltac:(left; reflexivity) Hgeta).
           apply debug_same_div_mod_priority__relocation_semantics; try eapply Hrange;
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
Lemma debug_encode_tbl_as_lor__relocation_semantics :
  forall l st y,
    NoDup l ->
    task_priority_unique st ->
    (forall tid t, In tid l -> st.(inUsedTaskStates) tid = Some t ->
       0 <= t.(curPrio)) ->
    encode_ready_tbl_at l st y =
      fold_right
        (fun tid acc =>
           match st.(inUsedTaskStates) tid with
           | Some t =>
               if Z.eqb (t.(curPrio) / 8) y
               then Z.lor (Z.shiftl 1 (t.(curPrio) mod 8)) acc
               else acc
           | None => acc
           end) 0 l.
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
    intros l0 acc. apply Ucos2Verify.lib.sched.fold_left_ext.
    intros z tid. unfold f.
    destruct (st.(inUsedTaskStates) tid);
      [destruct (Z.eqb (curPrio t / 8) y)|]; lia.
  }
  rewrite Hconv, debug_fold_add_as_sum__relocation_semantics. simpl.
  clear Hconv.
  induction l as [|a rest IH]; simpl; [reflexivity|].
  inversion Hnd as [|? ? Hnotin Hndrest]; subst.
  destruct (st.(inUsedTaskStates) a) as [ta|] eqn:Hgeta.
  - destruct (Z.eqb (ta.(curPrio) / 8) y) eqn:Hrow.
    + rewrite IH.
      2: exact Hndrest.
      2: { intros; eapply Hrange; [right; eassumption | eassumption]. }
      unfold f. rewrite Hgeta, Hrow.
      pose proof (debug_bit_disjoint_tbl_lor__relocation_semantics rest st y ta.(curPrio))
        as Hdisj.
      specialize (Hdisj ltac:(eapply Hrange; [left; reflexivity | exact Hgeta])).
      specialize (Hdisj ltac:(apply Z.eqb_eq in Hrow; exact Hrow)).
      specialize (Hdisj
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
      pose proof (Z.add_lor_land
        (Z.shiftl 1 (ta.(curPrio) mod 8))
        (fold_right
          (fun tid acc =>
             match st.(inUsedTaskStates) tid with
             | Some t =>
                 if Z.eqb (t.(curPrio) / 8) y
                 then Z.lor (Z.shiftl 1 (t.(curPrio) mod 8)) acc
                 else acc
             | None => acc
             end) 0 rest)) as Hadd.
      rewrite Hdisj, Z.add_0_r in Hadd.
      lia.
    + rewrite IH.
      2: exact Hndrest.
      2: { intros; eapply Hrange; [right; eassumption | eassumption]. }
      unfold f. rewrite Hgeta, Hrow. lia.
  - rewrite IH.
    2: exact Hndrest.
    2: { intros; eapply Hrange; [right; eassumption | eassumption]. }
    unfold f. rewrite Hgeta. lia.
Qed.
Lemma debug_remove_perm_cons__relocation_semantics : forall x l,
  In x l -> NoDup l ->
  Permutation l (x :: Ucos2Verify.lib.helpers.remove_Z_eqb x l).
Proof.
  intros x l Hin Hnd.
  induction l as [|a rest IH]; [contradiction|].
  inversion Hnd as [|? ? Hnotin Hndrest]; subst.
  simpl in Hin. destruct Hin as [->|Hin].
  - simpl. rewrite Z.eqb_refl.
    rewrite Ucos2Verify.lib.helpers.remove_Z_eqb_notin_eq by exact Hnotin.
    reflexivity.
  - simpl. destruct (Z.eqb a x) eqn:Hax.
    + apply Z.eqb_eq in Hax. subst a. contradiction.
    + eapply Permutation_trans.
      * apply perm_skip. apply IH; assumption.
      * apply perm_swap.
Qed.
Lemma debug_encode_grp_perm__relocation_semantics : forall l1 l2 st,
  Permutation l1 l2 -> encode_ready_grp l1 st = encode_ready_grp l2 st.
Proof.
  intros l1 l2 st Hp. induction Hp.
  - reflexivity.
  - simpl. destruct (inUsedTaskStates st x); simpl; now rewrite IHHp.
  - simpl.
    destruct (inUsedTaskStates st x); destruct (inUsedTaskStates st y); simpl;
      try reflexivity; rewrite Z.lor_assoc,
        (Z.lor_comm _ (Z.shiftl 1 (curPrio t / 8))),
        <- Z.lor_assoc; reflexivity.
  - etransitivity; eauto.
Qed.
Lemma debug_encode_tbl_perm__relocation_semantics : forall l1 l2 st y,
  Permutation l1 l2 ->
  encode_ready_tbl_at l1 st y = encode_ready_tbl_at l2 st y.
Proof.
  intros l1 l2 st y Hp.
  unfold encode_ready_tbl_at.
  set (f := fun tid =>
    match inUsedTaskStates st tid with
    | Some t => if Z.eqb (curPrio t / 8) y
                then Z.shiftl 1 (curPrio t mod 8) else 0
    | None => 0
    end).
  assert (Hconv : forall l acc,
    fold_left (fun acc tid =>
      match inUsedTaskStates st tid with
      | Some t => if Z.eqb (curPrio t / 8) y
                  then acc + Z.shiftl 1 (curPrio t mod 8) else acc
      | None => acc
      end) l acc =
    fold_left (fun z tid => z + f tid) l acc).
  {
    intros l acc. apply Ucos2Verify.lib.sched.fold_left_ext.
    intros z tid. unfold f.
    destruct (inUsedTaskStates st tid);
      [destruct (Z.eqb (curPrio t / 8) y)|]; lia.
  }
  rewrite !Hconv, !debug_fold_add_as_sum__relocation_semantics.
  f_equal.
  induction Hp; simpl; lia.
Qed.
Lemma debug_encode_grp_ext_in__relocation_semantics : forall l st1 st2,
  (forall tid, In tid l ->
    inUsedTaskStates st1 tid = inUsedTaskStates st2 tid) ->
  encode_ready_grp l st1 = encode_ready_grp l st2.
Proof.
  induction l as [|a rest IH]; intros st1 st2 Heq; simpl; [reflexivity|].
  rewrite (Heq a ltac:(left; reflexivity)).
  destruct (inUsedTaskStates st2 a); simpl.
  - f_equal. apply IH. intros; apply Heq; right; assumption.
  - apply IH. intros; apply Heq; right; assumption.
Qed.
Lemma debug_encode_tbl_ext_in__relocation_semantics : forall l st1 st2 y,
  (forall tid, In tid l ->
    inUsedTaskStates st1 tid = inUsedTaskStates st2 tid) ->
  encode_ready_tbl_at l st1 y = encode_ready_tbl_at l st2 y.
Proof.
  intros l st1 st2 y Heq.
  unfold encode_ready_tbl_at.
  generalize 0 as acc. induction l as [|a rest IH]; intro acc; simpl;
    [reflexivity|].
  rewrite (Heq a ltac:(left; reflexivity)).
  apply IH. intros; apply Heq; right; assumption.
Qed.
Lemma debug_shiftl_bit_byte__relocation_semantics : forall i,
  0 <= i < 8 -> 0 <= Z.shiftl 1 i < 2 ^ 8.
Proof.
  intros i Hi. rewrite Z.shiftl_1_l.
  assert (Hi_cases : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/
          i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct Hi_cases as [Heq|Hi_cases]; [subst i; cbn; lia|].
  destruct Hi_cases as [Heq|Hi_cases]; [subst i; cbn; lia|].
  destruct Hi_cases as [Heq|Hi_cases]; [subst i; cbn; lia|].
  destruct Hi_cases as [Heq|Hi_cases]; [subst i; cbn; lia|].
  destruct Hi_cases as [Heq|Hi_cases]; [subst i; cbn; lia|].
  destruct Hi_cases as [Heq|Hi_cases]; [subst i; cbn; lia|].
  destruct Hi_cases as [Heq|Heq]; subst i; cbn; lia.
Qed.
Lemma debug_lor_byte__relocation_semantics : forall a b,
  0 <= a < 2 ^ 8 -> 0 <= b < 2 ^ 8 ->
  0 <= Z.lor a b < 2 ^ 8.
Proof.
  intros a b Ha Hb.
  pose proof (unsigned_Lastnbits_range (Z.lor a b) 8 ltac:(lia)) as Hr.
  rewrite unsigned_last_nbits_lor_distr_missing in Hr; lia.
Qed.
Lemma debug_tbl_lor_byte__relocation_semantics : forall l st y,
  0 <=
    fold_right
      (fun tid acc =>
         match st.(inUsedTaskStates) tid with
         | Some t =>
             if Z.eqb (t.(curPrio) / 8) y
             then Z.lor (Z.shiftl 1 (t.(curPrio) mod 8)) acc
             else acc
         | None => acc
         end) 0 l < 2 ^ 8.
Proof.
  induction l as [|a rest IH]; intros st y; simpl; [lia|].
  destruct (st.(inUsedTaskStates) a) as [ta|]; [|apply IH].
  destruct (Z.eqb (ta.(curPrio) / 8) y); [|apply IH].
  apply debug_lor_byte__relocation_semantics; [|apply IH].
  apply debug_shiftl_bit_byte__relocation_semantics. apply Z.mod_pos_bound. lia.
Qed.
Lemma debug_encode_tbl_byte__relocation_semantics : forall l st y,
  NoDup l -> task_priority_unique st ->
  (forall tid t, In tid l -> st.(inUsedTaskStates) tid = Some t ->
     0 <= t.(curPrio)) ->
  0 <= encode_ready_tbl_at l st y < 2 ^ 8.
Proof.
  intros l st y Hnd Huniq Hrange.
  rewrite debug_encode_tbl_as_lor__relocation_semantics by assumption.
  apply debug_tbl_lor_byte__relocation_semantics.
Qed.
Lemma debug_ldiff_lor_disjoint__relocation_semantics : forall bit rest,
  Z.land bit rest = 0 ->
  Z.ldiff (Z.lor bit rest) bit = rest.
Proof.
  intros bit rest Hdisj.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.ldiff_spec, Z.lor_spec.
  assert (Hbit : Z.testbit (Z.land bit rest) n = false).
  { rewrite Hdisj, Z.testbit_0_l. reflexivity. }
  rewrite Z.land_spec in Hbit.
  destruct (Z.testbit bit n), (Z.testbit rest n); cbn in *;
    try reflexivity; discriminate.
Qed.
Lemma debug_clear_lor_byte__relocation_semantics : forall bit rest,
  0 <= Z.lor bit rest < 2 ^ 8 ->
  Z.land bit rest = 0 ->
  Z.land (Z.lor bit rest) (unsigned_last_nbits (Z.lnot bit) 8) = rest.
Proof.
  intros bit rest Hbyte Hdisj.
  rewrite <- (unsigned_last_nbits_eq (Z.lor bit rest) 8 Hbyte) at 1.
  rewrite unsigned_last_nbits_land_clear_r by lia.
  rewrite unsigned_last_nbits_eq by exact Hbyte.
  rewrite <- Z.ldiff_land.
  apply debug_ldiff_lor_disjoint__relocation_semantics. exact Hdisj.
Qed.
Lemma debug_ready_tbl_remove_selected_row__relocation_semantics :
  forall rl st tid t,
    In tid rl -> NoDup rl ->
    st.(inUsedTaskStates) tid = Some t ->
    task_priority_unique st ->
    (forall tid0 t0, In tid0 rl ->
       st.(inUsedTaskStates) tid0 = Some t0 -> 0 <= t0.(curPrio)) ->
    encode_ready_tbl_at (Ucos2Verify.lib.helpers.remove_Z_eqb tid rl) st (t.(curPrio) / 8) =
      Z.land (encode_ready_tbl_at rl st (t.(curPrio) / 8))
        (unsigned_last_nbits
          (Z.lnot (Z.shiftl 1 (t.(curPrio) mod 8))) 8).
Proof.
  intros rl st tid t Hin Hnd Hget Huniq Hrange.
  set (filtered := Ucos2Verify.lib.helpers.remove_Z_eqb tid rl).
  assert (Hperm : Permutation rl (tid :: filtered)).
  { subst filtered. apply debug_remove_perm_cons__relocation_semantics; assumption. }
  assert (Hndf : NoDup filtered).
  { subst filtered. apply Ucos2Verify.lib.helpers.remove_Z_eqb_NoDup. exact Hnd. }
  assert (Hnot : ~ In tid filtered).
  { subst filtered. apply Ucos2Verify.lib.helpers.remove_Z_eqb_notin. }
  assert (Hrangef : forall tid0 t0, In tid0 filtered ->
    st.(inUsedTaskStates) tid0 = Some t0 -> 0 <= t0.(curPrio)).
  {
    intros tid0 t0 Hin0 Hget0. eapply Hrange; [|exact Hget0].
    subst filtered. eapply Ucos2Verify.lib.helpers.remove_Z_eqb_in. exact Hin0.
  }
  assert (Hneqf : forall tid0 t0, In tid0 filtered ->
    st.(inUsedTaskStates) tid0 = Some t0 ->
    t0.(curPrio) <> t.(curPrio)).
  {
    intros tid0 t0 Hin0 Hget0 Heq.
    assert (tid0 = tid) by (eapply Huniq; eassumption).
    subst tid0. contradiction.
  }
  assert (Hdisj :
    Z.land (Z.shiftl 1 (t.(curPrio) mod 8))
      (encode_ready_tbl_at filtered st (t.(curPrio) / 8)) = 0).
  {
    rewrite debug_encode_tbl_as_lor__relocation_semantics by assumption.
    apply debug_bit_disjoint_tbl_lor__relocation_semantics; try reflexivity.
    - eapply Hrange; [exact Hin | exact Hget].
    - exact Hrangef.
    - exact Hneqf.
  }
  assert (Hold :
    encode_ready_tbl_at rl st (t.(curPrio) / 8) =
      Z.lor (Z.shiftl 1 (t.(curPrio) mod 8))
        (encode_ready_tbl_at filtered st (t.(curPrio) / 8))).
  {
    rewrite (debug_encode_tbl_perm__relocation_semantics _ _ _ _ Hperm).
    rewrite debug_encode_tbl_as_lor__relocation_semantics.
    2: { constructor; assumption. }
    2: exact Huniq.
    2: {
      intros tid0 t0 [Heq|Hin0] Hget0.
      - subst tid0. exact (Hrange tid t0 Hin Hget0).
      - exact (Hrangef tid0 t0 Hin0 Hget0).
    }
    simpl. rewrite Hget, Z.eqb_refl.
    rewrite <- debug_encode_tbl_as_lor__relocation_semantics by assumption.
    reflexivity.
  }
  rewrite Hold.
  symmetry.
  apply debug_clear_lor_byte__relocation_semantics.
  - rewrite <- Hold. apply debug_encode_tbl_byte__relocation_semantics; assumption.
  - exact Hdisj.
Qed.
Lemma debug_ready_tbl_remove_other_row__relocation_semantics :
  forall rl st tid t y,
    In tid rl -> NoDup rl ->
    st.(inUsedTaskStates) tid = Some t ->
    task_priority_unique st ->
    (forall tid0 t0, In tid0 rl ->
       st.(inUsedTaskStates) tid0 = Some t0 -> 0 <= t0.(curPrio)) ->
    t.(curPrio) / 8 <> y ->
    encode_ready_tbl_at (Ucos2Verify.lib.helpers.remove_Z_eqb tid rl) st y =
      encode_ready_tbl_at rl st y.
Proof.
  intros rl st tid t y Hin Hnd Hget Huniq Hrange Hrowneq.
  set (filtered := Ucos2Verify.lib.helpers.remove_Z_eqb tid rl).
  assert (Hperm : Permutation rl (tid :: filtered)).
  { subst filtered. apply debug_remove_perm_cons__relocation_semantics; assumption. }
  assert (Hndf : NoDup filtered).
  { subst filtered. apply Ucos2Verify.lib.helpers.remove_Z_eqb_NoDup. exact Hnd. }
  assert (Hrangef : forall tid0 t0, In tid0 filtered ->
    st.(inUsedTaskStates) tid0 = Some t0 -> 0 <= t0.(curPrio)).
  {
    intros tid0 t0 Hin0 Hget0. eapply Hrange; [|exact Hget0].
    subst filtered. eapply Ucos2Verify.lib.helpers.remove_Z_eqb_in. exact Hin0.
  }
  rewrite (debug_encode_tbl_perm__relocation_semantics _ _ _ _ Hperm).
  symmetry.
  rewrite debug_encode_tbl_as_lor__relocation_semantics.
  2: {
    constructor.
    - subst filtered. apply Ucos2Verify.lib.helpers.remove_Z_eqb_notin.
    - exact Hndf.
  }
  2: exact Huniq.
  2: {
    intros tid0 t0 [Heq|Hin0] Hget0.
    - subst tid0. exact (Hrange tid t0 Hin Hget0).
    - exact (Hrangef tid0 t0 Hin0 Hget0).
  }
  simpl. rewrite Hget.
  destruct (Z.eqb (t.(curPrio) / 8) y) eqn:Hrow; [|].
  - apply Z.eqb_eq in Hrow. contradiction.
  - rewrite <- debug_encode_tbl_as_lor__relocation_semantics by assumption. reflexivity.
Qed.
Lemma debug_ready_tbl_insert_updated__relocation_semantics :
  forall (key : TaskID -> Z) filtered st st2 tid t2 newPrio y,
    ~ In tid filtered -> NoDup filtered ->
    st2.(inUsedTaskStates) tid = Some t2 ->
    t2.(curPrio) = newPrio ->
    (forall tid0, In tid0 filtered ->
       st2.(inUsedTaskStates) tid0 = st.(inUsedTaskStates) tid0) ->
    task_priority_unique st2 ->
    (forall tid0 t0, In tid0 (tid :: filtered) ->
       st2.(inUsedTaskStates) tid0 = Some t0 -> 0 <= t0.(curPrio)) ->
    encode_ready_tbl_at (Ucos2Verify.lib.helpers.insert_sorted_by key tid filtered) st2 y =
      if Z.eqb (newPrio / 8) y
      then Z.lor (Z.shiftl 1 (newPrio mod 8))
             (encode_ready_tbl_at filtered st y)
      else encode_ready_tbl_at filtered st y.
Proof.
  intros key filtered st st2 tid t2 newPrio y Hnot Hnd Hget Hprio
    Hext Huniq Hrange.
  pose proof (Ucos2Verify.lib.helpers.insert_sorted_by_perm TaskID key tid filtered) as Hperm.
  rewrite <- (debug_encode_tbl_perm__relocation_semantics _ _ st2 y Hperm).
  rewrite debug_encode_tbl_as_lor__relocation_semantics.
  2: { constructor; assumption. }
  2: exact Huniq.
  2: exact Hrange.
  simpl. rewrite Hget, Hprio.
  rewrite <- debug_encode_tbl_as_lor__relocation_semantics.
  2: exact Hnd.
  2: exact Huniq.
  2: {
    intros tid0 t0 Hin0 Hget0.
    eapply Hrange; [right; exact Hin0 | exact Hget0].
  }
  rewrite (debug_encode_tbl_ext_in__relocation_semantics filtered st2 st y Hext).
  destruct (Z.eqb (newPrio / 8) y); reflexivity.
Qed.
Lemma debug_ready_grp_insert_updated__relocation_semantics :
  forall (key : TaskID -> Z) filtered st st2 tid t2 newPrio,
    st2.(inUsedTaskStates) tid = Some t2 ->
    t2.(curPrio) = newPrio ->
    (forall tid0, In tid0 filtered ->
       st2.(inUsedTaskStates) tid0 = st.(inUsedTaskStates) tid0) ->
    encode_ready_grp (Ucos2Verify.lib.helpers.insert_sorted_by key tid filtered) st2 =
      Z.lor (Z.shiftl 1 (newPrio / 8))
        (encode_ready_grp filtered st).
Proof.
  intros key filtered st st2 tid t2 newPrio Hget Hprio Hext.
  pose proof (Ucos2Verify.lib.helpers.insert_sorted_by_perm TaskID key tid filtered) as Hperm.
  rewrite <- (debug_encode_grp_perm__relocation_semantics _ _ st2 Hperm).
  simpl. rewrite Hget, Hprio.
  rewrite (debug_encode_grp_ext_in__relocation_semantics filtered st2 st Hext).
  reflexivity.
Qed.
Lemma debug_ready_tbl_relocation_formula__relocation_semantics :
  forall (key : TaskID -> Z) rl st st2 tid old_t new_t newPrio y,
    In tid rl -> NoDup rl ->
    st.(inUsedTaskStates) tid = Some old_t ->
    st2.(inUsedTaskStates) tid = Some new_t ->
    new_t.(curPrio) = newPrio ->
    (forall tid0, In tid0 (Ucos2Verify.lib.helpers.remove_Z_eqb tid rl) ->
       st2.(inUsedTaskStates) tid0 = st.(inUsedTaskStates) tid0) ->
    task_priority_unique st -> task_priority_unique st2 ->
    (forall tid0 t0, In tid0 rl ->
       st.(inUsedTaskStates) tid0 = Some t0 -> 0 <= t0.(curPrio)) ->
    (forall tid0 t0, In tid0 (tid :: Ucos2Verify.lib.helpers.remove_Z_eqb tid rl) ->
       st2.(inUsedTaskStates) tid0 = Some t0 -> 0 <= t0.(curPrio)) ->
    encode_ready_tbl_at
      (Ucos2Verify.lib.helpers.insert_sorted_by key tid (Ucos2Verify.lib.helpers.remove_Z_eqb tid rl)) st2 y =
      if Z.eqb (newPrio / 8) y
      then Z.lor (Z.shiftl 1 (newPrio mod 8))
        (if Z.eqb (old_t.(curPrio) / 8) y
         then Z.land (encode_ready_tbl_at rl st y)
           (unsigned_last_nbits
             (Z.lnot (Z.shiftl 1 (old_t.(curPrio) mod 8))) 8)
         else encode_ready_tbl_at rl st y)
      else if Z.eqb (old_t.(curPrio) / 8) y
      then Z.land (encode_ready_tbl_at rl st y)
        (unsigned_last_nbits
          (Z.lnot (Z.shiftl 1 (old_t.(curPrio) mod 8))) 8)
      else encode_ready_tbl_at rl st y.
Proof.
  intros key rl st st2 tid old_t new_t newPrio y Hin Hnd Hget Hget2
    Hnew Hext Huniq Huniq2 Hrange Hrange2.
  rewrite debug_ready_tbl_insert_updated__relocation_semantics with
    (st := st) (t2 := new_t) (newPrio := newPrio).
  2: apply Ucos2Verify.lib.helpers.remove_Z_eqb_notin.
  2: apply Ucos2Verify.lib.helpers.remove_Z_eqb_NoDup; exact Hnd.
  2: exact Hget2.
  2: exact Hnew.
  2: exact Hext.
  2: exact Huniq2.
  2: exact Hrange2.
  destruct (Z.eqb (newPrio / 8) y) eqn:Hnewrow;
    destruct (Z.eqb (old_t.(curPrio) / 8) y) eqn:Holdrow.
  - apply Z.eqb_eq in Holdrow. subst y.
    rewrite debug_ready_tbl_remove_selected_row__relocation_semantics with (t := old_t);
      try assumption.
    reflexivity.
  - apply Z.eqb_neq in Holdrow.
    rewrite debug_ready_tbl_remove_other_row__relocation_semantics with (t := old_t);
      try assumption.
    reflexivity.
  - apply Z.eqb_eq in Holdrow. subst y.
    rewrite debug_ready_tbl_remove_selected_row__relocation_semantics with (t := old_t);
      try assumption.
    reflexivity.
  - apply Z.eqb_neq in Holdrow.
    rewrite debug_ready_tbl_remove_other_row__relocation_semantics with (t := old_t);
      try assumption.
    reflexivity.
Qed.
Lemma debug_encode_grp_byte__relocation_semantics : forall l st,
  (forall tid t, In tid l -> st.(inUsedTaskStates) tid = Some t ->
     0 <= t.(curPrio) / 8 < 8) ->
  0 <= encode_ready_grp l st < 2 ^ 8.
Proof.
  induction l as [|a rest IH]; intros st Hrange; simpl; [lia|].
  destruct (st.(inUsedTaskStates) a) as [ta|] eqn:Hgeta.
  - apply debug_lor_byte__relocation_semantics.
    + apply debug_shiftl_bit_byte__relocation_semantics.
      eapply Hrange; [left; reflexivity | exact Hgeta].
    + apply IH. intros; eapply Hrange; [right; eassumption | eassumption].
  - apply IH. intros; eapply Hrange; [right; eassumption | eassumption].
Qed.
Lemma debug_no_row_group_disjoint__relocation_semantics : forall l st y,
  0 <= y ->
  (forall tid t, In tid l -> st.(inUsedTaskStates) tid = Some t ->
     0 <= t.(curPrio) / 8) ->
  (forall tid t, In tid l -> st.(inUsedTaskStates) tid = Some t ->
     t.(curPrio) / 8 <> y) ->
  Z.land (Z.shiftl 1 y) (encode_ready_grp l st) = 0.
Proof.
  induction l as [|a rest IH]; intros st y Hy Hrange Hnorow; simpl.
  - apply Z.land_0_r.
  - destruct (st.(inUsedTaskStates) a) as [ta|] eqn:Hgeta.
    + rewrite Z.land_lor_distr_r.
      rewrite IH with (st := st) (y := y).
      2: exact Hy.
      2: { intros; eapply Hrange; [right; eassumption | eassumption]. }
      2: { intros; eapply Hnorow; [right; eassumption | eassumption]. }
      rewrite Z.lor_0_r.
      apply debug_land_single_bits_neq__relocation_semantics.
      * exact Hy.
      * eapply Hrange; [left; reflexivity | exact Hgeta].
      * intro Heq. apply (Hnorow a ta ltac:(left; reflexivity) Hgeta).
        symmetry. exact Heq.
    + apply IH with (st := st) (y := y); auto.
      * intros; eapply Hrange; [right; eassumption | eassumption].
      * intros; eapply Hnorow; [right; eassumption | eassumption].
Qed.
Lemma debug_tbl_lor_nonzero_has_row__relocation_semantics : forall l st y,
  fold_right
    (fun tid acc =>
       match st.(inUsedTaskStates) tid with
       | Some t =>
           if Z.eqb (t.(curPrio) / 8) y
           then Z.lor (Z.shiftl 1 (t.(curPrio) mod 8)) acc
           else acc
       | None => acc
       end) 0 l <> 0 ->
  exists tid t, In tid l /\
    st.(inUsedTaskStates) tid = Some t /\ t.(curPrio) / 8 = y.
Proof.
  induction l as [|a rest IH]; intros st y Hne; simpl in Hne.
  - contradiction.
  - destruct (st.(inUsedTaskStates) a) as [ta|] eqn:Hgeta.
    + destruct (Z.eqb (ta.(curPrio) / 8) y) eqn:Hrow.
      * exists a, ta. repeat split; try (left; reflexivity); try exact Hgeta.
        apply Z.eqb_eq. exact Hrow.
      * destruct (IH st y Hne) as [tid [t [Hin [Hget Hroweq]]]].
        exists tid, t. repeat split; try (right; exact Hin); assumption.
    + destruct (IH st y Hne) as [tid [t [Hin [Hget Hroweq]]]].
      exists tid, t. repeat split; try (right; exact Hin); assumption.
Qed.
Lemma debug_encode_tbl_nonzero_has_row__relocation_semantics : forall l st y,
  NoDup l -> task_priority_unique st ->
  (forall tid t, In tid l -> st.(inUsedTaskStates) tid = Some t ->
     0 <= t.(curPrio)) ->
  encode_ready_tbl_at l st y <> 0 ->
  exists tid t, In tid l /\
    st.(inUsedTaskStates) tid = Some t /\ t.(curPrio) / 8 = y.
Proof.
  intros l st y Hnd Huniq Hrange Hne.
  rewrite debug_encode_tbl_as_lor__relocation_semantics in Hne by assumption.
  eapply debug_tbl_lor_nonzero_has_row__relocation_semantics. exact Hne.
Qed.
Lemma debug_group_absorbs_present_row__relocation_semantics : forall l st y tid t,
  In tid l -> NoDup l ->
  st.(inUsedTaskStates) tid = Some t ->
  t.(curPrio) / 8 = y ->
  Z.lor (Z.shiftl 1 y) (encode_ready_grp l st) =
    encode_ready_grp l st.
Proof.
  intros l st y tid t Hin Hnd Hget Hrow.
  pose proof (debug_remove_perm_cons__relocation_semantics tid l Hin Hnd) as Hperm.
  rewrite (debug_encode_grp_perm__relocation_semantics _ _ st Hperm).
  simpl. rewrite Hget, Hrow.
  rewrite Z.lor_assoc, Z.lor_diag. reflexivity.
Qed.
Lemma debug_ready_grp_relocation_nonzero__relocation_semantics :
  forall (key : TaskID -> Z) rl st st2 tid old_t new_t newPrio,
    In tid rl -> NoDup rl ->
    st.(inUsedTaskStates) tid = Some old_t ->
    st2.(inUsedTaskStates) tid = Some new_t ->
    new_t.(curPrio) = newPrio ->
    (forall tid0, In tid0 (Ucos2Verify.lib.helpers.remove_Z_eqb tid rl) ->
       st2.(inUsedTaskStates) tid0 = st.(inUsedTaskStates) tid0) ->
    task_priority_unique st ->
    (forall tid0 t0, In tid0 rl ->
       st.(inUsedTaskStates) tid0 = Some t0 -> 0 <= t0.(curPrio)) ->
    Z.land (encode_ready_tbl_at rl st (old_t.(curPrio) / 8))
      (unsigned_last_nbits
        (Z.lnot (Z.shiftl 1 (old_t.(curPrio) mod 8))) 8) <> 0 ->
    encode_ready_grp
      (Ucos2Verify.lib.helpers.insert_sorted_by key tid (Ucos2Verify.lib.helpers.remove_Z_eqb tid rl)) st2 =
      Z.lor (Z.shiftl 1 (newPrio / 8)) (encode_ready_grp rl st).
Proof.
  intros key rl st st2 tid old_t new_t newPrio Hin Hnd Hget Hget2
    Hnew Hext Huniq Hrange Hclearnz.
  set (filtered := Ucos2Verify.lib.helpers.remove_Z_eqb tid rl).
  assert (Hndf : NoDup filtered).
  { subst filtered. apply Ucos2Verify.lib.helpers.remove_Z_eqb_NoDup. exact Hnd. }
  assert (Hrangef : forall tid0 t0, In tid0 filtered ->
    st.(inUsedTaskStates) tid0 = Some t0 -> 0 <= t0.(curPrio)).
  {
    intros tid0 t0 Hin0 Hget0. eapply Hrange; [|exact Hget0].
    subst filtered. apply Ucos2Verify.lib.helpers.remove_Z_eqb_in with (x := tid). exact Hin0.
  }
  assert (Hfilternz :
    encode_ready_tbl_at filtered st (old_t.(curPrio) / 8) <> 0).
  {
    rewrite debug_ready_tbl_remove_selected_row__relocation_semantics with
      (rl := rl) (tid := tid) (t := old_t); assumption.
  }
  destruct (debug_encode_tbl_nonzero_has_row__relocation_semantics filtered st
    (old_t.(curPrio) / 8) Hndf Huniq Hrangef Hfilternz)
    as [tid0 [t0 [Hin0 [Hget0 Hrow0]]]].
  assert (Habsorb :
    Z.lor (Z.shiftl 1 (old_t.(curPrio) / 8))
      (encode_ready_grp filtered st) = encode_ready_grp filtered st).
  { eapply debug_group_absorbs_present_row__relocation_semantics; eassumption. }
  rewrite debug_ready_grp_insert_updated__relocation_semantics with
    (st := st) (t2 := new_t) (newPrio := newPrio).
  2: exact Hget2.
  2: exact Hnew.
  2: exact Hext.
  assert (Hperm : Permutation rl (tid :: filtered)).
  { subst filtered. apply debug_remove_perm_cons__relocation_semantics; assumption. }
  rewrite (debug_encode_grp_perm__relocation_semantics _ _ st Hperm).
  simpl. rewrite Hget.
  rewrite Habsorb. reflexivity.
Qed.
Lemma debug_encode_tbl_present_row_nonzero__relocation_semantics : forall l st y tid t,
  In tid l -> NoDup l ->
  st.(inUsedTaskStates) tid = Some t ->
  t.(curPrio) / 8 = y ->
  task_priority_unique st ->
  (forall tid0 t0, In tid0 l ->
     st.(inUsedTaskStates) tid0 = Some t0 -> 0 <= t0.(curPrio)) ->
  encode_ready_tbl_at l st y <> 0.
Proof.
  intros l st y tid t Hin Hnd Hget Hrow Huniq Hrange Hzero.
  pose proof (debug_remove_perm_cons__relocation_semantics tid l Hin Hnd) as Hperm.
  rewrite (debug_encode_tbl_perm__relocation_semantics _ _ st y Hperm) in Hzero.
  rewrite debug_encode_tbl_as_lor__relocation_semantics in Hzero.
  2: {
    constructor.
    - apply Ucos2Verify.lib.helpers.remove_Z_eqb_notin.
    - apply Ucos2Verify.lib.helpers.remove_Z_eqb_NoDup. exact Hnd.
  }
  2: exact Huniq.
  2: {
    intros tid0 t0 [Heq|Hin0] Hget0.
    - subst tid0. eapply Hrange; [exact Hin | exact Hget0].
    - eapply Hrange; [|exact Hget0].
      eapply Ucos2Verify.lib.helpers.remove_Z_eqb_in. exact Hin0.
  }
  simpl in Hzero. rewrite Hget, Hrow, Z.eqb_refl in Hzero.
  assert (Hbit :
    Z.testbit
      (Z.lor (Z.shiftl 1 (t.(curPrio) mod 8))
        (fold_right
          (fun tid0 acc =>
             match st.(inUsedTaskStates) tid0 with
             | Some t0 =>
                 if Z.eqb (t0.(curPrio) / 8) y
                 then Z.lor (Z.shiftl 1 (t0.(curPrio) mod 8)) acc
                 else acc
             | None => acc
             end) 0 (Ucos2Verify.lib.helpers.remove_Z_eqb tid l)))
      (t.(curPrio) mod 8) = false).
  { rewrite Hzero, Z.testbit_0_l. reflexivity. }
  rewrite Z.lor_spec, Z.shiftl_1_l,
    Z.pow2_bits_eqb, Z.eqb_refl in Hbit.
  - discriminate.
  - apply Z.mod_pos_bound. lia.
Qed.
Lemma debug_encode_tbl_zero_no_row__relocation_semantics : forall l st y,
  NoDup l -> task_priority_unique st ->
  (forall tid t, In tid l -> st.(inUsedTaskStates) tid = Some t ->
     0 <= t.(curPrio)) ->
  encode_ready_tbl_at l st y = 0 ->
  forall tid t, In tid l -> st.(inUsedTaskStates) tid = Some t ->
    t.(curPrio) / 8 <> y.
Proof.
  intros l st y Hnd Huniq Hrange Hzero tid t Hin Hget Hrow.
  pose proof (debug_encode_tbl_present_row_nonzero__relocation_semantics
    l st y tid t Hin Hnd Hget Hrow Huniq Hrange) as Hne.
  contradiction.
Qed.
Lemma debug_ready_grp_relocation_zero__relocation_semantics :
  forall (key : TaskID -> Z) rl st st2 tid old_t new_t newPrio,
    In tid rl -> NoDup rl ->
    st.(inUsedTaskStates) tid = Some old_t ->
    st2.(inUsedTaskStates) tid = Some new_t ->
    new_t.(curPrio) = newPrio ->
    (forall tid0, In tid0 (Ucos2Verify.lib.helpers.remove_Z_eqb tid rl) ->
       st2.(inUsedTaskStates) tid0 = st.(inUsedTaskStates) tid0) ->
    task_priority_unique st ->
    (forall tid0 t0, In tid0 rl ->
       st.(inUsedTaskStates) tid0 = Some t0 -> 0 <= t0.(curPrio)) ->
    (forall tid0 t0, In tid0 rl ->
       st.(inUsedTaskStates) tid0 = Some t0 ->
       0 <= t0.(curPrio) / 8 < 8) ->
    Z.land (encode_ready_tbl_at rl st (old_t.(curPrio) / 8))
      (unsigned_last_nbits
        (Z.lnot (Z.shiftl 1 (old_t.(curPrio) mod 8))) 8) = 0 ->
    encode_ready_grp
      (Ucos2Verify.lib.helpers.insert_sorted_by key tid (Ucos2Verify.lib.helpers.remove_Z_eqb tid rl)) st2 =
      Z.lor
        (Z.land (encode_ready_grp rl st)
          (unsigned_last_nbits
            (Z.lnot (Z.shiftl 1 (old_t.(curPrio) / 8))) 8))
        (Z.shiftl 1 (newPrio / 8)).
Proof.
  intros key rl st st2 tid old_t new_t newPrio Hin Hnd Hget Hget2
    Hnew Hext Huniq Hrange Hdivrange Hclearzero.
  set (filtered := Ucos2Verify.lib.helpers.remove_Z_eqb tid rl).
  assert (Hndf : NoDup filtered).
  { subst filtered. apply Ucos2Verify.lib.helpers.remove_Z_eqb_NoDup. exact Hnd. }
  assert (Hrangef : forall tid0 t0, In tid0 filtered ->
    st.(inUsedTaskStates) tid0 = Some t0 -> 0 <= t0.(curPrio)).
  {
    intros tid0 t0 Hin0 Hget0. eapply Hrange; [|exact Hget0].
    subst filtered. apply Ucos2Verify.lib.helpers.remove_Z_eqb_in with (x := tid). exact Hin0.
  }
  assert (Hdivrangef : forall tid0 t0, In tid0 filtered ->
    st.(inUsedTaskStates) tid0 = Some t0 ->
    0 <= t0.(curPrio) / 8 < 8).
  {
    intros tid0 t0 Hin0 Hget0. eapply Hdivrange; [|exact Hget0].
    subst filtered. apply Ucos2Verify.lib.helpers.remove_Z_eqb_in with (x := tid). exact Hin0.
  }
  assert (Hfilterzero :
    encode_ready_tbl_at filtered st (old_t.(curPrio) / 8) = 0).
  {
    rewrite debug_ready_tbl_remove_selected_row__relocation_semantics with
      (rl := rl) (tid := tid) (t := old_t); assumption.
  }
  assert (Hnorow : forall tid0 t0, In tid0 filtered ->
    st.(inUsedTaskStates) tid0 = Some t0 ->
    t0.(curPrio) / 8 <> old_t.(curPrio) / 8).
  {
    eapply debug_encode_tbl_zero_no_row__relocation_semantics; eassumption.
  }
  assert (Holddy : 0 <= old_t.(curPrio) / 8).
  { eapply Hdivrange; [exact Hin | exact Hget]. }
  assert (Hgrpdisj :
    Z.land (Z.shiftl 1 (old_t.(curPrio) / 8))
      (encode_ready_grp filtered st) = 0).
  {
    apply debug_no_row_group_disjoint__relocation_semantics.
    - exact Holddy.
    - intros. eapply Hdivrangef; eassumption.
    - exact Hnorow.
  }
  assert (Hperm : Permutation rl (tid :: filtered)).
  { subst filtered. apply debug_remove_perm_cons__relocation_semantics; assumption. }
  assert (Holdgrp : encode_ready_grp rl st =
    Z.lor (Z.shiftl 1 (old_t.(curPrio) / 8))
      (encode_ready_grp filtered st)).
  {
    rewrite (debug_encode_grp_perm__relocation_semantics _ _ st Hperm).
    simpl. rewrite Hget. reflexivity.
  }
  assert (Hgrpclear :
    Z.land (encode_ready_grp rl st)
      (unsigned_last_nbits
        (Z.lnot (Z.shiftl 1 (old_t.(curPrio) / 8))) 8) =
    encode_ready_grp filtered st).
  {
    rewrite Holdgrp.
    apply debug_clear_lor_byte__relocation_semantics.
    - rewrite <- Holdgrp. apply debug_encode_grp_byte__relocation_semantics. exact Hdivrange.
    - exact Hgrpdisj.
  }
  rewrite debug_ready_grp_insert_updated__relocation_semantics with
    (st := st) (t2 := new_t) (newPrio := newPrio).
  2: exact Hget2.
  2: exact Hnew.
  2: exact Hext.
  rewrite Hgrpclear, Z.lor_comm. reflexivity.
Qed.
Lemma debug_atomic_ready_bitmap_correspondence__relocation_semantics :
  forall sg (key : TaskID -> Z) rl st st2 tid old_t new_t newPrio,
    In tid rl -> NoDup rl ->
    st.(inUsedTaskStates) tid = Some old_t ->
    new_t =
      {| taskID := old_t.(taskID);
     taskGeneration := old_t.(taskGeneration);
     tcbStkPtr := old_t.(tcbStkPtr);
     tcbExtPtr := old_t.(tcbExtPtr);
     tcbStkBottom := old_t.(tcbStkBottom);
     tcbStkSize := old_t.(tcbStkSize);
     tcbOpt := old_t.(tcbOpt);
     tcbPublicId := old_t.(tcbPublicId);
     tcbFlagNode := old_t.(tcbFlagNode);
     tcbFlagsRdy := old_t.(tcbFlagsRdy);
     tcbTaskName := old_t.(tcbTaskName);
     tcbReg0 := old_t.(tcbReg0);
     tcbCtxSwCtr := old_t.(tcbCtxSwCtr);
     tcbCyclesTot := old_t.(tcbCyclesTot);
     tcbCyclesStart := old_t.(tcbCyclesStart);
     tcbStkBase := old_t.(tcbStkBase);
     tcbStkUsed := old_t.(tcbStkUsed);
     tcbPadding42 := old_t.(tcbPadding42);
     tcbPadding43 := old_t.(tcbPadding43);
     tcbEventMultiPtr := old_t.(tcbEventMultiPtr);
         curPrio := newPrio;
         stat := old_t.(stat);
         statPend := old_t.(statPend);
         dly := old_t.(dly);
         eventPtr := old_t.(eventPtr);
         eventMultiWaitEvents := old_t.(eventMultiWaitEvents);
         eventMultiRdy := old_t.(eventMultiRdy);
         msg := old_t.(msg);
         nextTCB := old_t.(nextTCB);
         prevTCB := old_t.(prevTCB);
         delReq := old_t.(delReq) |} ->
    st2 =
      {| inUsedTaskStates := fun tid' =>
           if Z.eqb tid' tid then Some new_t
           else st.(inUsedTaskStates) tid';
         unUsedTaskStates := st.(unUsedTaskStates);
         tcbListHead := st.(tcbListHead);
         prioTbl := fun p =>
           if Z.eqb p newPrio then PTTask tid else st.(prioTbl) p;
         taskRegNextID := st.(taskRegNextID);
         parkedTaskStacks := st.(parkedTaskStacks);
         taskLifecycle := st.(taskLifecycle);
     taskCount := st.(taskCount) |} ->
    verification_slice_task_validity sg st ->
    verification_slice_task_validity sg st2 ->
    (forall y,
      encode_ready_tbl_at
        (Ucos2Verify.lib.helpers.insert_sorted_by key tid (Ucos2Verify.lib.helpers.remove_Z_eqb tid rl)) st2 y =
        if Z.eqb (newPrio / 8) y
        then Z.lor (Z.shiftl 1 (newPrio mod 8))
          (if Z.eqb (old_t.(curPrio) / 8) y
           then Z.land (encode_ready_tbl_at rl st y)
             (unsigned_last_nbits
               (Z.lnot (Z.shiftl 1 (old_t.(curPrio) mod 8))) 8)
           else encode_ready_tbl_at rl st y)
        else if Z.eqb (old_t.(curPrio) / 8) y
        then Z.land (encode_ready_tbl_at rl st y)
          (unsigned_last_nbits
            (Z.lnot (Z.shiftl 1 (old_t.(curPrio) mod 8))) 8)
        else encode_ready_tbl_at rl st y) /\
    (Z.land (encode_ready_tbl_at rl st (old_t.(curPrio) / 8))
       (unsigned_last_nbits
         (Z.lnot (Z.shiftl 1 (old_t.(curPrio) mod 8))) 8) <> 0 ->
     encode_ready_grp
       (Ucos2Verify.lib.helpers.insert_sorted_by key tid (Ucos2Verify.lib.helpers.remove_Z_eqb tid rl)) st2 =
       Z.lor (Z.shiftl 1 (newPrio / 8)) (encode_ready_grp rl st)) /\
    (Z.land (encode_ready_tbl_at rl st (old_t.(curPrio) / 8))
       (unsigned_last_nbits
         (Z.lnot (Z.shiftl 1 (old_t.(curPrio) mod 8))) 8) = 0 ->
     encode_ready_grp
       (Ucos2Verify.lib.helpers.insert_sorted_by key tid (Ucos2Verify.lib.helpers.remove_Z_eqb tid rl)) st2 =
       Z.lor
         (Z.land (encode_ready_grp rl st)
           (unsigned_last_nbits
             (Z.lnot (Z.shiftl 1 (old_t.(curPrio) / 8))) 8))
         (Z.shiftl 1 (newPrio / 8))).
Proof.
  intros sg key rl st st2 tid old_t new_t newPrio Hin Hnd Hget
    Hnew Hst2 Hvalid Hvalid2.
  assert (Hget2 : st2.(inUsedTaskStates) tid = Some new_t).
  { subst st2. cbn. rewrite Z.eqb_refl. reflexivity. }
  assert (Hnewprio : new_t.(curPrio) = newPrio).
  { subst new_t. reflexivity. }
  assert (Hext : forall tid0, In tid0 (Ucos2Verify.lib.helpers.remove_Z_eqb tid rl) ->
    st2.(inUsedTaskStates) tid0 = st.(inUsedTaskStates) tid0).
  {
    intros tid0 Hin0. subst st2. cbn.
    destruct (Z.eqb tid0 tid) eqn:Heq; [|reflexivity].
    apply Z.eqb_eq in Heq. subst tid0.
    exfalso. exact (Ucos2Verify.lib.helpers.remove_Z_eqb_notin tid rl Hin0).
  }
  destruct Hvalid as [Hstate Hderived].
  unfold verification_slice_task_in_range in Hstate.
  destruct Hstate as
    [Hids [Hfree_nd [Hfree_range [Hfree_unused [Hprio [_ Huniq]]]]]].
  assert (Hrange : forall tid0 t0, In tid0 rl ->
    st.(inUsedTaskStates) tid0 = Some t0 -> 0 <= t0.(curPrio)).
  {
    intros tid0 t0 Hin0 Hget0.
    destruct (Hderived tid0 t0 Hget0) as [[Hp _] _]. exact Hp.
  }
  assert (Hdivrange : forall tid0 t0, In tid0 rl ->
    st.(inUsedTaskStates) tid0 = Some t0 ->
    0 <= t0.(curPrio) / 8 < 8).
  {
    intros tid0 t0 Hin0 Hget0.
    destruct (Hderived tid0 t0 Hget0) as [_ [_ [_ Hdiv]]].
    exact Hdiv.
  }
  destruct Hvalid2 as [Hstate2 Hderived2].
  unfold verification_slice_task_in_range in Hstate2.
  destruct Hstate2 as
    [Hids2 [Hfree_nd2 [Hfree_range2 [Hfree_unused2 [Hprio2 [_ Huniq2]]]]]].
  assert (Hrange2 : forall tid0 t0,
    In tid0 (tid :: Ucos2Verify.lib.helpers.remove_Z_eqb tid rl) ->
    st2.(inUsedTaskStates) tid0 = Some t0 -> 0 <= t0.(curPrio)).
  {
    intros tid0 t0 Hin0 Hget0.
    destruct (Hderived2 tid0 t0 Hget0) as [[Hp _] _]. exact Hp.
  }
  split.
  - intro y. eapply debug_ready_tbl_relocation_formula__relocation_semantics; eassumption.
  - split.
    + intro Hclearnz. eapply debug_ready_grp_relocation_nonzero__relocation_semantics;
        eassumption.
    + intro Hclearzero. eapply debug_ready_grp_relocation_zero__relocation_semantics;
        eassumption.
Qed.
Lemma debug_atomic_ready_bitmap_bytes__relocation_semantics :
  forall sg (key : TaskID -> Z) rl st st2 tid old_t new_t newPrio,
    In tid rl -> NoDup rl ->
    st.(inUsedTaskStates) tid = Some old_t ->
    new_t =
      {| taskID := old_t.(taskID);
     taskGeneration := old_t.(taskGeneration);
     tcbStkPtr := old_t.(tcbStkPtr);
     tcbExtPtr := old_t.(tcbExtPtr);
     tcbStkBottom := old_t.(tcbStkBottom);
     tcbStkSize := old_t.(tcbStkSize);
     tcbOpt := old_t.(tcbOpt);
     tcbPublicId := old_t.(tcbPublicId);
     tcbFlagNode := old_t.(tcbFlagNode);
     tcbFlagsRdy := old_t.(tcbFlagsRdy);
     tcbTaskName := old_t.(tcbTaskName);
     tcbReg0 := old_t.(tcbReg0);
     tcbCtxSwCtr := old_t.(tcbCtxSwCtr);
     tcbCyclesTot := old_t.(tcbCyclesTot);
     tcbCyclesStart := old_t.(tcbCyclesStart);
     tcbStkBase := old_t.(tcbStkBase);
     tcbStkUsed := old_t.(tcbStkUsed);
     tcbPadding42 := old_t.(tcbPadding42);
     tcbPadding43 := old_t.(tcbPadding43);
     tcbEventMultiPtr := old_t.(tcbEventMultiPtr);
         curPrio := newPrio;
         stat := old_t.(stat);
         statPend := old_t.(statPend);
         dly := old_t.(dly);
         eventPtr := old_t.(eventPtr);
         eventMultiWaitEvents := old_t.(eventMultiWaitEvents);
         eventMultiRdy := old_t.(eventMultiRdy);
         msg := old_t.(msg);
         nextTCB := old_t.(nextTCB);
         prevTCB := old_t.(prevTCB);
         delReq := old_t.(delReq) |} ->
    st2 =
      {| inUsedTaskStates := fun tid' =>
           if Z.eqb tid' tid then Some new_t
           else st.(inUsedTaskStates) tid';
         unUsedTaskStates := st.(unUsedTaskStates);
         tcbListHead := st.(tcbListHead);
         prioTbl := fun p =>
           if Z.eqb p newPrio then PTTask tid else st.(prioTbl) p;
         taskRegNextID := st.(taskRegNextID);
         parkedTaskStacks := st.(parkedTaskStacks);
         taskLifecycle := st.(taskLifecycle);
     taskCount := st.(taskCount) |} ->
    verification_slice_task_validity sg st ->
    verification_slice_task_validity sg st2 ->
    (forall y, 0 <= encode_ready_tbl_at rl st y < 2 ^ 8) /\
    (forall y,
      0 <= encode_ready_tbl_at (Ucos2Verify.lib.helpers.remove_Z_eqb tid rl) st y < 2 ^ 8) /\
    (forall y,
      0 <= encode_ready_tbl_at
        (Ucos2Verify.lib.helpers.insert_sorted_by key tid (Ucos2Verify.lib.helpers.remove_Z_eqb tid rl)) st2 y < 2 ^ 8) /\
    0 <= encode_ready_grp rl st < 2 ^ 8 /\
    0 <= encode_ready_grp (Ucos2Verify.lib.helpers.remove_Z_eqb tid rl) st < 2 ^ 8 /\
    0 <= encode_ready_grp
      (Ucos2Verify.lib.helpers.insert_sorted_by key tid (Ucos2Verify.lib.helpers.remove_Z_eqb tid rl)) st2 < 2 ^ 8.
Proof.
  intros sg key rl st st2 tid old_t new_t newPrio Hin Hnd Hget
    Hnew Hst2 Hvalid Hvalid2.
  assert (Hndf : NoDup (Ucos2Verify.lib.helpers.remove_Z_eqb tid rl)).
  { apply Ucos2Verify.lib.helpers.remove_Z_eqb_NoDup. exact Hnd. }
  assert (Hnot : ~ In tid (Ucos2Verify.lib.helpers.remove_Z_eqb tid rl)).
  { apply Ucos2Verify.lib.helpers.remove_Z_eqb_notin. }
  assert (Hndpost :
    NoDup (Ucos2Verify.lib.helpers.insert_sorted_by key tid (Ucos2Verify.lib.helpers.remove_Z_eqb tid rl))).
  {
    apply Ucos2Verify.lib.helpers.insert_sorted_by_preserves_NoDup.
    - exact Hndf.
    - exact Hnot.
  }
  destruct Hvalid as [Hstate Hderived].
  unfold verification_slice_task_in_range in Hstate.
  destruct Hstate as
    [Hids [Hfree_nd [Hfree_range [Hfree_unused [Hprio [_ Huniq]]]]]].
  assert (Hrange : forall tid0 t0,
    st.(inUsedTaskStates) tid0 = Some t0 -> 0 <= t0.(curPrio)).
  {
    intros tid0 t0 Hget0.
    destruct (Hderived tid0 t0 Hget0) as [[Hp _] _]. exact Hp.
  }
  assert (Hdivrange : forall tid0 t0,
    st.(inUsedTaskStates) tid0 = Some t0 ->
    0 <= t0.(curPrio) / 8 < 8).
  {
    intros tid0 t0 Hget0.
    destruct (Hderived tid0 t0 Hget0) as [_ [_ [_ Hdiv]]]. exact Hdiv.
  }
  destruct Hvalid2 as [Hstate2 Hderived2].
  unfold verification_slice_task_in_range in Hstate2.
  destruct Hstate2 as
    [Hids2 [Hfree_nd2 [Hfree_range2 [Hfree_unused2 [Hprio2 [_ Huniq2]]]]]].
  assert (Hrange2 : forall tid0 t0,
    st2.(inUsedTaskStates) tid0 = Some t0 -> 0 <= t0.(curPrio)).
  {
    intros tid0 t0 Hget0.
    destruct (Hderived2 tid0 t0 Hget0) as [[Hp _] _]. exact Hp.
  }
  assert (Hdivrange2 : forall tid0 t0,
    st2.(inUsedTaskStates) tid0 = Some t0 ->
    0 <= t0.(curPrio) / 8 < 8).
  {
    intros tid0 t0 Hget0.
    destruct (Hderived2 tid0 t0 Hget0) as [_ [_ [_ Hdiv]]]. exact Hdiv.
  }
  split.
  - intro y. apply debug_encode_tbl_byte__relocation_semantics.
    + exact Hnd.
    + exact Huniq.
    + intros. eapply Hrange. eassumption.
  - split.
    + intro y. apply debug_encode_tbl_byte__relocation_semantics.
      * exact Hndf.
      * exact Huniq.
      * intros. eapply Hrange. eassumption.
    + split.
      * intro y. apply debug_encode_tbl_byte__relocation_semantics.
        -- exact Hndpost.
        -- exact Huniq2.
        -- intros. eapply Hrange2. eassumption.
      * split.
        -- apply debug_encode_grp_byte__relocation_semantics.
           intros. eapply Hdivrange. eassumption.
        -- split.
           ++ apply debug_encode_grp_byte__relocation_semantics.
              intros. eapply Hdivrange. eassumption.
           ++ apply debug_encode_grp_byte__relocation_semantics.
              intros. eapply Hdivrange2. eassumption.
Qed.
Lemma debug_atomic_ready_tbl_clear_formula__relocation_semantics :
  forall sg (key : TaskID -> Z) rl st st2 tid old_t new_t newPrio,
    In tid rl -> NoDup rl ->
    st.(inUsedTaskStates) tid = Some old_t ->
    new_t =
      {| taskID := old_t.(taskID);
     taskGeneration := old_t.(taskGeneration);
     tcbStkPtr := old_t.(tcbStkPtr);
     tcbExtPtr := old_t.(tcbExtPtr);
     tcbStkBottom := old_t.(tcbStkBottom);
     tcbStkSize := old_t.(tcbStkSize);
     tcbOpt := old_t.(tcbOpt);
     tcbPublicId := old_t.(tcbPublicId);
     tcbFlagNode := old_t.(tcbFlagNode);
     tcbFlagsRdy := old_t.(tcbFlagsRdy);
     tcbTaskName := old_t.(tcbTaskName);
     tcbReg0 := old_t.(tcbReg0);
     tcbCtxSwCtr := old_t.(tcbCtxSwCtr);
     tcbCyclesTot := old_t.(tcbCyclesTot);
     tcbCyclesStart := old_t.(tcbCyclesStart);
     tcbStkBase := old_t.(tcbStkBase);
     tcbStkUsed := old_t.(tcbStkUsed);
     tcbPadding42 := old_t.(tcbPadding42);
     tcbPadding43 := old_t.(tcbPadding43);
     tcbEventMultiPtr := old_t.(tcbEventMultiPtr);
         curPrio := newPrio;
         stat := old_t.(stat);
         statPend := old_t.(statPend);
         dly := old_t.(dly);
         eventPtr := old_t.(eventPtr);
         eventMultiWaitEvents := old_t.(eventMultiWaitEvents);
         eventMultiRdy := old_t.(eventMultiRdy);
         msg := old_t.(msg);
         nextTCB := old_t.(nextTCB);
         prevTCB := old_t.(prevTCB);
         delReq := old_t.(delReq) |} ->
    st2 =
      {| inUsedTaskStates := fun tid' =>
           if Z.eqb tid' tid then Some new_t
           else st.(inUsedTaskStates) tid';
         unUsedTaskStates := st.(unUsedTaskStates);
         tcbListHead := st.(tcbListHead);
         prioTbl := fun p =>
           if Z.eqb p newPrio then PTTask tid else st.(prioTbl) p;
         taskRegNextID := st.(taskRegNextID);
         parkedTaskStacks := st.(parkedTaskStacks);
         taskLifecycle := st.(taskLifecycle);
     taskCount := st.(taskCount) |} ->
    verification_slice_task_validity sg st ->
    verification_slice_task_validity sg st2 ->
    forall y,
      encode_ready_tbl_at (Ucos2Verify.lib.helpers.remove_Z_eqb tid rl) st y =
      if Z.eqb (old_t.(curPrio) / 8) y
      then Z.land (encode_ready_tbl_at rl st y)
        (unsigned_last_nbits
          (Z.lnot (Z.shiftl 1 (old_t.(curPrio) mod 8))) 8)
      else encode_ready_tbl_at rl st y.
Proof.
  intros sg key rl st st2 tid old_t new_t newPrio Hin Hnd Hget
    Hnew Hst2 Hvalid Hvalid2 y.
  destruct Hvalid as [Hstate Hderived].
  unfold verification_slice_task_in_range in Hstate.
  destruct Hstate as
    [Hids [Hfree_nd [Hfree_range [Hfree_unused [Hprio [_ Huniq]]]]]].
  assert (Hrange : forall tid0 t0, In tid0 rl ->
    st.(inUsedTaskStates) tid0 = Some t0 -> 0 <= t0.(curPrio)).
  {
    intros tid0 t0 Hin0 Hget0.
    destruct (Hderived tid0 t0 Hget0) as [[Hp _] _]. exact Hp.
  }
  destruct (Z.eqb (old_t.(curPrio) / 8) y) eqn:Hrow.
  - apply Z.eqb_eq in Hrow. subst y.
    eapply debug_ready_tbl_remove_selected_row__relocation_semantics; eassumption.
  - apply Z.eqb_neq in Hrow.
    eapply debug_ready_tbl_remove_other_row__relocation_semantics; eassumption.
Qed.
Lemma debug_ready_tid_not_event_wait__relocation_semantics :
  forall sg tskSt schedSt evSt tid t eid e,
    verification_slice_sched_in_range sg tskSt schedSt ->
    verification_slice_event_in_range sg tskSt evSt ->
    inUsedTaskStates tskSt tid = Some t ->
    In tid (readyList schedSt) ->
    inUsedEventStates evSt eid = Some e ->
    ~ In tid (waitList e).
Proof.
  intros sg tskSt schedSt evSt tid t eid e Hsched Hevent Hget Hin Hgetev Hwait.
  destruct Hsched as [Hall _].
  destruct (Hall tid Hin) as [t' [Hget' Hready]].
  rewrite Hget in Hget'. inversion Hget'; subst t'.
  destruct Hevent as [_ [_ [_ [_ [_ [_ [_ Hentry]]]]]]].
  specialize (Hentry eid e Hgetev).
  unfold Ucos2Verify.lib.event_wait.verification_slice_event_wait_entry_consistency in Hentry.
  destruct Hentry as [_ Hback].
  destruct (Ucos2Verify.lib.event_wait.event_type_to_pend_type (eventType e))
    as [pty|] eqn:Hpty.
  - destruct (Hback tid Hwait) as [tw [Hgetw [_ [_ Hpend]]]].
    rewrite Hget in Hgetw. inversion Hgetw; subst tw.
    unfold is_effectively_ready in Hready. rewrite Hpend in Hready.
    destruct pty; discriminate.
  - rewrite Hback in Hwait. contradiction.
Qed.
Lemma debug_event_grp_ext_in__relocation_semantics : forall l st1 st2,
  (forall tid, In tid l ->
    inUsedTaskStates st1 tid = inUsedTaskStates st2 tid) ->
  encode_event_wait_grp l st1 = encode_event_wait_grp l st2.
Proof.
  induction l as [|a rest IH]; intros st1 st2 Heq; simpl; [reflexivity|].
  rewrite (Heq a ltac:(left; reflexivity)).
  destruct (inUsedTaskStates st2 a); simpl.
  - f_equal. apply IH. intros; apply Heq; right; assumption.
  - apply IH. intros; apply Heq; right; assumption.
Qed.
Lemma debug_event_tbl_ext_in__relocation_semantics : forall l st1 st2 y,
  (forall tid, In tid l ->
    inUsedTaskStates st1 tid = inUsedTaskStates st2 tid) ->
  encode_event_wait_tbl_at l st1 y = encode_event_wait_tbl_at l st2 y.
Proof.
  intros l st1 st2 y Heq.
  unfold encode_event_wait_tbl_at.
  generalize 0 as acc. induction l as [|a rest IH]; intro acc; simpl; [reflexivity|].
  rewrite (Heq a ltac:(left; reflexivity)).
  apply IH. intros; apply Heq; right; assumption.
Qed.
Lemma debug_used_event_ext_in__relocation_semantics :
  forall sg st1 st2 base eid e,
    (forall tid, In tid (waitList e) ->
      inUsedTaskStates st1 tid = inUsedTaskStates st2 tid) ->
    used_complete_event sg st1 base eid e =
    used_complete_event sg st2 base eid e.
Proof.
  intros sg st1 st2 base eid e Heq.
  unfold used_complete_event.
  rewrite (debug_event_grp_ext_in__relocation_semantics _ _ _ Heq).
  rewrite (debug_event_tbl_ext_in__relocation_semantics _ _ _ 0 Heq).
  rewrite (debug_event_tbl_ext_in__relocation_semantics _ _ _ 1 Heq).
  rewrite (debug_event_tbl_ext_in__relocation_semantics _ _ _ 2 Heq).
  rewrite (debug_event_tbl_ext_in__relocation_semantics _ _ _ 3 Heq).
  rewrite (debug_event_tbl_ext_in__relocation_semantics _ _ _ 4 Heq).
  rewrite (debug_event_tbl_ext_in__relocation_semantics _ _ _ 5 Heq).
  rewrite (debug_event_tbl_ext_in__relocation_semantics _ _ _ 6 Heq).
  rewrite (debug_event_tbl_ext_in__relocation_semantics _ _ _ 7 Heq).
  reflexivity.
Qed.
Lemma debug_event_wait_entry_update_absent__relocation_semantics :
  forall sg st1 st2 changed eid e,
    (forall tid, tid <> changed ->
      inUsedTaskStates st1 tid = inUsedTaskStates st2 tid) ->
    ~ In changed (waitList e) ->
    Ucos2Verify.lib.event_wait.verification_slice_event_wait_entry_consistency sg st1 eid e ->
    Ucos2Verify.lib.event_wait.verification_slice_event_wait_entry_consistency sg st2 eid e.
Proof.
  intros sg st1 st2 changed eid e Heq Habsent Hentry.
  unfold Ucos2Verify.lib.event_wait.verification_slice_event_wait_entry_consistency in *.
  destruct Hentry as [[Hnd [Hsorted Hvalid]] Hback].
  split.
  - unfold Ucos2Verify.lib.event_wait.event_waitList_canonical.
    split; [exact Hnd|]. split.
    + eapply strictly_sorted_by_key_ext_in__relocation_semantics.
      * intros tid Hin. unfold Ucos2Verify.lib.event_wait.wait_prio_key.
        rewrite <- Heq; [reflexivity|]. intro; subst; contradiction.
      * exact Hsorted.
    + intros tid Hin. destruct (Hvalid tid Hin) as [t [Hget Hprio]].
      exists t. split; [rewrite <- Heq; auto|exact Hprio].
      intro; subst; contradiction.
  - destruct (Ucos2Verify.lib.event_wait.event_type_to_pend_type (eventType e));
      [|exact Hback].
    intros tid Hin. destruct (Hback tid Hin) as [t [Hget Hrest]].
    exists t. split; [rewrite <- Heq; auto|exact Hrest].
    intro; subst; contradiction.
Qed.
Lemma debug_event_in_range_update_absent__relocation_semantics :
  forall sg st1 st2 ev changed,
    (forall tid, tid <> changed ->
      inUsedTaskStates st1 tid = inUsedTaskStates st2 tid) ->
    (forall eid e, inUsedEventStates ev eid = Some e ->
      ~ In changed (waitList e)) ->
    verification_slice_event_in_range sg st1 ev ->
    verification_slice_event_in_range sg st2 ev.
Proof.
  intros sg st1 st2 ev changed Heq Habsent Hevent.
  destruct Hevent as [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
  split; [exact H7|].
  intros eid0 e0 Hget.
  eapply debug_event_wait_entry_update_absent__relocation_semantics; eauto.
Qed.
Lemma debug_store_used_event_map_ext__relocation_semantics :
  forall sg st1 st2 ev,
    (forall eid e, inUsedEventStates ev eid = Some e ->
      used_complete_event sg st1 (event_addr sg eid) eid e =
      used_complete_event sg st2 (event_addr sg eid) eid e) ->
    store_used_event_map sg st1 (inUsedEventStates ev) |--
    store_used_event_map sg st2 (inUsedEventStates ev).
Proof.
  intros sg st1 st2 ev Heq.
  unfold store_used_event_map, store_map.
  Intros l. Exists l. entailer!.
  assert (Hmap :
    map (fun eid =>
      match inUsedEventStates ev eid with
      | Some e => used_complete_event sg st1 (event_addr sg eid) eid e
      | None => emp
      end) l =
    map (fun eid =>
      match inUsedEventStates ev eid with
      | Some e => used_complete_event sg st2 (event_addr sg eid) eid e
      | None => emp
      end) l).
  {
    apply map_ext_in. intros eid Hin.
    destruct (inUsedEventStates ev eid) as [e|] eqn:Hget; [apply Heq; exact Hget|reflexivity].
  }
  rewrite Hmap. entailer!.
Qed.
Lemma debug_event_inv_update_absent__relocation_semantics :
  forall sg st1 st2 ev changed,
    (forall tid, tid <> changed ->
      inUsedTaskStates st1 tid = inUsedTaskStates st2 tid) ->
    (forall eid e, inUsedEventStates ev eid = Some e ->
      ~ In changed (waitList e)) ->
    verification_slice_event_inv sg st1 ev |-- verification_slice_event_inv sg st2 ev.
Proof.
  intros sg st1 st2 ev changed Heq Habsent.
  unfold verification_slice_event_inv. pureIntros.
  assert (Hv2 : verification_slice_event_in_range sg st2 ev).
  {
    unfold verification_slice_event_in_range in *.
    eapply debug_event_in_range_update_absent__relocation_semantics; eauto.
  }
  assert (Hstoreeq : forall eid e, inUsedEventStates ev eid = Some e ->
      used_complete_event sg st1 (event_addr sg eid) eid e =
      used_complete_event sg st2 (event_addr sg eid) eid e).
  {
    intros eid e Hget.
    apply debug_used_event_ext_in__relocation_semantics. intros tid Hin.
    apply Heq. intro; subst; exact (Habsent eid e Hget Hin).
  }
  pose proof (debug_store_used_event_map_ext__relocation_semantics sg st1 st2 ev Hstoreeq) as Hstore.
  sep_apply_l_atomic Hstore. entailer!.
Qed.
Lemma debug_ready_cross_preserved__relocation_semantics :
  forall sg ls1 ls2 restore_mid tid old_t newPrio,
    valid_stable_glob_vars sg ->
    verification_slice_sched_in_range sg (TskState ls1) (SchedState ls1) ->
    verification_slice_event_in_range sg (TskState ls1) (EventState ls1) ->
    verification_slice_task_validity sg (TskState ls2) ->
    verification_slice_sched_in_range sg (TskState ls2) (SchedState ls2) ->
    verification_slice_cross_module_consistency sg ls1 ->
    ready_owner_relocation_domain sg (TskState ls1) (SchedState ls1)
      tid old_t newPrio ->
    task_priority_relocation_legal sg ls1 tid newPrio ->
    mutex_ready_relocation_safe
      sg (EventState ls1) restore_mid tid old_t.(curPrio) newPrio ->
    atomic_task_set_curPrio_ready_owner_exec
      sg tid old_t newPrio ls1 tt ls2 ->
    verification_slice_cross_module_consistency sg ls2.
Proof.
  intros sg ls1 ls2 restore_mid tid old_t newPrio
    Hsg Hsched Hevent Htask2 Hsched2 Hcross Hdom Hlegal Hsafe Hat.
  unfold ready_owner_relocation_domain in Hdom.
  destruct Hdom as (Hget & Hin & Hnewvalid).
  unfold task_priority_relocation_legal in Hlegal.
  destruct Hlegal as
    (legal_t & Hlegal_get & Hlegal_slot & Hlegal_safe & Hlegal_old_alias).
  rewrite Hget in Hlegal_get. inversion Hlegal_get; subst legal_t.
  unfold atomic_task_set_curPrio_ready_owner_exec in Hat.
  destruct Hat as
    (new_t & Hin' & Hget' & Hlo & Hhi & Hnew & Heqpost).
  rewrite Hget in Hget'. inversion Hget'.
  cbv zeta in Heqpost.
  assert (Habsent : forall eid e,
      inUsedEventStates (EventState ls1) eid = Some e ->
      ~ In tid (waitList e)).
  {
    intros eid e Hgete.
    eapply debug_ready_tid_not_event_wait__relocation_semantics
      with (tskSt := TskState ls1) (schedSt := SchedState ls1)
           (evSt := EventState ls1) (t := old_t); eauto.
  }
  assert (Hready_mem : forall x,
      In x (readyList (SchedState ls2)) <->
      In x (readyList (SchedState ls1))).
  {
    intro x. rewrite Heqpost. cbn.
    rewrite Ucos2Verify.lib.helpers.insert_sorted_by_in.
    split.
    - intros [-> | Hrest].
      + exact Hin.
      + eapply Ucos2Verify.lib.helpers.remove_Z_eqb_in; eauto.
    - intro Hx. destruct (Z.eq_dec x tid) as [-> | Hne].
      + left; reflexivity.
      + right. eapply Ucos2Verify.lib.helpers.remove_Z_eqb_in_neq; eauto.
  }
  unfold verification_slice_cross_module_consistency in Hcross |- *.
  destruct Hcross as
    [H_osprio [H_pt [H_mo [H_mw [H_rlc [H_rlo
      [H_ceil [H_tpu [H_protocol H_pcp_unique]]]]]]]]].
  refine (conj _
    (conj _
      (conj _
        (conj _
          (conj _
            (conj _ (conj _ (conj _ (conj _ _))))))))).
  - unfold osprio_cur_consistency in H_osprio |- *.
    rewrite Heqpost. cbn.
    destruct (curTaskID (SchedState ls1)) as [current_tid |]
      eqn:Hcurrent_tid.
    + destruct H_osprio as (current_t & Hcurrent_get & Hcurrent_prio).
      destruct (Z.eqb current_tid tid) eqn:Hsame.
      * apply Z.eqb_eq in Hsame. subst current_tid.
        rewrite Hget in Hcurrent_get. inversion Hcurrent_get; subst current_t.
        exists new_t. split.
        -- reflexivity.
        -- unfold ready_owner_cur_prio_after.
           rewrite Hcurrent_tid, Z.eqb_refl, Hnew.
           reflexivity.
      * exists current_t. split.
        -- exact Hcurrent_get.
        -- unfold ready_owner_cur_prio_after.
           rewrite Hcurrent_tid, Hsame.
           exact Hcurrent_prio.
    + unfold ready_owner_cur_prio_after.
      rewrite Hcurrent_tid.
      exact H_osprio.
  - unfold priotbl_consistency in H_pt |- *.
    intro p. rewrite Heqpost. cbn.
    destruct (Z.eqb p newPrio) eqn:Hpeq.
    + apply Z.eqb_eq in Hpeq. subst p.
      exists new_t. split.
      * rewrite Z.eqb_refl. reflexivity.
      * left. rewrite Hnew. reflexivity.
    + apply Z.eqb_neq in Hpeq.
      specialize (H_pt p).
      destruct (prioTbl (TskState ls1) p) as [| |owner] eqn:Holdpt.
      * destruct H_pt as [Hno_ready Hno_mutex].
        split.
        -- intros (tid0 & Hin0 & t0 & Hget0 & Hprio0).
           apply Ucos2Verify.lib.helpers.insert_sorted_by_in in Hin0.
           destruct Hin0 as [Heqtid | Hrest].
           ++ subst tid0. rewrite Z.eqb_refl in Hget0.
              inversion Hget0; subst t0.
              rewrite Hnew in Hprio0. cbn in Hprio0.
              apply Hpeq. symmetry. exact Hprio0.
           ++ assert (Hne : tid0 <> tid).
              {
                intro; subst tid0.
                exact (Ucos2Verify.lib.helpers.remove_Z_eqb_notin tid _ Hrest).
              }
              rewrite (proj2 (Z.eqb_neq tid0 tid) Hne) in Hget0.
              apply Hno_ready. exists tid0. split.
              ** eapply Ucos2Verify.lib.helpers.remove_Z_eqb_in; eauto.
              ** exists t0. split; assumption.
        -- exact Hno_mutex.
      * destruct H_pt as (mid & e & m & Hgete & Htype & Hmf & Hpcp & Howner).
        exists mid, e, m. repeat split; try assumption.
        destruct (mfOwner m) as [owner|] eqn:Hown; [|exact I].
        destruct Howner as (to & op & Hgetto & Horig & Hcurop).
        destruct (Z.eqb owner tid) eqn:Howneq.
        -- apply Z.eqb_eq in Howneq. subst owner.
           rewrite Hget in Hgetto. inversion Hgetto; subst to.
           exists new_t, op. split.
           ++ reflexivity.
           ++ split; [exact Horig|].
              destruct Hsafe as [Heqprio | [Hchange [Hreason Howned]]].
              ** rewrite Hnew. cbn. rewrite <- Heqprio, Hcurop. reflexivity.
              ** specialize (Howned mid e m Hgete Htype Hmf Hown).
                 destruct Howned as [Horig_new | [Henabled Hpcp_new]].
                 --- rewrite Horig in Horig_new. inversion Horig_new; subst op.
                     rewrite Hnew. reflexivity.
                 --- exfalso. apply Hpeq.
                     rewrite <- Hpcp_new. symmetry. exact Hpcp.
        -- exists to, op. split.
           ++ exact Hgetto.
           ++ split; assumption.
      * destruct H_pt as (to & Hgetto & Hsource).
        destruct (Z.eqb owner tid) eqn:Howneq.
        -- apply Z.eqb_eq in Howneq. subst owner.
           rewrite Hget in Hgetto. inversion Hgetto; subst to.
           exists new_t. split.
           ++ reflexivity.
           ++ right.
              destruct Hsource as [Hcurp | Hmutexsrc].
              ** destruct Hsafe as [Heqprio | [Hchange [Hreason Howned]]].
                 --- exfalso. apply Hpeq.
                     rewrite <- Hcurp. exact Heqprio.
                 --- unfold mutex_target_restore_reason in Hreason.
                     destruct Hreason as
                       (e & m & Hgete & Htype & Hmf & Hown & Henabled & Hpcp & Horig).
                     exists restore_mid, e, m. repeat split; try assumption.
                     left. rewrite <- Hcurp. exact Hpcp.
              ** exact Hmutexsrc.
        -- exists to. split.
           ++ exact Hgetto.
           ++ exact Hsource.
  - unfold mutex_owner_consistency in H_mo |- *.
    intros mid e m Hprem.
    rewrite Heqpost in Hprem. cbn in Hprem.
    specialize (H_mo mid e m Hprem).
    destruct (mfOwner m) as [owner|] eqn:Hown; [|exact I].
    destruct H_mo as (to & op & Hgetto & Horig & Hcompat & Hnotin).
    destruct (Z.eqb owner tid) eqn:Howneq.
    + apply Z.eqb_eq in Howneq. subst owner.
      rewrite Hget in Hgetto. inversion Hgetto; subst to.
      exists new_t, op. split.
      * rewrite Heqpost. cbn. rewrite Z.eqb_refl. reflexivity.
      * split; [exact Horig|]. split.
        { destruct Hprem as [Hgete [Htype Hmf]].
          destruct Hsafe as [Heqprio | [Hchange [Hreason Howned]]].
          - rewrite Hnew. cbn. rewrite <- Heqprio. exact Hcompat.
          - specialize (Howned mid e m Hgete Htype Hmf Hown).
            destruct Howned as [Horig_new | [Henabled Hpcp_new]].
            + left. rewrite Horig in Horig_new. inversion Horig_new; subst op.
              rewrite Hnew. reflexivity.
            + right. split; [exact Henabled|].
              rewrite Hnew. symmetry. exact Hpcp_new. }
        exact Hnotin.
    + exists to, op. split.
      * rewrite Heqpost. cbn. rewrite Howneq. exact Hgetto.
      * split; [exact Horig|]. split; assumption.
  - unfold verification_slice_event_wait_object_consistency in H_mw |- *.
    destruct H_mw as [Hentries [Hrefback Hclosed]].
    split; [|split].
    + intros eid e Hgete.
      rewrite Heqpost in Hgete. cbn in Hgete.
      eapply debug_event_wait_entry_update_absent__relocation_semantics
        with (st1 := TskState ls1) (changed := tid).
      * intros tid0 Hne. rewrite Heqpost. cbn.
        rewrite (proj2 (Z.eqb_neq tid0 tid) Hne). reflexivity.
      * exact (Habsent eid e Hgete).
      * exact (Hentries eid e Hgete).
    + unfold Ucos2Verify.lib.event_wait.task_event_reference_backlink_consistency
        in Hrefback |- *.
      intros tid0 t0 eid e Hget0 Hgete Href.
      rewrite Heqpost in Hget0, Hgete. cbn in Hget0, Hgete.
      destruct (Z.eqb tid0 tid) eqn:Htid0.
      * apply Z.eqb_eq in Htid0. subst tid0.
        inversion Hget0; subst t0.
        rewrite Hnew in Href. cbn in Href.
        eapply Hrefback with (t := old_t) (e := e); eauto.
      * eapply Hrefback with (t := t0) (e := e); eauto.
    + unfold Ucos2Verify.lib.event_wait.task_event_reference_closure
        in Hclosed |- *.
      intros tid0 t0 Hget0.
      rewrite Heqpost in Hget0 |- *. cbn in Hget0 |- *.
      destruct (Z.eqb tid0 tid) eqn:Htid0.
      * apply Z.eqb_eq in Htid0. subst tid0.
        inversion Hget0; subst t0.
        specialize (Hclosed tid old_t Hget).
        rewrite Hnew. cbn. exact Hclosed.
      * eapply Hclosed. exact Hget0.
  - unfold ready_list_completeness.
    destruct Hsched2 as [_ [_ [Hcomplete _]]]. exact Hcomplete.
  - unfold ready_list_order.
    destruct Hsched2 as [_ [Hsorted [_ [Hnodup _]]]]. split; assumption.
  - unfold ceiling_priotbl_free in H_ceil |- *.
    rewrite Heqpost. cbn.
    assert (Hceil_ne : osPrioMutexCeilDis sg <> newPrio).
    {
      unfold valid_stable_glob_vars in Hsg.
      unfold verification_slice_priority_index in Hnewvalid.
      destruct Hsg as [_ [_ [_ [_ [_ [Hlowest [_ [_ [Hceil _]]]]]]]]].
      rewrite Hceil. rewrite Hlowest in Hnewvalid. lia.
    }
    rewrite (proj2 (Z.eqb_neq _ _) Hceil_ne). exact H_ceil.
  - unfold task_priority_unique_prop.
    destruct Htask2 as [Hrange2 _].
    unfold verification_slice_task_in_range in Hrange2.
    destruct Hrange2 as
      [_ [_ [_ [_ [_ [_ Hunique2]]]]]].
    exact Hunique2.
  - unfold mutex_protocol_consistency in H_protocol |- *.
    intros mid e m Hgete Htype Hfields.
    rewrite Heqpost in Hgete |- *. cbn in Hgete |- *.
    pose proof (H_protocol mid e m Hgete Htype Hfields) as
      [Hpcp_valid [Howner_shape Hpcp_slot]].
    refine (conj Hpcp_valid (conj Howner_shape _)).
    destruct Hpcp_slot as
      [Hdisabled | [Henabled [Hreserved | [owner [Howner_eq Howner_slot]]]]].
    + left. exact Hdisabled.
    + right. split; [exact Henabled|].
      destruct (Z.eqb (mfPCP m) newPrio) eqn:Hsame.
      * apply Z.eqb_eq in Hsame.
        rewrite Hsame in Hreserved.
        destruct Hlegal_slot as
          [Hdestination | [Hdestination Hclaim]].
        -- rewrite Hdestination in Hreserved. discriminate.
        -- right. exists tid. split.
           ++ unfold mutex_task_enabled_pcp_claim in Hclaim.
              destruct Hclaim as
                (claim_mid & claim_e & claim_m & Hclaim_get & Hclaim_type &
                 Hclaim_fields & Hclaim_owner & Hclaim_enabled & Hclaim_pcp).
              assert (Hmid : mid = claim_mid).
              {
                eapply H_pcp_unique.
                - exact Hgete.
                - exact Htype.
                - exact Hfields.
                - exact Hclaim_get.
                - exact Hclaim_type.
                - exact Hclaim_fields.
                - rewrite Hsame, Hclaim_pcp. reflexivity.
                - exact Henabled.
              }
              subst claim_mid.
              rewrite Hgete in Hclaim_get.
              inversion Hclaim_get; subst claim_e.
              rewrite Hfields in Hclaim_fields.
              inversion Hclaim_fields; subst claim_m.
              exact Hclaim_owner.
           ++ reflexivity.
      * left. exact Hreserved.
    + right. split; [exact Henabled|].
      destruct (Z.eqb (mfPCP m) newPrio) eqn:Hsame.
      * apply Z.eqb_eq in Hsame.
        rewrite Hsame in Howner_slot.
        destruct Hlegal_slot as
          [Hdestination | [Hdestination Hclaim]].
        -- rewrite Hdestination in Howner_slot.
           inversion Howner_slot; subst owner.
           right. exists tid. split; [exact Howner_eq|].
           reflexivity.
        -- rewrite Hdestination in Howner_slot. discriminate.
      * right. exists owner. split; [exact Howner_eq|].
        exact Howner_slot.
  - eapply mutex_enabled_pcp_unique_transport with (lvs1 := ls1).
    + intros mid e m Hget_post Htype Hfields.
      rewrite Heqpost in Hget_post. cbn in Hget_post.
      exists e, m. repeat split; assumption.
    + exact H_pcp_unique.
Qed.
Lemma debug_ready_post_properties__relocation_semantics :
  forall sg ls1 ls2 tid old_t newPrio,
    valid_stable_glob_vars sg ->
    verification_slice_task_validity sg (TskState ls1) ->
    verification_slice_sched_in_range sg (TskState ls1) (SchedState ls1) ->
    verification_slice_event_in_range sg (TskState ls1) (EventState ls1) ->
    verification_slice_cross_module_consistency sg ls1 ->
    ready_owner_relocation_domain sg (TskState ls1) (SchedState ls1)
      tid old_t newPrio ->
    task_priority_relocation_legal sg ls1 tid newPrio ->
    atomic_task_set_curPrio_ready_owner_exec
      sg tid old_t newPrio ls1 tt ls2 ->
    verification_slice_task_validity sg (TskState ls2) /\
    verification_slice_sched_in_range sg (TskState ls2) (SchedState ls2) /\
    verification_slice_event_in_range sg (TskState ls2) (EventState ls2).
Proof.
  intros sg ls1 ls2 tid old_t newPrio
    Hsg Htask Hsched Hevent Hcross Hdom Hlegal Hat.
  pose proof
    (ready_task_relocation_destination_unique_from_closure
      sg ls1 tid newPrio Htask Hlegal)
    as Hunique.
  unfold ready_owner_relocation_domain in Hdom.
  destruct Hdom as (Hget & Hin & Hnewvalid).
  unfold atomic_task_set_curPrio_ready_owner_exec in Hat.
  destruct Hat as
    (new_t & Hin' & Hget' & Hlo & Hhi & Hnew & Heqpost).
  rewrite Hget in Hget'. inversion Hget'.
  cbv zeta in Heqpost.
  assert (Htask2 : verification_slice_task_validity sg (TskState ls2)).
  {
    eapply OSMutex_RdyAtPrio_task_post_valid__relocation_semantics
      with (st := TskState ls1) (tid := tid) (old_t := old_t)
           (newPrio := newPrio) (new_t := new_t).
    - exact Hget. - exact Hnew.
    - rewrite Heqpost. reflexivity.
    - exact Hsg. - exact Htask. - exact Hnewvalid. - exact Hunique.
  }
  assert (Hsched2 : verification_slice_sched_in_range sg (TskState ls2) (SchedState ls2)).
  {
    eapply OSMutex_RdyAtPrio_sched_post_valid__relocation_semantics
      with (st := TskState ls1) (ss := SchedState ls1)
           (tid := tid) (old_t := old_t) (newPrio := newPrio)
           (new_t := new_t).
    - exact Hget. - exact Hin. - exact Hsched. - exact Hunique.
    - exact Hnew.
    - rewrite Heqpost. reflexivity.
    - rewrite Heqpost. reflexivity.
  }
  assert (Habsent : forall eid e,
      inUsedEventStates (EventState ls1) eid = Some e ->
      ~ In tid (waitList e)).
  {
    intros eid e Hgete.
    eapply debug_ready_tid_not_event_wait__relocation_semantics
      with (tskSt := TskState ls1) (schedSt := SchedState ls1)
           (evSt := EventState ls1) (t := old_t); eauto.
  }
  assert (Hevent2 : verification_slice_event_in_range sg (TskState ls2) (EventState ls2)).
  {
    rewrite Heqpost. cbn.
    unfold verification_slice_event_in_range in *.
    eapply debug_event_in_range_update_absent__relocation_semantics
      with (st1 := TskState ls1) (changed := tid).
    - intros tid' Hne. cbn.
      rewrite (proj2 (Z.eqb_neq tid' tid) Hne). reflexivity.
    - exact Habsent.
    - exact Hevent.
  }
  exact (conj Htask2 (conj Hsched2 Hevent2)).
Qed.
Lemma debug_ready_effect_post_properties__relocation_semantics :
  forall sg ls1 ls2 tid old_t newPrio,
    valid_stable_glob_vars sg ->
    verification_slice_task_validity sg (TskState ls1) ->
    verification_slice_sched_in_range sg (TskState ls1) (SchedState ls1) ->
    verification_slice_event_in_range sg (TskState ls1) (EventState ls1) ->
    verification_slice_cross_module_consistency sg ls1 ->
    ready_task_relocation_domain sg (TskState ls1) (SchedState ls1)
      tid old_t newPrio ->
    task_priority_relocation_legal sg ls1 tid newPrio ->
    OSMutex_RdyAtPrio_ready_effect
      sg tid old_t newPrio ls1 tt ls2 ->
    verification_slice_task_validity sg (TskState ls2) /\
    verification_slice_sched_in_range sg (TskState ls2) (SchedState ls2) /\
    verification_slice_event_in_range sg (TskState ls2) (EventState ls2).
Proof.
  intros sg ls1 ls2 tid old_t newPrio
    Hsg Htask Hsched Hevent Hcross Hdom Hlegal Heffect.
  unfold OSMutex_RdyAtPrio_ready_effect in Heffect.
  eapply debug_ready_post_properties__relocation_semantics; eauto.
  - eapply ready_task_relocation_domain_refines_ready_owner_domain.
    exact Hdom.
  - eapply current_ready_literal_exec_refines_ready_owner_exec.
    exact Heffect.
Qed.

Lemma debug_ready_effect_conditional_cross__relocation_semantics :
  forall sg ls1 ls2 restore_mid tid old_t newPrio,
    valid_stable_glob_vars sg ->
    verification_slice_task_validity sg (TskState ls1) ->
    verification_slice_sched_in_range sg (TskState ls1) (SchedState ls1) ->
    verification_slice_event_in_range sg (TskState ls1) (EventState ls1) ->
    verification_slice_cross_module_consistency sg ls1 ->
    ready_task_relocation_domain sg (TskState ls1) (SchedState ls1)
      tid old_t newPrio ->
    OSMutex_RdyAtPrio_ready_effect
      sg tid old_t newPrio ls1 tt ls2 ->
    task_priority_relocation_legal sg ls1 tid newPrio ->
    mutex_ready_relocation_safe
      sg (EventState ls1) restore_mid tid old_t.(curPrio) newPrio ->
    verification_slice_cross_module_consistency sg ls2.
Proof.
  intros sg ls1 ls2 restore_mid tid old_t newPrio
    Hsg Htask Hsched Hevent Hcross Hdom Heffect Hlegal Hsafe.
  pose proof (debug_ready_effect_post_properties__relocation_semantics
    sg ls1 ls2 tid old_t newPrio
      Hsg Htask Hsched Hevent Hcross Hdom Hlegal Heffect)
    as (Htask2 & Hsched2 & Hevent2).
  unfold OSMutex_RdyAtPrio_ready_effect in Heffect.
  eapply debug_ready_cross_preserved__relocation_semantics.
  - exact Hsg.
  - exact Hsched.
  - exact Hevent.
  - exact Htask2.
  - exact Hsched2.
  - exact Hcross.
  - eapply ready_task_relocation_domain_refines_ready_owner_domain.
    exact Hdom.
  - exact Hlegal.
  - exact Hsafe.
  - eapply current_ready_literal_exec_refines_ready_owner_exec.
    exact Heffect.
Qed.
Lemma debug_priority_encoding__relocation_semantics :
  forall sg p,
    valid_stable_glob_vars sg ->
    verification_slice_priority_index sg p ->
    Z.land p 7 = tcb_x_of_prio p /\
    Z.land (Z.shiftr p 3) 7 = tcb_y_of_prio p /\
    unsigned_last_nbits (Z.shiftl 1 (Z.land p 7)) 8 =
      tcb_bit_x_of_prio p /\
    unsigned_last_nbits (Z.shiftl 1 (Z.land (Z.shiftr p 3) 7)) 8 =
      tcb_bit_y_of_prio p.
Proof.
  intros sg p Hsg Hp.
  unfold verification_slice_priority_index in Hp.
  unfold valid_stable_glob_vars in Hsg.
  destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]].
  rewrite Hlowest in Hp.
  assert (Hx : Z.land p 7 = p mod 8).
  {
    replace 7 with (Z.ones 3) by reflexivity.
    rewrite Z.land_ones by lia. reflexivity.
  }
  assert (Hshift : Z.shiftr p 3 = p / 8).
  {
    rewrite Z.shiftr_div_pow2 by lia. reflexivity.
  }
  assert (HyRange : 0 <= p / 8 < 8).
  {
    split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; lia.
  }
  assert (Hy : Z.land (Z.shiftr p 3) 7 = p / 8).
  {
    rewrite Hshift.
    replace 7 with (Z.ones 3) by reflexivity.
    rewrite Z.land_ones by lia.
    apply Z.mod_small. exact HyRange.
  }
  assert (HxRange : 0 <= p mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  assert (Hbitx : unsigned_last_nbits (Z.shiftl 1 (Z.land p 7)) 8 =
      Z.shiftl 1 (p mod 8)).
  {
    rewrite Hx. apply unsigned_last_nbits_eq. split.
    - apply (proj2 (Z.shiftl_nonneg 1 (p mod 8))). lia.
    - rewrite Z.shiftl_mul_pow2 by lia.
      assert (2 ^ (p mod 8) < 2 ^ 8).
      { apply Z.pow_lt_mono_r; lia. }
      lia.
  }
  assert (Hbity :
      unsigned_last_nbits (Z.shiftl 1 (Z.land (Z.shiftr p 3) 7)) 8 =
      Z.shiftl 1 (p / 8)).
  {
    rewrite Hy. apply unsigned_last_nbits_eq. split.
    - apply (proj2 (Z.shiftl_nonneg 1 (p / 8))). lia.
    - rewrite Z.shiftl_mul_pow2 by lia.
      assert (2 ^ (p / 8) < 2 ^ 8).
      { apply Z.pow_lt_mono_r; lia. }
      lia.
  }
  unfold tcb_x_of_prio, tcb_y_of_prio,
    tcb_bit_x_of_prio, tcb_bit_y_of_prio.
  tauto.
Qed.
Lemma debug_extract_relocation_validities__relocation_semantics :
  forall sg ls tid,
    verification_slice_task_inv_no_tid_priotbl sg (TskState ls) tid **
    verification_slice_sched_inv_rest_ready_prio sg (TskState ls) (SchedState ls) **
    verification_slice_event_inv sg (TskState ls) (EventState ls)
    |--
    coq_prop
      (verification_slice_task_validity sg (TskState ls) /\
       verification_slice_sched_in_range sg (TskState ls) (SchedState ls) /\
       verification_slice_event_in_range sg (TskState ls) (EventState ls)) &&
    verification_slice_task_inv_no_tid_priotbl sg (TskState ls) tid **
    verification_slice_sched_inv_rest_ready_prio sg (TskState ls) (SchedState ls) **
    verification_slice_event_inv sg (TskState ls) (EventState ls).
Proof.
  intros sg ls tid.
  unfold verification_slice_task_inv_no_tid_priotbl, verification_slice_sched_inv_rest_ready_prio, verification_slice_event_inv.
  entailer!.
Qed.
Lemma debug_ready_transition_exists__relocation_semantics :
  forall sg ls tid old_t newPrio,
    ready_task_relocation_domain sg (TskState ls) (SchedState ls)
      tid old_t newPrio ->
    exists (new_t : TaskAbstractState) (ls2 : UCOS2_Verify_State),
      OSMutex_RdyAtPrio_ready_effect
        sg tid old_t newPrio ls tt ls2.
Proof.
  intros sg ls tid old_t newPrio Hdom.
  unfold ready_task_relocation_domain in Hdom.
  destruct Hdom as
    (Hget & Hin & Hcur & Hcurprio & Hvalid).
  unfold verification_slice_priority_index in Hvalid.
  set (new_t :=
    {| taskID := old_t.(taskID);
     taskGeneration := old_t.(taskGeneration);
     tcbStkPtr := old_t.(tcbStkPtr);
     tcbExtPtr := old_t.(tcbExtPtr);
     tcbStkBottom := old_t.(tcbStkBottom);
     tcbStkSize := old_t.(tcbStkSize);
     tcbOpt := old_t.(tcbOpt);
     tcbPublicId := old_t.(tcbPublicId);
     tcbFlagNode := old_t.(tcbFlagNode);
     tcbFlagsRdy := old_t.(tcbFlagsRdy);
     tcbTaskName := old_t.(tcbTaskName);
     tcbReg0 := old_t.(tcbReg0);
     tcbCtxSwCtr := old_t.(tcbCtxSwCtr);
     tcbCyclesTot := old_t.(tcbCyclesTot);
     tcbCyclesStart := old_t.(tcbCyclesStart);
     tcbStkBase := old_t.(tcbStkBase);
     tcbStkUsed := old_t.(tcbStkUsed);
     tcbPadding42 := old_t.(tcbPadding42);
     tcbPadding43 := old_t.(tcbPadding43);
     tcbEventMultiPtr := old_t.(tcbEventMultiPtr);
       curPrio := newPrio;
       stat := old_t.(stat);
       statPend := old_t.(statPend);
       dly := old_t.(dly);
       eventPtr := old_t.(eventPtr);
       eventMultiWaitEvents := old_t.(eventMultiWaitEvents);
       eventMultiRdy := old_t.(eventMultiRdy);
       msg := old_t.(msg);
       nextTCB := old_t.(nextTCB);
       prevTCB := old_t.(prevTCB);
       delReq := old_t.(delReq) |}).
  set (tskSt2 :=
    {| inUsedTaskStates := fun tid' =>
         if Z.eqb tid' tid then Some new_t
         else inUsedTaskStates (TskState ls) tid';
       unUsedTaskStates := unUsedTaskStates (TskState ls);
       tcbListHead := tcbListHead (TskState ls);
       prioTbl := fun p =>
         if Z.eqb p newPrio then PTTask tid else prioTbl (TskState ls) p;
       taskRegNextID := taskRegNextID (TskState ls);
       parkedTaskStacks := parkedTaskStacks (TskState ls);
       taskLifecycle := taskLifecycle (TskState ls);
     taskCount := taskCount (TskState ls) |}).
  set (newReady :=
    Ucos2Verify.lib.helpers.insert_sorted_by
      (fun tid' =>
         match inUsedTaskStates tskSt2 tid' with
         | Some t => curPrio t
         | None => osLowestPrio sg + 1
         end)
      tid
      (Ucos2Verify.lib.helpers.remove_Z_eqb tid
        (readyList (SchedState ls)))).
  set (schedSt2 :=
    {| readyList := newReady;
       curTaskID := curTaskID (SchedState ls);
       curSchedPrio := Some newPrio;
       highRdyTid :=
         match newReady with h :: _ => Some h | nil => None end;
       highRdyPrio :=
         match newReady with
         | h :: _ =>
             match inUsedTaskStates tskSt2 h with
             | Some t => Some (curPrio t)
             | None => None
             end
         | nil => None
         end;
       ctxSwCtr := ctxSwCtr (SchedState ls);
       isRunning := isRunning (SchedState ls) |}).
  exists new_t.
  exists
    {| IntrState := IntrState ls;
       TskState := tskSt2;
       SchedState := schedSt2;
       EventState := EventState ls;
       TickState := TickState ls;
       FlagState := ls.(FlagState);
       MemoryState := ls.(MemoryState);
       TimerState := ls.(TimerState);
       StatsState := ls.(StatsState);
       ControlState := ls.(ControlState);
       NameState := ls.(NameState) |}.
  unfold OSMutex_RdyAtPrio_ready_effect.
  unfold atomic_task_set_curPrio_ready_literal_exec.
  exists new_t.
  repeat split; try assumption; try reflexivity.
  + exact (proj1 Hvalid).
  + exact (proj2 Hvalid).
Qed.
Lemma debug_priotbl_rel_update_task__relocation_semantics :
  forall sg st st2 tid p l,
    valid_stable_glob_vars sg ->
    verification_slice_priority_index sg p ->
    prioTbl st2 =
      (fun q => if Z.eqb q p then PTTask tid else prioTbl st q) ->
    prio_tbl_list_rel sg st l ->
    prio_tbl_list_rel sg st2 (replace_Znth p (verification_slice_tcb_addr sg tid) l).
Proof.
  intros sg st st2 tid p l Hsg Hp Htbl Hrel.
  unfold verification_slice_priority_index in Hp.
  unfold valid_stable_glob_vars in Hsg.
  destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]].
  rewrite Hlowest in Hp.
  unfold prio_tbl_list_rel in Hrel |- *.
  destruct Hrel as [Hlen Hnth].
  split.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - intros q Hq.
    rewrite Htbl.
    destruct (Z.eq_dec q p) as [-> | Hne].
    + rewrite Ucos2Verify.lib.array_abstraction.Znth_replace_Znth_eq_gen by
        (rewrite Hlen; unfold OS_PRIO_TBL_SIZE; lia).
      rewrite Z.eqb_refl. reflexivity.
    + rewrite Ucos2Verify.lib.array_abstraction.Znth_replace_Znth_neq_gen.
      2: exact Hne.
      2: rewrite Hlen; exact Hq.
      2: rewrite Hlen; unfold OS_PRIO_TBL_SIZE; lia.
      rewrite Hnth by exact Hq.
      rewrite (proj2 (Z.eqb_neq q p) Hne). reflexivity.
Qed.
Lemma debug_task_residual_relocation__relocation_semantics :
  forall sg ls1 ls2 tid old_t new_t newPrio,
    new_t =
      {| taskID := old_t.(taskID);
     taskGeneration := old_t.(taskGeneration);
     tcbStkPtr := old_t.(tcbStkPtr);
     tcbExtPtr := old_t.(tcbExtPtr);
     tcbStkBottom := old_t.(tcbStkBottom);
     tcbStkSize := old_t.(tcbStkSize);
     tcbOpt := old_t.(tcbOpt);
     tcbPublicId := old_t.(tcbPublicId);
     tcbFlagNode := old_t.(tcbFlagNode);
     tcbFlagsRdy := old_t.(tcbFlagsRdy);
     tcbTaskName := old_t.(tcbTaskName);
     tcbReg0 := old_t.(tcbReg0);
     tcbCtxSwCtr := old_t.(tcbCtxSwCtr);
     tcbCyclesTot := old_t.(tcbCyclesTot);
     tcbCyclesStart := old_t.(tcbCyclesStart);
     tcbStkBase := old_t.(tcbStkBase);
     tcbStkUsed := old_t.(tcbStkUsed);
     tcbPadding42 := old_t.(tcbPadding42);
     tcbPadding43 := old_t.(tcbPadding43);
     tcbEventMultiPtr := old_t.(tcbEventMultiPtr);
         curPrio := newPrio;
         stat := old_t.(stat);
         statPend := old_t.(statPend);
         dly := old_t.(dly);
         eventPtr := old_t.(eventPtr);
         eventMultiWaitEvents := old_t.(eventMultiWaitEvents);
         eventMultiRdy := old_t.(eventMultiRdy);
         msg := old_t.(msg);
         nextTCB := old_t.(nextTCB);
         prevTCB := old_t.(prevTCB);
         delReq := old_t.(delReq) |} ->
    TskState ls2 =
      {| inUsedTaskStates := fun tid' =>
           if Z.eqb tid' tid then Some new_t
           else inUsedTaskStates (TskState ls1) tid';
         unUsedTaskStates := unUsedTaskStates (TskState ls1);
         tcbListHead := tcbListHead (TskState ls1);
         prioTbl := fun p =>
           if Z.eqb p newPrio then PTTask tid
           else prioTbl (TskState ls1) p;
         taskRegNextID := taskRegNextID (TskState ls1);
         parkedTaskStacks := parkedTaskStacks (TskState ls1);
         taskLifecycle := taskLifecycle (TskState ls1);
     taskCount := taskCount (TskState ls1) |} ->
    verification_slice_task_validity sg (TskState ls2) ->
    used_task_rdy_rest sg (verification_slice_tcb_addr sg tid) tid old_t **
    verification_slice_task_inv_no_tid_priotbl sg (TskState ls1) tid
    |--
    used_task_rdy_rest sg (verification_slice_tcb_addr sg tid) tid new_t **
    verification_slice_task_inv_no_tid_priotbl sg (TskState ls2) tid.
Proof.
  intros sg ls1 ls2 tid old_t new_t newPrio Hnew Htsk Hvalid.
  subst new_t.
  unfold verification_slice_task_inv_no_tid_priotbl, used_task_rdy_rest,
    verification_slice_store_used_task_map_missing_i.
  pureIntros.
  assert (Hother : forall tid', tid' <> tid ->
      inUsedTaskStates (TskState ls1) tid' =
      inUsedTaskStates (TskState ls2) tid').
  {
    intros tid' Hne. rewrite Htsk. cbn.
    rewrite (proj2 (Z.eqb_neq tid' tid) Hne). reflexivity.
  }
  pose proof (proj1 (store_map_missing_i_equiv
    (fun tid0 t => verification_slice_used_complete_task sg (verification_slice_tcb_addr sg tid0) tid0 t)
    (inUsedTaskStates (TskState ls1))
    (inUsedTaskStates (TskState ls2)) tid Hother)) as Hmissing.
  sep_apply_l_atomic Hmissing.
  rewrite Htsk. cbn.
  entailer!.
  rewrite <- Htsk. exact Hvalid.
Qed.
Lemma debug_zlist_replace__relocation_semantics :
  forall (l : list Z) oldi oldv i,
    0 <= oldi < Zlength l ->
    0 <= i < Zlength l ->
    Znth i (replace_Znth oldi oldv l) 0 =
      if Z.eqb oldi i then oldv else Znth i l 0.
Proof.
  intros l oldi oldv i Hold Hi.
  destruct (Z.eqb oldi i) eqn:Hoi.
  - apply Z.eqb_eq in Hoi. subst i.
    rewrite Ucos2Verify.lib.array_abstraction.Znth_replace_Znth_eq_gen by exact Hold. reflexivity.
  - apply Z.eqb_neq in Hoi.
    rewrite Ucos2Verify.lib.array_abstraction.Znth_replace_Znth_neq_gen; try assumption; congruence.
Qed.
Lemma debug_prio_rec__relocation_semantics :
  forall sg f n acc,
    verification_slice_prioTbl_to_addrs_rec sg f n acc =
      map (fun k => verification_slice_prio_tbl_entry_to_addr sg (f (Z.of_nat k)))
        (seq 0 n) ++ acc.
Proof.
  intros sg f n. induction n as [|n IH]; intro acc.
  - reflexivity.
  - simpl verification_slice_prioTbl_to_addrs_rec.
    rewrite IH, seq_S, map_app. simpl.
    rewrite <- app_assoc. reflexivity.
Qed.
Lemma debug_prio_canonical__relocation_semantics :
  forall sg st l,
    prio_tbl_list_rel sg st l ->
    l = verification_slice_prioTbl_to_addrs sg st.(prioTbl).
Proof.
  intros sg st l [Hlen Hnth].
  unfold verification_slice_prioTbl_to_addrs.
  rewrite debug_prio_rec__relocation_semantics.
  rewrite app_nil_r.
  apply (proj2 (list_eq_ext l
    (map (fun k => verification_slice_prio_tbl_entry_to_addr sg (st.(prioTbl) (Z.of_nat k)))
      (seq 0 64)) 0)).
  split.
  - rewrite Hlen, Zlength_correct, map_length, seq_length.
    reflexivity.
  - intros i Hi.
    assert (Hi64 : 0 <= i < OS_PRIO_TBL_SIZE).
    { rewrite <- Hlen. exact Hi. }
    unfold OS_PRIO_TBL_SIZE in Hi64.
    assert (Hin : (Z.to_nat i < 64)%nat).
    {
      change (Z.to_nat i < Z.to_nat 64)%nat.
      apply Z2Nat.inj_lt; lia.
    }
    specialize (Hnth i Hi64).
    rewrite Hnth.
    unfold Znth.
    rewrite map_nth_len with (dy := 0%nat).
    2: rewrite seq_length; exact Hin.
    rewrite seq_nth.
    2: exact Hin.
    simpl.
    rewrite Z2Nat.id by lia.
    reflexivity.
Qed.
Lemma debug_rdy_canonical__relocation_semantics :
  forall sg tskSt schedSt l,
    Ucos2Verify.lib.array_abstraction.osrdytbl_list_rel sg tskSt schedSt l ->
    l = (encode_ready_tbl_at schedSt.(readyList) tskSt 0 ::
         encode_ready_tbl_at schedSt.(readyList) tskSt 1 ::
         encode_ready_tbl_at schedSt.(readyList) tskSt 2 ::
         encode_ready_tbl_at schedSt.(readyList) tskSt 3 ::
         encode_ready_tbl_at schedSt.(readyList) tskSt 4 ::
         encode_ready_tbl_at schedSt.(readyList) tskSt 5 ::
         encode_ready_tbl_at schedSt.(readyList) tskSt 6 ::
         encode_ready_tbl_at schedSt.(readyList) tskSt 7 :: nil).
Proof.
  intros sg tskSt schedSt l [Hlen Hnth].
  apply (proj2 (list_eq_ext l
    (encode_ready_tbl_at schedSt.(readyList) tskSt 0 ::
     encode_ready_tbl_at schedSt.(readyList) tskSt 1 ::
     encode_ready_tbl_at schedSt.(readyList) tskSt 2 ::
     encode_ready_tbl_at schedSt.(readyList) tskSt 3 ::
     encode_ready_tbl_at schedSt.(readyList) tskSt 4 ::
     encode_ready_tbl_at schedSt.(readyList) tskSt 5 ::
     encode_ready_tbl_at schedSt.(readyList) tskSt 6 ::
     encode_ready_tbl_at schedSt.(readyList) tskSt 7 :: nil) 0)).
  split.
  - rewrite Hlen. unfold Ucos2Verify.lib.array_abstraction.OS_RDY_TBL_SIZE. reflexivity.
  - intros i Hi.
    assert (Hrange : 0 <= i < Ucos2Verify.lib.array_abstraction.OS_RDY_TBL_SIZE).
    { rewrite <- Hlen. exact Hi. }
    rewrite Hnth by exact Hrange.
    unfold Znth.
    replace i with (Z.of_nat (Z.to_nat i)) by
      (rewrite Z2Nat.id by lia; reflexivity).
    remember (Z.to_nat i) as n eqn:Hn.
    assert (Hn8 : (n < 8)%nat).
    {
      subst n.
      apply (proj1 (Z2Nat.inj_lt i 8 ltac:(lia) ltac:(lia))).
      unfold Ucos2Verify.lib.array_abstraction.OS_RDY_TBL_SIZE in Hrange.
      exact (proj2 Hrange).
    }
    do 8 (destruct n as [|n]; [reflexivity|]).
    lia.
Qed.
Lemma debug_sched_ready_prio_stage_merge__relocation_semantics :
  forall sg pre post oldT postT rdyL,
    verification_slice_sched_in_range sg postT post ->
    Ucos2Verify.lib.array_abstraction.osrdytbl_list_rel sg postT post rdyL ->
    curTaskID post = curTaskID pre ->
    ctxSwCtr post = ctxSwCtr pre ->
    isRunning post = isRunning pre ->
    sg.(g_OSRdyGrp) # UChar |->
      encode_ready_grp post.(readyList) postT **
    Ucos2Verify.lib.array_abstraction.store_osrdytbl sg rdyL **
    sg.(g_OSPrioCur) # UChar |->
      (match post.(curSchedPrio) with Some p => p | None => 0xFF end) **
    verification_slice_sched_inv_rest_ready_prio sg oldT pre
    |-- verification_slice_sched_inv_ready_prio_stage sg pre post postT.
Proof.
  intros sg pre post oldT postT rdyL Hvalid Hrdy Hcur Hctx Hrun.
  pose proof (debug_rdy_canonical__relocation_semantics sg postT post rdyL Hrdy) as Hrdycanon.
  rewrite Hrdycanon.
  unfold verification_slice_sched_inv_ready_prio_stage, verification_slice_sched_inv_rest_ready_prio.
  pureIntros.
  unfold verification_slice_store_sched_state_ready_prio_stage,
    verification_slice_store_sched_state_rest_ready_prio.
  unfold Ucos2Verify.lib.array_abstraction.store_osrdytbl, store_array, Ucos2Verify.lib.array_abstraction.osrdytbl_element_store,
    Ucos2Verify.lib.array_abstraction.sizeof_OS_PRIO.
  cbn [store_array_rec].
  rewrite Hcur, Hctx, Hrun.
  entailer!.
Qed.
Lemma debug_priority_fields_pack__relocation_semantics :
  forall prio_addr x_addr y_addr bitx_addr bity_addr
         prio_v x_v y_v bitx_v bity_v t,
    prio_v = t.(curPrio) ->
    x_v = tcb_x_of_prio t.(curPrio) ->
    y_v = tcb_y_of_prio t.(curPrio) ->
    bitx_v = tcb_bit_x_of_prio t.(curPrio) ->
    bity_v = tcb_bit_y_of_prio t.(curPrio) ->
    prio_addr # UChar |-> prio_v **
    x_addr # UChar |-> x_v **
    y_addr # UChar |-> y_v **
    bitx_addr # UChar |-> bitx_v **
    bity_addr # UChar |-> bity_v
    |-- used_task_priority_fields_at
      prio_addr x_addr y_addr bitx_addr bity_addr t.
Proof.
  intros. subst prio_v x_v y_v bitx_v bity_v.
  unfold used_task_priority_fields_at. entailer!.
Qed.
Lemma debug_sched_ready_prio_stage_merge_values__relocation_semantics :
  forall sg pre post oldT postT rdyL rdyGrp prioCur,
    verification_slice_sched_in_range sg postT post ->
    Ucos2Verify.lib.array_abstraction.osrdytbl_list_rel sg postT post rdyL ->
    rdyGrp = encode_ready_grp post.(readyList) postT ->
    prioCur =
      (match post.(curSchedPrio) with Some p => p | None => 0xFF end) ->
    curTaskID post = curTaskID pre ->
    ctxSwCtr post = ctxSwCtr pre ->
    isRunning post = isRunning pre ->
    sg.(g_OSRdyGrp) # UChar |-> rdyGrp **
    Ucos2Verify.lib.array_abstraction.store_osrdytbl sg rdyL **
    sg.(g_OSPrioCur) # UChar |-> prioCur **
    verification_slice_sched_inv_rest_ready_prio sg oldT pre
    |-- verification_slice_sched_inv_ready_prio_stage sg pre post postT.
Proof.
  intros. subst rdyGrp prioCur.
  apply debug_sched_ready_prio_stage_merge__relocation_semantics; assumption.
Qed.
Lemma debug_relocation_literal_stage_pack__relocation_semantics :
  forall sg ls0 ls_post,
    (interrupt_inv sg ls_post.(IntrState) **
    verification_slice_task_inv sg ls_post.(TskState) **
    verification_slice_sched_inv_ready_prio_stage
      sg ls0.(SchedState) ls_post.(SchedState) ls_post.(TskState) **
    verification_slice_event_inv sg ls_post.(TskState) ls_post.(EventState) **
    verification_slice_tick_inv sg ls_post.(TickState) **
    TT)
    |-- OSMutex_RdyAtPrio_literal_stage sg ls0 ls_post.
Proof.
  intros sg ls0 ls_post.
  unfold OSMutex_RdyAtPrio_literal_stage.
  entailer!.
Qed.

Lemma debug_truep_merge__relocation_semantics :
  (TT ** TT) |-- TT.
Proof.
  apply derivable1_truep_intros.
Qed.
Lemma debug_store_osrdytbl_merge_c_cell__relocation_semantics :
  forall sg l i v,
    Ucos2Verify.lib.array_abstraction.osrdytbl_index_in_range i ->
    Zlength l = Ucos2Verify.lib.array_abstraction.OS_RDY_TBL_SIZE ->
    (sg.(g_OSRdyTbl) + i * sizeof(UCHAR)) # UChar |-> v **
    Ucos2Verify.lib.array_abstraction.store_osrdytbl_missing_i sg l i
    |-- Ucos2Verify.lib.array_abstraction.store_osrdytbl sg (replace_Znth i v l).
Proof.
  intros sg l i v Hrange Hlen.
  change (Ucos2Verify.lib.array_abstraction.osrdytbl_element_store (g_OSRdyTbl sg) i v **
    Ucos2Verify.lib.array_abstraction.store_osrdytbl_missing_i sg l i |--
    Ucos2Verify.lib.array_abstraction.store_osrdytbl sg (replace_Znth i v l)).
  apply Ucos2Verify.lib.array_abstraction.store_osrdytbl_merge; assumption.
Qed.
Lemma debug_store_priotbl_merge_c_cell__relocation_semantics :
  forall sg l i v,
    Ucos2Verify.lib.array_abstraction.priotbl_index_in_range i ->
    Zlength l = OS_PRIO_TBL_SIZE ->
    (sg.(g_OSTCBPrioTbl) + i * sizeof(PTR)) # Ptr |-> v **
    verification_slice_store_priotbl_list_missing_i sg l i
    |-- verification_slice_store_priotbl_list sg (replace_Znth i v l).
Proof.
  intros sg l i v Hrange Hlen.
  change (priotbl_element_store (g_OSTCBPrioTbl sg) i v **
    verification_slice_store_priotbl_list_missing_i sg l i |--
    verification_slice_store_priotbl_list sg (replace_Znth i v l)).
  apply Ucos2Verify.lib.array_abstraction.verification_slice_store_priotbl_list_merge; assumption.
Qed.

(* The public domain is constructive for every ready owner, including the
   noncurrent family witnessed above.  This theorem records totality of the
   exact raw state transformer and deliberately assumes neither destination
   compatibility nor stable-invariant closure. *)
Lemma OSMutex_RdyAtPrio_ready_owner_transition_exists :
  forall sg ls tid old_t newPrio,
    ready_owner_relocation_domain
      sg ls.(TskState) ls.(SchedState) tid old_t newPrio ->
    exists (new_t : TaskAbstractState) (ls_post : UCOS2_Verify_State),
      atomic_task_set_curPrio_ready_owner_exec
        sg tid old_t newPrio ls tt ls_post.
Proof.
  intros sg ls tid old_t newPrio Hdom.
  unfold ready_owner_relocation_domain in Hdom.
  destruct Hdom as (Hget & Hin & Hvalid).
  unfold verification_slice_priority_index in Hvalid.
  set (new_t :=
    {| taskID := old_t.(taskID);
     taskGeneration := old_t.(taskGeneration);
     tcbStkPtr := old_t.(tcbStkPtr);
     tcbExtPtr := old_t.(tcbExtPtr);
     tcbStkBottom := old_t.(tcbStkBottom);
     tcbStkSize := old_t.(tcbStkSize);
     tcbOpt := old_t.(tcbOpt);
     tcbPublicId := old_t.(tcbPublicId);
     tcbFlagNode := old_t.(tcbFlagNode);
     tcbFlagsRdy := old_t.(tcbFlagsRdy);
     tcbTaskName := old_t.(tcbTaskName);
     tcbReg0 := old_t.(tcbReg0);
     tcbCtxSwCtr := old_t.(tcbCtxSwCtr);
     tcbCyclesTot := old_t.(tcbCyclesTot);
     tcbCyclesStart := old_t.(tcbCyclesStart);
     tcbStkBase := old_t.(tcbStkBase);
     tcbStkUsed := old_t.(tcbStkUsed);
     tcbPadding42 := old_t.(tcbPadding42);
     tcbPadding43 := old_t.(tcbPadding43);
     tcbEventMultiPtr := old_t.(tcbEventMultiPtr);
       curPrio := newPrio;
       stat := old_t.(stat);
       statPend := old_t.(statPend);
       dly := old_t.(dly);
       eventPtr := old_t.(eventPtr);
       eventMultiWaitEvents := old_t.(eventMultiWaitEvents);
       eventMultiRdy := old_t.(eventMultiRdy);
       msg := old_t.(msg);
       nextTCB := old_t.(nextTCB);
       prevTCB := old_t.(prevTCB);
       delReq := old_t.(delReq) |}).
  set (tskSt2 :=
    {| inUsedTaskStates := fun tid' =>
         if Z.eqb tid' tid then Some new_t
         else inUsedTaskStates (TskState ls) tid';
       unUsedTaskStates := unUsedTaskStates (TskState ls);
       tcbListHead := tcbListHead (TskState ls);
       prioTbl := fun p =>
         if Z.eqb p newPrio then PTTask tid else prioTbl (TskState ls) p;
       taskRegNextID := taskRegNextID (TskState ls);
       parkedTaskStacks := parkedTaskStacks (TskState ls);
       taskLifecycle := taskLifecycle (TskState ls);
     taskCount := taskCount (TskState ls) |}).
  set (newReady :=
    Ucos2Verify.lib.helpers.insert_sorted_by
      (fun tid' =>
         match inUsedTaskStates tskSt2 tid' with
         | Some t => curPrio t
         | None => osLowestPrio sg + 1
         end)
      tid
      (Ucos2Verify.lib.helpers.remove_Z_eqb tid
        (readyList (SchedState ls)))).
  set (schedSt2 :=
    {| readyList := newReady;
       curTaskID := curTaskID (SchedState ls);
       curSchedPrio := ready_owner_cur_prio_after
                         (SchedState ls) tid newPrio;
       highRdyTid := match newReady with h :: _ => Some h | nil => None end;
       highRdyPrio :=
         match newReady with
         | h :: _ =>
             match inUsedTaskStates tskSt2 h with
             | Some t => Some (curPrio t)
             | None => None
             end
         | nil => None
         end;
       ctxSwCtr := ctxSwCtr (SchedState ls);
       isRunning := isRunning (SchedState ls) |}).
  exists new_t.
  exists
    {| IntrState := IntrState ls;
       TskState := tskSt2;
       SchedState := schedSt2;
       EventState := EventState ls;
       TickState := TickState ls;
       FlagState := ls.(FlagState);
       MemoryState := ls.(MemoryState);
       TimerState := ls.(TimerState);
       StatsState := ls.(StatsState);
       ControlState := ls.(ControlState);
       NameState := ls.(NameState) |}.
  unfold atomic_task_set_curPrio_ready_owner_exec.
  exists new_t.
  repeat split; try assumption; try reflexivity.
  - exact (proj1 Hvalid).
  - exact (proj2 Hvalid).
Qed.

(* A public ready-owner execution can be reused by the established
   current-ready preservation development without changing the public call
   domain.  The current-ready and relocation-legal hypotheses occur only
   under [OSMutex_RdyAtPrio_conditional_preservation], so a noncurrent owner
   or a colliding destination still has the exact raw execution above. *)
Lemma OSMutex_RdyAtPrio_owner_effect_conditional_preservation :
  forall sg ls0 ls_post tid old_t newPrio,
    valid_stable_glob_vars sg ->
    verification_slice_task_validity sg ls0.(TskState) ->
    verification_slice_sched_in_range sg ls0.(TskState) ls0.(SchedState) ->
    verification_slice_event_in_range sg ls0.(TskState) ls0.(EventState) ->
    verification_slice_cross_module_consistency sg ls0 ->
    atomic_task_set_curPrio_ready_owner_exec
      sg tid old_t newPrio ls0 tt ls_post ->
    OSMutex_RdyAtPrio_conditional_preservation
      sg ls0 tid old_t newPrio ls_post.
Proof.
  intros sg ls0 ls_post tid old_t newPrio
    Hsg Htask Hsched Hevent Hcross Hraw.
  unfold OSMutex_RdyAtPrio_conditional_preservation.
  intros Hdom Hlegal.
  eapply debug_ready_post_properties__relocation_semantics.
  - exact Hsg.
  - exact Htask.
  - exact Hsched.
  - exact Hevent.
  - exact Hcross.
  - exact Hdom.
  - exact Hlegal.
  - exact Hraw.
Qed.

(* The analogous bridge for the cross-module protocol keeps mutex restore
   safety in the conditional closure layer.  It is deliberately absent from
   [ready_owner_relocation_domain] and from the raw transformer. *)
Lemma OSMutex_RdyAtPrio_owner_effect_conditional_cross :
  forall sg ls0 ls_post restore_mid tid old_t newPrio,
    valid_stable_glob_vars sg ->
    verification_slice_task_validity sg ls0.(TskState) ->
    verification_slice_sched_in_range sg ls0.(TskState) ls0.(SchedState) ->
    verification_slice_event_in_range sg ls0.(TskState) ls0.(EventState) ->
    verification_slice_cross_module_consistency sg ls0 ->
    atomic_task_set_curPrio_ready_owner_exec
      sg tid old_t newPrio ls0 tt ls_post ->
    OSMutex_RdyAtPrio_conditional_cross
      sg ls0 restore_mid tid old_t newPrio ls_post.
Proof.
  intros sg ls0 ls_post restore_mid tid old_t newPrio
    Hsg Htask Hsched Hevent Hcross Hraw.
  unfold OSMutex_RdyAtPrio_conditional_cross.
  intros Hdom Hlegal Hsafe.
  pose proof
    (debug_ready_post_properties__relocation_semantics
      sg ls0 ls_post tid old_t newPrio
      Hsg Htask Hsched Hevent Hcross Hdom Hlegal Hraw)
    as Hpost_properties.
  destruct Hpost_properties as (Htask2 & Hsched2 & _).
  eapply debug_ready_cross_preserved__relocation_semantics.
  - exact Hsg.
  - exact Hsched.
  - exact Hevent.
  - exact Htask2.
  - exact Hsched2.
  - exact Hcross.
  - exact Hdom.
  - exact Hlegal.
  - exact Hsafe.
  - exact Hraw.
Qed.

Lemma OSMutex_RdyAtPrio_owner_effect_conditional_ready_snapshot__owner_transition_return :
  forall sg ls0 ls_post tid old_t newPrio
         rdy_grp_in rdyL_in prio_cur_in
         tcb_y_in tcb_bitx_in tcb_bity_in
         tcb_y_out tcb_bitx_out tcb_bity_out
         rdy_tbl_y_in rdy_tbl_y_out
         rdy_tbl_new_y_in rdy_tbl_new_y_out
         rdy_grp_out rdyL_out,
    valid_stable_glob_vars sg ->
    verification_slice_task_validity sg ls0.(TskState) ->
    verification_slice_sched_in_range sg ls0.(TskState) ls0.(SchedState) ->
    verification_slice_event_in_range sg ls0.(TskState) ls0.(EventState) ->
    verification_slice_cross_module_consistency sg ls0 ->
    sched_ready_prio_snapshot_prop
      sg ls0.(TskState) ls0.(SchedState)
      rdy_grp_in rdyL_in prio_cur_in ->
    tcb_y_in = tcb_y_of_prio old_t.(curPrio) ->
    tcb_bitx_in = tcb_bit_x_of_prio old_t.(curPrio) ->
    tcb_bity_in = tcb_bit_y_of_prio old_t.(curPrio) ->
    tcb_y_out = Z.land (Z.shiftr newPrio 3) 7 ->
    tcb_bitx_out = Z.shiftl 1 (Z.land newPrio 7) ->
    tcb_bity_out = Z.shiftl 1 tcb_y_out ->
    Znth tcb_y_in rdyL_in 0 = rdy_tbl_y_in ->
    rdy_tbl_y_out =
      Z.land rdy_tbl_y_in
        (unsigned_last_nbits (Z.lnot tcb_bitx_in) 8) ->
    rdy_grp_out =
      ready_group_after_relocation
        rdy_grp_in rdy_tbl_y_out tcb_bity_in tcb_bity_out ->
    rdy_tbl_new_y_in =
      Znth tcb_y_out
        (replace_Znth tcb_y_in rdy_tbl_y_out rdyL_in) 0 ->
    rdy_tbl_new_y_out = Z.lor rdy_tbl_new_y_in tcb_bitx_out ->
    rdyL_out =
      replace_Znth tcb_y_out rdy_tbl_new_y_out
        (replace_Znth tcb_y_in rdy_tbl_y_out rdyL_in) ->
    atomic_task_set_curPrio_ready_owner_exec
      sg tid old_t newPrio ls0 tt ls_post ->
    OSMutex_RdyAtPrio_conditional_ready_snapshot
      sg ls0 tid old_t newPrio ls_post rdy_grp_out rdyL_out.
Proof.
  intros sg ls0 ls_post tid old_t newPrio
    rdy_grp_in rdyL_in prio_cur_in
    tcb_y_in tcb_bitx_in tcb_bity_in
    tcb_y_out tcb_bitx_out tcb_bity_out
    rdy_tbl_y_in rdy_tbl_y_out
    rdy_tbl_new_y_in rdy_tbl_new_y_out
    rdy_grp_out rdyL_out
    Hsg Htask Hsched Hevent Hcross Hsnap
    Holdy Holdbitx Holdbity Hnewy Hnewbitx Hnewbity
    Hrow Hclear Hgrp Hnewrow Hsetbit Hrdy Hraw.
  unfold OSMutex_RdyAtPrio_conditional_ready_snapshot.
  intros Hdom Hlegal.
  pose proof
    (OSMutex_RdyAtPrio_owner_effect_conditional_preservation
       sg ls0 ls_post tid old_t newPrio
       Hsg Htask Hsched Hevent Hcross Hraw)
    as Hpres.
  unfold OSMutex_RdyAtPrio_conditional_preservation in Hpres.
  specialize (Hpres Hdom Hlegal).
  destruct Hpres as (Htask2 & Hsched2 & Hevent2).
  destruct Hsnap as (Hgrp0 & Hrdy0 & Hcur0).
  unfold atomic_task_set_curPrio_ready_owner_exec in Hraw.
  destruct Hraw as
    (new_t & Hin & Hget & Hlo & Hhi & Hnew & Hpost).
  cbv zeta in Hpost.
  assert (Hvalidnew : verification_slice_priority_index sg newPrio).
  { unfold verification_slice_priority_index. tauto. }
  pose proof
    (debug_priority_encoding__relocation_semantics
       sg newPrio Hsg Hvalidnew)
    as (Hencx & Hency & Hencbitx & Hencbity).
  unfold tcb_y_of_prio in Holdy, Hency.
  unfold tcb_bit_x_of_prio, tcb_x_of_prio in Holdbitx.
  unfold tcb_bit_y_of_prio, tcb_y_of_prio in Holdbity.
  assert (HnewY : tcb_y_out = newPrio / 8).
  { rewrite Hnewy, Hency. reflexivity. }
  assert (HnewBitX : tcb_bitx_out = Z.shiftl 1 (newPrio mod 8)).
  { rewrite Hnewbitx, Hencx. unfold tcb_x_of_prio. reflexivity. }
  assert (HnewBitY : tcb_bity_out = Z.shiftl 1 (newPrio / 8)).
  { rewrite Hnewbity, HnewY. reflexivity. }
  assert (HtskEq :
    ls_post.(TskState) =
      {| inUsedTaskStates := fun tid' =>
           if Z.eqb tid' tid then Some new_t
           else ls0.(TskState).(inUsedTaskStates) tid';
         unUsedTaskStates := ls0.(TskState).(unUsedTaskStates);
         tcbListHead := ls0.(TskState).(tcbListHead);
         prioTbl := fun p =>
           if Z.eqb p newPrio then PTTask tid
           else ls0.(TskState).(prioTbl) p;
         taskRegNextID := ls0.(TskState).(taskRegNextID);
         parkedTaskStacks := ls0.(TskState).(parkedTaskStacks);
         taskLifecycle := ls0.(TskState).(taskLifecycle);
     taskCount := ls0.(TskState).(taskCount) |}).
  { rewrite Hpost. reflexivity. }
  assert (HreadyEq :
    ls_post.(SchedState).(readyList) =
      Ucos2Verify.lib.helpers.insert_sorted_by
        (fun tid' =>
           match ls_post.(TskState).(inUsedTaskStates) tid' with
           | Some t => t.(curPrio)
           | None => sg.(osLowestPrio) + 1
           end)
        tid
        (Ucos2Verify.lib.helpers.remove_Z_eqb
           tid ls0.(SchedState).(readyList))).
  { rewrite Hpost. reflexivity. }
  assert (HcurEq :
    ls_post.(SchedState).(curSchedPrio) =
      ready_owner_cur_prio_after ls0.(SchedState) tid newPrio).
  { rewrite Hpost. reflexivity. }
  pose proof Hsched as Hsched_entry.
  unfold verification_slice_sched_in_range in Hsched_entry.
  destruct Hsched_entry as (_ & _ & _ & Hnodup & _).
  pose proof
    (debug_atomic_ready_bitmap_correspondence__relocation_semantics
       sg
       (fun tid' =>
          match ls_post.(TskState).(inUsedTaskStates) tid' with
          | Some t => t.(curPrio)
          | None => sg.(osLowestPrio) + 1
          end)
       ls0.(SchedState).(readyList)
       ls0.(TskState) ls_post.(TskState)
       tid old_t new_t newPrio
       Hin Hnodup Hget Hnew HtskEq Htask Htask2)
    as (Htblcorr & Hgrpnz & Hgrpzero).
  destruct Hrdy0 as (Hrdylen & Hrdynth).
  pose proof Hsg as Hsg_fields.
  unfold valid_stable_glob_vars in Hsg_fields.
  destruct Hsg_fields as (_ & _ & _ & _ & _ & Hlowest & _).
  assert (HoldYRange : 0 <= old_t.(curPrio) / 8 < 8).
  {
    destruct Htask as (_ & Hderived).
    destruct (Hderived tid old_t Hget) as (_ & _ & _ & Hrange).
    exact Hrange.
  }
  assert (HnewYRange : 0 <= newPrio / 8 < 8).
  {
    unfold verification_slice_priority_index in Hvalidnew.
    rewrite Hlowest in Hvalidnew.
    split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia.
  }
  assert (HclearAbs :
    rdy_tbl_y_out =
      Z.land
        (encode_ready_tbl_at
           ls0.(SchedState).(readyList) ls0.(TskState)
           (old_t.(curPrio) / 8))
        (unsigned_last_nbits
           (Z.lnot (Z.shiftl 1 (old_t.(curPrio) mod 8))) 8)).
  {
    rewrite Hclear, <- Hrow, Holdy, Holdbitx.
    rewrite Hrdynth by exact HoldYRange.
    reflexivity.
  }
  assert (HrdyCanonical :
    rdyL_out =
      replace_Znth (newPrio / 8)
        (Z.lor
          (Znth (newPrio / 8)
            (replace_Znth (old_t.(curPrio) / 8)
              (Z.land
                (encode_ready_tbl_at
                  ls0.(SchedState).(readyList) ls0.(TskState)
                  (old_t.(curPrio) / 8))
                (unsigned_last_nbits
                  (Z.lnot (Z.shiftl 1 (old_t.(curPrio) mod 8))) 8))
              rdyL_in) 0)
          (Z.shiftl 1 (newPrio mod 8)))
        (replace_Znth (old_t.(curPrio) / 8)
          (Z.land
            (encode_ready_tbl_at
              ls0.(SchedState).(readyList) ls0.(TskState)
              (old_t.(curPrio) / 8))
            (unsigned_last_nbits
              (Z.lnot (Z.shiftl 1 (old_t.(curPrio) mod 8))) 8))
          rdyL_in)).
  {
    rewrite Hrdy, Hsetbit, Hnewrow, HnewY, Holdy,
      HnewBitX, HclearAbs.
    reflexivity.
  }
  unfold sched_ready_prio_snapshot_prop.
  split.
  - rewrite Hgrp.
    unfold ready_group_after_relocation.
    destruct (Z.eqb rdy_tbl_y_out 0) eqn:Hzero.
    + apply Z.eqb_eq in Hzero.
      assert (Hclearzero :
        Z.land
          (encode_ready_tbl_at
             ls0.(SchedState).(readyList) ls0.(TskState)
             (old_t.(curPrio) / 8))
          (unsigned_last_nbits
             (Z.lnot (Z.shiftl 1 (old_t.(curPrio) mod 8))) 8) = 0).
      { rewrite <- HclearAbs. exact Hzero. }
      specialize (Hgrpzero Hclearzero).
      rewrite <- HreadyEq in Hgrpzero.
      rewrite Hgrpzero, Hgrp0, Holdbity, HnewBitY.
      reflexivity.
    + apply Z.eqb_neq in Hzero.
      assert (Hclearnz :
        Z.land
          (encode_ready_tbl_at
             ls0.(SchedState).(readyList) ls0.(TskState)
             (old_t.(curPrio) / 8))
          (unsigned_last_nbits
             (Z.lnot (Z.shiftl 1 (old_t.(curPrio) mod 8))) 8) <> 0).
      { rewrite <- HclearAbs. exact Hzero. }
      specialize (Hgrpnz Hclearnz).
      rewrite <- HreadyEq in Hgrpnz.
      rewrite Hgrpnz, Hgrp0, HnewBitY.
      apply Z.lor_comm.
  - split.
    + unfold osrdytbl_list_rel.
      change (Zlength rdyL_in = 8) in Hrdylen.
      split.
      * rewrite HrdyCanonical, !Zlength_replace_Znth.
        exact Hrdylen.
      * intros y Hy.
        change (0 <= y < 8) in Hy.
        rewrite HreadyEq, Htblcorr, HrdyCanonical.
        assert (HclearLen :
          Zlength
            (replace_Znth (old_t.(curPrio) / 8)
              (Z.land
                (encode_ready_tbl_at
                  ls0.(SchedState).(readyList) ls0.(TskState)
                  (old_t.(curPrio) / 8))
                (unsigned_last_nbits
                  (Z.lnot (Z.shiftl 1 (old_t.(curPrio) mod 8))) 8))
              rdyL_in) = 8).
        { rewrite Zlength_replace_Znth. exact Hrdylen. }
        rewrite (debug_zlist_replace__relocation_semantics
          (replace_Znth (old_t.(curPrio) / 8)
            (Z.land
              (encode_ready_tbl_at
                ls0.(SchedState).(readyList) ls0.(TskState)
                (old_t.(curPrio) / 8))
              (unsigned_last_nbits
                (Z.lnot (Z.shiftl 1 (old_t.(curPrio) mod 8))) 8))
            rdyL_in)
          (newPrio / 8)
          (Z.lor
            (Znth (newPrio / 8)
              (replace_Znth (old_t.(curPrio) / 8)
                (Z.land
                  (encode_ready_tbl_at
                    ls0.(SchedState).(readyList) ls0.(TskState)
                    (old_t.(curPrio) / 8))
                  (unsigned_last_nbits
                    (Z.lnot (Z.shiftl 1 (old_t.(curPrio) mod 8))) 8))
                rdyL_in) 0)
            (Z.shiftl 1 (newPrio mod 8)))
          y).
        2: rewrite HclearLen; exact HnewYRange.
        2: rewrite HclearLen; exact Hy.
        destruct (Z.eqb (newPrio / 8) y) eqn:Hnewroweq.
        -- apply Z.eqb_eq in Hnewroweq. subst y.
           rewrite (debug_zlist_replace__relocation_semantics
             rdyL_in (old_t.(curPrio) / 8)
             (Z.land
               (encode_ready_tbl_at
                 ls0.(SchedState).(readyList) ls0.(TskState)
                 (old_t.(curPrio) / 8))
               (unsigned_last_nbits
                 (Z.lnot (Z.shiftl 1 (old_t.(curPrio) mod 8))) 8))
             (newPrio / 8)).
           2: rewrite Hrdylen; exact HoldYRange.
           2: rewrite Hrdylen; exact HnewYRange.
           destruct (Z.eqb (old_t.(curPrio) / 8) (newPrio / 8))
             eqn:Holdeq.
           ++ apply Z.eqb_eq in Holdeq.
              rewrite <- Holdeq.
              apply Z.lor_comm.
           ++ rewrite Hrdynth by exact HnewYRange.
              apply Z.lor_comm.
        -- rewrite (debug_zlist_replace__relocation_semantics
             rdyL_in (old_t.(curPrio) / 8)
             (Z.land
               (encode_ready_tbl_at
                 ls0.(SchedState).(readyList) ls0.(TskState)
                 (old_t.(curPrio) / 8))
               (unsigned_last_nbits
                 (Z.lnot (Z.shiftl 1 (old_t.(curPrio) mod 8))) 8))
             y).
           2: rewrite Hrdylen; exact HoldYRange.
           2: rewrite Hrdylen; exact Hy.
           destruct (Z.eqb (old_t.(curPrio) / 8) y) eqn:Holdeq.
           ++ apply Z.eqb_eq in Holdeq.
              rewrite Holdeq.
              reflexivity.
           ++ rewrite Hrdynth by exact Hy. reflexivity.
    + rewrite HcurEq. reflexivity.
Qed.
Lemma store_osrdytbl_missing_i_range__spatial_localization :
  forall sg l i,
    store_osrdytbl_missing_i sg l i |--
      coq_prop (osrdytbl_index_in_range i).
Proof.
  intros sg l i.
  unfold store_osrdytbl_missing_i, osrdytbl_index_in_range.
  assert (Hrange : forall (xs : list Z) (lo : Z),
    store_array_missing_i_rec osrdytbl_element_store
      (g_OSRdyTbl sg) i lo OS_RDY_TBL_SIZE xs |--
    coq_prop (lo <= i < OS_RDY_TBL_SIZE)).
  {
    intros xs.
    induction xs as [|a xs IH]; intros lo.
    - simpl. entailer!.
    - simpl. Split; Intros.
      + prop_apply store_array_rec_length.
        Intros. entailer!.
      + sep_apply IH.
        entailer!.
  }
  apply Hrange.
Qed.

Lemma OSMutex_RdyAtPrio_sched_rest_fold__return_transition_rebuild :
  forall sg tskSt schedSt tcbcur,
    verification_slice_sched_tcb_cur_snapshot_prop sg schedSt tcbcur ->
    sg.(g_OSTCBCur) # Ptr |-> tcbcur **
    verification_slice_sched_inv_rest_ready_current sg tskSt schedSt
    |-- verification_slice_sched_inv_rest_ready_prio sg tskSt schedSt.
Proof.
  intros sg tskSt schedSt tcbcur Hcur.
  unfold verification_slice_sched_tcb_cur_snapshot_prop in Hcur.
  unfold verification_slice_sched_inv_rest_ready_current, verification_slice_sched_inv_rest_ready_prio.
  pureIntros.
  unfold verification_slice_store_sched_state_rest_ready_current,
    verification_slice_store_sched_state_rest_ready_prio.
  rewrite Hcur.
  entailer!.
Qed.
Lemma OSMutex_RdyAtPrio_truep_contract_across__return_transition_rebuild :
  forall P : Assertion,
    TT ** (P ** TT) |-- P ** TT.
Proof.
  intros P.
  rewrite (logic_equiv_sepcon_swap (TT) P (TT)).
  sep_apply_l_atomic debug_truep_merge__relocation_semantics.
  entailer!.
Qed.
Lemma OSMutex_RdyAtPrio_entail_add_truep__return_transition_rebuild :
  forall P Q : Assertion,
    P |-- Q ->
    P |-- TT ** Q.
Proof.
  intros P Q H.
  unfold derivable1, sepcon, truep in *.
  intros m HP.
  destruct (unit_join m) as [u [Hu Hjoin]].
  exists u, m.
  split.
  - apply join_comm. exact Hjoin.
  - split; [exact I | apply H; exact HP].
Qed.
Lemma sched_ready_current_split__spatial_localization :
  forall sg tskSt schedSt,
    verification_slice_sched_inv sg tskSt schedSt |--
      sg.(g_OSRdyGrp) # UChar |->
        encode_ready_grp schedSt.(readyList) tskSt **
      store_osrdytbl sg
        [encode_ready_tbl_at schedSt.(readyList) tskSt 0;
         encode_ready_tbl_at schedSt.(readyList) tskSt 1;
         encode_ready_tbl_at schedSt.(readyList) tskSt 2;
         encode_ready_tbl_at schedSt.(readyList) tskSt 3;
         encode_ready_tbl_at schedSt.(readyList) tskSt 4;
         encode_ready_tbl_at schedSt.(readyList) tskSt 5;
         encode_ready_tbl_at schedSt.(readyList) tskSt 6;
         encode_ready_tbl_at schedSt.(readyList) tskSt 7] **
      sg.(g_OSPrioCur) # UChar |->
        (match schedSt.(curSchedPrio) with Some p => p | None => 255 end) **
      sg.(g_OSTCBCur) # Ptr |->
        (match schedSt.(curTaskID) with
         | Some tid => verification_slice_tcb_addr sg tid
         | None => 0
         end) **
      verification_slice_sched_inv_rest_ready_current sg tskSt schedSt.
Proof.
  intros.
  unfold verification_slice_sched_inv, verification_slice_store_sched_state,
    verification_slice_sched_inv_rest_ready_current, verification_slice_store_sched_state_rest_ready_current,
    store_osrdytbl, store_array, osrdytbl_element_store, sizeof_OS_PRIO.
  pureIntros.
  cbn [store_array_rec sizeof_front_end_type].
  entailer!.
Qed.
