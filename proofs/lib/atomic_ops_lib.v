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
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.event_multi.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.error_codes.
Import UCOS2_C_Rules.
Import TaskStateDef.
Import EventStateDef.
Import SchedStateDef.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope list.
Local Open Scope sac_scope.

(* ================================================================== *)
(* Phase 7 Task 7.1:atomic_priotbl_reserve                             *)
(* ================================================================== *)

(* atomic_priotbl_reserve:OSTCBPrioTbl[p] == 0 (PTFree) 时占用为 RESERVED     *)
(* 对应 OSMutexCreate line 226-231:if (OSTCBPrioTbl[prio] != 0) error; else reserved *)
Definition atomic_priotbl_reserve (p : Priority)
  : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    (lvs1.(TskState).(prioTbl)) p = PTFree /\
    lvs2 = replace_TskS
             {| inUsedTaskStates := lvs1.(TskState).(inUsedTaskStates);
                unUsedTaskStates := lvs1.(TskState).(unUsedTaskStates);
                tcbListHead      := lvs1.(TskState).(tcbListHead);
                prioTbl          := fun p' =>
                  if Z.eqb p' p then PTReserved
                  else (lvs1.(TskState).(prioTbl)) p';
                taskRegNextID := lvs1.(TskState).(taskRegNextID);
                parkedTaskStacks := lvs1.(TskState).(parkedTaskStacks);
                taskLifecycle := lvs1.(TskState).(taskLifecycle);
     taskCount        := lvs1.(TskState).(taskCount);
             |}
             lvs1.

(* ================================================================== *)
(* Phase 7 Task 7.2:atomic_event_alloc / free                         *)
(* ================================================================== *)

Definition atomic_event_alloc
  : program UCOS2_Verify_State EventID :=
  fun lvs1 eid lvs2 =>
    exists e_free rest,
      lvs1.(EventState).(unUsedEventStates) = e_free :: rest /\
      eid = e_free /\
      lvs2 = replace_EventS
               {| inUsedEventStates := fun eid' =>
                   if Z.eqb eid' eid
                   then Some {| eventGeneration := 0%nat;
                                eventName := 0; eventPadding1 := None; eventPadding2 := None;
     eventPadding3 := None; eventPadding19 := None;
                                eventType   := OS_EVENT_TYPE_UNUSED;
                                mutexFields := None;
                                semFields   := None;
                                mboxFields  := None;
                                queueFields := None;
                                waitList    := [];
                             |}
                   else (lvs1.(EventState).(inUsedEventStates)) eid';
                  eventLifecycle := lvs1.(EventState).(eventLifecycle);
                  publishedQueueBytes := lvs1.(EventState).(publishedQueueBytes);
                  unUsedEventStates := rest;
               |}
               lvs1.

(* ================================================================== *)
(* Phase 7 Task 7.3:atomic_mutex_init / acquire / release / transfer  *)
(* ================================================================== *)

Definition atomic_mutex_init (eid : EventID) (pcp : Priority)
  : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists e1 e2 m,
      (lvs1.(EventState).(inUsedEventStates)) eid = Some e1 /\
      e1.(eventType) = OS_EVENT_TYPE_UNUSED /\
      m = {| mfPCP := pcp; mfOwner := None; mfOwnerOrigPrio := None; |} /\
      e2 = {| eventGeneration := e1.(eventGeneration);
              eventName := e1.(eventName);
     eventPadding1 := e1.(eventPadding1);
     eventPadding2 := e1.(eventPadding2);
     eventPadding3 := e1.(eventPadding3);
     eventPadding19 := e1.(eventPadding19);
              eventType   := OS_EVENT_TYPE_MUTEX;
              mutexFields := Some m;
              semFields   := None;
              mboxFields  := None;
              queueFields := None;
              waitList    := [];
           |} /\
      lvs2 = update_event_field lvs1 eid e2.

(* atomic_mutex_acquire:mutex owner None→Some tid,同时不改 prioTbl/curPrio。
   协议前提(curTaskID/inUsedTaskStates/curPrio/task_non_suspension_bits)由 caller
   (OSMutexAccept_sem/OSMutexPend_sem)从 verification_slice_sched_inv 推导后传入,
   使 mutex_owner_consistency_preserved_by_acquire 可 Qed。
   priority-table 和 owner 协议的保持性由 cross_module_invariants.v 中
   已证明的 acquire 规则承担；这里仅保留原始可执行状态转换。 *)
Definition atomic_mutex_acquire (mid : EventID) (tid : TaskID) (origPrio : Priority)
  : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists e1 e2 m1 m2 t_acquire,
      (lvs1.(EventState).(inUsedEventStates)) mid = Some e1 /\
      e1.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e1.(mutexFields) = Some m1 /\ m1.(mfOwner) = None /\
      (* 跨切片协议前提 *)
      (lvs1.(SchedState).(curTaskID)) = Some tid /\
      (lvs1.(TskState).(inUsedTaskStates)) tid = Some t_acquire /\
      t_acquire.(curPrio) = origPrio /\
      (task_non_suspension_bits (t_acquire.(stat))) = 0 /\
      m2 = {| mfPCP := m1.(mfPCP); mfOwner := Some tid; mfOwnerOrigPrio := Some origPrio; |} /\
      e2 = {| eventGeneration := e1.(eventGeneration);
              eventName := e1.(eventName);
     eventPadding1 := e1.(eventPadding1);
     eventPadding2 := e1.(eventPadding2);
     eventPadding3 := e1.(eventPadding3);
     eventPadding19 := e1.(eventPadding19);
              eventType   := e1.(eventType);
              mutexFields := Some m2;
              semFields   := e1.(semFields);
              mboxFields  := e1.(mboxFields);
              queueFields := e1.(queueFields);
              waitList    := e1.(waitList);
           |} /\
      lvs2 = update_event_field lvs1 mid e2.

(* Source-exact empty-wait-list completion stage of OSMutexPost: clear the
   owner fields and, for an enabled PCP, release the PCP table entry back to
   [PTReserved].  The public semantics has already checked that the caller is
   the owner.  Priority restoration is only a preceding conditional call in
   the C source; nested/out-of-order release still executes this stage when
   the old owner's current priority differs from [mfOwnerOrigPrio].  Therefore
   old-owner lookup/equality is a protocol-closure condition, not a guard of
   this raw transformer. *)
Definition atomic_mutex_release (sg : StableGlobVars) (mid : EventID)
  : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists e1 e2 m1 m2 owner_tid evSt2 tskSt2,
      (lvs1.(EventState).(inUsedEventStates)) mid = Some e1 /\
      e1.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e1.(mutexFields) = Some m1 /\ e1.(waitList) = [] /\
      m1.(mfOwner) = Some owner_tid /\
      m2 = {| mfPCP := m1.(mfPCP); mfOwner := None; mfOwnerOrigPrio := None; |} /\
      e2 = {| eventGeneration := e1.(eventGeneration);
              eventName := e1.(eventName);
     eventPadding1 := e1.(eventPadding1);
     eventPadding2 := e1.(eventPadding2);
     eventPadding3 := e1.(eventPadding3);
     eventPadding19 := e1.(eventPadding19);
              eventType   := e1.(eventType);
              mutexFields := Some m2;
              semFields   := e1.(semFields);
              mboxFields  := e1.(mboxFields);
              queueFields := e1.(queueFields);
              waitList    := e1.(waitList);
           |} /\
      evSt2 = update_event_field_raw lvs1.(EventState) mid e2 /\
      tskSt2 = {| inUsedTaskStates := lvs1.(TskState).(inUsedTaskStates);
                  unUsedTaskStates := lvs1.(TskState).(unUsedTaskStates);
                  tcbListHead      := lvs1.(TskState).(tcbListHead);
                  prioTbl          := fun p =>
                    if (negb (Z.eqb m1.(mfPCP) sg.(osPrioMutexCeilDis))
                         && Z.eqb p m1.(mfPCP))%bool
                    then PTReserved
                    else (lvs1.(TskState).(prioTbl)) p;
                  taskRegNextID := lvs1.(TskState).(taskRegNextID);
                  parkedTaskStacks := lvs1.(TskState).(parkedTaskStacks);
                  taskLifecycle := lvs1.(TskState).(taskLifecycle);
     taskCount        := lvs1.(TskState).(taskCount);
               |} /\
      lvs2 = {| IntrState  := lvs1.(IntrState);
                TskState   := tskSt2;
                SchedState := lvs1.(SchedState);
                EventState := evSt2;
                TickState  := lvs1.(TickState);
                FlagState := lvs1.(FlagState);
                MemoryState := lvs1.(MemoryState);
                TimerState := lvs1.(TimerState);
                StatsState := lvs1.(StatsState);
                ControlState := lvs1.(ControlState);
                NameState := lvs1.(NameState);
             |}.

(* ================================================================== *)
(* Phase 17:atomic_mutex_query_step                                    *)
(* ================================================================== *)
(* 对应 OSMutexQuery(os_mutex.c:727-769)临界区内整段操作:               *)
(*   1. 已校验 eventType = MUTEX                                        *)
(*   2. 拷贝字段到 caller 的 p_mutex_data buffer                       *)
(*   3. 退出临界区                                                      *)
(*                                                                      *)
(* abstract state 不变(lvs2 = lvs1),因 caller 的 p_mutex_data buffer   *)
(* 不在 verification_slice_event_inv 持有的 SL 内存范围内。                                 *)
(*                                                                      *)
(* 在 C spec 中通过 atomic_cmd 包装后,以 safeExec(LastSeen(lvs1),      *)
(* atomic_cmd(atomic_mutex_query_step sg eid), X) 形式使用。            *)
Definition atomic_mutex_query_step (sg : StableGlobVars) (eid : EventID)
  : program UCOS2_Verify_State OSErrCode :=
  fun lvs1 ret lvs2 =>
    exists e,
      (lvs1.(EventState).(inUsedEventStates)) eid = Some e /\
      e.(eventType) = OS_EVENT_TYPE_MUTEX /\
      ret = OS_ERR_NONE /\
      lvs2 = lvs1.

(* ================================================================== *)
(* Phase 7 Task 7.4:atomic_task_set_curPrio(核心)                     *)
(* ================================================================== *)
(* 注:sg 作为参数,因为 StableGlobVars 不在 UCOS2_Verify_State 中        *)
(*                                                                    *)
(* Phase 7.5 Bug B 修复:补前置 In tid readyList。                     *)
(* 对应 C 代码 OSMutex_RdyAtPrio 的"task 必在 readyList"假设。         *)
(*                                                                    *)
(* Ready-task relocation, used by OSMutex_RdyAtPrio and by the common
   priority-inheritance path. *)
Definition atomic_task_set_curPrio_ready
  (sg : StableGlobVars) (tid : TaskID) (newPrio : Priority)
  : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists t oldPrio t',
      In tid lvs1.(SchedState).(readyList) /\
      (lvs1.(TskState).(inUsedTaskStates)) tid = Some t /\
      oldPrio = t.(curPrio) /\
      oldPrio <> newPrio /\
      0 <= newPrio /\ newPrio < sg.(osLowestPrio) /\
      ((lvs1.(TskState).(prioTbl)) newPrio = PTReserved \/
       (lvs1.(TskState).(prioTbl)) newPrio = PTTask tid) /\
      t' = {| taskID        := t.(taskID);
     taskGeneration := t.(taskGeneration);
     tcbStkPtr := t.(tcbStkPtr);
     tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom);
     tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt);
     tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode);
     tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName);
     tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr);
     tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart);
     tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr);
              curPrio        := newPrio;
              stat           := t.(stat);
              statPend       := t.(statPend);
              dly            := t.(dly);
              eventPtr       := t.(eventPtr);
              eventMultiWaitEvents  := t.(eventMultiWaitEvents);
              eventMultiRdy  := t.(eventMultiRdy);
              msg            := t.(msg);
              nextTCB        := t.(nextTCB);
              prevTCB        := t.(prevTCB);
              delReq         := t.(delReq);
           |} /\
      (let tskSt2 :=
         {| inUsedTaskStates := fun tid' =>
              if Z.eqb tid' tid then Some t'
              else (lvs1.(TskState).(inUsedTaskStates)) tid';
            unUsedTaskStates := lvs1.(TskState).(unUsedTaskStates);
            tcbListHead      := lvs1.(TskState).(tcbListHead);
            (* uC/OS-II keeps the owner's original-priority entry while the
               task inherits a mutex PCP. Release code updates the PCP entry
               after OSMutex_RdyAtPrio returns. *)
            prioTbl          := fun p =>
              if Z.eqb p newPrio then PTTask tid
              else (lvs1.(TskState).(prioTbl)) p;
            taskRegNextID := lvs1.(TskState).(taskRegNextID);
            parkedTaskStacks := lvs1.(TskState).(parkedTaskStacks);
            taskLifecycle := lvs1.(TskState).(taskLifecycle);
     taskCount        := lvs1.(TskState).(taskCount);
         |}
       in
       let schedSt1 := lvs1.(SchedState) in
       let filtered := remove_Z_eqb tid schedSt1.(readyList) in
       let newReadyList := insert_sorted_by
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
            curSchedPrio := match schedSt1.(curTaskID) with
                            | Some t'' => if Z.eqb t'' tid then Some newPrio
                                          else schedSt1.(curSchedPrio)
                            | None => schedSt1.(curSchedPrio)
                            end;
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
            isRunning    := schedSt1.(isRunning);
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
         NameState := lvs1.(NameState);
       |}).

(* Total abstract execution of the literal ready-task helper.  The shared
   relocation transformer above intentionally records a genuine priority
   change and therefore requires [old <> new].  The C helper nevertheless
   executes its clear/reinsert/field/table writes for every represented input,
   including [old = new].  In that equality case the final priority-table write
   can still change any destination entry to [PTTask tid], so the whole state
   must not be collapsed to identity.  In particular, the source contains no
   guard for [PTFree] or [PTTask other] destinations: those writes remain part
   of raw execution even when they break a stable task/mutex protocol.  Slot
   compatibility, priority uniqueness, and unchanged-event compatibility are
   theorem-side closure obligations expressed by
   [task_priority_relocation_legal] and [mutex_ready_relocation_safe]. *)
Definition atomic_task_set_curPrio_ready_literal_exec
  (sg : StableGlobVars) (tid : TaskID) (old_t : TaskAbstractState)
  (newPrio : Priority) : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists t',
      In tid lvs1.(SchedState).(readyList) /\
      lvs1.(SchedState).(curTaskID) = Some tid /\
      lvs1.(SchedState).(curSchedPrio) = Some old_t.(curPrio) /\
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
              delReq         := old_t.(delReq);
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
     taskCount        := lvs1.(TskState).(taskCount);
         |}
       in
       let schedSt1 := lvs1.(SchedState) in
       let filtered := remove_Z_eqb tid schedSt1.(readyList) in
       let newReadyList := insert_sorted_by
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
            (* The source writes OSPrioCur unconditionally.  This literal
               transformer is therefore current-ready-only and records that
               write directly. *)
            curSchedPrio := Some newPrio;
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
            isRunning    := schedSt1.(isRunning);
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
         NameState := lvs1.(NameState);
       |}).

(* Source-total current-TCB variant used by OSMutexPost.  The literal helper
   clears the old ready bit and then inserts the new bit even when the entry
   is a valid blocked-before-schedule stage and the current TCB is absent
   from the ready bitmap.  Therefore ready-list membership is not a raw
   execution guard.  Stable Post closure needs an explicit task-call
   boundary (or a larger exact transient); the current r21 public contract
   does not authorize adding that premise.  The older [_ready_literal_exec]
   relation above remains the ready-domain specialization consumed by
   existing shared preservation theorems. *)
Definition atomic_task_set_curPrio_current_literal_exec
  (sg : StableGlobVars) (tid : TaskID) (old_t : TaskAbstractState)
  (newPrio : Priority) : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists t',
      lvs1.(SchedState).(curTaskID) = Some tid /\
      lvs1.(SchedState).(curSchedPrio) = Some old_t.(curPrio) /\
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
              delReq         := old_t.(delReq);
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
     taskCount        := lvs1.(TskState).(taskCount);
         |}
       in
       let schedSt1 := lvs1.(SchedState) in
       let filtered := remove_Z_eqb tid schedSt1.(readyList) in
       let newReadyList := insert_sorted_by
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
            curSchedPrio := Some newPrio;
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
            isRunning    := schedSt1.(isRunning);
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
         NameState := lvs1.(NameState);
       |}).

Lemma atomic_task_set_curPrio_ready_literal_exec_sets_destination :
  forall sg tid old_t newPrio lvs1 lvs2,
    atomic_task_set_curPrio_ready_literal_exec
      sg tid old_t newPrio lvs1 tt lvs2 ->
    lvs2.(TskState).(prioTbl) newPrio = PTTask tid.
Proof.
  intros sg tid old_t newPrio lvs1 lvs2
    (t' & Hin & Hcur & Hcurprio & Hget & Hlo & Hhi & Hnew & Hpost).
  cbv zeta in Hpost.
  subst lvs2. cbn. rewrite Z.eqb_refl. reflexivity.
Qed.

(* On a genuine priority change, a closure-safe literal current-ready
   relocation refines the older shared relation.  The raw literal transformer
   itself has no destination-slot guard; [task_priority_relocation_legal] is
   required only here because the older relation and stable-invariant closure
   admit the compatible [PTTask tid]/owned-[PTReserved] cases.  The scheduler
   records then coincide because the current-task premise reduces the older
   conditional OSPrioCur update to the source's unconditional write. *)
Lemma atomic_task_set_curPrio_ready_literal_exec_neq_refines :
  forall sg tid old_t newPrio lvs1 lvs2,
    old_t.(curPrio) <> newPrio ->
    task_priority_relocation_legal sg lvs1 tid newPrio ->
    atomic_task_set_curPrio_ready_literal_exec
      sg tid old_t newPrio lvs1 tt lvs2 ->
    atomic_task_set_curPrio_ready sg tid newPrio lvs1 tt lvs2.
Proof.
  intros sg tid old_t newPrio lvs1 lvs2 Hneq Hlegal
    (t' & Hin & Hcur & Hcurprio & Hget & Hlo & Hhi & Hnew & Hpost).
  assert (Hslot :
    lvs1.(TskState).(prioTbl) newPrio = PTReserved \/
    lvs1.(TskState).(prioTbl) newPrio = PTTask tid).
  {
    unfold task_priority_relocation_legal in Hlegal.
    destruct Hlegal as
      (legal_t & Hlegal_get & [Htask_slot | [Hreserved Hclaim]] &
       Hrestore_safe & Hold_alias).
    - right. exact Htask_slot.
    - left. exact Hreserved.
  }
  unfold atomic_task_set_curPrio_ready.
  exists old_t, old_t.(curPrio), t'.
  repeat split; try assumption; try reflexivity.
  cbv zeta in Hpost |- *.
  rewrite Hcur in Hpost |- *.
  rewrite Z.eqb_refl.
  exact Hpost.
Qed.

(* Source-exact ready-owner relocation used by OSMutexDel(OS_DEL_ALWAYS).

   Unlike the Post/RdyAtPrio call above, the mutex owner passed by Del need
   not be the current task.  The C helper nevertheless writes [OSPrioCur]
   unconditionally, so this relation deliberately records
   [curSchedPrio := Some newPrio] while leaving [curTaskID] unchanged.  This
   can expose a scheduler-protocol violation when a non-current owner is
   restored; it must not be silently repaired by a conditional write in the
   raw transformer.

   The official Del contract assumes that an owner is ready-to-run.  Hence
   [In tid readyList] is the documented call protocol, while destination-slot
   compatibility and cross-mutex restoration safety remain separate
   invariant-closure obligations rather than execution guards. *)
Definition atomic_task_set_curPrio_ready_owner_literal_exec
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
              delReq         := old_t.(delReq);
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
     taskCount        := lvs1.(TskState).(taskCount);
         |}
       in
       let schedSt1 := lvs1.(SchedState) in
       let filtered := remove_Z_eqb tid schedSt1.(readyList) in
       let newReadyList := insert_sorted_by
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
            curSchedPrio := Some newPrio;
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
            isRunning    := schedSt1.(isRunning);
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
         NameState := lvs1.(NameState);
       |}).

(* Generic diagnostic consequence of the source-exact ready-owner helper.
   The official helper writes OSPrioCur to [newPrio] unconditionally, even
   when the ready owner being relocated is not OSTCBCur.  Consequently, if
   the untouched current task has a different priority, the post-state keeps
   [curTaskID = current_tid] but can no longer satisfy the scheduler's
   current-task/OSPrioCur consistency relation.  This is deliberately a
   theorem about raw execution, not an extra guard which would hide that
   execution from a caller.  The lookup/priority premises are direct
   projections of a stable scheduler/task pre-state. *)
Lemma atomic_task_set_curPrio_ready_owner_literal_exec_noncurrent_breaks_sched_current_consistency :
  forall sg owner_tid owner_t newPrio lvs1 lvs2
         current_tid current_t current_prio,
    owner_tid <> current_tid ->
    lvs1.(SchedState).(curTaskID) = Some current_tid ->
    lvs1.(TskState).(inUsedTaskStates) current_tid = Some current_t ->
    current_t.(curPrio) = current_prio ->
    newPrio <> current_prio ->
    atomic_task_set_curPrio_ready_owner_literal_exec
      sg owner_tid owner_t newPrio lvs1 tt lvs2 ->
    ~ sched_current_consistency lvs2.(TskState) lvs2.(SchedState).
Proof.
  intros sg owner_tid owner_t newPrio lvs1 lvs2
    current_tid current_t current_prio
    Hnoncurrent Hcurrent Hcurrent_lookup Hcurrent_prio Hnew_prio
    (owner_t' & Howner_ready & Howner_lookup & Hlo & Hhi &
     Howner_t' & Hpost).
  cbv zeta in Hpost.
  subst lvs2.
  unfold sched_current_consistency.
  cbn.
  rewrite Hcurrent.
  intros (post_current_t & Hpost_lookup & Hpost_prio).
  assert (Hids : Z.eqb current_tid owner_tid = false).
  {
    apply Z.eqb_neq.
    intros Heq.
    apply Hnoncurrent.
    symmetry; exact Heq.
  }
  rewrite Hids in Hpost_lookup.
  rewrite Hcurrent_lookup in Hpost_lookup.
  inversion Hpost_lookup; subst post_current_t.
  inversion Hpost_prio.
  apply Hnew_prio.
  rewrite <- Hcurrent_prio.
  assumption.
Qed.

(* Blocked-owner relocation from os_mutex.c:544-577.  The ready list and
   scheduler metadata are unchanged; the task is removed and reinserted in
   its single event wait list according to the inherited priority. *)
Definition atomic_task_set_curPrio_waiting
  (sg : StableGlobVars) (tid : TaskID) (newPrio : Priority)
  : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists t oldPrio t' wait_eid wait_e wait_e' tskSt2 evSt2 pty,
      ~ In tid lvs1.(SchedState).(readyList) /\
      lvs1.(TskState).(inUsedTaskStates) tid = Some t /\
      oldPrio = t.(curPrio) /\
      oldPrio <> newPrio /\
      0 <= newPrio /\ newPrio < sg.(osLowestPrio) /\
      (lvs1.(TskState).(prioTbl) newPrio = PTReserved \/
       lvs1.(TskState).(prioTbl) newPrio = PTTask tid) /\
      (task_non_suspension_bits t.(stat)) = task_pend_mask pty /\
      t.(eventPtr) = Some wait_eid /\
      t.(eventMultiWaitEvents) = [] /\
      lvs1.(EventState).(inUsedEventStates) wait_eid = Some wait_e /\
      event_type_to_pend_type wait_e.(eventType) = Some pty /\
      In tid wait_e.(waitList) /\
      t' = {| taskID        := t.(taskID);
     taskGeneration := t.(taskGeneration);
     tcbStkPtr := t.(tcbStkPtr);
     tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom);
     tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt);
     tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode);
     tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName);
     tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr);
     tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart);
     tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr);
              curPrio       := newPrio;
              stat          := t.(stat);
              statPend      := t.(statPend);
              dly           := t.(dly);
              eventPtr      := t.(eventPtr);
              eventMultiWaitEvents := t.(eventMultiWaitEvents);
              eventMultiRdy := t.(eventMultiRdy);
              msg           := t.(msg);
              nextTCB       := t.(nextTCB);
              prevTCB       := t.(prevTCB);
              delReq        := t.(delReq); |} /\
      tskSt2 =
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
     taskCount        := lvs1.(TskState).(taskCount); |} /\
      wait_e' =
        {| eventGeneration := wait_e.(eventGeneration);
           eventName := wait_e.(eventName);
     eventPadding1 := wait_e.(eventPadding1);
     eventPadding2 := wait_e.(eventPadding2);
     eventPadding3 := wait_e.(eventPadding3);
     eventPadding19 := wait_e.(eventPadding19);
           eventType   := wait_e.(eventType);
           mutexFields := wait_e.(mutexFields);
           semFields   := wait_e.(semFields);
           mboxFields  := wait_e.(mboxFields);
           queueFields := wait_e.(queueFields);
           waitList    := insert_sorted_by
                            (wait_prio_key sg tskSt2)
                            tid (remove_Z_eqb tid wait_e.(waitList)); |} /\
      evSt2 = update_event_field_raw lvs1.(EventState) wait_eid wait_e' /\
      lvs2 = {|
        IntrState  := lvs1.(IntrState);
        TskState   := tskSt2;
        SchedState := lvs1.(SchedState);
        EventState := evSt2;
        TickState  := lvs1.(TickState);
        FlagState := lvs1.(FlagState);
        MemoryState := lvs1.(MemoryState);
        TimerState := lvs1.(TimerState);
        StatsState := lvs1.(StatsState);
        ControlState := lvs1.(ControlState);
        NameState := lvs1.(NameState);
      |}.

(* A delayed, suspended, or flag-pending owner is neither ready nor linked
   through OSTCBEventPtr.  The source still updates its TCB priority and PCP
   table entry; the scheduler and event objects stay unchanged. *)
Definition atomic_task_set_curPrio_dormant
  (sg : StableGlobVars) (tid : TaskID) (newPrio : Priority)
  : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists t oldPrio t' tskSt2,
      ~ In tid lvs1.(SchedState).(readyList) /\
      lvs1.(TskState).(inUsedTaskStates) tid = Some t /\
      oldPrio = t.(curPrio) /\
      oldPrio <> newPrio /\
      0 <= newPrio /\ newPrio < sg.(osLowestPrio) /\
      (lvs1.(TskState).(prioTbl) newPrio = PTReserved \/
       lvs1.(TskState).(prioTbl) newPrio = PTTask tid) /\
      t.(eventPtr) = None /\
      t.(eventMultiWaitEvents) = [] /\
      is_effectively_ready t.(stat) t.(dly) = false /\
      t' = {| taskID        := t.(taskID);
     taskGeneration := t.(taskGeneration);
     tcbStkPtr := t.(tcbStkPtr);
     tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom);
     tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt);
     tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode);
     tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName);
     tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr);
     tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart);
     tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr);
              curPrio       := newPrio;
              stat          := t.(stat);
              statPend      := t.(statPend);
              dly           := t.(dly);
              eventPtr      := t.(eventPtr);
              eventMultiWaitEvents := t.(eventMultiWaitEvents);
              eventMultiRdy := t.(eventMultiRdy);
              msg           := t.(msg);
              nextTCB       := t.(nextTCB);
              prevTCB       := t.(prevTCB);
              delReq        := t.(delReq); |} /\
      tskSt2 =
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
     taskCount        := lvs1.(TskState).(taskCount); |} /\
      lvs2 = {|
        IntrState  := lvs1.(IntrState);
        TskState   := tskSt2;
        SchedState := lvs1.(SchedState);
        EventState := lvs1.(EventState);
        TickState  := lvs1.(TickState);
        FlagState := lvs1.(FlagState);
        MemoryState := lvs1.(MemoryState);
        TimerState := lvs1.(TimerState);
        StatsState := lvs1.(StatsState);
        ControlState := lvs1.(ControlState);
        NameState := lvs1.(NameState);
      |}.

Definition atomic_task_set_curPrio
  (sg : StableGlobVars) (tid : TaskID) (newPrio : Priority)
  : program UCOS2_Verify_State unit :=
  fun lvs1 u lvs2 =>
    atomic_task_set_curPrio_ready sg tid newPrio lvs1 u lvs2 \/
    atomic_task_set_curPrio_waiting sg tid newPrio lvs1 u lvs2 \/
    atomic_task_set_curPrio_dormant sg tid newPrio lvs1 u lvs2.

(* mutex_func_sem.v 只在 task_priority_relocation_legal 成立时证明完整
   invariant 保持；本文件中的 raw relation 不把该合法调用条件编码成
   源码执行分支，因此不会隐藏真实 C 行为。 *)

(** Selected live-TCB portions of OSTaskSuspend/Resume, before EXIT and
    the conditional OS_Sched call.  Public argument/SELF/priority-table
    selection and errors belong to the API prefix, not these endpoints.
    Suspend clears ready before setting SUSPEND.  Resume tests the actual
    remaining PEND_ANY bits and Dly; neither operation refreshes caches. *)
Definition atomic_task_suspend_selected (tid : TaskID) : program UCOS2_Verify_State unit :=
  fun entry (_ : unit) post => exists t,
    entry.(TskState).(inUsedTaskStates) tid = Some t /\
    post = task_suspend_state entry tid t.

Definition atomic_task_resume_selected (sg : StableGlobVars) (tid : TaskID)
  : program UCOS2_Verify_State unit :=
  fun entry (_ : unit) post => exists t,
    entry.(TskState).(inUsedTaskStates) tid = Some t /\ task_is_suspended t.(stat) = true /\
    post = task_resume_state sg entry tid t.

Lemma atomic_task_suspend_selected_task_update : forall tid entry post,
  atomic_task_suspend_selected tid entry tt post -> exists t,
    entry.(TskState).(inUsedTaskStates) tid = Some t /\
    post.(TskState) = glob_task_set_usedtask entry.(TskState) tid (task_suspend t) /\
    post.(SchedState).(readyList) = remove_Z_eqb tid entry.(SchedState).(readyList).
Proof. intros tid entry post [t [Ht ->]]; exists t; split; [exact Ht|]; split; reflexivity. Qed.

Lemma atomic_task_resume_selected_task_update : forall sg tid entry post,
  atomic_task_resume_selected sg tid entry tt post -> exists t,
    entry.(TskState).(inUsedTaskStates) tid = Some t /\ task_is_suspended t.(stat) = true /\
    post.(TskState) = glob_task_set_usedtask entry.(TskState) tid (task_resume t).
Proof. intros sg tid entry post [t [Ht [Hs ->]]]; exists t; split; [exact Ht|]; split; [exact Hs|reflexivity]. Qed.

Lemma atomic_task_resume_selected_ready_membership : forall sg tid entry post slot,
  atomic_task_resume_selected sg tid entry tt post -> exists t,
    entry.(TskState).(inUsedTaskStates) tid = Some t /\
    (In slot post.(SchedState).(readyList) <-> In slot entry.(SchedState).(readyList) \/
      (slot = tid /\ Z.land (encode_task_status t.(stat)) task_pend_any_mask = 0 /\ t.(dly) = 0)).
Proof.
  intros sg tid entry post slot [t [Ht [Hs ->]]]; exists t; split; [exact Ht|].
  apply sched_resume_task_ready_membership.
Qed.

Lemma atomic_task_suspend_selected_preserves_task_sched : forall sg tid entry post,
  atomic_task_suspend_selected tid entry tt post ->
  task_in_range sg entry.(TskState) -> sched_in_range sg entry.(TskState) entry.(SchedState) ->
  task_in_range sg post.(TskState) /\ sched_in_range sg post.(TskState) post.(SchedState).
Proof.
  intros sg tid entry post [t [Ht ->]] Htask Hsched; split.
  - eapply task_update_preserves_in_range; try eassumption; reflexivity.
  - eapply sched_remove_ready_task_preserves_in_range;
      [exact Hsched|exact Ht|reflexivity|apply task_suspend_not_ready].
Qed.

Lemma atomic_task_resume_selected_preserves_task_structure : forall sg tid entry post,
  atomic_task_resume_selected sg tid entry tt post ->
  task_in_range sg entry.(TskState) -> sched_ready_structure sg entry.(TskState) entry.(SchedState) ->
  task_in_range sg post.(TskState) /\ sched_ready_structure sg post.(TskState) post.(SchedState).
Proof.
  intros sg tid entry post [t [Ht [Hs ->]] ] Htask Hready; split.
  - eapply task_update_preserves_in_range; try eassumption; reflexivity.
  - eapply sched_ready_structure_update_task; [exact Ht|reflexivity|].
    unfold task_resume_state; cbn [replace_SchedS SchedState]; unfold sched_resume_task.
    destruct (task_resume_ready_test t); [|exact Hready].
    destruct Htask as [_ [_ [_ [_ [_ [_ [Hunique [Hpriority _]]]]]]]].
    eapply sched_wake_by_status_preserves_structure;
      [exact Hunique|exact Ht|exact (Hpriority tid t Ht)|exact Hready].
Qed.

Lemma atomic_task_suspend_selected_frame : forall sg tid entry post,
  atomic_task_suspend_selected tid entry tt post ->
  post = replace_TskS post.(TskState) (replace_SchedS post.(SchedState) entry) /\
  sched_physical_rep sg post.(SchedState) = sched_physical_rep sg entry.(SchedState).
Proof. intros sg tid entry post [t [_ ->]]; split; reflexivity. Qed.

Lemma atomic_task_resume_selected_frame : forall sg tid entry post,
  atomic_task_resume_selected sg tid entry tt post ->
  post = replace_SchedS post.(SchedState) (replace_TskS post.(TskState) entry) /\
  sched_physical_rep sg post.(SchedState) = sched_physical_rep sg entry.(SchedState).
Proof.
  intros sg tid entry post [t [_ [_ ->]]]; split; [reflexivity|].
  apply sched_resume_task_physical_rep_eq.
Qed.

(* ================================================================== *)
(* Phase 7 Task 7.5:atomic_mutex_inherit / restore + event 任务操作   *)
(* ================================================================== *)

Definition atomic_mutex_inherit (sg : StableGlobVars) (mid : EventID)
  : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists e m owner_tid,
      (lvs1.(EventState).(inUsedEventStates)) mid = Some e /\
      e.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e.(mutexFields) = Some m /\
      m.(mfOwner) = Some owner_tid /\
      m.(mfPCP) <> sg.(osPrioMutexCeilDis) /\
      atomic_task_set_curPrio sg owner_tid m.(mfPCP) lvs1 tt lvs2.

Definition atomic_mutex_restore (sg : StableGlobVars) (mid : EventID)
  : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists e m owner_tid origPrio,
      (lvs1.(EventState).(inUsedEventStates)) mid = Some e /\
      e.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e.(mutexFields) = Some m /\
      m.(mfOwner) = Some owner_tid /\
      m.(mfOwnerOrigPrio) = Some origPrio /\
      atomic_task_set_curPrio sg owner_tid origPrio lvs1 tt lvs2.

(** The Pend caller writes Stat/StatPend/Dly, then OS_EventTaskWait
    registers its EventPtr and wait bit and removes its ready bit.  A live
    current pointer is this internal operation's model domain, not a NULL
    check in the C helper.  No cache refresh or fabricated absence guard
    belongs to this step; the shared endpoint preserves every other owner. *)
Definition atomic_event_task_wait_kind
  (sg : StableGlobVars) (mid : EventID) (pty : PendType) (timeout : Z)
  : program UCOS2_Verify_State unit :=
  fun entry (_ : unit) post =>
    exists tid old e,
      entry.(SchedState).(curTaskID) = Some tid /\
      entry.(TskState).(inUsedTaskStates) tid = Some old /\
      entry.(EventState).(inUsedEventStates) mid = Some e /\
      post = event_pend_state sg entry mid e tid old pty timeout.

Definition atomic_event_task_wait_mutex (sg : StableGlobVars)
  (mid : EventID) (timeout : Z)
  : program UCOS2_Verify_State unit :=
  atomic_event_task_wait_kind sg mid PendMutex timeout.

(** Only the Event-registration while loop inside WaitMulti.  The TCB
    MultiPtr/MultiRdy stores precede this phase; ready removal follows it.
    This operation must not be mistaken for the complete C helper. *)
Definition atomic_event_multi_register_events (sg : StableGlobVars) (ids : list EventID)
  : program UCOS2_Verify_State unit :=
  fun entry (_ : unit) post =>
    exists tid t events,
      entry.(SchedState).(curTaskID) = Some tid /\
      entry.(TskState).(inUsedTaskStates) tid = Some t /\
      event_multi_wait_loop sg entry.(TskState) entry.(EventState) tid ids = Some events /\
      post = replace_EventS events entry.

Lemma atomic_event_multi_register_events_from_binding : forall sg entry tid t pointers instances,
  entry.(SchedState).(curTaskID) = Some tid ->
  entry.(TskState).(inUsedTaskStates) tid = Some t ->
  event_multi_array_binding sg entry.(EventState) pointers instances ->
  atomic_event_multi_register_events sg (map fst instances) entry tt
    (replace_EventS
      (event_multi_insert_waiters sg entry.(TskState) entry.(EventState) tid (map fst instances)) entry).
Proof.
  intros sg entry tid t pointers instances Hcur Ht Hbinding.
  exists tid, t, (event_multi_insert_waiters sg entry.(TskState) entry.(EventState) tid (map fst instances)).
  split; [exact Hcur|]; split; [exact Ht|]; split; [|reflexivity].
  exact (proj1 (event_multi_wait_loop_from_binding sg entry.(TskState)
    entry.(EventState) tid pointers instances Hbinding)).
Qed.

Lemma atomic_event_multi_register_events_frame : forall sg ids entry post,
  atomic_event_multi_register_events sg ids entry tt post ->
  post = replace_EventS post.(EventState) entry.
Proof. intros sg ids entry post [tid [t [events [_ [_ [_ ->]]]]]]; reflexivity. Qed.

(** Complete value-level WaitMulti helper: the caller has already written
    the status/result/delay prefix.  Array memory, its live-Event binding,
    and cross-schedule borrowing remain caller-owned proof obligations. *)
Definition event_multi_wait_state (entry : UCOS2_Verify_State)
  (tid : TaskID) (t : TaskAbstractState) (array : addr) (ids : list EventID)
  (events : Glob_EventAbstractState) : UCOS2_Verify_State :=
  replace_SchedS (sched_remove_ready_task entry.(SchedState) tid)
    (replace_TskS (glob_task_set_usedtask entry.(TskState) tid (task_set_multi_fields t array ids None))
      (replace_EventS events entry)).

Definition atomic_event_task_wait_multi (sg : StableGlobVars) (array : addr) (ids : list EventID)
  : program UCOS2_Verify_State unit :=
  fun entry (_ : unit) post => exists tid t events,
    entry.(SchedState).(curTaskID) = Some tid /\ entry.(TskState).(inUsedTaskStates) tid = Some t /\
    event_multi_wait_loop sg entry.(TskState) entry.(EventState) tid ids = Some events /\
    post = event_multi_wait_state entry tid t array ids events.

Lemma atomic_event_task_wait_multi_from_binding : forall sg entry tid t array pointers instances,
  entry.(SchedState).(curTaskID) = Some tid -> entry.(TskState).(inUsedTaskStates) tid = Some t ->
  event_multi_array_binding sg entry.(EventState) pointers instances ->
  atomic_event_task_wait_multi sg array (map fst instances) entry tt
    (event_multi_wait_state entry tid t array (map fst instances)
      (event_multi_insert_waiters sg entry.(TskState) entry.(EventState) tid (map fst instances))).
Proof.
  intros sg entry tid t array pointers instances Hcur Ht Hbinding.
  exists tid, t, (event_multi_insert_waiters sg entry.(TskState) entry.(EventState) tid (map fst instances)).
  split; [exact Hcur|]; split; [exact Ht|]; split; [|reflexivity].
  exact (proj1 (event_multi_wait_loop_from_binding sg entry.(TskState)
    entry.(EventState) tid pointers instances Hbinding)).
Qed.

Lemma atomic_event_task_wait_multi_image_step : forall sg array ids entry post,
  atomic_event_task_wait_multi sg array ids entry tt post -> exists tid t,
    entry.(TskState).(inUsedTaskStates) tid = Some t /\
    post.(TskState).(inUsedTaskStates) tid = Some (task_set_multi_fields t array ids None) /\
    event_multi_wait_step sg entry.(TskState) tid array ids (task_layout_image sg t)
      entry.(EventState) entry.(SchedState)
      (task_layout_image sg (task_set_multi_fields t array ids None)) post.(EventState) post.(SchedState).
Proof.
  intros sg array ids entry post [tid [t [events [Hcur [Ht [Hloop ->]]]]]].
  exists tid, t; split; [exact Ht|]; split.
  - simpl; rewrite Z.eqb_refl; reflexivity.
  - split; [exact Hcur|]; split; [apply task_register_multi_wait_image_eq|].
    split; [exact Hloop|reflexivity].
Qed.

Lemma atomic_event_task_wait_multi_frame : forall sg array ids entry post,
  atomic_event_task_wait_multi sg array ids entry tt post ->
  post = replace_SchedS post.(SchedState) (replace_TskS post.(TskState) (replace_EventS post.(EventState) entry)).
Proof. intros sg array ids entry post [tid [t [events [_ [_ [_ ->]]]]]]; reflexivity. Qed.

Lemma atomic_event_task_wait_multi_preserves_task_structure : forall sg array ids entry post,
  atomic_event_task_wait_multi sg array ids entry tt post ->
  task_in_range sg entry.(TskState) ->
  sched_ready_structure sg entry.(TskState) entry.(SchedState) ->
  task_in_range sg post.(TskState) /\
  sched_ready_structure sg post.(TskState) post.(SchedState).
Proof.
  intros sg array ids entry post [tid [t [events [_ [Ht [_ ->]]]]]] Htask Hready.
  split.
  - eapply task_set_multi_fields_preserves_in_range; eauto.
  - eapply sched_ready_structure_update_task; [exact Ht|reflexivity|].
    apply sched_remove_ready_preserves_structure; exact Hready.
Qed.

(** The already-selected, MultiPtr-non-NULL branch of EventTaskRdy on the
    canonical state.  Bitmap selection and the borrowed-array binding are
    separate entry obligations.  No current/high-ready cache is normalized
    and no remaining pending bit is dropped to manufacture readiness. *)
Definition event_multi_wake_state (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (tid : TaskID) (t : TaskAbstractState) (selected : EventID) (kind : PendType)
  (message : addr) (result : PendStatus) (events : Glob_EventAbstractState) : UCOS2_Verify_State :=
  let after := task_multi_wake t kind message result selected in
  replace_SchedS
    (sched_wake_by_status sg entry.(TskState) entry.(SchedState) tid
      (encode_task_status after.(stat)))
    (replace_TskS (glob_task_set_usedtask entry.(TskState) tid after)
      (replace_EventS events entry)).

Definition atomic_event_task_wake_multi (sg : StableGlobVars) (tid : TaskID)
  (selected : EventID) (kind : PendType) (message : addr) (result : PendStatus)
  : program UCOS2_Verify_State unit :=
  fun entry (_ : unit) post => exists t events,
    entry.(TskState).(inUsedTaskStates) tid = Some t /\ t.(tcbEventMultiPtr) <> 0 /\
    event_multi_remove_loop entry.(EventState) tid (selected :: t.(eventMultiWaitEvents)) = Some events /\
    post = event_multi_wake_state sg entry tid t selected kind message result events.

Lemma atomic_event_task_wake_multi_from_binding : forall sg entry tid t selected e kind message result pointers instances,
  entry.(TskState).(inUsedTaskStates) tid = Some t -> t.(tcbEventMultiPtr) <> 0 ->
  entry.(EventState).(inUsedEventStates) selected = Some e ->
  t.(eventMultiWaitEvents) = map fst instances ->
  event_multi_array_binding sg entry.(EventState) pointers instances ->
  atomic_event_task_wake_multi sg tid selected kind message result entry tt
    (event_multi_wake_state sg entry tid t selected kind message result
      (event_multi_remove_waiters entry.(EventState) tid (selected :: t.(eventMultiWaitEvents)))).
Proof.
  intros sg entry tid t selected e kind message result pointers instances Ht Hptr He Hids Hbinding.
  exists t, (event_multi_remove_waiters entry.(EventState) tid (selected :: t.(eventMultiWaitEvents))).
  split; [exact Ht|]; split; [exact Hptr|]; split; [|reflexivity].
  apply event_multi_remove_loop_eq_endpoint; constructor; [eauto|].
  pose proof (event_multi_array_binding_live sg entry.(EventState) pointers instances Hbinding) as Hlive.
  rewrite Hids, Forall_forall; rewrite Forall_forall in Hlive.
  intros eid Hin; apply in_map_iff in Hin; destruct Hin as [instance [<- Hin]].
  destruct (Hlive instance Hin) as [node [Hnode _]]; eauto.
Qed.

Lemma atomic_event_task_wake_multi_image_step : forall sg tid selected kind message result entry post,
  atomic_event_task_wake_multi sg tid selected kind message result entry tt post -> exists t,
    entry.(TskState).(inUsedTaskStates) tid = Some t /\
    post.(TskState).(inUsedTaskStates) tid = Some (task_multi_wake t kind message result selected) /\
    event_multi_wake_selected_step sg entry.(TskState) tid selected t.(tcbEventMultiPtr)
      t.(eventMultiWaitEvents) (encode_task_status t.(stat)) (task_pend_mask kind) message result
      (task_layout_image sg t) entry.(EventState) entry.(SchedState)
      (task_layout_image sg (task_multi_wake t kind message result selected))
      post.(EventState) post.(SchedState).
Proof.
  intros sg tid selected kind message result entry post [t [events [Ht [Hptr [Hloop ->]]]]].
  exists t; split; [exact Ht|]; split; [simpl; rewrite Z.eqb_refl; reflexivity|].
  split; [reflexivity|]; split; [reflexivity|]; split; [exact Hptr|].
  split; [apply task_multi_wake_layout_image_eq|]; split; [exact Hloop|].
  unfold event_multi_wake_state; cbn [replace_SchedS SchedState].
  change (sched_wake_by_status sg entry.(TskState) entry.(SchedState) tid
    (encode_task_status (task_clear_pending_status t.(stat) kind)) =
    sched_wake_by_status sg entry.(TskState) entry.(SchedState) tid
      (task_status_clear_wait (encode_task_status t.(stat)) (task_pend_mask kind))).
  rewrite task_clear_pending_status_encoding; reflexivity.
Qed.

Lemma atomic_event_task_wake_multi_ready_membership : forall sg tid selected kind message result entry post slot,
  atomic_event_task_wake_multi sg tid selected kind message result entry tt post -> exists t,
    entry.(TskState).(inUsedTaskStates) tid = Some t /\
    (In slot post.(SchedState).(readyList) <-> In slot entry.(SchedState).(readyList) \/
      (slot = tid /\ task_is_suspended t.(stat) = false)).
Proof.
  intros sg tid selected kind message result entry post slot [t [events [Ht [Hptr [Hloop ->]]]]].
  exists t; split; [exact Ht|].
  change (In slot (sched_wake_by_status sg entry.(TskState) entry.(SchedState) tid
    (encode_task_status (task_clear_pending_status t.(stat) kind))).(readyList) <->
    In slot entry.(SchedState).(readyList) \/ (slot = tid /\ task_is_suspended t.(stat) = false)).
  rewrite sched_wake_by_status_membership.
  change ((In slot entry.(SchedState).(readyList) \/
    (slot = tid /\ task_is_suspended (task_clear_pending_status t.(stat) kind) = false)) <->
    (In slot entry.(SchedState).(readyList) \/ (slot = tid /\ task_is_suspended t.(stat) = false))).
  rewrite task_clear_pending_status_preserves_suspension; reflexivity.
Qed.

Lemma atomic_event_task_wake_multi_clears_wait_set : forall sg tid selected kind message result entry post t,
  atomic_event_task_wake_multi sg tid selected kind message result entry tt post ->
  entry.(TskState).(inUsedTaskStates) tid = Some t ->
  Forall (fun eid => exists e, entry.(EventState).(inUsedEventStates) eid = Some e)
    (selected :: t.(eventMultiWaitEvents)) ->
  event_multi_wait_set entry.(EventState) tid t.(eventMultiWaitEvents) ->
  event_multi_wait_set post.(EventState) tid [].
Proof.
  intros sg tid selected kind message result entry post t
    [old [events [Hold [_ [Hloop ->]]]]] Ht Hlive Hset.
  assert (old = t) by congruence; subst old.
  rewrite (event_multi_remove_loop_eq_endpoint _ _ _ Hlive) in Hloop.
  injection Hloop as Hevents; subst events; intros eid e He; simpl.
  change ((event_multi_remove_waiters entry.(EventState) tid
    (selected :: t.(eventMultiWaitEvents))).(inUsedEventStates) eid = Some e) in He.
  assert (Habsent : ~ In tid e.(waitList)).
  { destruct (in_dec Z.eq_dec eid (selected :: t.(eventMultiWaitEvents))) as [Hin|Hnot].
    - exact (event_multi_remove_waiters_clears_member entry.(EventState) tid
        (selected :: t.(eventMultiWaitEvents)) eid e Hin He).
    - rewrite event_multi_remove_waiters_unlisted in He by exact Hnot.
      intro Hwait; apply Hnot; right; apply (proj1 (Hset eid e He)); exact Hwait. }
  tauto.
Qed.

Lemma atomic_event_task_wake_multi_preserves_task_structure : forall sg tid selected kind message result entry post,
  atomic_event_task_wake_multi sg tid selected kind message result entry tt post ->
  task_in_range sg entry.(TskState) ->
  sched_ready_structure sg entry.(TskState) entry.(SchedState) ->
  task_in_range sg post.(TskState) /\
  sched_ready_structure sg post.(TskState) post.(SchedState).
Proof.
  intros sg tid selected kind message result entry post [t [events [Ht [_ [_ ->]]]]] Htask Hready.
  split.
  - eapply task_update_preserves_in_range; try eassumption; reflexivity.
  - eapply sched_ready_structure_update_task; [exact Ht|reflexivity|].
    destruct Htask as [_ [_ [_ [_ [_ [_ [Hunique [Hpriority _]]]]]]]].
    eapply sched_wake_by_status_preserves_structure; [|exact Ht| |exact Hready].
    + exact Hunique.
    + exact (Hpriority tid t Ht).
Qed.

Lemma atomic_event_task_wake_multi_frame : forall sg tid selected kind message result entry post,
  atomic_event_task_wake_multi sg tid selected kind message result entry tt post ->
  post = replace_SchedS post.(SchedState) (replace_TskS post.(TskState) (replace_EventS post.(EventState) entry)) /\
  sched_physical_rep sg post.(SchedState) = sched_physical_rep sg entry.(SchedState).
Proof.
  intros sg tid selected kind message result entry post [t [events [_ [_ [_ ->]]]]].
  split; [reflexivity|apply sched_wake_by_status_physical_rep_eq].
Qed.

(* Single-Event compatibility relation for OS_EventTaskRdy.  Multi cleanup
   is modeled separately above; this legacy normalized-cache interface is
   not the full Multi-enabled source endpoint.

   The source obtains three observations which coincide only in a stable
   state:

   - [returned_prio] is decoded from the event wait bitmap;
   - [canonical_waiter] is the abstract waiter represented by that bit;
   - [table_owner] is read from OSTCBPrioTbl[returned_prio].

   The TCB and ready-bitmap effects target [table_owner], while the event
   bitmap/list effect removes [canonical_waiter].  Requiring the table slot
   to contain a live task classifies the normal-return path; PTFree,
   PTReserved, or a dangling TCB pointer is a source fault and is not assigned
   an arbitrary task identity.  No equality between the two task identities
   is assumed here.  Stable-state protocol closure is responsible for proving
   that equality when it is valid.

   OS_EventTaskRdy does not physically write
   OSPrioHighRdy/OSTCBHighRdy.  The abstract scheduler state below normalizes
   that cache pair to the new ready-list head so stable mathematical closure
   remains expressible even when OS_Sched is locked.  This is a logical
   normalization, not a C write: every concrete annotation for this
   intermediate state must use [verification_slice_sched_raw_ready_prio_stage] (via
   [UCOS2_verification_slice_raw_ready_prio_stage]), which anchors the two physical cache cells
   in the entry scheduler state.  Only a later enabled [atomic_sched] may
   expose the normalized pair through the ordinary full representation. *)
Definition atomic_event_task_rdy_one (sg : StableGlobVars)
  (mid : EventID) (pty : PendType) (msg : option addr)
  (pend_stat : PendStatus)
  (lvs1 : UCOS2_Verify_State) (returned_prio : Priority)
  (canonical_waiter table_owner : TaskID)
  (lvs2 : UCOS2_Verify_State) : Prop :=
    exists e1 e2 canonical_waiter_t table_owner_t table_owner_t',
      (lvs1.(EventState).(inUsedEventStates)) mid = Some e1 /\
      event_type_to_pend_type e1.(eventType) = Some pty /\
      e1.(waitList) <> [] /\
      canonical_waiter = List.hd 0 e1.(waitList) /\
      (lvs1.(TskState).(inUsedTaskStates)) canonical_waiter =
        Some canonical_waiter_t /\
      returned_prio = canonical_waiter_t.(curPrio) /\
      lvs1.(TskState).(prioTbl) returned_prio = PTTask table_owner /\
      (lvs1.(TskState).(inUsedTaskStates)) table_owner =
        Some table_owner_t /\
      table_owner_t.(curPrio) = returned_prio /\
      table_owner_t' = {| taskID        := table_owner_t.(taskID);
     taskGeneration := table_owner_t.(taskGeneration);
     tcbStkPtr := table_owner_t.(tcbStkPtr);
     tcbExtPtr := table_owner_t.(tcbExtPtr);
     tcbStkBottom := table_owner_t.(tcbStkBottom);
     tcbStkSize := table_owner_t.(tcbStkSize);
     tcbOpt := table_owner_t.(tcbOpt);
     tcbPublicId := table_owner_t.(tcbPublicId);
     tcbFlagNode := table_owner_t.(tcbFlagNode);
     tcbFlagsRdy := table_owner_t.(tcbFlagsRdy);
     tcbTaskName := table_owner_t.(tcbTaskName);
     tcbReg0 := table_owner_t.(tcbReg0);
     tcbCtxSwCtr := table_owner_t.(tcbCtxSwCtr);
     tcbCyclesTot := table_owner_t.(tcbCyclesTot);
     tcbCyclesStart := table_owner_t.(tcbCyclesStart);
     tcbStkBase := table_owner_t.(tcbStkBase);
     tcbStkUsed := table_owner_t.(tcbStkUsed);
     tcbPadding42 := table_owner_t.(tcbPadding42);
     tcbPadding43 := table_owner_t.(tcbPadding43);
     tcbEventMultiPtr := table_owner_t.(tcbEventMultiPtr);
              curPrio        := table_owner_t.(curPrio);
              stat           := task_clear_pending_status table_owner_t.(stat) pty;
              statPend       := pend_stat;
              dly            := 0;
              eventPtr       := None;
              eventMultiWaitEvents  := table_owner_t.(eventMultiWaitEvents);
              eventMultiRdy  := table_owner_t.(eventMultiRdy);
              msg            := msg;
              nextTCB        := table_owner_t.(nextTCB);
              prevTCB        := table_owner_t.(prevTCB);
              delReq         := table_owner_t.(delReq);
           |} /\
      e2 = {| eventGeneration := e1.(eventGeneration);
              eventName := e1.(eventName);
     eventPadding1 := e1.(eventPadding1);
     eventPadding2 := e1.(eventPadding2);
     eventPadding3 := e1.(eventPadding3);
     eventPadding19 := e1.(eventPadding19);
              eventType   := e1.(eventType);
              mutexFields := e1.(mutexFields);
              semFields   := e1.(semFields);
              mboxFields  := e1.(mboxFields);
              queueFields := e1.(queueFields);
              waitList    :=
                remove_Z_eqb canonical_waiter e1.(waitList);
           |} /\
      let schedSt1 := lvs1.(SchedState) in
      let ready_after :=
        if (task_is_suspended table_owner_t'.(stat))
        then schedSt1.(readyList)
        else insert_sorted_by
               (fun tid => match (lvs1.(TskState).(inUsedTaskStates)) tid with
                           | Some task => task.(curPrio)
                           | None => sg.(osLowestPrio) + 1
                           end)
               table_owner
               (remove_Z_eqb table_owner schedSt1.(readyList)) in
      let schedSt2 := {| readyList    := ready_after;
                         curTaskID    := schedSt1.(curTaskID);
                         curSchedPrio := schedSt1.(curSchedPrio);
                         highRdyTid   := match ready_after with
                                         | head :: _ => Some head
                                         | [] => None
                                         end;
                         highRdyPrio  := match ready_after with
                                         | head :: _ =>
                                             match
                                               (lvs1.(TskState).(inUsedTaskStates)) head
                                             with
                                             | Some headT =>
                                                 Some headT.(curPrio)
                                             | None => None
                                             end
                                         | [] => None
                                         end;
                         ctxSwCtr     := schedSt1.(ctxSwCtr);
                         isRunning    := schedSt1.(isRunning);
                      |} in
      lvs2 = {|
        IntrState  := lvs1.(IntrState);
        TskState   := {| inUsedTaskStates := fun tid =>
                           if Z.eqb tid table_owner
                           then Some table_owner_t'
                           else (lvs1.(TskState).(inUsedTaskStates)) tid;
                          unUsedTaskStates := lvs1.(TskState).(unUsedTaskStates);
                          tcbListHead      := lvs1.(TskState).(tcbListHead);
                          prioTbl          := lvs1.(TskState).(prioTbl);
                          taskRegNextID := lvs1.(TskState).(taskRegNextID);
                          parkedTaskStacks := lvs1.(TskState).(parkedTaskStacks);
                          taskLifecycle := lvs1.(TskState).(taskLifecycle);
     taskCount        := lvs1.(TskState).(taskCount);
                       |};
        SchedState := schedSt2;
        EventState := update_event_field_raw lvs1.(EventState) mid e2;
        TickState  := lvs1.(TickState);
        FlagState := lvs1.(FlagState);
        MemoryState := lvs1.(MemoryState);
        TimerState := lvs1.(TimerState);
        StatsState := lvs1.(StatsState);
        ControlState := lvs1.(ControlState);
        NameState := lvs1.(NameState);
      |}.

Definition atomic_event_task_rdy (sg : StableGlobVars)
  (mid : EventID) (pend_stat : PendStatus)
  (lvs1 : UCOS2_Verify_State) (returned_prio : Priority)
  (canonical_waiter table_owner : TaskID)
  (lvs2 : UCOS2_Verify_State) : Prop :=
  atomic_event_task_rdy_one
    sg mid PendMutex None pend_stat lvs1 returned_prio
    canonical_waiter table_owner lvs2.

Definition atomic_event_task_remove (tid : TaskID) (mid : EventID)
  : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists e1 e2 t t',
      (lvs1.(EventState).(inUsedEventStates)) mid = Some e1 /\
      In tid e1.(waitList) /\
      (lvs1.(TskState).(inUsedTaskStates)) tid = Some t /\
      e2 = {| eventGeneration := e1.(eventGeneration);
              eventName := e1.(eventName);
     eventPadding1 := e1.(eventPadding1);
     eventPadding2 := e1.(eventPadding2);
     eventPadding3 := e1.(eventPadding3);
     eventPadding19 := e1.(eventPadding19);
              eventType   := e1.(eventType);
              mutexFields := e1.(mutexFields);
              semFields   := e1.(semFields);
              mboxFields  := e1.(mboxFields);
              queueFields := e1.(queueFields);
              waitList    := remove_Z_eqb tid e1.(waitList);
           |} /\
      t' = {| taskID        := t.(taskID);
     taskGeneration := t.(taskGeneration);
     tcbStkPtr := t.(tcbStkPtr);
     tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom);
     tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt);
     tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode);
     tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName);
     tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr);
     tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart);
     tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr);
              curPrio        := t.(curPrio);
              stat           := t.(stat);
              statPend       := t.(statPend);
              dly            := t.(dly);
              eventPtr       := None;
              eventMultiWaitEvents  := t.(eventMultiWaitEvents);
              eventMultiRdy  := t.(eventMultiRdy);
              msg            := t.(msg);
              nextTCB        := t.(nextTCB);
              prevTCB        := t.(prevTCB);
              delReq         := t.(delReq);
           |} /\
      lvs2 = {|
        IntrState  := lvs1.(IntrState);
        TskState   := {| inUsedTaskStates := fun tid' =>
                           if Z.eqb tid' tid then Some t'
                           else (lvs1.(TskState).(inUsedTaskStates)) tid';
                          unUsedTaskStates := lvs1.(TskState).(unUsedTaskStates);
                          tcbListHead      := lvs1.(TskState).(tcbListHead);
                          prioTbl          := lvs1.(TskState).(prioTbl);
                          taskRegNextID := lvs1.(TskState).(taskRegNextID);
                          parkedTaskStacks := lvs1.(TskState).(parkedTaskStacks);
                          taskLifecycle := lvs1.(TskState).(taskLifecycle);
     taskCount        := lvs1.(TskState).(taskCount);
                       |};
        SchedState := lvs1.(SchedState);
        EventState := update_event_field_raw lvs1.(EventState) mid e2;
        TickState  := lvs1.(TickState);
        FlagState := lvs1.(FlagState);
        MemoryState := lvs1.(MemoryState);
        TimerState := lvs1.(TimerState);
        StatsState := lvs1.(StatsState);
        ControlState := lvs1.(ControlState);
        NameState := lvs1.(NameState);
      |}.

(** RemoveMulti only changes Event row/group cells.  The input IDs are the
    ordered decoding of the caller's borrowed pointer array; their binding
    and byte ownership are separate resource premises.  A live TCB is
    required for the initial cache reads, not checked by an invented C guard.
    In particular this helper does not clear EventPtr, MultiPtr or MultiRdy. *)
Definition atomic_event_task_remove_multi (tid : TaskID) (ids : list EventID)
  : program UCOS2_Verify_State unit :=
  fun entry (_ : unit) post =>
    exists t events,
      entry.(TskState).(inUsedTaskStates) tid = Some t /\
      event_multi_remove_loop entry.(EventState) tid ids = Some events /\
      post = replace_EventS events entry.

Lemma atomic_event_task_remove_multi_from_binding : forall sg entry tid t pointers instances,
  entry.(TskState).(inUsedTaskStates) tid = Some t ->
  event_multi_array_binding sg entry.(EventState) pointers instances ->
  atomic_event_task_remove_multi tid (map fst instances) entry tt
    (replace_EventS (event_multi_remove_waiters entry.(EventState) tid (map fst instances)) entry).
Proof.
  intros; exists t, (event_multi_remove_waiters entry.(EventState) tid (map fst instances)).
  split; [exact H|]; split; [|reflexivity].
  exact (proj1 (event_multi_remove_loop_from_binding sg entry.(EventState) tid pointers instances H0)).
Qed.

Lemma atomic_event_task_remove_multi_deterministic : forall tid ids entry first second,
  atomic_event_task_remove_multi tid ids entry tt first ->
  atomic_event_task_remove_multi tid ids entry tt second -> first = second.
Proof.
  intros tid ids entry first second [t1 [e1 [_ [H1 ->]]]] [t2 [e2 [_ [H2 ->]]]]; congruence.
Qed.

Lemma atomic_event_task_remove_multi_frame : forall tid ids entry post,
  atomic_event_task_remove_multi tid ids entry tt post ->
  post = replace_EventS post.(EventState) entry.
Proof. intros tid ids entry post [t [events [_ [_ ->]]]]; reflexivity. Qed.

Definition atomic_event_wait_list_init (mid : EventID)
  : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists e1 e2,
      (lvs1.(EventState).(inUsedEventStates)) mid = Some e1 /\
      e2 = {| eventGeneration := e1.(eventGeneration);
              eventName := e1.(eventName);
     eventPadding1 := e1.(eventPadding1);
     eventPadding2 := e1.(eventPadding2);
     eventPadding3 := e1.(eventPadding3);
     eventPadding19 := e1.(eventPadding19);
              eventType   := e1.(eventType);
              mutexFields := e1.(mutexFields);
              semFields   := e1.(semFields);
              mboxFields  := e1.(mboxFields);
              queueFields := e1.(queueFields);
              waitList    := [];
           |} /\
      lvs2 = replace_EventS
               {| inUsedEventStates := fun eid =>
                   if Z.eqb eid mid then Some e2
                   else (lvs1.(EventState).(inUsedEventStates)) eid;
                  eventLifecycle := lvs1.(EventState).(eventLifecycle);
                  publishedQueueBytes := lvs1.(EventState).(publishedQueueBytes);
                  unUsedEventStates := lvs1.(EventState).(unUsedEventStates);
               |}
               lvs1.

(* ================================================================== *)
(* Phase 7 Task 7.6:atomic_sched + atomic_tick_advance + 复合 mutex   *)
(* ================================================================== *)

Inductive SchedResult : Type :=
| SchedNoSwitch
| SchedSwitchedTo (new_tid : TaskID).

Inductive MutexPendResumeResult : Type :=
| MutexPendResumeOK
| MutexPendResumeAbort
| MutexPendResumeTimeout.

Definition encode_mutex_pend_resume_stat (res : MutexPendResumeResult) : Z :=
  match res with
  | MutexPendResumeOK => 0
  | MutexPendResumeAbort => 0
  | MutexPendResumeTimeout => 0x10
  end.

Definition encode_mutex_pend_resume_statpend (res : MutexPendResumeResult) : Z :=
  match res with
  | MutexPendResumeOK => 0
  | MutexPendResumeAbort => 2
  | MutexPendResumeTimeout => 1
  end.

Definition encode_mutex_pend_resume_event_ptr
           (res : MutexPendResumeResult) (event_ptr : addr) : Z :=
  match res with
  | MutexPendResumeOK => 0
  | MutexPendResumeAbort => 0
  | MutexPendResumeTimeout => event_ptr
  end.

Definition atomic_sched : program UCOS2_Verify_State SchedResult :=
  fun lvs1 res lvs2 =>
    let schedSt1 := lvs1.(SchedState) in
    let intrSt := lvs1.(IntrState) in
    (* Official OS_Sched gates selection only on interrupt/scheduler nesting.
       OSRunning is an observed kernel flag, not an execution guard here. *)
    if (Z.eqb intrSt.(intNesting) 0 &&
        Z.eqb intrSt.(lockNesting) 0)%bool
    then
      match schedSt1.(readyList), schedSt1.(curTaskID) with
      | head :: _, Some cur_tid =>
          match (lvs1.(TskState).(inUsedTaskStates)) head,
                (lvs1.(TskState).(inUsedTaskStates)) cur_tid with
          | Some headT, Some curT =>
              let cur_ready :=
                (is_effectively_ready curT.(stat) curT.(dly) &&
                 existsb (Z.eqb cur_tid) schedSt1.(readyList))%bool in
              if (negb cur_ready || negb (Z.eqb head cur_tid))%bool
              then
                exists schedSt2,
                  schedSt2 = {| readyList    := schedSt1.(readyList);
                                curTaskID    := Some head;
                                curSchedPrio := Some headT.(curPrio);
                                highRdyTid   := Some head;
                                highRdyPrio  := Some headT.(curPrio);
                                ctxSwCtr     := (schedSt1.(ctxSwCtr) + 1) mod 4294967296;
                                isRunning    := schedSt1.(isRunning);
                             |} /\
                  lvs2 = replace_SchedS schedSt2 lvs1 /\
                  res = SchedSwitchedTo head
              else lvs2 = replace_SchedS
                     (sched_write_high_pointer
                       (sched_write_high_priority schedSt1 (Some headT.(curPrio)))
                       (Some head)) lvs1 /\ res = SchedNoSwitch
          | _, _ => lvs2 = lvs1 /\ res = SchedNoSwitch
          end
      | _, _ => lvs2 = lvs1 /\ res = SchedNoSwitch
      end
    else lvs2 = lvs1 /\ res = SchedNoSwitch.

(** Counter-only substep of OSTimeTick.  The native producer owns UInt
    wraparound; the following relation does not stand for traversal or the
    tick hook, whose source steps are separate obligations. *)
Definition atomic_tick_advance : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists tickSt1 tickSt2,
      tickSt1 = lvs1.(TickState) /\
      tickSt2 = tick_counter_advance tickSt1 /\
      lvs2 = replace_TickS tickSt2 lvs1.

(* ================================================================== *)
(* Phase 7.5 Gap D:atomic_mutex_release_with_handover                 *)
(* ================================================================== *)
(* 复合原子步:对应 OSMutexPost line 681-698 waitList 非空路径          *)
(* 一次原子完成:                                                        *)
(*   1. 取 waitList 头部 task X(由调用方保证排序保证 head 是 HPT)      *)
(*   2. X 从 waitList 移除,task_non_suspension_bits/statPend/dly/eventPtr 清零         *)
(*   3. X 加入 readyList(insert_sorted_by 保持排序)                    *)
(*   4. mutex.mfOwner = X,mfOwnerOrigPrio = X.curPrio                  *)
(*   5. prioTbl[pcp] = PTReserved(若 PCP 启用,留给下一任 boost)        *)
(* 返回值:new_owner tid(供 spec 校验返回值 = waitList head)            *)
(* The optional old-owner disinherit call precedes this stage in the source.
   This raw transformer deliberately does not require that call to have made
   [old_owner.curPrio = mfOwnerOrigPrio]: the wake/handover writes execute even
   for nested/out-of-order release.  Any condition needed to re-establish the
   full cross-module invariant belongs to the caller's protocol-closure
   theorem, not to the executable transformer. *)
Definition atomic_mutex_release_with_handover (sg : StableGlobVars) (mid : EventID)
  : program UCOS2_Verify_State TaskID :=
  fun lvs1 new_owner lvs2 =>
    exists e1 e2 m1 m2 old_owner new_owner_t new_owner_t'
           evSt2 tskSt2 schedSt1 schedSt2 newReadyList rest_waitlist,
      (lvs1.(EventState).(inUsedEventStates)) mid = Some e1 /\
      e1.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e1.(mutexFields) = Some m1 /\
      m1.(mfOwner) = Some old_owner /\
      e1.(waitList) = new_owner :: rest_waitlist /\
      (lvs1.(TskState).(inUsedTaskStates)) new_owner = Some new_owner_t /\
      new_owner_t' = {| taskID        := new_owner_t.(taskID);
     taskGeneration := new_owner_t.(taskGeneration);
     tcbStkPtr := new_owner_t.(tcbStkPtr);
     tcbExtPtr := new_owner_t.(tcbExtPtr);
     tcbStkBottom := new_owner_t.(tcbStkBottom);
     tcbStkSize := new_owner_t.(tcbStkSize);
     tcbOpt := new_owner_t.(tcbOpt);
     tcbPublicId := new_owner_t.(tcbPublicId);
     tcbFlagNode := new_owner_t.(tcbFlagNode);
     tcbFlagsRdy := new_owner_t.(tcbFlagsRdy);
     tcbTaskName := new_owner_t.(tcbTaskName);
     tcbReg0 := new_owner_t.(tcbReg0);
     tcbCtxSwCtr := new_owner_t.(tcbCtxSwCtr);
     tcbCyclesTot := new_owner_t.(tcbCyclesTot);
     tcbCyclesStart := new_owner_t.(tcbCyclesStart);
     tcbStkBase := new_owner_t.(tcbStkBase);
     tcbStkUsed := new_owner_t.(tcbStkUsed);
     tcbPadding42 := new_owner_t.(tcbPadding42);
     tcbPadding43 := new_owner_t.(tcbPadding43);
     tcbEventMultiPtr := new_owner_t.(tcbEventMultiPtr);
                        curPrio        := new_owner_t.(curPrio);
                        stat           := task_clear_pending_status new_owner_t.(stat) PendMutex;
                        statPend       := PendOK;
                        dly            := 0;
                        eventPtr       := None;
                        eventMultiWaitEvents  := new_owner_t.(eventMultiWaitEvents);
                        eventMultiRdy  := new_owner_t.(eventMultiRdy);
                        msg            := new_owner_t.(msg);
                        nextTCB        := new_owner_t.(nextTCB);
                        prevTCB        := new_owner_t.(prevTCB);
                        delReq         := new_owner_t.(delReq);
                     |} /\
      m2 = {| mfPCP := m1.(mfPCP);
              mfOwner := Some new_owner;
              mfOwnerOrigPrio := Some new_owner_t.(curPrio); |} /\
      e2 = {| eventGeneration := e1.(eventGeneration);
              eventName := e1.(eventName);
     eventPadding1 := e1.(eventPadding1);
     eventPadding2 := e1.(eventPadding2);
     eventPadding3 := e1.(eventPadding3);
     eventPadding19 := e1.(eventPadding19);
              eventType   := e1.(eventType);
              mutexFields := Some m2;
              semFields   := e1.(semFields);
              mboxFields  := e1.(mboxFields);
              queueFields := e1.(queueFields);
              waitList    := rest_waitlist;
           |} /\
      evSt2 = update_event_field_raw lvs1.(EventState) mid e2 /\
      schedSt1 = lvs1.(SchedState) /\
      newReadyList = insert_sorted_by
                       (fun (tid' : TaskID) =>
                         match (lvs1.(TskState).(inUsedTaskStates)) tid' with
                         | Some t'' => t''.(curPrio)
                         | None => sg.(osLowestPrio) + 1
                         end)
                       new_owner schedSt1.(readyList) /\
      schedSt2 = {| readyList    := newReadyList;
                    curTaskID    := schedSt1.(curTaskID);
                    curSchedPrio := schedSt1.(curSchedPrio);
                    highRdyTid   := match newReadyList with
                                    | head :: _ => Some head
                                    | [] => None
                                    end;
                    highRdyPrio  := match newReadyList with
                                    | head :: _ =>
                                        match (lvs1.(TskState).(inUsedTaskStates)) head with
                                        | Some t'' => Some t''.(curPrio)
                                        | None => None
                                        end
                                    | [] => None
                                    end;
                    ctxSwCtr     := schedSt1.(ctxSwCtr);
                    isRunning    := schedSt1.(isRunning);
                 |} /\
      tskSt2 = {| inUsedTaskStates := fun tid' =>
                   if Z.eqb tid' new_owner then Some new_owner_t'
                   else (lvs1.(TskState).(inUsedTaskStates)) tid';
                  unUsedTaskStates := lvs1.(TskState).(unUsedTaskStates);
                  tcbListHead      := lvs1.(TskState).(tcbListHead);
                  prioTbl          := fun p =>
                    if (negb (Z.eqb m1.(mfPCP) sg.(osPrioMutexCeilDis))
                         && Z.eqb p m1.(mfPCP))%bool
                    then PTReserved
                    else (lvs1.(TskState).(prioTbl)) p;
                  taskRegNextID := lvs1.(TskState).(taskRegNextID);
                  parkedTaskStacks := lvs1.(TskState).(parkedTaskStacks);
                  taskLifecycle := lvs1.(TskState).(taskLifecycle);
     taskCount        := lvs1.(TskState).(taskCount);
               |} /\
      lvs2 = {| IntrState  := lvs1.(IntrState);
                TskState   := tskSt2;
                SchedState := schedSt2;
                EventState := evSt2;
                TickState  := lvs1.(TickState);
                FlagState := lvs1.(FlagState);
                MemoryState := lvs1.(MemoryState);
                TimerState := lvs1.(TimerState);
                StatsState := lvs1.(StatsState);
                ControlState := lvs1.(ControlState);
                NameState := lvs1.(NameState);
             |}.

(* Resume of a blocked mutex pend models the environment action that made the
   task runnable.  A successful wake-up is not merely EventTaskRdy: the
   posting task first restores the old owner's priority and atomically hands
   the mutex to the highest-priority waiter. *)
Definition atomic_mutex_pend_sched_resume (sg : StableGlobVars)
  (mid : EventID) (cur_tid : TaskID)
  : program UCOS2_Verify_State MutexPendResumeResult :=
  fun lvs1 res lvs2 =>
    (res = MutexPendResumeOK /\
     exists lvs_d lvs_r,
       atomic_mutex_restore sg mid lvs1 tt lvs_d /\
       atomic_mutex_release_with_handover sg mid lvs_d cur_tid lvs_r /\
       lvs2 = lvs_r) \/
    (res = MutexPendResumeAbort /\
     exists lvs_r returned_prio table_owner,
       atomic_event_task_rdy
         sg mid PendAbort lvs1 returned_prio cur_tid table_owner lvs_r /\
       lvs2 = lvs_r) \/
    (res = MutexPendResumeTimeout /\
     exists t t',
       lvs1.(TskState).(inUsedTaskStates) cur_tid = Some t /\
       t' = {| taskID        := t.(taskID);
     taskGeneration := t.(taskGeneration);
     tcbStkPtr := t.(tcbStkPtr);
     tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom);
     tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt);
     tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode);
     tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName);
     tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr);
     tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart);
     tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr);
               curPrio       := t.(curPrio);
               stat          := t.(stat);
               statPend      := PendTimeout;
               dly           := 0;
               eventPtr      := t.(eventPtr);
               eventMultiWaitEvents := t.(eventMultiWaitEvents);
               eventMultiRdy := t.(eventMultiRdy);
               msg           := t.(msg);
               nextTCB       := t.(nextTCB);
               prevTCB       := t.(prevTCB);
               delReq        := t.(delReq); |} /\
       lvs2 = replace_TskS
                {| inUsedTaskStates := fun tid =>
                     if Z.eqb tid cur_tid then Some t'
                     else lvs1.(TskState).(inUsedTaskStates) tid;
                   unUsedTaskStates := lvs1.(TskState).(unUsedTaskStates);
                   tcbListHead      := lvs1.(TskState).(tcbListHead);
                   prioTbl          := lvs1.(TskState).(prioTbl);
                   taskRegNextID := lvs1.(TskState).(taskRegNextID);
                   parkedTaskStacks := lvs1.(TskState).(parkedTaskStacks);
                   taskLifecycle := lvs1.(TskState).(taskLifecycle);
     taskCount        := lvs1.(TskState).(taskCount); |}
                lvs1).

Definition mutex_del_abort_task (t : TaskAbstractState) : TaskAbstractState :=
  {| taskID        := t.(taskID);
     taskGeneration := t.(taskGeneration);
     tcbStkPtr := t.(tcbStkPtr);
     tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom);
     tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt);
     tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode);
     tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName);
     tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr);
     tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart);
     tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr);
     curPrio        := t.(curPrio);
     stat           := task_clear_pending_status t.(stat) PendMutex;
     statPend       := PendAbort;
     dly            := 0;
     eventPtr       := None;
     eventMultiWaitEvents  := t.(eventMultiWaitEvents);
     eventMultiRdy  := t.(eventMultiRdy);
     msg            := None;
     nextTCB        := t.(nextTCB);
     prevTCB        := t.(prevTCB);
     delReq         := t.(delReq);
  |}.

Definition task_prio_key (sg : StableGlobVars)
           (tasks : TaskID -> option TaskAbstractState) (tid : TaskID) : Z :=
  match tasks tid with
  | Some t => t.(curPrio)
  | None => sg.(osLowestPrio) + 1
  end.

Definition mutex_del_abort_tasks (waiters : list TaskID)
           (tasks : TaskID -> option TaskAbstractState)
  : TaskID -> option TaskAbstractState :=
  fun tid =>
    if existsb (Z.eqb tid) waiters
    then match tasks tid with
         | Some t => Some (mutex_del_abort_task t)
         | None => None
         end
    else tasks tid.

Definition mutex_del_ready_after_abort (sg : StableGlobVars)
           (tasks : TaskID -> option TaskAbstractState)
           (waiters ready_list : list TaskID) : list TaskID :=
  fold_right
    (fun tid ready_after =>
       match tasks tid with
       | Some t =>
           let t' := mutex_del_abort_task t in
           if (task_is_suspended t'.(stat))
           then remove_Z_eqb tid ready_after
           else insert_sorted_by
                  (task_prio_key sg tasks)
                  tid
                  (remove_Z_eqb tid ready_after)
       | None => ready_after
       end)
    ready_list
    waiters.

(* Focused OSMutexDel ready-all step: models the repeated OS_EventTaskRdy
   loop with OS_STAT_PEND_ABORT. Owner restore and final event free are
   intentionally outside this atomic step. *)
Definition atomic_event_task_rdy_all_mutex_abort (sg : StableGlobVars)
           (mid : EventID)
  : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists e1 m1 tskSt2 ready_after schedSt2 evSt2,
      (lvs1.(EventState).(inUsedEventStates)) mid = Some e1 /\
      e1.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e1.(mutexFields) = Some m1 /\
      tskSt2 =
        {| inUsedTaskStates :=
             mutex_del_abort_tasks
               e1.(waitList)
               lvs1.(TskState).(inUsedTaskStates);
           unUsedTaskStates := lvs1.(TskState).(unUsedTaskStates);
           tcbListHead      := lvs1.(TskState).(tcbListHead);
           prioTbl          := lvs1.(TskState).(prioTbl);
           taskRegNextID := lvs1.(TskState).(taskRegNextID);
           parkedTaskStacks := lvs1.(TskState).(parkedTaskStacks);
           taskLifecycle := lvs1.(TskState).(taskLifecycle);
     taskCount        := lvs1.(TskState).(taskCount);
        |} /\
      ready_after =
        mutex_del_ready_after_abort
          sg
          lvs1.(TskState).(inUsedTaskStates)
          e1.(waitList)
          lvs1.(SchedState).(readyList) /\
      schedSt2 =
        {| readyList    := ready_after;
           curTaskID    := lvs1.(SchedState).(curTaskID);
           curSchedPrio := lvs1.(SchedState).(curSchedPrio);
           highRdyTid   := match ready_after with
                           | head :: _ => Some head
                           | [] => None
                           end;
           highRdyPrio  := match ready_after with
                           | head :: _ =>
                               match tskSt2.(inUsedTaskStates) head with
                               | Some head_t => Some head_t.(curPrio)
                               | None => None
                               end
                           | [] => None
                           end;
           ctxSwCtr     := lvs1.(SchedState).(ctxSwCtr);
           isRunning    := lvs1.(SchedState).(isRunning);
        |} /\
      evSt2 =
        update_event_field_raw
          lvs1.(EventState)
          mid
          {| eventGeneration := e1.(eventGeneration);
             eventName := e1.(eventName);
     eventPadding1 := e1.(eventPadding1);
     eventPadding2 := e1.(eventPadding2);
     eventPadding3 := e1.(eventPadding3);
     eventPadding19 := e1.(eventPadding19);
             eventType   := e1.(eventType);
             mutexFields := Some m1;
             semFields   := e1.(semFields);
             mboxFields  := e1.(mboxFields);
             queueFields := e1.(queueFields);
             waitList    := [];
          |} /\
      lvs2 =
        replace_TskS
          tskSt2
          (replace_SchedS
             schedSt2
             (replace_EventS evSt2 lvs1)).

(* Ordered owner-restoration stage of OSMutexDel(OS_DEL_ALWAYS).

   The C branch is:
     enabled PCP -> non-null owner -> owner.curPrio = PCP -> RdyAtPrio(orig).
   Every failed runtime guard is identity.  In particular, equality with the
   original priority is not a guard, and an enabled owned mutex is not restored
   unconditionally.  Mismatched owner/original-priority options are rejected as
   non-representable abstract mutex shapes; valid invariants already exclude
   them, so this explicit case does not weaken the invariant. *)
Definition atomic_mutex_del_owner_restore (sg : StableGlobVars) (m : MutexFields)
  : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    (match m.(mfOwner), m.(mfOwnerOrigPrio) with
     | None, None | Some _, Some _ => True
     | _, _ => False
     end) /\
    if Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis)
    then lvs2 = lvs1
    else
      match m.(mfOwner), m.(mfOwnerOrigPrio) with
      | None, None => lvs2 = lvs1
      | Some owner_tid, Some origPrio =>
          exists owner_t,
            lvs1.(TskState).(inUsedTaskStates) owner_tid = Some owner_t /\
            if Z.eqb owner_t.(curPrio) m.(mfPCP)
            then atomic_task_set_curPrio_ready_owner_literal_exec
                   sg owner_tid owner_t origPrio lvs1 tt lvs2
            else lvs2 = lvs1
      | _, _ => False
      end.

Definition atomic_mutex_del_prepare (sg : StableGlobVars) (mid : EventID)
  : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists e1 m1 lvs_owner tskSt2 ready_after schedSt2 evSt2,
      (lvs1.(EventState).(inUsedEventStates)) mid = Some e1 /\
      e1.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e1.(mutexFields) = Some m1 /\
      atomic_mutex_del_owner_restore sg m1 lvs1 tt lvs_owner /\
      tskSt2 =
        {| inUsedTaskStates :=
             mutex_del_abort_tasks
               e1.(waitList)
               lvs_owner.(TskState).(inUsedTaskStates);
           unUsedTaskStates := lvs_owner.(TskState).(unUsedTaskStates);
           tcbListHead      := lvs_owner.(TskState).(tcbListHead);
           prioTbl          := lvs_owner.(TskState).(prioTbl);
           taskRegNextID := lvs_owner.(TskState).(taskRegNextID);
           parkedTaskStacks := lvs_owner.(TskState).(parkedTaskStacks);
           taskLifecycle := lvs_owner.(TskState).(taskLifecycle);
     taskCount        := lvs_owner.(TskState).(taskCount);
        |} /\
      ready_after =
        mutex_del_ready_after_abort
          sg
          lvs_owner.(TskState).(inUsedTaskStates)
          e1.(waitList)
          lvs_owner.(SchedState).(readyList) /\
      schedSt2 =
        {| readyList    := ready_after;
           curTaskID    := lvs_owner.(SchedState).(curTaskID);
           curSchedPrio := lvs_owner.(SchedState).(curSchedPrio);
           highRdyTid   := match ready_after with
                           | head :: _ => Some head
                           | [] => None
                           end;
           highRdyPrio  := match ready_after with
                           | head :: _ =>
                               match tskSt2.(inUsedTaskStates) head with
                               | Some head_t => Some head_t.(curPrio)
                               | None => None
                               end
                           | [] => None
                           end;
           ctxSwCtr     := lvs_owner.(SchedState).(ctxSwCtr);
           isRunning    := lvs_owner.(SchedState).(isRunning);
        |} /\
      evSt2 =
        update_event_field_raw
          lvs_owner.(EventState)
          mid
          {| eventGeneration := e1.(eventGeneration);
             eventName := e1.(eventName);
     eventPadding1 := e1.(eventPadding1);
     eventPadding2 := e1.(eventPadding2);
     eventPadding3 := e1.(eventPadding3);
     eventPadding19 := e1.(eventPadding19);
             eventType   := e1.(eventType);
             mutexFields := Some {| mfPCP := m1.(mfPCP);
                                    mfOwner := None;
                                    mfOwnerOrigPrio := None; |};
             semFields   := e1.(semFields);
             mboxFields  := e1.(mboxFields);
             queueFields := e1.(queueFields);
             waitList    := [];
          |} /\
      lvs2 =
        replace_TskS
          tskSt2
          (replace_SchedS
             schedSt2
             (replace_EventS evSt2 lvs_owner)).

(* ================================================================== *)
(* Phase 7.5 Gap E:atomic_event_free_with_priotbl_free                 *)
(* ================================================================== *)
(* 复合原子步:对应 OSMutexDel NO_PEND 模式 line 361-368 / ALWAYS 397-404 *)
(* 的释放部分(owner/waitList 已由前置 atomic 步处理干净)*)
(* 一次原子完成:                                                        *)
(*   1. event 从 inUsed 移到 unUsed(type 隐式变 UNUSED,因 inUsed=None) *)
(*   2. prioTbl[pcp] = PTFree(若 PCP 启用,完全释放 pcp 资源)          *)
(* 前置:event 类型为 MUTEX 且 mutex 无 owner 且 waitList 为空          *)
(*       (NO_PEND:自然满足;ALWAYS:由调用方先 disinherit + rdy all)    *)
Definition atomic_event_free_with_priotbl_free (sg : StableGlobVars) (mid : EventID)
  : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists e1 m1 evSt2 tskSt2,
      (lvs1.(EventState).(inUsedEventStates)) mid = Some e1 /\
      e1.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e1.(mutexFields) = Some m1 /\
      m1.(mfOwner) = None /\
      e1.(waitList) = [] /\
      evSt2 = {| inUsedEventStates := fun eid' =>
                   if Z.eqb eid' mid then None
                   else (lvs1.(EventState).(inUsedEventStates)) eid';
                 eventLifecycle := lvs1.(EventState).(eventLifecycle);
                 publishedQueueBytes := lvs1.(EventState).(publishedQueueBytes);
                 unUsedEventStates := mid :: lvs1.(EventState).(unUsedEventStates);
              |} /\
      tskSt2 = {| inUsedTaskStates := lvs1.(TskState).(inUsedTaskStates);
                  unUsedTaskStates := lvs1.(TskState).(unUsedTaskStates);
                  tcbListHead      := lvs1.(TskState).(tcbListHead);
                  prioTbl          := fun p =>
                    if (negb (Z.eqb m1.(mfPCP) sg.(osPrioMutexCeilDis))
                         && Z.eqb p m1.(mfPCP))%bool
                    then PTFree
                    else (lvs1.(TskState).(prioTbl)) p;
                  taskRegNextID := lvs1.(TskState).(taskRegNextID);
                  parkedTaskStacks := lvs1.(TskState).(parkedTaskStacks);
                  taskLifecycle := lvs1.(TskState).(taskLifecycle);
     taskCount        := lvs1.(TskState).(taskCount);
               |} /\
      lvs2 = {| IntrState  := lvs1.(IntrState);
                TskState   := tskSt2;
                SchedState := lvs1.(SchedState);
                EventState := evSt2;
                TickState  := lvs1.(TickState);
                FlagState := lvs1.(FlagState);
                MemoryState := lvs1.(MemoryState);
                TimerState := lvs1.(TimerState);
                StatsState := lvs1.(StatsState);
                ControlState := lvs1.(ControlState);
                NameState := lvs1.(NameState);
             |}.

(* 复合 atomic_mutex_create:event_alloc + mutex_init +(optional) priotbl_reserve *)
Definition verification_slice_atomic_mutex_create (sg : StableGlobVars) (pcp : Priority)
  : program UCOS2_Verify_State (option EventID) :=
  fun lvs1 oid lvs2 =>
    exists lvs_alloc eid lvs_init lvs_reserve,
      atomic_event_alloc lvs1 eid lvs_alloc /\
      atomic_mutex_init eid pcp lvs_alloc tt lvs_init /\
      (if Z.eqb pcp sg.(osPrioMutexCeilDis)
       then lvs_reserve = lvs_init
       else atomic_priotbl_reserve pcp lvs_init tt lvs_reserve) /\
      oid = Some eid /\
      lvs2 = lvs_reserve.

(** The current Create endpoint accounts for the physical free-storage
    map and allocation identity.  The earlier relation above belongs to
    the historical verification slice; it does not establish the current
    pool partition or its storage-domain invariant. *)
Definition mutex_create_priority_state (sg : StableGlobVars) (pcp : Priority)
  (before : Glob_TaskAbstractState) : Glob_TaskAbstractState :=
  {| inUsedTaskStates := before.(inUsedTaskStates);
     unUsedTaskStates := before.(unUsedTaskStates);
     tcbListHead := before.(tcbListHead);
     prioTbl := if Z.eqb pcp sg.(osPrioMutexCeilDis)
       then before.(prioTbl)
       else update_prio_tbl before.(prioTbl) pcp PTReserved;
     taskRegNextID := before.(taskRegNextID);
     parkedTaskStacks := before.(parkedTaskStacks);
     taskLifecycle := before.(taskLifecycle);
     taskCount := before.(taskCount) |}.

Definition mutex_create_storage (before : Glob_EventAbstractState)
  (eid : EventID) : EventStorage :=
  match before.(eventLifecycle).(eventFreeStorage) eid with
  | Some image => image
  | None => fun _ => None
  end.

(** Only the source-written payload/bitmap fields are initialized.
    Padding is retained from the detached storage; generation is allocated
    by [event_detach_head], not reset on slot reuse.  This source profile
    has no OSEventName store; the optional name slot is therefore not an
    extra write performed by Create. *)
Definition mutex_create_node (pcp : Priority) (generation : nat)
  (image : EventStorage) : OSEventAbstractState :=
  {| eventGeneration := generation;
     eventName := match image EventNameField with Some name => name | None => 0 end;
     eventPadding1 := image EventPadding1;
     eventPadding2 := image EventPadding2;
     eventPadding3 := image EventPadding3;
     eventPadding19 := image EventPadding19;
     eventType := OS_EVENT_TYPE_MUTEX;
     mutexFields := Some {| mfPCP := pcp; mfOwner := None; mfOwnerOrigPrio := None |};
     semFields := None; mboxFields := None; queueFields := None; waitList := [] |}.

Definition mutex_create_event_state (pcp : Priority) (eid : EventID)
  (rest : list EventID) (before : Glob_EventAbstractState) : Glob_EventAbstractState :=
  let image := mutex_create_storage before eid in
  event_publish (event_detach_head before eid rest image) eid
    (mutex_create_node pcp before.(eventLifecycle).(eventNextGeneration) image).

(** The actual Restore frontier: the table was reserved and the ECB has
    been detached, but no payload field or wait bitmap is initialized yet.
    The PCP lease is attached to this private allocation, not published
    as an OS_EVENT_TYPE_MUTEX node. *)
Definition mutex_create_detached_state (sg : StableGlobVars) (pcp : Priority)
  (eid : EventID) (rest : list EventID) (before : UCOS2_Verify_State)
  : UCOS2_Verify_State :=
  replace_EventS
    (event_detach_mutex_head sg before.(EventState) eid rest
      (mutex_create_storage before.(EventState) eid) pcp)
    (replace_TskS (mutex_create_priority_state sg pcp before.(TskState)) before).

Definition mutex_create_state (sg : StableGlobVars) (pcp : Priority)
  (eid : EventID) (rest : list EventID) (before : UCOS2_Verify_State)
  : UCOS2_Verify_State :=
  replace_EventS (mutex_create_event_state pcp eid rest before.(EventState))
    (replace_TskS (mutex_create_priority_state sg pcp before.(TskState)) before).

Lemma mutex_create_detached_publish_eq : forall sg pcp eid rest before,
  replace_EventS
    (event_publish (mutex_create_detached_state sg pcp eid rest before).(EventState) eid
      (mutex_create_node pcp before.(EventState).(eventLifecycle).(eventNextGeneration)
        (mutex_create_storage before.(EventState) eid)))
    (mutex_create_detached_state sg pcp eid rest before) =
  mutex_create_state sg pcp eid rest before.
Proof.
  intros; unfold mutex_create_detached_state, mutex_create_state, mutex_create_event_state.
  cbn [replace_EventS replace_TskS EventState].
  rewrite event_publish_detach_mutex_eq; reflexivity.
Qed.

(** Source guards only.  Representation, pool validity and full closure
    remain theorem premises, not hidden execution guards.  Failure and
    rollback branches are owned by the ordered public semantics. *)
Definition atomic_mutex_create (sg : StableGlobVars) (pcp : Priority)
  : program UCOS2_Verify_State (option EventID) :=
  fun before oid after =>
    exists eid rest,
      before.(EventState).(unUsedEventStates) = eid :: rest /\
      (pcp = sg.(osPrioMutexCeilDis) \/ before.(TskState).(prioTbl) pcp = PTFree) /\
      oid = Some eid /\ after = mutex_create_state sg pcp eid rest before.
