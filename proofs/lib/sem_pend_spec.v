Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.atomic_ops_lib.

Import ListNotations.
Import Monad.
Import TaskStateDef.
Import EventStateDef.
Import UCOS2_C_Rules.

Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source-visible outcomes.  Posted and immediate success deliberately stay
    distinct even though both write [OS_ERR_NONE]. *)
Inductive SemPendResult : Type :=
| SemPendNull
| SemPendWrongType
| SemPendISR
| SemPendLocked
| SemPendImmediate
| SemPendPosted
| SemPendAborted
| SemPendTimedOut.

Definition encode_sem_pend_result (res : SemPendResult) : Z :=
  match res with
  | SemPendNull      => encode_os_err_code OS_ERR_PEVENT_NULL
  | SemPendWrongType => encode_os_err_code OS_ERR_EVENT_TYPE
  | SemPendISR       => encode_os_err_code OS_ERR_PEND_ISR
  | SemPendLocked    => encode_os_err_code OS_ERR_PEND_LOCKED
  | SemPendImmediate => encode_os_err_code OS_ERR_NONE
  | SemPendPosted    => encode_os_err_code OS_ERR_NONE
  | SemPendAborted   => encode_os_err_code OS_ERR_PEND_ABORT
  | SemPendTimedOut  => encode_os_err_code OS_ERR_TIMEOUT
  end.

Inductive SemPendResumeResult : Type :=
| SemPendResumePosted
| SemPendResumeAborted
| SemPendResumeTimedOut.

Definition encode_sem_pend_resume_stat
  (res : SemPendResumeResult) : Z :=
  match res with
  | SemPendResumePosted => 0
  | SemPendResumeAborted => 0
  | SemPendResumeTimedOut => 1
  end.

Definition encode_sem_pend_resume_statpend
  (res : SemPendResumeResult) : Z :=
  match res with
  | SemPendResumePosted => 0
  | SemPendResumeAborted => 2
  | SemPendResumeTimedOut => 1
  end.

Definition encode_sem_pend_resume_event_ptr
  (res : SemPendResumeResult) (event_ptr : addr) : Z :=
  match res with
  | SemPendResumePosted => 0
  | SemPendResumeAborted => 0
  | SemPendResumeTimedOut => event_ptr
  end.

(** Exact count update for the immediate-acquire path. *)
Definition sem_pend_event_with_count
  (e : OSEventAbstractState) (cnt : Z) : OSEventAbstractState :=
  {| eventGeneration := e.(eventGeneration);
     eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19);
     eventType   := e.(eventType);
     mutexFields := e.(mutexFields);
     semFields   := Some {| semCount := cnt |};
     mboxFields  := e.(mboxFields);
     queueFields := e.(queueFields);
     waitList    := e.(waitList) |}.

Definition sem_pend_decrement_state
  (entry : UCOS2_Verify_State) (eid : EventID)
  (e : OSEventAbstractState) : UCOS2_Verify_State :=
  replace_EventS
    (update_event_field_raw
       entry.(EventState) eid
       (sem_pend_event_with_count e
          (encode_event_cnt_value e - 1)))
    entry.

(** The source writes the current TCB's pend fields and then delegates the
    event insertion and ready-list removal to OS_EventTaskWait.  The shared
    atomic relation intentionally covers that complete source step. *)
Definition sem_pend_wait_step
  (sg : StableGlobVars) (eid : EventID) (timeout : Z)
  (entry post : UCOS2_Verify_State) : Prop :=
  atomic_event_task_wait_kind
    sg eid PendSem timeout entry tt post.

Definition sem_pend_select_current
  (entry : UCOS2_Verify_State) (cur_tid : TaskID) : Prop :=
  entry.(SchedState).(curTaskID) = Some cur_tid.

Definition sem_pend_timeout_resume
  (sg : StableGlobVars) (cur_tid : TaskID)
  (entry post : UCOS2_Verify_State) : Prop :=
  exists t t',
    entry.(TskState).(inUsedTaskStates) cur_tid = Some t /\
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
            msg            := t.(msg);
            nextTCB        := t.(nextTCB);
            prevTCB        := t.(prevTCB);
            delReq         := t.(delReq) |} /\
    let schedSt1 := entry.(SchedState) in
    let ready_after :=
      if (task_is_suspended t'.(stat))
      then schedSt1.(readyList)
      else insert_sorted_by
             (wait_prio_key sg entry.(TskState))
             cur_tid
             (remove_Z_eqb cur_tid schedSt1.(readyList)) in
    let schedSt2 :=
      {| readyList    := ready_after;
         curTaskID    := schedSt1.(curTaskID);
         curSchedPrio := schedSt1.(curSchedPrio);
         highRdyTid   := match ready_after with
                         | head :: _ => Some head
                         | [] => None
                         end;
         highRdyPrio  := match ready_after with
                         | head :: _ =>
                             match entry.(TskState).(inUsedTaskStates) head with
                             | Some headT => Some headT.(curPrio)
                             | None => None
                             end
                         | [] => None
                         end;
         ctxSwCtr     := schedSt1.(ctxSwCtr);
         isRunning    := schedSt1.(isRunning) |} in
    post =
      {| IntrState  := entry.(IntrState);
         TskState   :=
           {| inUsedTaskStates := fun tid =>
                if Z.eqb tid cur_tid then Some t'
                else entry.(TskState).(inUsedTaskStates) tid;
              unUsedTaskStates := entry.(TskState).(unUsedTaskStates);
              tcbListHead      := entry.(TskState).(tcbListHead);
              prioTbl          := entry.(TskState).(prioTbl);
              taskRegNextID := entry.(TskState).(taskRegNextID);
              parkedTaskStacks := entry.(TskState).(parkedTaskStacks);
              taskLifecycle := entry.(TskState).(taskLifecycle);
     taskCount        := entry.(TskState).(taskCount) |};
         SchedState := schedSt2;
         EventState := entry.(EventState);
         TickState  := entry.(TickState);
         FlagState := entry.(FlagState);
         MemoryState := entry.(MemoryState);
         TimerState := entry.(TimerState);
         StatsState := entry.(StatsState);
         ControlState := entry.(ControlState);
         NameState := entry.(NameState) |}.

(** The scheduler returns only after the current waiter has been posted,
    aborted, or timed out.  Posted/abort transitions use the shared
    semaphore-specific ready relation.  Timeout marks StatPend/Dly, restores
    the runnable task to the scheduler ready list (unless it is suspended),
    and deliberately leaves the event backlink for OS_EventTaskRemove. *)
Definition sem_pend_resume_step
  (sg : StableGlobVars) (eid : EventID) (cur_tid : TaskID)
  (entry : UCOS2_Verify_State) (res : SemPendResumeResult)
  (post : UCOS2_Verify_State) : Prop :=
  match res with
  | SemPendResumePosted =>
      exists returned_prio,
        atomic_event_task_rdy_one
          sg eid PendSem None PendOK entry returned_prio
          cur_tid cur_tid post
  | SemPendResumeAborted =>
      exists returned_prio,
        atomic_event_task_rdy_one
          sg eid PendSem None PendAbort entry returned_prio
          cur_tid cur_tid post
  | SemPendResumeTimedOut =>
      sem_pend_timeout_resume sg cur_tid entry post
  end.

Definition sem_pend_cleanup_step
  (cur_tid : TaskID)
  (entry post : UCOS2_Verify_State) : Prop :=
  exists t t',
    entry.(TskState).(inUsedTaskStates) cur_tid = Some t /\
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
            stat          := (task_status_single None ((task_is_suspended t.(stat))));
            statPend      := PendOK;
            dly           := t.(dly);
            eventPtr      := None;
            eventMultiWaitEvents := t.(eventMultiWaitEvents);
            eventMultiRdy := t.(eventMultiRdy);
            msg            := t.(msg);
            nextTCB        := t.(nextTCB);
            prevTCB        := t.(prevTCB);
            delReq         := t.(delReq) |} /\
    post = replace_TskS
      {| inUsedTaskStates := fun tid =>
           if Z.eqb tid cur_tid then Some t'
           else entry.(TskState).(inUsedTaskStates) tid;
         unUsedTaskStates := entry.(TskState).(unUsedTaskStates);
         tcbListHead      := entry.(TskState).(tcbListHead);
         prioTbl          := entry.(TskState).(prioTbl);
         taskRegNextID := entry.(TskState).(taskRegNextID);
         parkedTaskStacks := entry.(TskState).(parkedTaskStacks);
         taskLifecycle := entry.(TskState).(taskLifecycle);
     taskCount        := entry.(TskState).(taskCount) |}
      entry.

Definition sem_pend_final_step
  (eid : EventID) (cur_tid : TaskID)
  (res : SemPendResumeResult)
  (entry post : UCOS2_Verify_State) : Prop :=
  match res with
  | SemPendResumePosted => sem_pend_cleanup_step cur_tid entry post
  | SemPendResumeAborted => sem_pend_cleanup_step cur_tid entry post
  | SemPendResumeTimedOut =>
      exists removed,
        atomic_event_task_remove cur_tid eid entry tt removed /\
        sem_pend_cleanup_step cur_tid removed post
  end.

Definition sem_pend_blocked_result
  (res : SemPendResumeResult) : SemPendResult :=
  match res with
  | SemPendResumePosted => SemPendPosted
  | SemPendResumeAborted => SemPendAborted
  | SemPendResumeTimedOut => SemPendTimedOut
  end.

(** Branch-merge token for the concrete [OSTCBStatPend] dispatch.  The
    cleanup state is the resume state for posted/aborted wakeups and the
    event-removal successor for timeout.  Keeping the error byte in this
    proposition lets the three C switch arms rejoin without hiding their
    exact externally observable result. *)
Definition sem_pend_tail_result_prop
  (eid cur_tid : Z) (res : SemPendResumeResult)
  (resume_state cleanup_state : UCOS2_Verify_State) (err : Z) : Prop :=
  match res with
  | SemPendResumePosted =>
      cleanup_state = resume_state /\ err = 0
  | SemPendResumeAborted =>
      cleanup_state = resume_state /\ err = 14
  | SemPendResumeTimedOut =>
      atomic_event_task_remove
        cur_tid eid resume_state tt cleanup_state /\ err = 10
  end.

(** Complete source-ordered functional semantics. *)
Definition OSSemPend_sem
  (sg : StableGlobVars) (pevent : addr) (timeout : Z)
  : program UCOS2_Verify_State SemPendResult :=
  fun entry res post =>
    (pevent = 0 /\ res = SemPendNull /\ post = entry) \/
    (pevent <> 0 /\
     exists eid e,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       entry.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) <> OS_EVENT_TYPE_SEM /\
       res = SemPendWrongType /\ post = entry) \/
    (pevent <> 0 /\
     exists eid e,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       entry.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_SEM /\
       entry.(IntrState).(intNesting) > 0 /\
       res = SemPendISR /\ post = entry) \/
    (pevent <> 0 /\
     exists eid e,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       entry.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_SEM /\
       entry.(IntrState).(intNesting) <= 0 /\
       entry.(IntrState).(lockNesting) > 0 /\
       res = SemPendLocked /\ post = entry) \/
    (pevent <> 0 /\
     exists eid e sf,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       entry.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_SEM /\
       e.(semFields) = Some sf /\
       entry.(IntrState).(intNesting) <= 0 /\
       entry.(IntrState).(lockNesting) <= 0 /\
       0 < sf.(semCount) /\
       res = SemPendImmediate /\
       post = sem_pend_decrement_state entry eid e) \/
    (pevent <> 0 /\
     exists eid e sf cur_tid wait_state resume_state resume_res,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       entry.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_SEM /\
       e.(semFields) = Some sf /\
       entry.(IntrState).(intNesting) <= 0 /\
       entry.(IntrState).(lockNesting) <= 0 /\
       sf.(semCount) = 0 /\
       sem_pend_select_current entry cur_tid /\
       sem_pend_wait_step sg eid timeout entry wait_state /\
       sem_pend_resume_step
         sg eid cur_tid wait_state resume_res resume_state /\
       sem_pend_final_step eid cur_tid resume_res resume_state post /\
       res = sem_pend_blocked_result resume_res).

Definition sem_pend_exact_result_prop
  (sg : StableGlobVars) (pevent : addr) (timeout : Z)
  (entry post : UCOS2_Verify_State) (res : SemPendResult) : Prop :=
  OSSemPend_sem sg pevent timeout entry res post.

Definition sem_pend_result_prop
  (sg : StableGlobVars) (pevent : addr) (timeout : Z)
  (entry post : UCOS2_Verify_State) (err : Z) : Prop :=
  exists res,
    OSSemPend_sem sg pevent timeout entry res post /\
    err = encode_sem_pend_result res.

Definition OSSemPend_post_token
  (post : UCOS2_Verify_State) : UCOS2_Verify_State -> Prop :=
  fun observed => observed = post.

Definition OSSemPend_LastSeen
  (sg : StableGlobVars) (pevent : addr) (timeout : Z)
  (entry : UCOS2_Verify_State) (res : SemPendResult)
  (post : UCOS2_Verify_State)
  : (UCOS2_Verify_State -> Prop) -> Prop :=
  fun X =>
    OSSemPend_sem sg pevent timeout entry res post /\
    X = OSSemPend_post_token post.

Definition OSSemPend_atomic_cmd
  (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (pevent : addr) (timeout : Z)
  : program (UCOS2_Verify_State -> Prop) SemPendResult :=
  fun X1 res X2 =>
    LastSeen entry X1 /\
    exists post,
      OSSemPend_LastSeen sg pevent timeout entry res post X2.

Definition observe_sem_pend_result (res : SemPendResult)
  : program (UCOS2_Verify_State -> Prop) Z :=
  fun X1 n X2 => n = encode_sem_pend_result res /\ X2 = X1.

Lemma OSSemPend_safe_return :
  forall sg pevent timeout entry res post
         (X : Z -> (UCOS2_Verify_State -> Prop) -> Prop),
    OSSemPend_sem sg pevent timeout entry res post ->
    safeExec (LastSeen entry)
      (bind (OSSemPend_atomic_cmd sg entry pevent timeout)
            observe_sem_pend_result) X ->
    safeExec
      (OSSemPend_LastSeen sg pevent timeout entry res post)
      (@StateRelMonad.ret
         (UCOS2_Verify_State -> Prop) Z
         (encode_sem_pend_result res)) X.
Proof.
  intros sg pevent timeout entry res post X Hsem Hexec.
  assert (Hatomic : hs_eval
    (OSSemPend_atomic_cmd sg entry pevent timeout)
    (LastSeen entry)
    (OSSemPend_LastSeen sg pevent timeout entry res post) res).
  {
    unfold hs_eval, OSSemPend_atomic_cmd.
    intros X1 HX1.
    exists (OSSemPend_post_token post).
    split.
    - split; [exact HX1 |].
      exists post. unfold OSSemPend_LastSeen.
      split; [exact Hsem | reflexivity].
    - unfold OSSemPend_LastSeen.
      split; [exact Hsem | reflexivity].
  }
  pose proof (highstepbind_derive
    (OSSemPend_atomic_cmd sg entry pevent timeout)
    observe_sem_pend_result (LastSeen entry) res
    (OSSemPend_LastSeen sg pevent timeout entry res post)
    Hatomic X Hexec) as Hobserve.
  eapply (highstependret_derive
    (observe_sem_pend_result res)
    (OSSemPend_LastSeen sg pevent timeout entry res post)
    (encode_sem_pend_result res)
    (fun _ => OSSemPend_LastSeen
      sg pevent timeout entry res post)).
  2: exact Hobserve.
  unfold hs_eval, observe_sem_pend_result.
  intros X1 HX1. exists X1. split.
  - split; reflexivity.
  - exact HX1.
Qed.

(** Public endpoints are stable kernel states. *)
Definition sem_pend_rep
  (sg : StableGlobVars) (_entry post : UCOS2_Verify_State) : Assertion :=
  UCOS2_verification_slice_inv sg post.

Definition sem_pend_conditional_validity_prop
  (sg : StableGlobVars) (post : UCOS2_Verify_State) : Prop :=
  UCOS2_verification_slice_state_inv sg post.

(** Reversible event localization used around the source dereferences. *)
Definition sem_pend_rep_no_event
  (sg : StableGlobVars) (post : UCOS2_Verify_State)
  (eid : EventID) : Assertion :=
  interrupt_inv sg post.(IntrState) **
  verification_slice_task_inv sg post.(TskState) **
  verification_slice_sched_inv sg post.(TskState) post.(SchedState) **
  verification_slice_event_inv_no_eid sg post.(TskState) post.(EventState) eid **
  verification_slice_tick_inv sg post.(TickState) **
  coq_prop (verification_slice_cross_module_consistency sg post).

Definition sem_pend_public_event_domain_prop
  (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (pevent : addr) (eid : EventID) (e : OSEventAbstractState)
  (etype ecnt eptr egrp : Z) (tbl : list Z)
  (type_addr ptr_addr cnt_addr grp_addr tbl_addr : addr) : Prop :=
  pevent <> 0 /\
  valid_event_id sg eid /\
  pevent = event_addr sg eid /\
  event_snapshot_of_prop
    sg entry.(TskState) entry.(EventState) eid e
    etype ecnt eptr egrp tbl /\
  event_core_fields_layout_prop
    sg eid type_addr ptr_addr cnt_addr /\
  event_wait_fields_layout_prop sg eid grp_addr tbl_addr.

Definition sem_pend_selected_event_prop
  (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState)
  (etype ecnt eptr egrp : Z) (tbl : list Z) : Prop :=
  valid_event_id sg eid /\
  entry.(EventState).(inUsedEventStates) eid = Some e /\
  event_snapshot_of_prop
    sg entry.(TskState) entry.(EventState) eid e
    etype ecnt eptr egrp tbl /\
  etype = encode_event_type e.(eventType) /\
  ecnt = encode_event_cnt_value e /\
  egrp = encode_event_wait_grp e.(waitList) entry.(TskState).

Definition sem_pend_task_snapshot_prop
  (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (cur_tid : TaskID) (cur_t : TaskAbstractState)
  (tcbcur prio stat statpend dly eventptr
   eventmultiptr eventmultirdy : Z) : Prop :=
  task_mutex_full_snapshot_of_prop
    sg entry.(TskState) cur_tid cur_t
    tcbcur prio stat statpend dly eventptr
    eventmultiptr eventmultirdy.

(** L1 representation bridge for the concrete focus used throughout
    OSSemPend.  QCP keeps C structure-field and symbol addresses opaque,
    while the shared task/scheduler representations use canonical offsets
    and stable-global projections.  These equalities are compiler-layout
    facts supplied at the public boundary and framed across the complete
    operation; they impose no behavioural restriction on an input state. *)
Definition sem_pend_runtime_layout_prop
  (sg : StableGlobVars) (tcbcur : addr)
  (prio_addr stat_addr statpend_addr dly_addr eventptr_addr
   eventmultiptr_addr eventmultirdy_addr
   tcbcur_global_addr rdygrp_global_addr priocur_global_addr : addr) : Prop :=
  prio_addr = tcbcur + verification_slice_OSTCBPrio_off /\
  stat_addr = tcbcur + verification_slice_OSTCBStat_off /\
  statpend_addr = tcbcur + verification_slice_OSTCBStatPend_off /\
  dly_addr = tcbcur + verification_slice_OSTCBDly_off /\
  eventptr_addr = tcbcur + verification_slice_OSTCBEventPtr_off /\
  eventmultiptr_addr = tcbcur + verification_slice_OSTCBEventMultiPtr_off /\
  eventmultirdy_addr = tcbcur + verification_slice_OSTCBEventMultiRdy_off /\
  os_tcb_cur_addr sg tcbcur_global_addr /\
  os_rdy_grp_addr sg rdygrp_global_addr /\
  os_prio_cur_addr sg priocur_global_addr.

Definition sem_pend_task_entry_prop
  (cur_t : TaskAbstractState) : Prop :=
  task_mutex_pend_entry_prop cur_t.

(** Source-ordered guard.  The current-task facts are required only in the
    final arm reached after type, ISR and scheduler-lock rejection. *)
Definition sem_pend_task_sched_guard_prop
  (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (pevent etype isr lock : Z)
  (cur_tid : TaskID) (cur_t : TaskAbstractState)
  (tcbcur prio stat statpend dly eventptr
   eventmultiptr eventmultirdy rdygrp priocur : Z)
  (rdytbl : list Z) : Prop :=
  pevent = 0 \/
  (pevent <> 0 /\ etype <> encode_event_type OS_EVENT_TYPE_SEM) \/
  (pevent <> 0 /\ etype = encode_event_type OS_EVENT_TYPE_SEM /\
   isr > 0) \/
  (pevent <> 0 /\ etype = encode_event_type OS_EVENT_TYPE_SEM /\
   isr <= 0 /\ lock > 0) \/
  (pevent <> 0 /\ etype = encode_event_type OS_EVENT_TYPE_SEM /\
   isr <= 0 /\ lock <= 0 /\ tcbcur <> 0 /\
   verification_slice_sched_tcb_cur_snapshot_prop sg entry.(SchedState) tcbcur /\
   sem_pend_task_snapshot_prop
     sg entry cur_tid cur_t tcbcur prio stat statpend dly
     eventptr eventmultiptr eventmultirdy /\
   sem_pend_task_entry_prop cur_t /\
   sched_ready_prio_snapshot_prop
     sg entry.(TskState) entry.(SchedState)
     rdygrp rdytbl priocur).

Definition sem_pend_immediate_step_prop
  (entry post : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState) : Prop :=
  post = sem_pend_decrement_state entry eid e.

Definition sem_pend_resume_task_prop
  (sg : StableGlobVars) (eid cur_tid : Z)
  (entry : UCOS2_Verify_State) (res : SemPendResumeResult)
  (cur_t : TaskAbstractState)
  (tcbcur stat statpend dly eventptr : Z) : Prop :=
  entry.(TskState).(inUsedTaskStates) cur_tid = Some cur_t /\
  tcbcur = verification_slice_tcb_addr sg cur_tid /\
  stat = encode_sem_pend_resume_stat res /\
  statpend = encode_sem_pend_resume_statpend res /\
  dly = 0 /\
  eventptr = encode_sem_pend_resume_event_ptr
               res (event_addr sg eid).

(** Focused concrete handoff from the first Restore to OS_Sched.  All
    unmentioned task/event/global resources stay in the caller frame. *)
Definition sem_pend_sched_pre
  (sg : StableGlobVars) (eid cur_tid : Z) (tcbcur : addr)
  (cur_t : TaskAbstractState)
  (wait_state frame_state outside_state : UCOS2_Verify_State)
  (timeout cur_prio prio_cur event_grp : Z)
  (event_tbl : list Z) (rdy_grp : Z) (rdy_tbl : list Z) : Assertion :=
  coq_prop
    (outside_state = wait_state /\
     sem_pend_wait_step sg eid timeout frame_state wait_state /\
     tcbcur = verification_slice_tcb_addr sg cur_tid) &&
  OutsideCritical (sg, outside_state) **
  interrupt_inv sg outside_state.(IntrState) **
  sg.(g_OSTCBCur) # Ptr |-> tcbcur **
  (tcbcur + verification_slice_OSTCBPrio_off) # UChar |-> cur_prio **
  (tcbcur + verification_slice_OSTCBStat_off) # UChar |-> 1 **
  (tcbcur + verification_slice_OSTCBStatPend_off) # UChar |-> 0 **
  (tcbcur + verification_slice_OSTCBDly_off) # UInt |-> timeout **
  (tcbcur + verification_slice_OSTCBEventPtr_off) # Ptr |-> event_addr sg eid **
  used_task_pend_rest sg tcbcur cur_tid cur_t **
  sg.(g_OSRdyGrp) # UChar |-> rdy_grp **
  store_osrdytbl sg rdy_tbl **
  sg.(g_OSPrioCur) # UChar |-> prio_cur **
  verification_slice_sched_inv_rest_ready_current
    sg frame_state.(TskState) frame_state.(SchedState) **
  (event_addr sg eid + OSEventGrp_off) # UChar |-> event_grp **
  store_oseventtbl sg (event_addr sg eid) event_tbl.

Definition sem_pend_cleanup_nonintr_rest
  (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (cur_tid : TaskID) (cur_t : TaskAbstractState) : Assertion :=
  coq_prop (s.(TskState).(inUsedTaskStates) cur_tid = Some cur_t) &&
  used_task_cleanup_rest sg (verification_slice_tcb_addr sg cur_tid) cur_tid cur_t **
  verification_slice_task_inv_no_tid sg s.(TskState) cur_tid **
  verification_slice_sched_inv_no_tcb_cur sg s.(TskState) s.(SchedState) **
  verification_slice_event_inv sg s.(TskState) s.(EventState) **
  verification_slice_tick_inv sg s.(TickState) **
  coq_prop (verification_slice_cross_module_consistency sg s).

Definition sem_pend_cleanup_rest
  (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (cur_tid : TaskID) (cur_t : TaskAbstractState) : Assertion :=
  interrupt_inv sg s.(IntrState) **
  sem_pend_cleanup_nonintr_rest sg s cur_tid cur_t.

(** The Restore call consumes the exact token produced by its matching Save.
    Kinds 0/1/2 denote immediate decrement, first wait exit, and the complete
    post-resume tail respectively. *)
Definition sem_pend_restore_transition_prop
  (sg : StableGlobVars)
  (entry critical_entry post : UCOS2_Verify_State)
  (eid cur_tid timeout kind : Z) (e : OSEventAbstractState)
  (resume_res : SemPendResumeResult) : Prop :=
  crit_rel_no_os_state_change entry critical_entry /\
  ((kind = 0 /\ post = sem_pend_decrement_state entry eid e) \/
   (kind = 1 /\ sem_pend_wait_step sg eid timeout entry post) \/
   (kind = 2 /\
    sem_pend_final_step eid cur_tid resume_res entry post)).

Import ListNotations.
Local Open Scope Z_scope.

Require Import Coq.Logic.FunctionalExtensionality.
Lemma sem_pend_table_group_to_event_rest__early_errors_and_guards :
  forall sg tskSt evSt eid e base grp_addr
         etype ecnt eptr egrp etbl,
    event_snapshot_of_prop sg tskSt evSt eid e
      etype ecnt eptr egrp etbl ->
    grp_addr = event_addr sg eid + OSEventGrp_off ->
    base = event_addr sg eid ->
    grp_addr # UChar |-> egrp **
    store_oseventtbl sg base etbl |--
    used_event_rest_no_type_cnt_ptr sg tskSt base eid e.
Proof.
  intros sg tskSt evSt eid e base grp_addr
    etype ecnt eptr egrp etbl Hsnap Hgrp Hbase.
  unfold event_snapshot_of_prop in Hsnap.
  destruct Hsnap as [_ [_ [_ [_ [Hegrp Hetbl]]]]].
  subst base. subst grp_addr. subst egrp. subst etbl.
  unfold store_oseventtbl, store_array,
    used_event_rest_no_type_cnt_ptr,
    encode_event_wait_tbl_values, oseventtbl_element_store.
  simpl.
  pureIntros.
  cancel.
Qed.
Lemma sem_pend_event_rebuild__early_errors_and_guards :
  forall sg tskSt evSt eid e base
         type_addr ptr_addr cnt_addr grp_addr tbl_addr
         etype ecnt eptr egrp etbl,
    event_snapshot_of_prop sg tskSt evSt eid e
      etype ecnt eptr egrp etbl ->
    event_core_fields_layout_prop sg eid
      type_addr ptr_addr cnt_addr ->
    event_wait_fields_layout_prop sg eid grp_addr tbl_addr ->
    base = event_addr sg eid ->
    type_addr # UChar |-> etype **
    ptr_addr # Ptr |-> eptr **
    cnt_addr # UShort |-> ecnt **
    grp_addr # UChar |-> egrp **
    store_oseventtbl sg base etbl **
    verification_slice_event_inv_no_eid sg tskSt evSt eid |--
    verification_slice_event_inv sg tskSt evSt.
Proof.
  intros sg tskSt evSt eid e base
    type_addr ptr_addr cnt_addr grp_addr tbl_addr
    etype ecnt eptr egrp etbl Hsnap Hcore Hwait Hbase.
  unfold event_wait_fields_layout_prop in Hwait.
  destruct Hwait as [Hgrp _].
  sep_apply_l_atomic
    (sem_pend_table_group_to_event_rest__early_errors_and_guards
      sg tskSt evSt eid e base grp_addr
      etype ecnt eptr egrp etbl Hsnap Hgrp Hbase).
  pose proof Hsnap as Hfields.
  unfold event_snapshot_of_prop in Hfields.
  destruct Hfields as [Heid [Hetype [Hecnt [Heptr [Hegrp Hetbl]]]]].
  assert (Hcomplete :
    type_addr # UChar |-> etype **
    ptr_addr # Ptr |-> eptr **
    cnt_addr # UShort |-> ecnt **
    used_event_rest_no_type_cnt_ptr sg tskSt base eid e |--
    used_complete_event sg tskSt (event_addr sg eid) eid e).
  { unfold event_core_fields_layout_prop in Hcore.
    destruct Hcore as [Htypeaddr [Hptraddr Hcntaddr]].
    rewrite Htypeaddr, Hptraddr, Hcntaddr, Hetype, Hecnt, Heptr, Hbase.
    unfold used_complete_event, used_event_rest_no_type_cnt_ptr.
    entailer!. }
  sep_apply_l_atomic Hcomplete.
  unfold verification_slice_event_inv, verification_slice_event_inv_no_eid,
    store_used_event_map, store_used_event_map_missing_i.
  entailer!.
  sep_apply_l_atomic (store_map_merge
    (fun eid0 e0 => used_complete_event sg tskSt
      (event_addr sg eid0) eid0 e0)
    eid e (inUsedEventStates evSt) Heid).
  entailer!.
Qed.
Lemma sem_pend_interrupt_rebuild__early_errors_and_guards :
  forall sg s int_addr lock_addr isr lock,
    os_int_nesting_addr sg int_addr ->
    os_lock_nesting_addr sg lock_addr ->
    isr = s.(intNesting) ->
    lock = s.(lockNesting) ->
    int_addr # UChar |-> isr **
    lock_addr # UChar |-> lock **
    interrupt_inv_no_nesting_cells s |--
    interrupt_inv sg s ** TT.
Proof.
  intros sg s int_addr lock_addr isr lock
    Hintaddr Hlockaddr Hisr Hlock.
  unfold os_int_nesting_addr in Hintaddr.
  unfold os_lock_nesting_addr in Hlockaddr.
  subst int_addr. subst lock_addr. subst isr. subst lock.
  unfold interrupt_inv, store_int_state,
    interrupt_inv_no_nesting_cells.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel.
Qed.
Lemma sem_pend_inv_preserve_validity__early_errors_and_guards :
  forall sg s,
    UCOS2_verification_slice_inv sg s |--
    UCOS2_verification_slice_inv sg s &&
    coq_prop (UCOS2_verification_slice_state_inv sg s).
Proof.
  intros sg s.
  apply _derivable1_andp_intros.
  - cancel (UCOS2_verification_slice_inv sg s).
  - sep_apply_l_atomic
      (UCOS2_verification_slice_inv_split_raw_validity sg s).
    andp_cancel.
Qed.
Lemma sem_pend_decrement_validity__entry_localization_and_immediate :
  forall sg entry eid e sf,
    UCOS2_verification_slice_state_inv sg entry ->
    entry.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_SEM ->
    e.(semFields) = Some sf ->
    0 < sf.(semCount) ->
    UCOS2_verification_slice_state_inv sg
      (sem_pend_decrement_state entry eid e).
Proof.
  intros sg entry eid e sf Hvalid Hlookup Htype Hsf Hpositive.
  assert (Hencode_count : encode_event_cnt_value e = sf.(semCount)).
  {
    unfold encode_event_cnt_value.
    rewrite Htype, Hsf.
    reflexivity.
  }
  destruct Hvalid as
    [Htask_valid [Hsched_valid [Hevent_valid Hcross_valid]]].
  set (e_post := sem_pend_event_with_count e
    (encode_event_cnt_value e - 1)).
  assert (Hpost_lookup : forall mid,
    inUsedEventStates (EventState
      (sem_pend_decrement_state entry eid e)) mid =
    if Z.eqb mid eid then Some e_post
    else entry.(EventState).(inUsedEventStates) mid).
  {
    intro mid.
    unfold sem_pend_decrement_state, update_event_field_raw, e_post.
    reflexivity.
  }
  assert (Hevent_post : verification_slice_event_in_range sg
    (TskState (sem_pend_decrement_state entry eid e))
    (EventState (sem_pend_decrement_state entry eid e))).
  {
    unfold verification_slice_event_in_range, verification_slice_event_in_range,
      verification_slice_event_in_range in Hevent_valid |- *.
    destruct Hevent_valid as
      [Hrange [Hnodup [Hfree_range [Hpartition
        [Hfields [Hpayload [Hqueue Hwait]]]]]]].
    split.
    - intros mid evx Hget.
      rewrite Hpost_lookup in Hget.
      destruct (Z.eqb mid eid) eqn:Hmid.
      + apply Z.eqb_eq in Hmid. subst mid.
        inversion Hget; subst evx.
        exact (Hrange eid e Hlookup).
      + exact (Hrange mid evx Hget).
    - split.
      + cbn [sem_pend_decrement_state update_event_field_raw].
        exact Hnodup.
      + split.
        * cbn [sem_pend_decrement_state update_event_field_raw].
          exact Hfree_range.
        * split.
          -- unfold event_slot_partition in Hpartition |- *.
             destruct Hpartition as [Hfree Hnone].
             split.
             ++ intros mid Hin.
                rewrite Hpost_lookup.
                destruct (Z.eqb mid eid) eqn:Hmid.
                ** apply Z.eqb_eq in Hmid. subst mid.
                   specialize (Hfree eid Hin).
                   rewrite Hlookup in Hfree.
                   discriminate.
                ** exact (Hfree mid Hin).
             ++ intros mid Hvalid_mid Hnone_post.
                rewrite Hpost_lookup in Hnone_post.
                destruct (Z.eqb mid eid) eqn:Hmid.
                ** discriminate.
                ** exact (Hnone mid Hvalid_mid Hnone_post).
          -- split.
             ++ intros mid evx Hget.
                rewrite Hpost_lookup in Hget.
                destruct (Z.eqb mid eid) eqn:Hmid.
                ** apply Z.eqb_eq in Hmid. subst mid.
                   inversion Hget; subst evx.
                   pose proof (Hfields eid e Hlookup) as Hfields_old.
                   unfold event_fields_consistency in Hfields_old |- *.
                   rewrite Htype in Hfields_old.
                   unfold e_post, sem_pend_event_with_count.
                   simpl.
                   rewrite Htype.
                   simpl.
                   destruct Hfields_old as
                     [Hmutex [_ [Hmbox Hqueue_none]]].
                   repeat split; try assumption; discriminate.
                ** exact (Hfields mid evx Hget).
             ++ split.
                ** intros mid evx Hget.
                   rewrite Hpost_lookup in Hget.
                   destruct (Z.eqb mid eid) eqn:Hmid.
                   --- apply Z.eqb_eq in Hmid. subst mid.
                       inversion Hget; subst evx.
                       pose proof (Hpayload eid e Hlookup) as Hpayload_old.
                       unfold event_payload_consistency in Hpayload_old |- *.
                       rewrite Htype, Hsf in Hpayload_old.
                       simpl in Hpayload_old.
                       destruct Hpayload_old as [Hcount_old Hwait_old].
                       unfold e_post, sem_pend_event_with_count.
                       simpl.
                       rewrite Htype.
                       simpl.
                       rewrite Hencode_count.
                       cbn.
                       split.
                       { change (0 <= sf.(semCount) - 1 <= 65535).
                         lia. }
                       { intro Hwait_nonempty.
                         specialize (Hwait_old Hwait_nonempty).
                         lia. }
                   --- exact (Hpayload mid evx Hget).
                ** split.
                   --- cbn [sem_pend_decrement_state update_event_field_raw].
                       eapply queue_binding_unique_update_same_binding.
                       +++ exact Hlookup.
                       +++ unfold event_queue_id, e_post,
                             sem_pend_event_with_count.
                           simpl. rewrite Htype. reflexivity.
                       +++ exact Hqueue.
                   --- intros mid evx Hget.
                       rewrite Hpost_lookup in Hget.
                       destruct (Z.eqb mid eid) eqn:Hmid.
                       +++ apply Z.eqb_eq in Hmid. subst mid.
                           inversion Hget; subst evx.
                           eapply verification_slice_event_wait_entry_consistency_irrelevant_fields.
                           *** unfold e_post, sem_pend_event_with_count.
                               reflexivity.
                           *** unfold e_post, sem_pend_event_with_count.
                               reflexivity.
                           *** exact (Hwait eid e Hlookup).
                       +++ exact (Hwait mid evx Hget).
  }
  assert (Hmutex_back : forall mid e0 m,
    inUsedEventStates (EventState
      (sem_pend_decrement_state entry eid e)) mid = Some e0 ->
    e0.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e0.(mutexFields) = Some m ->
    entry.(EventState).(inUsedEventStates) mid = Some e0).
  {
    intros mid e0 m Hget Htype0 Hmf0.
    rewrite Hpost_lookup in Hget.
    destruct (Z.eqb mid eid) eqn:Hmid.
    - inversion Hget; subst e0.
      unfold e_post, sem_pend_event_with_count in Htype0.
      simpl in Htype0.
      rewrite Htype in Htype0.
      discriminate.
    - exact Hget.
  }
  assert (Hmutex_forward : forall mid e0 m,
    entry.(EventState).(inUsedEventStates) mid = Some e0 ->
    e0.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e0.(mutexFields) = Some m ->
    inUsedEventStates (EventState
      (sem_pend_decrement_state entry eid e)) mid = Some e0).
  {
    intros mid e0 m Hget Htype0 Hmf0.
    rewrite Hpost_lookup.
    destruct (Z.eqb mid eid) eqn:Hmid.
    - apply Z.eqb_eq in Hmid. subst mid.
      rewrite Hlookup in Hget.
      inversion Hget; subst e0.
      rewrite Htype in Htype0.
      discriminate.
    - exact Hget.
  }
  assert (Hcross_post : verification_slice_cross_module_consistency sg
    (sem_pend_decrement_state entry eid e)).
  {
    unfold sem_pend_decrement_state.
    unfold verification_slice_cross_module_consistency in Hcross_valid |- *.
    destruct Hcross_valid as
      [Hos [Hpt [Hmo [Hwait_cross [Hready [Horder
        [Hceil [Hunique [Hprotocol Hpcp_unique]]]]]]]]].
    split; [| split; [| split; [| split; [| split; [| split;
      [| split; [| split; [| split]]]]]]]].
    - eapply osprio_cur_consistency_indep_EventState
        with (lvs1 := entry).
      + reflexivity.
      + reflexivity.
      + exact Hos.
    - unfold priotbl_consistency in Hpt |- *.
      intro p.
      specialize (Hpt p).
      repeat rewrite replace_EventS_other_Tsk.
      repeat rewrite replace_EventS_other_Sched.
      repeat rewrite replace_EventS_EventState.
      destruct (prioTbl (TskState entry) p) as [| |tid] eqn:Hslot.
      + destruct Hpt as [Hnot_task Hnot_mutex].
        split; [exact Hnot_task |].
        intros [mid [e0 [m [Hget [Htype0 [Hmf0 Hreserve]]]]]].
        apply Hnot_mutex.
        exists mid, e0, m.
        split.
        * eapply Hmutex_back; eauto.
        * split; [exact Htype0 |].
          split; [exact Hmf0 | exact Hreserve].
      + destruct Hpt as
          [mid [e0 [m [Hget [Htype0 [Hmf0 [Hpcp Howner]]]]]]].
        exists mid, e0, m.
        split.
        * eapply Hmutex_forward; eauto.
        * split; [exact Htype0 |].
          split; [exact Hmf0 |].
          split; [exact Hpcp | exact Howner].
      + destruct Hpt as [t [Htask [Htask_prio | Hmutex_slot]]].
        * exists t. split; [exact Htask |]. left. exact Htask_prio.
        * destruct Hmutex_slot as
            [mid [e0 [m [Hget [Htype0 [Hmf0 [Howner Hsource]]]]]]].
          exists t. split; [exact Htask |]. right.
          exists mid, e0, m.
          split.
          -- eapply Hmutex_forward; eauto.
          -- split; [exact Htype0 |].
             split; [exact Hmf0 |].
             split; [exact Howner | exact Hsource].
    - unfold mutex_owner_consistency in Hmo |- *.
      intros mid e0 m [Hget [Htype0 Hmf0]].
      apply (Hmo mid e0 m).
      split.
      + eapply Hmutex_back; eauto.
      + split; [exact Htype0 | exact Hmf0].
    - unfold verification_slice_event_wait_object_consistency in Hwait_cross |- *.
      destruct Hwait_cross as [Hentries [Hrefback Hclosed]].
      split; [| split].
      + intros mid e0 Hget.
        rewrite Hpost_lookup in Hget.
        destruct (Z.eqb mid eid) eqn:Hmid.
        * apply Z.eqb_eq in Hmid. subst mid.
          inversion Hget; subst e0.
          eapply verification_slice_event_wait_entry_consistency_irrelevant_fields.
          -- unfold e_post, sem_pend_event_with_count. reflexivity.
          -- unfold e_post, sem_pend_event_with_count. reflexivity.
          -- exact (Hentries eid e Hlookup).
        * exact (Hentries mid e0 Hget).
      + unfold
          Ucos2Verify.lib.event_wait.task_event_reference_backlink_consistency
          in Hrefback |- *.
        intros tid0 t mid e0 Htask Hget Href.
        repeat rewrite replace_EventS_other_Tsk in Htask.
        rewrite Hpost_lookup in Hget.
        destruct (Z.eqb mid eid) eqn:Hmid.
        * apply Z.eqb_eq in Hmid. subst mid.
          inversion Hget; subst e0.
          change (List.In tid0 e.(waitList)).
          eapply Hrefback; eauto.
        * eapply Hrefback; eauto.
      + eapply Ucos2Verify.lib.event_wait.task_event_reference_closure_preserved_by_event_extension.
        * intros mid [e0 Hget].
          rewrite Hpost_lookup.
          destruct (Z.eqb mid eid).
          -- eexists. reflexivity.
          -- exists e0. exact Hget.
        * exact Hclosed.
    - eapply ready_list_completeness_indep_EventState
        with (lvs1 := entry).
      + reflexivity.
      + reflexivity.
      + exact Hready.
    - eapply ready_list_order_indep_EventState
        with (lvs1 := entry).
      + reflexivity.
      + reflexivity.
      + exact Horder.
    - unfold ceiling_priotbl_free in Hceil |- *.
      repeat rewrite replace_EventS_other_Tsk.
      exact Hceil.
    - unfold task_priority_unique_prop in Hunique |- *.
      repeat rewrite replace_EventS_other_Tsk.
      exact Hunique.
    - unfold mutex_protocol_consistency in Hprotocol |- *.
      intros mid e0 m Hget Htype0 Hmf0.
      apply (Hprotocol mid e0 m).
      + eapply Hmutex_back; eauto.
      + exact Htype0.
      + exact Hmf0.
    - eapply mutex_enabled_pcp_unique_transport
        with (lvs1 := entry).
      + intros mid e0 m Hget Htype0 Hmf0.
        exists e0, m.
        repeat split; try assumption; try reflexivity.
        eapply Hmutex_back; eauto.
      + exact Hpcp_unique.
  }
  unfold UCOS2_verification_slice_state_inv.
  split.
  - repeat rewrite replace_EventS_other_Tsk.
    exact Htask_valid.
  - split.
    + repeat rewrite replace_EventS_other_Tsk.
      repeat rewrite replace_EventS_other_Sched.
      exact Hsched_valid.
    + split; [exact Hevent_post | exact Hcross_post].
Qed.
Lemma task_validity_same_prio_update__blocked_tail_second_restore :
  forall sg st tid old new,
    st.(inUsedTaskStates) tid = Some old ->
    new.(curPrio) = old.(curPrio) ->
    verification_slice_task_validity sg st ->
    verification_slice_task_validity sg (glob_task_set_usedtask st tid new).
Proof.
  intros sg st tid old new Hlookup Hprio [Hrange Hderived].
  unfold verification_slice_task_in_range in Hrange.
  destruct Hrange as
    [Hids [Hfree_nodup [Hfree_range [Hfree_unused
      [Htable_live [Hregistered Hunique]]]]]].
  split.
  - unfold verification_slice_task_in_range,
      glob_task_set_usedtask.
    cbn.
    split.
    + intros tid0 t0 Hlookup0.
      destruct (Z.eqb tid0 tid) eqn:Heq.
      * apply Z.eqb_eq in Heq. subst tid0.
        inversion Hlookup0; subst t0.
        eapply Hids. exact Hlookup.
      * eapply Hids. exact Hlookup0.
    + split; [exact Hfree_nodup |].
      split; [exact Hfree_range |].
      split.
      * intros tid0 Hin.
        destruct (Z.eqb tid0 tid) eqn:Heq.
        -- apply Z.eqb_eq in Heq. subst tid0.
           pose proof (Hfree_unused tid Hin) as Hnone.
           rewrite Hlookup in Hnone. discriminate.
        -- exact (Hfree_unused tid0 Hin).
      * split.
        -- intros p tid0 Htable.
           destruct (Htable_live p tid0 Htable)
             as [Hvalid_p [t0 Hlookup0]].
           split; [exact Hvalid_p |].
           destruct (Z.eqb tid0 tid) eqn:Heq.
           ++ apply Z.eqb_eq in Heq. subst tid0.
              exists new. reflexivity.
           ++ exists t0. exact Hlookup0.
        -- split.
           ++ eapply glob_task_set_usedtask_preserves_current_prio_registered.
              ** exact Hlookup.
              ** exact Hprio.
              ** exact Hregistered.
           ++ unfold task_priority_unique.
              cbn.
              intros tid1 tid2 t1 t2 Hlookup1 Hlookup2 Heq_prio.
              destruct (Z.eqb tid1 tid) eqn:Heq1;
                destruct (Z.eqb tid2 tid) eqn:Heq2.
              ** apply Z.eqb_eq in Heq1, Heq2. congruence.
              ** apply Z.eqb_eq in Heq1. subst tid1.
                 inversion Hlookup1; subst t1.
                 assert (tid2 = tid).
                 { eapply Hunique.
                   - exact Hlookup2.
                   - exact Hlookup.
                   - rewrite <- Hprio. symmetry. exact Heq_prio. }
                 subst tid2. rewrite Z.eqb_refl in Heq2. discriminate.
              ** apply Z.eqb_eq in Heq2. subst tid2.
                 inversion Hlookup2; subst t2.
                 assert (tid1 = tid).
                 { eapply Hunique.
                   - exact Hlookup1.
                   - exact Hlookup.
                   - rewrite <- Hprio. exact Heq_prio. }
                 subst tid1. rewrite Z.eqb_refl in Heq1. discriminate.
              ** eapply Hunique; eassumption.
  - intros tid0 t0 Hlookup0.
    unfold glob_task_set_usedtask in Hlookup0.
    cbn in Hlookup0.
    destruct (Z.eqb tid0 tid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst tid0.
      inversion Hlookup0; subst t0.
      pose proof (Hderived tid old Hlookup) as [Hvalid_p Hfields].
      split.
      * rewrite Hprio. exact Hvalid_p.
      * unfold valid_derived_fields in *.
        rewrite Hprio. exact Hfields.
    + exact (Hderived tid0 t0 Hlookup0).
Qed.
Lemma glob_task_set_usedtask_lookup__blocked_tail_second_restore :
  forall st tid new id,
    (glob_task_set_usedtask st tid new).(inUsedTaskStates) id =
    if Z.eqb id tid then Some new else st.(inUsedTaskStates) id.
Proof. reflexivity. Qed.
Lemma task_lookup_post_to_pre_same_prio__blocked_tail_second_restore :
  forall st tid old new id post_t,
    st.(inUsedTaskStates) tid = Some old ->
    new.(curPrio) = old.(curPrio) ->
    (glob_task_set_usedtask st tid new).(inUsedTaskStates) id = Some post_t ->
    exists pre_t,
      st.(inUsedTaskStates) id = Some pre_t /\
      post_t.(curPrio) = pre_t.(curPrio).
Proof.
  intros st tid old new id post_t Hlookup Hprio Hpost.
  rewrite glob_task_set_usedtask_lookup__blocked_tail_second_restore
    in Hpost.
  destruct (Z.eqb id tid) eqn:Heq.
  - apply Z.eqb_eq in Heq. subst id.
    inversion Hpost; subst post_t.
    exists old. split; assumption.
  - exists post_t. split; [exact Hpost | reflexivity].
Qed.
Lemma task_lookup_pre_to_post_same_prio__blocked_tail_second_restore :
  forall st tid old new id pre_t,
    st.(inUsedTaskStates) tid = Some old ->
    new.(curPrio) = old.(curPrio) ->
    st.(inUsedTaskStates) id = Some pre_t ->
    exists post_t,
      (glob_task_set_usedtask st tid new).(inUsedTaskStates) id = Some post_t /\
      post_t.(curPrio) = pre_t.(curPrio).
Proof.
  intros st tid old new id pre_t Hlookup Hprio Hpre.
  destruct (Z.eqb id tid) eqn:Heq.
  - apply Z.eqb_eq in Heq. subst id.
    rewrite Hlookup in Hpre. inversion Hpre; subst pre_t.
    exists new. split.
    + rewrite glob_task_set_usedtask_lookup__blocked_tail_second_restore,
        Z.eqb_refl. reflexivity.
    + exact Hprio.
  - exists pre_t. split.
    + rewrite glob_task_set_usedtask_lookup__blocked_tail_second_restore,
        Heq. exact Hpre.
    + reflexivity.
Qed.
Lemma task_prio_lookup_equiv_update__blocked_tail_second_restore :
  forall st tid old new,
    st.(inUsedTaskStates) tid = Some old ->
    new.(curPrio) = old.(curPrio) ->
    forall id,
      match
        (glob_task_set_usedtask st tid new).(inUsedTaskStates) id,
        st.(inUsedTaskStates) id
      with
      | Some t1, Some t2 => t1.(curPrio) = t2.(curPrio)
      | None, None => True
      | _, _ => False
      end.
Proof.
  intros st tid old new Hlookup Hprio id.
  unfold glob_task_set_usedtask. cbn.
  destruct (Z.eqb id tid) eqn:Heq.
  - apply Z.eqb_eq in Heq. subst id.
    rewrite Hlookup. exact Hprio.
  - destruct (st.(inUsedTaskStates) id); reflexivity.
Qed.
Lemma ready_grp_prio_equiv__blocked_tail_second_restore :
  forall rl st1 st2,
    (forall id,
      match st1.(inUsedTaskStates) id, st2.(inUsedTaskStates) id with
      | Some t1, Some t2 => t1.(curPrio) = t2.(curPrio)
      | None, None => True
      | _, _ => False
      end) ->
    encode_ready_grp rl st1 = encode_ready_grp rl st2.
Proof.
  induction rl as [|a rest IH]; intros st1 st2 Hequiv.
  - reflexivity.
  - cbn [encode_ready_grp].
    pose proof (Hequiv a) as Ha.
    destruct (st1.(inUsedTaskStates) a) as [t1|] eqn:H1;
      destruct (st2.(inUsedTaskStates) a) as [t2|] eqn:H2;
      cbn in Ha; try contradiction.
    + rewrite Ha. f_equal. apply IH. exact Hequiv.
    + apply IH. exact Hequiv.
Qed.
Lemma ready_grp_same_prio_update__blocked_tail_second_restore :
  forall rl st tid old new,
    st.(inUsedTaskStates) tid = Some old ->
    new.(curPrio) = old.(curPrio) ->
    encode_ready_grp rl (glob_task_set_usedtask st tid new) =
    encode_ready_grp rl st.
Proof.
  intros.
  apply ready_grp_prio_equiv__blocked_tail_second_restore.
  eapply task_prio_lookup_equiv_update__blocked_tail_second_restore;
    eassumption.
Qed.
Lemma ready_tbl_prio_equiv_acc__blocked_tail_second_restore :
  forall rl st1 st2 y acc,
    (forall id,
      match st1.(inUsedTaskStates) id, st2.(inUsedTaskStates) id with
      | Some t1, Some t2 => t1.(curPrio) = t2.(curPrio)
      | None, None => True
      | _, _ => False
      end) ->
    fold_left
      (fun acc0 tid0 =>
         match st1.(inUsedTaskStates) tid0 with
         | Some t =>
             if Z.eqb (t.(curPrio) / 8) y
             then acc0 + Z.shiftl 1 (t.(curPrio) mod 8)
             else acc0
         | None => acc0
         end) rl acc =
    fold_left
      (fun acc0 tid0 =>
         match st2.(inUsedTaskStates) tid0 with
         | Some t =>
             if Z.eqb (t.(curPrio) / 8) y
             then acc0 + Z.shiftl 1 (t.(curPrio) mod 8)
             else acc0
         | None => acc0
         end) rl acc.
Proof.
  induction rl as [|a rest IH]; intros st1 st2 y acc Hequiv.
  - reflexivity.
  - cbn.
    pose proof (Hequiv a) as Ha.
    destruct (st1.(inUsedTaskStates) a) as [t1|] eqn:H1;
      destruct (st2.(inUsedTaskStates) a) as [t2|] eqn:H2;
      cbn in Ha; try contradiction.
    + rewrite Ha. apply IH. exact Hequiv.
    + apply IH. exact Hequiv.
Qed.
Lemma ready_tbl_same_prio_update__blocked_tail_second_restore :
  forall rl st tid old new y,
    st.(inUsedTaskStates) tid = Some old ->
    new.(curPrio) = old.(curPrio) ->
    encode_ready_tbl_at rl (glob_task_set_usedtask st tid new) y =
    encode_ready_tbl_at rl st y.
Proof.
  intros. unfold encode_ready_tbl_at.
  apply ready_tbl_prio_equiv_acc__blocked_tail_second_restore.
  eapply task_prio_lookup_equiv_update__blocked_tail_second_restore;
    eassumption.
Qed.
Lemma event_grp_same_prio_update__blocked_tail_second_restore :
  forall wl st tid old new,
    st.(inUsedTaskStates) tid = Some old ->
    new.(curPrio) = old.(curPrio) ->
    encode_event_wait_grp wl (glob_task_set_usedtask st tid new) =
    encode_event_wait_grp wl st.
Proof.
  intros.
  change
    (encode_ready_grp wl (glob_task_set_usedtask st tid new) =
     encode_ready_grp wl st).
  apply ready_grp_same_prio_update__blocked_tail_second_restore
    with (old := old); assumption.
Qed.
Lemma event_tbl_same_prio_update__blocked_tail_second_restore :
  forall wl st tid old new y,
    st.(inUsedTaskStates) tid = Some old ->
    new.(curPrio) = old.(curPrio) ->
    encode_event_wait_tbl_at wl (glob_task_set_usedtask st tid new) y =
    encode_event_wait_tbl_at wl st y.
Proof.
  intros. unfold encode_event_wait_tbl_at.
  apply ready_tbl_prio_equiv_acc__blocked_tail_second_restore.
  eapply task_prio_lookup_equiv_update__blocked_tail_second_restore;
    eassumption.
Qed.
Lemma verification_slice_sched_in_range_same_prio_ready_update__blocked_tail_second_restore :
  forall sg st sched tid old new,
    st.(inUsedTaskStates) tid = Some old ->
    new.(curPrio) = old.(curPrio) ->
    is_effectively_ready new.(stat) new.(dly) =
      is_effectively_ready old.(stat) old.(dly) ->
    verification_slice_sched_in_range sg st sched ->
    verification_slice_sched_in_range sg (glob_task_set_usedtask st tid new) sched.
Proof.
  intros sg st sched tid old new Hlookup Hprio Hready
    [Hmembers [Hsorted [Hcomplete [Hnodup [Hctr [Hhigh Hcur]]]]]].
  split.
  - intros id Hin.
    destruct (Hmembers id Hin) as [t0 [Hget0 Heff]].
    destruct (Z.eqb id tid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst id.
      rewrite Hlookup in Hget0. inversion Hget0; subst t0.
      exists new. split.
      * rewrite glob_task_set_usedtask_lookup__blocked_tail_second_restore,
          Z.eqb_refl. reflexivity.
      * rewrite Hready. exact Heff.
    + exists t0. split.
      * rewrite glob_task_set_usedtask_lookup__blocked_tail_second_restore,
          Heq. exact Hget0.
      * exact Heff.
  - split.
    + apply
        (strictly_sorted_by_key_ext TaskID
          (fun id =>
             match st.(inUsedTaskStates) id with
             | Some t => t.(curPrio)
             | None => sg.(osLowestPrio) + 1
             end)
          (fun id =>
             match
               (glob_task_set_usedtask st tid new).(inUsedTaskStates) id
             with
             | Some t => t.(curPrio)
             | None => sg.(osLowestPrio) + 1
             end)
          sched.(readyList)).
      * intro id.
        pose proof
          (task_prio_lookup_equiv_update__blocked_tail_second_restore
             st tid old new Hlookup Hprio id) as Hobs.
        destruct
          ((glob_task_set_usedtask st tid new).(inUsedTaskStates) id)
          as [t1|] eqn:H1;
          destruct (st.(inUsedTaskStates) id) as [t2|] eqn:H2;
          cbn in Hobs; try contradiction; cbn.
        -- symmetry. exact Hobs.
        -- reflexivity.
      * exact Hsorted.
    + split.
      * intros id t0 Hget0 Heff.
        rewrite glob_task_set_usedtask_lookup__blocked_tail_second_restore
          in Hget0.
        destruct (Z.eqb id tid) eqn:Heq.
        -- apply Z.eqb_eq in Heq. subst id.
           inversion Hget0; subst t0.
           apply (Hcomplete tid old Hlookup).
           rewrite <- Hready. exact Heff.
        -- apply (Hcomplete id t0 Hget0 Heff).
      * split; [exact Hnodup |].
        split; [exact Hctr |].
        split.
        -- unfold sched_high_ready_consistency in *.
           destruct sched.(readyList) as [|head rest].
           ++ exact Hhigh.
           ++ destruct Hhigh as [Hhead [t0 [Hget0 Hhigh_prio]]].
              split; [exact Hhead |].
              destruct (Z.eqb head tid) eqn:Heq.
              ** apply Z.eqb_eq in Heq. subst head.
                 rewrite Hlookup in Hget0. inversion Hget0; subst t0.
                 exists new. split.
                 --- rewrite
                       glob_task_set_usedtask_lookup__blocked_tail_second_restore,
                       Z.eqb_refl. reflexivity.
                 --- rewrite Hprio. exact Hhigh_prio.
              ** exists t0. split.
                 --- rewrite
                       glob_task_set_usedtask_lookup__blocked_tail_second_restore,
                       Heq. exact Hget0.
                 --- exact Hhigh_prio.
        -- unfold sched_current_consistency in *.
           destruct sched.(curTaskID) as [current|].
           ++ destruct Hcur as [t0 [Hget0 Hcur_prio]].
              destruct (Z.eqb current tid) eqn:Heq.
              ** apply Z.eqb_eq in Heq. subst current.
                 rewrite Hlookup in Hget0. inversion Hget0; subst t0.
                 exists new. split.
                 --- rewrite
                       glob_task_set_usedtask_lookup__blocked_tail_second_restore,
                       Z.eqb_refl. reflexivity.
                 --- rewrite Hprio. exact Hcur_prio.
              ** exists t0. split.
                 --- rewrite
                       glob_task_set_usedtask_lookup__blocked_tail_second_restore,
                       Heq. exact Hget0.
                 --- exact Hcur_prio.
           ++ exact Hcur.
Qed.
Lemma verification_slice_event_in_range_cleanup_update__blocked_tail_second_restore :
  forall sg st ev tid old new,
    st.(inUsedTaskStates) tid = Some old ->
    new.(curPrio) = old.(curPrio) ->
    old.(eventPtr) = None ->
    new.(eventPtr) = None ->
    new.(eventMultiWaitEvents) = old.(eventMultiWaitEvents) ->
    verification_slice_event_in_range sg st ev ->
    verification_slice_event_in_range sg (glob_task_set_usedtask st tid new) ev.
Proof.
  intros sg st ev tid old new Hlookup Hprio Hold_ptr Hnew_ptr Hmulti
    [H1 [H2 [H3 [H4 [H5 [H6 [H7 Hentries]]]]]]].
  split; [exact H1 |].
  split; [exact H2 |].
  split; [exact H3 |].
  split; [exact H4 |].
  split; [exact H5 |].
  split; [exact H6 |].
  split; [exact H7 |].
  intros eid e Hevent.
  destruct (Hentries eid e Hevent) as [Hcanonical Hwaiting].
  split.
  - unfold event_waitList_canonical in *.
    destruct Hcanonical as [Hnodup [Hsorted Hlive]].
    split; [exact Hnodup |].
    split.
    + apply
        (strictly_sorted_by_key_ext TaskID
          (wait_prio_key sg st)
          (wait_prio_key sg (glob_task_set_usedtask st tid new))
          e.(waitList)).
      * intro id. unfold wait_prio_key.
        pose proof
          (task_prio_lookup_equiv_update__blocked_tail_second_restore
             st tid old new Hlookup Hprio id) as Hobs.
        destruct
          ((glob_task_set_usedtask st tid new).(inUsedTaskStates) id)
          as [t1|] eqn:Hpost;
          destruct (st.(inUsedTaskStates) id) as [t2|] eqn:Hpre;
          cbn in Hobs; try contradiction; cbn.
        -- symmetry. exact Hobs.
        -- reflexivity.
      * exact Hsorted.
    + intros id Hin.
      destruct (Hlive id Hin) as [t0 [Hget0 Hvalid_prio]].
      destruct (Z.eqb id tid) eqn:Heq.
      * apply Z.eqb_eq in Heq. subst id.
        rewrite Hlookup in Hget0. inversion Hget0; subst t0.
        exists new. split.
        -- rewrite glob_task_set_usedtask_lookup__blocked_tail_second_restore,
             Z.eqb_refl. reflexivity.
        -- rewrite Hprio. exact Hvalid_prio.
      * exists t0. split.
        -- rewrite glob_task_set_usedtask_lookup__blocked_tail_second_restore,
             Heq. exact Hget0.
        -- exact Hvalid_prio.
  - destruct (event_type_to_pend_type e.(eventType))
      as [pty|] eqn:Htype.
    + intros id Hin.
      destruct (Hwaiting id Hin)
        as [t0 [Hget0 [Hptr [Hmulti0 Hpend]]]].
      destruct (Z.eqb id tid) eqn:Heq.
      * apply Z.eqb_eq in Heq. subst id.
        rewrite Hlookup in Hget0. inversion Hget0; subst t0.
        rewrite Hold_ptr in Hptr. discriminate.
      * exists t0. split.
        -- rewrite glob_task_set_usedtask_lookup__blocked_tail_second_restore,
             Heq. exact Hget0.
        -- repeat split; assumption.
    + exact Hwaiting.
Qed.
Lemma event_wait_object_cleanup_update__blocked_tail_second_restore :
  forall sg s tid old new,
    s.(TskState).(inUsedTaskStates) tid = Some old ->
    new.(curPrio) = old.(curPrio) ->
    old.(eventPtr) = None ->
    new.(eventPtr) = None ->
    new.(eventMultiWaitEvents) = old.(eventMultiWaitEvents) ->
    verification_slice_event_wait_object_consistency sg s ->
    verification_slice_event_wait_object_consistency sg
      (replace_TskS (glob_task_set_usedtask s.(TskState) tid new) s).
Proof.
  intros sg s tid old new
    Hlookup Hprio Hold_ptr Hnew_ptr Hmulti
    [Hentries [Hrefback Hclosure]].
  set (st := s.(TskState)) in *.
  set (ev := s.(EventState)) in *.
  cbn in Hentries, Hrefback, Hclosure |- *.
  split; [|split].
  - intros eid e Hevent.
    destruct (Hentries eid e Hevent) as [Hcanonical Hwaiting].
    split.
    + unfold event_waitList_canonical in *.
      destruct Hcanonical as [Hnodup [Hsorted Hlive]].
      split; [exact Hnodup |].
      split.
      * apply
          (strictly_sorted_by_key_ext TaskID
            (wait_prio_key sg st)
            (wait_prio_key sg (glob_task_set_usedtask st tid new))
            e.(waitList)).
        -- intro id. unfold wait_prio_key.
           pose proof
             (task_prio_lookup_equiv_update__blocked_tail_second_restore
                st tid old new Hlookup Hprio id) as Hobs.
           destruct
             ((glob_task_set_usedtask st tid new).(inUsedTaskStates) id)
             as [t1|] eqn:Hpost;
             destruct (st.(inUsedTaskStates) id) as [t2|] eqn:Hpre;
             cbn in Hobs; try contradiction; cbn.
           ++ symmetry. exact Hobs.
           ++ reflexivity.
        -- exact Hsorted.
      * intros id Hin.
        destruct (Hlive id Hin) as [t0 [Hget0 Hvalid_prio]].
        destruct (task_lookup_pre_to_post_same_prio__blocked_tail_second_restore
          st tid old new id t0 Hlookup Hprio Hget0)
          as [post_t [Hpost Hpost_prio]].
        exists post_t. split; [exact Hpost |].
        unfold valid_task_prio in *.
        rewrite Hpost_prio. exact Hvalid_prio.
    + destruct (event_type_to_pend_type e.(eventType))
        as [pty|] eqn:Htype.
      * intros id Hin.
        destruct (Hwaiting id Hin)
          as [t0 [Hget0 [Hptr [Hmulti0 Hpend]]]].
        destruct (Z.eqb id tid) eqn:Heq.
        -- apply Z.eqb_eq in Heq. subst id.
           cbn in Hget0. rewrite Hlookup in Hget0.
           inversion Hget0; subst t0.
           rewrite Hold_ptr in Hptr. discriminate.
        -- exists t0. split.
           cbn.
           ++ cbn in Hget0. rewrite Heq. exact Hget0.
           ++ repeat split; assumption.
      * exact Hwaiting.
  - unfold task_event_reference_backlink_consistency in *.
    intros id t0 eid e Hget0 Hevent Href.
    cbn in Hget0, Hevent.
    destruct (Z.eqb id tid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst id.
      cbn in Hget0. injection Hget0 as Ht. subst t0.
      destruct Href as [Hptr | Hmulti_ref].
      * rewrite Hnew_ptr in Hptr. discriminate.
      * eapply Hrefback; [exact Hlookup|exact Hevent|].
        right. rewrite <- Hmulti. exact Hmulti_ref.
    + eapply Hrefback; eassumption.
  - unfold task_event_reference_closure in *.
      intros id t0 Hget0.
      cbn in Hget0.
      destruct (Z.eqb id tid) eqn:Heq.
      * apply Z.eqb_eq in Heq. subst id.
        cbn in Hget0.
        injection Hget0 as Ht. subst t0.
        destruct (Hclosure tid old Hlookup) as [_ Hmulti_old].
        split.
        -- intros eid Hptr. rewrite Hnew_ptr in Hptr. discriminate.
        -- intros eid Hin. apply Hmulti_old.
           rewrite <- Hmulti. exact Hin.
      * exact (Hclosure id t0 Hget0).
Qed.
Lemma cross_module_cleanup_update__blocked_tail_second_restore :
  forall sg s tid old new,
    s.(TskState).(inUsedTaskStates) tid = Some old ->
    new.(curPrio) = old.(curPrio) ->
    is_effectively_ready new.(stat) new.(dly) =
      is_effectively_ready old.(stat) old.(dly) ->
    old.(eventPtr) = None ->
    new.(eventPtr) = None ->
    new.(eventMultiWaitEvents) = old.(eventMultiWaitEvents) ->
    verification_slice_cross_module_consistency sg s ->
    verification_slice_cross_module_consistency sg
      (replace_TskS
        (glob_task_set_usedtask s.(TskState) tid new) s).
Proof.
  intros sg s tid old new Hlookup Hprio Hready Hold_ptr Hnew_ptr Hmulti
    [Hcur [Htable [Hmutex [Hwait [Hcomplete [Horder
      [Hceil [Hunique [Hprotocol Hpcp_unique]]]]]]]]].
  unfold verification_slice_cross_module_consistency.
  cbn [replace_TskS].
  split.
  - unfold osprio_cur_consistency in *.
    cbn in Hcur |- *.
    destruct s.(SchedState).(curTaskID) as [current|].
    + destruct Hcur as [t0 [Hget0 Hcur_prio]].
      destruct (task_lookup_pre_to_post_same_prio__blocked_tail_second_restore
        s.(TskState) tid old new current t0 Hlookup Hprio Hget0)
        as [post_t [Hpost Hpost_prio]].
      exists post_t. split; [exact Hpost |].
      rewrite Hpost_prio. exact Hcur_prio.
    + exact Hcur.
  - split.
    + unfold priotbl_consistency in *.
      cbn in Htable |- *.
      intro p. specialize (Htable p).
      destruct (s.(TskState).(prioTbl) p) as [| |table_tid] eqn:Hslot.
      * destruct Htable as [Hno_ready Hno_mutex].
        split.
        -- intros [id [Hin [post_t [Hpost Hpost_prio]]]].
           destruct
             (task_lookup_post_to_pre_same_prio__blocked_tail_second_restore
               s.(TskState) tid old new id post_t Hlookup Hprio Hpost)
             as [pre_t [Hpre Hsame]].
           apply Hno_ready. exists id. split; [exact Hin |].
           exists pre_t. split; [exact Hpre |].
           rewrite <- Hsame. exact Hpost_prio.
        -- exact Hno_mutex.
      * destruct Htable as [mid [e [m [Hevent [Htype [Hfields
          [Hpcp Howner]]]]]]].
        exists mid, e, m. repeat split; try assumption.
        destruct m.(mfOwner) as [owner|] eqn:Howner_eq.
        -- destruct Howner as [t0 [op [Hget0 [Horig Howner_prio]]]].
           destruct
             (task_lookup_pre_to_post_same_prio__blocked_tail_second_restore
               s.(TskState) tid old new owner t0 Hlookup Hprio Hget0)
             as [post_t [Hpost Hsame]].
           exists post_t, op. repeat split; try assumption.
           rewrite Hsame. exact Howner_prio.
        -- exact Howner.
      * destruct Htable as [t0 [Hget0 [Htask_prio | Howner_case]]].
        -- destruct
             (task_lookup_pre_to_post_same_prio__blocked_tail_second_restore
               s.(TskState) tid old new table_tid t0 Hlookup Hprio Hget0)
             as [post_t [Hpost Hsame]].
           exists post_t. split; [exact Hpost |]. left.
           rewrite Hsame. exact Htask_prio.
        -- destruct
             (task_lookup_pre_to_post_same_prio__blocked_tail_second_restore
               s.(TskState) tid old new table_tid t0 Hlookup Hprio Hget0)
             as [post_t [Hpost Hsame]].
           exists post_t. split; [exact Hpost |]. right.
           exact Howner_case.
    + split.
      * unfold mutex_owner_consistency in *.
        intros mid e m Hfacts.
        specialize (Hmutex mid e m Hfacts).
        destruct m.(mfOwner) as [owner|] eqn:Howner.
        -- destruct Hmutex as [t0 [op [Hget0 [Horig [Hprio_case Hnotin]]]]].
           destruct
             (task_lookup_pre_to_post_same_prio__blocked_tail_second_restore
               s.(TskState) tid old new owner t0 Hlookup Hprio Hget0)
             as [post_t [Hpost Hsame]].
           exists post_t, op. split; [exact Hpost|].
           split; [exact Horig|]. split.
           { destruct Hprio_case as [Heq | [Henabled Heq]].
             - left. rewrite Hsame. exact Heq.
             - right. split; [exact Henabled |].
               rewrite Hsame. exact Heq. }
           exact Hnotin.
        -- exact Hmutex.
      * split.
        -- unfold verification_slice_event_wait_object_consistency in *.
           eapply event_wait_object_cleanup_update__blocked_tail_second_restore
             with (s := s) (old := old); eassumption.
        -- split.
           ++ unfold ready_list_completeness in *.
              cbn in Hcomplete |- *.
              intros id post_t Hpost Heffective.
              destruct (Z.eqb id tid) eqn:Heq.
              ** apply Z.eqb_eq in Heq. subst id.
                 cbn in Hpost. inversion Hpost; subst.
                 apply (Hcomplete tid old Hlookup).
                 rewrite <- Hready. exact Heffective.
              ** exact (Hcomplete id post_t Hpost Heffective).
           ++ split.
              ** unfold ready_list_order in *.
                 destruct Horder as [Hsorted Hnodup]. split.
                 --- apply
                       (strictly_sorted_by_key_ext TaskID
                         (fun id =>
                            match s.(TskState).(inUsedTaskStates) id with
                            | Some t => t.(curPrio)
                            | None => sg.(osLowestPrio) + 1
                            end)
                         (fun id =>
                            match
                              (glob_task_set_usedtask
                                s.(TskState) tid new).(inUsedTaskStates) id
                            with
                            | Some t => t.(curPrio)
                            | None => sg.(osLowestPrio) + 1
                            end)
                         s.(SchedState).(readyList)).
                     +++ intro id.
                         pose proof
                           (task_prio_lookup_equiv_update__blocked_tail_second_restore
                             s.(TskState) tid old new Hlookup Hprio id) as Hobs.
                         destruct
                           ((glob_task_set_usedtask
                              s.(TskState) tid new).(inUsedTaskStates) id)
                           as [t1|] eqn:Hpost;
                           destruct (s.(TskState).(inUsedTaskStates) id)
                           as [t2|] eqn:Hpre;
                           cbn in Hobs; try contradiction; cbn.
                         *** symmetry. exact Hobs.
                         *** reflexivity.
                     +++ exact Hsorted.
                 --- exact Hnodup.
              ** split.
                 --- unfold ceiling_priotbl_free in *.
                     exact Hceil.
                 --- split.
                     +++ unfold task_priority_unique_prop,
                           task_priority_unique in *.
                         intros id1 id2 post1 post2 Hpost1 Hpost2 Hsame_post.
                         destruct
                           (task_lookup_post_to_pre_same_prio__blocked_tail_second_restore
                             s.(TskState) tid old new id1 post1
                             Hlookup Hprio Hpost1)
                           as [pre1 [Hpre1 Hsame1]].
                         destruct
                           (task_lookup_post_to_pre_same_prio__blocked_tail_second_restore
                             s.(TskState) tid old new id2 post2
                             Hlookup Hprio Hpost2)
                           as [pre2 [Hpre2 Hsame2]].
                         eapply Hunique; [exact Hpre1 | exact Hpre2 |].
                         rewrite <- Hsame1, <- Hsame2. exact Hsame_post.
                     +++ split.
                         *** unfold mutex_protocol_consistency in *.
                             exact Hprotocol.
                         *** unfold mutex_enabled_pcp_unique in *.
                             exact Hpcp_unique.
Qed.
Lemma used_task_cleanup_rest_clean_eq__blocked_tail_second_restore :
  forall sg base tid old new,
    new =
      {| taskID := old.(taskID);
     taskGeneration := old.(taskGeneration);
     tcbStkPtr := old.(tcbStkPtr);
     tcbExtPtr := old.(tcbExtPtr);
     tcbStkBottom := old.(tcbStkBottom);
     tcbStkSize := old.(tcbStkSize);
     tcbOpt := old.(tcbOpt);
     tcbPublicId := old.(tcbPublicId);
     tcbFlagNode := old.(tcbFlagNode);
     tcbFlagsRdy := old.(tcbFlagsRdy);
     tcbTaskName := old.(tcbTaskName);
     tcbReg0 := old.(tcbReg0);
     tcbCtxSwCtr := old.(tcbCtxSwCtr);
     tcbCyclesTot := old.(tcbCyclesTot);
     tcbCyclesStart := old.(tcbCyclesStart);
     tcbStkBase := old.(tcbStkBase);
     tcbStkUsed := old.(tcbStkUsed);
     tcbPadding42 := old.(tcbPadding42);
     tcbPadding43 := old.(tcbPadding43);
     tcbEventMultiPtr := old.(tcbEventMultiPtr);
         curPrio := old.(curPrio);
         stat := (task_status_single None ((task_is_suspended old.(stat))));
         statPend := PendOK;
         dly := old.(dly);
         eventPtr := None;
         eventMultiWaitEvents := old.(eventMultiWaitEvents);
         eventMultiRdy := old.(eventMultiRdy);
         msg := old.(msg);
         nextTCB := old.(nextTCB);
         prevTCB := old.(prevTCB);
         delReq := old.(delReq) |} ->
    used_task_cleanup_rest sg base tid new =
    used_task_cleanup_rest sg base tid old.
Proof. intros sg base tid old new Hnew. subst new. reflexivity. Qed.
Lemma verification_slice_task_inv_no_tid_cleanup_update__blocked_tail_second_restore :
  forall sg st tid old new,
    st.(inUsedTaskStates) tid = Some old ->
    new.(curPrio) = old.(curPrio) ->
    verification_slice_task_inv_no_tid sg st tid |--
    verification_slice_task_inv_no_tid sg
      (glob_task_set_usedtask st tid new) tid.
Proof.
  intros sg st tid old new Hlookup Hprio h Hinv.
  unfold verification_slice_task_inv_no_tid in *.
  destruct Hinv as [Hvalid Hspatial].
  split.
  - apply task_validity_same_prio_update__blocked_tail_second_restore
      with (old := old); try assumption.
  - destruct Hspatial as [h4 [hctr [Hj4 [H4 Hctr]]]].
    destruct H4 as [h3 [hlist [Hj3 [H3 Hlist]]]].
    destruct H3 as [h2 [hprio [Hj2 [H2 Hprio_tbl]]]].
    destruct H2 as [hmap [hfree [Hj1 [Hmap Hfree]]]].
    exists h4, hctr. split; [exact Hj4 |]. split.
    + exists h3, hlist. split; [exact Hj3 |]. split.
      * exists h2, hprio. split; [exact Hj2 |]. split.
        -- exists hmap, hfree. split; [exact Hj1 |]. split.
           ++ unfold verification_slice_store_used_task_map_missing_i in *.
              assert (Hext : forall id,
                id <> tid ->
                st.(inUsedTaskStates) id =
                (glob_task_set_usedtask st tid new).(inUsedTaskStates) id).
              { intros id Hneq.
                rewrite glob_task_set_usedtask_lookup__blocked_tail_second_restore.
                apply Z.eqb_neq in Hneq. rewrite Hneq. reflexivity. }
              pose proof
                (store_map_missing_i_equiv
                  (fun tid0 t =>
                    verification_slice_used_complete_task sg (verification_slice_tcb_addr sg tid0) tid0 t)
                  st.(inUsedTaskStates)
                  (glob_task_set_usedtask st tid new).(inUsedTaskStates)
                  tid Hext) as Hequiv.
              exact ((proj1 Hequiv) hmap Hmap).
           ++ exact Hfree.
        -- exact Hprio_tbl.
      * exact Hlist.
    + exact Hctr.
Qed.
Lemma verification_slice_sched_inv_no_tcb_cur_cleanup_update__blocked_tail_second_restore :
  forall sg st sched tid old new,
    st.(inUsedTaskStates) tid = Some old ->
    new.(curPrio) = old.(curPrio) ->
    is_effectively_ready
      new.(stat) new.(dly) =
      is_effectively_ready old.(stat) old.(dly) ->
    verification_slice_sched_inv_no_tcb_cur sg st sched |--
    verification_slice_sched_inv_no_tcb_cur sg
      (glob_task_set_usedtask st tid new) sched.
Proof.
  intros sg st sched tid old new Hlookup Hprio Hready h Hinv.
  unfold verification_slice_sched_inv_no_tcb_cur in *.
  destruct Hinv as [Hrange Hstore]. split.
  - apply verification_slice_sched_in_range_same_prio_ready_update__blocked_tail_second_restore
      with (old := old); try assumption.
  - assert (Hstore_eq :
      verification_slice_store_sched_state_no_tcb_cur sg sched
        (glob_task_set_usedtask st tid new) =
      verification_slice_store_sched_state_no_tcb_cur sg sched st).
    { unfold verification_slice_store_sched_state_no_tcb_cur.
      rewrite
        (ready_grp_same_prio_update__blocked_tail_second_restore
          sched.(readyList) st tid old new Hlookup Hprio).
      rewrite
        (ready_tbl_same_prio_update__blocked_tail_second_restore
          sched.(readyList) st tid old new 0 Hlookup Hprio),
        (ready_tbl_same_prio_update__blocked_tail_second_restore
          sched.(readyList) st tid old new 1 Hlookup Hprio),
        (ready_tbl_same_prio_update__blocked_tail_second_restore
          sched.(readyList) st tid old new 2 Hlookup Hprio),
        (ready_tbl_same_prio_update__blocked_tail_second_restore
          sched.(readyList) st tid old new 3 Hlookup Hprio),
        (ready_tbl_same_prio_update__blocked_tail_second_restore
          sched.(readyList) st tid old new 4 Hlookup Hprio),
        (ready_tbl_same_prio_update__blocked_tail_second_restore
          sched.(readyList) st tid old new 5 Hlookup Hprio),
        (ready_tbl_same_prio_update__blocked_tail_second_restore
          sched.(readyList) st tid old new 6 Hlookup Hprio),
        (ready_tbl_same_prio_update__blocked_tail_second_restore
          sched.(readyList) st tid old new 7 Hlookup Hprio).
      reflexivity. }
    rewrite Hstore_eq. exact Hstore.
Qed.
Lemma used_complete_event_cleanup_update_eq__blocked_tail_second_restore :
  forall sg st tid old new ebase eid e,
    st.(inUsedTaskStates) tid = Some old ->
    new.(curPrio) = old.(curPrio) ->
    used_complete_event sg
      (glob_task_set_usedtask st tid new)
      ebase eid e =
    used_complete_event sg st ebase eid e.
Proof.
  intros sg st tid old new ebase eid e Hlookup Hprio.
  unfold used_complete_event.
  rewrite
    (event_grp_same_prio_update__blocked_tail_second_restore
      e.(waitList) st tid old new Hlookup Hprio).
  rewrite
    (event_tbl_same_prio_update__blocked_tail_second_restore
      e.(waitList) st tid old new 0 Hlookup Hprio),
    (event_tbl_same_prio_update__blocked_tail_second_restore
      e.(waitList) st tid old new 1 Hlookup Hprio),
    (event_tbl_same_prio_update__blocked_tail_second_restore
      e.(waitList) st tid old new 2 Hlookup Hprio),
    (event_tbl_same_prio_update__blocked_tail_second_restore
      e.(waitList) st tid old new 3 Hlookup Hprio),
    (event_tbl_same_prio_update__blocked_tail_second_restore
      e.(waitList) st tid old new 4 Hlookup Hprio),
    (event_tbl_same_prio_update__blocked_tail_second_restore
      e.(waitList) st tid old new 5 Hlookup Hprio),
    (event_tbl_same_prio_update__blocked_tail_second_restore
      e.(waitList) st tid old new 6 Hlookup Hprio),
    (event_tbl_same_prio_update__blocked_tail_second_restore
      e.(waitList) st tid old new 7 Hlookup Hprio).
  reflexivity.
Qed.
Lemma event_inv_cleanup_update__blocked_tail_second_restore :
  forall sg st ev tid old new,
    st.(inUsedTaskStates) tid = Some old ->
    new.(curPrio) = old.(curPrio) ->
    old.(eventPtr) = None ->
    new.(eventPtr) = None ->
    new.(eventMultiWaitEvents) = old.(eventMultiWaitEvents) ->
    verification_slice_event_inv sg st ev |--
    verification_slice_event_inv sg
      (glob_task_set_usedtask st tid new) ev.
Proof.
  intros sg st ev tid old new Hlookup Hprio Hold_ptr Hnew_ptr Hmulti h Hinv.
  unfold verification_slice_event_inv in *.
  destruct Hinv as [Hvalid Hspatial]. split.
  - apply verification_slice_event_in_range_cleanup_update__blocked_tail_second_restore
      with (old := old); assumption.
  - assert (Hused_eq :
      store_used_event_map sg
        (glob_task_set_usedtask st tid new)
        ev.(inUsedEventStates) =
      store_used_event_map sg st ev.(inUsedEventStates)).
    { unfold store_used_event_map.
      assert (HP :
        (fun eid e =>
           used_complete_event sg
             (glob_task_set_usedtask st tid new)
             (event_addr sg eid) eid e) =
        (fun eid e => used_complete_event sg st (event_addr sg eid) eid e)).
      { apply functional_extensionality. intro eid.
        apply functional_extensionality. intro e.
        apply
          used_complete_event_cleanup_update_eq__blocked_tail_second_restore
          with (old := old); assumption. }
      rewrite HP. reflexivity. }
    destruct Hspatial as [hu [hf [Hjoin [Hused Hfree]]]].
    exists hu, hf. split; [exact Hjoin |]. split.
    + rewrite Hused_eq. exact Hused.
    + exact Hfree.
Qed.
Lemma sem_pend_cleanup_nonintr_transport__blocked_tail_second_restore :
  forall sg s tid old new,
    s.(TskState).(inUsedTaskStates) tid = Some old ->
    new =
      {| taskID := old.(taskID);
     taskGeneration := old.(taskGeneration);
     tcbStkPtr := old.(tcbStkPtr);
     tcbExtPtr := old.(tcbExtPtr);
     tcbStkBottom := old.(tcbStkBottom);
     tcbStkSize := old.(tcbStkSize);
     tcbOpt := old.(tcbOpt);
     tcbPublicId := old.(tcbPublicId);
     tcbFlagNode := old.(tcbFlagNode);
     tcbFlagsRdy := old.(tcbFlagsRdy);
     tcbTaskName := old.(tcbTaskName);
     tcbReg0 := old.(tcbReg0);
     tcbCtxSwCtr := old.(tcbCtxSwCtr);
     tcbCyclesTot := old.(tcbCyclesTot);
     tcbCyclesStart := old.(tcbCyclesStart);
     tcbStkBase := old.(tcbStkBase);
     tcbStkUsed := old.(tcbStkUsed);
     tcbPadding42 := old.(tcbPadding42);
     tcbPadding43 := old.(tcbPadding43);
     tcbEventMultiPtr := old.(tcbEventMultiPtr);
         curPrio := old.(curPrio);
         stat := (task_status_single None ((task_is_suspended old.(stat))));
         statPend := PendOK;
         dly := old.(dly);
         eventPtr := None;
         eventMultiWaitEvents := old.(eventMultiWaitEvents);
         eventMultiRdy := old.(eventMultiRdy);
         msg := old.(msg);
         nextTCB := old.(nextTCB);
         prevTCB := old.(prevTCB);
         delReq := old.(delReq) |} ->
    old.(eventPtr) = None ->
    is_effectively_ready new.(stat) new.(dly) =
    is_effectively_ready old.(stat) old.(dly) ->
    sem_pend_cleanup_nonintr_rest sg s tid old |--
    sem_pend_cleanup_nonintr_rest sg
      (replace_TskS
        (glob_task_set_usedtask s.(TskState) tid new) s)
      tid new.
Proof.
  intros sg s tid old new Hlookup Hnew Hold_ptr Hready h Hrest.
  assert (Hprio : new.(curPrio) = old.(curPrio)).
  { rewrite Hnew. reflexivity. }
  assert (Hnew_ptr : new.(eventPtr) = None).
  { rewrite Hnew. reflexivity. }
  assert (Hmulti : new.(eventMultiWaitEvents) = old.(eventMultiWaitEvents)).
  { rewrite Hnew. reflexivity. }
  unfold sem_pend_cleanup_nonintr_rest in *.
  destruct Hrest as [Hpure Hspatial].
  split.
  - unfold replace_TskS, glob_task_set_usedtask.
    cbn. rewrite Z.eqb_refl. reflexivity.
  - destruct Hspatial as [h5 [hcross [Hj5 [H5 Hcross]]]].
    destruct H5 as [h4 [htick [Hj4 [H4 Htick]]]].
    destruct H4 as [h3 [hevent [Hj3 [H3 Hevent]]]].
    destruct H3 as [h2 [hsched [Hj2 [H2 Hsched]]]].
    destruct H2 as [hused [htask [Hj1 [Hused Htask]]]].
    exists h5, hcross. split; [exact Hj5 |]. split.
    + exists h4, htick. split; [exact Hj4 |]. split.
      * exists h3, hevent. split; [exact Hj3 |]. split.
        -- exists h2, hsched. split; [exact Hj2 |]. split.
           ++ exists hused, htask. split; [exact Hj1 |]. split.
              ** rewrite
                   (used_task_cleanup_rest_clean_eq__blocked_tail_second_restore
                     sg (verification_slice_tcb_addr sg tid) tid old new Hnew).
                 exact Hused.
              ** cbn [replace_TskS].
                 eapply
                   verification_slice_task_inv_no_tid_cleanup_update__blocked_tail_second_restore.
                 --- exact Hlookup.
                 --- exact Hprio.
                 --- exact Htask.
           ++ cbn [replace_TskS].
              eapply
                verification_slice_sched_inv_no_tcb_cur_cleanup_update__blocked_tail_second_restore.
              ** exact Hlookup.
              ** exact Hprio.
              ** exact Hready.
              ** exact Hsched.
        -- cbn [replace_TskS].
           eapply event_inv_cleanup_update__blocked_tail_second_restore.
           ++ exact Hlookup.
           ++ exact Hprio.
           ++ exact Hold_ptr.
           ++ exact Hnew_ptr.
           ++ exact Hmulti.
           ++ exact Hevent.
      * cbn [replace_TskS]. exact Htick.
    + unfold coq_prop in *.
      eapply cross_module_cleanup_update__blocked_tail_second_restore.
      * exact Hlookup.
      * exact Hprio.
      * exact Hready.
      * exact Hold_ptr.
      * exact Hnew_ptr.
      * exact Hmulti.
      * exact Hcross.
Qed.
Lemma sem_pend_tail_task_cleanup_observations__blocked_tail_second_restore :
  forall sg eid tid wait_state resume_res resume_state tail_state tail_err
         old new,
    sem_pend_resume_step
      sg eid tid wait_state resume_res resume_state ->
    sem_pend_tail_result_prop
      eid tid resume_res resume_state tail_state tail_err ->
    tail_state.(TskState).(inUsedTaskStates) tid = Some old ->
    verification_slice_sched_in_range sg tail_state.(TskState) tail_state.(SchedState) ->
    new =
      {| taskID := old.(taskID);
     taskGeneration := old.(taskGeneration);
     tcbStkPtr := old.(tcbStkPtr);
     tcbExtPtr := old.(tcbExtPtr);
     tcbStkBottom := old.(tcbStkBottom);
     tcbStkSize := old.(tcbStkSize);
     tcbOpt := old.(tcbOpt);
     tcbPublicId := old.(tcbPublicId);
     tcbFlagNode := old.(tcbFlagNode);
     tcbFlagsRdy := old.(tcbFlagsRdy);
     tcbTaskName := old.(tcbTaskName);
     tcbReg0 := old.(tcbReg0);
     tcbCtxSwCtr := old.(tcbCtxSwCtr);
     tcbCyclesTot := old.(tcbCyclesTot);
     tcbCyclesStart := old.(tcbCyclesStart);
     tcbStkBase := old.(tcbStkBase);
     tcbStkUsed := old.(tcbStkUsed);
     tcbPadding42 := old.(tcbPadding42);
     tcbPadding43 := old.(tcbPadding43);
     tcbEventMultiPtr := old.(tcbEventMultiPtr);
         curPrio := old.(curPrio);
         stat := (task_status_single None ((task_is_suspended old.(stat))));
         statPend := PendOK;
         dly := old.(dly);
         eventPtr := None;
         eventMultiWaitEvents := old.(eventMultiWaitEvents);
         eventMultiRdy := old.(eventMultiRdy);
         msg := old.(msg);
         nextTCB := old.(nextTCB);
         prevTCB := old.(prevTCB);
         delReq := old.(delReq) |} ->
    old.(eventPtr) = None /\
    is_effectively_ready new.(stat) new.(dly) =
    is_effectively_ready old.(stat) old.(dly).
Proof.
  intros sg eid tid wait_state resume_res resume_state tail_state tail_err
    old new Hresume Htail Hlookup Hsched Hnew.
  subst new.
  (* Wake clears only the Sem bit.  Any other non-suspension bits are
     excluded here by the existing scheduler validity, not by the write. *)
  assert (Hreset_ready : forall status delay,
    (task_is_suspended status = false ->
       is_effectively_ready status delay = true) ->
    is_effectively_ready
      (task_status_single None (task_is_suspended status)) delay =
    is_effectively_ready status delay).
  { intros status delay Hready.
    unfold is_effectively_ready.
    rewrite (proj1 (task_status_single_observations None
      (task_is_suspended status))),
      (proj2 (task_status_single_observations None
      (task_is_suspended status))).
    cbn [encode_pend_type].
    destruct (task_is_suspended status) eqn:Hsuspended.
    - destruct (Z.eqb (task_non_suspension_bits status) 0); reflexivity.
    - destruct (Z.eqb (task_non_suspension_bits status) 0) eqn:Hpending;
        [reflexivity|].
      exfalso.
      assert (Heffective : is_effectively_ready status delay = true).
      { apply Hready; assumption || reflexivity. }
      unfold is_effectively_ready in Heffective.
      rewrite Hpending in Heffective; discriminate. }
  destruct resume_res.
  - unfold sem_pend_resume_step in Hresume.
    destruct Hresume as [returned_prio Hready_step].
    unfold atomic_event_task_rdy_one in Hready_step.
    destruct Hready_step as
      (e1 & e2 & waiter & owner & owner' & Hevent & Htype & Hnonempty &
       Hhead & Hwaiter & Hreturned & Hslot & Howner & Howner_prio &
       Howner' & He2 & Hresume_state).
    unfold sem_pend_tail_result_prop in Htail.
    destruct Htail as [Htail_state Herr].
    subst tail_state.
    cbv zeta in Hresume_state.
    assert (Hresume_lookup :
      resume_state.(TskState).(inUsedTaskStates) tid = Some owner').
    { rewrite Hresume_state. cbn. rewrite Z.eqb_refl. reflexivity. }
    rewrite Hresume_lookup in Hlookup.
    injection Hlookup as Hold; subst old.
    split; [rewrite Howner'; reflexivity|].
    apply Hreset_ready; intro Hsuspended.
    assert (Hin_ready : In tid resume_state.(SchedState).(readyList)).
    { rewrite Hresume_state. cbn. rewrite Hsuspended.
      apply insert_sorted_by_in. simpl; left; reflexivity. }
    destruct ((proj1 Hsched) tid Hin_ready)
      as [ready_t [Hready_lookup Heffective]].
    rewrite Hresume_lookup in Hready_lookup.
    injection Hready_lookup as Hready_eq; subst ready_t.
    exact Heffective.
  - unfold sem_pend_resume_step in Hresume.
    destruct Hresume as [returned_prio Hready_step].
    unfold atomic_event_task_rdy_one in Hready_step.
    destruct Hready_step as
      (e1 & e2 & waiter & owner & owner' & Hevent & Htype & Hnonempty &
       Hhead & Hwaiter & Hreturned & Hslot & Howner & Howner_prio &
       Howner' & He2 & Hresume_state).
    unfold sem_pend_tail_result_prop in Htail.
    destruct Htail as [Htail_state Herr].
    subst tail_state.
    cbv zeta in Hresume_state.
    assert (Hresume_lookup :
      resume_state.(TskState).(inUsedTaskStates) tid = Some owner').
    { rewrite Hresume_state. cbn. rewrite Z.eqb_refl. reflexivity. }
    rewrite Hresume_lookup in Hlookup.
    injection Hlookup as Hold; subst old.
    split; [rewrite Howner'; reflexivity|].
    apply Hreset_ready; intro Hsuspended.
    assert (Hin_ready : In tid resume_state.(SchedState).(readyList)).
    { rewrite Hresume_state. cbn. rewrite Hsuspended.
      apply insert_sorted_by_in. simpl; left; reflexivity. }
    destruct ((proj1 Hsched) tid Hin_ready)
      as [ready_t [Hready_lookup Heffective]].
    rewrite Hresume_lookup in Hready_lookup.
    injection Hready_lookup as Hready_eq; subst ready_t.
    exact Heffective.
  - unfold sem_pend_resume_step, sem_pend_timeout_resume in Hresume.
    destruct Hresume as [t [t' [Hwait_lookup [Ht' Hresume_state]]]].
    cbv zeta in Hresume_state.
    unfold sem_pend_tail_result_prop in Htail.
    destruct Htail as [Hremove Herr].
    unfold atomic_event_task_remove in Hremove.
    destruct Hremove as
      (e1 & e2 & removed & removed' & Hevent & Hin_wait & Hremoved &
       He2 & Hremoved' & Htail_state).
    pose proof Hlookup as Htail_lookup.
    rewrite Htail_state in Hlookup.
    cbn in Hlookup.
    rewrite Z.eqb_refl in Hlookup.
    injection Hlookup as Hold_eq.
    rewrite Hresume_state in Hremoved.
    cbn in Hremoved.
    rewrite Z.eqb_refl in Hremoved.
    injection Hremoved as Hremoved_eq.
    assert (Hold_stat : old.(stat) = t.(stat)).
    { rewrite <- Hold_eq. rewrite Hremoved'. cbn.
      rewrite <- Hremoved_eq. rewrite Ht'. reflexivity. }
    split.
    + rewrite <- Hold_eq. rewrite Hremoved'. reflexivity.
    + apply Hreset_ready; intro Hsuspended.
      assert (Ht_suspended : task_is_suspended t.(stat) = false).
      { rewrite <- Hold_stat; exact Hsuspended. }
      assert (Hin_ready : In tid tail_state.(SchedState).(readyList)).
      { rewrite Htail_state. cbn. rewrite Hresume_state. cbn.
        rewrite Ht'. cbn. rewrite Ht_suspended.
        apply insert_sorted_by_in. simpl; left; reflexivity. }
      destruct ((proj1 Hsched) tid Hin_ready)
        as [ready_t [Hready_lookup Heffective]].
      rewrite Htail_lookup in Hready_lookup.
      injection Hready_lookup as Hready_eq; subst ready_t.
      exact Heffective.
Qed.
Lemma sem_pend_final_cleanup_nonintr_transport__blocked_tail_second_restore :
  forall sg eid tid wait_state resume_res resume_state tail_state tail_err
         final_state cur_t,
    sem_pend_resume_step
      sg eid tid wait_state resume_res resume_state ->
    sem_pend_tail_result_prop
      eid tid resume_res resume_state tail_state tail_err ->
    sem_pend_cleanup_step tid tail_state final_state ->
    sem_pend_cleanup_nonintr_rest sg tail_state tid cur_t |--
    EX final_t : TaskAbstractState,
      sem_pend_cleanup_nonintr_rest sg final_state tid final_t.
Proof.
  intros sg eid tid wait_state resume_res resume_state tail_state tail_err
    final_state cur_t Hresume Htail Hcleanup h Hrest.
  pose proof Hrest as Hparts.
  unfold sem_pend_cleanup_nonintr_rest in Hparts.
  destruct Hparts as [Hlookup Hspatial].
  unfold coq_prop in Hlookup.
  destruct Hspatial as [h5 [hcross [Hj5 [H5 Hcross]]]].
  destruct H5 as [h4 [htick [Hj4 [H4 Htick]]]].
  destruct H4 as [h3 [hevent [Hj3 [H3 Hevent]]]].
  destruct H3 as [h2 [hsched [Hj2 [H2 Hsched]]]].
  unfold verification_slice_sched_inv_no_tcb_cur in Hsched.
  destruct Hsched as [Hsched_range Hsched_store].
  destruct Hcleanup as [old [final_t [Hcleanup_lookup
    [Hfinal_t Hfinal_state]]]].
  rewrite Hlookup in Hcleanup_lookup.
  inversion Hcleanup_lookup; subst old.
  destruct
    (sem_pend_tail_task_cleanup_observations__blocked_tail_second_restore
      sg eid tid wait_state resume_res resume_state tail_state tail_err
      cur_t final_t Hresume Htail Hlookup Hsched_range Hfinal_t)
    as [Hevent_ptr Hready].
  subst final_state.
  exists final_t.
  eapply
    sem_pend_cleanup_nonintr_transport__blocked_tail_second_restore;
    eassumption.
Qed.
Lemma sem_pend_cleanup_step_preserves_intr__blocked_tail_second_restore :
  forall tid entry post,
    sem_pend_cleanup_step tid entry post ->
    post.(IntrState) = entry.(IntrState).
Proof.
  intros tid entry post Hstep.
  destruct Hstep as [t [t' [Hlookup [Ht' Hpost]]]].
  subst post. reflexivity.
Qed.
Lemma atomic_event_task_remove_deterministic__blocked_tail_second_restore :
  forall tid eid entry post1 post2,
    atomic_event_task_remove tid eid entry tt post1 ->
    atomic_event_task_remove tid eid entry tt post2 ->
    post1 = post2.
Proof.
  intros tid eid entry post1 post2 Hremove1 Hremove2.
  unfold atomic_event_task_remove in Hremove1, Hremove2.
  destruct Hremove1 as
    [e1 [e2 [t [t' [He1 [_ [Ht [He2 [Ht' Hpost1]]]]]]]]].
  destruct Hremove2 as
    [e1' [e2' [t0 [t0' [He1' [_ [Ht0 [He2' [Ht0' Hpost2]]]]]]]]].
  rewrite He1 in He1'.
  inversion He1'; subst e1'.
  rewrite Ht in Ht0.
  inversion Ht0; subst t0.
  subst e2 e2' t' t0' post1 post2.
  reflexivity.
Qed.
Lemma sem_pend_tail_finalize_facts__blocked_tail_second_restore :
  forall sg eid cur_tid timeout entry critical final tail res err e saved,
    sem_pend_final_step eid cur_tid res entry final ->
    sem_pend_tail_result_prop eid cur_tid res entry tail err ->
    interrupt_saved_cpu_sr entry critical saved ->
    sem_pend_cleanup_step cur_tid tail final /\
    err = encode_sem_pend_result (sem_pend_blocked_result res) /\
    sem_pend_restore_transition_prop
      sg entry critical final eid cur_tid timeout 2 e res /\
    interrupt_restore_consumes_saved_cpu_sr
      entry critical saved saved.
Proof.
  intros sg eid cur_tid timeout entry critical final tail res err e saved
    Hfinal Htail Hsaved.
  assert (Hconsume : interrupt_restore_consumes_saved_cpu_sr
      entry critical saved saved).
  { apply interrupt_restore_consumes_saved_cpu_sr_self. exact Hsaved. }
  destruct Hsaved as [Hcrit Hsaved_range].
  destruct res.
  - unfold sem_pend_final_step in Hfinal.
    unfold sem_pend_tail_result_prop in Htail.
    destruct Htail as [Htail Herr].
    subst tail err.
    split; [exact Hfinal |].
    split; [reflexivity |].
    split.
    + unfold sem_pend_restore_transition_prop.
      split; [exact Hcrit |].
      right; right; split; [reflexivity | exact Hfinal].
    + exact Hconsume.
  - unfold sem_pend_final_step in Hfinal.
    unfold sem_pend_tail_result_prop in Htail.
    destruct Htail as [Htail Herr].
    subst tail err.
    split; [exact Hfinal |].
    split; [reflexivity |].
    split.
    + unfold sem_pend_restore_transition_prop.
      split; [exact Hcrit |].
      right; right; split; [reflexivity | exact Hfinal].
    + exact Hconsume.
  - unfold sem_pend_final_step in Hfinal.
    unfold sem_pend_tail_result_prop in Htail.
    destruct Hfinal as [removed [Hremove Hcleanup]].
    destruct Htail as [Hremove_tail Herr].
    assert (Heq : removed = tail).
    { eapply atomic_event_task_remove_deterministic__blocked_tail_second_restore;
        eassumption. }
    subst removed err.
    split; [exact Hcleanup |].
    split; [reflexivity |].
    split.
    + unfold sem_pend_restore_transition_prop.
      split; [exact Hcrit |].
      right; right; split; [reflexivity |].
      unfold sem_pend_final_step.
      exists tail. split; assumption.
    + exact Hconsume.
Qed.
Lemma sem_pend_guard_select_entry__blocked_tail_second_restore :
  forall sg entry pevent etype isr lock cur_tid cur_t
         tcbcur prio stat statpend dly eventptr eventmultiptr
         eventmultirdy rdygrp priocur rdytbl,
    pevent <> 0 ->
    etype = 3 ->
    isr <= 0 ->
    lock <= 0 ->
    sem_pend_task_sched_guard_prop sg entry pevent etype isr lock
      cur_tid cur_t tcbcur prio stat statpend dly eventptr
      eventmultiptr eventmultirdy rdygrp priocur rdytbl ->
    sem_pend_select_current entry cur_tid /\
    entry.(TskState).(inUsedTaskStates) cur_tid = Some cur_t /\
    task_mutex_pend_entry_prop cur_t /\
    tcbcur = verification_slice_tcb_addr sg cur_tid.
Proof.
  intros sg entry pevent etype isr lock cur_tid cur_t
    tcbcur prio stat statpend dly eventptr eventmultiptr
    eventmultirdy rdygrp priocur rdytbl
    Hnonnull Hetype Hisr Hlock Hguard.
  unfold sem_pend_task_sched_guard_prop in Hguard.
  destruct Hguard as
    [Hzero | [Hwrong | [Hisr_case | [Hlock_case | Htask]]]].
  - contradiction.
  - destruct Hwrong as [_ Hwrong]. cbn in Hwrong. lia.
  - destruct Hisr_case as [_ [_ Hpositive]]. lia.
  - destruct Hlock_case as [_ [_ [_ Hpositive]]]. lia.
  - destruct Htask as
      [_ [_ [_ [_ [Htcb_nonzero [Hsched [Hsnapshot [Hentry_prop Hready]]]]]]]].
    unfold sem_pend_task_snapshot_prop,
      task_mutex_full_snapshot_of_prop in Hsnapshot.
    destruct Hsnapshot as
      [Hlookup [Htcb [Hprio [Hstat [Hstatpend [Hdly
       [Heventptr [Heventmultiptr Heventmultirdy]]]]]]]].
    assert (Hselect : sem_pend_select_current entry cur_tid).
    { unfold sem_pend_select_current.
      unfold verification_slice_sched_tcb_cur_snapshot_prop in Hsched.
      destruct entry.(SchedState).(curTaskID) as [current|] eqn:Hcurrent.
      - cbn in Hsched.
        assert (current = cur_tid).
        { unfold verification_slice_tcb_addr, verification_slice_tcb_size in Hsched, Htcb. lia. }
        subst current. reflexivity.
      - cbn in Hsched. subst tcbcur. contradiction. }
    split; [exact Hselect |].
    split; [exact Hlookup |].
    split; [exact Hentry_prop | exact Htcb].
Qed.
Lemma sem_pend_blocked_exact_result__blocked_tail_second_restore :
  forall sg entry pevent timeout eid e etype ecnt eptr egrp etbl
         cur_tid cur_t tcbcur prio stat statpend dly eventptr
         eventmultiptr eventmultirdy rdygrp priocur rdytbl
         wait_state resume_res resume_state final_state,
    pevent <> 0 ->
    pevent = event_addr sg eid ->
    etype = 3 ->
    ecnt = 0 ->
    entry.(IntrState).(intNesting) <= 0 ->
    entry.(IntrState).(lockNesting) <= 0 ->
    sem_pend_selected_event_prop sg entry eid e etype ecnt eptr egrp etbl ->
    UCOS2_verification_slice_state_inv sg entry ->
    sem_pend_task_sched_guard_prop sg entry pevent etype
      entry.(IntrState).(intNesting) entry.(IntrState).(lockNesting)
      cur_tid cur_t tcbcur prio stat statpend dly eventptr
      eventmultiptr eventmultirdy rdygrp priocur rdytbl ->
    sem_pend_wait_step sg eid timeout entry wait_state ->
    sem_pend_resume_step sg eid cur_tid wait_state resume_res resume_state ->
    sem_pend_final_step eid cur_tid resume_res resume_state final_state ->
    sem_pend_exact_result_prop sg pevent timeout entry final_state
      (sem_pend_blocked_result resume_res).
Proof.
  intros sg entry pevent timeout eid e etype ecnt eptr egrp etbl
    cur_tid cur_t tcbcur prio stat statpend dly eventptr
    eventmultiptr eventmultirdy rdygrp priocur rdytbl
    wait_state resume_res resume_state final_state
    Hnonnull Hptr Hetype Hcnt Hisr Hlock Hselected Hvalid Hguard
    Hwait Hresume Hfinal.
  destruct Hselected as
    [Heid [Hevent [Hsnapshot [Htype_enc [Hcnt_enc Hgrp]]]]].
  assert (Hevent_type : e.(eventType) = OS_EVENT_TYPE_SEM).
  { destruct e.(eventType); cbn in Htype_enc; lia || reflexivity. }
  destruct Hvalid as [Htask_valid [Hsched_valid [Hevent_valid Hcross]]].
  unfold verification_slice_event_in_range, verification_slice_event_in_range,
    verification_slice_event_in_range in Hevent_valid.
  destruct Hevent_valid as
    [Hused_range [Hfree_nodup [Hfree_range [Hpartition
     [Hfields [Hpayload [Hqueue Hwait_entries]]]]]]].
  pose proof (Hfields eid e Hevent) as Hfield_shape.
  unfold event_fields_consistency in Hfield_shape.
  rewrite Hevent_type in Hfield_shape.
  destruct Hfield_shape as
    [Hmutex_none [Hsem_some [Hmbox_none Hqueue_none]]].
  destruct e.(semFields) as [sf|] eqn:Hsf.
  2: { exfalso. apply Hsem_some. reflexivity. }
  assert (Hsf_zero : sf.(semCount) = 0).
  { unfold encode_event_cnt_value in Hcnt_enc.
    rewrite Hevent_type, Hsf in Hcnt_enc. cbn in Hcnt_enc. lia. }
  pose proof
    (sem_pend_guard_select_entry__blocked_tail_second_restore
      sg entry pevent etype entry.(IntrState).(intNesting)
      entry.(IntrState).(lockNesting) cur_tid cur_t tcbcur prio stat
      statpend dly eventptr eventmultiptr eventmultirdy rdygrp priocur
      rdytbl Hnonnull Hetype Hisr Hlock Hguard) as Hentry.
  destruct Hentry as [Hselect [Hentry_lookup [Hentry_clean Htcb]]].
  unfold sem_pend_exact_result_prop, OSSemPend_sem.
  right. right. right. right. right.
  split; [exact Hnonnull |].
  exists eid, e, sf, cur_tid, wait_state, resume_state, resume_res.
  split; [exact Heid |].
  split; [exact Hptr |].
  split; [exact Hevent |].
  split; [exact Hevent_type |].
  split; [exact Hsf |].
  split; [exact Hisr |].
  split; [exact Hlock |].
  split; [exact Hsf_zero |].
  split; [exact Hselect |].
  split; [exact Hwait |].
  split; [exact Hresume |].
  split; [exact Hfinal | reflexivity].
Qed.
Lemma sem_pend_wait_task_observations__blocked_tail_second_restore :
  forall sg eid timeout entry wait_state tid entry_t,
    sem_pend_select_current entry tid ->
    entry.(TskState).(inUsedTaskStates) tid = Some entry_t ->
    task_mutex_pend_entry_prop entry_t ->
    sem_pend_wait_step sg eid timeout entry wait_state ->
    exists wait_t,
      wait_state.(TskState).(inUsedTaskStates) tid = Some wait_t /\
      (task_is_suspended wait_t.(stat)) = false /\
      wait_t.(eventMultiWaitEvents) = [] /\
      wait_t.(eventMultiRdy) = None.
Proof.
  intros sg eid timeout entry wait_state tid entry_t
    Hselect Hentry_lookup Hentry_clean Hwait.
  unfold sem_pend_wait_step, atomic_event_task_wait_kind in Hwait.
  destruct Hwait as
    (wait_tid & wait_t & e & Hwait_tid & Hwait_lookup & Hevent & Hwait_state).
  unfold sem_pend_select_current in Hselect.
  rewrite Hselect in Hwait_tid. injection Hwait_tid as Htid; subst wait_tid.
  rewrite Hentry_lookup in Hwait_lookup.
  inversion Hwait_lookup; subst wait_t.
  destruct Hentry_clean as
    [Hpend [Hsuspended [Hpendstat [Hdly [Heventptr
     [Heventmulti Heventmultirdy]]]]]].
  subst wait_state.
  exists (task_set_event_ptr
    (task_prepare_event_wait entry_t PendSem timeout) (Some eid)).
  split.
  - unfold event_pend_state, event_wait_state.
    cbn. rewrite Z.eqb_refl; reflexivity.
  - split.
    + change (task_is_suspended
        (task_prepare_event_wait entry_t PendSem timeout).(stat) = false).
      unfold task_is_suspended.
      rewrite task_prepare_event_wait_status_encoding.
      rewrite (task_status_single_of_mask entry_t.(stat) None Hpend).
      rewrite Hsuspended; reflexivity.
    + cbn [task_set_event_ptr task_prepare_event_wait].
      split; assumption.
Qed.
Lemma sem_pend_resume_task_observations__blocked_tail_second_restore :
  forall sg eid tid wait_state res resume_state wait_t,
    wait_state.(TskState).(inUsedTaskStates) tid = Some wait_t ->
    (task_is_suspended wait_t.(stat)) = false ->
    wait_t.(eventMultiWaitEvents) = [] ->
    wait_t.(eventMultiRdy) = None ->
    sem_pend_resume_step sg eid tid wait_state res resume_state ->
    exists resume_t,
      resume_state.(TskState).(inUsedTaskStates) tid = Some resume_t /\
      (task_is_suspended resume_t.(stat)) = false /\
      resume_t.(dly) = 0 /\
      resume_t.(eventMultiWaitEvents) = [] /\
      resume_t.(eventMultiRdy) = None.
Proof.
  intros sg eid tid wait_state res resume_state wait_t
    Hwait_lookup Hsuspended Heventmulti Heventmultirdy Hresume.
  destruct res.
  - unfold sem_pend_resume_step in Hresume.
    destruct Hresume as [returned_prio Hready].
    unfold atomic_event_task_rdy_one in Hready.
    destruct Hready as
      (e1 & e2 & waiter_t & owner_t & owner_t' & Hevent & Htype &
       Hnonempty & Hhead & Hwaiter & Hreturned & Hslot & Howner &
       Howner_prio & Howner_t' & He2 & Hresume_state).
    rewrite Hwait_lookup in Howner. inversion Howner; subst owner_t.
    subst owner_t'. cbv zeta in Hresume_state. subst resume_state.
    cbn. rewrite Z.eqb_refl.
    eexists. split; [reflexivity |].
    split.
    + change (task_is_suspended
        (task_clear_pending_status wait_t.(stat) PendSem) = false).
      rewrite task_clear_pending_status_preserves_suspension.
      exact Hsuspended.
    + cbn. repeat split; assumption || reflexivity.
  - unfold sem_pend_resume_step in Hresume.
    destruct Hresume as [returned_prio Hready].
    unfold atomic_event_task_rdy_one in Hready.
    destruct Hready as
      (e1 & e2 & waiter_t & owner_t & owner_t' & Hevent & Htype &
       Hnonempty & Hhead & Hwaiter & Hreturned & Hslot & Howner &
       Howner_prio & Howner_t' & He2 & Hresume_state).
    rewrite Hwait_lookup in Howner. inversion Howner; subst owner_t.
    subst owner_t'. cbv zeta in Hresume_state. subst resume_state.
    cbn. rewrite Z.eqb_refl.
    eexists. split; [reflexivity |].
    split.
    + change (task_is_suspended
        (task_clear_pending_status wait_t.(stat) PendSem) = false).
      rewrite task_clear_pending_status_preserves_suspension.
      exact Hsuspended.
    + cbn. repeat split; assumption || reflexivity.
  - unfold sem_pend_resume_step, sem_pend_timeout_resume in Hresume.
    destruct Hresume as [old [new [Hold [Hnew Hresume_state]]]].
    rewrite Hwait_lookup in Hold. inversion Hold; subst old.
    subst new. cbv zeta in Hresume_state. subst resume_state.
    cbn. rewrite Z.eqb_refl.
    eexists. split; [reflexivity |].
    cbn. repeat split; assumption || reflexivity.
Qed.
Lemma sem_pend_remove_task_observations__blocked_tail_second_restore :
  forall eid tid entry post entry_t,
    entry.(TskState).(inUsedTaskStates) tid = Some entry_t ->
    (task_is_suspended entry_t.(stat)) = false ->
    entry_t.(dly) = 0 ->
    entry_t.(eventMultiWaitEvents) = [] ->
    entry_t.(eventMultiRdy) = None ->
    atomic_event_task_remove tid eid entry tt post ->
    exists post_t,
      post.(TskState).(inUsedTaskStates) tid = Some post_t /\
      (task_is_suspended post_t.(stat)) = false /\
      post_t.(dly) = 0 /\
      post_t.(eventMultiWaitEvents) = [] /\
      post_t.(eventMultiRdy) = None.
Proof.
  intros eid tid entry post entry_t Hentry_lookup Hsuspended Hdly
    Heventmulti Heventmultirdy Hremove.
  unfold atomic_event_task_remove in Hremove.
  destruct Hremove as
    (e1 & e2 & old & new & Hevent & Hin & Hold & He2 & Hnew & Hpost).
  rewrite Hentry_lookup in Hold. inversion Hold; subst old.
  subst new post. cbn. rewrite Z.eqb_refl.
  eexists. split; [reflexivity |].
  cbn. repeat split; assumption || reflexivity.
Qed.
Lemma sem_pend_cleanup_task_clean__blocked_tail_second_restore :
  forall tid entry post entry_t post_t,
    entry.(TskState).(inUsedTaskStates) tid = Some entry_t ->
    (task_is_suspended entry_t.(stat)) = false ->
    entry_t.(dly) = 0 ->
    entry_t.(eventMultiWaitEvents) = [] ->
    entry_t.(eventMultiRdy) = None ->
    sem_pend_cleanup_step tid entry post ->
    post.(TskState).(inUsedTaskStates) tid = Some post_t ->
    task_mutex_pend_clean_prop post_t.
Proof.
  intros tid entry post entry_t post_t Hentry_lookup Hsuspended Hdly
    Heventmulti Heventmultirdy Hcleanup Hpost_lookup.
  destruct Hcleanup as [old [new [Hold [Hnew Hpost]]]].
  rewrite Hentry_lookup in Hold. inversion Hold; subst old.
  subst new post. cbn in Hpost_lookup. rewrite Z.eqb_refl in Hpost_lookup.
  inversion Hpost_lookup; subst post_t.
  unfold task_mutex_pend_clean_prop. cbn.
  rewrite Hsuspended.
  repeat split; assumption || reflexivity.
Qed.
Lemma sem_pend_final_task_clean__blocked_tail_second_restore :
  forall eid tid res resume_state final_state resume_t final_t,
    resume_state.(TskState).(inUsedTaskStates) tid = Some resume_t ->
    (task_is_suspended resume_t.(stat)) = false ->
    resume_t.(dly) = 0 ->
    resume_t.(eventMultiWaitEvents) = [] ->
    resume_t.(eventMultiRdy) = None ->
    sem_pend_final_step eid tid res resume_state final_state ->
    final_state.(TskState).(inUsedTaskStates) tid = Some final_t ->
    task_mutex_pend_clean_prop final_t.
Proof.
  intros eid tid res resume_state final_state resume_t final_t
    Hresume_lookup Hsuspended Hdly Heventmulti Heventmultirdy
    Hfinal Hfinal_lookup.
  destruct res.
  - unfold sem_pend_final_step in Hfinal.
    exact
      (sem_pend_cleanup_task_clean__blocked_tail_second_restore
        tid resume_state final_state resume_t final_t Hresume_lookup
        Hsuspended Hdly Heventmulti Heventmultirdy Hfinal Hfinal_lookup).
  - unfold sem_pend_final_step in Hfinal.
    exact
      (sem_pend_cleanup_task_clean__blocked_tail_second_restore
        tid resume_state final_state resume_t final_t Hresume_lookup
        Hsuspended Hdly Heventmulti Heventmultirdy Hfinal Hfinal_lookup).
  - unfold sem_pend_final_step in Hfinal.
    destruct Hfinal as [removed [Hremove Hcleanup]].
    destruct
      (sem_pend_remove_task_observations__blocked_tail_second_restore
        eid tid resume_state removed resume_t Hresume_lookup Hsuspended
        Hdly Heventmulti Heventmultirdy Hremove)
      as [removed_t [Hremoved_lookup [Hremoved_suspended [Hremoved_dly
          [Hremoved_multi Hremoved_multirdy]]]]].
    exact
      (sem_pend_cleanup_task_clean__blocked_tail_second_restore
        tid removed final_state removed_t final_t Hremoved_lookup
        Hremoved_suspended Hremoved_dly Hremoved_multi Hremoved_multirdy
        Hcleanup Hfinal_lookup).
Qed.
Lemma sem_pend_execution_final_task_clean__blocked_tail_second_restore :
  forall sg eid timeout entry wait_state res resume_state final_state
         tid entry_t final_t,
    sem_pend_select_current entry tid ->
    entry.(TskState).(inUsedTaskStates) tid = Some entry_t ->
    task_mutex_pend_entry_prop entry_t ->
    sem_pend_wait_step sg eid timeout entry wait_state ->
    sem_pend_resume_step sg eid tid wait_state res resume_state ->
    sem_pend_final_step eid tid res resume_state final_state ->
    final_state.(TskState).(inUsedTaskStates) tid = Some final_t ->
    task_mutex_pend_clean_prop final_t.
Proof.
  intros sg eid timeout entry wait_state res resume_state final_state
    tid entry_t final_t Hselect Hentry_lookup Hentry_clean Hwait
    Hresume Hfinal Hfinal_lookup.
  destruct
    (sem_pend_wait_task_observations__blocked_tail_second_restore
      sg eid timeout entry wait_state tid entry_t Hselect Hentry_lookup
      Hentry_clean Hwait)
    as [wait_t [Hwait_lookup [Hwait_suspended
        [Hwait_multi Hwait_multirdy]]]].
  destruct
    (sem_pend_resume_task_observations__blocked_tail_second_restore
      sg eid tid wait_state res resume_state wait_t Hwait_lookup
      Hwait_suspended Hwait_multi Hwait_multirdy Hresume)
    as [resume_t [Hresume_lookup [Hresume_suspended [Hresume_dly
        [Hresume_multi Hresume_multirdy]]]]].
  eapply sem_pend_final_task_clean__blocked_tail_second_restore;
    eassumption.
Qed.
Lemma sem_pend_cleanup_fields_to_no_prio__blocked_tail_second_restore :
  forall sg base tid t,
    task_mutex_pend_clean_prop t ->
    (base + verification_slice_OSTCBStat_off) # UChar |-> 0 **
    (base + verification_slice_OSTCBStatPend_off) # UChar |-> 0 **
    (base + verification_slice_OSTCBDly_off) # UInt |-> 0 **
    (base + verification_slice_OSTCBEventPtr_off) # Ptr |-> 0 **
    used_task_cleanup_rest sg base tid t |--
    (base + verification_slice_OSTCBPrio_off) # UChar |-> t.(curPrio) **
    used_task_no_prio sg base tid t.
Proof.
  intros sg base tid t Hclean.
  unfold task_mutex_pend_clean_prop in Hclean.
  destruct Hclean as
    [Hpend [Hsuspended [Hpendstat [Hdly [Heventptr
     [Heventmulti Heventmultirdy]]]]]].
  assert (Hstat : encode_task_status t.(stat) = 0).
  { change (task_status.encode_task_status t.(stat) = 0).
    rewrite task_status_value_decomposition, Hpend, Hsuspended.
    reflexivity. }
  unfold used_task_cleanup_rest, used_task_no_prio.
  rewrite Hstat, Hpendstat, Hdly, Heventptr,
    Heventmulti, Heventmultirdy.
  cbn [encode_pend_status encode_event_ptr encode_event_multi_ptr].
  cancel ((base + verification_slice_OSTCBPrio_off) # UChar |-> t.(curPrio)).
  cancel ((base + verification_slice_OSTCBStat_off) # UChar |-> 0).
  cancel ((base + verification_slice_OSTCBStatPend_off) # UChar |-> 0).
  cancel ((base + verification_slice_OSTCBDly_off) # UInt |-> 0).
  cancel ((base + verification_slice_OSTCBX_off) # UChar |-> tcb_x_of_prio t.(curPrio)).
  cancel ((base + verification_slice_OSTCBY_off) # UChar |-> tcb_y_of_prio t.(curPrio)).
  cancel ((base + verification_slice_OSTCBBitX_off) # UChar |-> tcb_bit_x_of_prio t.(curPrio)).
  cancel ((base + verification_slice_OSTCBBitY_off) # UChar |-> tcb_bit_y_of_prio t.(curPrio)).
  cancel ((base + verification_slice_OSTCBEventPtr_off) # Ptr |-> 0).
  cancel ((base + verification_slice_OSTCBEventMultiPtr_off) # Ptr |-> 0).
  cancel ((base + verification_slice_OSTCBEventMultiRdy_off) # Ptr |-> 0).
  cancel ((base + verification_slice_OSTCBMsg_off) # Ptr |-> encode_msg t.(msg)).
  cancel ((base + verification_slice_OSTCBNext_off) # Ptr |->
    (match t.(nextTCB) with None => 0 | Some tid' => verification_slice_tcb_addr sg tid' end)).
  cancel ((base + verification_slice_OSTCBPrev_off) # Ptr |->
    (match t.(prevTCB) with None => 0 | Some tid' => verification_slice_tcb_addr sg tid' end)).
  cancel ((base + verification_slice_OSTCBDelReq_off) # UChar |-> encode_bool t.(delReq)).
Qed.
Lemma sem_pend_cleanup_task_inv_rebuild__blocked_tail_second_restore :
  forall sg st tid t,
    st.(inUsedTaskStates) tid = Some t ->
    task_mutex_pend_clean_prop t ->
    (verification_slice_tcb_addr sg tid + verification_slice_OSTCBStat_off) # UChar |-> 0 **
    (verification_slice_tcb_addr sg tid + verification_slice_OSTCBStatPend_off) # UChar |-> 0 **
    (verification_slice_tcb_addr sg tid + verification_slice_OSTCBDly_off) # UInt |-> 0 **
    (verification_slice_tcb_addr sg tid + verification_slice_OSTCBEventPtr_off) # Ptr |-> 0 **
    used_task_cleanup_rest sg (verification_slice_tcb_addr sg tid) tid t **
    verification_slice_task_inv_no_tid sg st tid |--
    verification_slice_task_inv sg st.
Proof.
  intros sg st tid t Hlookup Hclean.
  sep_apply_l_atomic
    (sem_pend_cleanup_fields_to_no_prio__blocked_tail_second_restore
      sg (verification_slice_tcb_addr sg tid) tid t Hclean).
  assert (Hcomplete :
    (verification_slice_tcb_addr sg tid + verification_slice_OSTCBPrio_off)
      # UChar |-> t.(curPrio) **
    used_task_no_prio sg (verification_slice_tcb_addr sg tid) tid t |--
    verification_slice_used_complete_task sg (verification_slice_tcb_addr sg tid) tid t).
  { unfold verification_slice_used_complete_task, used_task_no_prio.
    entailer!. }
  sep_apply_l_atomic Hcomplete.
  unfold verification_slice_task_inv, verification_slice_task_inv_no_tid,
    verification_slice_store_used_task_map, verification_slice_store_used_task_map_missing_i.
  entailer!.
  sep_apply_l_atomic (store_map_merge
    (fun tid0 t0 => verification_slice_used_complete_task
      sg (verification_slice_tcb_addr sg tid0) tid0 t0)
    tid t (inUsedTaskStates st) Hlookup).
  entailer!.
Qed.
Lemma sem_pend_wait_cur_task_preserved__blocked_tail_second_restore :
  forall sg eid timeout entry post,
    sem_pend_wait_step sg eid timeout entry post ->
    post.(SchedState).(curTaskID) = entry.(SchedState).(curTaskID).
Proof.
  intros sg eid timeout entry post Hwait.
  unfold sem_pend_wait_step, atomic_event_task_wait_kind in Hwait.
  destruct Hwait as (tid & old & e & Htid & Hold & Hevent & Hpost).
  subst post; reflexivity.
Qed.
Lemma sem_pend_resume_cur_task_preserved__blocked_tail_second_restore :
  forall sg eid tid entry res post,
    sem_pend_resume_step sg eid tid entry res post ->
    post.(SchedState).(curTaskID) = entry.(SchedState).(curTaskID).
Proof.
  intros sg eid tid entry res post Hresume.
  destruct res.
  - unfold sem_pend_resume_step in Hresume.
    destruct Hresume as [returned_prio Hready].
    unfold atomic_event_task_rdy_one in Hready.
    destruct Hready as
      (e1 & e2 & waiter & owner & owner' & Hevent & Htype & Hnonempty &
       Hhead & Hwaiter & Hreturned & Hslot & Howner & Howner_prio &
       Howner' & He2 & Hpost).
    cbv zeta in Hpost. subst post. reflexivity.
  - unfold sem_pend_resume_step in Hresume.
    destruct Hresume as [returned_prio Hready].
    unfold atomic_event_task_rdy_one in Hready.
    destruct Hready as
      (e1 & e2 & waiter & owner & owner' & Hevent & Htype & Hnonempty &
       Hhead & Hwaiter & Hreturned & Hslot & Howner & Howner_prio &
       Howner' & He2 & Hpost).
    cbv zeta in Hpost. subst post. reflexivity.
  - unfold sem_pend_resume_step, sem_pend_timeout_resume in Hresume.
    destruct Hresume as [old [new [Hold [Hnew Hpost]]]].
    cbv zeta in Hpost. subst post. reflexivity.
Qed.
Lemma sem_pend_cleanup_sched_preserved__blocked_tail_second_restore :
  forall tid entry post,
    sem_pend_cleanup_step tid entry post ->
    post.(SchedState) = entry.(SchedState).
Proof.
  intros tid entry post Hcleanup.
  destruct Hcleanup as [old [new [Hold [Hnew Hpost]]]].
  subst post. reflexivity.
Qed.
Lemma sem_pend_remove_sched_preserved__blocked_tail_second_restore :
  forall eid tid entry post,
    atomic_event_task_remove tid eid entry tt post ->
    post.(SchedState) = entry.(SchedState).
Proof.
  intros eid tid entry post Hremove.
  unfold atomic_event_task_remove in Hremove.
  destruct Hremove as
    (e1 & e2 & old & new & Hevent & Hin & Hold & He2 & Hnew & Hpost).
  subst post. reflexivity.
Qed.
Lemma sem_pend_final_cur_task_preserved__blocked_tail_second_restore :
  forall eid tid res entry post,
    sem_pend_final_step eid tid res entry post ->
    post.(SchedState).(curTaskID) = entry.(SchedState).(curTaskID).
Proof.
  intros eid tid res entry post Hfinal.
  destruct res.
  - unfold sem_pend_final_step in Hfinal.
    rewrite (sem_pend_cleanup_sched_preserved__blocked_tail_second_restore
      tid entry post Hfinal). reflexivity.
  - unfold sem_pend_final_step in Hfinal.
    rewrite (sem_pend_cleanup_sched_preserved__blocked_tail_second_restore
      tid entry post Hfinal). reflexivity.
  - unfold sem_pend_final_step in Hfinal.
    destruct Hfinal as [removed [Hremove Hcleanup]].
    rewrite (sem_pend_cleanup_sched_preserved__blocked_tail_second_restore
      tid removed post Hcleanup).
    rewrite (sem_pend_remove_sched_preserved__blocked_tail_second_restore
      eid tid entry removed Hremove).
    reflexivity.
Qed.
Lemma sem_pend_execution_final_tcb_snapshot__blocked_tail_second_restore :
  forall sg eid timeout entry wait_state res resume_state final_state tid tcb,
    sem_pend_select_current entry tid ->
    tcb = verification_slice_tcb_addr sg tid ->
    sem_pend_wait_step sg eid timeout entry wait_state ->
    sem_pend_resume_step sg eid tid wait_state res resume_state ->
    sem_pend_final_step eid tid res resume_state final_state ->
    verification_slice_sched_tcb_cur_snapshot_prop sg final_state.(SchedState) tcb.
Proof.
  intros sg eid timeout entry wait_state res resume_state final_state
    tid tcb Hselect Htcb Hwait Hresume Hfinal.
  pose proof
    (sem_pend_wait_cur_task_preserved__blocked_tail_second_restore
      sg eid timeout entry wait_state Hwait) as Hwait_cur.
  pose proof
    (sem_pend_resume_cur_task_preserved__blocked_tail_second_restore
      sg eid tid wait_state res resume_state Hresume) as Hresume_cur.
  pose proof
    (sem_pend_final_cur_task_preserved__blocked_tail_second_restore
      eid tid res resume_state final_state Hfinal) as Hfinal_cur.
  unfold sem_pend_select_current in Hselect.
  unfold verification_slice_sched_tcb_cur_snapshot_prop.
  rewrite Hfinal_cur, Hresume_cur, Hwait_cur, Hselect.
  exact Htcb.
Qed.
Lemma sem_pend_cleanup_rebuild_inv__blocked_tail_second_restore :
  forall sg s tid t tcb
         prio_addr stat_addr statpend_addr dly_addr eventptr_addr
         eventmultiptr_addr eventmultirdy_addr
         tcbcur_global_addr rdygrp_global_addr priocur_global_addr,
    sem_pend_runtime_layout_prop sg tcb prio_addr stat_addr statpend_addr
      dly_addr eventptr_addr eventmultiptr_addr eventmultirdy_addr
      tcbcur_global_addr rdygrp_global_addr priocur_global_addr ->
    tcb = verification_slice_tcb_addr sg tid ->
    task_mutex_pend_clean_prop t ->
    verification_slice_sched_tcb_cur_snapshot_prop sg s.(SchedState) tcb ->
    sem_pend_cleanup_nonintr_rest sg s tid t **
    interrupt_inv sg s.(IntrState) **
    tcbcur_global_addr # Ptr |-> tcb **
    stat_addr # UChar |-> 0 **
    statpend_addr # UChar |-> 0 **
    dly_addr # UInt |-> 0 **
    eventptr_addr # Ptr |-> 0 |--
    UCOS2_verification_slice_inv sg s.
Proof.
  intros sg s tid t tcb prio_addr stat_addr statpend_addr dly_addr
    eventptr_addr eventmultiptr_addr eventmultirdy_addr
    tcbcur_global_addr rdygrp_global_addr priocur_global_addr
    Hlayout Htcb Hclean Hsnapshot.
  unfold sem_pend_runtime_layout_prop in Hlayout.
  destruct Hlayout as
    [Hprio_addr [Hstat_addr [Hstatpend_addr [Hdly_addr [Heventptr_addr
     [Heventmultiptr_addr [Heventmultirdy_addr [Htcb_global
      [Hrdygrp_global Hpriocur_global]]]]]]]]].
  subst tcb. subst stat_addr. subst statpend_addr.
  subst dly_addr. subst eventptr_addr.
  unfold sem_pend_cleanup_nonintr_rest.
  pureIntros.
  sep_apply_l_atomic
    (sem_pend_cleanup_task_inv_rebuild__blocked_tail_second_restore
      sg s.(TskState) tid t H Hclean).
  assert (Hsched :
    tcbcur_global_addr # Ptr |-> verification_slice_tcb_addr sg tid **
    verification_slice_sched_inv_no_tcb_cur sg s.(TskState) s.(SchedState) |--
    verification_slice_sched_inv sg s.(TskState) s.(SchedState)).
  { unfold os_tcb_cur_addr in Htcb_global.
    unfold verification_slice_sched_tcb_cur_snapshot_prop in Hsnapshot.
    rewrite Htcb_global, Hsnapshot.
    unfold verification_slice_sched_inv, verification_slice_sched_inv_no_tcb_cur,
      verification_slice_store_sched_state, verification_slice_store_sched_state_no_tcb_cur.
    entailer!. }
  sep_apply_l_atomic Hsched.
  unfold UCOS2_verification_slice_inv.
  cancel (interrupt_inv sg s.(IntrState)).
  cancel (verification_slice_task_inv sg s.(TskState)).
  cancel (verification_slice_sched_inv sg s.(TskState) s.(SchedState)).
  cancel (verification_slice_event_inv sg s.(TskState) s.(EventState)).
  cancel (verification_slice_tick_inv sg s.(TickState)).
  unfold derivable1, coq_prop. intros. exact H0.
Qed.
Lemma UCOS2_verification_slice_inv_expose_validity__blocked_tail_second_restore :
  forall sg s,
    UCOS2_verification_slice_inv sg s |--
      UCOS2_verification_slice_inv sg s &&
      coq_prop (UCOS2_verification_slice_state_inv sg s).
Proof.
  intros sg s h Hinv.
  split; [exact Hinv |].
  pose proof (UCOS2_verification_slice_inv_split_raw_validity sg s h Hinv) as Hsplit.
  exact (proj2 Hsplit).
Qed.
Lemma sem_pend_cleanup_nonintr_expose_lookup__blocked_tail_second_restore :
  forall sg s tid t,
    sem_pend_cleanup_nonintr_rest sg s tid t |--
      sem_pend_cleanup_nonintr_rest sg s tid t &&
      coq_prop (s.(TskState).(inUsedTaskStates) tid = Some t).
Proof.
  intros sg s tid t h Hrest.
  split; [exact Hrest |].
  unfold sem_pend_cleanup_nonintr_rest in Hrest.
  exact (proj1 Hrest).
Qed.
Lemma truep_sepcon_truep__blocked_tail_second_restore :
  TT |-- TT ** TT.
Proof.
  unfold derivable1, truep, sepcon.
  intros m Htrue.
  destruct (unit_join m) as [u [Hunit Hjoin]].
  exists m, u. split; [exact Hjoin |].
  split; exact I.
Qed.
Lemma sem_pend_rdy_tbl_canonical__wait_task_sched_transport :
  forall sg tskSt schedSt l,
    array_abstraction.osrdytbl_list_rel sg tskSt schedSt l ->
    l = (sched.encode_ready_tbl_at
           (ucos2_verify_state_def.SchedStateDef.readyList schedSt) tskSt 0 ::
         sched.encode_ready_tbl_at
           (ucos2_verify_state_def.SchedStateDef.readyList schedSt) tskSt 1 ::
         sched.encode_ready_tbl_at
           (ucos2_verify_state_def.SchedStateDef.readyList schedSt) tskSt 2 ::
         sched.encode_ready_tbl_at
           (ucos2_verify_state_def.SchedStateDef.readyList schedSt) tskSt 3 ::
         sched.encode_ready_tbl_at
           (ucos2_verify_state_def.SchedStateDef.readyList schedSt) tskSt 4 ::
         sched.encode_ready_tbl_at
           (ucos2_verify_state_def.SchedStateDef.readyList schedSt) tskSt 5 ::
         sched.encode_ready_tbl_at
           (ucos2_verify_state_def.SchedStateDef.readyList schedSt) tskSt 6 ::
         sched.encode_ready_tbl_at
           (ucos2_verify_state_def.SchedStateDef.readyList schedSt) tskSt 7 :: nil).
Proof.
  intros sg tskSt schedSt l [Hlen Hnth].
  apply (proj2 (list_eq_ext l
    (sched.encode_ready_tbl_at
       (ucos2_verify_state_def.SchedStateDef.readyList schedSt) tskSt 0 ::
     sched.encode_ready_tbl_at
       (ucos2_verify_state_def.SchedStateDef.readyList schedSt) tskSt 1 ::
     sched.encode_ready_tbl_at
       (ucos2_verify_state_def.SchedStateDef.readyList schedSt) tskSt 2 ::
     sched.encode_ready_tbl_at
       (ucos2_verify_state_def.SchedStateDef.readyList schedSt) tskSt 3 ::
     sched.encode_ready_tbl_at
       (ucos2_verify_state_def.SchedStateDef.readyList schedSt) tskSt 4 ::
     sched.encode_ready_tbl_at
       (ucos2_verify_state_def.SchedStateDef.readyList schedSt) tskSt 5 ::
     sched.encode_ready_tbl_at
       (ucos2_verify_state_def.SchedStateDef.readyList schedSt) tskSt 6 ::
     sched.encode_ready_tbl_at
       (ucos2_verify_state_def.SchedStateDef.readyList schedSt) tskSt 7 :: nil) 0)).
  split.
  - rewrite Hlen.
    unfold array_abstraction.OS_RDY_TBL_SIZE.
    reflexivity.
  - intros i Hi.
    assert (Hrange : 0 <= i < array_abstraction.OS_RDY_TBL_SIZE).
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
      unfold array_abstraction.OS_RDY_TBL_SIZE in Hrange.
      exact (proj2 Hrange).
    }
    do 8 (destruct n as [|n]; [reflexivity|]).
    lia.
Qed.
Lemma sem_pend_sched_inv_split__wait_task_sched_transport :
  forall sg tskSt schedSt rdygrp rdytbl priocur tcbcur,
    array_abstraction.sched_ready_prio_snapshot_prop
      sg tskSt schedSt rdygrp rdytbl priocur ->
    sched.verification_slice_sched_tcb_cur_snapshot_prop sg schedSt tcbcur ->
    sched.verification_slice_sched_inv sg tskSt schedSt |--
      stable_glob_vars.g_OSTCBCur sg # Ptr |-> tcbcur **
      stable_glob_vars.g_OSRdyGrp sg # UChar |-> rdygrp **
      array_abstraction.store_osrdytbl sg rdytbl **
      stable_glob_vars.g_OSPrioCur sg # UChar |-> priocur **
      sched.verification_slice_sched_inv_rest_ready_current sg tskSt schedSt.
Proof.
  intros sg tskSt schedSt rdygrp rdytbl priocur tcbcur
    [Hgrp [Htbl Hprio]] Htcb.
  pose proof
    (sem_pend_rdy_tbl_canonical__wait_task_sched_transport
       sg tskSt schedSt rdytbl Htbl) as Hcanonical.
  subst rdytbl.
  unfold sched.verification_slice_sched_tcb_cur_snapshot_prop in Htcb.
  subst rdygrp priocur tcbcur.
  unfold sched.verification_slice_sched_inv, sched.verification_slice_store_sched_state,
    sched.verification_slice_sched_inv_rest_ready_current,
    sched.verification_slice_store_sched_state_rest_ready_current,
    array_abstraction.store_osrdytbl,
    store_array,
    array_abstraction.osrdytbl_element_store,
    array_abstraction.sizeof_OS_PRIO.
  cbn [store_array_rec sizeof_front_end_type].
  replace (stable_glob_vars.g_OSRdyTbl sg + 0 * 1)
    with (stable_glob_vars.g_OSRdyTbl sg + 0) by lia.
  replace (stable_glob_vars.g_OSRdyTbl sg + (0 + 1) * 1)
    with (stable_glob_vars.g_OSRdyTbl sg + 1) by lia.
  replace (stable_glob_vars.g_OSRdyTbl sg + (0 + 1 + 1) * 1)
    with (stable_glob_vars.g_OSRdyTbl sg + 2) by lia.
  replace (stable_glob_vars.g_OSRdyTbl sg + (0 + 1 + 1 + 1) * 1)
    with (stable_glob_vars.g_OSRdyTbl sg + 3) by lia.
  replace (stable_glob_vars.g_OSRdyTbl sg + (0 + 1 + 1 + 1 + 1) * 1)
    with (stable_glob_vars.g_OSRdyTbl sg + 4) by lia.
  replace (stable_glob_vars.g_OSRdyTbl sg + (0 + 1 + 1 + 1 + 1 + 1) * 1)
    with (stable_glob_vars.g_OSRdyTbl sg + 5) by lia.
  replace (stable_glob_vars.g_OSRdyTbl sg +
      (0 + 1 + 1 + 1 + 1 + 1 + 1) * 1)
    with (stable_glob_vars.g_OSRdyTbl sg + 6) by lia.
  replace (stable_glob_vars.g_OSRdyTbl sg +
      (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) * 1)
    with (stable_glob_vars.g_OSRdyTbl sg + 7) by lia.
  pureIntros.
  split_pure_spatial.
  - cancel.
    reflexivity.
  - split_pures.
    + apply derivable1s_coq_prop_r; exact H.
    + apply derivable1s_coq_prop_r.
      unfold array_abstraction.OS_RDY_TBL_SIZE.
      reflexivity.
    + apply derivable1s_coq_prop_r; reflexivity.
Qed.
Lemma sem_pend_task_inv_split__wait_task_sched_transport :
  forall sg entry cur_tid cur_t tcbcur cur_prio cur_stat cur_statpend
      cur_dly cur_eventptr cur_eventmultiptr cur_eventmultirdy,
    sem_pend_task_snapshot_prop sg entry cur_tid cur_t tcbcur cur_prio
      cur_stat cur_statpend cur_dly cur_eventptr cur_eventmultiptr
      cur_eventmultirdy ->
    task.verification_slice_task_inv sg (ucos2_verify_state_def.TskState entry) |--
      (tcbcur + task.verification_slice_OSTCBPrio_off) # UChar |-> cur_prio **
      (tcbcur + task.verification_slice_OSTCBStat_off) # UChar |-> cur_stat **
      (tcbcur + task.verification_slice_OSTCBStatPend_off) # UChar |-> cur_statpend **
      (tcbcur + task.verification_slice_OSTCBDly_off) # UInt |-> cur_dly **
      (tcbcur + task.verification_slice_OSTCBEventPtr_off) # Ptr |-> cur_eventptr **
      (tcbcur + task.verification_slice_OSTCBEventMultiPtr_off) # Ptr |-> cur_eventmultiptr **
      (tcbcur + task.verification_slice_OSTCBEventMultiRdy_off) # Ptr |-> cur_eventmultirdy **
      task.used_task_pend_rest sg tcbcur cur_tid cur_t **
      task.verification_slice_task_inv_no_tid sg (ucos2_verify_state_def.TskState entry) cur_tid.
Proof.
  intros sg entry cur_tid cur_t tcbcur cur_prio cur_stat cur_statpend
    cur_dly cur_eventptr cur_eventmultiptr cur_eventmultirdy Hsnapshot.
  unfold sem_pend_task_snapshot_prop,
    task.task_mutex_full_snapshot_of_prop in Hsnapshot.
  destruct Hsnapshot as
    [Hmap [Htcb [Hprio [Hstat [Hstatpend [Hdly
    [Heventptr [Heventmultiptr Heventmultirdy]]]]]]]].
  subst tcbcur cur_prio cur_stat cur_statpend cur_dly cur_eventptr
    cur_eventmultiptr cur_eventmultirdy.
  sep_apply_l_atomic
    (ucos2_verify_inv.verification_slice_task_inv_split_prio__focus_and_pure
       sg (ucos2_verify_state_def.TskState entry) cur_tid cur_t Hmap).
  unfold task.used_task_no_prio, task.used_task_pend_rest.
  cancel ((task.verification_slice_tcb_addr sg cur_tid + task.verification_slice_OSTCBPrio_off) # UChar |->
    ucos2_verify_state_def.TaskStateDef.curPrio cur_t).
  cancel ((task.verification_slice_tcb_addr sg cur_tid + task.verification_slice_OSTCBStat_off) # UChar |->
    task.encode_task_status
      (ucos2_verify_state_def.TaskStateDef.stat cur_t)).
  cancel ((task.verification_slice_tcb_addr sg cur_tid + task.verification_slice_OSTCBStatPend_off) # UChar |->
    task.encode_pend_status
      (ucos2_verify_state_def.TaskStateDef.statPend cur_t)).
  cancel ((task.verification_slice_tcb_addr sg cur_tid + task.verification_slice_OSTCBDly_off) # UInt |->
    ucos2_verify_state_def.TaskStateDef.dly cur_t).
  cancel ((task.verification_slice_tcb_addr sg cur_tid + task.verification_slice_OSTCBX_off) # UChar |->
    task.tcb_x_of_prio
      (ucos2_verify_state_def.TaskStateDef.curPrio cur_t)).
  cancel ((task.verification_slice_tcb_addr sg cur_tid + task.verification_slice_OSTCBY_off) # UChar |->
    task.tcb_y_of_prio
      (ucos2_verify_state_def.TaskStateDef.curPrio cur_t)).
  cancel ((task.verification_slice_tcb_addr sg cur_tid + task.verification_slice_OSTCBBitX_off) # UChar |->
    task.tcb_bit_x_of_prio
      (ucos2_verify_state_def.TaskStateDef.curPrio cur_t)).
  cancel ((task.verification_slice_tcb_addr sg cur_tid + task.verification_slice_OSTCBBitY_off) # UChar |->
    task.tcb_bit_y_of_prio
      (ucos2_verify_state_def.TaskStateDef.curPrio cur_t)).
  cancel ((task.verification_slice_tcb_addr sg cur_tid + task.verification_slice_OSTCBEventPtr_off) # Ptr |->
    task.encode_event_ptr
      (ucos2_verify_state_def.TaskStateDef.eventPtr cur_t)).
  cancel ((task.verification_slice_tcb_addr sg cur_tid + task.verification_slice_OSTCBEventMultiPtr_off) # Ptr |->
    task.encode_event_multi_ptr
      (ucos2_verify_state_def.TaskStateDef.eventMultiWaitEvents cur_t)).
  cancel ((task.verification_slice_tcb_addr sg cur_tid + task.verification_slice_OSTCBEventMultiRdy_off) # Ptr |->
    task.encode_event_ptr
      (ucos2_verify_state_def.TaskStateDef.eventMultiRdy cur_t)).
  cancel ((task.verification_slice_tcb_addr sg cur_tid + task.verification_slice_OSTCBMsg_off) # Ptr |->
    task.encode_msg (ucos2_verify_state_def.TaskStateDef.msg cur_t)).
  cancel ((task.verification_slice_tcb_addr sg cur_tid + task.verification_slice_OSTCBNext_off) # Ptr |->
    match ucos2_verify_state_def.TaskStateDef.nextTCB cur_t with
    | Some tid' => task.verification_slice_tcb_addr sg tid'
    | None => 0
    end).
  cancel ((task.verification_slice_tcb_addr sg cur_tid + task.verification_slice_OSTCBPrev_off) # Ptr |->
    match ucos2_verify_state_def.TaskStateDef.prevTCB cur_t with
    | Some tid' => task.verification_slice_tcb_addr sg tid'
    | None => 0
    end).
  cancel ((task.verification_slice_tcb_addr sg cur_tid + task.verification_slice_OSTCBDelReq_off) # UChar |->
    task.encode_bool
      (ucos2_verify_state_def.TaskStateDef.delReq cur_t)).
  cancel (task.verification_slice_task_inv_no_tid sg
    (ucos2_verify_state_def.TskState entry) cur_tid).
Qed.
