Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Import UCOS2_C_Rules.
Import TaskStateDef.

Local Open Scope Z_scope.
Local Open Scope sac_scope.

(* ================================================================== *)
(* L6: reversible annotation slices for OSMutexPend                     *)
(* ================================================================== *)

(* Concrete footprint passed from OSMutexPend's wait phase to OS_Sched.
   Keeping this as one named, reversible slice avoids fragile unification
   of anonymous array values while retaining every byte that the
   scheduler/resume step may inspect or update. *)
Definition mutex_pend_sched_pre
  (sg : StableGlobVars) (eid : EventID) (cur_tid : TaskID)
  (tcbcur : addr) (cur_t : TaskAbstractState)
  (ls_wait ls_frame ls_in : UCOS2_Verify_State)
  (timeout cur_prio prio_cur event_grp : Z)
  (event_tbl : list Z) (rdy_grp : Z) (rdy_tbl : list Z) : Assertion :=
  coq_prop (GTrans_C sg ls_wait sg ls_in /\
            crit_rel_task_event_sched ls_wait ls_in /\
            tcbcur = verification_slice_tcb_addr sg cur_tid) &&
  UCOS2_C_Rules.OutsideCritical (sg, ls_in) **
  interrupt_inv sg ls_in.(IntrState) **
  sg.(g_OSTCBCur) # Ptr |-> tcbcur **
  (tcbcur + verification_slice_OSTCBPrio_off) # UChar |-> cur_prio **
  (tcbcur + verification_slice_OSTCBStat_off) # UChar |-> 16 **
  (tcbcur + verification_slice_OSTCBStatPend_off) # UChar |-> 0 **
  (tcbcur + verification_slice_OSTCBDly_off) # UInt |-> timeout **
  (tcbcur + verification_slice_OSTCBEventPtr_off) # Ptr |-> event_addr sg eid **
  used_task_pend_rest sg tcbcur cur_tid cur_t **
  sg.(g_OSRdyGrp) # UChar |-> rdy_grp **
  store_osrdytbl sg rdy_tbl **
  sg.(g_OSPrioCur) # UChar |-> prio_cur **
  verification_slice_sched_inv_rest_ready_current
    sg ls_frame.(TskState) ls_frame.(SchedState) **
  (event_addr sg eid + OSEventGrp_off) # UChar |-> event_grp **
  store_oseventtbl sg (event_addr sg eid) event_tbl.

(* Global invariant with the current TCB's resume/cleanup cells and the
   OSTCBCur cell removed.  The caller owns those cells explicitly. *)
Definition mutex_pend_cleanup_nonintr_rest
  (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (cur_tid : TaskID) (cur_t : TaskAbstractState) : Assertion :=
  coq_prop (s.(TskState).(inUsedTaskStates) cur_tid = Some cur_t) &&
  used_task_cleanup_rest sg (verification_slice_tcb_addr sg cur_tid) cur_tid cur_t **
  verification_slice_task_inv_no_tid sg s.(TskState) cur_tid **
  verification_slice_sched_inv_no_tcb_cur sg s.(TskState) s.(SchedState) **
  verification_slice_event_inv sg s.(TskState) s.(EventState) **
  verification_slice_tick_inv sg s.(TickState) **
  coq_prop (verification_slice_cross_module_consistency sg s).

Definition mutex_pend_cleanup_rest
  (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (cur_tid : TaskID) (cur_t : TaskAbstractState) : Assertion :=
  interrupt_inv sg s.(IntrState) **
  mutex_pend_cleanup_nonintr_rest sg s cur_tid cur_t.
