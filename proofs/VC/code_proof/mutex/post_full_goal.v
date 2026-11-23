Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.mutex_func_sem.
Require Import Ucos2Verify.lib.mutex_rdyatprio_spec.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.mutex_post_spec.
Local Open Scope sac.

(*----- Function OSMutexPost_full -----*)

Definition OSMutexPost_full_safety_wit_1 := 
forall (pevent_pre: Z) (isr: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr <= 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (pevent_pre = pevent0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH10 : (isr > 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ False ”
.

Definition OSMutexPost_full_safety_wit_2 := 
forall (pevent_pre: Z) (isr: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr > 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (pevent_pre = pevent0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH10 : (isr <= 0)) (PreH11 : (pevent0 = 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ False ”
.

Definition OSMutexPost_full_safety_wit_3 := 
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr > 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (pevent_pre = pevent0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH10 : (isr <= 0)) (PreH11 : (pevent0 <> 0)) (PreH12 : (pevent0 = (event_addr (sg) (eid)))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ False ”
.

Definition OSMutexPost_full_safety_wit_4 := 
forall (pevent_pre: Z) (isr: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr <= 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (pevent_pre = pevent0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH10 : (isr <= 0)) (PreH11 : (pevent0 = 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexPost_full_safety_wit_5 := 
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr <= 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (pevent_pre = pevent0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH10 : (isr <= 0)) (PreH11 : (pevent0 <> 0)) (PreH12 : (pevent0 = (event_addr (sg) (eid)))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexPost_full_safety_wit_6 := 
forall (pevent_pre: Z) (isr: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre <> 0)) (PreH2 : (isr <= 0)) (PreH3 : (0 <= isr)) (PreH4 : (isr <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (pevent_pre = pevent0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH11 : (isr <= 0)) (PreH12 : (pevent0 = 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ False ”
.

Definition OSMutexPost_full_safety_wit_7 := 
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre = 0)) (PreH2 : (isr <= 0)) (PreH3 : (0 <= isr)) (PreH4 : (isr <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (pevent_pre = pevent0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH11 : (isr <= 0)) (PreH12 : (pevent0 <> 0)) (PreH13 : (pevent0 = (event_addr (sg) (eid)))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ False ”
.

Definition OSMutexPost_full_safety_wit_8 := 
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (PreH1 : (RTrans_C sg ls0 sg ls1 )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (etype = 4)) (PreH4 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) ,
  (InsideCritical sg ls1 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent0)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (0 <= ecnt_in) ” 
  &&  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
) \/
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (PreH1 : (RTrans_C sg ls0 sg ls1 )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (etype = 4)) (PreH4 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) ,
  (InsideCritical sg ls1 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent0)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (0 <= ecnt_in) ” 
  &&  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
).

Definition OSMutexPost_full_safety_wit_8_split_goal_1 := 
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (PreH1 : (RTrans_C sg ls0 sg ls1 )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (etype = 4)) (PreH4 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) ,
  (InsideCritical sg ls1 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent0)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (0 <= ecnt_in) ”
.

Definition OSMutexPost_full_safety_wit_8_split_goal_2 := 
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (PreH1 : (RTrans_C sg ls0 sg ls1 )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (etype = 4)) (PreH4 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) ,
  (InsideCritical sg ls1 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent0)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (8 <= 31) ”
.

Definition OSMutexPost_full_safety_wit_8_split_goal_3 := 
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (PreH1 : (RTrans_C sg ls0 sg ls1 )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (etype = 4)) (PreH4 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) ,
  (InsideCritical sg ls1 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent0)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (0 <= 8) ”
.

Definition OSMutexPost_full_safety_wit_9 := 
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_d: UCOS2_Verify_State) (prioL_d: (@list Z)) (cpu_sr_v: Z) (pcp_v: Z) (prio_v: Z) (PreH1 : (pcp_idx <> 255)) (PreH2 : (0 <= pcp_idx)) (PreH3 : (pcp_idx < 64)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH5 : (pevent0 = (event_addr (sg) (eid)))) (PreH6 : (pcp_v = pcp_idx)) (PreH7 : (pcp_idx <> 255)) (PreH8 : (0 <= pcp_idx)) (PreH9 : (pcp_idx < 64)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_idx)
  **  (((( &( "OSTCBPrioTbl" ) ) + (pcp_idx * sizeof(PTR)))) # Ptr  |-> (Znth (pcp_idx) (prioL_d) (0)))
  **  (store_priotbl_list_missing_i sg prioL_d pcp_idx )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_d.(TskState) )) (prioL_d)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_d.(TskState) )) ((ls_d.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent0)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (mutex_post_rep_no_priotbl_no_event sg ls0 ls_d eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "prio" ) )) # UChar  |-> prio_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OSMutexPost_full_safety_wit_10 := 
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls2: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State) (cpu_sr_v: Z) (pcp_v: Z) (prio_v: Z) (PreH1 : ((unsigned_last_nbits (egrp_in) (32)) <> 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH3 : (pevent0 = (event_addr (sg) (eid)))) (PreH4 : (pcp_v = pcp_idx)) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls2.(TskState) )) ((ls2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent0)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (mutex_post_rep_no_event sg ls0 ls2 eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |-> prio_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexPost_full_safety_wit_11 := 
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls2: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State) (cpu_sr_v: Z) (pcp_v: Z) (prio_v: Z) (PreH1 : ((unsigned_last_nbits (egrp_in) (32)) = 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH3 : (pevent0 = (event_addr (sg) (eid)))) (PreH4 : (pcp_v = pcp_idx)) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls2.(TskState) )) ((ls2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent0)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (mutex_post_rep_no_event sg ls0 ls2 eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits (ecnt_in) (16)) 255))
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |-> prio_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexPost_full_entail_wit_1_1 := 
(
forall (pevent_pre: Z) (isr: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (pevent_pre = pevent0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH5 : (isr > 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pevent_pre = pevent0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (isr > 0) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
) \/
(
forall (pevent_pre: Z) (isr: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (pevent_pre = pevent0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH7 : (isr > 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (isr <= 255) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
).

Definition OSMutexPost_full_entail_wit_1_1_split_goal_1 := 
forall (pevent_pre: Z) (isr: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (pevent_pre = pevent0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH7 : (isr > 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (isr <= 255) ”
.

Definition OSMutexPost_full_entail_wit_1_1_split_goal_spatial := 
forall (pevent_pre: Z) (isr: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (pevent_pre = pevent0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH7 : (isr > 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
.

Definition OSMutexPost_full_entail_wit_1_2 := 
(
forall (pevent_pre: Z) (isr: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (pevent_pre = pevent0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH5 : (isr <= 0)) (PreH6 : (pevent0 = 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pevent_pre = pevent0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent0 = 0) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
) \/
(
forall (pevent_pre: Z) (isr: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (pevent_pre = pevent0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH7 : (isr <= 0)) (PreH8 : (pevent0 = 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (0 <= isr) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
).

Definition OSMutexPost_full_entail_wit_1_2_split_goal_1 := 
forall (pevent_pre: Z) (isr: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (pevent_pre = pevent0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH7 : (isr <= 0)) (PreH8 : (pevent0 = 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (0 <= isr) ”
.

Definition OSMutexPost_full_entail_wit_1_2_split_goal_spatial := 
forall (pevent_pre: Z) (isr: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (pevent_pre = pevent0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH7 : (isr <= 0)) (PreH8 : (pevent0 = 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
.

Definition OSMutexPost_full_entail_wit_1_3 := 
(
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (pevent_pre = pevent0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH5 : (isr <= 0)) (PreH6 : (pevent0 <> 0)) (PreH7 : (pevent0 = (event_addr (sg) (eid)))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pevent_pre = pevent0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent0 <> 0) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
) \/
(
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (pevent_pre = pevent0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH7 : (isr <= 0)) (PreH8 : (pevent0 <> 0)) (PreH9 : (pevent0 = (event_addr (sg) (eid)))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (0 <= isr) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
).

Definition OSMutexPost_full_entail_wit_1_3_split_goal_1 := 
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (pevent_pre = pevent0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH7 : (isr <= 0)) (PreH8 : (pevent0 <> 0)) (PreH9 : (pevent0 = (event_addr (sg) (eid)))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (0 <= isr) ”
.

Definition OSMutexPost_full_entail_wit_1_3_split_goal_spatial := 
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (pevent_pre = pevent0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH7 : (isr <= 0)) (PreH8 : (pevent0 <> 0)) (PreH9 : (pevent0 = (event_addr (sg) (eid)))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
.

Definition OSMutexPost_full_entail_wit_2 := 
(
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype = 4)) (PreH2 : (tcbcur <> 0)) (PreH3 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH4 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH5 : ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) = 4)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (pevent_pre <> 0)) (PreH8 : (isr <= 0)) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (pevent_pre = pevent0)) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH17 : (isr <= 0)) (PreH18 : (pevent0 <> 0)) (PreH19 : (pevent0 = (event_addr (sg) (eid)))) ,
  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (pcp_idx = (decode_PCP_from_cnt (ecnt_in))) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ”
  &&  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
) \/
(
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype = 4)) (PreH2 : (tcbcur <> 0)) (PreH3 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH4 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH5 : ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) = 4)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (pevent_pre <> 0)) (PreH8 : (isr <= 0)) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (pevent_pre = pevent0)) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH17 : (isr <= 0)) (PreH18 : (pevent0 <> 0)) (PreH19 : (pevent0 = (event_addr (sg) (eid)))) ,
  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
).

Definition OSMutexPost_full_entail_wit_2_split_goal_spatial := 
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype = 4)) (PreH2 : (tcbcur <> 0)) (PreH3 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH4 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH5 : ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) = 4)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (pevent_pre <> 0)) (PreH8 : (isr <= 0)) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (pevent_pre = pevent0)) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH17 : (isr <= 0)) (PreH18 : (pevent0 <> 0)) (PreH19 : (pevent0 = (event_addr (sg) (eid)))) ,
  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
.

Definition OSMutexPost_full_entail_wit_3 := 
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1_2: UCOS2_Verify_State) (PreH1 : (RTrans_C sg ls0 sg ls1_2 )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (etype = 4)) (PreH4 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) ,
  (InsideCritical sg ls1_2 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  EX (ls1: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = pcp_idx) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = (decode_PCP_from_cnt (ecnt_in))) ” 
  &&  “ ((Z.land ecnt_in 255) = (decode_OwnerPrio_from_cnt (ecnt_in))) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (InsideCritical sg ls1 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls1.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls1.(TskState) ) (ls1.(SchedState) ) )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (tick_inv sg (ls1.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls1)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls1.(TskState) )) ((ls1.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls1.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls1.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1.(TskState) )) (prioL_in)) )
) \/
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1_2: UCOS2_Verify_State) (PreH1 : (RTrans_C sg ls0 sg ls1_2 )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (etype = 4)) (PreH4 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) ,
  (InsideCritical sg ls1_2 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  EX (ls1: UCOS2_Verify_State) ,
  “ (etype = 4) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = pcp_idx) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = (decode_PCP_from_cnt (ecnt_in))) ” 
  &&  “ ((Z.land ecnt_in 255) = (decode_OwnerPrio_from_cnt (ecnt_in))) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (InsideCritical sg ls1 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls1.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls1.(TskState) ) (ls1.(SchedState) ) )
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (tick_inv sg (ls1.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls1)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls1.(TskState) )) ((ls1.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls1.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls1.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1.(TskState) )) (prioL_in)) )
).

Definition OSMutexPost_full_entail_wit_4 := 
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1_2: UCOS2_Verify_State) (pcp_v: Z) (prio_v: Z) (PreH1 : (tcbcur = owner_ptr)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH3 : (pevent0 = (event_addr (sg) (eid)))) (PreH4 : (tcbcur <> 0)) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (pcp_v = pcp_idx)) (PreH7 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH8 : (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in)))) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (InsideCritical sg ls1_2 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_inv sg (ls1_2.(IntrState) ) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls1_2.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls1_2.(TskState) ) (ls1_2.(SchedState) ) )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (event_inv_no_eid sg (ls1_2.(TskState) ) (ls1_2.(EventState) ) eid )
  **  (tick_inv sg (ls1_2.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls1_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls1_2.(TskState) )) ((ls1_2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls1_2.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls1_2.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
|--
  EX (ls1: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (owner_ptr = tcbcur) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (pcp_v = (decode_PCP_from_cnt (ecnt_in))) ” 
  &&  “ (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in))) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_entry_context_prop (sg) (pevent0) (eid) (ls0) (ls1) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (tcbcur) (tcbprio)) )
  **  (InsideCritical sg ls1 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls1.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls1.(TskState) ) (ls1.(SchedState) ) )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (tick_inv sg (ls1.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls1)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls1.(TskState) )) ((ls1.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls1.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1.(TskState) )) (prioL_in)) )
) \/
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1_2: UCOS2_Verify_State) (pcp_v: Z) (prio_v: Z) (PreH1 : (tcbcur = owner_ptr)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH3 : (pevent0 = (event_addr (sg) (eid)))) (PreH4 : (tcbcur <> 0)) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (pcp_v = pcp_idx)) (PreH7 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH8 : (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in)))) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (InsideCritical sg ls1_2 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_inv sg (ls1_2.(IntrState) ) )
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls1_2.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  (sched_inv_no_tcb_cur sg (ls1_2.(TskState) ) (ls1_2.(SchedState) ) )
  **  (event_inv_no_eid sg (ls1_2.(TskState) ) (ls1_2.(EventState) ) eid )
  **  (tick_inv sg (ls1_2.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls1_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls1_2.(TskState) )) ((ls1_2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls1_2.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls1_2.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
|--
  EX (ls1: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (owner_ptr = tcbcur) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (pcp_v = (decode_PCP_from_cnt (ecnt_in))) ” 
  &&  “ (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in))) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_entry_context_prop (sg) (pevent0) (eid) (ls0) (ls1) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (tcbcur) (tcbprio)) )
  **  (InsideCritical sg ls1 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls1.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  (sched_inv_no_tcb_cur sg (ls1.(TskState) ) (ls1.(SchedState) ) )
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (tick_inv sg (ls1.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls1)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls1.(TskState) )) ((ls1.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls1.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1.(TskState) )) (prioL_in)) )
).

Definition OSMutexPost_full_entail_wit_5 := 
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (pcp_v: Z) (prio_v: Z) (PreH1 : (tcbprio = pcp_v)) (PreH2 : ((unsigned_last_nbits (pcp_v) (32)) <> 255)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH4 : (pevent0 = (event_addr (sg) (eid)))) (PreH5 : (owner_ptr = tcbcur)) (PreH6 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH7 : (pcp_v = pcp_idx)) (PreH8 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH9 : (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in)))) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_entry_context_prop (sg) (pevent0) (eid) (ls0) (ls1) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (tcbcur) (tcbprio)) )
  **  (InsideCritical sg ls1 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls1.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls1.(TskState) ) (ls1.(SchedState) ) )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (tick_inv sg (ls1.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls1)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls1.(TskState) )) ((ls1.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls1.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1.(TskState) )) (prioL_in)) )
|--
  EX (Xrdy: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop)))  (ls_rdy_pre: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (safeExec (LastSeen (ls_rdy_pre)) (bind ((OSMutexPost_RdyAtPrio_atomic_cmd (sg) (ls_rdy_pre) (tcbcur) (prio_v))) (observe_unit_void)) Xrdy ) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (pcp_idx <> 255) ” 
  &&  “ (tcbprio = pcp_idx) ” 
  &&  “ (owner_ptr = tcbcur) ” 
  &&  “ (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in))) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_entry_context_prop (sg) (pevent0) (eid) (ls0) (ls_rdy_pre) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (tcbcur) (pcp_idx)) )
  **  (InsideCritical sg ls_rdy_pre )
  **  (interrupt_inv sg (ls_rdy_pre.(IntrState) ) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls_rdy_pre.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls_rdy_pre.(TskState) ) (ls_rdy_pre.(SchedState) ) )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (event_inv_no_eid sg (ls_rdy_pre.(TskState) ) (ls_rdy_pre.(EventState) ) eid )
  **  (tick_inv sg (ls_rdy_pre.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls_rdy_pre)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_rdy_pre.(TskState) )) ((ls_rdy_pre.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_rdy_pre.(TskState) )) (prioL_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls_rdy_pre.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
) \/
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (pcp_v: Z) (prio_v: Z) (PreH1 : (tcbprio = pcp_v)) (PreH2 : ((unsigned_last_nbits (pcp_v) (32)) <> 255)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH4 : (pevent0 = (event_addr (sg) (eid)))) (PreH5 : (owner_ptr = tcbcur)) (PreH6 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH7 : (pcp_v = pcp_idx)) (PreH8 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH9 : (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in)))) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_entry_context_prop (sg) (pevent0) (eid) (ls0) (ls1) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (tcbcur) (tcbprio)) )
  **  (InsideCritical sg ls1 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls1.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  (sched_inv_no_tcb_cur sg (ls1.(TskState) ) (ls1.(SchedState) ) )
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (tick_inv sg (ls1.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls1)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls1.(TskState) )) ((ls1.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls1.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1.(TskState) )) (prioL_in)) )
|--
  EX (Xrdy: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop)))  (ls_rdy_pre: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (safeExec (LastSeen (ls_rdy_pre)) (bind ((OSMutexPost_RdyAtPrio_atomic_cmd (sg) (ls_rdy_pre) (tcbcur) (prio_v))) (observe_unit_void)) Xrdy ) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (pcp_idx <> 255) ” 
  &&  “ (tcbprio = pcp_idx) ” 
  &&  “ (owner_ptr = tcbcur) ” 
  &&  “ (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in))) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_entry_context_prop (sg) (pevent0) (eid) (ls0) (ls_rdy_pre) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (tcbcur) (pcp_idx)) )
  **  (InsideCritical sg ls_rdy_pre )
  **  (interrupt_inv sg (ls_rdy_pre.(IntrState) ) )
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls_rdy_pre.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  (sched_inv_no_tcb_cur sg (ls_rdy_pre.(TskState) ) (ls_rdy_pre.(SchedState) ) )
  **  (event_inv_no_eid sg (ls_rdy_pre.(TskState) ) (ls_rdy_pre.(EventState) ) eid )
  **  (tick_inv sg (ls_rdy_pre.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls_rdy_pre)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_rdy_pre.(TskState) )) ((ls_rdy_pre.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_rdy_pre.(TskState) )) (prioL_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls_rdy_pre.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
).

Definition OSMutexPost_full_entail_wit_6_1 := 
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (pcp_v: Z) (prio_v: Z) (PreH1 : (tcbprio <> pcp_v)) (PreH2 : ((unsigned_last_nbits (pcp_v) (32)) <> 255)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH4 : (pevent0 = (event_addr (sg) (eid)))) (PreH5 : (owner_ptr = tcbcur)) (PreH6 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH7 : (pcp_v = pcp_idx)) (PreH8 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH9 : (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in)))) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_entry_context_prop (sg) (pevent0) (eid) (ls0) (ls1) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (tcbcur) (tcbprio)) )
  **  (InsideCritical sg ls1 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls1.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls1.(TskState) ) (ls1.(SchedState) ) )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (tick_inv sg (ls1.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls1)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls1.(TskState) )) ((ls1.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls1.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1.(TskState) )) (prioL_in)) )
|--
  EX (ls_d: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (pcp_idx <> 255) ” 
  &&  “ (0 <= pcp_idx) ” 
  &&  “ (pcp_idx < 64) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_d.(TskState) )) ((ls_d.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (mutex_post_rep sg ls0 ls_d )
) \/
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (pcp_v: Z) (prio_v: Z) (PreH1 : (tcbprio <> pcp_v)) (PreH2 : ((unsigned_last_nbits (pcp_v) (32)) <> 255)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH4 : (pevent0 = (event_addr (sg) (eid)))) (PreH5 : (owner_ptr = tcbcur)) (PreH6 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH7 : (pcp_v = pcp_idx)) (PreH8 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH9 : (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in)))) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_entry_context_prop (sg) (pevent0) (eid) (ls0) (ls1) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (tcbcur) (tcbprio)) )
  **  (InsideCritical sg ls1 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls1.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls1.(TskState) ) (ls1.(SchedState) ) )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (tick_inv sg (ls1.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls1)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls1.(TskState) )) ((ls1.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls1.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1.(TskState) )) (prioL_in)) )
|--
  EX (ls_d: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (pcp_idx <> 255) ” 
  &&  “ (0 <= pcp_idx) ” 
  &&  “ (pcp_idx < 64) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_d.(TskState) )) ((ls_d.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (mutex_post_rep sg ls0 ls_d )
).

Definition OSMutexPost_full_entail_wit_6_2 := 
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_rdy_pre: UCOS2_Verify_State) (Xrdy: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (pcp_v: Z) (prio_v: Z) (ls_rdy: UCOS2_Verify_State) (PreH1 : (safeExec (OSMutexPost_RdyAtPrio_LastSeen (sg) (tcbcur) (prio_v) (ls_rdy_pre) (ls_rdy)) (return (tt)) Xrdy )) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH3 : (safeExec (LastSeen (ls_rdy_pre)) (bind ((OSMutexPost_RdyAtPrio_atomic_cmd (sg) (ls_rdy_pre) (tcbcur) (prio_v))) (observe_unit_void)) Xrdy )) (PreH4 : (pcp_v = pcp_idx)) (PreH5 : (pcp_idx <> 255)) (PreH6 : (tcbprio = pcp_idx)) (PreH7 : (owner_ptr = tcbcur)) (PreH8 : (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in)))) (PreH9 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  (coq_prop (mutex_post_current_ready_step_prop (sg) (tcbcur) (prio_v) (ls_rdy_pre) (ls_rdy)) )
  **  (coq_prop (OSMutexPost_RdyAtPrio_guarantee (sg) (tcbcur) (prio_v) (ls_rdy_pre) (ls_rdy)) )
  **  (coq_prop (mutex_post_owner_entry_context_prop (sg) (pevent0) (eid) (ls0) (ls_rdy_pre) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (tcbcur) (tcbprio)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_rdy)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_rdy.(TskState) )) ((ls_rdy.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls_rdy_pre )
  **  (UCOS2_raw_ready_prio_stage sg ls_rdy_pre ls_rdy )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  EX (ls_d: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (pcp_idx <> 255) ” 
  &&  “ (0 <= pcp_idx) ” 
  &&  “ (pcp_idx < 64) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_d.(TskState) )) ((ls_d.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (mutex_post_rep sg ls0 ls_d )
) \/
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_rdy_pre: UCOS2_Verify_State) (Xrdy: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (pcp_v: Z) (prio_v: Z) (ls_rdy: UCOS2_Verify_State) (PreH1 : (safeExec (OSMutexPost_RdyAtPrio_LastSeen (sg) (tcbcur) (prio_v) (ls_rdy_pre) (ls_rdy)) (return (tt)) Xrdy )) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH3 : (safeExec (LastSeen (ls_rdy_pre)) (bind ((OSMutexPost_RdyAtPrio_atomic_cmd (sg) (ls_rdy_pre) (tcbcur) (prio_v))) (observe_unit_void)) Xrdy )) (PreH4 : (pcp_v = pcp_idx)) (PreH5 : (pcp_idx <> 255)) (PreH6 : (tcbprio = pcp_idx)) (PreH7 : (owner_ptr = tcbcur)) (PreH8 : (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in)))) (PreH9 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  (coq_prop (mutex_post_current_ready_step_prop (sg) (tcbcur) (prio_v) (ls_rdy_pre) (ls_rdy)) )
  **  (coq_prop (OSMutexPost_RdyAtPrio_guarantee (sg) (tcbcur) (prio_v) (ls_rdy_pre) (ls_rdy)) )
  **  (coq_prop (mutex_post_owner_entry_context_prop (sg) (pevent0) (eid) (ls0) (ls_rdy_pre) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (tcbcur) (tcbprio)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_rdy)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_rdy.(TskState) )) ((ls_rdy.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls_rdy_pre )
  **  (UCOS2_raw_ready_prio_stage sg ls_rdy_pre ls_rdy )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  EX (ls_d: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (pcp_idx <> 255) ” 
  &&  “ (0 <= pcp_idx) ” 
  &&  “ (pcp_idx < 64) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_d.(TskState) )) ((ls_d.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (mutex_post_rep sg ls0 ls_d )
).

Definition OSMutexPost_full_entail_wit_7 := 
(
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_d_2: UCOS2_Verify_State) (pcp_v: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (pcp_v = pcp_idx)) (PreH4 : (pcp_idx <> 255)) (PreH5 : (0 <= pcp_idx)) (PreH6 : (pcp_idx < 64)) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_d_2.(TskState) )) ((ls_d_2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (mutex_post_rep sg ls0 ls_d_2 )
|--
  EX (prioL_d: (@list Z))  (ls_d: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (pcp_idx <> 255) ” 
  &&  “ (0 <= pcp_idx) ” 
  &&  “ (pcp_idx < 64) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_d.(TskState) )) (prioL_d)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_d.(TskState) )) ((ls_d.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (store_priotbl_list sg prioL_d )
  **  (mutex_post_rep_no_priotbl_no_event sg ls0 ls_d eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
) \/
(
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_d_2: UCOS2_Verify_State) (pcp_v: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (pcp_v = pcp_idx)) (PreH4 : (pcp_idx <> 255)) (PreH5 : (0 <= pcp_idx)) (PreH6 : (pcp_idx < 64)) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_d_2.(TskState) )) ((ls_d_2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (mutex_post_rep sg ls0 ls_d_2 )
|--
  EX (prioL_d: (@list Z))  (ls_d: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (pcp_idx <> 255) ” 
  &&  “ (0 <= pcp_idx) ” 
  &&  “ (pcp_idx < 64) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_d.(TskState) )) (prioL_d)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_d.(TskState) )) ((ls_d.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (store_priotbl_list sg prioL_d )
  **  (mutex_post_rep_no_priotbl_no_event sg ls0 ls_d eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
).

Definition OSMutexPost_full_entail_wit_8_1 := 
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (pcp_v: Z) (prio_v: Z) (PreH1 : ((unsigned_last_nbits (pcp_v) (32)) = 255)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH3 : (pevent0 = (event_addr (sg) (eid)))) (PreH4 : (owner_ptr = tcbcur)) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (pcp_v = pcp_idx)) (PreH7 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH8 : (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in)))) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_entry_context_prop (sg) (pevent0) (eid) (ls0) (ls1) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (tcbcur) (tcbprio)) )
  **  (InsideCritical sg ls1 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls1.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls1.(TskState) ) (ls1.(SchedState) ) )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (tick_inv sg (ls1.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls1)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls1.(TskState) )) ((ls1.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls1.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1.(TskState) )) (prioL_in)) )
|--
  EX (ls2: UCOS2_Verify_State)  (ls_d: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls2.(TskState) )) ((ls2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (mutex_post_rep_no_event sg ls0 ls2 eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
) \/
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (pcp_v: Z) (prio_v: Z) (PreH1 : ((unsigned_last_nbits (pcp_v) (32)) = 255)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH3 : (pevent0 = (event_addr (sg) (eid)))) (PreH4 : (owner_ptr = tcbcur)) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (pcp_v = pcp_idx)) (PreH7 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH8 : (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in)))) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_entry_context_prop (sg) (pevent0) (eid) (ls0) (ls1) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (tcbcur) (tcbprio)) )
  **  (InsideCritical sg ls1 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls1.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls1.(TskState) ) (ls1.(SchedState) ) )
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (tick_inv sg (ls1.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls1)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls1.(TskState) )) ((ls1.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls1.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1.(TskState) )) (prioL_in)) )
|--
  EX (ls2: UCOS2_Verify_State)  (ls_d: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls2.(TskState) )) ((ls2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (mutex_post_rep_no_event sg ls0 ls2 eid )
).

Definition OSMutexPost_full_entail_wit_8_2 := 
(
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_d_2: UCOS2_Verify_State) (prioL_d: (@list Z)) (pcp_v: Z) (PreH1 : (pcp_idx <> 255)) (PreH2 : (0 <= pcp_idx)) (PreH3 : (pcp_idx < 64)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH5 : (pevent0 = (event_addr (sg) (eid)))) (PreH6 : (pcp_v = pcp_idx)) (PreH7 : (pcp_idx <> 255)) (PreH8 : (0 <= pcp_idx)) (PreH9 : (pcp_idx < 64)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (pcp_idx * sizeof(PTR)))) # Ptr  |-> 1)
  **  (store_priotbl_list_missing_i sg prioL_d pcp_idx )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_d_2.(TskState) )) (prioL_d)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_d_2.(TskState) )) ((ls_d_2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (mutex_post_rep_no_priotbl_no_event sg ls0 ls_d_2 eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
|--
  EX (ls2: UCOS2_Verify_State)  (ls_d: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_idx = pcp_idx) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls2.(TskState) )) ((ls2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (mutex_post_rep_no_event sg ls0 ls2 eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
) \/
(
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_d_2: UCOS2_Verify_State) (prioL_d: (@list Z)) (pcp_v: Z) (PreH1 : (pcp_idx <> 255)) (PreH2 : (0 <= pcp_idx)) (PreH3 : (pcp_idx < 64)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH5 : (pevent0 = (event_addr (sg) (eid)))) (PreH6 : (pcp_v = pcp_idx)) (PreH7 : (pcp_idx <> 255)) (PreH8 : (0 <= pcp_idx)) (PreH9 : (pcp_idx < 64)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (pcp_idx * sizeof(PTR)))) # Ptr  |-> 1)
  **  (store_priotbl_list_missing_i sg prioL_d pcp_idx )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_d_2.(TskState) )) (prioL_d)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_d_2.(TskState) )) ((ls_d_2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (mutex_post_rep_no_priotbl_no_event sg ls0 ls_d_2 eid )
|--
  EX (ls2: UCOS2_Verify_State)  (ls_d: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls2.(TskState) )) ((ls2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (mutex_post_rep_no_event sg ls0 ls2 eid )
).

Definition OSMutexPost_full_entail_wit_9 := 
(
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp_v: Z) (e_h_2: OSEventAbstractState) (cnt_out: Z) (ptr_out: Z) (egrp_out: Z) (evtL_out: (@list Z)) (ls_d: UCOS2_Verify_State) (ls: UCOS2_Verify_State) (canonical_waiter_2: Z) (table_owner_2: Z) (ls_wake_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (pevent0 = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits (egrp_in) (32)) <> 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH4 : (pevent0 = (event_addr (sg) (eid)))) (PreH5 : (pcp_v = pcp_idx)) ,
  (coq_prop (mutex_post_wake_step_prop (sg) (eid) (ls) (retval) (canonical_waiter_2) (table_owner_2) (ls_wake_2)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls.(TskState) )) ((ls.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_wake_2.(TskState) )) ((ls_wake_2.(EventState) )) (eid) (e_h_2) (4) (cnt_out) (ptr_out) (egrp_out) (evtL_out)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (should_be_equal (((ls_wake_2.(TskState) ).(prioTbl) (retval))) ((PTTask (table_owner_2)))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (mutex_post_handover_residual sg ls0 ls_wake_2 eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land ecnt_in 65280) (unsigned_last_nbits (retval) (16))))
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_out)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_out) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_out) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_out) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_out) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_out) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_out) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_out) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_out) (0)))
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
|--
  EX (prioL_h: (@list Z))  (e_h: OSEventAbstractState)  (cnt_h: Z)  (ptr_h: Z)  (egrp_h: Z)  (evtL_h: (@list Z))  (ls_cnt: UCOS2_Verify_State)  (canonical_waiter: Z)  (table_owner: Z)  (ls_wake: UCOS2_Verify_State)  (ls_r: UCOS2_Verify_State)  (ls_d0: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 64) ” 
  &&  “ ((Znth (retval) (prioL_h) (0)) = (tcb_addr (sg) (table_owner))) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d0)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d0) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_wake_step_prop (sg) (eid) (ls_r) (retval) (canonical_waiter) (table_owner) (ls_wake)) )
  **  (coq_prop (mutex_post_count_commit_step_prop (eid) (retval) (ls_wake) (ls_cnt)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_cnt.(TskState) )) ((ls_cnt.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (egrp_h) (evtL_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (should_be_equal (((ls_cnt.(TskState) ).(prioTbl) (retval))) ((PTTask (table_owner)))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_cnt.(TskState) )) (prioL_h)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (mutex_post_handover_residual_no_priotbl sg ls0 ls_cnt eid )
  **  (store_priotbl_list sg prioL_h )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_h)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_h)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_h) (0)))
) \/
(
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp_v: Z) (e_h_2: OSEventAbstractState) (cnt_out: Z) (ptr_out: Z) (egrp_out: Z) (evtL_out: (@list Z)) (ls_d: UCOS2_Verify_State) (ls: UCOS2_Verify_State) (canonical_waiter_2: Z) (table_owner_2: Z) (ls_wake_2: UCOS2_Verify_State) (retval: Z) (PreH1 : (pevent0 = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits (egrp_in) (32)) <> 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH4 : (pevent0 = (event_addr (sg) (eid)))) (PreH5 : (pcp_v = pcp_idx)) ,
  (coq_prop (mutex_post_wake_step_prop (sg) (eid) (ls) (retval) (canonical_waiter_2) (table_owner_2) (ls_wake_2)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls.(TskState) )) ((ls.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_wake_2.(TskState) )) ((ls_wake_2.(EventState) )) (eid) (e_h_2) (4) (cnt_out) (ptr_out) (egrp_out) (evtL_out)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (should_be_equal (((ls_wake_2.(TskState) ).(prioTbl) (retval))) ((PTTask (table_owner_2)))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (mutex_post_handover_residual sg ls0 ls_wake_2 eid )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
|--
  EX (prioL_h: (@list Z))  (e_h: OSEventAbstractState)  (ptr_h: Z)  (evtL_h: (@list Z))  (ls_cnt: UCOS2_Verify_State)  (canonical_waiter: Z)  (table_owner: Z)  (ls_wake: UCOS2_Verify_State)  (ls_r: UCOS2_Verify_State)  (ls_d0: UCOS2_Verify_State) ,
  “ ((Znth (7) (evtL_out) (0)) = (Znth (7) (evtL_h) (0))) ” 
  &&  “ ((Znth (6) (evtL_out) (0)) = (Znth (6) (evtL_h) (0))) ” 
  &&  “ ((Znth (5) (evtL_out) (0)) = (Znth (5) (evtL_h) (0))) ” 
  &&  “ ((Znth (4) (evtL_out) (0)) = (Znth (4) (evtL_h) (0))) ” 
  &&  “ ((Znth (3) (evtL_out) (0)) = (Znth (3) (evtL_h) (0))) ” 
  &&  “ ((Znth (2) (evtL_out) (0)) = (Znth (2) (evtL_h) (0))) ” 
  &&  “ ((Znth (1) (evtL_out) (0)) = (Znth (1) (evtL_h) (0))) ” 
  &&  “ ((Znth (0) (evtL_out) (0)) = (Znth (0) (evtL_h) (0))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 64) ” 
  &&  “ ((Znth (retval) (prioL_h) (0)) = (tcb_addr (sg) (table_owner))) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d0)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d0) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_wake_step_prop (sg) (eid) (ls_r) (retval) (canonical_waiter) (table_owner) (ls_wake)) )
  **  (coq_prop (mutex_post_count_commit_step_prop (eid) (retval) (ls_wake) (ls_cnt)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_cnt.(TskState) )) ((ls_cnt.(EventState) )) (eid) (e_h) (4) ((Z.lor (Z.land ecnt_in 65280) (unsigned_last_nbits (retval) (16)))) (ptr_h) (egrp_out) (evtL_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (should_be_equal (((ls_cnt.(TskState) ).(prioTbl) (retval))) ((PTTask (table_owner)))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_cnt.(TskState) )) (prioL_h)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (mutex_post_handover_residual_no_priotbl sg ls0 ls_cnt eid )
  **  (store_priotbl_list sg prioL_h )
).

Definition OSMutexPost_full_entail_wit_10 := 
(
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_wake_2: UCOS2_Verify_State) (ls_cnt_2: UCOS2_Verify_State) (ls_r_2: UCOS2_Verify_State) (ls_d0: UCOS2_Verify_State) (canonical_waiter_2: Z) (table_owner_2: Z) (e_h_2: OSEventAbstractState) (prioL_h: (@list Z)) (cnt_h_2: Z) (ptr_h_2: Z) (egrp_h: Z) (evtL_h: (@list Z)) (pcp_v: Z) (prio_v: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (pcp_v = pcp_idx)) (PreH4 : (0 <= prio_v)) (PreH5 : (prio_v < 64)) (PreH6 : ((Znth (prio_v) (prioL_h) (0)) = (tcb_addr (sg) (table_owner_2)))) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_v * sizeof(PTR)))) # Ptr  |-> (tcb_addr (sg) (table_owner_2)))
  **  (store_priotbl_list_missing_i sg prioL_h prio_v )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d0)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d0) (ls_r_2)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r_2.(TskState) )) ((ls_r_2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_wake_step_prop (sg) (eid) (ls_r_2) (prio_v) (canonical_waiter_2) (table_owner_2) (ls_wake_2)) )
  **  (coq_prop (mutex_post_count_commit_step_prop (eid) (prio_v) (ls_wake_2) (ls_cnt_2)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_cnt_2.(TskState) )) ((ls_cnt_2.(EventState) )) (eid) (e_h_2) (4) (cnt_h_2) (ptr_h_2) (egrp_h) (evtL_h)) )
  **  (coq_prop (should_be_equal (((ls_cnt_2.(TskState) ).(prioTbl) (prio_v))) ((PTTask (table_owner_2)))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_cnt_2.(TskState) )) (prioL_h)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (mutex_post_handover_residual_no_priotbl sg ls0 ls_cnt_2 eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_h_2)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (tcb_addr (sg) (table_owner_2)))
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_h)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_h) (0)))
|--
  EX (e_h: OSEventAbstractState)  (cnt_h: Z)  (ptr_h: Z)  (grp_h: Z)  (tbl_h: (@list Z))  (ls_h: UCOS2_Verify_State)  (ls_cnt: UCOS2_Verify_State)  (canonical_waiter: Z)  (table_owner: Z)  (ls_wake: UCOS2_Verify_State)  (ls_r: UCOS2_Verify_State)  (ls_d: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_wake_step_prop (sg) (eid) (ls_r) (prio_v) (canonical_waiter) (table_owner) (ls_wake)) )
  **  (coq_prop (mutex_post_count_commit_step_prop (eid) (prio_v) (ls_wake) (ls_cnt)) )
  **  (coq_prop (mutex_post_owner_commit_step_prop (eid) (prio_v) (table_owner) (ls_cnt) (ls_h)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_v) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (crit_rel_task_event_sched (ls0) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_h)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (InsideCritical sg ls0 )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h )
) \/
(
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_wake_2: UCOS2_Verify_State) (ls_cnt_2: UCOS2_Verify_State) (ls_r_2: UCOS2_Verify_State) (ls_d0: UCOS2_Verify_State) (canonical_waiter_2: Z) (table_owner_2: Z) (e_h_2: OSEventAbstractState) (prioL_h: (@list Z)) (cnt_h_2: Z) (ptr_h_2: Z) (egrp_h: Z) (evtL_h: (@list Z)) (pcp_v: Z) (prio_v: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (pcp_v = pcp_idx)) (PreH4 : (0 <= prio_v)) (PreH5 : (prio_v < 64)) (PreH6 : ((Znth (prio_v) (prioL_h) (0)) = (tcb_addr (sg) (table_owner_2)))) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_v * sizeof(PTR)))) # Ptr  |-> (tcb_addr (sg) (table_owner_2)))
  **  (store_priotbl_list_missing_i sg prioL_h prio_v )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d0)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d0) (ls_r_2)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r_2.(TskState) )) ((ls_r_2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_wake_step_prop (sg) (eid) (ls_r_2) (prio_v) (canonical_waiter_2) (table_owner_2) (ls_wake_2)) )
  **  (coq_prop (mutex_post_count_commit_step_prop (eid) (prio_v) (ls_wake_2) (ls_cnt_2)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_cnt_2.(TskState) )) ((ls_cnt_2.(EventState) )) (eid) (e_h_2) (4) (cnt_h_2) (ptr_h_2) (egrp_h) (evtL_h)) )
  **  (coq_prop (should_be_equal (((ls_cnt_2.(TskState) ).(prioTbl) (prio_v))) ((PTTask (table_owner_2)))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_cnt_2.(TskState) )) (prioL_h)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (mutex_post_handover_residual_no_priotbl sg ls0 ls_cnt_2 eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_h_2)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (tcb_addr (sg) (table_owner_2)))
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_h)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_h) (0)))
|--
  EX (e_h: OSEventAbstractState)  (cnt_h: Z)  (ptr_h: Z)  (grp_h: Z)  (tbl_h: (@list Z))  (ls_h: UCOS2_Verify_State)  (ls_cnt: UCOS2_Verify_State)  (canonical_waiter: Z)  (table_owner: Z)  (ls_wake: UCOS2_Verify_State)  (ls_r: UCOS2_Verify_State)  (ls_d: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_wake_step_prop (sg) (eid) (ls_r) (prio_v) (canonical_waiter) (table_owner) (ls_wake)) )
  **  (coq_prop (mutex_post_count_commit_step_prop (eid) (prio_v) (ls_wake) (ls_cnt)) )
  **  (coq_prop (mutex_post_owner_commit_step_prop (eid) (prio_v) (table_owner) (ls_cnt) (ls_h)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_v) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (crit_rel_task_event_sched (ls0) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_h)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (InsideCritical sg ls0 )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h )
).

Definition OSMutexPost_full_entail_wit_11 := 
(
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_h_2: UCOS2_Verify_State) (ls_cnt: UCOS2_Verify_State) (ls_wake: UCOS2_Verify_State) (ls_r_2: UCOS2_Verify_State) (ls_d_2: UCOS2_Verify_State) (e_h_2: OSEventAbstractState) (canonical_waiter_2: Z) (table_owner_2: Z) (pcp_v: Z) (prio_v: Z) (cnt_h_2: Z) (ptr_h_2: Z) (grp_h_2: Z) (tbl_h: (@list Z)) (PreH1 : (GTrans_C sg ls0 sg ls_h_2 )) (PreH2 : (prio_v <= pcp_v)) (PreH3 : ((unsigned_last_nbits (pcp_v) (32)) <> 255)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH5 : (pevent0 = (event_addr (sg) (eid)))) (PreH6 : (pcp_v = pcp_idx)) ,
  (OutsideCritical sg ls_h_2 )
  **  (coq_prop (crit_rel_task_event_sched (ls0) (ls_h_2)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d_2)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d_2) (ls_r_2)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r_2.(TskState) )) ((ls_r_2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_wake_step_prop (sg) (eid) (ls_r_2) (prio_v) (canonical_waiter_2) (table_owner_2) (ls_wake)) )
  **  (coq_prop (mutex_post_count_commit_step_prop (eid) (prio_v) (ls_wake) (ls_cnt)) )
  **  (coq_prop (mutex_post_owner_commit_step_prop (eid) (prio_v) (table_owner_2) (ls_cnt) (ls_h_2)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d_2) (prio_v) (canonical_waiter_2) (table_owner_2) (ls_h_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h_2.(TskState) )) ((ls_h_2.(EventState) )) (eid) (e_h_2) (4) (cnt_h_2) (ptr_h_2) (grp_h_2) (tbl_h)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h_2 )
|--
  EX (e_h: OSEventAbstractState)  (cnt_h: Z)  (ptr_h: Z)  (grp_h: Z)  (tbl_o: (@list Z))  (canonical_waiter: Z)  (table_owner: Z)  (ls_h: UCOS2_Verify_State)  (ls_r: UCOS2_Verify_State)  (ls_d: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (pcp_idx <> 255) ” 
  &&  “ (prio_v <= pcp_idx) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_v) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_o)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (OutsideCritical sg ls_h )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h )
) \/
(
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_h_2: UCOS2_Verify_State) (ls_cnt: UCOS2_Verify_State) (ls_wake: UCOS2_Verify_State) (ls_r_2: UCOS2_Verify_State) (ls_d_2: UCOS2_Verify_State) (e_h_2: OSEventAbstractState) (canonical_waiter_2: Z) (table_owner_2: Z) (pcp_v: Z) (prio_v: Z) (cnt_h_2: Z) (ptr_h_2: Z) (grp_h_2: Z) (tbl_h: (@list Z)) (PreH1 : (GTrans_C sg ls0 sg ls_h_2 )) (PreH2 : (prio_v <= pcp_v)) (PreH3 : ((unsigned_last_nbits (pcp_v) (32)) <> 255)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH5 : (pevent0 = (event_addr (sg) (eid)))) (PreH6 : (pcp_v = pcp_idx)) ,
  (OutsideCritical sg ls_h_2 )
  **  (coq_prop (crit_rel_task_event_sched (ls0) (ls_h_2)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d_2)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d_2) (ls_r_2)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r_2.(TskState) )) ((ls_r_2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_wake_step_prop (sg) (eid) (ls_r_2) (prio_v) (canonical_waiter_2) (table_owner_2) (ls_wake)) )
  **  (coq_prop (mutex_post_count_commit_step_prop (eid) (prio_v) (ls_wake) (ls_cnt)) )
  **  (coq_prop (mutex_post_owner_commit_step_prop (eid) (prio_v) (table_owner_2) (ls_cnt) (ls_h_2)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d_2) (prio_v) (canonical_waiter_2) (table_owner_2) (ls_h_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h_2.(TskState) )) ((ls_h_2.(EventState) )) (eid) (e_h_2) (4) (cnt_h_2) (ptr_h_2) (grp_h_2) (tbl_h)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h_2 )
|--
  EX (e_h: OSEventAbstractState)  (cnt_h: Z)  (ptr_h: Z)  (grp_h: Z)  (tbl_o: (@list Z))  (canonical_waiter: Z)  (table_owner: Z)  (ls_h: UCOS2_Verify_State)  (ls_r: UCOS2_Verify_State)  (ls_d: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (pcp_idx <> 255) ” 
  &&  “ (prio_v <= pcp_idx) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_v) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_o)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (OutsideCritical sg ls_h )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h )
).

Definition OSMutexPost_full_entail_wit_12_1 := 
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_h_2: UCOS2_Verify_State) (ls_cnt: UCOS2_Verify_State) (ls_wake: UCOS2_Verify_State) (ls_r_2: UCOS2_Verify_State) (ls_d_2: UCOS2_Verify_State) (e_h_2: OSEventAbstractState) (canonical_waiter_2: Z) (table_owner_2: Z) (pcp_v: Z) (prio_v: Z) (cnt_h_2: Z) (ptr_h_2: Z) (grp_h_2: Z) (tbl_h: (@list Z)) (PreH1 : (GTrans_C sg ls0 sg ls_h_2 )) (PreH2 : (prio_v > pcp_v)) (PreH3 : ((unsigned_last_nbits (pcp_v) (32)) <> 255)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH5 : (pevent0 = (event_addr (sg) (eid)))) (PreH6 : (pcp_v = pcp_idx)) ,
  (OutsideCritical sg ls_h_2 )
  **  (coq_prop (crit_rel_task_event_sched (ls0) (ls_h_2)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d_2)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d_2) (ls_r_2)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r_2.(TskState) )) ((ls_r_2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_wake_step_prop (sg) (eid) (ls_r_2) (prio_v) (canonical_waiter_2) (table_owner_2) (ls_wake)) )
  **  (coq_prop (mutex_post_count_commit_step_prop (eid) (prio_v) (ls_wake) (ls_cnt)) )
  **  (coq_prop (mutex_post_owner_commit_step_prop (eid) (prio_v) (table_owner_2) (ls_cnt) (ls_h_2)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d_2) (prio_v) (canonical_waiter_2) (table_owner_2) (ls_h_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h_2.(TskState) )) ((ls_h_2.(EventState) )) (eid) (e_h_2) (4) (cnt_h_2) (ptr_h_2) (grp_h_2) (tbl_h)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h_2 )
|--
  (EX (e_h: OSEventAbstractState)  (cnt_h: Z)  (ptr_h: Z)  (grp_h: Z)  (tbl_o: (@list Z))  (canonical_waiter: Z)  (table_owner: Z)  (ls_h: UCOS2_Verify_State)  (ls_r: UCOS2_Verify_State)  (ls_d: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (prio_v > pcp_idx) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_v) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_o)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (OutsideCritical sg ls_h )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h ))
  ||
  (EX (e_h: OSEventAbstractState)  (cnt_h: Z)  (ptr_h: Z)  (grp_h: Z)  (tbl_o: (@list Z))  (canonical_waiter: Z)  (table_owner: Z)  (ls_h: UCOS2_Verify_State)  (ls_r: UCOS2_Verify_State)  (ls_d: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (pcp_idx = 255) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_v) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_o)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (OutsideCritical sg ls_h )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h ))
.

Definition OSMutexPost_full_entail_wit_12_2 := 
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_h_2: UCOS2_Verify_State) (ls_cnt: UCOS2_Verify_State) (ls_wake: UCOS2_Verify_State) (ls_r_2: UCOS2_Verify_State) (ls_d_2: UCOS2_Verify_State) (e_h_2: OSEventAbstractState) (canonical_waiter_2: Z) (table_owner_2: Z) (pcp_v: Z) (prio_v: Z) (cnt_h_2: Z) (ptr_h_2: Z) (grp_h_2: Z) (tbl_h: (@list Z)) (PreH1 : (GTrans_C sg ls0 sg ls_h_2 )) (PreH2 : ((unsigned_last_nbits (pcp_v) (32)) = 255)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH4 : (pevent0 = (event_addr (sg) (eid)))) (PreH5 : (pcp_v = pcp_idx)) ,
  (OutsideCritical sg ls_h_2 )
  **  (coq_prop (crit_rel_task_event_sched (ls0) (ls_h_2)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d_2)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d_2) (ls_r_2)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r_2.(TskState) )) ((ls_r_2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_wake_step_prop (sg) (eid) (ls_r_2) (prio_v) (canonical_waiter_2) (table_owner_2) (ls_wake)) )
  **  (coq_prop (mutex_post_count_commit_step_prop (eid) (prio_v) (ls_wake) (ls_cnt)) )
  **  (coq_prop (mutex_post_owner_commit_step_prop (eid) (prio_v) (table_owner_2) (ls_cnt) (ls_h_2)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d_2) (prio_v) (canonical_waiter_2) (table_owner_2) (ls_h_2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h_2.(TskState) )) ((ls_h_2.(EventState) )) (eid) (e_h_2) (4) (cnt_h_2) (ptr_h_2) (grp_h_2) (tbl_h)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h_2 )
|--
  (EX (e_h: OSEventAbstractState)  (cnt_h: Z)  (ptr_h: Z)  (grp_h: Z)  (tbl_o: (@list Z))  (canonical_waiter: Z)  (table_owner: Z)  (ls_h: UCOS2_Verify_State)  (ls_r: UCOS2_Verify_State)  (ls_d: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (prio_v > pcp_idx) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_v) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_o)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (OutsideCritical sg ls_h )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h ))
  ||
  (EX (e_h: OSEventAbstractState)  (cnt_h: Z)  (ptr_h: Z)  (grp_h: Z)  (tbl_o: (@list Z))  (canonical_waiter: Z)  (table_owner: Z)  (ls_h: UCOS2_Verify_State)  (ls_r: UCOS2_Verify_State)  (ls_d: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (pcp_idx = 255) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_v) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_o)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (OutsideCritical sg ls_h )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h ))
.

Definition OSMutexPost_full_entail_wit_13 := 
(
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls2: UCOS2_Verify_State) (ls_d_2: UCOS2_Verify_State) (pcp_v: Z) (PreH1 : ((unsigned_last_nbits (egrp_in) (32)) = 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH3 : (pevent0 = (event_addr (sg) (eid)))) (PreH4 : (pcp_v = pcp_idx)) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d_2)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d_2) (ls2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls2.(TskState) )) ((ls2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (mutex_post_rep_no_event sg ls0 ls2 eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits (ecnt_in) (16)) 255))
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
|--
  EX (e_r: OSEventAbstractState)  (cnt_r: Z)  (ptr_r: Z)  (grp_r: Z)  (tbl_r: (@list Z))  (ls_r: UCOS2_Verify_State)  (ls_available: UCOS2_Verify_State)  (ls_reserved: UCOS2_Verify_State)  (ls_d: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_reserved)) )
  **  (coq_prop (mutex_post_empty_count_commit_step_prop (eid) (ls_reserved) (ls_available)) )
  **  (coq_prop (mutex_post_empty_owner_commit_step_prop (eid) (ls_available) (ls_r)) )
  **  (coq_prop (mutex_post_release_step_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (crit_rel_task_event_sched (ls0) (ls_r)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e_r) (4) (cnt_r) (ptr_r) (grp_r) (tbl_r)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (InsideCritical sg ls0 )
  **  (mutex_post_rep sg ls0 ls_r )
) \/
(
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls2: UCOS2_Verify_State) (ls_d_2: UCOS2_Verify_State) (pcp_v: Z) (PreH1 : ((unsigned_last_nbits (egrp_in) (32)) = 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH3 : (pevent0 = (event_addr (sg) (eid)))) (PreH4 : (pcp_v = pcp_idx)) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d_2)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d_2) (ls2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls2.(TskState) )) ((ls2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (mutex_post_rep_no_event sg ls0 ls2 eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits (ecnt_in) (16)) 255))
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
|--
  EX (e_r: OSEventAbstractState)  (cnt_r: Z)  (ptr_r: Z)  (grp_r: Z)  (tbl_r: (@list Z))  (ls_r: UCOS2_Verify_State)  (ls_available: UCOS2_Verify_State)  (ls_reserved: UCOS2_Verify_State)  (ls_d: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ”
  &&  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_reserved)) )
  **  (coq_prop (mutex_post_empty_count_commit_step_prop (eid) (ls_reserved) (ls_available)) )
  **  (coq_prop (mutex_post_empty_owner_commit_step_prop (eid) (ls_available) (ls_r)) )
  **  (coq_prop (mutex_post_release_step_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (crit_rel_task_event_sched (ls0) (ls_r)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e_r) (4) (cnt_r) (ptr_r) (grp_r) (tbl_r)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (InsideCritical sg ls0 )
  **  (mutex_post_rep sg ls0 ls_r )
).

Definition OSMutexPost_full_return_wit_1 := 
(
forall (pcp_idx: Z) (ecnt_in: Z) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_r: UCOS2_Verify_State) (ls_available: UCOS2_Verify_State) (ls_reserved: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State) (e_r: OSEventAbstractState) (pcp_v: Z) (cnt_r: Z) (ptr_r: Z) (grp_r: Z) (tbl_r: (@list Z)) (PreH1 : (GTrans_C sg ls0 sg ls_r )) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH3 : (pevent0 = (event_addr (sg) (eid)))) (PreH4 : (pcp_v = pcp_idx)) ,
  (OutsideCritical sg ls_r )
  **  (coq_prop (crit_rel_task_event_sched (ls0) (ls_r)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_reserved)) )
  **  (coq_prop (mutex_post_empty_count_commit_step_prop (eid) (ls_reserved) (ls_available)) )
  **  (coq_prop (mutex_post_empty_owner_commit_step_prop (eid) (ls_available) (ls_r)) )
  **  (coq_prop (mutex_post_release_step_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e_r) (4) (cnt_r) (ptr_r) (grp_r) (tbl_r)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (mutex_post_rep sg ls0 ls_r )
|--
  EX (ls_post: UCOS2_Verify_State)  (err: OSErrCode) ,
  “ (safeExec (OSMutexPost_LastSeen (sg) (pevent0) (ls0) (err) (ls_post)) (return ((encode_os_err_code (err)))) X ) ” 
  &&  “ (0 = (encode_os_err_code (err))) ”
  &&  (OutsideCritical sg ls_post )
  **  (mutex_post_rep sg ls0 ls_post )
  **  (coq_prop (mutex_post_result_prop (sg) (pevent0) (ls0) (ls_post) (0)) )
  **  (coq_prop (mutex_post_conditional_validity_prop (sg) (pevent0) (ls0) (ls_post)) )
) \/
(
forall (pcp_idx: Z) (ecnt_in: Z) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_r: UCOS2_Verify_State) (ls_available: UCOS2_Verify_State) (ls_reserved: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State) (e_r: OSEventAbstractState) (pcp_v: Z) (cnt_r: Z) (ptr_r: Z) (grp_r: Z) (tbl_r: (@list Z)) (PreH1 : (GTrans_C sg ls0 sg ls_r )) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH3 : (pevent0 = (event_addr (sg) (eid)))) (PreH4 : (pcp_v = pcp_idx)) ,
  (OutsideCritical sg ls_r )
  **  (coq_prop (crit_rel_task_event_sched (ls0) (ls_r)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_reserved)) )
  **  (coq_prop (mutex_post_empty_count_commit_step_prop (eid) (ls_reserved) (ls_available)) )
  **  (coq_prop (mutex_post_empty_owner_commit_step_prop (eid) (ls_available) (ls_r)) )
  **  (coq_prop (mutex_post_release_step_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e_r) (4) (cnt_r) (ptr_r) (grp_r) (tbl_r)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (mutex_post_rep sg ls0 ls_r )
|--
  EX (ls_post: UCOS2_Verify_State)  (err: OSErrCode) ,
  “ (safeExec (OSMutexPost_LastSeen (sg) (pevent0) (ls0) (err) (ls_post)) (return ((encode_os_err_code (err)))) X ) ” 
  &&  “ (0 = (encode_os_err_code (err))) ”
  &&  (OutsideCritical sg ls_post )
  **  (mutex_post_rep sg ls0 ls_post )
  **  (coq_prop (mutex_post_result_prop (sg) (pevent0) (ls0) (ls_post) (0)) )
  **  (coq_prop (mutex_post_conditional_validity_prop (sg) (pevent0) (ls0) (ls_post)) )
).

Definition OSMutexPost_full_return_wit_2 := 
(
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_h: UCOS2_Verify_State) (ls_r: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State) (e_h: OSEventAbstractState) (canonical_waiter: Z) (table_owner: Z) (cnt_h: Z) (ptr_h: Z) (grp_h: Z) (tbl_o: (@list Z)) (pcp_o: Z) (prio_o: Z) (ls_sched: UCOS2_Verify_State) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (pcp_o = pcp_idx)) (PreH4 : (prio_o > pcp_idx)) ,
  (coq_prop (mutex_post_sched_step_prop (ls_h) (ls_sched)) )
  **  (OutsideCritical sg ls_sched )
  **  (mutex_post_rep sg ls0 ls_sched )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_o) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_o)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  EX (ls_post: UCOS2_Verify_State)  (err: OSErrCode) ,
  “ (safeExec (OSMutexPost_LastSeen (sg) (pevent0) (ls0) (err) (ls_post)) (return ((encode_os_err_code (err)))) X ) ” 
  &&  “ (0 = (encode_os_err_code (err))) ”
  &&  (OutsideCritical sg ls_post )
  **  (mutex_post_rep sg ls0 ls_post )
  **  (coq_prop (mutex_post_result_prop (sg) (pevent0) (ls0) (ls_post) (0)) )
  **  (coq_prop (mutex_post_conditional_validity_prop (sg) (pevent0) (ls0) (ls_post)) )
) \/
(
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_h: UCOS2_Verify_State) (ls_r: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State) (e_h: OSEventAbstractState) (canonical_waiter: Z) (table_owner: Z) (cnt_h: Z) (ptr_h: Z) (grp_h: Z) (tbl_o: (@list Z)) (pcp_o: Z) (prio_o: Z) (ls_sched: UCOS2_Verify_State) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (pcp_o = pcp_idx)) (PreH4 : (prio_o > pcp_idx)) ,
  (coq_prop (mutex_post_sched_step_prop (ls_h) (ls_sched)) )
  **  (OutsideCritical sg ls_sched )
  **  (mutex_post_rep sg ls0 ls_sched )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_o) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_o)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  EX (ls_post: UCOS2_Verify_State)  (err: OSErrCode) ,
  “ (safeExec (OSMutexPost_LastSeen (sg) (pevent0) (ls0) (err) (ls_post)) (return ((encode_os_err_code (err)))) X ) ” 
  &&  “ (0 = (encode_os_err_code (err))) ”
  &&  (OutsideCritical sg ls_post )
  **  (mutex_post_rep sg ls0 ls_post )
  **  (coq_prop (mutex_post_result_prop (sg) (pevent0) (ls0) (ls_post) (0)) )
  **  (coq_prop (mutex_post_conditional_validity_prop (sg) (pevent0) (ls0) (ls_post)) )
).

Definition OSMutexPost_full_return_wit_3 := 
(
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_h: UCOS2_Verify_State) (ls_r: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State) (e_h: OSEventAbstractState) (canonical_waiter: Z) (table_owner: Z) (cnt_h: Z) (ptr_h: Z) (grp_h: Z) (tbl_o: (@list Z)) (pcp_o: Z) (prio_o: Z) (ls_sched: UCOS2_Verify_State) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (pcp_o = pcp_idx)) (PreH4 : (pcp_idx = 255)) ,
  (coq_prop (mutex_post_sched_step_prop (ls_h) (ls_sched)) )
  **  (OutsideCritical sg ls_sched )
  **  (mutex_post_rep sg ls0 ls_sched )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_o) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_o)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  EX (ls_post: UCOS2_Verify_State)  (err: OSErrCode) ,
  “ (safeExec (OSMutexPost_LastSeen (sg) (pevent0) (ls0) (err) (ls_post)) (return ((encode_os_err_code (err)))) X ) ” 
  &&  “ (0 = (encode_os_err_code (err))) ”
  &&  (OutsideCritical sg ls_post )
  **  (mutex_post_rep sg ls0 ls_post )
  **  (coq_prop (mutex_post_result_prop (sg) (pevent0) (ls0) (ls_post) (0)) )
  **  (coq_prop (mutex_post_conditional_validity_prop (sg) (pevent0) (ls0) (ls_post)) )
) \/
(
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_h: UCOS2_Verify_State) (ls_r: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State) (e_h: OSEventAbstractState) (canonical_waiter: Z) (table_owner: Z) (cnt_h: Z) (ptr_h: Z) (grp_h: Z) (tbl_o: (@list Z)) (pcp_o: Z) (prio_o: Z) (ls_sched: UCOS2_Verify_State) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (pcp_o = pcp_idx)) (PreH4 : (pcp_idx = 255)) ,
  (coq_prop (mutex_post_sched_step_prop (ls_h) (ls_sched)) )
  **  (OutsideCritical sg ls_sched )
  **  (mutex_post_rep sg ls0 ls_sched )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_o) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_o)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  EX (ls_post: UCOS2_Verify_State)  (err: OSErrCode) ,
  “ (safeExec (OSMutexPost_LastSeen (sg) (pevent0) (ls0) (err) (ls_post)) (return ((encode_os_err_code (err)))) X ) ” 
  &&  “ (0 = (encode_os_err_code (err))) ”
  &&  (OutsideCritical sg ls_post )
  **  (mutex_post_rep sg ls0 ls_post )
  **  (coq_prop (mutex_post_result_prop (sg) (pevent0) (ls0) (ls_post) (0)) )
  **  (coq_prop (mutex_post_conditional_validity_prop (sg) (pevent0) (ls0) (ls_post)) )
).

Definition OSMutexPost_full_return_wit_4 := 
(
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_h: UCOS2_Verify_State) (ls_r: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State) (e_h: OSEventAbstractState) (canonical_waiter: Z) (table_owner: Z) (cnt_h: Z) (ptr_h: Z) (grp_h: Z) (tbl_o: (@list Z)) (pcp_o: Z) (prio_o: Z) (ls_sched: UCOS2_Verify_State) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (pcp_o = pcp_idx)) (PreH4 : (pcp_idx <> 255)) (PreH5 : (prio_o <= pcp_idx)) ,
  (coq_prop (mutex_post_sched_step_prop (ls_h) (ls_sched)) )
  **  (OutsideCritical sg ls_sched )
  **  (mutex_post_rep sg ls0 ls_sched )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_o) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_o)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  EX (ls_post: UCOS2_Verify_State)  (err: OSErrCode) ,
  “ (safeExec (OSMutexPost_LastSeen (sg) (pevent0) (ls0) (err) (ls_post)) (return ((encode_os_err_code (err)))) X ) ” 
  &&  “ (120 = (encode_os_err_code (err))) ”
  &&  (OutsideCritical sg ls_post )
  **  (mutex_post_rep sg ls0 ls_post )
  **  (coq_prop (mutex_post_result_prop (sg) (pevent0) (ls0) (ls_post) (120)) )
  **  (coq_prop (mutex_post_conditional_validity_prop (sg) (pevent0) (ls0) (ls_post)) )
) \/
(
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_h: UCOS2_Verify_State) (ls_r: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State) (e_h: OSEventAbstractState) (canonical_waiter: Z) (table_owner: Z) (cnt_h: Z) (ptr_h: Z) (grp_h: Z) (tbl_o: (@list Z)) (pcp_o: Z) (prio_o: Z) (ls_sched: UCOS2_Verify_State) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (pcp_o = pcp_idx)) (PreH4 : (pcp_idx <> 255)) (PreH5 : (prio_o <= pcp_idx)) ,
  (coq_prop (mutex_post_sched_step_prop (ls_h) (ls_sched)) )
  **  (OutsideCritical sg ls_sched )
  **  (mutex_post_rep sg ls0 ls_sched )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_o) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_o)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  EX (ls_post: UCOS2_Verify_State)  (err: OSErrCode) ,
  “ (safeExec (OSMutexPost_LastSeen (sg) (pevent0) (ls0) (err) (ls_post)) (return ((encode_os_err_code (err)))) X ) ” 
  &&  “ (120 = (encode_os_err_code (err))) ”
  &&  (OutsideCritical sg ls_post )
  **  (mutex_post_rep sg ls0 ls_post )
  **  (coq_prop (mutex_post_result_prop (sg) (pevent0) (ls0) (ls_post) (120)) )
  **  (coq_prop (mutex_post_conditional_validity_prop (sg) (pevent0) (ls0) (ls_post)) )
).

Definition OSMutexPost_full_return_wit_5 := 
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (pcp_v: Z) (prio_v: Z) (PreH1 : (GTrans_C sg ls1 sg ls0 )) (PreH2 : (tcbcur <> owner_ptr)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH4 : (pevent0 = (event_addr (sg) (eid)))) (PreH5 : (tcbcur <> 0)) (PreH6 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH7 : (pcp_v = pcp_idx)) (PreH8 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH9 : (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in)))) ,
  (OutsideCritical sg ls0 )
  **  (coq_prop (crit_rel_task_event_sched (ls1) (ls0)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls1.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls1.(TskState) ) (ls1.(SchedState) ) )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (tick_inv sg (ls1.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls1)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls1.(TskState) )) ((ls1.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls1.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls1.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1.(TskState) )) (prioL_in)) )
|--
  EX (ls_post: UCOS2_Verify_State)  (err: OSErrCode) ,
  “ (safeExec (OSMutexPost_LastSeen (sg) (pevent0) (ls0) (err) (ls_post)) (return ((encode_os_err_code (err)))) X ) ” 
  &&  “ (100 = (encode_os_err_code (err))) ”
  &&  (OutsideCritical sg ls_post )
  **  (mutex_post_rep sg ls0 ls_post )
  **  (coq_prop (mutex_post_result_prop (sg) (pevent0) (ls0) (ls_post) (100)) )
  **  (coq_prop (mutex_post_conditional_validity_prop (sg) (pevent0) (ls0) (ls_post)) )
) \/
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (pcp_v: Z) (prio_v: Z) (PreH1 : (GTrans_C sg ls1 sg ls0 )) (PreH2 : (tcbcur <> owner_ptr)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH4 : (pevent0 = (event_addr (sg) (eid)))) (PreH5 : (tcbcur <> 0)) (PreH6 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH7 : (pcp_v = pcp_idx)) (PreH8 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH9 : (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in)))) ,
  (OutsideCritical sg ls0 )
  **  (coq_prop (crit_rel_task_event_sched (ls1) (ls0)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls1.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls1.(TskState) ) (ls1.(SchedState) ) )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (tick_inv sg (ls1.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls1)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls1.(TskState) )) ((ls1.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls1.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls1.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1.(TskState) )) (prioL_in)) )
|--
  EX (ls_post: UCOS2_Verify_State)  (err: OSErrCode) ,
  “ (safeExec (OSMutexPost_LastSeen (sg) (pevent0) (ls0) (err) (ls_post)) (return ((encode_os_err_code (err)))) X ) ” 
  &&  “ (100 = (encode_os_err_code (err))) ”
  &&  (OutsideCritical sg ls_post )
  **  (mutex_post_rep sg ls0 ls_post )
  **  (coq_prop (mutex_post_result_prop (sg) (pevent0) (ls0) (ls_post) (100)) )
  **  (coq_prop (mutex_post_conditional_validity_prop (sg) (pevent0) (ls0) (ls_post)) )
).

Definition OSMutexPost_full_return_wit_6 := 
(
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) <> 4)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (pevent_pre <> 0)) (PreH4 : (isr <= 0)) (PreH5 : (0 <= isr)) (PreH6 : (isr <= 255)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (pevent_pre = pevent0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH13 : (isr <= 0)) (PreH14 : (pevent0 <> 0)) (PreH15 : (pevent0 = (event_addr (sg) (eid)))) ,
  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (ls_post: UCOS2_Verify_State)  (err: OSErrCode) ,
  “ (safeExec (OSMutexPost_LastSeen (sg) (pevent0) (ls0) (err) (ls_post)) (return ((encode_os_err_code (err)))) X ) ” 
  &&  “ (1 = (encode_os_err_code (err))) ”
  &&  (OutsideCritical sg ls_post )
  **  (mutex_post_rep sg ls0 ls_post )
  **  (coq_prop (mutex_post_result_prop (sg) (pevent0) (ls0) (ls_post) (1)) )
  **  (coq_prop (mutex_post_conditional_validity_prop (sg) (pevent0) (ls0) (ls_post)) )
) \/
(
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) <> 4)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (pevent_pre <> 0)) (PreH4 : (isr <= 0)) (PreH5 : (0 <= isr)) (PreH6 : (isr <= 255)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (pevent_pre = pevent0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH13 : (isr <= 0)) (PreH14 : (pevent0 <> 0)) (PreH15 : (pevent0 = (event_addr (sg) (eid)))) ,
  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (ls_post: UCOS2_Verify_State)  (err: OSErrCode) ,
  “ (safeExec (OSMutexPost_LastSeen (sg) (pevent0) (ls0) (err) (ls_post)) (return ((encode_os_err_code (err)))) X ) ” 
  &&  “ (1 = (encode_os_err_code (err))) ”
  &&  (OutsideCritical sg ls_post )
  **  (mutex_post_rep sg ls0 ls_post )
  **  (coq_prop (mutex_post_result_prop (sg) (pevent0) (ls0) (ls_post) (1)) )
  **  (coq_prop (mutex_post_conditional_validity_prop (sg) (pevent0) (ls0) (ls_post)) )
).

Definition OSMutexPost_full_return_wit_7 := 
(
forall (pevent_pre: Z) (isr: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre = 0)) (PreH2 : (isr <= 0)) (PreH3 : (0 <= isr)) (PreH4 : (isr <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (pevent_pre = pevent0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH11 : (isr <= 0)) (PreH12 : (pevent0 = 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (ls_post: UCOS2_Verify_State)  (err: OSErrCode) ,
  “ (safeExec (OSMutexPost_LastSeen (sg) (pevent0) (ls0) (err) (ls_post)) (return ((encode_os_err_code (err)))) X ) ” 
  &&  “ (4 = (encode_os_err_code (err))) ”
  &&  (OutsideCritical sg ls_post )
  **  (mutex_post_rep sg ls0 ls_post )
  **  (coq_prop (mutex_post_result_prop (sg) (pevent0) (ls0) (ls_post) (4)) )
  **  (coq_prop (mutex_post_conditional_validity_prop (sg) (pevent0) (ls0) (ls_post)) )
) \/
(
forall (pevent_pre: Z) (isr: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre = 0)) (PreH2 : (isr <= 0)) (PreH3 : (0 <= isr)) (PreH4 : (isr <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (pevent_pre = pevent0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH11 : (isr <= 0)) (PreH12 : (pevent0 = 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (ls_post: UCOS2_Verify_State)  (err: OSErrCode) ,
  “ (safeExec (OSMutexPost_LastSeen (sg) (pevent0) (ls0) (err) (ls_post)) (return ((encode_os_err_code (err)))) X ) ” 
  &&  “ (4 = (encode_os_err_code (err))) ”
  &&  (OutsideCritical sg ls_post )
  **  (mutex_post_rep sg ls0 ls_post )
  **  (coq_prop (mutex_post_result_prop (sg) (pevent0) (ls0) (ls_post) (4)) )
  **  (coq_prop (mutex_post_conditional_validity_prop (sg) (pevent0) (ls0) (ls_post)) )
).

Definition OSMutexPost_full_return_wit_8 := 
(
forall (pevent_pre: Z) (isr: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr > 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (pevent_pre = pevent0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH10 : (isr > 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (ls_post: UCOS2_Verify_State)  (err: OSErrCode) ,
  “ (safeExec (OSMutexPost_LastSeen (sg) (pevent0) (ls0) (err) (ls_post)) (return ((encode_os_err_code (err)))) X ) ” 
  &&  “ (5 = (encode_os_err_code (err))) ”
  &&  (OutsideCritical sg ls_post )
  **  (mutex_post_rep sg ls0 ls_post )
  **  (coq_prop (mutex_post_result_prop (sg) (pevent0) (ls0) (ls_post) (5)) )
  **  (coq_prop (mutex_post_conditional_validity_prop (sg) (pevent0) (ls0) (ls_post)) )
) \/
(
forall (pevent_pre: Z) (isr: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr > 0)) (PreH2 : (0 <= isr)) (PreH3 : (isr <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (pevent_pre = pevent0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH10 : (isr > 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (ls_post: UCOS2_Verify_State)  (err: OSErrCode) ,
  “ (safeExec (OSMutexPost_LastSeen (sg) (pevent0) (ls0) (err) (ls_post)) (return ((encode_os_err_code (err)))) X ) ” 
  &&  “ (5 = (encode_os_err_code (err))) ”
  &&  (OutsideCritical sg ls_post )
  **  (mutex_post_rep sg ls0 ls_post )
  **  (coq_prop (mutex_post_result_prop (sg) (pevent0) (ls0) (ls_post) (5)) )
  **  (coq_prop (mutex_post_conditional_validity_prop (sg) (pevent0) (ls0) (ls_post)) )
).

Definition OSMutexPost_full_partial_solve_wit_1_pure := 
forall (pevent_pre: Z) (isr: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre = pevent0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH4 : (isr > 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
.

Definition OSMutexPost_full_partial_solve_wit_1_aux := 
forall (pevent_pre: Z) (isr: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre = pevent0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH4 : (isr > 0)) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pevent_pre = pevent0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (isr > 0) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
.

Definition OSMutexPost_full_partial_solve_wit_1 := OSMutexPost_full_partial_solve_wit_1_pure -> OSMutexPost_full_partial_solve_wit_1_aux.

Definition OSMutexPost_full_partial_solve_wit_2_pure := 
forall (pevent_pre: Z) (isr: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre = pevent0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH4 : (isr <= 0)) (PreH5 : (pevent0 = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
.

Definition OSMutexPost_full_partial_solve_wit_2_aux := 
forall (pevent_pre: Z) (isr: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre = pevent0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH4 : (isr <= 0)) (PreH5 : (pevent0 = 0)) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pevent_pre = pevent0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent0 = 0) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
.

Definition OSMutexPost_full_partial_solve_wit_2 := OSMutexPost_full_partial_solve_wit_2_pure -> OSMutexPost_full_partial_solve_wit_2_aux.

Definition OSMutexPost_full_partial_solve_wit_3_pure := 
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre = pevent0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH4 : (isr <= 0)) (PreH5 : (pevent0 <> 0)) (PreH6 : (pevent0 = (event_addr (sg) (eid)))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
.

Definition OSMutexPost_full_partial_solve_wit_3_aux := 
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre = pevent0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH4 : (isr <= 0)) (PreH5 : (pevent0 <> 0)) (PreH6 : (pevent0 = (event_addr (sg) (eid)))) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pevent_pre = pevent0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent0 <> 0) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
.

Definition OSMutexPost_full_partial_solve_wit_3 := OSMutexPost_full_partial_solve_wit_3_pure -> OSMutexPost_full_partial_solve_wit_3_aux.

Definition OSMutexPost_full_partial_solve_wit_4_pure := 
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre <> 0)) (PreH2 : (isr <= 0)) (PreH3 : (0 <= isr)) (PreH4 : (isr <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (pevent_pre = pevent0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH11 : (isr <= 0)) (PreH12 : (pevent0 <> 0)) (PreH13 : (pevent0 = (event_addr (sg) (eid)))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
.

Definition OSMutexPost_full_partial_solve_wit_4_aux := 
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre <> 0)) (PreH2 : (isr <= 0)) (PreH3 : (0 <= isr)) (PreH4 : (isr <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (pevent_pre = pevent0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH11 : (isr <= 0)) (PreH12 : (pevent0 <> 0)) (PreH13 : (pevent0 = (event_addr (sg) (eid)))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pevent_pre = pevent0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent0 <> 0) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
.

Definition OSMutexPost_full_partial_solve_wit_4 := OSMutexPost_full_partial_solve_wit_4_pure -> OSMutexPost_full_partial_solve_wit_4_aux.

Definition OSMutexPost_full_partial_solve_wit_5 := 
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (pevent_pre <> 0)) (PreH3 : (isr <= 0)) (PreH4 : (0 <= isr)) (PreH5 : (isr <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (pevent_pre = pevent0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH12 : (isr <= 0)) (PreH13 : (pevent0 <> 0)) (PreH14 : (pevent0 = (event_addr (sg) (eid)))) ,
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pevent_pre = pevent0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent0 <> 0) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
.

Definition OSMutexPost_full_partial_solve_wit_6 := 
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (pevent_pre <> 0)) (PreH3 : (isr <= 0)) (PreH4 : (0 <= isr)) (PreH5 : (isr <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (pevent_pre = pevent0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH12 : (isr <= 0)) (PreH13 : (pevent0 <> 0)) (PreH14 : (pevent0 = (event_addr (sg) (eid)))) ,
  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((ls0.(EventState) )) (eid)))
  **  (UCOS2_Verify_inv_no_event_type sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pevent_pre = pevent0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent0 <> 0) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ”
  &&  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((ls0.(EventState) )) (eid)))
  **  (UCOS2_Verify_inv_no_event_type sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
.

Definition OSMutexPost_full_partial_solve_wit_7 := 
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) <> 4)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (pevent_pre <> 0)) (PreH4 : (isr <= 0)) (PreH5 : (0 <= isr)) (PreH6 : (isr <= 255)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (pevent_pre = pevent0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH13 : (isr <= 0)) (PreH14 : (pevent0 <> 0)) (PreH15 : (pevent0 = (event_addr (sg) (eid)))) ,
  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((ls0.(EventState) )) (eid)))
  **  (UCOS2_Verify_inv_no_event_type sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) <> 4) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pevent_pre = pevent0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent0 <> 0) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((ls0.(EventState) )) (eid)))
  **  (UCOS2_Verify_inv_no_event_type sg ls0 eid )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
.

Definition OSMutexPost_full_partial_solve_wit_8 := 
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) = 4)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (pevent_pre <> 0)) (PreH4 : (isr <= 0)) (PreH5 : (0 <= isr)) (PreH6 : (isr <= 255)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (pevent_pre = pevent0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH13 : (isr <= 0)) (PreH14 : (pevent0 <> 0)) (PreH15 : (pevent0 = (event_addr (sg) (eid)))) ,
  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((ls0.(EventState) )) (eid)))
  **  (UCOS2_Verify_inv_no_event_type sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) = 4) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pevent_pre = pevent0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent0 <> 0) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((ls0.(EventState) )) (eid)))
  **  (UCOS2_Verify_inv_no_event_type sg ls0 eid )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
.

Definition OSMutexPost_full_partial_solve_wit_9_pure := 
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) = 4)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (pevent_pre <> 0)) (PreH4 : (isr <= 0)) (PreH5 : (0 <= isr)) (PreH6 : (isr <= 255)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (pevent_pre = pevent0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH13 : (isr <= 0)) (PreH14 : (pevent0 <> 0)) (PreH15 : (pevent0 = (event_addr (sg) (eid)))) ,
  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) = 4) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ”
.

Definition OSMutexPost_full_partial_solve_wit_9_aux := 
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) = 4)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (pevent_pre <> 0)) (PreH4 : (isr <= 0)) (PreH5 : (0 <= isr)) (PreH6 : (isr <= 255)) (PreH7 : (0 <= UINT_MAX)) (PreH8 : (0 >= 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (pevent_pre = pevent0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH13 : (isr <= 0)) (PreH14 : (pevent0 <> 0)) (PreH15 : (pevent0 = (event_addr (sg) (eid)))) ,
  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) = 4) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) = 4) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pevent_pre = pevent0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent0 <> 0) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ”
  &&  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_pre) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
.

Definition OSMutexPost_full_partial_solve_wit_9 := OSMutexPost_full_partial_solve_wit_9_pure -> OSMutexPost_full_partial_solve_wit_9_aux.

Definition OSMutexPost_full_partial_solve_wit_10 := 
forall (pevent_pre: Z) (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype = 4)) (PreH2 : (tcbcur <> 0)) (PreH3 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH4 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH5 : ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) = 4)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (pevent_pre <> 0)) (PreH8 : (isr <= 0)) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (pevent_pre = pevent0)) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH17 : (isr <= 0)) (PreH18 : (pevent0 <> 0)) (PreH19 : (pevent0 = (event_addr (sg) (eid)))) ,
  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (etype = 4) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ (pcp_idx = (decode_PCP_from_cnt (ecnt_in))) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ” 
  &&  “ ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) = 4) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pevent_pre = pevent0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent0 <> 0) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ”
  &&  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
.

Definition OSMutexPost_full_partial_solve_wit_11 := 
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent0 = (event_addr (sg) (eid)))) (PreH2 : (etype = 4)) (PreH3 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH4 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH5 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) ,
  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (pcp_idx = (decode_PCP_from_cnt (ecnt_in))) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ”
  &&  (OutsideCritical sg ls0 )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
.

Definition OSMutexPost_full_partial_solve_wit_12 := 
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (pcp_v: Z) (prio_v: Z) (PreH1 : (tcbcur <> owner_ptr)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH3 : (pevent0 = (event_addr (sg) (eid)))) (PreH4 : (tcbcur <> 0)) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (pcp_v = pcp_idx)) (PreH7 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH8 : (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in)))) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (InsideCritical sg ls1 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls1.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls1.(TskState) ) (ls1.(SchedState) ) )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (tick_inv sg (ls1.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls1)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls1.(TskState) )) ((ls1.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls1.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls1.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1.(TskState) )) (prioL_in)) )
|--
  “ (tcbcur <> owner_ptr) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (pcp_v = (decode_PCP_from_cnt (ecnt_in))) ” 
  &&  “ (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in))) ”
  &&  (InsideCritical sg ls1 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls1.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls1.(TskState) ) (ls1.(SchedState) ) )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (tick_inv sg (ls1.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls1)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls1.(TskState) )) ((ls1.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls1.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls1.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1.(TskState) )) (prioL_in)) )
.

Definition OSMutexPost_full_partial_solve_wit_13 := 
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (pcp_v: Z) (prio_v: Z) (PreH1 : (tcbcur <> owner_ptr)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH3 : (pevent0 = (event_addr (sg) (eid)))) (PreH4 : (tcbcur <> 0)) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (pcp_v = pcp_idx)) (PreH7 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH8 : (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in)))) ,
  (InsideCritical sg ls1 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (crit_rel_task_event_sched (ls1) (ls0)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls1.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls1.(TskState) ) (ls1.(SchedState) ) )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (tick_inv sg (ls1.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls1)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls1.(TskState) )) ((ls1.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls1.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls1.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1.(TskState) )) (prioL_in)) )
|--
  “ (tcbcur <> owner_ptr) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (pcp_v = (decode_PCP_from_cnt (ecnt_in))) ” 
  &&  “ (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in))) ”
  &&  (InsideCritical sg ls1 )
  **  (coq_prop (crit_rel_task_event_sched (ls1) (ls0)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (mutex_post_checked_entry_prop (ls0) (pevent0)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls1.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls1.(TskState) ) (ls1.(SchedState) ) )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (tick_inv sg (ls1.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls1)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls1.(TskState) )) ((ls1.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls1.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls1.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1.(TskState) )) (prioL_in)) )
.

Definition OSMutexPost_full_partial_solve_wit_14_pure := 
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_rdy_pre: UCOS2_Verify_State) (Xrdy: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (cpu_sr_v: Z) (pcp_v: Z) (prio_v: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH2 : (safeExec (LastSeen (ls_rdy_pre)) (bind ((OSMutexPost_RdyAtPrio_atomic_cmd (sg) (ls_rdy_pre) (tcbcur) (prio_v))) (observe_unit_void)) Xrdy )) (PreH3 : (pcp_v = pcp_idx)) (PreH4 : (pcp_idx <> 255)) (PreH5 : (tcbprio = pcp_idx)) (PreH6 : (owner_ptr = tcbcur)) (PreH7 : (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in)))) (PreH8 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_entry_context_prop (sg) (pevent0) (eid) (ls0) (ls_rdy_pre) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (tcbcur) (pcp_idx)) )
  **  (InsideCritical sg ls_rdy_pre )
  **  (interrupt_inv sg (ls_rdy_pre.(IntrState) ) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls_rdy_pre.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls_rdy_pre.(TskState) ) (ls_rdy_pre.(SchedState) ) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent0)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (event_inv_no_eid sg (ls_rdy_pre.(TskState) ) (ls_rdy_pre.(EventState) ) eid )
  **  (tick_inv sg (ls_rdy_pre.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls_rdy_pre)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |-> prio_v)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_rdy_pre.(TskState) )) ((ls_rdy_pre.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_rdy_pre.(TskState) )) (prioL_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls_rdy_pre.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
|--
  “ (safeExec (LastSeen (ls_rdy_pre)) (bind ((OSMutexPost_RdyAtPrio_atomic_cmd (sg) (ls_rdy_pre) (tcbcur) (prio_v))) (observe_unit_void)) Xrdy ) ”
.

Definition OSMutexPost_full_partial_solve_wit_14_aux := 
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_rdy_pre: UCOS2_Verify_State) (Xrdy: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (pcp_v: Z) (prio_v: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH2 : (safeExec (LastSeen (ls_rdy_pre)) (bind ((OSMutexPost_RdyAtPrio_atomic_cmd (sg) (ls_rdy_pre) (tcbcur) (prio_v))) (observe_unit_void)) Xrdy )) (PreH3 : (pcp_v = pcp_idx)) (PreH4 : (pcp_idx <> 255)) (PreH5 : (tcbprio = pcp_idx)) (PreH6 : (owner_ptr = tcbcur)) (PreH7 : (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in)))) (PreH8 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_entry_context_prop (sg) (pevent0) (eid) (ls0) (ls_rdy_pre) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (tcbcur) (pcp_idx)) )
  **  (InsideCritical sg ls_rdy_pre )
  **  (interrupt_inv sg (ls_rdy_pre.(IntrState) ) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls_rdy_pre.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls_rdy_pre.(TskState) ) (ls_rdy_pre.(SchedState) ) )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (event_inv_no_eid sg (ls_rdy_pre.(TskState) ) (ls_rdy_pre.(EventState) ) eid )
  **  (tick_inv sg (ls_rdy_pre.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls_rdy_pre)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_rdy_pre.(TskState) )) ((ls_rdy_pre.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_rdy_pre.(TskState) )) (prioL_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls_rdy_pre.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
|--
  “ (safeExec (LastSeen (ls_rdy_pre)) (bind ((OSMutexPost_RdyAtPrio_atomic_cmd (sg) (ls_rdy_pre) (tcbcur) (prio_v))) (observe_unit_void)) Xrdy ) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (safeExec (LastSeen (ls_rdy_pre)) (bind ((OSMutexPost_RdyAtPrio_atomic_cmd (sg) (ls_rdy_pre) (tcbcur) (prio_v))) (observe_unit_void)) Xrdy ) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (pcp_idx <> 255) ” 
  &&  “ (tcbprio = pcp_idx) ” 
  &&  “ (owner_ptr = tcbcur) ” 
  &&  “ (prio_v = (decode_OwnerPrio_from_cnt (ecnt_in))) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ”
  &&  (coq_prop (mutex_post_owner_entry_context_prop (sg) (pevent0) (eid) (ls0) (ls_rdy_pre) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls_rdy_pre.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_rdy_pre.(TskState) )) ((ls_rdy_pre.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_rdy_pre.(TskState) )) (prioL_in)) )
  **  (InsideCritical sg ls_rdy_pre )
  **  (interrupt_inv sg (ls_rdy_pre.(IntrState) ) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid_priotbl sg (ls_rdy_pre.(TskState) ) cur_tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls_rdy_pre.(TskState) ) (ls_rdy_pre.(SchedState) ) )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (event_inv_no_eid sg (ls_rdy_pre.(TskState) ) (ls_rdy_pre.(EventState) ) eid )
  **  (tick_inv sg (ls_rdy_pre.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls_rdy_pre)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
.

Definition OSMutexPost_full_partial_solve_wit_14 := OSMutexPost_full_partial_solve_wit_14_pure -> OSMutexPost_full_partial_solve_wit_14_aux.

Definition OSMutexPost_full_partial_solve_wit_15_pure := 
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_d: UCOS2_Verify_State) (prioL_d: (@list Z)) (cpu_sr_v: Z) (pcp_v: Z) (prio_v: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (pcp_v = pcp_idx)) (PreH4 : (pcp_idx <> 255)) (PreH5 : (0 <= pcp_idx)) (PreH6 : (pcp_idx < 64)) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_d.(TskState) )) (prioL_d)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_d.(TskState) )) ((ls_d.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent0)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (store_priotbl_list sg prioL_d )
  **  (mutex_post_rep_no_priotbl_no_event sg ls0 ls_d eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |-> prio_v)
|--
  “ (pcp_idx <> 255) ” 
  &&  “ (0 <= pcp_idx) ” 
  &&  “ (pcp_idx < 64) ”
.

Definition OSMutexPost_full_partial_solve_wit_15_aux := 
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_d: UCOS2_Verify_State) (prioL_d: (@list Z)) (pcp_v: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (pcp_v = pcp_idx)) (PreH4 : (pcp_idx <> 255)) (PreH5 : (0 <= pcp_idx)) (PreH6 : (pcp_idx < 64)) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_d.(TskState) )) (prioL_d)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_d.(TskState) )) ((ls_d.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (store_priotbl_list sg prioL_d )
  **  (mutex_post_rep_no_priotbl_no_event sg ls0 ls_d eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
|--
  “ (pcp_idx <> 255) ” 
  &&  “ (0 <= pcp_idx) ” 
  &&  “ (pcp_idx < 64) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (pcp_idx <> 255) ” 
  &&  “ (0 <= pcp_idx) ” 
  &&  “ (pcp_idx < 64) ”
  &&  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_idx)
  **  (store_priotbl_list sg prioL_d )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_d.(TskState) )) (prioL_d)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_d.(TskState) )) ((ls_d.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (mutex_post_rep_no_priotbl_no_event sg ls0 ls_d eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
.

Definition OSMutexPost_full_partial_solve_wit_15 := OSMutexPost_full_partial_solve_wit_15_pure -> OSMutexPost_full_partial_solve_wit_15_aux.

Definition OSMutexPost_full_partial_solve_wit_16_pure := 
(
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls2: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State) (cpu_sr_v: Z) (pcp_v: Z) (prio_v: Z) (PreH1 : ((unsigned_last_nbits (egrp_in) (32)) <> 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH3 : (pevent0 = (event_addr (sg) (eid)))) (PreH4 : (pcp_v = pcp_idx)) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls2.(TskState) )) ((ls2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent0)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (mutex_post_rep_no_event sg ls0 ls2 eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |-> prio_v)
|--
  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pevent0 = pevent0) ” 
  &&  “ (egrp_in <> 0) ”
) \/
(
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls2: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State) (cpu_sr_v: Z) (pcp_v: Z) (prio_v: Z) (PreH1 : (cpu_sr_v <= UINT_MAX)) (PreH2 : (cpu_sr_v >= 0)) (PreH3 : ((unsigned_last_nbits (egrp_in) (32)) <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH5 : (pevent0 = (event_addr (sg) (eid)))) (PreH6 : (pcp_v = pcp_idx)) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls2.(TskState) )) ((ls2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent0)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (mutex_post_rep_no_event sg ls0 ls2 eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |-> prio_v)
|--
  “ (egrp_in <> 0) ”
).

Definition OSMutexPost_full_partial_solve_wit_16_pure_split_goal_1 := 
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls2: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State) (cpu_sr_v: Z) (pcp_v: Z) (prio_v: Z) (PreH1 : (cpu_sr_v <= UINT_MAX)) (PreH2 : (cpu_sr_v >= 0)) (PreH3 : ((unsigned_last_nbits (egrp_in) (32)) <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH5 : (pevent0 = (event_addr (sg) (eid)))) (PreH6 : (pcp_v = pcp_idx)) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls2.(TskState) )) ((ls2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent0)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (mutex_post_rep_no_event sg ls0 ls2 eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |-> prio_v)
|--
  “ (egrp_in <> 0) ”
.

Definition OSMutexPost_full_partial_solve_wit_16_aux := 
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls2: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State) (pcp_v: Z) (PreH1 : ((unsigned_last_nbits (egrp_in) (32)) <> 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH3 : (pevent0 = (event_addr (sg) (eid)))) (PreH4 : (pcp_v = pcp_idx)) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls2)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls2.(TskState) )) ((ls2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (mutex_post_rep_no_event sg ls0 ls2 eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
|--
  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pevent0 = pevent0) ” 
  &&  “ (egrp_in <> 0) ” 
  &&  “ ((unsigned_last_nbits (egrp_in) (32)) <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ”
  &&  (InsideCritical sg ls0 )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls2)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls2.(TskState) )) ((ls2.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (mutex_post_rep_no_event sg ls0 ls2 eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
.

Definition OSMutexPost_full_partial_solve_wit_16 := OSMutexPost_full_partial_solve_wit_16_pure -> OSMutexPost_full_partial_solve_wit_16_aux.

Definition OSMutexPost_full_partial_solve_wit_17_pure := 
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_wake: UCOS2_Verify_State) (ls_cnt: UCOS2_Verify_State) (ls_r: UCOS2_Verify_State) (ls_d0: UCOS2_Verify_State) (canonical_waiter: Z) (table_owner: Z) (e_h: OSEventAbstractState) (prioL_h: (@list Z)) (cnt_h: Z) (ptr_h: Z) (egrp_h: Z) (evtL_h: (@list Z)) (cpu_sr_v: Z) (pcp_v: Z) (prio_v: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (pcp_v = pcp_idx)) (PreH4 : (0 <= prio_v)) (PreH5 : (prio_v < 64)) (PreH6 : ((Znth (prio_v) (prioL_h) (0)) = (tcb_addr (sg) (table_owner)))) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d0)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d0) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_wake_step_prop (sg) (eid) (ls_r) (prio_v) (canonical_waiter) (table_owner) (ls_wake)) )
  **  (coq_prop (mutex_post_count_commit_step_prop (eid) (prio_v) (ls_wake) (ls_cnt)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_cnt.(TskState) )) ((ls_cnt.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (egrp_h) (evtL_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (should_be_equal (((ls_cnt.(TskState) ).(prioTbl) (prio_v))) ((PTTask (table_owner)))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_cnt.(TskState) )) (prioL_h)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent0)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (mutex_post_handover_residual_no_priotbl sg ls0 ls_cnt eid )
  **  (store_priotbl_list sg prioL_h )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_h)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_h)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_h) (0)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |-> prio_v)
|--
  “ (0 <= prio_v) ” 
  &&  “ (prio_v < 64) ” 
  &&  “ ((Znth (prio_v) (prioL_h) (0)) = (tcb_addr (sg) (table_owner))) ”
.

Definition OSMutexPost_full_partial_solve_wit_17_aux := 
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_wake: UCOS2_Verify_State) (ls_cnt: UCOS2_Verify_State) (ls_r: UCOS2_Verify_State) (ls_d0: UCOS2_Verify_State) (canonical_waiter: Z) (table_owner: Z) (e_h: OSEventAbstractState) (prioL_h: (@list Z)) (cnt_h: Z) (ptr_h: Z) (egrp_h: Z) (evtL_h: (@list Z)) (pcp_v: Z) (prio_v: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (pcp_v = pcp_idx)) (PreH4 : (0 <= prio_v)) (PreH5 : (prio_v < 64)) (PreH6 : ((Znth (prio_v) (prioL_h) (0)) = (tcb_addr (sg) (table_owner)))) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d0)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d0) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_wake_step_prop (sg) (eid) (ls_r) (prio_v) (canonical_waiter) (table_owner) (ls_wake)) )
  **  (coq_prop (mutex_post_count_commit_step_prop (eid) (prio_v) (ls_wake) (ls_cnt)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_cnt.(TskState) )) ((ls_cnt.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (egrp_h) (evtL_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (should_be_equal (((ls_cnt.(TskState) ).(prioTbl) (prio_v))) ((PTTask (table_owner)))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_cnt.(TskState) )) (prioL_h)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (mutex_post_handover_residual_no_priotbl sg ls0 ls_cnt eid )
  **  (store_priotbl_list sg prioL_h )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_h)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_h)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_h) (0)))
|--
  “ (0 <= prio_v) ” 
  &&  “ (prio_v < 64) ” 
  &&  “ ((Znth (prio_v) (prioL_h) (0)) = (tcb_addr (sg) (table_owner))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ” 
  &&  “ (0 <= prio_v) ” 
  &&  “ (prio_v < 64) ” 
  &&  “ ((Znth (prio_v) (prioL_h) (0)) = (tcb_addr (sg) (table_owner))) ”
  &&  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (store_priotbl_list sg prioL_h )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d0)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d0) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_wake_step_prop (sg) (eid) (ls_r) (prio_v) (canonical_waiter) (table_owner) (ls_wake)) )
  **  (coq_prop (mutex_post_count_commit_step_prop (eid) (prio_v) (ls_wake) (ls_cnt)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_cnt.(TskState) )) ((ls_cnt.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (egrp_h) (evtL_h)) )
  **  (coq_prop (should_be_equal (((ls_cnt.(TskState) ).(prioTbl) (prio_v))) ((PTTask (table_owner)))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_cnt.(TskState) )) (prioL_h)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (InsideCritical sg ls0 )
  **  (mutex_post_handover_residual_no_priotbl sg ls0 ls_cnt eid )
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> cnt_h)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_h)
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_h) (0)))
  **  (((&((pevent0)  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_h) (0)))
.

Definition OSMutexPost_full_partial_solve_wit_17 := OSMutexPost_full_partial_solve_wit_17_pure -> OSMutexPost_full_partial_solve_wit_17_aux.

Definition OSMutexPost_full_partial_solve_wit_18 := 
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_h: UCOS2_Verify_State) (ls_cnt: UCOS2_Verify_State) (ls_wake: UCOS2_Verify_State) (ls_r: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State) (e_h: OSEventAbstractState) (canonical_waiter: Z) (table_owner: Z) (pcp_v: Z) (prio_v: Z) (cnt_h: Z) (ptr_h: Z) (grp_h: Z) (tbl_h: (@list Z)) (PreH1 : (prio_v <= pcp_v)) (PreH2 : ((unsigned_last_nbits (pcp_v) (32)) <> 255)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH4 : (pevent0 = (event_addr (sg) (eid)))) (PreH5 : (pcp_v = pcp_idx)) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_wake_step_prop (sg) (eid) (ls_r) (prio_v) (canonical_waiter) (table_owner) (ls_wake)) )
  **  (coq_prop (mutex_post_count_commit_step_prop (eid) (prio_v) (ls_wake) (ls_cnt)) )
  **  (coq_prop (mutex_post_owner_commit_step_prop (eid) (prio_v) (table_owner) (ls_cnt) (ls_h)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_v) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (crit_rel_task_event_sched (ls0) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_h)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (InsideCritical sg ls0 )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h )
|--
  “ (prio_v <= pcp_v) ” 
  &&  “ ((unsigned_last_nbits (pcp_v) (32)) <> 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ”
  &&  (InsideCritical sg ls0 )
  **  (coq_prop (crit_rel_task_event_sched (ls0) (ls_h)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_wake_step_prop (sg) (eid) (ls_r) (prio_v) (canonical_waiter) (table_owner) (ls_wake)) )
  **  (coq_prop (mutex_post_count_commit_step_prop (eid) (prio_v) (ls_wake) (ls_cnt)) )
  **  (coq_prop (mutex_post_owner_commit_step_prop (eid) (prio_v) (table_owner) (ls_cnt) (ls_h)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_v) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_h)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h )
.

Definition OSMutexPost_full_partial_solve_wit_19 := 
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_h: UCOS2_Verify_State) (ls_r: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State) (e_h: OSEventAbstractState) (canonical_waiter: Z) (table_owner: Z) (cnt_h: Z) (ptr_h: Z) (grp_h: Z) (tbl_o: (@list Z)) (pcp_o: Z) (prio_o: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (pcp_o = pcp_idx)) (PreH4 : (pcp_idx <> 255)) (PreH5 : (prio_o <= pcp_idx)) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_o) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_o)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (OutsideCritical sg ls_h )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h )
|--
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_o = pcp_idx) ” 
  &&  “ (pcp_idx <> 255) ” 
  &&  “ (prio_o <= pcp_idx) ”
  &&  (OutsideCritical sg ls_h )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_o) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_o)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSMutexPost_full_partial_solve_wit_20 := 
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_h: UCOS2_Verify_State) (ls_cnt: UCOS2_Verify_State) (ls_wake: UCOS2_Verify_State) (ls_r: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State) (e_h: OSEventAbstractState) (canonical_waiter: Z) (table_owner: Z) (pcp_v: Z) (prio_v: Z) (cnt_h: Z) (ptr_h: Z) (grp_h: Z) (tbl_h: (@list Z)) (PreH1 : ((unsigned_last_nbits (pcp_v) (32)) = 255)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH3 : (pevent0 = (event_addr (sg) (eid)))) (PreH4 : (pcp_v = pcp_idx)) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_wake_step_prop (sg) (eid) (ls_r) (prio_v) (canonical_waiter) (table_owner) (ls_wake)) )
  **  (coq_prop (mutex_post_count_commit_step_prop (eid) (prio_v) (ls_wake) (ls_cnt)) )
  **  (coq_prop (mutex_post_owner_commit_step_prop (eid) (prio_v) (table_owner) (ls_cnt) (ls_h)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_v) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (crit_rel_task_event_sched (ls0) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_h)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (InsideCritical sg ls0 )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h )
|--
  “ ((unsigned_last_nbits (pcp_v) (32)) = 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ”
  &&  (InsideCritical sg ls0 )
  **  (coq_prop (crit_rel_task_event_sched (ls0) (ls_h)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_wake_step_prop (sg) (eid) (ls_r) (prio_v) (canonical_waiter) (table_owner) (ls_wake)) )
  **  (coq_prop (mutex_post_count_commit_step_prop (eid) (prio_v) (ls_wake) (ls_cnt)) )
  **  (coq_prop (mutex_post_owner_commit_step_prop (eid) (prio_v) (table_owner) (ls_cnt) (ls_h)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_v) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_h)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h )
.

Definition OSMutexPost_full_partial_solve_wit_21 := 
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_h: UCOS2_Verify_State) (ls_cnt: UCOS2_Verify_State) (ls_wake: UCOS2_Verify_State) (ls_r: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State) (e_h: OSEventAbstractState) (canonical_waiter: Z) (table_owner: Z) (pcp_v: Z) (prio_v: Z) (cnt_h: Z) (ptr_h: Z) (grp_h: Z) (tbl_h: (@list Z)) (PreH1 : (prio_v > pcp_v)) (PreH2 : ((unsigned_last_nbits (pcp_v) (32)) <> 255)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH4 : (pevent0 = (event_addr (sg) (eid)))) (PreH5 : (pcp_v = pcp_idx)) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_wake_step_prop (sg) (eid) (ls_r) (prio_v) (canonical_waiter) (table_owner) (ls_wake)) )
  **  (coq_prop (mutex_post_count_commit_step_prop (eid) (prio_v) (ls_wake) (ls_cnt)) )
  **  (coq_prop (mutex_post_owner_commit_step_prop (eid) (prio_v) (table_owner) (ls_cnt) (ls_h)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_v) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (crit_rel_task_event_sched (ls0) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_h)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (InsideCritical sg ls0 )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h )
|--
  “ (prio_v > pcp_v) ” 
  &&  “ ((unsigned_last_nbits (pcp_v) (32)) <> 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ”
  &&  (InsideCritical sg ls0 )
  **  (coq_prop (crit_rel_task_event_sched (ls0) (ls_h)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_wake_step_prop (sg) (eid) (ls_r) (prio_v) (canonical_waiter) (table_owner) (ls_wake)) )
  **  (coq_prop (mutex_post_count_commit_step_prop (eid) (prio_v) (ls_wake) (ls_cnt)) )
  **  (coq_prop (mutex_post_owner_commit_step_prop (eid) (prio_v) (table_owner) (ls_cnt) (ls_h)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_v) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_h)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h )
.

Definition OSMutexPost_full_partial_solve_wit_22 := 
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_h: UCOS2_Verify_State) (ls_r: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State) (e_h: OSEventAbstractState) (canonical_waiter: Z) (table_owner: Z) (cnt_h: Z) (ptr_h: Z) (grp_h: Z) (tbl_o: (@list Z)) (pcp_o: Z) (prio_o: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (pcp_o = pcp_idx)) (PreH4 : (prio_o > pcp_idx)) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_o) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_o)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (OutsideCritical sg ls_h )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h )
|--
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_o = pcp_idx) ” 
  &&  “ (prio_o > pcp_idx) ”
  &&  (OutsideCritical sg ls_h )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_o) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_o)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSMutexPost_full_partial_solve_wit_23 := 
forall (pcp_idx: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_h: UCOS2_Verify_State) (ls_r: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State) (e_h: OSEventAbstractState) (canonical_waiter: Z) (table_owner: Z) (cnt_h: Z) (ptr_h: Z) (grp_h: Z) (tbl_o: (@list Z)) (pcp_o: Z) (prio_o: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (pcp_o = pcp_idx)) (PreH4 : (pcp_idx = 255)) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_o) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_o)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (OutsideCritical sg ls_h )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h )
|--
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_o = pcp_idx) ” 
  &&  “ (pcp_idx = 255) ”
  &&  (OutsideCritical sg ls_h )
  **  (UCOS2_raw_ready_prio_stage sg ls0 ls_h )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e) (4) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_post_handover_step_prop (sg) (eid) (ls_d) (prio_o) (canonical_waiter) (table_owner) (ls_h)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_h.(TskState) )) ((ls_h.(EventState) )) (eid) (e_h) (4) (cnt_h) (ptr_h) (grp_h) (tbl_o)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSMutexPost_full_partial_solve_wit_24 := 
forall (pcp_idx: Z) (ecnt_in: Z) (eid: Z) (pevent0: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_r: UCOS2_Verify_State) (ls_available: UCOS2_Verify_State) (ls_reserved: UCOS2_Verify_State) (ls_d: UCOS2_Verify_State) (e_r: OSEventAbstractState) (pcp_v: Z) (cnt_r: Z) (ptr_r: Z) (grp_r: Z) (tbl_r: (@list Z)) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X )) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) (PreH3 : (pcp_v = pcp_idx)) ,
  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_reserved)) )
  **  (coq_prop (mutex_post_empty_count_commit_step_prop (eid) (ls_reserved) (ls_available)) )
  **  (coq_prop (mutex_post_empty_owner_commit_step_prop (eid) (ls_available) (ls_r)) )
  **  (coq_prop (mutex_post_release_step_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (crit_rel_task_event_sched (ls0) (ls_r)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e_r) (4) (cnt_r) (ptr_r) (grp_r) (tbl_r)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (InsideCritical sg ls0 )
  **  (mutex_post_rep sg ls0 ls_r )
|--
  “ (safeExec (LastSeen (ls0)) (bind ((OSMutexPost_atomic_cmd (sg) (ls0) (pevent0))) (observe_os_err_code)) X ) ” 
  &&  “ (pevent0 = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_v = pcp_idx) ”
  &&  (InsideCritical sg ls0 )
  **  (coq_prop (crit_rel_task_event_sched (ls0) (ls_r)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
  **  (coq_prop (mutex_post_owner_disinherit_stage_prop (sg) (pevent0) (ls0) (pcp_idx) ((decode_OwnerPrio_from_cnt (ecnt_in))) (ls_d)) )
  **  (coq_prop (mutex_post_reservation_stage_prop (sg) (eid) (ls_d) (ls_reserved)) )
  **  (coq_prop (mutex_post_empty_count_commit_step_prop (eid) (ls_reserved) (ls_available)) )
  **  (coq_prop (mutex_post_empty_owner_commit_step_prop (eid) (ls_available) (ls_r)) )
  **  (coq_prop (mutex_post_release_step_prop (sg) (eid) (ls_d) (ls_r)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (event_raw_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e_r) (4) (cnt_r) (ptr_r) (grp_r) (tbl_r)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventType")) (&((pevent0)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent0)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent0)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent0)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (mutex_post_rep sg ls0 ls_r )
.

Definition OSMutexPost_full_which_implies_wit_1 := 
(
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_Verify_inv sg ls0 )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
) \/
(
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_Verify_inv sg ls0 )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
).

Definition OSMutexPost_full_which_implies_wit_1_split_goal_spatial := 
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_Verify_inv sg ls0 )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
.

Definition OSMutexPost_full_which_implies_wit_2 := 
(
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
  &&  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
) \/
(
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
).

Definition OSMutexPost_full_which_implies_wit_2_split_goal_spatial := 
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
.

Definition OSMutexPost_full_which_implies_wit_3 := 
(
forall (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_Verify_inv sg ls0 )
|--
  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((ls0.(EventState) )) (eid)))
  **  (UCOS2_Verify_inv_no_event_type sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
) \/
(
forall (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_Verify_inv sg ls0 )
|--
  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((ls0.(EventState) )) (eid)))
  **  (UCOS2_Verify_inv_no_event_type sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
).

Definition OSMutexPost_full_which_implies_wit_3_split_goal_spatial := 
forall (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_Verify_inv sg ls0 )
|--
  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((ls0.(EventState) )) (eid)))
  **  (UCOS2_Verify_inv_no_event_type sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
.

Definition OSMutexPost_full_which_implies_wit_4 := 
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pevent_v: Z) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_v) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((ls0.(EventState) )) (eid)))
  **  (UCOS2_Verify_inv_no_event_type sg ls0 eid )
|--
  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_v) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_Verify_inv sg ls0 )
) \/
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pevent_v: Z) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_v) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((ls0.(EventState) )) (eid)))
  **  (UCOS2_Verify_inv_no_event_type sg ls0 eid )
|--
  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_v) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_Verify_inv sg ls0 )
).

Definition OSMutexPost_full_which_implies_wit_4_split_goal_spatial := 
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pevent_v: Z) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_v) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((ls0.(EventState) )) (eid)))
  **  (UCOS2_Verify_inv_no_event_type sg ls0 eid )
|--
  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_v) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_Verify_inv sg ls0 )
.

Definition OSMutexPost_full_which_implies_wit_5 := 
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pevent_v: Z) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_v) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((ls0.(EventState) )) (eid)))
  **  (UCOS2_Verify_inv_no_event_type sg ls0 eid )
|--
  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_v) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_Verify_inv sg ls0 )
) \/
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pevent_v: Z) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_v) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((ls0.(EventState) )) (eid)))
  **  (UCOS2_Verify_inv_no_event_type sg ls0 eid )
|--
  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_v) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_Verify_inv sg ls0 )
).

Definition OSMutexPost_full_which_implies_wit_5_split_goal_spatial := 
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pevent_v: Z) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_v) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((ls0.(EventState) )) (eid)))
  **  (UCOS2_Verify_inv_no_event_type sg ls0 eid )
|--
  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent_v) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_Verify_inv sg ls0 )
.

Definition OSMutexPost_full_which_implies_wit_6 := 
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) = 4)) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (etype = 4) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ (pcp_idx = (decode_PCP_from_cnt (ecnt_in))) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ”
  &&  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent0)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
) \/
(
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) = 4)) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) ,
  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ” 
  &&  “ (pcp_idx = (decode_PCP_from_cnt (ecnt_in))) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (pevent = pevent0) ”
  &&  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
).

Definition OSMutexPost_full_which_implies_wit_6_split_goal_1 := 
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) = 4)) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) ,
  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ”
.

Definition OSMutexPost_full_which_implies_wit_6_split_goal_2 := 
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) = 4)) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) ,
  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (pcp_idx = (decode_PCP_from_cnt (ecnt_in))) ”
.

Definition OSMutexPost_full_which_implies_wit_6_split_goal_3 := 
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) = 4)) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) ,
  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (tcbcur <> 0) ”
.

Definition OSMutexPost_full_which_implies_wit_6_split_goal_4 := 
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) = 4)) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) ,
  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (etype = 4) ”
.

Definition OSMutexPost_full_which_implies_wit_6_split_goal_5 := 
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) = 4)) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) ,
  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (pevent = pevent0) ”
.

Definition OSMutexPost_full_which_implies_wit_6_split_goal_spatial := 
forall (prioL_in: (@list Z)) (prio_tbl_pcp: Z) (pcp_idx: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (pevent0: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((event_slot_type_value ((ls0.(EventState) )) (eid))) (32)) = 4)) (PreH2 : (pevent0 = (event_addr (sg) (eid)))) ,
  (coq_prop (mutex_post_public_event_domain_prop (sg) (ls0) (pevent) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in) (pcp_idx) (prio_tbl_pcp) (tcbcur) (tcbprio) (prioL_in) (cur_tid) (cur_t) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl")) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_prio_snapshot_of_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
.

Definition OSMutexPost_full_which_implies_wit_7 := 
(
forall (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (UCOS2_Verify_inv sg ls0 )
|--
  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
) \/
(
forall (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (UCOS2_Verify_inv sg ls0 )
|--
  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
).

Definition OSMutexPost_full_which_implies_wit_7_split_goal_spatial := 
forall (evtL_in: (@list Z)) (egrp_in: Z) (owner_ptr: Z) (ecnt_in: Z) (etype: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  (UCOS2_Verify_inv sg ls0 )
|--
  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (owner_ptr) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) (&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (UCOS2_isr_or_task_call_boundary_prop (ls0)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> owner_ptr)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (1) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (2 * sizeof(UCHAR)))) # UChar  |-> (Znth (2) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (3 * sizeof(UCHAR)))) # UChar  |-> (Znth (3) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (4 * sizeof(UCHAR)))) # UChar  |-> (Znth (4) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (5 * sizeof(UCHAR)))) # UChar  |-> (Znth (5) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (6 * sizeof(UCHAR)))) # UChar  |-> (Znth (6) (evtL_in) (0)))
  **  (((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventTbl") + (7 * sizeof(UCHAR)))) # UChar  |-> (Znth (7) (evtL_in) (0)))
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls0)) )
.

Definition OSMutexPost_full_which_implies_wit_8 := 
(
forall (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_cs: UCOS2_Verify_State) ,
  (InsideCritical sg ls_cs )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls_cs)) )
|--
  (InsideCritical sg ls_cs )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls_cs)) )
  **  (coq_prop (crit_rel_task_event_sched (ls_cs) (ls0)) )
) \/
(
forall (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_cs: UCOS2_Verify_State) ,
  (InsideCritical sg ls_cs )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls_cs)) )
|--
  (InsideCritical sg ls_cs )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls_cs)) )
  **  (coq_prop (crit_rel_task_event_sched (ls_cs) (ls0)) )
).

Definition OSMutexPost_full_which_implies_wit_8_split_goal_spatial := 
forall (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_cs: UCOS2_Verify_State) ,
  (InsideCritical sg ls_cs )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls_cs)) )
|--
  (InsideCritical sg ls_cs )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls_cs)) )
  **  (coq_prop (crit_rel_task_event_sched (ls_cs) (ls0)) )
.

Definition OSMutexPost_full_which_implies_wit_9 := 
(
forall (pcp_idx: Z) (sg: StableGlobVars) (prioL_d: (@list Z)) (PreH1 : (pcp_idx <> 255)) (PreH2 : (0 <= pcp_idx)) (PreH3 : (pcp_idx < 64)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (store_priotbl_list sg prioL_d )
|--
  “ (pcp_idx <> 255) ” 
  &&  “ (0 <= pcp_idx) ” 
  &&  “ (pcp_idx < 64) ”
  &&  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (pcp_idx * sizeof(PTR)))) # Ptr  |-> (Znth (pcp_idx) (prioL_d) (0)))
  **  (store_priotbl_list_missing_i sg prioL_d pcp_idx )
) \/
(
forall (pcp_idx: Z) (sg: StableGlobVars) (prioL_d: (@list Z)) (PreH1 : (pcp_idx <> 255)) (PreH2 : (0 <= pcp_idx)) (PreH3 : (pcp_idx < 64)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (store_priotbl_list sg prioL_d )
|--
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (pcp_idx * sizeof(PTR)))) # Ptr  |-> (Znth (pcp_idx) (prioL_d) (0)))
  **  (store_priotbl_list_missing_i sg prioL_d pcp_idx )
).

Definition OSMutexPost_full_which_implies_wit_9_split_goal_spatial := 
forall (pcp_idx: Z) (sg: StableGlobVars) (prioL_d: (@list Z)) (PreH1 : (pcp_idx <> 255)) (PreH2 : (0 <= pcp_idx)) (PreH3 : (pcp_idx < 64)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (store_priotbl_list sg prioL_d )
|--
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_mutex_pcp (sg) (pcp_idx)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (pcp_idx * sizeof(PTR)))) # Ptr  |-> (Znth (pcp_idx) (prioL_d) (0)))
  **  (store_priotbl_list_missing_i sg prioL_d pcp_idx )
.

Definition OSMutexPost_full_which_implies_wit_10 := 
(
forall (sg: StableGlobVars) (prio_v: Z) (prioL_h: (@list Z)) (table_owner: Z) (PreH1 : (0 <= prio_v)) (PreH2 : (prio_v < 64)) (PreH3 : ((Znth (prio_v) (prioL_h) (0)) = (tcb_addr (sg) (table_owner)))) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (store_priotbl_list sg prioL_h )
|--
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_v * sizeof(PTR)))) # Ptr  |-> (tcb_addr (sg) (table_owner)))
  **  (store_priotbl_list_missing_i sg prioL_h prio_v )
) \/
(
forall (sg: StableGlobVars) (prio_v: Z) (prioL_h: (@list Z)) (table_owner: Z) (PreH1 : (0 <= prio_v)) (PreH2 : (prio_v < 64)) (PreH3 : ((Znth (prio_v) (prioL_h) (0)) = (tcb_addr (sg) (table_owner)))) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (store_priotbl_list sg prioL_h )
|--
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_v * sizeof(PTR)))) # Ptr  |-> (tcb_addr (sg) (table_owner)))
  **  (store_priotbl_list_missing_i sg prioL_h prio_v )
).

Definition OSMutexPost_full_which_implies_wit_10_split_goal_spatial := 
forall (sg: StableGlobVars) (prio_v: Z) (prioL_h: (@list Z)) (table_owner: Z) (PreH1 : (0 <= prio_v)) (PreH2 : (prio_v < 64)) (PreH3 : ((Znth (prio_v) (prioL_h) (0)) = (tcb_addr (sg) (table_owner)))) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (store_priotbl_list sg prioL_h )
|--
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_v * sizeof(PTR)))) # Ptr  |-> (tcb_addr (sg) (table_owner)))
  **  (store_priotbl_list_missing_i sg prioL_h prio_v )
.

Module Type VC_Correct.


Axiom proof_of_OSMutexPost_full_safety_wit_1 : OSMutexPost_full_safety_wit_1.
Axiom proof_of_OSMutexPost_full_safety_wit_2 : OSMutexPost_full_safety_wit_2.
Axiom proof_of_OSMutexPost_full_safety_wit_3 : OSMutexPost_full_safety_wit_3.
Axiom proof_of_OSMutexPost_full_safety_wit_4 : OSMutexPost_full_safety_wit_4.
Axiom proof_of_OSMutexPost_full_safety_wit_5 : OSMutexPost_full_safety_wit_5.
Axiom proof_of_OSMutexPost_full_safety_wit_6 : OSMutexPost_full_safety_wit_6.
Axiom proof_of_OSMutexPost_full_safety_wit_7 : OSMutexPost_full_safety_wit_7.
Axiom proof_of_OSMutexPost_full_safety_wit_8 : OSMutexPost_full_safety_wit_8.
Axiom proof_of_OSMutexPost_full_safety_wit_9 : OSMutexPost_full_safety_wit_9.
Axiom proof_of_OSMutexPost_full_safety_wit_10 : OSMutexPost_full_safety_wit_10.
Axiom proof_of_OSMutexPost_full_safety_wit_11 : OSMutexPost_full_safety_wit_11.
Axiom proof_of_OSMutexPost_full_entail_wit_1_1 : OSMutexPost_full_entail_wit_1_1.
Axiom proof_of_OSMutexPost_full_entail_wit_1_2 : OSMutexPost_full_entail_wit_1_2.
Axiom proof_of_OSMutexPost_full_entail_wit_1_3 : OSMutexPost_full_entail_wit_1_3.
Axiom proof_of_OSMutexPost_full_entail_wit_2 : OSMutexPost_full_entail_wit_2.
Axiom proof_of_OSMutexPost_full_entail_wit_3 : OSMutexPost_full_entail_wit_3.
Axiom proof_of_OSMutexPost_full_entail_wit_4 : OSMutexPost_full_entail_wit_4.
Axiom proof_of_OSMutexPost_full_entail_wit_5 : OSMutexPost_full_entail_wit_5.
Axiom proof_of_OSMutexPost_full_entail_wit_6_1 : OSMutexPost_full_entail_wit_6_1.
Axiom proof_of_OSMutexPost_full_entail_wit_6_2 : OSMutexPost_full_entail_wit_6_2.
Axiom proof_of_OSMutexPost_full_entail_wit_7 : OSMutexPost_full_entail_wit_7.
Axiom proof_of_OSMutexPost_full_entail_wit_8_1 : OSMutexPost_full_entail_wit_8_1.
Axiom proof_of_OSMutexPost_full_entail_wit_8_2 : OSMutexPost_full_entail_wit_8_2.
Axiom proof_of_OSMutexPost_full_entail_wit_9 : OSMutexPost_full_entail_wit_9.
Axiom proof_of_OSMutexPost_full_entail_wit_10 : OSMutexPost_full_entail_wit_10.
Axiom proof_of_OSMutexPost_full_entail_wit_11 : OSMutexPost_full_entail_wit_11.
Axiom proof_of_OSMutexPost_full_entail_wit_12_1 : OSMutexPost_full_entail_wit_12_1.
Axiom proof_of_OSMutexPost_full_entail_wit_12_2 : OSMutexPost_full_entail_wit_12_2.
Axiom proof_of_OSMutexPost_full_entail_wit_13 : OSMutexPost_full_entail_wit_13.
Axiom proof_of_OSMutexPost_full_return_wit_1 : OSMutexPost_full_return_wit_1.
Axiom proof_of_OSMutexPost_full_return_wit_2 : OSMutexPost_full_return_wit_2.
Axiom proof_of_OSMutexPost_full_return_wit_3 : OSMutexPost_full_return_wit_3.
Axiom proof_of_OSMutexPost_full_return_wit_4 : OSMutexPost_full_return_wit_4.
Axiom proof_of_OSMutexPost_full_return_wit_5 : OSMutexPost_full_return_wit_5.
Axiom proof_of_OSMutexPost_full_return_wit_6 : OSMutexPost_full_return_wit_6.
Axiom proof_of_OSMutexPost_full_return_wit_7 : OSMutexPost_full_return_wit_7.
Axiom proof_of_OSMutexPost_full_return_wit_8 : OSMutexPost_full_return_wit_8.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_1_pure : OSMutexPost_full_partial_solve_wit_1_pure.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_1 : OSMutexPost_full_partial_solve_wit_1.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_2_pure : OSMutexPost_full_partial_solve_wit_2_pure.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_2 : OSMutexPost_full_partial_solve_wit_2.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_3_pure : OSMutexPost_full_partial_solve_wit_3_pure.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_3 : OSMutexPost_full_partial_solve_wit_3.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_4_pure : OSMutexPost_full_partial_solve_wit_4_pure.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_4 : OSMutexPost_full_partial_solve_wit_4.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_5 : OSMutexPost_full_partial_solve_wit_5.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_6 : OSMutexPost_full_partial_solve_wit_6.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_7 : OSMutexPost_full_partial_solve_wit_7.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_8 : OSMutexPost_full_partial_solve_wit_8.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_9_pure : OSMutexPost_full_partial_solve_wit_9_pure.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_9 : OSMutexPost_full_partial_solve_wit_9.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_10 : OSMutexPost_full_partial_solve_wit_10.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_11 : OSMutexPost_full_partial_solve_wit_11.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_12 : OSMutexPost_full_partial_solve_wit_12.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_13 : OSMutexPost_full_partial_solve_wit_13.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_14_pure : OSMutexPost_full_partial_solve_wit_14_pure.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_14 : OSMutexPost_full_partial_solve_wit_14.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_15_pure : OSMutexPost_full_partial_solve_wit_15_pure.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_15 : OSMutexPost_full_partial_solve_wit_15.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_16_pure : OSMutexPost_full_partial_solve_wit_16_pure.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_16 : OSMutexPost_full_partial_solve_wit_16.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_17_pure : OSMutexPost_full_partial_solve_wit_17_pure.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_17 : OSMutexPost_full_partial_solve_wit_17.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_18 : OSMutexPost_full_partial_solve_wit_18.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_19 : OSMutexPost_full_partial_solve_wit_19.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_20 : OSMutexPost_full_partial_solve_wit_20.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_21 : OSMutexPost_full_partial_solve_wit_21.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_22 : OSMutexPost_full_partial_solve_wit_22.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_23 : OSMutexPost_full_partial_solve_wit_23.
Axiom proof_of_OSMutexPost_full_partial_solve_wit_24 : OSMutexPost_full_partial_solve_wit_24.
Axiom proof_of_OSMutexPost_full_which_implies_wit_1 : OSMutexPost_full_which_implies_wit_1.
Axiom proof_of_OSMutexPost_full_which_implies_wit_2 : OSMutexPost_full_which_implies_wit_2.
Axiom proof_of_OSMutexPost_full_which_implies_wit_3 : OSMutexPost_full_which_implies_wit_3.
Axiom proof_of_OSMutexPost_full_which_implies_wit_4 : OSMutexPost_full_which_implies_wit_4.
Axiom proof_of_OSMutexPost_full_which_implies_wit_5 : OSMutexPost_full_which_implies_wit_5.
Axiom proof_of_OSMutexPost_full_which_implies_wit_6 : OSMutexPost_full_which_implies_wit_6.
Axiom proof_of_OSMutexPost_full_which_implies_wit_7 : OSMutexPost_full_which_implies_wit_7.
Axiom proof_of_OSMutexPost_full_which_implies_wit_8 : OSMutexPost_full_which_implies_wit_8.
Axiom proof_of_OSMutexPost_full_which_implies_wit_9 : OSMutexPost_full_which_implies_wit_9.
Axiom proof_of_OSMutexPost_full_which_implies_wit_10 : OSMutexPost_full_which_implies_wit_10.

End VC_Correct.
