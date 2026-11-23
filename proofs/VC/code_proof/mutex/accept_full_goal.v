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
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.mutex_func_sem.
Require Import Ucos2Verify.lib.array_abstraction.
Local Open Scope sac.

(*----- Function OSMutexAccept_full -----*)

Definition OSMutexAccept_full_safety_wit_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr >= 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (perr_pre <> 0)) (PreH4 : (pd = perr_pre)) (PreH5 : (pe = pevent_pre)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH7 : (pevent_pre <> 0)) (PreH8 : (pevent_pre = (event_addr (sg) (eid)))) (PreH9 : (0 <= etype)) (PreH10 : (etype <= 255)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexAccept_full_safety_wit_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr >= 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (perr_pre <> 0)) (PreH4 : (pd = perr_pre)) (PreH5 : (pe = pevent_pre)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH7 : (pevent_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexAccept_full_safety_wit_3 := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre = 0)) (PreH2 : (isr >= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (perr_pre <> 0)) (PreH5 : (pd = perr_pre)) (PreH6 : (pe = pevent_pre)) (PreH7 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH8 : (pevent_pre <> 0)) (PreH9 : (pevent_pre = (event_addr (sg) (eid)))) (PreH10 : (0 <= etype)) (PreH11 : (etype <= 255)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ False ”
.

Definition OSMutexAccept_full_safety_wit_4 := 
forall (perr_pre: Z) (pevent_pre: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre <> 0)) (PreH2 : (isr >= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (perr_pre <> 0)) (PreH5 : (pd = perr_pre)) (PreH6 : (pe = pevent_pre)) (PreH7 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH8 : (pevent_pre = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  “ False ”
.

Definition OSMutexAccept_full_safety_wit_5 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (PreH1 : (RTrans_C sg ls0 sg ls1 )) (PreH2 : (etype = 4)) (PreH3 : (isr <= 0)) (PreH4 : (tcbcur <> 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (etype = 4)) (PreH7 : (isr <= 0)) (PreH8 : (tcbcur <> 0)) (PreH9 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (etype = 4)) (PreH12 : (pevent_pre <> 0)) (PreH13 : (isr >= 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (perr_pre <> 0)) (PreH16 : (pd = perr_pre)) (PreH17 : (pe = pevent_pre)) (PreH18 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = (event_addr (sg) (eid)))) (PreH21 : (0 <= etype)) (PreH22 : (etype <= 255)) ,
  (InsideCritical sg ls1 )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pcp" ) )) # UChar  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (0 <= ecnt_in) ” 
  &&  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (PreH1 : (RTrans_C sg ls0 sg ls1 )) (PreH2 : (etype = 4)) (PreH3 : (isr <= 0)) (PreH4 : (tcbcur <> 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (etype = 4)) (PreH7 : (isr <= 0)) (PreH8 : (tcbcur <> 0)) (PreH9 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (etype = 4)) (PreH12 : (pevent_pre <> 0)) (PreH13 : (isr >= 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (perr_pre <> 0)) (PreH16 : (pd = perr_pre)) (PreH17 : (pe = pevent_pre)) (PreH18 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = (event_addr (sg) (eid)))) (PreH21 : (0 <= etype)) (PreH22 : (etype <= 255)) ,
  (InsideCritical sg ls1 )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pcp" ) )) # UChar  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (0 <= ecnt_in) ” 
  &&  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
).

Definition OSMutexAccept_full_safety_wit_5_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (PreH1 : (RTrans_C sg ls0 sg ls1 )) (PreH2 : (etype = 4)) (PreH3 : (isr <= 0)) (PreH4 : (tcbcur <> 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (etype = 4)) (PreH7 : (isr <= 0)) (PreH8 : (tcbcur <> 0)) (PreH9 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (etype = 4)) (PreH12 : (pevent_pre <> 0)) (PreH13 : (isr >= 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (perr_pre <> 0)) (PreH16 : (pd = perr_pre)) (PreH17 : (pe = pevent_pre)) (PreH18 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = (event_addr (sg) (eid)))) (PreH21 : (0 <= etype)) (PreH22 : (etype <= 255)) ,
  (InsideCritical sg ls1 )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pcp" ) )) # UChar  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (0 <= ecnt_in) ”
.

Definition OSMutexAccept_full_safety_wit_5_split_goal_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (PreH1 : (RTrans_C sg ls0 sg ls1 )) (PreH2 : (etype = 4)) (PreH3 : (isr <= 0)) (PreH4 : (tcbcur <> 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (etype = 4)) (PreH7 : (isr <= 0)) (PreH8 : (tcbcur <> 0)) (PreH9 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (etype = 4)) (PreH12 : (pevent_pre <> 0)) (PreH13 : (isr >= 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (perr_pre <> 0)) (PreH16 : (pd = perr_pre)) (PreH17 : (pe = pevent_pre)) (PreH18 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = (event_addr (sg) (eid)))) (PreH21 : (0 <= etype)) (PreH22 : (etype <= 255)) ,
  (InsideCritical sg ls1 )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pcp" ) )) # UChar  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (8 <= 31) ”
.

Definition OSMutexAccept_full_safety_wit_5_split_goal_3 := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (PreH1 : (RTrans_C sg ls0 sg ls1 )) (PreH2 : (etype = 4)) (PreH3 : (isr <= 0)) (PreH4 : (tcbcur <> 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (etype = 4)) (PreH7 : (isr <= 0)) (PreH8 : (tcbcur <> 0)) (PreH9 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (etype = 4)) (PreH12 : (pevent_pre <> 0)) (PreH13 : (isr >= 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (perr_pre <> 0)) (PreH16 : (pd = perr_pre)) (PreH17 : (pe = pevent_pre)) (PreH18 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = (event_addr (sg) (eid)))) (PreH21 : (0 <= etype)) (PreH22 : (etype <= 255)) ,
  (InsideCritical sg ls1 )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pcp" ) )) # UChar  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (0 <= 8) ”
.

Definition OSMutexAccept_full_return_wit_1 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls_next: UCOS2_Verify_State) (ls_cs: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls_cs sg ls_next )) (PreH2 : ((Z.land ecnt_in 255) <> 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (etype = 4)) (PreH5 : (isr <= 0)) (PreH6 : (tcbcur <> 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (etype = 4)) (PreH9 : (isr <= 0)) (PreH10 : (tcbcur <> 0)) (PreH11 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH12 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH13 : (etype = 4)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (isr >= 0)) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (perr_pre <> 0)) (PreH18 : (pd = perr_pre)) (PreH19 : (pe = pevent_pre)) (PreH20 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = (event_addr (sg) (eid)))) (PreH23 : (0 <= etype)) (PreH24 : (etype <= 255)) ,
  (OutsideCritical sg ls_next )
  **  (interrupt_inv sg (ls_next.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_next.(TskState) ) (ls_next.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (mutex_accept_restore_transition_prop (ls0) (ls_cs) (ls_next) (eid) (e) (cur_tid) (tcbprio) (false)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((perr_pre) # UChar  |-> 0)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((Z.land ecnt_in 255) <> 255) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 0)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls_next: UCOS2_Verify_State) (ls_cs: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls_cs sg ls_next )) (PreH2 : ((Z.land ecnt_in 255) <> 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (etype = 4)) (PreH5 : (isr <= 0)) (PreH6 : (tcbcur <> 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (etype = 4)) (PreH9 : (isr <= 0)) (PreH10 : (tcbcur <> 0)) (PreH11 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH12 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH13 : (etype = 4)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (isr >= 0)) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (perr_pre <> 0)) (PreH18 : (pd = perr_pre)) (PreH19 : (pe = pevent_pre)) (PreH20 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = (event_addr (sg) (eid)))) (PreH23 : (0 <= etype)) (PreH24 : (etype <= 255)) ,
  (OutsideCritical sg ls_next )
  **  (interrupt_inv sg (ls_next.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_next.(TskState) ) (ls_next.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (mutex_accept_restore_transition_prop (ls0) (ls_cs) (ls_next) (eid) (e) (cur_tid) (tcbprio) (false)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls_post)) (return (0)) X ) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((Z.land ecnt_in 255) <> 255) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
).

Definition OSMutexAccept_full_return_wit_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls_next: UCOS2_Verify_State) (ls_cs: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls_cs sg ls_next )) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = 255)) (PreH3 : ((Z.land ecnt_in 255) = 255)) (PreH4 : (RTrans_C sg ls0 sg ls1 )) (PreH5 : (etype = 4)) (PreH6 : (isr <= 0)) (PreH7 : (tcbcur <> 0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (etype = 4)) (PreH10 : (isr <= 0)) (PreH11 : (tcbcur <> 0)) (PreH12 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (etype = 4)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr >= 0)) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (perr_pre <> 0)) (PreH19 : (pd = perr_pre)) (PreH20 : (pe = pevent_pre)) (PreH21 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = (event_addr (sg) (eid)))) (PreH24 : (0 <= etype)) (PreH25 : (etype <= 255)) ,
  (OutsideCritical sg ls_next )
  **  (interrupt_inv sg (ls_next.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_next.(TskState) ) (ls_next.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (mutex_accept_restore_transition_prop (ls0) (ls_cs) (ls_next) (eid) (e) (cur_tid) (tcbprio) (true)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> tcbcur)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land ecnt_in 65280) (unsigned_last_nbits (tcbprio) (16))))
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((perr_pre) # UChar  |-> 0)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  (EX (e_post: OSEventAbstractState)  (ecnt_post: Z)  (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (1 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (1 = 1) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((Z.land ecnt_in 255) = 255) ” 
  &&  “ (ecnt_post = (Z.lor (Z.land ecnt_in 65280) tcbprio)) ” 
  &&  “ ((Z.shiftr ecnt_in 8) <> 255) ” 
  &&  “ (tcbprio <= (Z.shiftr ecnt_in 8)) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e_post) (4) (ecnt_post) (tcbcur) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 120))
  ||
  (EX (e_post: OSEventAbstractState)  (ecnt_post: Z)  (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (1 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (1 = 1) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((Z.land ecnt_in 255) = 255) ” 
  &&  “ (ecnt_post = (Z.lor (Z.land ecnt_in 65280) tcbprio)) ” 
  &&  “ (tcbprio > (Z.shiftr ecnt_in 8)) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e_post) (4) (ecnt_post) (tcbcur) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 0))
  ||
  (EX (e_post: OSEventAbstractState)  (ecnt_post: Z)  (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (1 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (1 = 1) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((Z.land ecnt_in 255) = 255) ” 
  &&  “ (ecnt_post = (Z.lor (Z.land ecnt_in 65280) tcbprio)) ” 
  &&  “ ((Z.shiftr ecnt_in 8) = 255) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e_post) (4) (ecnt_post) (tcbcur) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 0))
.

Definition OSMutexAccept_full_return_wit_3 := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls_next: UCOS2_Verify_State) (ls_cs: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls_cs sg ls_next )) (PreH2 : (tcbprio > (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH3 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH4 : ((Z.land ecnt_in 255) = 255)) (PreH5 : (RTrans_C sg ls0 sg ls1 )) (PreH6 : (etype = 4)) (PreH7 : (isr <= 0)) (PreH8 : (tcbcur <> 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (etype = 4)) (PreH11 : (isr <= 0)) (PreH12 : (tcbcur <> 0)) (PreH13 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (etype = 4)) (PreH16 : (pevent_pre <> 0)) (PreH17 : (isr >= 0)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (perr_pre <> 0)) (PreH20 : (pd = perr_pre)) (PreH21 : (pe = pevent_pre)) (PreH22 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = (event_addr (sg) (eid)))) (PreH25 : (0 <= etype)) (PreH26 : (etype <= 255)) ,
  (OutsideCritical sg ls_next )
  **  (interrupt_inv sg (ls_next.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_next.(TskState) ) (ls_next.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (mutex_accept_restore_transition_prop (ls0) (ls_cs) (ls_next) (eid) (e) (cur_tid) (tcbprio) (true)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> tcbcur)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land ecnt_in 65280) (unsigned_last_nbits (tcbprio) (16))))
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((perr_pre) # UChar  |-> 0)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  (EX (e_post: OSEventAbstractState)  (ecnt_post: Z)  (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (1 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (1 = 1) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((Z.land ecnt_in 255) = 255) ” 
  &&  “ (ecnt_post = (Z.lor (Z.land ecnt_in 65280) tcbprio)) ” 
  &&  “ ((Z.shiftr ecnt_in 8) <> 255) ” 
  &&  “ (tcbprio <= (Z.shiftr ecnt_in 8)) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e_post) (4) (ecnt_post) (tcbcur) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 120))
  ||
  (EX (e_post: OSEventAbstractState)  (ecnt_post: Z)  (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (1 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (1 = 1) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((Z.land ecnt_in 255) = 255) ” 
  &&  “ (ecnt_post = (Z.lor (Z.land ecnt_in 65280) tcbprio)) ” 
  &&  “ (tcbprio > (Z.shiftr ecnt_in 8)) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e_post) (4) (ecnt_post) (tcbcur) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 0))
  ||
  (EX (e_post: OSEventAbstractState)  (ecnt_post: Z)  (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (1 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (1 = 1) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((Z.land ecnt_in 255) = 255) ” 
  &&  “ (ecnt_post = (Z.lor (Z.land ecnt_in 65280) tcbprio)) ” 
  &&  “ ((Z.shiftr ecnt_in 8) = 255) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e_post) (4) (ecnt_post) (tcbcur) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 0))
.

Definition OSMutexAccept_full_return_wit_4 := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls_next: UCOS2_Verify_State) (ls_cs: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls_cs sg ls_next )) (PreH2 : (tcbprio <= (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH3 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH4 : ((Z.land ecnt_in 255) = 255)) (PreH5 : (RTrans_C sg ls0 sg ls1 )) (PreH6 : (etype = 4)) (PreH7 : (isr <= 0)) (PreH8 : (tcbcur <> 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (etype = 4)) (PreH11 : (isr <= 0)) (PreH12 : (tcbcur <> 0)) (PreH13 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (etype = 4)) (PreH16 : (pevent_pre <> 0)) (PreH17 : (isr >= 0)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (perr_pre <> 0)) (PreH20 : (pd = perr_pre)) (PreH21 : (pe = pevent_pre)) (PreH22 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = (event_addr (sg) (eid)))) (PreH25 : (0 <= etype)) (PreH26 : (etype <= 255)) ,
  (OutsideCritical sg ls_next )
  **  (interrupt_inv sg (ls_next.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_next.(TskState) ) (ls_next.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (mutex_accept_restore_transition_prop (ls0) (ls_cs) (ls_next) (eid) (e) (cur_tid) (tcbprio) (true)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> tcbcur)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land ecnt_in 65280) (unsigned_last_nbits (tcbprio) (16))))
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((perr_pre) # UChar  |-> 120)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  (EX (e_post: OSEventAbstractState)  (ecnt_post: Z)  (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (1 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (1 = 1) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((Z.land ecnt_in 255) = 255) ” 
  &&  “ (ecnt_post = (Z.lor (Z.land ecnt_in 65280) tcbprio)) ” 
  &&  “ ((Z.shiftr ecnt_in 8) <> 255) ” 
  &&  “ (tcbprio <= (Z.shiftr ecnt_in 8)) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e_post) (4) (ecnt_post) (tcbcur) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 120))
  ||
  (EX (e_post: OSEventAbstractState)  (ecnt_post: Z)  (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (1 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (1 = 1) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((Z.land ecnt_in 255) = 255) ” 
  &&  “ (ecnt_post = (Z.lor (Z.land ecnt_in 65280) tcbprio)) ” 
  &&  “ (tcbprio > (Z.shiftr ecnt_in 8)) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e_post) (4) (ecnt_post) (tcbcur) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 0))
  ||
  (EX (e_post: OSEventAbstractState)  (ecnt_post: Z)  (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (1 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (1 = 1) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((Z.land ecnt_in 255) = 255) ” 
  &&  “ (ecnt_post = (Z.lor (Z.land ecnt_in 65280) tcbprio)) ” 
  &&  “ ((Z.shiftr ecnt_in 8) = 255) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e_post) (4) (ecnt_post) (tcbcur) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 0))
.

Definition OSMutexAccept_full_return_wit_5 := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits (isr) (32)) > 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (etype = 4)) (PreH4 : (pevent_pre <> 0)) (PreH5 : (isr >= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (perr_pre <> 0)) (PreH8 : (pd = perr_pre)) (PreH9 : (pe = pevent_pre)) (PreH10 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = (event_addr (sg) (eid)))) (PreH13 : (0 <= etype)) (PreH14 : (etype <= 255)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  ((perr_pre) # UChar  |-> 2)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((Z.land ecnt_in 255) <> 255) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 0))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr > 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 2))
.

Definition OSMutexAccept_full_return_wit_6 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype <> 4)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (isr >= 0)) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (perr_pre <> 0)) (PreH6 : (pd = perr_pre)) (PreH7 : (pe = pevent_pre)) (PreH8 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = (event_addr (sg) (eid)))) (PreH11 : (0 <= etype)) (PreH12 : (etype <= 255)) ,
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  ((perr_pre) # UChar  |-> 1)
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype <> 4) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 1)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype <> 4)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (isr >= 0)) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (perr_pre <> 0)) (PreH6 : (pd = perr_pre)) (PreH7 : (pe = pevent_pre)) (PreH8 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = (event_addr (sg) (eid)))) (PreH11 : (0 <= etype)) (PreH12 : (etype <= 255)) ,
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls_post)) (return (0)) X ) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype <> 4) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
).

Definition OSMutexAccept_full_return_wit_7 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (pd: Z) (pe: Z) (isr: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre = 0)) (PreH2 : (isr >= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (perr_pre <> 0)) (PreH5 : (pd = perr_pre)) (PreH6 : (pe = pevent_pre)) (PreH7 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH8 : (pevent_pre = 0)) ,
  ((perr_pre) # UChar  |-> 4)
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (pevent_pre = 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  ((perr_pre) # UChar  |-> 4)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (pd: Z) (pe: Z) (isr: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre = 0)) (PreH2 : (isr >= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (perr_pre <> 0)) (PreH5 : (pd = perr_pre)) (PreH6 : (pe = pevent_pre)) (PreH7 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH8 : (pevent_pre = 0)) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls_post)) (return (0)) X ) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent_pre = 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
).

Definition OSMutexAccept_full_partial_solve_wit_1_pure := 
(
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre <> 0)) (PreH2 : (isr >= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (perr_pre <> 0)) (PreH5 : (pd = perr_pre)) (PreH6 : (pe = pevent_pre)) (PreH7 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH8 : (pevent_pre <> 0)) (PreH9 : (pevent_pre = (event_addr (sg) (eid)))) (PreH10 : (0 <= etype)) (PreH11 : (etype <= 255)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (pe = pe) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pevent_pre <> 0)) (PreH4 : (isr >= 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (perr_pre <> 0)) (PreH7 : (pd = perr_pre)) (PreH8 : (pe = pevent_pre)) (PreH9 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH10 : (pevent_pre <> 0)) (PreH11 : (pevent_pre = (event_addr (sg) (eid)))) (PreH12 : (0 <= etype)) (PreH13 : (etype <= 255)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (pe = (event_addr (sg) (eid))) ”
).

Definition OSMutexAccept_full_partial_solve_wit_1_pure_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pevent_pre <> 0)) (PreH4 : (isr >= 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (perr_pre <> 0)) (PreH7 : (pd = perr_pre)) (PreH8 : (pe = pevent_pre)) (PreH9 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH10 : (pevent_pre <> 0)) (PreH11 : (pevent_pre = (event_addr (sg) (eid)))) (PreH12 : (0 <= etype)) (PreH13 : (etype <= 255)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSMutexAccept_full_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre <> 0)) (PreH2 : (isr >= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (perr_pre <> 0)) (PreH5 : (pd = perr_pre)) (PreH6 : (pe = pevent_pre)) (PreH7 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH8 : (pevent_pre <> 0)) (PreH9 : (pevent_pre = (event_addr (sg) (eid)))) (PreH10 : (0 <= etype)) (PreH11 : (etype <= 255)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (pe = pe) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ”
  &&  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (UCOS2_Verify_inv sg ls0 )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
.

Definition OSMutexAccept_full_partial_solve_wit_1 := OSMutexAccept_full_partial_solve_wit_1_pure -> OSMutexAccept_full_partial_solve_wit_1_aux.

Definition OSMutexAccept_full_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype = 4)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (isr >= 0)) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (perr_pre <> 0)) (PreH6 : (pd = perr_pre)) (PreH7 : (pe = pevent_pre)) (PreH8 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = (event_addr (sg) (eid)))) (PreH11 : (0 <= etype)) (PreH12 : (etype <= 255)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
.

Definition OSMutexAccept_full_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype = 4)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (isr >= 0)) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (perr_pre <> 0)) (PreH6 : (pd = perr_pre)) (PreH7 : (pe = pevent_pre)) (PreH8 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = (event_addr (sg) (eid)))) (PreH11 : (0 <= etype)) (PreH12 : (etype <= 255)) ,
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
.

Definition OSMutexAccept_full_partial_solve_wit_2 := OSMutexAccept_full_partial_solve_wit_2_pure -> OSMutexAccept_full_partial_solve_wit_2_aux.

Definition OSMutexAccept_full_partial_solve_wit_3_pure := 
(
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (etype = 4)) (PreH4 : (pevent_pre <> 0)) (PreH5 : (isr >= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (perr_pre <> 0)) (PreH8 : (pd = perr_pre)) (PreH9 : (pe = pevent_pre)) (PreH10 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = (event_addr (sg) (eid)))) (PreH13 : (0 <= etype)) (PreH14 : (etype <= 255)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((intNesting ((ls0.(IntrState) ))) <= 0) ”
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (etype = 4)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (isr >= 0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (perr_pre <> 0)) (PreH10 : (pd = perr_pre)) (PreH11 : (pe = pevent_pre)) (PreH12 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (pevent_pre = (event_addr (sg) (eid)))) (PreH15 : (0 <= etype)) (PreH16 : (etype <= 255)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ ((intNesting ((ls0.(IntrState) ))) <= 0) ” 
  &&  “ (isr <= 0) ”
).

Definition OSMutexAccept_full_partial_solve_wit_3_pure_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (etype = 4)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (isr >= 0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (perr_pre <> 0)) (PreH10 : (pd = perr_pre)) (PreH11 : (pe = pevent_pre)) (PreH12 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (pevent_pre = (event_addr (sg) (eid)))) (PreH15 : (0 <= etype)) (PreH16 : (etype <= 255)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ ((intNesting ((ls0.(IntrState) ))) <= 0) ”
.

Definition OSMutexAccept_full_partial_solve_wit_3_pure_split_goal_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (etype = 4)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (isr >= 0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (perr_pre <> 0)) (PreH10 : (pd = perr_pre)) (PreH11 : (pe = pevent_pre)) (PreH12 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH13 : (pevent_pre <> 0)) (PreH14 : (pevent_pre = (event_addr (sg) (eid)))) (PreH15 : (0 <= etype)) (PreH16 : (etype <= 255)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (isr <= 0) ”
.

Definition OSMutexAccept_full_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (etype = 4)) (PreH4 : (pevent_pre <> 0)) (PreH5 : (isr >= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (perr_pre <> 0)) (PreH8 : (pd = perr_pre)) (PreH9 : (pe = pevent_pre)) (PreH10 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH11 : (pevent_pre <> 0)) (PreH12 : (pevent_pre = (event_addr (sg) (eid)))) (PreH13 : (0 <= etype)) (PreH14 : (etype <= 255)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((intNesting ((ls0.(IntrState) ))) <= 0) ” 
  &&  “ ((unsigned_last_nbits (isr) (32)) <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ”
  &&  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
.

Definition OSMutexAccept_full_partial_solve_wit_3 := OSMutexAccept_full_partial_solve_wit_3_pure -> OSMutexAccept_full_partial_solve_wit_3_aux.

Definition OSMutexAccept_full_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype = 4)) (PreH2 : (isr <= 0)) (PreH3 : (tcbcur <> 0)) (PreH4 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (etype = 4)) (PreH7 : (pevent_pre <> 0)) (PreH8 : (isr >= 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (perr_pre <> 0)) (PreH11 : (pd = perr_pre)) (PreH12 : (pe = pevent_pre)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = (event_addr (sg) (eid)))) (PreH16 : (0 <= etype)) (PreH17 : (etype <= 255)) ,
  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
.

Definition OSMutexAccept_full_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype = 4)) (PreH2 : (isr <= 0)) (PreH3 : (tcbcur <> 0)) (PreH4 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (etype = 4)) (PreH7 : (pevent_pre <> 0)) (PreH8 : (isr >= 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (perr_pre <> 0)) (PreH11 : (pd = perr_pre)) (PreH12 : (pe = pevent_pre)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH14 : (pevent_pre <> 0)) (PreH15 : (pevent_pre = (event_addr (sg) (eid)))) (PreH16 : (0 <= etype)) (PreH17 : (etype <= 255)) ,
  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ ((unsigned_last_nbits (isr) (32)) <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
.

Definition OSMutexAccept_full_partial_solve_wit_4 := OSMutexAccept_full_partial_solve_wit_4_pure -> OSMutexAccept_full_partial_solve_wit_4_aux.

Definition OSMutexAccept_full_partial_solve_wit_5_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (etype = 4)) (PreH3 : (isr <= 0)) (PreH4 : (tcbcur <> 0)) (PreH5 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (etype = 4)) (PreH8 : (pevent_pre <> 0)) (PreH9 : (isr >= 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (perr_pre <> 0)) (PreH12 : (pd = perr_pre)) (PreH13 : (pe = pevent_pre)) (PreH14 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH15 : (pevent_pre <> 0)) (PreH16 : (pevent_pre = (event_addr (sg) (eid)))) (PreH17 : (0 <= etype)) (PreH18 : (etype <= 255)) ,
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pcp" ) )) # UChar  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ”
.

Definition OSMutexAccept_full_partial_solve_wit_5_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (etype = 4)) (PreH3 : (isr <= 0)) (PreH4 : (tcbcur <> 0)) (PreH5 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (etype = 4)) (PreH8 : (pevent_pre <> 0)) (PreH9 : (isr >= 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (perr_pre <> 0)) (PreH12 : (pd = perr_pre)) (PreH13 : (pe = pevent_pre)) (PreH14 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH15 : (pevent_pre <> 0)) (PreH16 : (pevent_pre = (event_addr (sg) (eid)))) (PreH17 : (0 <= etype)) (PreH18 : (etype <= 255)) ,
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ ((unsigned_last_nbits (isr) (32)) <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ”
  &&  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSMutexAccept_full_partial_solve_wit_5 := OSMutexAccept_full_partial_solve_wit_5_pure -> OSMutexAccept_full_partial_solve_wit_5_aux.

Definition OSMutexAccept_full_partial_solve_wit_6 := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype = 4)) (PreH2 : (isr <= 0)) (PreH3 : (tcbcur <> 0)) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (etype = 4)) (PreH6 : (isr <= 0)) (PreH7 : (tcbcur <> 0)) (PreH8 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (etype = 4)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (isr >= 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (perr_pre <> 0)) (PreH15 : (pd = perr_pre)) (PreH16 : (pe = pevent_pre)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = (event_addr (sg) (eid)))) (PreH20 : (0 <= etype)) (PreH21 : (etype <= 255)) ,
  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ ((unsigned_last_nbits (isr) (32)) <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ”
  &&  (OutsideCritical sg ls0 )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSMutexAccept_full_partial_solve_wit_7 := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (PreH1 : (tcbprio <= (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : ((Z.land ecnt_in 255) = 255)) (PreH4 : (RTrans_C sg ls0 sg ls1 )) (PreH5 : (etype = 4)) (PreH6 : (isr <= 0)) (PreH7 : (tcbcur <> 0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (etype = 4)) (PreH10 : (isr <= 0)) (PreH11 : (tcbcur <> 0)) (PreH12 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (etype = 4)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr >= 0)) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (perr_pre <> 0)) (PreH19 : (pd = perr_pre)) (PreH20 : (pe = pevent_pre)) (PreH21 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = (event_addr (sg) (eid)))) (PreH24 : (0 <= etype)) (PreH25 : (etype <= 255)) ,
  (InsideCritical sg ls1 )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> tcbcur)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land ecnt_in 65280) (unsigned_last_nbits (tcbprio) (16))))
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (tcbprio <= (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ ((Z.land ecnt_in 255) = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ ((unsigned_last_nbits (isr) (32)) <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ”
  &&  (InsideCritical sg ls1 )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> tcbcur)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land ecnt_in 65280) (unsigned_last_nbits (tcbprio) (16))))
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSMutexAccept_full_partial_solve_wit_8 := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls_next: UCOS2_Verify_State) (ls_cs: UCOS2_Verify_State) (PreH1 : (tcbprio <= (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : ((Z.land ecnt_in 255) = 255)) (PreH4 : (RTrans_C sg ls0 sg ls1 )) (PreH5 : (etype = 4)) (PreH6 : (isr <= 0)) (PreH7 : (tcbcur <> 0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (etype = 4)) (PreH10 : (isr <= 0)) (PreH11 : (tcbcur <> 0)) (PreH12 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (etype = 4)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr >= 0)) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (perr_pre <> 0)) (PreH19 : (pd = perr_pre)) (PreH20 : (pe = pevent_pre)) (PreH21 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = (event_addr (sg) (eid)))) (PreH24 : (0 <= etype)) (PreH25 : (etype <= 255)) ,
  (InsideCritical sg ls_cs )
  **  (interrupt_inv sg (ls_cs.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_cs.(TskState) ) (ls_cs.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (mutex_accept_restore_transition_prop (ls0) (ls_cs) (ls_next) (eid) (e) (cur_tid) (tcbprio) (true)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> tcbcur)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land ecnt_in 65280) (unsigned_last_nbits (tcbprio) (16))))
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (tcbprio <= (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ ((Z.land ecnt_in 255) = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ ((unsigned_last_nbits (isr) (32)) <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ”
  &&  (InsideCritical sg ls_cs )
  **  (interrupt_inv sg (ls_cs.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_cs.(TskState) ) (ls_cs.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (mutex_accept_restore_transition_prop (ls0) (ls_cs) (ls_next) (eid) (e) (cur_tid) (tcbprio) (true)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> tcbcur)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land ecnt_in 65280) (unsigned_last_nbits (tcbprio) (16))))
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSMutexAccept_full_partial_solve_wit_9 := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (PreH1 : (tcbprio > (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : ((Z.land ecnt_in 255) = 255)) (PreH4 : (RTrans_C sg ls0 sg ls1 )) (PreH5 : (etype = 4)) (PreH6 : (isr <= 0)) (PreH7 : (tcbcur <> 0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (etype = 4)) (PreH10 : (isr <= 0)) (PreH11 : (tcbcur <> 0)) (PreH12 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (etype = 4)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr >= 0)) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (perr_pre <> 0)) (PreH19 : (pd = perr_pre)) (PreH20 : (pe = pevent_pre)) (PreH21 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = (event_addr (sg) (eid)))) (PreH24 : (0 <= etype)) (PreH25 : (etype <= 255)) ,
  (InsideCritical sg ls1 )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> tcbcur)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land ecnt_in 65280) (unsigned_last_nbits (tcbprio) (16))))
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (tcbprio > (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ ((Z.land ecnt_in 255) = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ ((unsigned_last_nbits (isr) (32)) <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ”
  &&  (InsideCritical sg ls1 )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> tcbcur)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land ecnt_in 65280) (unsigned_last_nbits (tcbprio) (16))))
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSMutexAccept_full_partial_solve_wit_10 := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = 255)) (PreH2 : ((Z.land ecnt_in 255) = 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (etype = 4)) (PreH5 : (isr <= 0)) (PreH6 : (tcbcur <> 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (etype = 4)) (PreH9 : (isr <= 0)) (PreH10 : (tcbcur <> 0)) (PreH11 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH12 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH13 : (etype = 4)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (isr >= 0)) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (perr_pre <> 0)) (PreH18 : (pd = perr_pre)) (PreH19 : (pe = pevent_pre)) (PreH20 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = (event_addr (sg) (eid)))) (PreH23 : (0 <= etype)) (PreH24 : (etype <= 255)) ,
  (InsideCritical sg ls1 )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> tcbcur)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land ecnt_in 65280) (unsigned_last_nbits (tcbprio) (16))))
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = 255) ” 
  &&  “ ((Z.land ecnt_in 255) = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ ((unsigned_last_nbits (isr) (32)) <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ”
  &&  (InsideCritical sg ls1 )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> tcbcur)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land ecnt_in 65280) (unsigned_last_nbits (tcbprio) (16))))
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSMutexAccept_full_partial_solve_wit_11 := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls_next: UCOS2_Verify_State) (ls_cs: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = 255)) (PreH2 : ((Z.land ecnt_in 255) = 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (etype = 4)) (PreH5 : (isr <= 0)) (PreH6 : (tcbcur <> 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (etype = 4)) (PreH9 : (isr <= 0)) (PreH10 : (tcbcur <> 0)) (PreH11 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH12 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH13 : (etype = 4)) (PreH14 : (pevent_pre <> 0)) (PreH15 : (isr >= 0)) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (perr_pre <> 0)) (PreH18 : (pd = perr_pre)) (PreH19 : (pe = pevent_pre)) (PreH20 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH21 : (pevent_pre <> 0)) (PreH22 : (pevent_pre = (event_addr (sg) (eid)))) (PreH23 : (0 <= etype)) (PreH24 : (etype <= 255)) ,
  (InsideCritical sg ls_cs )
  **  (interrupt_inv sg (ls_cs.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_cs.(TskState) ) (ls_cs.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (mutex_accept_restore_transition_prop (ls0) (ls_cs) (ls_next) (eid) (e) (cur_tid) (tcbprio) (true)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> tcbcur)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land ecnt_in 65280) (unsigned_last_nbits (tcbprio) (16))))
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = 255) ” 
  &&  “ ((Z.land ecnt_in 255) = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ ((unsigned_last_nbits (isr) (32)) <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ”
  &&  (InsideCritical sg ls_cs )
  **  (interrupt_inv sg (ls_cs.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_cs.(TskState) ) (ls_cs.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (mutex_accept_restore_transition_prop (ls0) (ls_cs) (ls_next) (eid) (e) (cur_tid) (tcbprio) (true)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> tcbcur)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land ecnt_in 65280) (unsigned_last_nbits (tcbprio) (16))))
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSMutexAccept_full_partial_solve_wit_12 := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls_next: UCOS2_Verify_State) (ls_cs: UCOS2_Verify_State) (PreH1 : (tcbprio > (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : ((Z.land ecnt_in 255) = 255)) (PreH4 : (RTrans_C sg ls0 sg ls1 )) (PreH5 : (etype = 4)) (PreH6 : (isr <= 0)) (PreH7 : (tcbcur <> 0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (etype = 4)) (PreH10 : (isr <= 0)) (PreH11 : (tcbcur <> 0)) (PreH12 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (etype = 4)) (PreH15 : (pevent_pre <> 0)) (PreH16 : (isr >= 0)) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (perr_pre <> 0)) (PreH19 : (pd = perr_pre)) (PreH20 : (pe = pevent_pre)) (PreH21 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH22 : (pevent_pre <> 0)) (PreH23 : (pevent_pre = (event_addr (sg) (eid)))) (PreH24 : (0 <= etype)) (PreH25 : (etype <= 255)) ,
  (InsideCritical sg ls_cs )
  **  (interrupt_inv sg (ls_cs.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_cs.(TskState) ) (ls_cs.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (mutex_accept_restore_transition_prop (ls0) (ls_cs) (ls_next) (eid) (e) (cur_tid) (tcbprio) (true)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> tcbcur)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land ecnt_in 65280) (unsigned_last_nbits (tcbprio) (16))))
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ (tcbprio > (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ ((Z.land ecnt_in 255) = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ ((unsigned_last_nbits (isr) (32)) <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ”
  &&  (InsideCritical sg ls_cs )
  **  (interrupt_inv sg (ls_cs.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_cs.(TskState) ) (ls_cs.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (mutex_accept_restore_transition_prop (ls0) (ls_cs) (ls_next) (eid) (e) (cur_tid) (tcbprio) (true)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> tcbcur)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (Z.land ecnt_in 65280) (unsigned_last_nbits (tcbprio) (16))))
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSMutexAccept_full_partial_solve_wit_13 := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (PreH1 : ((Z.land ecnt_in 255) <> 255)) (PreH2 : (RTrans_C sg ls0 sg ls1 )) (PreH3 : (etype = 4)) (PreH4 : (isr <= 0)) (PreH5 : (tcbcur <> 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (etype = 4)) (PreH8 : (isr <= 0)) (PreH9 : (tcbcur <> 0)) (PreH10 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (etype = 4)) (PreH13 : (pevent_pre <> 0)) (PreH14 : (isr >= 0)) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (perr_pre <> 0)) (PreH17 : (pd = perr_pre)) (PreH18 : (pe = pevent_pre)) (PreH19 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = (event_addr (sg) (eid)))) (PreH22 : (0 <= etype)) (PreH23 : (etype <= 255)) ,
  (InsideCritical sg ls1 )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ ((Z.land ecnt_in 255) <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ ((unsigned_last_nbits (isr) (32)) <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ”
  &&  (InsideCritical sg ls1 )
  **  (interrupt_inv sg (ls1.(IntrState) ) )
  **  (event_inv_no_eid sg (ls1.(TskState) ) (ls1.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSMutexAccept_full_partial_solve_wit_14 := 
forall (perr_pre: Z) (pevent_pre: Z) (tcbprio: Z) (tcbcur: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (perr_in: Z) (etype: Z) (pd: Z) (pe: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls_next: UCOS2_Verify_State) (ls_cs: UCOS2_Verify_State) (PreH1 : ((Z.land ecnt_in 255) <> 255)) (PreH2 : (RTrans_C sg ls0 sg ls1 )) (PreH3 : (etype = 4)) (PreH4 : (isr <= 0)) (PreH5 : (tcbcur <> 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (etype = 4)) (PreH8 : (isr <= 0)) (PreH9 : (tcbcur <> 0)) (PreH10 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (etype = 4)) (PreH13 : (pevent_pre <> 0)) (PreH14 : (isr >= 0)) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (perr_pre <> 0)) (PreH17 : (pd = perr_pre)) (PreH18 : (pe = pevent_pre)) (PreH19 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = (event_addr (sg) (eid)))) (PreH22 : (0 <= etype)) (PreH23 : (etype <= 255)) ,
  (InsideCritical sg ls_cs )
  **  (interrupt_inv sg (ls_cs.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_cs.(TskState) ) (ls_cs.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (mutex_accept_restore_transition_prop (ls0) (ls_cs) (ls_next) (eid) (e) (cur_tid) (tcbprio) (false)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ ((Z.land ecnt_in 255) <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ” 
  &&  “ ((unsigned_last_nbits (isr) (32)) <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (isr >= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexAccept_sem (sg) (pevent_pre))))) (observe_mutex_accept_bool)) X ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ”
  &&  (InsideCritical sg ls_cs )
  **  (interrupt_inv sg (ls_cs.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_cs.(TskState) ) (ls_cs.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (mutex_accept_restore_transition_prop (ls0) (ls_cs) (ls_next) (eid) (e) (cur_tid) (tcbprio) (false)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pe eid e )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
.

Definition OSMutexAccept_full_which_implies_wit_1 := 
(
forall (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (pe: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pevent_v: Z) (PreH1 : (pevent_v = pe)) (PreH2 : (pevent_v = (event_addr (sg) (eid)))) ,
  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent_v)  # "os_event" ->ₛ "OSEventType")) (&((pevent_v)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_v)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_Verify_inv sg ls0 )
|--
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pevent_v eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent_v)  # "os_event" ->ₛ "OSEventType")) (&((pevent_v)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_v)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
) \/
(
forall (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (pe: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pevent_v: Z) (PreH1 : (pevent_v = pe)) (PreH2 : (pevent_v = (event_addr (sg) (eid)))) ,
  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent_v)  # "os_event" ->ₛ "OSEventType")) (&((pevent_v)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_v)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_Verify_inv sg ls0 )
|--
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pevent_v eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent_v)  # "os_event" ->ₛ "OSEventType")) (&((pevent_v)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_v)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
).

Definition OSMutexAccept_full_which_implies_wit_1_split_goal_spatial := 
forall (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (pe: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pevent_v: Z) (PreH1 : (pevent_v = pe)) (PreH2 : (pevent_v = (event_addr (sg) (eid)))) ,
  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent_v)  # "os_event" ->ₛ "OSEventType")) (&((pevent_v)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_v)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (UCOS2_Verify_inv sg ls0 )
|--
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  (used_event_rest_no_type_cnt_ptr sg (ls0.(TskState) ) pevent_v eid e )
  **  (event_inv_no_eid sg (ls0.(TskState) ) (ls0.(EventState) ) eid )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent_v)  # "os_event" ->ₛ "OSEventType")) (&((pevent_v)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_v)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
.

Definition OSMutexAccept_full_which_implies_wit_2 := 
(
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
) \/
(
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
).

Definition OSMutexAccept_full_which_implies_wit_2_split_goal_spatial := 
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
.

Definition OSMutexAccept_full_which_implies_wit_3 := 
(
forall (tcbprio: Z) (tcbcur: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype = 4)) (PreH2 : (isr <= 0)) ,
  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
|--
  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ”
  &&  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
) \/
(
forall (tcbprio: Z) (tcbcur: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype = 4)) (PreH2 : (isr <= 0)) ,
  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
|--
  “ (tcbcur <> 0) ”
  &&  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
).

Definition OSMutexAccept_full_which_implies_wit_3_split_goal_1 := 
forall (tcbprio: Z) (tcbcur: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype = 4)) (PreH2 : (isr <= 0)) ,
  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
|--
  “ (tcbcur <> 0) ”
.

Definition OSMutexAccept_full_which_implies_wit_3_split_goal_spatial := 
forall (tcbprio: Z) (tcbcur: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype = 4)) (PreH2 : (isr <= 0)) ,
  (coq_prop (mutex_accept_task_sched_guard_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (etype) (isr) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
|--
  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
.

Definition OSMutexAccept_full_which_implies_wit_4 := 
(
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
  &&  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
) \/
(
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
).

Definition OSMutexAccept_full_which_implies_wit_4_split_goal_spatial := 
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
.

Definition OSMutexAccept_full_which_implies_wit_5 := 
(
forall (tcbprio: Z) (tcbcur: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype = 4)) (PreH2 : (isr <= 0)) (PreH3 : (tcbcur <> 0)) ,
  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
|--
  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (tcbcur <> 0) ”
  &&  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
) \/
(
forall (tcbprio: Z) (tcbcur: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype = 4)) (PreH2 : (isr <= 0)) (PreH3 : (tcbcur <> 0)) ,
  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
|--
  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
).

Definition OSMutexAccept_full_which_implies_wit_5_split_goal_spatial := 
forall (tcbprio: Z) (tcbcur: Z) (etype: Z) (isr: Z) (cur_t: TaskAbstractState) (cur_tid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype = 4)) (PreH2 : (isr <= 0)) (PreH3 : (tcbcur <> 0)) ,
  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (task_inv sg (ls0.(TskState) ) )
  **  (sched_inv sg (ls0.(TskState) ) (ls0.(SchedState) ) )
|--
  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur)) )
  **  (coq_prop (task_runnable_prio_snapshot_prop (sg) ((ls0.(TskState) )) (cur_tid) (cur_t) (tcbcur) (tcbprio)) )
  **  ((&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcbprio)
  **  (used_task_no_prio sg tcbcur cur_tid cur_t )
  **  (task_inv_no_tid sg (ls0.(TskState) ) cur_tid )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur)
  **  (sched_inv_no_tcb_cur sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_prio_field_layout_prop (tcbcur) (&((tcbcur)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
.

Definition OSMutexAccept_full_which_implies_wit_6 := 
(
forall (tcbprio: Z) (ecnt_in: Z) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_cs_2: UCOS2_Verify_State) ,
  (InsideCritical sg ls_cs_2 )
  **  (interrupt_inv sg (ls_cs_2.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_cs_2.(TskState) ) (ls_cs_2.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls_cs_2)) )
|--
  EX (ls_next: UCOS2_Verify_State)  (ls_cs: UCOS2_Verify_State) ,
  (InsideCritical sg ls_cs )
  **  (interrupt_inv sg (ls_cs.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_cs.(TskState) ) (ls_cs.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (mutex_accept_restore_transition_prop (ls0) (ls_cs) (ls_next) (eid) (e) (cur_tid) (tcbprio) (true)) )
) \/
(
forall (tcbprio: Z) (ecnt_in: Z) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_cs_2: UCOS2_Verify_State) ,
  (InsideCritical sg ls_cs_2 )
  **  (interrupt_inv sg (ls_cs_2.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_cs_2.(TskState) ) (ls_cs_2.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls_cs_2)) )
|--
  EX (ls_next: UCOS2_Verify_State)  (ls_cs: UCOS2_Verify_State) ,
  (InsideCritical sg ls_cs )
  **  (interrupt_inv sg (ls_cs.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_cs.(TskState) ) (ls_cs.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (mutex_accept_restore_transition_prop (ls0) (ls_cs) (ls_next) (eid) (e) (cur_tid) (tcbprio) (true)) )
).

Definition OSMutexAccept_full_which_implies_wit_7 := 
(
forall (tcbprio: Z) (ecnt_in: Z) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_cs_2: UCOS2_Verify_State) ,
  (InsideCritical sg ls_cs_2 )
  **  (interrupt_inv sg (ls_cs_2.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_cs_2.(TskState) ) (ls_cs_2.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls_cs_2)) )
|--
  EX (ls_next: UCOS2_Verify_State)  (ls_cs: UCOS2_Verify_State) ,
  (InsideCritical sg ls_cs )
  **  (interrupt_inv sg (ls_cs.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_cs.(TskState) ) (ls_cs.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (mutex_accept_restore_transition_prop (ls0) (ls_cs) (ls_next) (eid) (e) (cur_tid) (tcbprio) (true)) )
) \/
(
forall (tcbprio: Z) (ecnt_in: Z) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_cs_2: UCOS2_Verify_State) ,
  (InsideCritical sg ls_cs_2 )
  **  (interrupt_inv sg (ls_cs_2.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_cs_2.(TskState) ) (ls_cs_2.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls_cs_2)) )
|--
  EX (ls_next: UCOS2_Verify_State)  (ls_cs: UCOS2_Verify_State) ,
  (InsideCritical sg ls_cs )
  **  (interrupt_inv sg (ls_cs.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_cs.(TskState) ) (ls_cs.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (mutex_accept_restore_transition_prop (ls0) (ls_cs) (ls_next) (eid) (e) (cur_tid) (tcbprio) (true)) )
).

Definition OSMutexAccept_full_which_implies_wit_8 := 
(
forall (tcbprio: Z) (ecnt_in: Z) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_cs_2: UCOS2_Verify_State) ,
  (InsideCritical sg ls_cs_2 )
  **  (interrupt_inv sg (ls_cs_2.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_cs_2.(TskState) ) (ls_cs_2.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls_cs_2)) )
|--
  EX (ls_next: UCOS2_Verify_State)  (ls_cs: UCOS2_Verify_State) ,
  (InsideCritical sg ls_cs )
  **  (interrupt_inv sg (ls_cs.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_cs.(TskState) ) (ls_cs.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (mutex_accept_restore_transition_prop (ls0) (ls_cs) (ls_next) (eid) (e) (cur_tid) (tcbprio) (false)) )
) \/
(
forall (tcbprio: Z) (ecnt_in: Z) (cur_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_cs_2: UCOS2_Verify_State) ,
  (InsideCritical sg ls_cs_2 )
  **  (interrupt_inv sg (ls_cs_2.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_cs_2.(TskState) ) (ls_cs_2.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls_cs_2)) )
|--
  EX (ls_next: UCOS2_Verify_State)  (ls_cs: UCOS2_Verify_State) ,
  (InsideCritical sg ls_cs )
  **  (interrupt_inv sg (ls_cs.(IntrState) ) )
  **  (event_inv_no_eid sg (ls_cs.(TskState) ) (ls_cs.(EventState) ) eid )
  **  (coq_prop (event_vaild_cond_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) ))) )
  **  (coq_prop (event_count_value_range_prop (ecnt_in)) )
  **  (coq_prop (mutex_accept_restore_transition_prop (ls0) (ls_cs) (ls_next) (eid) (e) (cur_tid) (tcbprio) (false)) )
).

Module Type VC_Correct.


Axiom proof_of_OSMutexAccept_full_safety_wit_1 : OSMutexAccept_full_safety_wit_1.
Axiom proof_of_OSMutexAccept_full_safety_wit_2 : OSMutexAccept_full_safety_wit_2.
Axiom proof_of_OSMutexAccept_full_safety_wit_3 : OSMutexAccept_full_safety_wit_3.
Axiom proof_of_OSMutexAccept_full_safety_wit_4 : OSMutexAccept_full_safety_wit_4.
Axiom proof_of_OSMutexAccept_full_safety_wit_5 : OSMutexAccept_full_safety_wit_5.
Axiom proof_of_OSMutexAccept_full_return_wit_1 : OSMutexAccept_full_return_wit_1.
Axiom proof_of_OSMutexAccept_full_return_wit_2 : OSMutexAccept_full_return_wit_2.
Axiom proof_of_OSMutexAccept_full_return_wit_3 : OSMutexAccept_full_return_wit_3.
Axiom proof_of_OSMutexAccept_full_return_wit_4 : OSMutexAccept_full_return_wit_4.
Axiom proof_of_OSMutexAccept_full_return_wit_5 : OSMutexAccept_full_return_wit_5.
Axiom proof_of_OSMutexAccept_full_return_wit_6 : OSMutexAccept_full_return_wit_6.
Axiom proof_of_OSMutexAccept_full_return_wit_7 : OSMutexAccept_full_return_wit_7.
Axiom proof_of_OSMutexAccept_full_partial_solve_wit_1_pure : OSMutexAccept_full_partial_solve_wit_1_pure.
Axiom proof_of_OSMutexAccept_full_partial_solve_wit_1 : OSMutexAccept_full_partial_solve_wit_1.
Axiom proof_of_OSMutexAccept_full_partial_solve_wit_2_pure : OSMutexAccept_full_partial_solve_wit_2_pure.
Axiom proof_of_OSMutexAccept_full_partial_solve_wit_2 : OSMutexAccept_full_partial_solve_wit_2.
Axiom proof_of_OSMutexAccept_full_partial_solve_wit_3_pure : OSMutexAccept_full_partial_solve_wit_3_pure.
Axiom proof_of_OSMutexAccept_full_partial_solve_wit_3 : OSMutexAccept_full_partial_solve_wit_3.
Axiom proof_of_OSMutexAccept_full_partial_solve_wit_4_pure : OSMutexAccept_full_partial_solve_wit_4_pure.
Axiom proof_of_OSMutexAccept_full_partial_solve_wit_4 : OSMutexAccept_full_partial_solve_wit_4.
Axiom proof_of_OSMutexAccept_full_partial_solve_wit_5_pure : OSMutexAccept_full_partial_solve_wit_5_pure.
Axiom proof_of_OSMutexAccept_full_partial_solve_wit_5 : OSMutexAccept_full_partial_solve_wit_5.
Axiom proof_of_OSMutexAccept_full_partial_solve_wit_6 : OSMutexAccept_full_partial_solve_wit_6.
Axiom proof_of_OSMutexAccept_full_partial_solve_wit_7 : OSMutexAccept_full_partial_solve_wit_7.
Axiom proof_of_OSMutexAccept_full_partial_solve_wit_8 : OSMutexAccept_full_partial_solve_wit_8.
Axiom proof_of_OSMutexAccept_full_partial_solve_wit_9 : OSMutexAccept_full_partial_solve_wit_9.
Axiom proof_of_OSMutexAccept_full_partial_solve_wit_10 : OSMutexAccept_full_partial_solve_wit_10.
Axiom proof_of_OSMutexAccept_full_partial_solve_wit_11 : OSMutexAccept_full_partial_solve_wit_11.
Axiom proof_of_OSMutexAccept_full_partial_solve_wit_12 : OSMutexAccept_full_partial_solve_wit_12.
Axiom proof_of_OSMutexAccept_full_partial_solve_wit_13 : OSMutexAccept_full_partial_solve_wit_13.
Axiom proof_of_OSMutexAccept_full_partial_solve_wit_14 : OSMutexAccept_full_partial_solve_wit_14.
Axiom proof_of_OSMutexAccept_full_which_implies_wit_1 : OSMutexAccept_full_which_implies_wit_1.
Axiom proof_of_OSMutexAccept_full_which_implies_wit_2 : OSMutexAccept_full_which_implies_wit_2.
Axiom proof_of_OSMutexAccept_full_which_implies_wit_3 : OSMutexAccept_full_which_implies_wit_3.
Axiom proof_of_OSMutexAccept_full_which_implies_wit_4 : OSMutexAccept_full_which_implies_wit_4.
Axiom proof_of_OSMutexAccept_full_which_implies_wit_5 : OSMutexAccept_full_which_implies_wit_5.
Axiom proof_of_OSMutexAccept_full_which_implies_wit_6 : OSMutexAccept_full_which_implies_wit_6.
Axiom proof_of_OSMutexAccept_full_which_implies_wit_7 : OSMutexAccept_full_which_implies_wit_7.
Axiom proof_of_OSMutexAccept_full_which_implies_wit_8 : OSMutexAccept_full_which_implies_wit_8.

End VC_Correct.
