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
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.mutex_func_sem.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.mutex_create_spec.
Local Open Scope sac.

(*----- Function OSMutexCreate_full -----*)

Definition OSMutexCreate_full_safety_wit_1 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (prio_pre = prio_in)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : (pd = perr_pre)) (PreH5 : (perr_pre <> 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH10 : (freelist_in <> 0)) ,
  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_full_safety_wit_2 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (prio_pre = prio_in)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : (pd = perr_pre)) (PreH5 : (perr_pre <> 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH10 : (freelist_in = 0)) ,
  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_full_safety_wit_3 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (prio_pre >= 63)) (PreH2 : (prio_pre <> 255)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (pd = perr_pre)) (PreH7 : (perr_pre <> 0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH12 : (freelist_in <> 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> 42)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_full_safety_wit_4 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (prio_pre >= 63)) (PreH2 : (prio_pre <> 255)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (pd = perr_pre)) (PreH7 : (perr_pre <> 0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH12 : (freelist_in = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> 42)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_full_safety_wit_5 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr > 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (pd = perr_pre)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (0 <= isr)) (PreH13 : (isr <= 255)) (PreH14 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH15 : (freelist_in <> 0)) ,
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> 16)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_full_safety_wit_6 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr > 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (pd = perr_pre)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (0 <= isr)) (PreH13 : (isr <= 255)) (PreH14 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH15 : (freelist_in = 0)) ,
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> 16)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_full_safety_wit_7 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr > 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (pd = perr_pre)) (PreH9 : (perr_pre <> 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH14 : (freelist_in <> 0)) ,
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> 16)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_full_safety_wit_8 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr > 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (pd = perr_pre)) (PreH9 : (perr_pre <> 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH14 : (freelist_in = 0)) ,
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> 16)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_full_safety_wit_9 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre = 255)) (PreH2 : (RTrans_C sg ls0 sg ls1 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (prio_pre < 63)) (PreH7 : (prio_pre <> 255)) (PreH8 : (prio_pre = prio_in)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : (pd = perr_pre)) (PreH12 : (perr_pre <> 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH17 : (freelist_in <> 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ False ”
.

Definition OSMutexCreate_full_safety_wit_10 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre = 255)) (PreH2 : (RTrans_C sg ls0 sg ls1 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (prio_pre < 63)) (PreH7 : (prio_pre <> 255)) (PreH8 : (prio_pre = prio_in)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : (pd = perr_pre)) (PreH12 : (perr_pre <> 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH17 : (freelist_in = 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ False ”
.

Definition OSMutexCreate_full_safety_wit_11 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (RTrans_C sg ls0 sg ls1 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (prio_pre = 255)) (PreH7 : (prio_pre = prio_in)) (PreH8 : (0 <= prio_in)) (PreH9 : (prio_in <= 255)) (PreH10 : (pd = perr_pre)) (PreH11 : (perr_pre <> 0)) (PreH12 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH16 : (freelist_in <> 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ False ”
.

Definition OSMutexCreate_full_safety_wit_12 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (RTrans_C sg ls0 sg ls1 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (prio_pre = 255)) (PreH7 : (prio_pre = prio_in)) (PreH8 : (0 <= prio_in)) (PreH9 : (prio_in <= 255)) (PreH10 : (pd = perr_pre)) (PreH11 : (perr_pre <> 0)) (PreH12 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH16 : (freelist_in = 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ False ”
.

Definition OSMutexCreate_full_safety_wit_13 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (RTrans_C sg ls0 sg ls1 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (prio_pre < 63)) (PreH7 : (prio_pre <> 255)) (PreH8 : (prio_pre = prio_in)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : (pd = perr_pre)) (PreH12 : (perr_pre <> 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH17 : (freelist_in = 0)) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (Znth (prio_in) (prioL_in) (0)))
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_full_safety_wit_14 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (RTrans_C sg ls0 sg ls1 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (prio_pre < 63)) (PreH7 : (prio_pre <> 255)) (PreH8 : (prio_pre = prio_in)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : (pd = perr_pre)) (PreH12 : (perr_pre <> 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH17 : (freelist_in <> 0)) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (Znth (prio_in) (prioL_in) (0)))
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_full_safety_wit_15 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (ls1_2: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_2 sg ls_post )) (PreH2 : ((Znth (prio_in) (prioL_in) (0)) <> 0)) (PreH3 : (prio_pre <> 255)) (PreH4 : (RTrans_C sg ls0 sg ls1 )) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (isr <= 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (prio_pre < 63)) (PreH9 : (prio_pre <> 255)) (PreH10 : (prio_pre = prio_in)) (PreH11 : (0 <= prio_in)) (PreH12 : (prio_in <= 255)) (PreH13 : (pd = perr_pre)) (PreH14 : (perr_pre <> 0)) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (0 <= isr)) (PreH17 : (isr <= 255)) (PreH18 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH19 : (freelist_in = 0)) ,
  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 40)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_full_safety_wit_16 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (ls1_2: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_2 sg ls_post )) (PreH2 : ((Znth (prio_in) (prioL_in) (0)) <> 0)) (PreH3 : (prio_pre <> 255)) (PreH4 : (RTrans_C sg ls0 sg ls1 )) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (isr <= 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (prio_pre < 63)) (PreH9 : (prio_pre <> 255)) (PreH10 : (prio_pre = prio_in)) (PreH11 : (0 <= prio_in)) (PreH12 : (prio_in <= 255)) (PreH13 : (pd = perr_pre)) (PreH14 : (perr_pre <> 0)) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (0 <= isr)) (PreH17 : (isr <= 255)) (PreH18 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH19 : (freelist_in <> 0)) ,
  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 40)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_full_safety_wit_17 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH2 : (prio_pre <> 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre < 63)) (PreH8 : (prio_pre <> 255)) (PreH9 : (prio_pre = prio_in)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : (pd = perr_pre)) (PreH13 : (perr_pre <> 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH18 : (freelist_in = 0)) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (Znth (prio_in) (prioL_in) (0)))
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OSMutexCreate_full_safety_wit_18 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH2 : (prio_pre <> 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre < 63)) (PreH8 : (prio_pre <> 255)) (PreH9 : (prio_pre = prio_in)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : (pd = perr_pre)) (PreH13 : (perr_pre <> 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH18 : (freelist_in <> 0)) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (Znth (prio_in) (prioL_in) (0)))
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OSMutexCreate_full_safety_wit_19_disabled_empty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH2 : (RTrans_C sg ls0 sg ls1_2 )) (PreH3 : (0 <= prio_in)) (PreH4 : (prio_in <= 255)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (0 <= isr)) (PreH7 : (isr <= 255)) (PreH8 : (isr <= 0)) (PreH9 : (pd <> 0)) (PreH10 : (prio_in = 255)) (PreH11 : (prio_pre = 255)) (PreH12 : (RTrans_C sg ls0 sg ls1 )) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (isr <= 0)) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (prio_pre = 255)) (PreH17 : (prio_pre = prio_in)) (PreH18 : (0 <= prio_in)) (PreH19 : (prio_in <= 255)) (PreH20 : (pd = perr_pre)) (PreH21 : (perr_pre <> 0)) (PreH22 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH23 : (0 <= isr)) (PreH24 : (isr <= 255)) (PreH25 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH26 : (freelist_in = 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_full_safety_wit_20_disabled_nonempty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH2 : (RTrans_C sg ls0 sg ls1_2 )) (PreH3 : (0 <= prio_in)) (PreH4 : (prio_in <= 255)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (0 <= isr)) (PreH7 : (isr <= 255)) (PreH8 : (isr <= 0)) (PreH9 : (pd <> 0)) (PreH10 : (prio_in = 255)) (PreH11 : (prio_pre = 255)) (PreH12 : (RTrans_C sg ls0 sg ls1 )) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (isr <= 0)) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (prio_pre = 255)) (PreH17 : (prio_pre = prio_in)) (PreH18 : (0 <= prio_in)) (PreH19 : (prio_in <= 255)) (PreH20 : (pd = perr_pre)) (PreH21 : (perr_pre <> 0)) (PreH22 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH23 : (0 <= isr)) (PreH24 : (isr <= 255)) (PreH25 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH26 : (freelist_in <> 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_full_safety_wit_21_enabled_nonempty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH2 : (RTrans_C sg ls0 sg ls1_2 )) (PreH3 : (0 <= prio_in)) (PreH4 : (prio_in <= 255)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (0 <= isr)) (PreH7 : (isr <= 255)) (PreH8 : (isr <= 0)) (PreH9 : (pd <> 0)) (PreH10 : (prio_in <> 255)) (PreH11 : (0 <= prio_in)) (PreH12 : (prio_in < 64)) (PreH13 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH14 : (prio_pre <> 255)) (PreH15 : (RTrans_C sg ls0 sg ls1 )) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (prio_pre < 63)) (PreH20 : (prio_pre <> 255)) (PreH21 : (prio_pre = prio_in)) (PreH22 : (0 <= prio_in)) (PreH23 : (prio_in <= 255)) (PreH24 : (pd = perr_pre)) (PreH25 : (perr_pre <> 0)) (PreH26 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH27 : (0 <= isr)) (PreH28 : (isr <= 255)) (PreH29 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH30 : (freelist_in <> 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_full_safety_wit_22_enabled_empty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH2 : (RTrans_C sg ls0 sg ls1_2 )) (PreH3 : (0 <= prio_in)) (PreH4 : (prio_in <= 255)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (0 <= isr)) (PreH7 : (isr <= 255)) (PreH8 : (isr <= 0)) (PreH9 : (pd <> 0)) (PreH10 : (prio_in <> 255)) (PreH11 : (0 <= prio_in)) (PreH12 : (prio_in < 64)) (PreH13 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH14 : (prio_pre <> 255)) (PreH15 : (RTrans_C sg ls0 sg ls1 )) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (prio_pre < 63)) (PreH20 : (prio_pre <> 255)) (PreH21 : (prio_pre = prio_in)) (PreH22 : (0 <= prio_in)) (PreH23 : (prio_in <= 255)) (PreH24 : (pd = perr_pre)) (PreH25 : (perr_pre <> 0)) (PreH26 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH27 : (0 <= isr)) (PreH28 : (isr <= 255)) (PreH29 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH30 : (freelist_in = 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_full_safety_wit_23_disabled_empty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (freelist_in <> 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH3 : (RTrans_C sg ls0 sg ls1_2 )) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : (isr <= 0)) (PreH10 : (pd <> 0)) (PreH11 : (prio_in = 255)) (PreH12 : (prio_pre = 255)) (PreH13 : (RTrans_C sg ls0 sg ls1 )) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (isr <= 0)) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (prio_pre = 255)) (PreH18 : (prio_pre = prio_in)) (PreH19 : (0 <= prio_in)) (PreH20 : (prio_in <= 255)) (PreH21 : (pd = perr_pre)) (PreH22 : (perr_pre <> 0)) (PreH23 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH24 : (0 <= isr)) (PreH25 : (isr <= 255)) (PreH26 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH27 : (freelist_in = 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ False ”
.

Definition OSMutexCreate_full_safety_wit_24_disabled_nonempty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (freelist_in = 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH3 : (RTrans_C sg ls0 sg ls1_2 )) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : (isr <= 0)) (PreH10 : (pd <> 0)) (PreH11 : (prio_in = 255)) (PreH12 : (prio_pre = 255)) (PreH13 : (RTrans_C sg ls0 sg ls1 )) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (isr <= 0)) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (prio_pre = 255)) (PreH18 : (prio_pre = prio_in)) (PreH19 : (0 <= prio_in)) (PreH20 : (prio_in <= 255)) (PreH21 : (pd = perr_pre)) (PreH22 : (perr_pre <> 0)) (PreH23 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH24 : (0 <= isr)) (PreH25 : (isr <= 255)) (PreH26 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH27 : (freelist_in <> 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ False ”
.

Definition OSMutexCreate_full_safety_wit_25_enabled_nonempty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (freelist_in = 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH3 : (RTrans_C sg ls0 sg ls1_2 )) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : (isr <= 0)) (PreH10 : (pd <> 0)) (PreH11 : (prio_in <> 255)) (PreH12 : (0 <= prio_in)) (PreH13 : (prio_in < 64)) (PreH14 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH15 : (prio_pre <> 255)) (PreH16 : (RTrans_C sg ls0 sg ls1 )) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (isr <= 0)) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (prio_pre < 63)) (PreH21 : (prio_pre <> 255)) (PreH22 : (prio_pre = prio_in)) (PreH23 : (0 <= prio_in)) (PreH24 : (prio_in <= 255)) (PreH25 : (pd = perr_pre)) (PreH26 : (perr_pre <> 0)) (PreH27 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH28 : (0 <= isr)) (PreH29 : (isr <= 255)) (PreH30 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH31 : (freelist_in <> 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ False ”
.

Definition OSMutexCreate_full_safety_wit_26_enabled_empty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (freelist_in <> 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH3 : (RTrans_C sg ls0 sg ls1_2 )) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : (isr <= 0)) (PreH10 : (pd <> 0)) (PreH11 : (prio_in <> 255)) (PreH12 : (0 <= prio_in)) (PreH13 : (prio_in < 64)) (PreH14 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH15 : (prio_pre <> 255)) (PreH16 : (RTrans_C sg ls0 sg ls1 )) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (isr <= 0)) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (prio_pre < 63)) (PreH21 : (prio_pre <> 255)) (PreH22 : (prio_pre = prio_in)) (PreH23 : (0 <= prio_in)) (PreH24 : (prio_in <= 255)) (PreH25 : (pd = perr_pre)) (PreH26 : (perr_pre <> 0)) (PreH27 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH28 : (0 <= isr)) (PreH29 : (isr <= 255)) (PreH30 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH31 : (freelist_in = 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ False ”
.

Definition OSMutexCreate_full_safety_wit_27_disabled_empty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (freelist_in = 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH4 : (RTrans_C sg ls0 sg ls1_2 )) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (isr <= 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_in = 255)) (PreH13 : (prio_pre = 255)) (PreH14 : (RTrans_C sg ls0 sg ls1 )) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (isr <= 0)) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (prio_pre = 255)) (PreH19 : (prio_pre = prio_in)) (PreH20 : (0 <= prio_in)) (PreH21 : (prio_in <= 255)) (PreH22 : (pd = perr_pre)) (PreH23 : (perr_pre <> 0)) (PreH24 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH25 : (0 <= isr)) (PreH26 : (isr <= 255)) (PreH27 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH28 : (freelist_in = 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ False ”
.

Definition OSMutexCreate_full_safety_wit_28_enabled_empty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre = 255)) (PreH2 : (freelist_in = 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH4 : (RTrans_C sg ls0 sg ls1_2 )) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (isr <= 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH16 : (prio_pre <> 255)) (PreH17 : (RTrans_C sg ls0 sg ls1 )) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (isr <= 0)) (PreH20 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH21 : (prio_pre < 63)) (PreH22 : (prio_pre <> 255)) (PreH23 : (prio_pre = prio_in)) (PreH24 : (0 <= prio_in)) (PreH25 : (prio_in <= 255)) (PreH26 : (pd = perr_pre)) (PreH27 : (perr_pre <> 0)) (PreH28 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH29 : (0 <= isr)) (PreH30 : (isr <= 255)) (PreH31 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH32 : (freelist_in = 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ False ”
.

Definition OSMutexCreate_full_safety_wit_29_enabled_empty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (freelist_in = 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH4 : (RTrans_C sg ls0 sg ls1_2 )) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (isr <= 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH16 : (prio_pre <> 255)) (PreH17 : (RTrans_C sg ls0 sg ls1 )) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (isr <= 0)) (PreH20 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH21 : (prio_pre < 63)) (PreH22 : (prio_pre <> 255)) (PreH23 : (prio_pre = prio_in)) (PreH24 : (0 <= prio_in)) (PreH25 : (prio_in <= 255)) (PreH26 : (pd = perr_pre)) (PreH27 : (perr_pre <> 0)) (PreH28 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH29 : (0 <= isr)) (PreH30 : (isr <= 255)) (PreH31 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH32 : (freelist_in = 0)) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> 1)
  **  (store_priotbl_list_missing_i sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) prio_in )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_full_safety_wit_30_disabled_nonempty := 
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in = 255)) (PreH14 : (prio_pre = 255)) (PreH15 : (RTrans_C sg ls0 sg ls1 )) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (prio_pre = 255)) (PreH20 : (prio_pre = prio_in)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in <= 255)) (PreH23 : (pd = perr_pre)) (PreH24 : (perr_pre <> 0)) (PreH25 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH26 : (0 <= isr)) (PreH27 : (isr <= 255)) (PreH28 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH29 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  (mutex_create_wait_table_uninitialized freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ ((signed_last_nbits ((prio_pre * (2^8) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((prio_pre * (2^8) )) (32))) ” 
  &&  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in = 255)) (PreH14 : (prio_pre = 255)) (PreH15 : (RTrans_C sg ls0 sg ls1 )) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (prio_pre = 255)) (PreH20 : (prio_pre = prio_in)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in <= 255)) (PreH23 : (pd = perr_pre)) (PreH24 : (perr_pre <> 0)) (PreH25 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH26 : (0 <= isr)) (PreH27 : (isr <= 255)) (PreH28 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH29 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  (mutex_create_wait_table_uninitialized freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ ((signed_last_nbits ((prio_pre * (2^8) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((prio_pre * (2^8) )) (32))) ” 
  &&  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
).

Definition OSMutexCreate_full_safety_wit_30_disabled_nonempty_split_goal_1 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in = 255)) (PreH14 : (prio_pre = 255)) (PreH15 : (RTrans_C sg ls0 sg ls1 )) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (prio_pre = 255)) (PreH20 : (prio_pre = prio_in)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in <= 255)) (PreH23 : (pd = perr_pre)) (PreH24 : (perr_pre <> 0)) (PreH25 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH26 : (0 <= isr)) (PreH27 : (isr <= 255)) (PreH28 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH29 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  (mutex_create_wait_table_uninitialized freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ ((signed_last_nbits ((prio_pre * (2^8) )) (32)) <= INT_MAX) ”
.

Definition OSMutexCreate_full_safety_wit_30_disabled_nonempty_split_goal_2 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in = 255)) (PreH14 : (prio_pre = 255)) (PreH15 : (RTrans_C sg ls0 sg ls1 )) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (prio_pre = 255)) (PreH20 : (prio_pre = prio_in)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in <= 255)) (PreH23 : (pd = perr_pre)) (PreH24 : (perr_pre <> 0)) (PreH25 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH26 : (0 <= isr)) (PreH27 : (isr <= 255)) (PreH28 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH29 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  (mutex_create_wait_table_uninitialized freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ ((INT_MIN) <= (signed_last_nbits ((prio_pre * (2^8) )) (32))) ”
.

Definition OSMutexCreate_full_safety_wit_30_disabled_nonempty_split_goal_3 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in = 255)) (PreH14 : (prio_pre = 255)) (PreH15 : (RTrans_C sg ls0 sg ls1 )) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (prio_pre = 255)) (PreH20 : (prio_pre = prio_in)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in <= 255)) (PreH23 : (pd = perr_pre)) (PreH24 : (perr_pre <> 0)) (PreH25 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH26 : (0 <= isr)) (PreH27 : (isr <= 255)) (PreH28 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH29 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  (mutex_create_wait_table_uninitialized freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (8 <= 31) ”
.

Definition OSMutexCreate_full_safety_wit_30_disabled_nonempty_split_goal_4 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in = 255)) (PreH14 : (prio_pre = 255)) (PreH15 : (RTrans_C sg ls0 sg ls1 )) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (prio_pre = 255)) (PreH20 : (prio_pre = prio_in)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in <= 255)) (PreH23 : (pd = perr_pre)) (PreH24 : (perr_pre <> 0)) (PreH25 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH26 : (0 <= isr)) (PreH27 : (isr <= 255)) (PreH28 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH29 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  (mutex_create_wait_table_uninitialized freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (0 <= 8) ”
.

Definition OSMutexCreate_full_safety_wit_31_enabled_nonempty := 
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in <> 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in < 64)) (PreH16 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH17 : (prio_pre <> 255)) (PreH18 : (RTrans_C sg ls0 sg ls1 )) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (isr <= 0)) (PreH21 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (pd = perr_pre)) (PreH28 : (perr_pre <> 0)) (PreH29 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH30 : (0 <= isr)) (PreH31 : (isr <= 255)) (PreH32 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH33 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  (mutex_create_wait_table_uninitialized freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ ((signed_last_nbits ((prio_pre * (2^8) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((prio_pre * (2^8) )) (32))) ” 
  &&  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in <> 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in < 64)) (PreH16 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH17 : (prio_pre <> 255)) (PreH18 : (RTrans_C sg ls0 sg ls1 )) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (isr <= 0)) (PreH21 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (pd = perr_pre)) (PreH28 : (perr_pre <> 0)) (PreH29 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH30 : (0 <= isr)) (PreH31 : (isr <= 255)) (PreH32 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH33 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  (mutex_create_wait_table_uninitialized freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ ((signed_last_nbits ((prio_pre * (2^8) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((prio_pre * (2^8) )) (32))) ” 
  &&  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
).

Definition OSMutexCreate_full_safety_wit_31_enabled_nonempty_split_goal_1 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in <> 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in < 64)) (PreH16 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH17 : (prio_pre <> 255)) (PreH18 : (RTrans_C sg ls0 sg ls1 )) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (isr <= 0)) (PreH21 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (pd = perr_pre)) (PreH28 : (perr_pre <> 0)) (PreH29 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH30 : (0 <= isr)) (PreH31 : (isr <= 255)) (PreH32 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH33 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  (mutex_create_wait_table_uninitialized freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ ((signed_last_nbits ((prio_pre * (2^8) )) (32)) <= INT_MAX) ”
.

Definition OSMutexCreate_full_safety_wit_31_enabled_nonempty_split_goal_2 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in <> 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in < 64)) (PreH16 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH17 : (prio_pre <> 255)) (PreH18 : (RTrans_C sg ls0 sg ls1 )) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (isr <= 0)) (PreH21 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (pd = perr_pre)) (PreH28 : (perr_pre <> 0)) (PreH29 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH30 : (0 <= isr)) (PreH31 : (isr <= 255)) (PreH32 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH33 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  (mutex_create_wait_table_uninitialized freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ ((INT_MIN) <= (signed_last_nbits ((prio_pre * (2^8) )) (32))) ”
.

Definition OSMutexCreate_full_safety_wit_31_enabled_nonempty_split_goal_3 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in <> 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in < 64)) (PreH16 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH17 : (prio_pre <> 255)) (PreH18 : (RTrans_C sg ls0 sg ls1 )) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (isr <= 0)) (PreH21 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (pd = perr_pre)) (PreH28 : (perr_pre <> 0)) (PreH29 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH30 : (0 <= isr)) (PreH31 : (isr <= 255)) (PreH32 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH33 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  (mutex_create_wait_table_uninitialized freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (8 <= 31) ”
.

Definition OSMutexCreate_full_safety_wit_31_enabled_nonempty_split_goal_4 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in <> 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in < 64)) (PreH16 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH17 : (prio_pre <> 255)) (PreH18 : (RTrans_C sg ls0 sg ls1 )) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (isr <= 0)) (PreH21 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (pd = perr_pre)) (PreH28 : (perr_pre <> 0)) (PreH29 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH30 : (0 <= isr)) (PreH31 : (isr <= 255)) (PreH32 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH33 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  (mutex_create_wait_table_uninitialized freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (0 <= 8) ”
.

Definition OSMutexCreate_full_safety_wit_32_disabled_nonempty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in = 255)) (PreH14 : (prio_pre = 255)) (PreH15 : (RTrans_C sg ls0 sg ls1 )) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (prio_pre = 255)) (PreH20 : (prio_pre = prio_in)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in <= 255)) (PreH23 : (pd = perr_pre)) (PreH24 : (perr_pre <> 0)) (PreH25 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH26 : (0 <= isr)) (PreH27 : (isr <= 255)) (PreH28 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH29 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255))
  **  (mutex_create_wait_table_uninitialized freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_full_safety_wit_33_enabled_nonempty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in <> 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in < 64)) (PreH16 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH17 : (prio_pre <> 255)) (PreH18 : (RTrans_C sg ls0 sg ls1 )) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (isr <= 0)) (PreH21 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (pd = perr_pre)) (PreH28 : (perr_pre <> 0)) (PreH29 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH30 : (0 <= isr)) (PreH31 : (isr <= 255)) (PreH32 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH33 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255))
  **  (mutex_create_wait_table_uninitialized freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexCreate_full_entail_wit_1_disabled_empty := 
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (PreH1 : (prio_in = 255)) (PreH2 : (prio_pre = 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre = 255)) (PreH8 : (prio_pre = prio_in)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : (pd = perr_pre)) (PreH12 : (perr_pre <> 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH17 : (freelist_in = 0)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  (InsideCritical sg ls1_3 )
  **  (mutex_create_head_open_inv sg ls1_3 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_3.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  EX (ls1_2: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (PreH1 : (prio_in = 255)) (PreH2 : (prio_pre = 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre = 255)) (PreH8 : (prio_pre = prio_in)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : (pd = perr_pre)) (PreH12 : (perr_pre <> 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH17 : (freelist_in = 0)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  (InsideCritical sg ls1_3 )
  **  (mutex_create_head_open_inv sg ls1_3 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_3.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  EX (ls1_2: UCOS2_Verify_State) ,
  “ (perr_pre = pd) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexCreate_full_entail_wit_2_disabled_nonempty := 
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (PreH1 : (prio_in = 255)) (PreH2 : (prio_pre = 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre = 255)) (PreH8 : (prio_pre = prio_in)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : (pd = perr_pre)) (PreH12 : (perr_pre <> 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH17 : (freelist_in <> 0)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  (InsideCritical sg ls1_3 )
  **  (mutex_create_head_open_inv sg ls1_3 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_3.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  EX (ls1_2: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (PreH1 : (prio_in = 255)) (PreH2 : (prio_pre = 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre = 255)) (PreH8 : (prio_pre = prio_in)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : (pd = perr_pre)) (PreH12 : (perr_pre <> 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH17 : (freelist_in <> 0)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  (InsideCritical sg ls1_3 )
  **  (mutex_create_head_open_inv sg ls1_3 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_3.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  EX (ls1_2: UCOS2_Verify_State) ,
  “ (perr_pre = pd) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
).

Definition OSMutexCreate_full_entail_wit_3_enabled_nonempty := 
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (PreH1 : (prio_in <> 255)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in < 64)) (PreH4 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH5 : (prio_pre <> 255)) (PreH6 : (RTrans_C sg ls0 sg ls1 )) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (isr <= 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (prio_pre < 63)) (PreH11 : (prio_pre <> 255)) (PreH12 : (prio_pre = prio_in)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in <= 255)) (PreH15 : (pd = perr_pre)) (PreH16 : (perr_pre <> 0)) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (0 <= isr)) (PreH19 : (isr <= 255)) (PreH20 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH21 : (freelist_in <> 0)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_3 )
  **  (mutex_create_head_open_inv sg ls1_3 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_3.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  EX (ls1_2: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (PreH1 : (prio_in <> 255)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in < 64)) (PreH4 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH5 : (prio_pre <> 255)) (PreH6 : (RTrans_C sg ls0 sg ls1 )) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (isr <= 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (prio_pre < 63)) (PreH11 : (prio_pre <> 255)) (PreH12 : (prio_pre = prio_in)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in <= 255)) (PreH15 : (pd = perr_pre)) (PreH16 : (perr_pre <> 0)) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (0 <= isr)) (PreH19 : (isr <= 255)) (PreH20 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH21 : (freelist_in <> 0)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_3 )
  **  (mutex_create_head_open_inv sg ls1_3 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_3.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  EX (ls1_2: UCOS2_Verify_State) ,
  “ (perr_pre = pd) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
).

Definition OSMutexCreate_full_entail_wit_4_enabled_empty := 
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (PreH1 : (prio_in <> 255)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in < 64)) (PreH4 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH5 : (prio_pre <> 255)) (PreH6 : (RTrans_C sg ls0 sg ls1 )) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (isr <= 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (prio_pre < 63)) (PreH11 : (prio_pre <> 255)) (PreH12 : (prio_pre = prio_in)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in <= 255)) (PreH15 : (pd = perr_pre)) (PreH16 : (perr_pre <> 0)) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (0 <= isr)) (PreH19 : (isr <= 255)) (PreH20 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH21 : (freelist_in = 0)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_3 )
  **  (mutex_create_head_open_inv sg ls1_3 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_3.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  EX (ls1_2: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (PreH1 : (prio_in <> 255)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in < 64)) (PreH4 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH5 : (prio_pre <> 255)) (PreH6 : (RTrans_C sg ls0 sg ls1 )) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (isr <= 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (prio_pre < 63)) (PreH11 : (prio_pre <> 255)) (PreH12 : (prio_pre = prio_in)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in <= 255)) (PreH15 : (pd = perr_pre)) (PreH16 : (perr_pre <> 0)) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (0 <= isr)) (PreH19 : (isr <= 255)) (PreH20 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH21 : (freelist_in = 0)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_3 )
  **  (mutex_create_head_open_inv sg ls1_3 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_3.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  EX (ls1_2: UCOS2_Verify_State) ,
  “ (perr_pre = pd) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexCreate_full_entail_wit_5_disabled_empty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre = 255)) (PreH2 : (freelist_in = 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH4 : (RTrans_C sg ls0 sg ls1_2 )) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (isr <= 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_in = 255)) (PreH13 : (prio_pre = 255)) (PreH14 : (RTrans_C sg ls0 sg ls1 )) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (isr <= 0)) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (prio_pre = 255)) (PreH19 : (prio_pre = prio_in)) (PreH20 : (0 <= prio_in)) (PreH21 : (prio_in <= 255)) (PreH22 : (pd = perr_pre)) (PreH23 : (perr_pre <> 0)) (PreH24 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH25 : (0 <= isr)) (PreH26 : (isr <= 255)) (PreH27 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH28 : (freelist_in = 0)) ,
  (store_priotbl_list sg prioL_in )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  EX (ls1_3: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_3 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (freelist_in = 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (freelist_in = 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (InsideCritical sg ls1_3 )
  **  (mutex_create_head_open_inv sg ls1_3 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_3.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_entail_wit_6_enabled_empty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (freelist_in = 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH4 : (RTrans_C sg ls0 sg ls1_2 )) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (isr <= 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH16 : (prio_pre <> 255)) (PreH17 : (RTrans_C sg ls0 sg ls1 )) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (isr <= 0)) (PreH20 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH21 : (prio_pre < 63)) (PreH22 : (prio_pre <> 255)) (PreH23 : (prio_pre = prio_in)) (PreH24 : (0 <= prio_in)) (PreH25 : (prio_in <= 255)) (PreH26 : (pd = perr_pre)) (PreH27 : (perr_pre <> 0)) (PreH28 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH29 : (0 <= isr)) (PreH30 : (isr <= 255)) (PreH31 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH32 : (freelist_in = 0)) ,
  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (store_priotbl_list sg prioL_in )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
|--
  EX (ls1_3: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_3 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (freelist_in = 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (freelist_in = 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (InsideCritical sg ls1_3 )
  **  (mutex_create_head_open_inv sg ls1_3 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_3.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_entail_wit_7_enabled_nonempty := 
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_3: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in <> 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in < 64)) (PreH16 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH17 : (prio_pre <> 255)) (PreH18 : (RTrans_C sg ls0 sg ls1 )) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (isr <= 0)) (PreH21 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (pd = perr_pre)) (PreH28 : (perr_pre <> 0)) (PreH29 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH30 : (0 <= isr)) (PreH31 : (isr <= 255)) (PreH32 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH33 : (freelist_in <> 0)) ,
  (OutsideCritical sg ls_post_3 )
  **  (UCOS2_Verify_inv sg ls_post_3 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_3) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  EX (perr_v: Z)  (ls_post_2: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls_post_2)) (return (freelist_in)) X ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in = (event_addr (sg) (eid))) ” 
  &&  “ (next_in = (free_event_head (sg) (free_rest))) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (GTrans_C sg ls1_3 sg ls_post ) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_v)
  **  (OutsideCritical sg ls_post_2 )
  **  (UCOS2_Verify_inv sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_3: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in <> 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in < 64)) (PreH16 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH17 : (prio_pre <> 255)) (PreH18 : (RTrans_C sg ls0 sg ls1 )) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (isr <= 0)) (PreH21 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (pd = perr_pre)) (PreH28 : (perr_pre <> 0)) (PreH29 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH30 : (0 <= isr)) (PreH31 : (isr <= 255)) (PreH32 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH33 : (freelist_in <> 0)) ,
  (OutsideCritical sg ls_post_3 )
  **  (UCOS2_Verify_inv sg ls_post_3 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_3) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  EX (ls_post_2: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls_post_2)) (return (freelist_in)) X ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in = (event_addr (sg) (eid))) ” 
  &&  “ (next_in = (free_event_head (sg) (free_rest))) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (GTrans_C sg ls1_3 sg ls_post ) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (OutsideCritical sg ls_post_2 )
  **  (UCOS2_Verify_inv sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexCreate_full_entail_wit_8_disabled_nonempty := 
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_3: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in = 255)) (PreH14 : (prio_pre = 255)) (PreH15 : (RTrans_C sg ls0 sg ls1 )) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (prio_pre = 255)) (PreH20 : (prio_pre = prio_in)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in <= 255)) (PreH23 : (pd = perr_pre)) (PreH24 : (perr_pre <> 0)) (PreH25 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH26 : (0 <= isr)) (PreH27 : (isr <= 255)) (PreH28 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH29 : (freelist_in <> 0)) ,
  (OutsideCritical sg ls_post_3 )
  **  (UCOS2_Verify_inv sg ls_post_3 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_3) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  EX (perr_v: Z)  (ls_post_2: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls_post_2)) (return (freelist_in)) X ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in = (event_addr (sg) (eid))) ” 
  &&  “ (next_in = (free_event_head (sg) (free_rest))) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (GTrans_C sg ls1_3 sg ls_post ) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_v)
  **  (OutsideCritical sg ls_post_2 )
  **  (UCOS2_Verify_inv sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_3: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in = 255)) (PreH14 : (prio_pre = 255)) (PreH15 : (RTrans_C sg ls0 sg ls1 )) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (prio_pre = 255)) (PreH20 : (prio_pre = prio_in)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in <= 255)) (PreH23 : (pd = perr_pre)) (PreH24 : (perr_pre <> 0)) (PreH25 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH26 : (0 <= isr)) (PreH27 : (isr <= 255)) (PreH28 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH29 : (freelist_in <> 0)) ,
  (OutsideCritical sg ls_post_3 )
  **  (UCOS2_Verify_inv sg ls_post_3 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_3) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  EX (ls_post_2: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls_post_2)) (return (freelist_in)) X ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in = (event_addr (sg) (eid))) ” 
  &&  “ (next_in = (free_event_head (sg) (free_rest))) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (GTrans_C sg ls1_3 sg ls_post ) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (OutsideCritical sg ls_post_2 )
  **  (UCOS2_Verify_inv sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexCreate_full_return_wit_1_enabled_nonempty := 
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (ls_post_3: UCOS2_Verify_State) (PreH1 : (safeExec (LastSeen (ls_post_3)) (return (freelist_in)) X )) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (0 <= isr)) (PreH6 : (isr <= 255)) (PreH7 : (isr <= 0)) (PreH8 : (freelist_in <> 0)) (PreH9 : (freelist_in = (event_addr (sg) (eid)))) (PreH10 : (next_in = (free_event_head (sg) (free_rest)))) (PreH11 : (pd <> 0)) (PreH12 : (GTrans_C sg ls1_3 sg ls_post_2 )) (PreH13 : (freelist_in <> 0)) (PreH14 : (freelist_in <> 0)) (PreH15 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH16 : (RTrans_C sg ls0 sg ls1_2 )) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (0 <= isr)) (PreH21 : (isr <= 255)) (PreH22 : (isr <= 0)) (PreH23 : (pd <> 0)) (PreH24 : (prio_in <> 255)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in < 64)) (PreH27 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH28 : (prio_pre <> 255)) (PreH29 : (RTrans_C sg ls0 sg ls1 )) (PreH30 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH31 : (isr <= 0)) (PreH32 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH33 : (prio_pre < 63)) (PreH34 : (prio_pre <> 255)) (PreH35 : (prio_pre = prio_in)) (PreH36 : (0 <= prio_in)) (PreH37 : (prio_in <= 255)) (PreH38 : (pd = perr_pre)) (PreH39 : (perr_pre <> 0)) (PreH40 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH41 : (0 <= isr)) (PreH42 : (isr <= 255)) (PreH43 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH44 : (freelist_in <> 0)) ,
  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> 0)
  **  (OutsideCritical sg ls_post_3 )
  **  (UCOS2_Verify_inv sg ls_post_3 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_3) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  EX (errv: Z)  (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (freelist_in = retv) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  ((pd) # UChar  |-> errv)
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (retv) (errv)) )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (ls_post_3: UCOS2_Verify_State) (PreH1 : (safeExec (LastSeen (ls_post_3)) (return (freelist_in)) X )) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (0 <= isr)) (PreH6 : (isr <= 255)) (PreH7 : (isr <= 0)) (PreH8 : (freelist_in <> 0)) (PreH9 : (freelist_in = (event_addr (sg) (eid)))) (PreH10 : (next_in = (free_event_head (sg) (free_rest)))) (PreH11 : (pd <> 0)) (PreH12 : (GTrans_C sg ls1_3 sg ls_post_2 )) (PreH13 : (freelist_in <> 0)) (PreH14 : (freelist_in <> 0)) (PreH15 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH16 : (RTrans_C sg ls0 sg ls1_2 )) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (0 <= isr)) (PreH21 : (isr <= 255)) (PreH22 : (isr <= 0)) (PreH23 : (pd <> 0)) (PreH24 : (prio_in <> 255)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in < 64)) (PreH27 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH28 : (prio_pre <> 255)) (PreH29 : (RTrans_C sg ls0 sg ls1 )) (PreH30 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH31 : (isr <= 0)) (PreH32 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH33 : (prio_pre < 63)) (PreH34 : (prio_pre <> 255)) (PreH35 : (prio_pre = prio_in)) (PreH36 : (0 <= prio_in)) (PreH37 : (prio_in <= 255)) (PreH38 : (pd = perr_pre)) (PreH39 : (perr_pre <> 0)) (PreH40 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH41 : (0 <= isr)) (PreH42 : (isr <= 255)) (PreH43 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH44 : (freelist_in <> 0)) ,
  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (OutsideCritical sg ls_post_3 )
  **  (UCOS2_Verify_inv sg ls_post_3 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_3) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls_post)) (return (freelist_in)) X ) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (freelist_in) (0)) )
).

Definition OSMutexCreate_full_return_wit_2_disabled_nonempty := 
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (ls_post_3: UCOS2_Verify_State) (PreH1 : (safeExec (LastSeen (ls_post_3)) (return (freelist_in)) X )) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (0 <= isr)) (PreH6 : (isr <= 255)) (PreH7 : (isr <= 0)) (PreH8 : (freelist_in <> 0)) (PreH9 : (freelist_in = (event_addr (sg) (eid)))) (PreH10 : (next_in = (free_event_head (sg) (free_rest)))) (PreH11 : (pd <> 0)) (PreH12 : (GTrans_C sg ls1_3 sg ls_post_2 )) (PreH13 : (freelist_in <> 0)) (PreH14 : (freelist_in <> 0)) (PreH15 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH16 : (RTrans_C sg ls0 sg ls1_2 )) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (0 <= isr)) (PreH21 : (isr <= 255)) (PreH22 : (isr <= 0)) (PreH23 : (pd <> 0)) (PreH24 : (prio_in = 255)) (PreH25 : (prio_pre = 255)) (PreH26 : (RTrans_C sg ls0 sg ls1 )) (PreH27 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH28 : (isr <= 0)) (PreH29 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH30 : (prio_pre = 255)) (PreH31 : (prio_pre = prio_in)) (PreH32 : (0 <= prio_in)) (PreH33 : (prio_in <= 255)) (PreH34 : (pd = perr_pre)) (PreH35 : (perr_pre <> 0)) (PreH36 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH37 : (0 <= isr)) (PreH38 : (isr <= 255)) (PreH39 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH40 : (freelist_in <> 0)) ,
  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> 0)
  **  (OutsideCritical sg ls_post_3 )
  **  (UCOS2_Verify_inv sg ls_post_3 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_3) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  EX (errv: Z)  (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (freelist_in = retv) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  ((pd) # UChar  |-> errv)
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (retv) (errv)) )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (ls_post_3: UCOS2_Verify_State) (PreH1 : (safeExec (LastSeen (ls_post_3)) (return (freelist_in)) X )) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in <= 255)) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (0 <= isr)) (PreH6 : (isr <= 255)) (PreH7 : (isr <= 0)) (PreH8 : (freelist_in <> 0)) (PreH9 : (freelist_in = (event_addr (sg) (eid)))) (PreH10 : (next_in = (free_event_head (sg) (free_rest)))) (PreH11 : (pd <> 0)) (PreH12 : (GTrans_C sg ls1_3 sg ls_post_2 )) (PreH13 : (freelist_in <> 0)) (PreH14 : (freelist_in <> 0)) (PreH15 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH16 : (RTrans_C sg ls0 sg ls1_2 )) (PreH17 : (0 <= prio_in)) (PreH18 : (prio_in <= 255)) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (0 <= isr)) (PreH21 : (isr <= 255)) (PreH22 : (isr <= 0)) (PreH23 : (pd <> 0)) (PreH24 : (prio_in = 255)) (PreH25 : (prio_pre = 255)) (PreH26 : (RTrans_C sg ls0 sg ls1 )) (PreH27 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH28 : (isr <= 0)) (PreH29 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH30 : (prio_pre = 255)) (PreH31 : (prio_pre = prio_in)) (PreH32 : (0 <= prio_in)) (PreH33 : (prio_in <= 255)) (PreH34 : (pd = perr_pre)) (PreH35 : (perr_pre <> 0)) (PreH36 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH37 : (0 <= isr)) (PreH38 : (isr <= 255)) (PreH39 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH40 : (freelist_in <> 0)) ,
  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (OutsideCritical sg ls_post_3 )
  **  (UCOS2_Verify_inv sg ls_post_3 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_3) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls_post)) (return (freelist_in)) X ) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (freelist_in) (0)) )
).

Definition OSMutexCreate_full_return_wit_3_disabled_empty := 
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls1_4: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_4 sg ls_post_2 )) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH3 : (RTrans_C sg ls0 sg ls1_3 )) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : (isr <= 0)) (PreH10 : (freelist_in = 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_pre = 255)) (PreH13 : (freelist_in = 0)) (PreH14 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH15 : (RTrans_C sg ls0 sg ls1_2 )) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (0 <= isr)) (PreH20 : (isr <= 255)) (PreH21 : (isr <= 0)) (PreH22 : (pd <> 0)) (PreH23 : (prio_in = 255)) (PreH24 : (prio_pre = 255)) (PreH25 : (RTrans_C sg ls0 sg ls1 )) (PreH26 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH27 : (isr <= 0)) (PreH28 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH29 : (prio_pre = 255)) (PreH30 : (prio_pre = prio_in)) (PreH31 : (0 <= prio_in)) (PreH32 : (prio_in <= 255)) (PreH33 : (pd = perr_pre)) (PreH34 : (perr_pre <> 0)) (PreH35 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH36 : (0 <= isr)) (PreH37 : (isr <= 255)) (PreH38 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH39 : (freelist_in = 0)) ,
  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> 4)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  EX (errv: Z)  (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  ((pd) # UChar  |-> errv)
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (retv) (errv)) )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls1_4: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_4 sg ls_post_2 )) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH3 : (RTrans_C sg ls0 sg ls1_3 )) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : (isr <= 0)) (PreH10 : (freelist_in = 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_pre = 255)) (PreH13 : (freelist_in = 0)) (PreH14 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH15 : (RTrans_C sg ls0 sg ls1_2 )) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (0 <= isr)) (PreH20 : (isr <= 255)) (PreH21 : (isr <= 0)) (PreH22 : (pd <> 0)) (PreH23 : (prio_in = 255)) (PreH24 : (prio_pre = 255)) (PreH25 : (RTrans_C sg ls0 sg ls1 )) (PreH26 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH27 : (isr <= 0)) (PreH28 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH29 : (prio_pre = 255)) (PreH30 : (prio_pre = prio_in)) (PreH31 : (0 <= prio_in)) (PreH32 : (prio_in <= 255)) (PreH33 : (pd = perr_pre)) (PreH34 : (perr_pre <> 0)) (PreH35 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH36 : (0 <= isr)) (PreH37 : (isr <= 255)) (PreH38 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH39 : (freelist_in = 0)) ,
  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls_post)) (return (0)) X ) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (0) (4)) )
).

Definition OSMutexCreate_full_return_wit_4_enabled_empty := 
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls1_4: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_4 sg ls_post_2 )) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH3 : (RTrans_C sg ls0 sg ls1_3 )) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : (isr <= 0)) (PreH10 : (freelist_in = 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_pre <> 255)) (PreH13 : (freelist_in = 0)) (PreH14 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH15 : (RTrans_C sg ls0 sg ls1_2 )) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (0 <= isr)) (PreH20 : (isr <= 255)) (PreH21 : (isr <= 0)) (PreH22 : (pd <> 0)) (PreH23 : (prio_in <> 255)) (PreH24 : (0 <= prio_in)) (PreH25 : (prio_in < 64)) (PreH26 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH27 : (prio_pre <> 255)) (PreH28 : (RTrans_C sg ls0 sg ls1 )) (PreH29 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH30 : (isr <= 0)) (PreH31 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH32 : (prio_pre < 63)) (PreH33 : (prio_pre <> 255)) (PreH34 : (prio_pre = prio_in)) (PreH35 : (0 <= prio_in)) (PreH36 : (prio_in <= 255)) (PreH37 : (pd = perr_pre)) (PreH38 : (perr_pre <> 0)) (PreH39 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH40 : (0 <= isr)) (PreH41 : (isr <= 255)) (PreH42 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH43 : (freelist_in = 0)) ,
  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> 4)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  EX (errv: Z)  (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  ((pd) # UChar  |-> errv)
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (retv) (errv)) )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls1_4: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_4 sg ls_post_2 )) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH3 : (RTrans_C sg ls0 sg ls1_3 )) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : (isr <= 0)) (PreH10 : (freelist_in = 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_pre <> 255)) (PreH13 : (freelist_in = 0)) (PreH14 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH15 : (RTrans_C sg ls0 sg ls1_2 )) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (0 <= isr)) (PreH20 : (isr <= 255)) (PreH21 : (isr <= 0)) (PreH22 : (pd <> 0)) (PreH23 : (prio_in <> 255)) (PreH24 : (0 <= prio_in)) (PreH25 : (prio_in < 64)) (PreH26 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH27 : (prio_pre <> 255)) (PreH28 : (RTrans_C sg ls0 sg ls1 )) (PreH29 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH30 : (isr <= 0)) (PreH31 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH32 : (prio_pre < 63)) (PreH33 : (prio_pre <> 255)) (PreH34 : (prio_pre = prio_in)) (PreH35 : (0 <= prio_in)) (PreH36 : (prio_in <= 255)) (PreH37 : (pd = perr_pre)) (PreH38 : (perr_pre <> 0)) (PreH39 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH40 : (0 <= isr)) (PreH41 : (isr <= 255)) (PreH42 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH43 : (freelist_in = 0)) ,
  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls_post)) (return (0)) X ) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (0) (4)) )
).

Definition OSMutexCreate_full_return_wit_5 := 
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_2 sg ls_post_2 )) (PreH2 : ((Znth (prio_in) (prioL_in) (0)) <> 0)) (PreH3 : (prio_pre <> 255)) (PreH4 : (RTrans_C sg ls0 sg ls1 )) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (isr <= 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (prio_pre < 63)) (PreH9 : (prio_pre <> 255)) (PreH10 : (prio_pre = prio_in)) (PreH11 : (0 <= prio_in)) (PreH12 : (prio_in <= 255)) (PreH13 : (pd = perr_pre)) (PreH14 : (perr_pre <> 0)) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (0 <= isr)) (PreH17 : (isr <= 255)) (PreH18 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH19 : (freelist_in = 0)) ,
  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> 40)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  EX (errv: Z)  (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  ((pd) # UChar  |-> errv)
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (retv) (errv)) )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_2 sg ls_post_2 )) (PreH2 : ((Znth (prio_in) (prioL_in) (0)) <> 0)) (PreH3 : (prio_pre <> 255)) (PreH4 : (RTrans_C sg ls0 sg ls1 )) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (isr <= 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (prio_pre < 63)) (PreH9 : (prio_pre <> 255)) (PreH10 : (prio_pre = prio_in)) (PreH11 : (0 <= prio_in)) (PreH12 : (prio_in <= 255)) (PreH13 : (pd = perr_pre)) (PreH14 : (perr_pre <> 0)) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (0 <= isr)) (PreH17 : (isr <= 255)) (PreH18 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH19 : (freelist_in = 0)) ,
  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls_post)) (return (0)) X ) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (0) (40)) )
).

Definition OSMutexCreate_full_return_wit_6 := 
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_2 sg ls_post_2 )) (PreH2 : ((Znth (prio_in) (prioL_in) (0)) <> 0)) (PreH3 : (prio_pre <> 255)) (PreH4 : (RTrans_C sg ls0 sg ls1 )) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (isr <= 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (prio_pre < 63)) (PreH9 : (prio_pre <> 255)) (PreH10 : (prio_pre = prio_in)) (PreH11 : (0 <= prio_in)) (PreH12 : (prio_in <= 255)) (PreH13 : (pd = perr_pre)) (PreH14 : (perr_pre <> 0)) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (0 <= isr)) (PreH17 : (isr <= 255)) (PreH18 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH19 : (freelist_in <> 0)) ,
  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> 40)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  EX (errv: Z)  (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  ((pd) # UChar  |-> errv)
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (retv) (errv)) )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_2 sg ls_post_2 )) (PreH2 : ((Znth (prio_in) (prioL_in) (0)) <> 0)) (PreH3 : (prio_pre <> 255)) (PreH4 : (RTrans_C sg ls0 sg ls1 )) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (isr <= 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (prio_pre < 63)) (PreH9 : (prio_pre <> 255)) (PreH10 : (prio_pre = prio_in)) (PreH11 : (0 <= prio_in)) (PreH12 : (prio_in <= 255)) (PreH13 : (pd = perr_pre)) (PreH14 : (perr_pre <> 0)) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (0 <= isr)) (PreH17 : (isr <= 255)) (PreH18 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH19 : (freelist_in <> 0)) ,
  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls_post)) (return (0)) X ) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (0) (40)) )
).

Definition OSMutexCreate_full_return_wit_7 := 
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr > 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (pd = perr_pre)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (0 <= isr)) (PreH13 : (isr <= 255)) (PreH14 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH15 : (freelist_in <> 0)) ,
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> 16)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  EX (errv: Z)  (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  ((pd) # UChar  |-> errv)
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (retv) (errv)) )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr > 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (pd = perr_pre)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (0 <= isr)) (PreH13 : (isr <= 255)) (PreH14 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH15 : (freelist_in <> 0)) ,
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls_post)) (return (0)) X ) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (0) (16)) )
).

Definition OSMutexCreate_full_return_wit_8 := 
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr > 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (pd = perr_pre)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (0 <= isr)) (PreH13 : (isr <= 255)) (PreH14 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH15 : (freelist_in = 0)) ,
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> 16)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  EX (errv: Z)  (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  ((pd) # UChar  |-> errv)
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (retv) (errv)) )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr > 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (pd = perr_pre)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (0 <= isr)) (PreH13 : (isr <= 255)) (PreH14 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH15 : (freelist_in = 0)) ,
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls_post)) (return (0)) X ) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (0) (16)) )
).

Definition OSMutexCreate_full_return_wit_9 := 
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr > 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (pd = perr_pre)) (PreH9 : (perr_pre <> 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH14 : (freelist_in <> 0)) ,
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> 16)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  EX (errv: Z)  (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  ((pd) # UChar  |-> errv)
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (retv) (errv)) )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr > 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (pd = perr_pre)) (PreH9 : (perr_pre <> 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH14 : (freelist_in <> 0)) ,
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls_post)) (return (0)) X ) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (0) (16)) )
).

Definition OSMutexCreate_full_return_wit_10 := 
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr > 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (pd = perr_pre)) (PreH9 : (perr_pre <> 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH14 : (freelist_in = 0)) ,
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> 16)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  EX (errv: Z)  (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  ((pd) # UChar  |-> errv)
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (retv) (errv)) )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr > 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (pd = perr_pre)) (PreH9 : (perr_pre <> 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH14 : (freelist_in = 0)) ,
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls_post)) (return (0)) X ) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (0) (16)) )
).

Definition OSMutexCreate_full_return_wit_11 := 
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (prio_pre >= 63)) (PreH2 : (prio_pre <> 255)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (pd = perr_pre)) (PreH7 : (perr_pre <> 0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH12 : (freelist_in <> 0)) ,
  ((perr_pre) # UChar  |-> 42)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  EX (errv: Z)  (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  ((pd) # UChar  |-> errv)
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (retv) (errv)) )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (prio_pre >= 63)) (PreH2 : (prio_pre <> 255)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (pd = perr_pre)) (PreH7 : (perr_pre <> 0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH12 : (freelist_in <> 0)) ,
  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls_post)) (return (0)) X ) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (0) (42)) )
).

Definition OSMutexCreate_full_return_wit_12 := 
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (prio_pre >= 63)) (PreH2 : (prio_pre <> 255)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (pd = perr_pre)) (PreH7 : (perr_pre <> 0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH12 : (freelist_in = 0)) ,
  ((perr_pre) # UChar  |-> 42)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  EX (errv: Z)  (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  ((pd) # UChar  |-> errv)
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (retv) (errv)) )
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (prio_pre >= 63)) (PreH2 : (prio_pre <> 255)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (pd = perr_pre)) (PreH7 : (perr_pre <> 0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH12 : (freelist_in = 0)) ,
  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls_post)) (return (0)) X ) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pd <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_create_result_prop (sg) (ls0) (ls_post) (prio_in) (isr) (prioL_in) (freelist_in) (eid) (free_rest) (0) (42)) )
).

Definition OSMutexCreate_full_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (prio_pre = 255)) (PreH2 : (prio_pre = prio_in)) (PreH3 : (0 <= prio_in)) (PreH4 : (prio_in <= 255)) (PreH5 : (pd = perr_pre)) (PreH6 : (perr_pre <> 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH11 : (freelist_in = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
.

Definition OSMutexCreate_full_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (prio_pre = 255)) (PreH2 : (prio_pre = prio_in)) (PreH3 : (0 <= prio_in)) (PreH4 : (prio_in <= 255)) (PreH5 : (pd = perr_pre)) (PreH6 : (perr_pre <> 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH11 : (freelist_in = 0)) ,
  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_Verify_inv sg ls0 )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
.

Definition OSMutexCreate_full_partial_solve_wit_1 := OSMutexCreate_full_partial_solve_wit_1_pure -> OSMutexCreate_full_partial_solve_wit_1_aux.

Definition OSMutexCreate_full_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (prio_pre = 255)) (PreH2 : (prio_pre = prio_in)) (PreH3 : (0 <= prio_in)) (PreH4 : (prio_in <= 255)) (PreH5 : (pd = perr_pre)) (PreH6 : (perr_pre <> 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH11 : (freelist_in <> 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
.

Definition OSMutexCreate_full_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (prio_pre = 255)) (PreH2 : (prio_pre = prio_in)) (PreH3 : (0 <= prio_in)) (PreH4 : (prio_in <= 255)) (PreH5 : (pd = perr_pre)) (PreH6 : (perr_pre <> 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH11 : (freelist_in <> 0)) ,
  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_Verify_inv sg ls0 )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
.

Definition OSMutexCreate_full_partial_solve_wit_2 := OSMutexCreate_full_partial_solve_wit_2_pure -> OSMutexCreate_full_partial_solve_wit_2_aux.

Definition OSMutexCreate_full_partial_solve_wit_3_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (prio_pre < 63)) (PreH2 : (prio_pre <> 255)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (pd = perr_pre)) (PreH7 : (perr_pre <> 0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH12 : (freelist_in = 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
.

Definition OSMutexCreate_full_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (prio_pre < 63)) (PreH2 : (prio_pre <> 255)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (pd = perr_pre)) (PreH7 : (perr_pre <> 0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH12 : (freelist_in = 0)) ,
  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_Verify_inv sg ls0 )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
.

Definition OSMutexCreate_full_partial_solve_wit_3 := OSMutexCreate_full_partial_solve_wit_3_pure -> OSMutexCreate_full_partial_solve_wit_3_aux.

Definition OSMutexCreate_full_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (prio_pre < 63)) (PreH2 : (prio_pre <> 255)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (pd = perr_pre)) (PreH7 : (perr_pre <> 0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH12 : (freelist_in <> 0)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
.

Definition OSMutexCreate_full_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (prio_pre < 63)) (PreH2 : (prio_pre <> 255)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (pd = perr_pre)) (PreH7 : (perr_pre <> 0)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH12 : (freelist_in <> 0)) ,
  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_Verify_inv sg ls0 )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
.

Definition OSMutexCreate_full_partial_solve_wit_4 := OSMutexCreate_full_partial_solve_wit_4_pure -> OSMutexCreate_full_partial_solve_wit_4_aux.

Definition OSMutexCreate_full_partial_solve_wit_5_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr > 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (prio_pre = 255)) (PreH4 : (prio_pre = prio_in)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (pd = perr_pre)) (PreH8 : (perr_pre <> 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (0 <= isr)) (PreH11 : (isr <= 255)) (PreH12 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH13 : (freelist_in = 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
.

Definition OSMutexCreate_full_partial_solve_wit_5_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr > 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (prio_pre = 255)) (PreH4 : (prio_pre = prio_in)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (pd = perr_pre)) (PreH8 : (perr_pre <> 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (0 <= isr)) (PreH11 : (isr <= 255)) (PreH12 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH13 : (freelist_in = 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr > 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
.

Definition OSMutexCreate_full_partial_solve_wit_5 := OSMutexCreate_full_partial_solve_wit_5_pure -> OSMutexCreate_full_partial_solve_wit_5_aux.

Definition OSMutexCreate_full_partial_solve_wit_6_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr > 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (prio_pre = 255)) (PreH4 : (prio_pre = prio_in)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (pd = perr_pre)) (PreH8 : (perr_pre <> 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (0 <= isr)) (PreH11 : (isr <= 255)) (PreH12 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH13 : (freelist_in <> 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
.

Definition OSMutexCreate_full_partial_solve_wit_6_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr > 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (prio_pre = 255)) (PreH4 : (prio_pre = prio_in)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (pd = perr_pre)) (PreH8 : (perr_pre <> 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (0 <= isr)) (PreH11 : (isr <= 255)) (PreH12 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH13 : (freelist_in <> 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr > 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
.

Definition OSMutexCreate_full_partial_solve_wit_6 := OSMutexCreate_full_partial_solve_wit_6_pure -> OSMutexCreate_full_partial_solve_wit_6_aux.

Definition OSMutexCreate_full_partial_solve_wit_7_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr > 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (prio_pre < 63)) (PreH4 : (prio_pre <> 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (pd = perr_pre)) (PreH9 : (perr_pre <> 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH14 : (freelist_in = 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
.

Definition OSMutexCreate_full_partial_solve_wit_7_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr > 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (prio_pre < 63)) (PreH4 : (prio_pre <> 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (pd = perr_pre)) (PreH9 : (perr_pre <> 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH14 : (freelist_in = 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr > 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
.

Definition OSMutexCreate_full_partial_solve_wit_7 := OSMutexCreate_full_partial_solve_wit_7_pure -> OSMutexCreate_full_partial_solve_wit_7_aux.

Definition OSMutexCreate_full_partial_solve_wit_8_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr > 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (prio_pre < 63)) (PreH4 : (prio_pre <> 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (pd = perr_pre)) (PreH9 : (perr_pre <> 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH14 : (freelist_in <> 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
.

Definition OSMutexCreate_full_partial_solve_wit_8_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr > 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (prio_pre < 63)) (PreH4 : (prio_pre <> 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (pd = perr_pre)) (PreH9 : (perr_pre <> 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH14 : (freelist_in <> 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr > 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
.

Definition OSMutexCreate_full_partial_solve_wit_8 := OSMutexCreate_full_partial_solve_wit_8_pure -> OSMutexCreate_full_partial_solve_wit_8_aux.

Definition OSMutexCreate_full_partial_solve_wit_9_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr <= 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (prio_pre = 255)) (PreH4 : (prio_pre = prio_in)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (pd = perr_pre)) (PreH8 : (perr_pre <> 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (0 <= isr)) (PreH11 : (isr <= 255)) (PreH12 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH13 : (freelist_in = 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
.

Definition OSMutexCreate_full_partial_solve_wit_9_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr <= 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (prio_pre = 255)) (PreH4 : (prio_pre = prio_in)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (pd = perr_pre)) (PreH8 : (perr_pre <> 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (0 <= isr)) (PreH11 : (isr <= 255)) (PreH12 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH13 : (freelist_in = 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
.

Definition OSMutexCreate_full_partial_solve_wit_9 := OSMutexCreate_full_partial_solve_wit_9_pure -> OSMutexCreate_full_partial_solve_wit_9_aux.

Definition OSMutexCreate_full_partial_solve_wit_10_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr <= 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (prio_pre = 255)) (PreH4 : (prio_pre = prio_in)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (pd = perr_pre)) (PreH8 : (perr_pre <> 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (0 <= isr)) (PreH11 : (isr <= 255)) (PreH12 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH13 : (freelist_in <> 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
.

Definition OSMutexCreate_full_partial_solve_wit_10_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr <= 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (prio_pre = 255)) (PreH4 : (prio_pre = prio_in)) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (pd = perr_pre)) (PreH8 : (perr_pre <> 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (0 <= isr)) (PreH11 : (isr <= 255)) (PreH12 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH13 : (freelist_in <> 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
.

Definition OSMutexCreate_full_partial_solve_wit_10 := OSMutexCreate_full_partial_solve_wit_10_pure -> OSMutexCreate_full_partial_solve_wit_10_aux.

Definition OSMutexCreate_full_partial_solve_wit_11_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr <= 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (prio_pre < 63)) (PreH4 : (prio_pre <> 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (pd = perr_pre)) (PreH9 : (perr_pre <> 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH14 : (freelist_in = 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
.

Definition OSMutexCreate_full_partial_solve_wit_11_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr <= 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (prio_pre < 63)) (PreH4 : (prio_pre <> 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (pd = perr_pre)) (PreH9 : (perr_pre <> 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH14 : (freelist_in = 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
.

Definition OSMutexCreate_full_partial_solve_wit_11 := OSMutexCreate_full_partial_solve_wit_11_pure -> OSMutexCreate_full_partial_solve_wit_11_aux.

Definition OSMutexCreate_full_partial_solve_wit_12_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr <= 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (prio_pre < 63)) (PreH4 : (prio_pre <> 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (pd = perr_pre)) (PreH9 : (perr_pre <> 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH14 : (freelist_in <> 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
.

Definition OSMutexCreate_full_partial_solve_wit_12_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr <= 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (prio_pre < 63)) (PreH4 : (prio_pre <> 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (pd = perr_pre)) (PreH9 : (perr_pre <> 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH14 : (freelist_in <> 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
.

Definition OSMutexCreate_full_partial_solve_wit_12 := OSMutexCreate_full_partial_solve_wit_12_pure -> OSMutexCreate_full_partial_solve_wit_12_aux.

Definition OSMutexCreate_full_partial_solve_wit_13 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (pd = perr_pre)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (0 <= isr)) (PreH13 : (isr <= 255)) (PreH14 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH15 : (freelist_in <> 0)) ,
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
.

Definition OSMutexCreate_full_partial_solve_wit_14 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (prio_pre < 63)) (PreH5 : (prio_pre <> 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (pd = perr_pre)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (0 <= isr)) (PreH13 : (isr <= 255)) (PreH14 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH15 : (freelist_in = 0)) ,
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
.

Definition OSMutexCreate_full_partial_solve_wit_15 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (pd = perr_pre)) (PreH9 : (perr_pre <> 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH14 : (freelist_in <> 0)) ,
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
.

Definition OSMutexCreate_full_partial_solve_wit_16 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (prio_pre = 255)) (PreH5 : (prio_pre = prio_in)) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (pd = perr_pre)) (PreH9 : (perr_pre <> 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH14 : (freelist_in = 0)) ,
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
.

Definition OSMutexCreate_full_partial_solve_wit_17 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (PreH1 : (RTrans_C sg ls0 sg ls1 )) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (isr <= 0)) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (prio_pre = 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (pd = perr_pre)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (0 <= isr)) (PreH13 : (isr <= 255)) (PreH14 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH15 : (freelist_in = 0)) ,
  (InsideCritical sg ls1 )
  **  (UCOS2_Verify_inv sg ls1 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (InsideCritical sg ls1 )
  **  (UCOS2_Verify_inv sg ls1 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
.

Definition OSMutexCreate_full_partial_solve_wit_18 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (PreH1 : (RTrans_C sg ls0 sg ls1 )) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (isr <= 0)) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (prio_pre = 255)) (PreH6 : (prio_pre = prio_in)) (PreH7 : (0 <= prio_in)) (PreH8 : (prio_in <= 255)) (PreH9 : (pd = perr_pre)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (0 <= isr)) (PreH13 : (isr <= 255)) (PreH14 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH15 : (freelist_in <> 0)) ,
  (InsideCritical sg ls1 )
  **  (UCOS2_Verify_inv sg ls1 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (InsideCritical sg ls1 )
  **  (UCOS2_Verify_inv sg ls1 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
.

Definition OSMutexCreate_full_partial_solve_wit_19 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (PreH1 : (RTrans_C sg ls0 sg ls1 )) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (isr <= 0)) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (prio_pre < 63)) (PreH6 : (prio_pre <> 255)) (PreH7 : (prio_pre = prio_in)) (PreH8 : (0 <= prio_in)) (PreH9 : (prio_in <= 255)) (PreH10 : (pd = perr_pre)) (PreH11 : (perr_pre <> 0)) (PreH12 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH16 : (freelist_in = 0)) ,
  (InsideCritical sg ls1 )
  **  (UCOS2_Verify_inv sg ls1 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (InsideCritical sg ls1 )
  **  (UCOS2_Verify_inv sg ls1 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
.

Definition OSMutexCreate_full_partial_solve_wit_20 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (PreH1 : (RTrans_C sg ls0 sg ls1 )) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (isr <= 0)) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (prio_pre < 63)) (PreH6 : (prio_pre <> 255)) (PreH7 : (prio_pre = prio_in)) (PreH8 : (0 <= prio_in)) (PreH9 : (prio_in <= 255)) (PreH10 : (pd = perr_pre)) (PreH11 : (perr_pre <> 0)) (PreH12 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH16 : (freelist_in <> 0)) ,
  (InsideCritical sg ls1 )
  **  (UCOS2_Verify_inv sg ls1 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (InsideCritical sg ls1 )
  **  (UCOS2_Verify_inv sg ls1 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
.

Definition OSMutexCreate_full_partial_solve_wit_21_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (RTrans_C sg ls0 sg ls1 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (prio_pre < 63)) (PreH7 : (prio_pre <> 255)) (PreH8 : (prio_pre = prio_in)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : (pd = perr_pre)) (PreH12 : (perr_pre <> 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH17 : (freelist_in = 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ”
.

Definition OSMutexCreate_full_partial_solve_wit_21_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (RTrans_C sg ls0 sg ls1 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (prio_pre < 63)) (PreH7 : (prio_pre <> 255)) (PreH8 : (prio_pre = prio_in)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : (pd = perr_pre)) (PreH12 : (perr_pre <> 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH17 : (freelist_in = 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (store_priotbl_list sg prioL_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
.

Definition OSMutexCreate_full_partial_solve_wit_21 := OSMutexCreate_full_partial_solve_wit_21_pure -> OSMutexCreate_full_partial_solve_wit_21_aux.

Definition OSMutexCreate_full_partial_solve_wit_22_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (RTrans_C sg ls0 sg ls1 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (prio_pre < 63)) (PreH7 : (prio_pre <> 255)) (PreH8 : (prio_pre = prio_in)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : (pd = perr_pre)) (PreH12 : (perr_pre <> 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH17 : (freelist_in <> 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ”
.

Definition OSMutexCreate_full_partial_solve_wit_22_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (RTrans_C sg ls0 sg ls1 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (prio_pre < 63)) (PreH7 : (prio_pre <> 255)) (PreH8 : (prio_pre = prio_in)) (PreH9 : (0 <= prio_in)) (PreH10 : (prio_in <= 255)) (PreH11 : (pd = perr_pre)) (PreH12 : (perr_pre <> 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (0 <= isr)) (PreH15 : (isr <= 255)) (PreH16 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH17 : (freelist_in <> 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (store_priotbl_list sg prioL_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
.

Definition OSMutexCreate_full_partial_solve_wit_22 := OSMutexCreate_full_partial_solve_wit_22_pure -> OSMutexCreate_full_partial_solve_wit_22_aux.

Definition OSMutexCreate_full_partial_solve_wit_23_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : ((Znth (prio_in) (prioL_in) (0)) <> 0)) (PreH2 : (prio_pre <> 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre < 63)) (PreH8 : (prio_pre <> 255)) (PreH9 : (prio_pre = prio_in)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : (pd = perr_pre)) (PreH13 : (perr_pre <> 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH18 : (freelist_in <> 0)) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (Znth (prio_in) (prioL_in) (0)))
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ”
.

Definition OSMutexCreate_full_partial_solve_wit_23_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (PreH1 : ((Znth (prio_in) (prioL_in) (0)) <> 0)) (PreH2 : (prio_pre <> 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre < 63)) (PreH8 : (prio_pre <> 255)) (PreH9 : (prio_pre = prio_in)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : (pd = perr_pre)) (PreH13 : (perr_pre <> 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH18 : (freelist_in <> 0)) ,
  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (Znth (prio_in) (prioL_in) (0)))
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) <> 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (Znth (prio_in) (prioL_in) (0)))
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
.

Definition OSMutexCreate_full_partial_solve_wit_23 := OSMutexCreate_full_partial_solve_wit_23_pure -> OSMutexCreate_full_partial_solve_wit_23_aux.

Definition OSMutexCreate_full_partial_solve_wit_24_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : ((Znth (prio_in) (prioL_in) (0)) <> 0)) (PreH2 : (prio_pre <> 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre < 63)) (PreH8 : (prio_pre <> 255)) (PreH9 : (prio_pre = prio_in)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : (pd = perr_pre)) (PreH13 : (perr_pre <> 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH18 : (freelist_in = 0)) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (Znth (prio_in) (prioL_in) (0)))
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ”
.

Definition OSMutexCreate_full_partial_solve_wit_24_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (PreH1 : ((Znth (prio_in) (prioL_in) (0)) <> 0)) (PreH2 : (prio_pre <> 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre < 63)) (PreH8 : (prio_pre <> 255)) (PreH9 : (prio_pre = prio_in)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : (pd = perr_pre)) (PreH13 : (perr_pre <> 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH18 : (freelist_in = 0)) ,
  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (Znth (prio_in) (prioL_in) (0)))
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) <> 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> (Znth (prio_in) (prioL_in) (0)))
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
.

Definition OSMutexCreate_full_partial_solve_wit_24 := OSMutexCreate_full_partial_solve_wit_24_pure -> OSMutexCreate_full_partial_solve_wit_24_aux.

Definition OSMutexCreate_full_partial_solve_wit_25 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (PreH1 : ((Znth (prio_in) (prioL_in) (0)) <> 0)) (PreH2 : (prio_pre <> 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre < 63)) (PreH8 : (prio_pre <> 255)) (PreH9 : (prio_pre = prio_in)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : (pd = perr_pre)) (PreH13 : (perr_pre <> 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH18 : (freelist_in <> 0)) ,
  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (store_priotbl_list sg prioL_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ ((Znth (prio_in) (prioL_in) (0)) <> 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
.

Definition OSMutexCreate_full_partial_solve_wit_26 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (PreH1 : ((Znth (prio_in) (prioL_in) (0)) <> 0)) (PreH2 : (prio_pre <> 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre < 63)) (PreH8 : (prio_pre <> 255)) (PreH9 : (prio_pre = prio_in)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : (pd = perr_pre)) (PreH13 : (perr_pre <> 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH18 : (freelist_in = 0)) ,
  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (store_priotbl_list sg prioL_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ ((Znth (prio_in) (prioL_in) (0)) <> 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
.

Definition OSMutexCreate_full_partial_solve_wit_27 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (PreH1 : ((Znth (prio_in) (prioL_in) (0)) <> 0)) (PreH2 : (prio_pre <> 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre < 63)) (PreH8 : (prio_pre <> 255)) (PreH9 : (prio_pre = prio_in)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : (pd = perr_pre)) (PreH13 : (perr_pre <> 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH18 : (freelist_in = 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ ((Znth (prio_in) (prioL_in) (0)) <> 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (InsideCritical sg ls1_2 )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
.

Definition OSMutexCreate_full_partial_solve_wit_28 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (PreH1 : ((Znth (prio_in) (prioL_in) (0)) <> 0)) (PreH2 : (prio_pre <> 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre < 63)) (PreH8 : (prio_pre <> 255)) (PreH9 : (prio_pre = prio_in)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : (pd = perr_pre)) (PreH13 : (perr_pre <> 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH18 : (freelist_in <> 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ ((Znth (prio_in) (prioL_in) (0)) <> 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (InsideCritical sg ls1_2 )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
.

Definition OSMutexCreate_full_partial_solve_wit_29 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_2 sg ls_post )) (PreH2 : ((Znth (prio_in) (prioL_in) (0)) <> 0)) (PreH3 : (prio_pre <> 255)) (PreH4 : (RTrans_C sg ls0 sg ls1 )) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (isr <= 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (prio_pre < 63)) (PreH9 : (prio_pre <> 255)) (PreH10 : (prio_pre = prio_in)) (PreH11 : (0 <= prio_in)) (PreH12 : (prio_in <= 255)) (PreH13 : (pd = perr_pre)) (PreH14 : (perr_pre <> 0)) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (0 <= isr)) (PreH17 : (isr <= 255)) (PreH18 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH19 : (freelist_in <> 0)) ,
  (OutsideCritical sg ls_post )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (mutex_create_restore_transition_prop (sg) (ls0) (ls1_2) (ls_post) (prio_in) (eid) (free_rest) (false)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (GTrans_C sg ls1_2 sg ls_post ) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) <> 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (mutex_create_restore_transition_prop (sg) (ls0) (ls1_2) (ls_post) (prio_in) (eid) (free_rest) (false)) )
  **  (OutsideCritical sg ls_post )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
.

Definition OSMutexCreate_full_partial_solve_wit_30 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_2 sg ls_post )) (PreH2 : ((Znth (prio_in) (prioL_in) (0)) <> 0)) (PreH3 : (prio_pre <> 255)) (PreH4 : (RTrans_C sg ls0 sg ls1 )) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (isr <= 0)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (prio_pre < 63)) (PreH9 : (prio_pre <> 255)) (PreH10 : (prio_pre = prio_in)) (PreH11 : (0 <= prio_in)) (PreH12 : (prio_in <= 255)) (PreH13 : (pd = perr_pre)) (PreH14 : (perr_pre <> 0)) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (0 <= isr)) (PreH17 : (isr <= 255)) (PreH18 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH19 : (freelist_in = 0)) ,
  (OutsideCritical sg ls_post )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (mutex_create_restore_transition_prop (sg) (ls0) (ls1_2) (ls_post) (prio_in) (eid) (free_rest) (false)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (GTrans_C sg ls1_2 sg ls_post ) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) <> 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (coq_prop (mutex_create_restore_transition_prop (sg) (ls0) (ls1_2) (ls_post) (prio_in) (eid) (free_rest) (false)) )
  **  (OutsideCritical sg ls_post )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
.

Definition OSMutexCreate_full_partial_solve_wit_31_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH2 : (prio_pre <> 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre < 63)) (PreH8 : (prio_pre <> 255)) (PreH9 : (prio_pre = prio_in)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : (pd = perr_pre)) (PreH13 : (perr_pre <> 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH18 : (freelist_in <> 0)) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> 1)
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ”
.

Definition OSMutexCreate_full_partial_solve_wit_31_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (PreH1 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH2 : (prio_pre <> 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre < 63)) (PreH8 : (prio_pre <> 255)) (PreH9 : (prio_pre = prio_in)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : (pd = perr_pre)) (PreH13 : (perr_pre <> 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH18 : (freelist_in <> 0)) ,
  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> 1)
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> 1)
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
.

Definition OSMutexCreate_full_partial_solve_wit_31 := OSMutexCreate_full_partial_solve_wit_31_pure -> OSMutexCreate_full_partial_solve_wit_31_aux.

Definition OSMutexCreate_full_partial_solve_wit_32_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH2 : (prio_pre <> 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre < 63)) (PreH8 : (prio_pre <> 255)) (PreH9 : (prio_pre = prio_in)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : (pd = perr_pre)) (PreH13 : (perr_pre <> 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH18 : (freelist_in = 0)) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> 1)
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ”
.

Definition OSMutexCreate_full_partial_solve_wit_32_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (PreH1 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH2 : (prio_pre <> 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre < 63)) (PreH8 : (prio_pre <> 255)) (PreH9 : (prio_pre = prio_in)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : (pd = perr_pre)) (PreH13 : (perr_pre <> 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH18 : (freelist_in = 0)) ,
  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> 1)
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> 1)
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
.

Definition OSMutexCreate_full_partial_solve_wit_32 := OSMutexCreate_full_partial_solve_wit_32_pure -> OSMutexCreate_full_partial_solve_wit_32_aux.

Definition OSMutexCreate_full_partial_solve_wit_33_enabled_nonempty_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH2 : (prio_pre <> 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre < 63)) (PreH8 : (prio_pre <> 255)) (PreH9 : (prio_pre = prio_in)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : (pd = perr_pre)) (PreH13 : (perr_pre <> 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH18 : (freelist_in <> 0)) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (store_priotbl_list sg (replace_Znth (prio_in) (1) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 63) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ”
.

Definition OSMutexCreate_full_partial_solve_wit_33_enabled_nonempty_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (PreH1 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH2 : (prio_pre <> 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre < 63)) (PreH8 : (prio_pre <> 255)) (PreH9 : (prio_pre = prio_in)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : (pd = perr_pre)) (PreH13 : (perr_pre <> 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH18 : (freelist_in <> 0)) ,
  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (store_priotbl_list sg (replace_Znth (prio_in) (1) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 63) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_priotbl_list sg (replace_Znth (prio_in) (1) (prioL_in)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
.

Definition OSMutexCreate_full_partial_solve_wit_33_enabled_nonempty := OSMutexCreate_full_partial_solve_wit_33_enabled_nonempty_pure -> OSMutexCreate_full_partial_solve_wit_33_enabled_nonempty_aux.

Definition OSMutexCreate_full_partial_solve_wit_34_enabled_empty_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH2 : (prio_pre <> 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre < 63)) (PreH8 : (prio_pre <> 255)) (PreH9 : (prio_pre = prio_in)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : (pd = perr_pre)) (PreH13 : (perr_pre <> 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH18 : (freelist_in = 0)) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (store_priotbl_list sg (replace_Znth (prio_in) (1) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 63) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ”
.

Definition OSMutexCreate_full_partial_solve_wit_34_enabled_empty_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (PreH1 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH2 : (prio_pre <> 255)) (PreH3 : (RTrans_C sg ls0 sg ls1 )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (prio_pre < 63)) (PreH8 : (prio_pre <> 255)) (PreH9 : (prio_pre = prio_in)) (PreH10 : (0 <= prio_in)) (PreH11 : (prio_in <= 255)) (PreH12 : (pd = perr_pre)) (PreH13 : (perr_pre <> 0)) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (0 <= isr)) (PreH16 : (isr <= 255)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH18 : (freelist_in = 0)) ,
  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (store_priotbl_list sg (replace_Znth (prio_in) (1) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 63) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_priotbl_list sg (replace_Znth (prio_in) (1) (prioL_in)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
.

Definition OSMutexCreate_full_partial_solve_wit_34_enabled_empty := OSMutexCreate_full_partial_solve_wit_34_enabled_empty_pure -> OSMutexCreate_full_partial_solve_wit_34_enabled_empty_aux.

Definition OSMutexCreate_full_partial_solve_wit_35_disabled_empty_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre = 255)) (PreH2 : (RTrans_C sg ls0 sg ls1 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (prio_pre = 255)) (PreH7 : (prio_pre = prio_in)) (PreH8 : (0 <= prio_in)) (PreH9 : (prio_in <= 255)) (PreH10 : (pd = perr_pre)) (PreH11 : (perr_pre <> 0)) (PreH12 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH16 : (freelist_in = 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (prio_in = 255) ”
.

Definition OSMutexCreate_full_partial_solve_wit_35_disabled_empty_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre = 255)) (PreH2 : (RTrans_C sg ls0 sg ls1 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (prio_pre = 255)) (PreH7 : (prio_pre = prio_in)) (PreH8 : (0 <= prio_in)) (PreH9 : (prio_in <= 255)) (PreH10 : (pd = perr_pre)) (PreH11 : (perr_pre <> 0)) (PreH12 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH16 : (freelist_in = 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_priotbl_list sg prioL_in )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
.

Definition OSMutexCreate_full_partial_solve_wit_35_disabled_empty := OSMutexCreate_full_partial_solve_wit_35_disabled_empty_pure -> OSMutexCreate_full_partial_solve_wit_35_disabled_empty_aux.

Definition OSMutexCreate_full_partial_solve_wit_36_disabled_nonempty_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (retval: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre = 255)) (PreH2 : (RTrans_C sg ls0 sg ls1 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (prio_pre = 255)) (PreH7 : (prio_pre = prio_in)) (PreH8 : (0 <= prio_in)) (PreH9 : (prio_in <= 255)) (PreH10 : (pd = perr_pre)) (PreH11 : (perr_pre <> 0)) (PreH12 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH16 : (freelist_in <> 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pevent" ) )) # Ptr  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (prio_in = 255) ”
.

Definition OSMutexCreate_full_partial_solve_wit_36_disabled_nonempty_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre = 255)) (PreH2 : (RTrans_C sg ls0 sg ls1 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (prio_pre = 255)) (PreH7 : (prio_pre = prio_in)) (PreH8 : (0 <= prio_in)) (PreH9 : (prio_in <= 255)) (PreH10 : (pd = perr_pre)) (PreH11 : (perr_pre <> 0)) (PreH12 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH13 : (0 <= isr)) (PreH14 : (isr <= 255)) (PreH15 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH16 : (freelist_in <> 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_priotbl_list sg prioL_in )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
.

Definition OSMutexCreate_full_partial_solve_wit_36_disabled_nonempty := OSMutexCreate_full_partial_solve_wit_36_disabled_nonempty_pure -> OSMutexCreate_full_partial_solve_wit_36_disabled_nonempty_aux.

Definition OSMutexCreate_full_partial_solve_wit_37_enabled_empty_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (freelist_in = 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH4 : (RTrans_C sg ls0 sg ls1_2 )) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (isr <= 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH16 : (prio_pre <> 255)) (PreH17 : (RTrans_C sg ls0 sg ls1 )) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (isr <= 0)) (PreH20 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH21 : (prio_pre < 63)) (PreH22 : (prio_pre <> 255)) (PreH23 : (prio_pre = prio_in)) (PreH24 : (0 <= prio_in)) (PreH25 : (prio_in <= 255)) (PreH26 : (pd = perr_pre)) (PreH27 : (perr_pre <> 0)) (PreH28 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH29 : (0 <= isr)) (PreH30 : (isr <= 255)) (PreH31 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH32 : (freelist_in = 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ (prio_in <> 255) ”
.

Definition OSMutexCreate_full_partial_solve_wit_37_enabled_empty_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (freelist_in = 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH4 : (RTrans_C sg ls0 sg ls1_2 )) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (isr <= 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH16 : (prio_pre <> 255)) (PreH17 : (RTrans_C sg ls0 sg ls1 )) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (isr <= 0)) (PreH20 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH21 : (prio_pre < 63)) (PreH22 : (prio_pre <> 255)) (PreH23 : (prio_pre = prio_in)) (PreH24 : (0 <= prio_in)) (PreH25 : (prio_in <= 255)) (PreH26 : (pd = perr_pre)) (PreH27 : (perr_pre <> 0)) (PreH28 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH29 : (0 <= isr)) (PreH30 : (isr <= 255)) (PreH31 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH32 : (freelist_in = 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (freelist_in = 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_37_enabled_empty := OSMutexCreate_full_partial_solve_wit_37_enabled_empty_pure -> OSMutexCreate_full_partial_solve_wit_37_enabled_empty_aux.

Definition OSMutexCreate_full_partial_solve_wit_38_enabled_empty_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (freelist_in = 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH4 : (RTrans_C sg ls0 sg ls1_2 )) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (isr <= 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH16 : (prio_pre <> 255)) (PreH17 : (RTrans_C sg ls0 sg ls1 )) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (isr <= 0)) (PreH20 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH21 : (prio_pre < 63)) (PreH22 : (prio_pre <> 255)) (PreH23 : (prio_pre = prio_in)) (PreH24 : (0 <= prio_in)) (PreH25 : (prio_in <= 255)) (PreH26 : (pd = perr_pre)) (PreH27 : (perr_pre <> 0)) (PreH28 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH29 : (0 <= isr)) (PreH30 : (isr <= 255)) (PreH31 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH32 : (freelist_in = 0)) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_priotbl_list_missing_i sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) prio_in )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ (prio_in <> 255) ”
.

Definition OSMutexCreate_full_partial_solve_wit_38_enabled_empty_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre <> 255)) (PreH2 : (freelist_in = 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH4 : (RTrans_C sg ls0 sg ls1_2 )) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (isr <= 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH16 : (prio_pre <> 255)) (PreH17 : (RTrans_C sg ls0 sg ls1 )) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (isr <= 0)) (PreH20 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH21 : (prio_pre < 63)) (PreH22 : (prio_pre <> 255)) (PreH23 : (prio_pre = prio_in)) (PreH24 : (0 <= prio_in)) (PreH25 : (prio_in <= 255)) (PreH26 : (pd = perr_pre)) (PreH27 : (perr_pre <> 0)) (PreH28 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH29 : (0 <= isr)) (PreH30 : (isr <= 255)) (PreH31 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH32 : (freelist_in = 0)) ,
  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_priotbl_list_missing_i sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) prio_in )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (freelist_in = 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_priotbl_list_missing_i sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) prio_in )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_38_enabled_empty := OSMutexCreate_full_partial_solve_wit_38_enabled_empty_pure -> OSMutexCreate_full_partial_solve_wit_38_enabled_empty_aux.

Definition OSMutexCreate_full_partial_solve_wit_39_disabled_empty_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre = 255)) (PreH2 : (freelist_in = 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH4 : (RTrans_C sg ls0 sg ls1_2 )) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (isr <= 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_in = 255)) (PreH13 : (prio_pre = 255)) (PreH14 : (RTrans_C sg ls0 sg ls1 )) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (isr <= 0)) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (prio_pre = 255)) (PreH19 : (prio_pre = prio_in)) (PreH20 : (0 <= prio_in)) (PreH21 : (prio_in <= 255)) (PreH22 : (pd = perr_pre)) (PreH23 : (perr_pre <> 0)) (PreH24 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH25 : (0 <= isr)) (PreH26 : (isr <= 255)) (PreH27 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH28 : (freelist_in = 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (prio_in = 255) ”
.

Definition OSMutexCreate_full_partial_solve_wit_39_disabled_empty_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (PreH1 : (prio_pre = 255)) (PreH2 : (freelist_in = 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH4 : (RTrans_C sg ls0 sg ls1_2 )) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (isr <= 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_in = 255)) (PreH13 : (prio_pre = 255)) (PreH14 : (RTrans_C sg ls0 sg ls1 )) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (isr <= 0)) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (prio_pre = 255)) (PreH19 : (prio_pre = prio_in)) (PreH20 : (0 <= prio_in)) (PreH21 : (prio_in <= 255)) (PreH22 : (pd = perr_pre)) (PreH23 : (perr_pre <> 0)) (PreH24 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH25 : (0 <= isr)) (PreH26 : (isr <= 255)) (PreH27 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH28 : (freelist_in = 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (freelist_in = 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_39_disabled_empty := OSMutexCreate_full_partial_solve_wit_39_disabled_empty_pure -> OSMutexCreate_full_partial_solve_wit_39_disabled_empty_aux.

Definition OSMutexCreate_full_partial_solve_wit_40_enabled_empty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH2 : (RTrans_C sg ls0 sg ls1_3 )) (PreH3 : (0 <= prio_in)) (PreH4 : (prio_in <= 255)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (0 <= isr)) (PreH7 : (isr <= 255)) (PreH8 : (isr <= 0)) (PreH9 : (freelist_in = 0)) (PreH10 : (pd <> 0)) (PreH11 : (prio_pre <> 255)) (PreH12 : (freelist_in = 0)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH14 : (RTrans_C sg ls0 sg ls1_2 )) (PreH15 : (0 <= prio_in)) (PreH16 : (prio_in <= 255)) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (0 <= isr)) (PreH19 : (isr <= 255)) (PreH20 : (isr <= 0)) (PreH21 : (pd <> 0)) (PreH22 : (prio_in <> 255)) (PreH23 : (0 <= prio_in)) (PreH24 : (prio_in < 64)) (PreH25 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH26 : (prio_pre <> 255)) (PreH27 : (RTrans_C sg ls0 sg ls1 )) (PreH28 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH29 : (isr <= 0)) (PreH30 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH31 : (prio_pre < 63)) (PreH32 : (prio_pre <> 255)) (PreH33 : (prio_pre = prio_in)) (PreH34 : (0 <= prio_in)) (PreH35 : (prio_in <= 255)) (PreH36 : (pd = perr_pre)) (PreH37 : (perr_pre <> 0)) (PreH38 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH39 : (0 <= isr)) (PreH40 : (isr <= 255)) (PreH41 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH42 : (freelist_in = 0)) ,
  (InsideCritical sg ls1_3 )
  **  (mutex_create_head_open_inv sg ls1_3 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_3.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_3 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (freelist_in = 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (freelist_in = 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (InsideCritical sg ls1_3 )
  **  (mutex_create_head_open_inv sg ls1_3 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_3.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_41_disabled_empty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH2 : (RTrans_C sg ls0 sg ls1_3 )) (PreH3 : (0 <= prio_in)) (PreH4 : (prio_in <= 255)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (0 <= isr)) (PreH7 : (isr <= 255)) (PreH8 : (isr <= 0)) (PreH9 : (freelist_in = 0)) (PreH10 : (pd <> 0)) (PreH11 : (prio_pre = 255)) (PreH12 : (freelist_in = 0)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH14 : (RTrans_C sg ls0 sg ls1_2 )) (PreH15 : (0 <= prio_in)) (PreH16 : (prio_in <= 255)) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (0 <= isr)) (PreH19 : (isr <= 255)) (PreH20 : (isr <= 0)) (PreH21 : (pd <> 0)) (PreH22 : (prio_in = 255)) (PreH23 : (prio_pre = 255)) (PreH24 : (RTrans_C sg ls0 sg ls1 )) (PreH25 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH26 : (isr <= 0)) (PreH27 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH28 : (prio_pre = 255)) (PreH29 : (prio_pre = prio_in)) (PreH30 : (0 <= prio_in)) (PreH31 : (prio_in <= 255)) (PreH32 : (pd = perr_pre)) (PreH33 : (perr_pre <> 0)) (PreH34 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH35 : (0 <= isr)) (PreH36 : (isr <= 255)) (PreH37 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH38 : (freelist_in = 0)) ,
  (InsideCritical sg ls1_3 )
  **  (mutex_create_head_open_inv sg ls1_3 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_3.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_3 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (freelist_in = 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (freelist_in = 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (InsideCritical sg ls1_3 )
  **  (mutex_create_head_open_inv sg ls1_3 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_3.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_42_disabled_empty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls1_4: UCOS2_Verify_State) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH2 : (RTrans_C sg ls0 sg ls1_3 )) (PreH3 : (0 <= prio_in)) (PreH4 : (prio_in <= 255)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (0 <= isr)) (PreH7 : (isr <= 255)) (PreH8 : (isr <= 0)) (PreH9 : (freelist_in = 0)) (PreH10 : (pd <> 0)) (PreH11 : (prio_pre = 255)) (PreH12 : (freelist_in = 0)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH14 : (RTrans_C sg ls0 sg ls1_2 )) (PreH15 : (0 <= prio_in)) (PreH16 : (prio_in <= 255)) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (0 <= isr)) (PreH19 : (isr <= 255)) (PreH20 : (isr <= 0)) (PreH21 : (pd <> 0)) (PreH22 : (prio_in = 255)) (PreH23 : (prio_pre = 255)) (PreH24 : (RTrans_C sg ls0 sg ls1 )) (PreH25 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH26 : (isr <= 0)) (PreH27 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH28 : (prio_pre = 255)) (PreH29 : (prio_pre = prio_in)) (PreH30 : (0 <= prio_in)) (PreH31 : (prio_in <= 255)) (PreH32 : (pd = perr_pre)) (PreH33 : (perr_pre <> 0)) (PreH34 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH35 : (0 <= isr)) (PreH36 : (isr <= 255)) (PreH37 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH38 : (freelist_in = 0)) ,
  (InsideCritical sg ls1_4 )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_4)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_3 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (freelist_in = 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (freelist_in = 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (InsideCritical sg ls1_4 )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_4)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_43_enabled_empty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls1_4: UCOS2_Verify_State) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH2 : (RTrans_C sg ls0 sg ls1_3 )) (PreH3 : (0 <= prio_in)) (PreH4 : (prio_in <= 255)) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (0 <= isr)) (PreH7 : (isr <= 255)) (PreH8 : (isr <= 0)) (PreH9 : (freelist_in = 0)) (PreH10 : (pd <> 0)) (PreH11 : (prio_pre <> 255)) (PreH12 : (freelist_in = 0)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH14 : (RTrans_C sg ls0 sg ls1_2 )) (PreH15 : (0 <= prio_in)) (PreH16 : (prio_in <= 255)) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (0 <= isr)) (PreH19 : (isr <= 255)) (PreH20 : (isr <= 0)) (PreH21 : (pd <> 0)) (PreH22 : (prio_in <> 255)) (PreH23 : (0 <= prio_in)) (PreH24 : (prio_in < 64)) (PreH25 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH26 : (prio_pre <> 255)) (PreH27 : (RTrans_C sg ls0 sg ls1 )) (PreH28 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH29 : (isr <= 0)) (PreH30 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH31 : (prio_pre < 63)) (PreH32 : (prio_pre <> 255)) (PreH33 : (prio_pre = prio_in)) (PreH34 : (0 <= prio_in)) (PreH35 : (prio_in <= 255)) (PreH36 : (pd = perr_pre)) (PreH37 : (perr_pre <> 0)) (PreH38 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH39 : (0 <= isr)) (PreH40 : (isr <= 255)) (PreH41 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH42 : (freelist_in = 0)) ,
  (InsideCritical sg ls1_4 )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_4)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_3 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (freelist_in = 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (freelist_in = 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (InsideCritical sg ls1_4 )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_4)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_44_enabled_empty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls1_4: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_4 sg ls_post )) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH3 : (RTrans_C sg ls0 sg ls1_3 )) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : (isr <= 0)) (PreH10 : (freelist_in = 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_pre <> 255)) (PreH13 : (freelist_in = 0)) (PreH14 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH15 : (RTrans_C sg ls0 sg ls1_2 )) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (0 <= isr)) (PreH20 : (isr <= 255)) (PreH21 : (isr <= 0)) (PreH22 : (pd <> 0)) (PreH23 : (prio_in <> 255)) (PreH24 : (0 <= prio_in)) (PreH25 : (prio_in < 64)) (PreH26 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH27 : (prio_pre <> 255)) (PreH28 : (RTrans_C sg ls0 sg ls1 )) (PreH29 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH30 : (isr <= 0)) (PreH31 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH32 : (prio_pre < 63)) (PreH33 : (prio_pre <> 255)) (PreH34 : (prio_pre = prio_in)) (PreH35 : (0 <= prio_in)) (PreH36 : (prio_in <= 255)) (PreH37 : (pd = perr_pre)) (PreH38 : (perr_pre <> 0)) (PreH39 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH40 : (0 <= isr)) (PreH41 : (isr <= 255)) (PreH42 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH43 : (freelist_in = 0)) ,
  (OutsideCritical sg ls_post )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (mutex_create_restore_transition_prop (sg) (ls0) (ls1_4) (ls_post) (prio_in) (eid) (free_rest) (false)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (GTrans_C sg ls1_4 sg ls_post ) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_3 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (freelist_in = 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (freelist_in = 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (coq_prop (mutex_create_restore_transition_prop (sg) (ls0) (ls1_4) (ls_post) (prio_in) (eid) (free_rest) (false)) )
  **  (OutsideCritical sg ls_post )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_45_disabled_empty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls1_4: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_4 sg ls_post )) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH3 : (RTrans_C sg ls0 sg ls1_3 )) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : (isr <= 0)) (PreH10 : (freelist_in = 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_pre = 255)) (PreH13 : (freelist_in = 0)) (PreH14 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH15 : (RTrans_C sg ls0 sg ls1_2 )) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in <= 255)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (0 <= isr)) (PreH20 : (isr <= 255)) (PreH21 : (isr <= 0)) (PreH22 : (pd <> 0)) (PreH23 : (prio_in = 255)) (PreH24 : (prio_pre = 255)) (PreH25 : (RTrans_C sg ls0 sg ls1 )) (PreH26 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH27 : (isr <= 0)) (PreH28 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH29 : (prio_pre = 255)) (PreH30 : (prio_pre = prio_in)) (PreH31 : (0 <= prio_in)) (PreH32 : (prio_in <= 255)) (PreH33 : (pd = perr_pre)) (PreH34 : (perr_pre <> 0)) (PreH35 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH36 : (0 <= isr)) (PreH37 : (isr <= 255)) (PreH38 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH39 : (freelist_in = 0)) ,
  (OutsideCritical sg ls_post )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (mutex_create_restore_transition_prop (sg) (ls0) (ls1_4) (ls_post) (prio_in) (eid) (free_rest) (false)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (GTrans_C sg ls1_4 sg ls_post ) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_3 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (freelist_in = 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (freelist_in = 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in = 0) ”
  &&  (coq_prop (mutex_create_restore_transition_prop (sg) (ls0) (ls1_4) (ls_post) (prio_in) (eid) (free_rest) (false)) )
  **  (OutsideCritical sg ls_post )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_46_enabled_nonempty_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (freelist_in <> 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH3 : (RTrans_C sg ls0 sg ls1_2 )) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : (isr <= 0)) (PreH10 : (pd <> 0)) (PreH11 : (prio_in <> 255)) (PreH12 : (0 <= prio_in)) (PreH13 : (prio_in < 64)) (PreH14 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH15 : (prio_pre <> 255)) (PreH16 : (RTrans_C sg ls0 sg ls1 )) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (isr <= 0)) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (prio_pre < 63)) (PreH21 : (prio_pre <> 255)) (PreH22 : (prio_pre = prio_in)) (PreH23 : (0 <= prio_in)) (PreH24 : (prio_in <= 255)) (PreH25 : (pd = perr_pre)) (PreH26 : (perr_pre <> 0)) (PreH27 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH28 : (0 <= isr)) (PreH29 : (isr <= 255)) (PreH30 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH31 : (freelist_in <> 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (freelist_in <> 0) ”
.

Definition OSMutexCreate_full_partial_solve_wit_46_enabled_nonempty_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (PreH1 : (freelist_in <> 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH3 : (RTrans_C sg ls0 sg ls1_2 )) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : (isr <= 0)) (PreH10 : (pd <> 0)) (PreH11 : (prio_in <> 255)) (PreH12 : (0 <= prio_in)) (PreH13 : (prio_in < 64)) (PreH14 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH15 : (prio_pre <> 255)) (PreH16 : (RTrans_C sg ls0 sg ls1 )) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (isr <= 0)) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (prio_pre < 63)) (PreH21 : (prio_pre <> 255)) (PreH22 : (prio_pre = prio_in)) (PreH23 : (0 <= prio_in)) (PreH24 : (prio_in <= 255)) (PreH25 : (pd = perr_pre)) (PreH26 : (perr_pre <> 0)) (PreH27 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH28 : (0 <= isr)) (PreH29 : (isr <= 255)) (PreH30 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH31 : (freelist_in <> 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_46_enabled_nonempty := OSMutexCreate_full_partial_solve_wit_46_enabled_nonempty_pure -> OSMutexCreate_full_partial_solve_wit_46_enabled_nonempty_aux.

Definition OSMutexCreate_full_partial_solve_wit_47_disabled_nonempty_pure := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (PreH1 : (freelist_in <> 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH3 : (RTrans_C sg ls0 sg ls1_2 )) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : (isr <= 0)) (PreH10 : (pd <> 0)) (PreH11 : (prio_in = 255)) (PreH12 : (prio_pre = 255)) (PreH13 : (RTrans_C sg ls0 sg ls1 )) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (isr <= 0)) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (prio_pre = 255)) (PreH18 : (prio_pre = prio_in)) (PreH19 : (0 <= prio_in)) (PreH20 : (prio_in <= 255)) (PreH21 : (pd = perr_pre)) (PreH22 : (perr_pre <> 0)) (PreH23 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH24 : (0 <= isr)) (PreH25 : (isr <= 255)) (PreH26 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH27 : (freelist_in <> 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (freelist_in <> 0) ”
.

Definition OSMutexCreate_full_partial_solve_wit_47_disabled_nonempty_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (PreH1 : (freelist_in <> 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH3 : (RTrans_C sg ls0 sg ls1_2 )) (PreH4 : (0 <= prio_in)) (PreH5 : (prio_in <= 255)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (0 <= isr)) (PreH8 : (isr <= 255)) (PreH9 : (isr <= 0)) (PreH10 : (pd <> 0)) (PreH11 : (prio_in = 255)) (PreH12 : (prio_pre = 255)) (PreH13 : (RTrans_C sg ls0 sg ls1 )) (PreH14 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH15 : (isr <= 0)) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (prio_pre = 255)) (PreH18 : (prio_pre = prio_in)) (PreH19 : (0 <= prio_in)) (PreH20 : (prio_in <= 255)) (PreH21 : (pd = perr_pre)) (PreH22 : (perr_pre <> 0)) (PreH23 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH24 : (0 <= isr)) (PreH25 : (isr <= 255)) (PreH26 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH27 : (freelist_in <> 0)) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
|--
  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_47_disabled_nonempty := OSMutexCreate_full_partial_solve_wit_47_disabled_nonempty_pure -> OSMutexCreate_full_partial_solve_wit_47_disabled_nonempty_aux.

Definition OSMutexCreate_full_partial_solve_wit_48_enabled_nonempty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (PreH1 : (freelist_in <> 0)) (PreH2 : (freelist_in <> 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH4 : (RTrans_C sg ls0 sg ls1_2 )) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (isr <= 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH16 : (prio_pre <> 255)) (PreH17 : (RTrans_C sg ls0 sg ls1 )) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (isr <= 0)) (PreH20 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH21 : (prio_pre < 63)) (PreH22 : (prio_pre <> 255)) (PreH23 : (prio_pre = prio_in)) (PreH24 : (0 <= prio_in)) (PreH25 : (prio_in <= 255)) (PreH26 : (pd = perr_pre)) (PreH27 : (perr_pre <> 0)) (PreH28 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH29 : (0 <= isr)) (PreH30 : (isr <= 255)) (PreH31 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH32 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (InsideCritical sg ls1_3 )
  **  (mutex_create_node_open_inv sg ls1_3 free_rest )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> next_in)
  **  (mutex_create_unused_event_no_ptr freelist_in )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> next_in)
  **  (mutex_create_unused_event_no_ptr freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (InsideCritical sg ls1_3 )
  **  (mutex_create_node_open_inv sg ls1_3 free_rest )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_49_disabled_nonempty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (PreH1 : (freelist_in <> 0)) (PreH2 : (freelist_in <> 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH4 : (RTrans_C sg ls0 sg ls1_2 )) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (isr <= 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_in = 255)) (PreH13 : (prio_pre = 255)) (PreH14 : (RTrans_C sg ls0 sg ls1 )) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (isr <= 0)) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (prio_pre = 255)) (PreH19 : (prio_pre = prio_in)) (PreH20 : (0 <= prio_in)) (PreH21 : (prio_in <= 255)) (PreH22 : (pd = perr_pre)) (PreH23 : (perr_pre <> 0)) (PreH24 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH25 : (0 <= isr)) (PreH26 : (isr <= 255)) (PreH27 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH28 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (InsideCritical sg ls1_3 )
  **  (mutex_create_node_open_inv sg ls1_3 free_rest )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> next_in)
  **  (mutex_create_unused_event_no_ptr freelist_in )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> next_in)
  **  (mutex_create_unused_event_no_ptr freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (InsideCritical sg ls1_3 )
  **  (mutex_create_node_open_inv sg ls1_3 free_rest )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_50_enabled_nonempty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (PreH1 : (freelist_in <> 0)) (PreH2 : (freelist_in <> 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH4 : (RTrans_C sg ls0 sg ls1_2 )) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (isr <= 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH16 : (prio_pre <> 255)) (PreH17 : (RTrans_C sg ls0 sg ls1 )) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (isr <= 0)) (PreH20 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH21 : (prio_pre < 63)) (PreH22 : (prio_pre <> 255)) (PreH23 : (prio_pre = prio_in)) (PreH24 : (0 <= prio_in)) (PreH25 : (prio_in <= 255)) (PreH26 : (pd = perr_pre)) (PreH27 : (perr_pre <> 0)) (PreH28 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH29 : (0 <= isr)) (PreH30 : (isr <= 255)) (PreH31 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH32 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (unused_complete_event sg freelist_in eid )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (InsideCritical sg ls1_3 )
  **  (mutex_create_node_open_inv sg ls1_3 free_rest )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (InsideCritical sg ls1_3 )
  **  (mutex_create_node_open_inv sg ls1_3 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (unused_complete_event sg freelist_in eid )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_51_disabled_nonempty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (PreH1 : (freelist_in <> 0)) (PreH2 : (freelist_in <> 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH4 : (RTrans_C sg ls0 sg ls1_2 )) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (isr <= 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_in = 255)) (PreH13 : (prio_pre = 255)) (PreH14 : (RTrans_C sg ls0 sg ls1 )) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (isr <= 0)) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (prio_pre = 255)) (PreH19 : (prio_pre = prio_in)) (PreH20 : (0 <= prio_in)) (PreH21 : (prio_in <= 255)) (PreH22 : (pd = perr_pre)) (PreH23 : (perr_pre <> 0)) (PreH24 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH25 : (0 <= isr)) (PreH26 : (isr <= 255)) (PreH27 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH28 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (unused_complete_event sg freelist_in eid )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (InsideCritical sg ls1_3 )
  **  (mutex_create_node_open_inv sg ls1_3 free_rest )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (InsideCritical sg ls1_3 )
  **  (mutex_create_node_open_inv sg ls1_3 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (unused_complete_event sg freelist_in eid )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_3.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_52_disabled_nonempty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (PreH1 : (freelist_in <> 0)) (PreH2 : (freelist_in <> 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH4 : (RTrans_C sg ls0 sg ls1_2 )) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (isr <= 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_in = 255)) (PreH13 : (prio_pre = 255)) (PreH14 : (RTrans_C sg ls0 sg ls1 )) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (isr <= 0)) (PreH17 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH18 : (prio_pre = 255)) (PreH19 : (prio_pre = prio_in)) (PreH20 : (0 <= prio_in)) (PreH21 : (prio_in <= 255)) (PreH22 : (pd = perr_pre)) (PreH23 : (perr_pre <> 0)) (PreH24 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH25 : (0 <= isr)) (PreH26 : (isr <= 255)) (PreH27 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH28 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (InsideCritical sg ls1_3 )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in true )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (InsideCritical sg ls1_3 )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in true )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_53_enabled_nonempty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (PreH1 : (freelist_in <> 0)) (PreH2 : (freelist_in <> 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH4 : (RTrans_C sg ls0 sg ls1_2 )) (PreH5 : (0 <= prio_in)) (PreH6 : (prio_in <= 255)) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (0 <= isr)) (PreH9 : (isr <= 255)) (PreH10 : (isr <= 0)) (PreH11 : (pd <> 0)) (PreH12 : (prio_in <> 255)) (PreH13 : (0 <= prio_in)) (PreH14 : (prio_in < 64)) (PreH15 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH16 : (prio_pre <> 255)) (PreH17 : (RTrans_C sg ls0 sg ls1 )) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (isr <= 0)) (PreH20 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH21 : (prio_pre < 63)) (PreH22 : (prio_pre <> 255)) (PreH23 : (prio_pre = prio_in)) (PreH24 : (0 <= prio_in)) (PreH25 : (prio_in <= 255)) (PreH26 : (pd = perr_pre)) (PreH27 : (perr_pre <> 0)) (PreH28 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH29 : (0 <= isr)) (PreH30 : (isr <= 255)) (PreH31 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH32 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (InsideCritical sg ls1_3 )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in true )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (InsideCritical sg ls1_3 )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in true )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_3)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_54_enabled_nonempty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in <> 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in < 64)) (PreH16 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH17 : (prio_pre <> 255)) (PreH18 : (RTrans_C sg ls0 sg ls1 )) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (isr <= 0)) (PreH21 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (pd = perr_pre)) (PreH28 : (perr_pre <> 0)) (PreH29 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH30 : (0 <= isr)) (PreH31 : (isr <= 255)) (PreH32 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH33 : (freelist_in <> 0)) ,
  (OutsideCritical sg ls_post )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in true )
  **  (coq_prop (mutex_create_restore_transition_prop (sg) (ls0) (ls1_3) (ls_post) (prio_in) (eid) (free_rest) (true)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (GTrans_C sg ls1_3 sg ls_post ) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in true )
  **  (coq_prop (mutex_create_restore_transition_prop (sg) (ls0) (ls1_3) (ls_post) (prio_in) (eid) (free_rest) (true)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_55_disabled_nonempty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in = 255)) (PreH14 : (prio_pre = 255)) (PreH15 : (RTrans_C sg ls0 sg ls1 )) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (prio_pre = 255)) (PreH20 : (prio_pre = prio_in)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in <= 255)) (PreH23 : (pd = perr_pre)) (PreH24 : (perr_pre <> 0)) (PreH25 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH26 : (0 <= isr)) (PreH27 : (isr <= 255)) (PreH28 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH29 : (freelist_in <> 0)) ,
  (OutsideCritical sg ls_post )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in true )
  **  (coq_prop (mutex_create_restore_transition_prop (sg) (ls0) (ls1_3) (ls_post) (prio_in) (eid) (free_rest) (true)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (GTrans_C sg ls1_3 sg ls_post ) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in true )
  **  (coq_prop (mutex_create_restore_transition_prop (sg) (ls0) (ls1_3) (ls_post) (prio_in) (eid) (free_rest) (true)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_56_enabled_nonempty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in <> 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in < 64)) (PreH16 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH17 : (prio_pre <> 255)) (PreH18 : (RTrans_C sg ls0 sg ls1 )) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (isr <= 0)) (PreH21 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (pd = perr_pre)) (PreH28 : (perr_pre <> 0)) (PreH29 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH30 : (0 <= isr)) (PreH31 : (isr <= 255)) (PreH32 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH33 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (unused_complete_event sg freelist_in eid )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (GTrans_C sg ls1_3 sg ls_post ) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  (unused_complete_event sg freelist_in eid )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_57_disabled_nonempty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in = 255)) (PreH14 : (prio_pre = 255)) (PreH15 : (RTrans_C sg ls0 sg ls1 )) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (prio_pre = 255)) (PreH20 : (prio_pre = prio_in)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in <= 255)) (PreH23 : (pd = perr_pre)) (PreH24 : (perr_pre <> 0)) (PreH25 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH26 : (0 <= isr)) (PreH27 : (isr <= 255)) (PreH28 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH29 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (unused_complete_event sg freelist_in eid )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (GTrans_C sg ls1_3 sg ls_post ) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  (unused_complete_event sg freelist_in eid )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_58_disabled_nonempty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in = 255)) (PreH14 : (prio_pre = 255)) (PreH15 : (RTrans_C sg ls0 sg ls1 )) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (prio_pre = 255)) (PreH20 : (prio_pre = prio_in)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in <= 255)) (PreH23 : (pd = perr_pre)) (PreH24 : (perr_pre <> 0)) (PreH25 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH26 : (0 <= isr)) (PreH27 : (isr <= 255)) (PreH28 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH29 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255))
  **  (mutex_create_wait_table_uninitialized freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (GTrans_C sg ls1_3 sg ls_post ) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (mutex_create_wait_table_uninitialized freelist_in )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255))
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_59_enabled_nonempty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in <> 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in < 64)) (PreH16 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH17 : (prio_pre <> 255)) (PreH18 : (RTrans_C sg ls0 sg ls1 )) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (isr <= 0)) (PreH21 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (pd = perr_pre)) (PreH28 : (perr_pre <> 0)) (PreH29 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH30 : (0 <= isr)) (PreH31 : (isr <= 255)) (PreH32 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH33 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255))
  **  (mutex_create_wait_table_uninitialized freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (GTrans_C sg ls1_3 sg ls_post ) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (mutex_create_wait_table_uninitialized freelist_in )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255))
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_60_enabled_nonempty_pure := 
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in <> 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in < 64)) (PreH16 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH17 : (prio_pre <> 255)) (PreH18 : (RTrans_C sg ls0 sg ls1 )) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (isr <= 0)) (PreH21 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (pd = perr_pre)) (PreH28 : (perr_pre <> 0)) (PreH29 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH30 : (0 <= isr)) (PreH31 : (isr <= 255)) (PreH32 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH33 : (freelist_in <> 0)) ,
  (mutex_create_wait_table_zero freelist_in )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255))
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl prio_in 8)) (16)) 255) = ((prio_in * 256 ) + 255 )) ”
) \/
(
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (cpu_sr_v <= UINT_MAX)) (PreH2 : (cpu_sr_v >= 0)) (PreH3 : (GTrans_C sg ls1_3 sg ls_post )) (PreH4 : (freelist_in <> 0)) (PreH5 : (freelist_in <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH7 : (RTrans_C sg ls0 sg ls1_2 )) (PreH8 : (0 <= prio_in)) (PreH9 : (prio_in <= 255)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (isr <= 0)) (PreH14 : (pd <> 0)) (PreH15 : (prio_in <> 255)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in < 64)) (PreH18 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH19 : (prio_pre <> 255)) (PreH20 : (RTrans_C sg ls0 sg ls1 )) (PreH21 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH22 : (isr <= 0)) (PreH23 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH24 : (prio_pre < 63)) (PreH25 : (prio_pre <> 255)) (PreH26 : (prio_pre = prio_in)) (PreH27 : (0 <= prio_in)) (PreH28 : (prio_in <= 255)) (PreH29 : (pd = perr_pre)) (PreH30 : (perr_pre <> 0)) (PreH31 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH32 : (0 <= isr)) (PreH33 : (isr <= 255)) (PreH34 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH35 : (freelist_in <> 0)) ,
  (mutex_create_wait_table_zero freelist_in )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255))
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl prio_in 8)) (16)) 255) = ((prio_in * 256 ) + 255 )) ”
).

Definition OSMutexCreate_full_partial_solve_wit_60_enabled_nonempty_pure_split_goal_1 := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (cpu_sr_v: Z) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (cpu_sr_v <= UINT_MAX)) (PreH2 : (cpu_sr_v >= 0)) (PreH3 : (GTrans_C sg ls1_3 sg ls_post )) (PreH4 : (freelist_in <> 0)) (PreH5 : (freelist_in <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH7 : (RTrans_C sg ls0 sg ls1_2 )) (PreH8 : (0 <= prio_in)) (PreH9 : (prio_in <= 255)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (0 <= isr)) (PreH12 : (isr <= 255)) (PreH13 : (isr <= 0)) (PreH14 : (pd <> 0)) (PreH15 : (prio_in <> 255)) (PreH16 : (0 <= prio_in)) (PreH17 : (prio_in < 64)) (PreH18 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH19 : (prio_pre <> 255)) (PreH20 : (RTrans_C sg ls0 sg ls1 )) (PreH21 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH22 : (isr <= 0)) (PreH23 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH24 : (prio_pre < 63)) (PreH25 : (prio_pre <> 255)) (PreH26 : (prio_pre = prio_in)) (PreH27 : (0 <= prio_in)) (PreH28 : (prio_in <= 255)) (PreH29 : (pd = perr_pre)) (PreH30 : (perr_pre <> 0)) (PreH31 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH32 : (0 <= isr)) (PreH33 : (isr <= 255)) (PreH34 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH35 : (freelist_in <> 0)) ,
  (mutex_create_wait_table_zero freelist_in )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255))
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pevent" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl prio_in 8)) (16)) 255) = ((prio_in * 256 ) + 255 )) ”
.

Definition OSMutexCreate_full_partial_solve_wit_60_enabled_nonempty_aux := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in <> 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in < 64)) (PreH16 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH17 : (prio_pre <> 255)) (PreH18 : (RTrans_C sg ls0 sg ls1 )) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (isr <= 0)) (PreH21 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (pd = perr_pre)) (PreH28 : (perr_pre <> 0)) (PreH29 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH30 : (0 <= isr)) (PreH31 : (isr <= 255)) (PreH32 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH33 : (freelist_in <> 0)) ,
  (mutex_create_wait_table_zero freelist_in )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255))
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ ((Z.lor (unsigned_last_nbits ((Z.shiftl prio_in 8)) (16)) 255) = ((prio_in * 256 ) + 255 )) ” 
  &&  “ (GTrans_C sg ls1_3 sg ls_post ) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((prio_in * 256 ) + 255 ))
  **  (mutex_create_wait_table_zero freelist_in )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_60_enabled_nonempty := OSMutexCreate_full_partial_solve_wit_60_enabled_nonempty_pure -> OSMutexCreate_full_partial_solve_wit_60_enabled_nonempty_aux.

Definition OSMutexCreate_full_partial_solve_wit_61_disabled_nonempty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in = 255)) (PreH14 : (prio_pre = 255)) (PreH15 : (RTrans_C sg ls0 sg ls1 )) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (prio_pre = 255)) (PreH20 : (prio_pre = prio_in)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in <= 255)) (PreH23 : (pd = perr_pre)) (PreH24 : (perr_pre <> 0)) (PreH25 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH26 : (0 <= isr)) (PreH27 : (isr <= 255)) (PreH28 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH29 : (freelist_in <> 0)) ,
  (mutex_create_wait_table_zero freelist_in )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (Z.lor (unsigned_last_nbits ((Z.shiftl prio_pre 8)) (16)) 255))
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (GTrans_C sg ls1_3 sg ls_post ) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((prio_in * 256 ) + 255 ))
  **  (mutex_create_wait_table_zero freelist_in )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_62_enabled_nonempty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in <> 255)) (PreH14 : (0 <= prio_in)) (PreH15 : (prio_in < 64)) (PreH16 : ((Znth (prio_in) (prioL_in) (0)) = 0)) (PreH17 : (prio_pre <> 255)) (PreH18 : (RTrans_C sg ls0 sg ls1 )) (PreH19 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH20 : (isr <= 0)) (PreH21 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH22 : (prio_pre < 63)) (PreH23 : (prio_pre <> 255)) (PreH24 : (prio_pre = prio_in)) (PreH25 : (0 <= prio_in)) (PreH26 : (prio_in <= 255)) (PreH27 : (pd = perr_pre)) (PreH28 : (perr_pre <> 0)) (PreH29 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH30 : (0 <= isr)) (PreH31 : (isr <= 255)) (PreH32 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH33 : (freelist_in <> 0)) ,
  (OutsideCritical sg ls_post_2 )
  **  (mutex_create_initialized_event sg ls_post_2 prio_in eid )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (GTrans_C sg ls1_3 sg ls_post ) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ” 
  &&  “ ((Znth (prio_in) (prioL_in) (0)) = 0) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (prio_pre <> 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (OutsideCritical sg ls_post_2 )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (mutex_create_initialized_event sg ls_post_2 prio_in eid )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_partial_solve_wit_63_disabled_nonempty := 
forall (perr_pre: Z) (prio_pre: Z) (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (pd: Z) (perr_in: Z) (prio_in: Z) (isr: Z) (eid: Z) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1: UCOS2_Verify_State) (ls1_2: UCOS2_Verify_State) (ls1_3: UCOS2_Verify_State) (ls_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) (PreH1 : (GTrans_C sg ls1_3 sg ls_post )) (PreH2 : (freelist_in <> 0)) (PreH3 : (freelist_in <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH5 : (RTrans_C sg ls0 sg ls1_2 )) (PreH6 : (0 <= prio_in)) (PreH7 : (prio_in <= 255)) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (0 <= isr)) (PreH10 : (isr <= 255)) (PreH11 : (isr <= 0)) (PreH12 : (pd <> 0)) (PreH13 : (prio_in = 255)) (PreH14 : (prio_pre = 255)) (PreH15 : (RTrans_C sg ls0 sg ls1 )) (PreH16 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH17 : (isr <= 0)) (PreH18 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH19 : (prio_pre = 255)) (PreH20 : (prio_pre = prio_in)) (PreH21 : (0 <= prio_in)) (PreH22 : (prio_in <= 255)) (PreH23 : (pd = perr_pre)) (PreH24 : (perr_pre <> 0)) (PreH25 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH26 : (0 <= isr)) (PreH27 : (isr <= 255)) (PreH28 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X )) (PreH29 : (freelist_in <> 0)) ,
  (OutsideCritical sg ls_post_2 )
  **  (mutex_create_initialized_event sg ls_post_2 prio_in eid )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (GTrans_C sg ls1_3 sg ls_post ) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (freelist_in <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_in))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (RTrans_C sg ls0 sg ls1_2 ) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pd <> 0) ” 
  &&  “ (prio_in = 255) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (RTrans_C sg ls0 sg ls1 ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (prio_pre = 255) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in <= 255) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (0 <= isr) ” 
  &&  “ (isr <= 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexCreate_sem (sg) (prio_pre))))) ((observe_mutex_create_ptr (sg)))) X ) ” 
  &&  “ (freelist_in <> 0) ”
  &&  (OutsideCritical sg ls_post_2 )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (mutex_create_initialized_event sg ls_post_2 prio_in eid )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (mutex_create_priority_input_prop (prio_pre) (prio_in)) )
  **  ((pd) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_which_implies_wit_1 := 
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

Definition OSMutexCreate_full_which_implies_wit_1_split_goal_spatial := 
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (UCOS2_Verify_inv sg ls0 )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
.

Definition OSMutexCreate_full_which_implies_wit_2 := 
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

Definition OSMutexCreate_full_which_implies_wit_2_split_goal_spatial := 
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
.

Definition OSMutexCreate_full_which_implies_wit_3 := 
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

Definition OSMutexCreate_full_which_implies_wit_3_split_goal_spatial := 
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (UCOS2_Verify_inv_no_int_nesting sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
.

Definition OSMutexCreate_full_which_implies_wit_4 := 
(
forall (prioL_in: (@list Z)) (freelist_in: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1_2: UCOS2_Verify_State) ,
  (InsideCritical sg ls1_2 )
  **  (UCOS2_Verify_inv sg ls1_2 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
|--
  EX (ls1: UCOS2_Verify_State) ,
  (InsideCritical sg ls1 )
  **  (mutex_create_head_open_inv sg ls1 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
) \/
(
forall (prioL_in: (@list Z)) (freelist_in: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1_2: UCOS2_Verify_State) ,
  (InsideCritical sg ls1_2 )
  **  (UCOS2_Verify_inv sg ls1_2 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
|--
  EX (ls1: UCOS2_Verify_State) ,
  (InsideCritical sg ls1 )
  **  (mutex_create_head_open_inv sg ls1 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
).

Definition OSMutexCreate_full_which_implies_wit_5 := 
(
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in < 64)) ,
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (store_priotbl_list sg prioL_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (Znth (prio_in) (prioL_in) (0)))
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
) \/
(
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in < 64)) ,
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (store_priotbl_list sg prioL_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (Znth (prio_in) (prioL_in) (0)))
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexCreate_full_which_implies_wit_5_split_goal_spatial := 
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in < 64)) ,
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (store_priotbl_list sg prioL_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (Znth (prio_in) (prioL_in) (0)))
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_which_implies_wit_6 := 
(
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in < 64)) ,
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (Znth (prio_in) (prioL_in) (0)))
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (store_priotbl_list sg prioL_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
) \/
(
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in < 64)) ,
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (Znth (prio_in) (prioL_in) (0)))
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (store_priotbl_list sg prioL_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexCreate_full_which_implies_wit_6_split_goal_spatial := 
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in < 64)) ,
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> (Znth (prio_in) (prioL_in) (0)))
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (store_priotbl_list sg prioL_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_which_implies_wit_7 := 
(
forall (prioL_in: (@list Z)) (free_rest: (@list Z)) (freelist_in: Z) (prio_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1_2: UCOS2_Verify_State) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
|--
  EX (ls1: UCOS2_Verify_State) ,
  (InsideCritical sg ls1 )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
) \/
(
forall (prioL_in: (@list Z)) (free_rest: (@list Z)) (freelist_in: Z) (prio_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1_2: UCOS2_Verify_State) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
|--
  EX (ls1: UCOS2_Verify_State) ,
  (InsideCritical sg ls1 )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
).

Definition OSMutexCreate_full_which_implies_wit_8 := 
(
forall (prioL_in: (@list Z)) (free_rest: (@list Z)) (prio_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_post: UCOS2_Verify_State) (ls_inside_post: UCOS2_Verify_State) ,
  (coq_prop (mutex_create_restore_transition_prop (sg) (ls0) (ls_inside_post) (ls_post) (prio_in) (eid) (free_rest) (false)) )
  **  (OutsideCritical sg ls_post )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
) \/
(
forall (prioL_in: (@list Z)) (free_rest: (@list Z)) (prio_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_post: UCOS2_Verify_State) (ls_inside_post: UCOS2_Verify_State) ,
  (coq_prop (mutex_create_restore_transition_prop (sg) (ls0) (ls_inside_post) (ls_post) (prio_in) (eid) (free_rest) (false)) )
  **  (OutsideCritical sg ls_post )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
).

Definition OSMutexCreate_full_which_implies_wit_8_split_goal_spatial := 
forall (prioL_in: (@list Z)) (free_rest: (@list Z)) (prio_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_post: UCOS2_Verify_State) (ls_inside_post: UCOS2_Verify_State) ,
  (coq_prop (mutex_create_restore_transition_prop (sg) (ls0) (ls_inside_post) (ls_post) (prio_in) (eid) (free_rest) (false)) )
  **  (OutsideCritical sg ls_post )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
.

Definition OSMutexCreate_full_which_implies_wit_9 := 
(
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in < 64)) ,
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> 1)
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (store_priotbl_list sg (replace_Znth (prio_in) (1) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
) \/
(
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in < 64)) ,
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> 1)
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (store_priotbl_list sg (replace_Znth (prio_in) (1) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexCreate_full_which_implies_wit_9_split_goal_spatial := 
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in < 64)) ,
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> 1)
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (store_priotbl_list sg (replace_Znth (prio_in) (1) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_which_implies_wit_10 := 
(
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (PreH1 : (prio_in <> 255)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in < 63)) (PreH4 : ((Znth (prio_in) (prioL_in) (0)) = 0)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_priotbl_list sg (replace_Znth (prio_in) (1) (prioL_in)) )
|--
  “ (prio_in <> 255) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ”
  &&  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
) \/
(
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (PreH1 : (prio_in <> 255)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in < 63)) (PreH4 : ((Znth (prio_in) (prioL_in) (0)) = 0)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_priotbl_list sg (replace_Znth (prio_in) (1) (prioL_in)) )
|--
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
).

Definition OSMutexCreate_full_which_implies_wit_10_split_goal_spatial := 
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (PreH1 : (prio_in <> 255)) (PreH2 : (0 <= prio_in)) (PreH3 : (prio_in < 63)) (PreH4 : ((Znth (prio_in) (prioL_in) (0)) = 0)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_priotbl_list sg (replace_Znth (prio_in) (1) (prioL_in)) )
|--
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
.

Definition OSMutexCreate_full_which_implies_wit_11 := 
(
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (PreH1 : (prio_in = 255)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_priotbl_list sg prioL_in )
|--
  “ (prio_in = 255) ”
  &&  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
) \/
(
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (PreH1 : (prio_in = 255)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_priotbl_list sg prioL_in )
|--
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
).

Definition OSMutexCreate_full_which_implies_wit_11_split_goal_spatial := 
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (PreH1 : (prio_in = 255)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (store_priotbl_list sg prioL_in )
|--
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
.

Definition OSMutexCreate_full_which_implies_wit_12 := 
(
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in < 64)) (PreH3 : (prio_in <> 255)) ,
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> 1)
  **  (store_priotbl_list_missing_i sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) prio_in )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
) \/
(
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in < 64)) (PreH3 : (prio_in <> 255)) ,
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> 1)
  **  (store_priotbl_list_missing_i sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) prio_in )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexCreate_full_which_implies_wit_12_split_goal_spatial := 
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in < 64)) (PreH3 : (prio_in <> 255)) ,
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> 1)
  **  (store_priotbl_list_missing_i sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) prio_in )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_which_implies_wit_13 := 
(
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in < 64)) (PreH3 : (prio_in <> 255)) ,
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_priotbl_list_missing_i sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) prio_in )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (store_priotbl_list sg prioL_in )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
) \/
(
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in < 64)) (PreH3 : (prio_in <> 255)) ,
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_priotbl_list_missing_i sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) prio_in )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (store_priotbl_list sg prioL_in )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexCreate_full_which_implies_wit_13_split_goal_spatial := 
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (prio: Z) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in < 64)) (PreH3 : (prio_in <> 255)) ,
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (((( &( "OSTCBPrioTbl" ) ) + (prio * sizeof(PTR)))) # Ptr  |-> 0)
  **  (store_priotbl_list_missing_i sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) prio_in )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (coq_prop (mutex_create_priority_input_prop (prio) (prio_in)) )
  **  (store_priotbl_list sg prioL_in )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexCreate_full_which_implies_wit_14 := 
(
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (PreH1 : (prio_in = 255)) ,
  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
|--
  (store_priotbl_list sg prioL_in )
) \/
(
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (PreH1 : (prio_in = 255)) ,
  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
|--
  (store_priotbl_list sg prioL_in )
).

Definition OSMutexCreate_full_which_implies_wit_14_split_goal_spatial := 
forall (prioL_in: (@list Z)) (prio_in: Z) (sg: StableGlobVars) (PreH1 : (prio_in = 255)) ,
  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
|--
  (store_priotbl_list sg prioL_in )
.

Definition OSMutexCreate_full_which_implies_wit_15 := 
(
forall (prioL_in: (@list Z)) (free_rest: (@list Z)) (freelist_in: Z) (prio_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1_2: UCOS2_Verify_State) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
|--
  EX (ls1: UCOS2_Verify_State) ,
  (InsideCritical sg ls1 )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
) \/
(
forall (prioL_in: (@list Z)) (free_rest: (@list Z)) (freelist_in: Z) (prio_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1_2: UCOS2_Verify_State) ,
  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls1_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
|--
  EX (ls1: UCOS2_Verify_State) ,
  (InsideCritical sg ls1 )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
).

Definition OSMutexCreate_full_which_implies_wit_16 := 
(
forall (prioL_in: (@list Z)) (free_rest: (@list Z)) (prio_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_post: UCOS2_Verify_State) (ls_inside_post: UCOS2_Verify_State) ,
  (coq_prop (mutex_create_restore_transition_prop (sg) (ls0) (ls_inside_post) (ls_post) (prio_in) (eid) (free_rest) (false)) )
  **  (OutsideCritical sg ls_post )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
|--
  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
) \/
(
forall (prioL_in: (@list Z)) (free_rest: (@list Z)) (prio_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_post: UCOS2_Verify_State) (ls_inside_post: UCOS2_Verify_State) ,
  (coq_prop (mutex_create_restore_transition_prop (sg) (ls0) (ls_inside_post) (ls_post) (prio_in) (eid) (free_rest) (false)) )
  **  (OutsideCritical sg ls_post )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
|--
  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
).

Definition OSMutexCreate_full_which_implies_wit_16_split_goal_spatial := 
forall (prioL_in: (@list Z)) (free_rest: (@list Z)) (prio_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_post: UCOS2_Verify_State) (ls_inside_post: UCOS2_Verify_State) ,
  (coq_prop (mutex_create_restore_transition_prop (sg) (ls0) (ls_inside_post) (ls_post) (prio_in) (eid) (free_rest) (false)) )
  **  (OutsideCritical sg ls_post )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in false )
|--
  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
.

Definition OSMutexCreate_full_which_implies_wit_17 := 
(
forall (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1_2: UCOS2_Verify_State) (PreH1 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  EX (ls1: UCOS2_Verify_State) ,
  “ (freelist_in <> 0) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (InsideCritical sg ls1 )
  **  (mutex_create_node_open_inv sg ls1 free_rest )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> next_in)
  **  (mutex_create_unused_event_no_ptr freelist_in )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
) \/
(
forall (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1_2: UCOS2_Verify_State) (PreH1 : (freelist_in <> 0)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_head_open_inv sg ls1_2 )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_free_snapshot_prop (sg) (ls0) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  EX (ls1: UCOS2_Verify_State) ,
  “ (freelist_in <> 0) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (InsideCritical sg ls1 )
  **  (mutex_create_node_open_inv sg ls1 free_rest )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> next_in)
  **  (mutex_create_unused_event_no_ptr freelist_in )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
).

Definition OSMutexCreate_full_which_implies_wit_18 := 
(
forall (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> next_in)
  **  (mutex_create_unused_event_no_ptr freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (unused_complete_event sg freelist_in eid )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
) \/
(
forall (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> next_in)
  **  (mutex_create_unused_event_no_ptr freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (unused_complete_event sg freelist_in eid )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
).

Definition OSMutexCreate_full_which_implies_wit_18_split_goal_spatial := 
forall (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> next_in)
  **  (mutex_create_unused_event_no_ptr freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (unused_complete_event sg freelist_in eid )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
.

Definition OSMutexCreate_full_which_implies_wit_19 := 
(
forall (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (prio_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1_2: UCOS2_Verify_State) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_node_open_inv sg ls1_2 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (unused_complete_event sg freelist_in eid )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
|--
  EX (ls1: UCOS2_Verify_State) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (InsideCritical sg ls1 )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in true )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
) \/
(
forall (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (prio_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls1_2: UCOS2_Verify_State) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (InsideCritical sg ls1_2 )
  **  (mutex_create_node_open_inv sg ls1_2 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (unused_complete_event sg freelist_in eid )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1_2)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls1_2.(TskState) )) (prioL_in)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
|--
  EX (ls1: UCOS2_Verify_State) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (InsideCritical sg ls1 )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in true )
  **  (coq_prop (crit_rel_no_os_state_change (ls0) (ls1)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (task_event_id_unreferenced_prop (ls0) (eid)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
).

Definition OSMutexCreate_full_which_implies_wit_20 := 
(
forall (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (prio_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_inside_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in true )
  **  (coq_prop (mutex_create_restore_transition_prop (sg) (ls0) (ls_inside_post) (ls_post_2) (prio_in) (eid) (free_rest) (true)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (unused_complete_event sg freelist_in eid )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
) \/
(
forall (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (prio_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_inside_post: UCOS2_Verify_State) (ls_post_2: UCOS2_Verify_State) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (mutex_create_restore_frame sg ls0 prio_in eid free_rest prioL_in true )
  **  (coq_prop (mutex_create_restore_transition_prop (sg) (ls0) (ls_inside_post) (ls_post_2) (prio_in) (eid) (free_rest) (true)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (unused_complete_event sg freelist_in eid )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
).

Definition OSMutexCreate_full_which_implies_wit_21 := 
(
forall (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (prio_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_post_2: UCOS2_Verify_State) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  (unused_complete_event sg freelist_in eid )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |->_)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |->_)
  **  (mutex_create_wait_table_uninitialized freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
) \/
(
forall (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (prio_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_post_2: UCOS2_Verify_State) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  (unused_complete_event sg freelist_in eid )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  EX (x_2: Z)  (x: Z)  (ls_post: UCOS2_Verify_State) ,
  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> x_2)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> x)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post) (prio_in) (eid) (free_rest)) )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  (mutex_create_wait_table_uninitialized freelist_in )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
).

Definition OSMutexCreate_full_which_implies_wit_22 := 
(
forall (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (prio_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_post_2: UCOS2_Verify_State) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((prio_in * 256 ) + 255 ))
  **  (mutex_create_wait_table_zero freelist_in )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  (OutsideCritical sg ls_post )
  **  (mutex_create_initialized_event sg ls_post prio_in eid )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
) \/
(
forall (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (prio_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_post_2: UCOS2_Verify_State) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((freelist_in)  # "os_event" ->ₛ "OSEventType")) (&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) (&((freelist_in)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (OutsideCritical sg ls_post_2 )
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&((freelist_in)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ((prio_in * 256 ) + 255 ))
  **  (mutex_create_wait_table_zero freelist_in )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  (OutsideCritical sg ls_post )
  **  (mutex_create_initialized_event sg ls_post prio_in eid )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
).

Definition OSMutexCreate_full_which_implies_wit_23 := 
(
forall (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (prio_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_post_2: UCOS2_Verify_State) ,
  (OutsideCritical sg ls_post_2 )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (mutex_create_initialized_event sg ls_post_2 prio_in eid )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
) \/
(
forall (prioL_in: (@list Z)) (free_rest: (@list Z)) (next_in: Z) (freelist_in: Z) (prio_in: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_post_2: UCOS2_Verify_State) ,
  (OutsideCritical sg ls_post_2 )
  **  (mutex_create_node_open_inv sg ls0 free_rest )
  **  (store_priotbl_list sg (mutex_create_priotbl_after (sg) (prio_in) (prioL_in)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> next_in)
  **  (mutex_create_initialized_event sg ls_post_2 prio_in eid )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post_2) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_create_success_transition_prop (sg) (ls0) (ls_post) (prio_in) (eid) (free_rest)) )
  **  (coq_prop (event_free_head_snapshot_prop (sg) ((ls0.(EventState) )) (eid) (free_rest) (freelist_in) (next_in)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (valid_mutex_pcp (sg) (prio_in)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (mutex_create_pcp_slot_available_prop (sg) (prio_in) (prioL_in)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
).

Module Type VC_Correct.


Axiom proof_of_OSMutexCreate_full_safety_wit_1 : OSMutexCreate_full_safety_wit_1.
Axiom proof_of_OSMutexCreate_full_safety_wit_2 : OSMutexCreate_full_safety_wit_2.
Axiom proof_of_OSMutexCreate_full_safety_wit_3 : OSMutexCreate_full_safety_wit_3.
Axiom proof_of_OSMutexCreate_full_safety_wit_4 : OSMutexCreate_full_safety_wit_4.
Axiom proof_of_OSMutexCreate_full_safety_wit_5 : OSMutexCreate_full_safety_wit_5.
Axiom proof_of_OSMutexCreate_full_safety_wit_6 : OSMutexCreate_full_safety_wit_6.
Axiom proof_of_OSMutexCreate_full_safety_wit_7 : OSMutexCreate_full_safety_wit_7.
Axiom proof_of_OSMutexCreate_full_safety_wit_8 : OSMutexCreate_full_safety_wit_8.
Axiom proof_of_OSMutexCreate_full_safety_wit_9 : OSMutexCreate_full_safety_wit_9.
Axiom proof_of_OSMutexCreate_full_safety_wit_10 : OSMutexCreate_full_safety_wit_10.
Axiom proof_of_OSMutexCreate_full_safety_wit_11 : OSMutexCreate_full_safety_wit_11.
Axiom proof_of_OSMutexCreate_full_safety_wit_12 : OSMutexCreate_full_safety_wit_12.
Axiom proof_of_OSMutexCreate_full_safety_wit_13 : OSMutexCreate_full_safety_wit_13.
Axiom proof_of_OSMutexCreate_full_safety_wit_14 : OSMutexCreate_full_safety_wit_14.
Axiom proof_of_OSMutexCreate_full_safety_wit_15 : OSMutexCreate_full_safety_wit_15.
Axiom proof_of_OSMutexCreate_full_safety_wit_16 : OSMutexCreate_full_safety_wit_16.
Axiom proof_of_OSMutexCreate_full_safety_wit_17 : OSMutexCreate_full_safety_wit_17.
Axiom proof_of_OSMutexCreate_full_safety_wit_18 : OSMutexCreate_full_safety_wit_18.
Axiom proof_of_OSMutexCreate_full_safety_wit_19_disabled_empty : OSMutexCreate_full_safety_wit_19_disabled_empty.
Axiom proof_of_OSMutexCreate_full_safety_wit_20_disabled_nonempty : OSMutexCreate_full_safety_wit_20_disabled_nonempty.
Axiom proof_of_OSMutexCreate_full_safety_wit_21_enabled_nonempty : OSMutexCreate_full_safety_wit_21_enabled_nonempty.
Axiom proof_of_OSMutexCreate_full_safety_wit_22_enabled_empty : OSMutexCreate_full_safety_wit_22_enabled_empty.
Axiom proof_of_OSMutexCreate_full_safety_wit_23_disabled_empty : OSMutexCreate_full_safety_wit_23_disabled_empty.
Axiom proof_of_OSMutexCreate_full_safety_wit_24_disabled_nonempty : OSMutexCreate_full_safety_wit_24_disabled_nonempty.
Axiom proof_of_OSMutexCreate_full_safety_wit_25_enabled_nonempty : OSMutexCreate_full_safety_wit_25_enabled_nonempty.
Axiom proof_of_OSMutexCreate_full_safety_wit_26_enabled_empty : OSMutexCreate_full_safety_wit_26_enabled_empty.
Axiom proof_of_OSMutexCreate_full_safety_wit_27_disabled_empty : OSMutexCreate_full_safety_wit_27_disabled_empty.
Axiom proof_of_OSMutexCreate_full_safety_wit_28_enabled_empty : OSMutexCreate_full_safety_wit_28_enabled_empty.
Axiom proof_of_OSMutexCreate_full_safety_wit_29_enabled_empty : OSMutexCreate_full_safety_wit_29_enabled_empty.
Axiom proof_of_OSMutexCreate_full_safety_wit_30_disabled_nonempty : OSMutexCreate_full_safety_wit_30_disabled_nonempty.
Axiom proof_of_OSMutexCreate_full_safety_wit_31_enabled_nonempty : OSMutexCreate_full_safety_wit_31_enabled_nonempty.
Axiom proof_of_OSMutexCreate_full_safety_wit_32_disabled_nonempty : OSMutexCreate_full_safety_wit_32_disabled_nonempty.
Axiom proof_of_OSMutexCreate_full_safety_wit_33_enabled_nonempty : OSMutexCreate_full_safety_wit_33_enabled_nonempty.
Axiom proof_of_OSMutexCreate_full_entail_wit_1_disabled_empty : OSMutexCreate_full_entail_wit_1_disabled_empty.
Axiom proof_of_OSMutexCreate_full_entail_wit_2_disabled_nonempty : OSMutexCreate_full_entail_wit_2_disabled_nonempty.
Axiom proof_of_OSMutexCreate_full_entail_wit_3_enabled_nonempty : OSMutexCreate_full_entail_wit_3_enabled_nonempty.
Axiom proof_of_OSMutexCreate_full_entail_wit_4_enabled_empty : OSMutexCreate_full_entail_wit_4_enabled_empty.
Axiom proof_of_OSMutexCreate_full_entail_wit_5_disabled_empty : OSMutexCreate_full_entail_wit_5_disabled_empty.
Axiom proof_of_OSMutexCreate_full_entail_wit_6_enabled_empty : OSMutexCreate_full_entail_wit_6_enabled_empty.
Axiom proof_of_OSMutexCreate_full_entail_wit_7_enabled_nonempty : OSMutexCreate_full_entail_wit_7_enabled_nonempty.
Axiom proof_of_OSMutexCreate_full_entail_wit_8_disabled_nonempty : OSMutexCreate_full_entail_wit_8_disabled_nonempty.
Axiom proof_of_OSMutexCreate_full_return_wit_1_enabled_nonempty : OSMutexCreate_full_return_wit_1_enabled_nonempty.
Axiom proof_of_OSMutexCreate_full_return_wit_2_disabled_nonempty : OSMutexCreate_full_return_wit_2_disabled_nonempty.
Axiom proof_of_OSMutexCreate_full_return_wit_3_disabled_empty : OSMutexCreate_full_return_wit_3_disabled_empty.
Axiom proof_of_OSMutexCreate_full_return_wit_4_enabled_empty : OSMutexCreate_full_return_wit_4_enabled_empty.
Axiom proof_of_OSMutexCreate_full_return_wit_5 : OSMutexCreate_full_return_wit_5.
Axiom proof_of_OSMutexCreate_full_return_wit_6 : OSMutexCreate_full_return_wit_6.
Axiom proof_of_OSMutexCreate_full_return_wit_7 : OSMutexCreate_full_return_wit_7.
Axiom proof_of_OSMutexCreate_full_return_wit_8 : OSMutexCreate_full_return_wit_8.
Axiom proof_of_OSMutexCreate_full_return_wit_9 : OSMutexCreate_full_return_wit_9.
Axiom proof_of_OSMutexCreate_full_return_wit_10 : OSMutexCreate_full_return_wit_10.
Axiom proof_of_OSMutexCreate_full_return_wit_11 : OSMutexCreate_full_return_wit_11.
Axiom proof_of_OSMutexCreate_full_return_wit_12 : OSMutexCreate_full_return_wit_12.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_1_pure : OSMutexCreate_full_partial_solve_wit_1_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_1 : OSMutexCreate_full_partial_solve_wit_1.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_2_pure : OSMutexCreate_full_partial_solve_wit_2_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_2 : OSMutexCreate_full_partial_solve_wit_2.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_3_pure : OSMutexCreate_full_partial_solve_wit_3_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_3 : OSMutexCreate_full_partial_solve_wit_3.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_4_pure : OSMutexCreate_full_partial_solve_wit_4_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_4 : OSMutexCreate_full_partial_solve_wit_4.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_5_pure : OSMutexCreate_full_partial_solve_wit_5_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_5 : OSMutexCreate_full_partial_solve_wit_5.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_6_pure : OSMutexCreate_full_partial_solve_wit_6_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_6 : OSMutexCreate_full_partial_solve_wit_6.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_7_pure : OSMutexCreate_full_partial_solve_wit_7_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_7 : OSMutexCreate_full_partial_solve_wit_7.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_8_pure : OSMutexCreate_full_partial_solve_wit_8_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_8 : OSMutexCreate_full_partial_solve_wit_8.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_9_pure : OSMutexCreate_full_partial_solve_wit_9_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_9 : OSMutexCreate_full_partial_solve_wit_9.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_10_pure : OSMutexCreate_full_partial_solve_wit_10_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_10 : OSMutexCreate_full_partial_solve_wit_10.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_11_pure : OSMutexCreate_full_partial_solve_wit_11_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_11 : OSMutexCreate_full_partial_solve_wit_11.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_12_pure : OSMutexCreate_full_partial_solve_wit_12_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_12 : OSMutexCreate_full_partial_solve_wit_12.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_13 : OSMutexCreate_full_partial_solve_wit_13.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_14 : OSMutexCreate_full_partial_solve_wit_14.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_15 : OSMutexCreate_full_partial_solve_wit_15.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_16 : OSMutexCreate_full_partial_solve_wit_16.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_17 : OSMutexCreate_full_partial_solve_wit_17.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_18 : OSMutexCreate_full_partial_solve_wit_18.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_19 : OSMutexCreate_full_partial_solve_wit_19.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_20 : OSMutexCreate_full_partial_solve_wit_20.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_21_pure : OSMutexCreate_full_partial_solve_wit_21_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_21 : OSMutexCreate_full_partial_solve_wit_21.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_22_pure : OSMutexCreate_full_partial_solve_wit_22_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_22 : OSMutexCreate_full_partial_solve_wit_22.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_23_pure : OSMutexCreate_full_partial_solve_wit_23_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_23 : OSMutexCreate_full_partial_solve_wit_23.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_24_pure : OSMutexCreate_full_partial_solve_wit_24_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_24 : OSMutexCreate_full_partial_solve_wit_24.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_25 : OSMutexCreate_full_partial_solve_wit_25.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_26 : OSMutexCreate_full_partial_solve_wit_26.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_27 : OSMutexCreate_full_partial_solve_wit_27.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_28 : OSMutexCreate_full_partial_solve_wit_28.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_29 : OSMutexCreate_full_partial_solve_wit_29.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_30 : OSMutexCreate_full_partial_solve_wit_30.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_31_pure : OSMutexCreate_full_partial_solve_wit_31_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_31 : OSMutexCreate_full_partial_solve_wit_31.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_32_pure : OSMutexCreate_full_partial_solve_wit_32_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_32 : OSMutexCreate_full_partial_solve_wit_32.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_33_enabled_nonempty_pure : OSMutexCreate_full_partial_solve_wit_33_enabled_nonempty_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_33_enabled_nonempty : OSMutexCreate_full_partial_solve_wit_33_enabled_nonempty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_34_enabled_empty_pure : OSMutexCreate_full_partial_solve_wit_34_enabled_empty_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_34_enabled_empty : OSMutexCreate_full_partial_solve_wit_34_enabled_empty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_35_disabled_empty_pure : OSMutexCreate_full_partial_solve_wit_35_disabled_empty_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_35_disabled_empty : OSMutexCreate_full_partial_solve_wit_35_disabled_empty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_36_disabled_nonempty_pure : OSMutexCreate_full_partial_solve_wit_36_disabled_nonempty_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_36_disabled_nonempty : OSMutexCreate_full_partial_solve_wit_36_disabled_nonempty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_37_enabled_empty_pure : OSMutexCreate_full_partial_solve_wit_37_enabled_empty_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_37_enabled_empty : OSMutexCreate_full_partial_solve_wit_37_enabled_empty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_38_enabled_empty_pure : OSMutexCreate_full_partial_solve_wit_38_enabled_empty_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_38_enabled_empty : OSMutexCreate_full_partial_solve_wit_38_enabled_empty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_39_disabled_empty_pure : OSMutexCreate_full_partial_solve_wit_39_disabled_empty_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_39_disabled_empty : OSMutexCreate_full_partial_solve_wit_39_disabled_empty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_40_enabled_empty : OSMutexCreate_full_partial_solve_wit_40_enabled_empty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_41_disabled_empty : OSMutexCreate_full_partial_solve_wit_41_disabled_empty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_42_disabled_empty : OSMutexCreate_full_partial_solve_wit_42_disabled_empty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_43_enabled_empty : OSMutexCreate_full_partial_solve_wit_43_enabled_empty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_44_enabled_empty : OSMutexCreate_full_partial_solve_wit_44_enabled_empty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_45_disabled_empty : OSMutexCreate_full_partial_solve_wit_45_disabled_empty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_46_enabled_nonempty_pure : OSMutexCreate_full_partial_solve_wit_46_enabled_nonempty_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_46_enabled_nonempty : OSMutexCreate_full_partial_solve_wit_46_enabled_nonempty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_47_disabled_nonempty_pure : OSMutexCreate_full_partial_solve_wit_47_disabled_nonempty_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_47_disabled_nonempty : OSMutexCreate_full_partial_solve_wit_47_disabled_nonempty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_48_enabled_nonempty : OSMutexCreate_full_partial_solve_wit_48_enabled_nonempty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_49_disabled_nonempty : OSMutexCreate_full_partial_solve_wit_49_disabled_nonempty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_50_enabled_nonempty : OSMutexCreate_full_partial_solve_wit_50_enabled_nonempty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_51_disabled_nonempty : OSMutexCreate_full_partial_solve_wit_51_disabled_nonempty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_52_disabled_nonempty : OSMutexCreate_full_partial_solve_wit_52_disabled_nonempty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_53_enabled_nonempty : OSMutexCreate_full_partial_solve_wit_53_enabled_nonempty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_54_enabled_nonempty : OSMutexCreate_full_partial_solve_wit_54_enabled_nonempty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_55_disabled_nonempty : OSMutexCreate_full_partial_solve_wit_55_disabled_nonempty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_56_enabled_nonempty : OSMutexCreate_full_partial_solve_wit_56_enabled_nonempty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_57_disabled_nonempty : OSMutexCreate_full_partial_solve_wit_57_disabled_nonempty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_58_disabled_nonempty : OSMutexCreate_full_partial_solve_wit_58_disabled_nonempty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_59_enabled_nonempty : OSMutexCreate_full_partial_solve_wit_59_enabled_nonempty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_60_enabled_nonempty_pure : OSMutexCreate_full_partial_solve_wit_60_enabled_nonempty_pure.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_60_enabled_nonempty : OSMutexCreate_full_partial_solve_wit_60_enabled_nonempty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_61_disabled_nonempty : OSMutexCreate_full_partial_solve_wit_61_disabled_nonempty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_62_enabled_nonempty : OSMutexCreate_full_partial_solve_wit_62_enabled_nonempty.
Axiom proof_of_OSMutexCreate_full_partial_solve_wit_63_disabled_nonempty : OSMutexCreate_full_partial_solve_wit_63_disabled_nonempty.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_1 : OSMutexCreate_full_which_implies_wit_1.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_2 : OSMutexCreate_full_which_implies_wit_2.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_3 : OSMutexCreate_full_which_implies_wit_3.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_4 : OSMutexCreate_full_which_implies_wit_4.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_5 : OSMutexCreate_full_which_implies_wit_5.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_6 : OSMutexCreate_full_which_implies_wit_6.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_7 : OSMutexCreate_full_which_implies_wit_7.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_8 : OSMutexCreate_full_which_implies_wit_8.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_9 : OSMutexCreate_full_which_implies_wit_9.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_10 : OSMutexCreate_full_which_implies_wit_10.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_11 : OSMutexCreate_full_which_implies_wit_11.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_12 : OSMutexCreate_full_which_implies_wit_12.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_13 : OSMutexCreate_full_which_implies_wit_13.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_14 : OSMutexCreate_full_which_implies_wit_14.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_15 : OSMutexCreate_full_which_implies_wit_15.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_16 : OSMutexCreate_full_which_implies_wit_16.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_17 : OSMutexCreate_full_which_implies_wit_17.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_18 : OSMutexCreate_full_which_implies_wit_18.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_19 : OSMutexCreate_full_which_implies_wit_19.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_20 : OSMutexCreate_full_which_implies_wit_20.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_21 : OSMutexCreate_full_which_implies_wit_21.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_22 : OSMutexCreate_full_which_implies_wit_22.
Axiom proof_of_OSMutexCreate_full_which_implies_wit_23 : OSMutexCreate_full_which_implies_wit_23.

End VC_Correct.
