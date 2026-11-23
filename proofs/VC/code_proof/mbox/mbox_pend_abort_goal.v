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
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_pend_abort_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSMboxPendAbort -----*)

Definition OSMboxPendAbort_safety_wit_1 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = pe)) (PreH2 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH3 : (opt_pre = option)) (PreH4 : (mbox_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH7 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH8 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "nbr_tasks" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPendAbort_safety_wit_2 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (mbox_post_profile sg )) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH6 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (0 >= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (mbox_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH19 : (opt_pre = option)) (PreH20 : (mbox_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH23 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH24 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH25 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_abort_save_result environment critical saved_local sg caller mask retval before eid observed )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "nbr_tasks" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPendAbort_safety_wit_3 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (nbr_tasks: Z) (perr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (0 <= nbr_tasks)) (PreH3 : (nbr_tasks < 255)) (PreH4 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (mbox_pend_abort_output_address error_addr perr )) (PreH8 : (option = 1)) (PreH9 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH10 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> nbr_tasks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed nbr_tasks tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 2 2 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((perr) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPendAbort_safety_wit_4 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (0 = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (1 <> opt_pre)) (PreH30 : (0 = opt_pre)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid initial_2 tid old 2 2 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPendAbort_safety_wit_5 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (0 = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (1 <> opt_pre)) (PreH30 : (0 <> opt_pre)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid initial_2 tid old 2 2 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPendAbort_safety_wit_6 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (perr: Z) (nbr_tasks: Z) (cpu_sr: Z) (PreH1 : (mbox_pend_abort_output_address error_addr perr )) (PreH2 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH3 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_abort_restore_post environment critical saved_local sg caller mask pe eid option before nbr_tasks 14 1 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> nbr_tasks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((perr) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPendAbort_safety_wit_7 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (mbox_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH20 : (opt_pre = option)) (PreH21 : (mbox_post_profile sg )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH24 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH25 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_abort_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid option before 0 0 0 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "nbr_tasks" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMboxPendAbort_entail_wit_1 := 
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (mbox_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH7 : (pevent_pre <> 0)) (PreH8 : (pevent_pre = pe)) (PreH9 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH10 : (opt_pre = option)) (PreH11 : (mbox_post_profile sg )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH14 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH15 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_pend_abort_type_context environment saved_local sg caller mask before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "nbr_tasks" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (opt_pre = option) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_pend_abort_type_context environment saved_local sg caller mask before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "nbr_tasks" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (mbox_post_profile sg )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH12 : (opt_pre = option)) (PreH13 : (mbox_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH16 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH17 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  TT && emp 
|--
  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ”
  &&  emp
).

Definition OSMboxPendAbort_entail_wit_1_split_goal_1 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (mbox_post_profile sg )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH12 : (opt_pre = option)) (PreH13 : (mbox_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH16 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH17 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((event_slot_type_value ((EventState (before))) (eid)) <= 255)
.

Definition OSMboxPendAbort_entail_wit_1_split_goal_2 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (mbox_post_profile sg )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH12 : (opt_pre = option)) (PreH13 : (mbox_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH16 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH17 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (0 <= (event_slot_type_value ((EventState (before))) (eid)))
.

Definition OSMboxPendAbort_entail_wit_2 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (initial_3: OSEventAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (0 = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired_2) (initial_2))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (1 = opt_pre)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active_2 mask retval before acquired_3 eid observed initial_3 acquired_3 initial_3 (@nil Z) 0 )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_3) (initial_3)))
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState)  (processed: (@list Z)) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (option = 1) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask retval before acquired eid observed initial state node processed 0 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPendAbort_entail_wit_3 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (nbr_tasks: Z) (perr: Z) (active_2: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (state_3: UCOS2_Verify_State) (node_3: OSEventAbstractState) (processed_2: (@list Z)) (tid_2: Z) (old_2: TaskAbstractState) (retval: Z) (PreH1 : (0 <= nbr_tasks)) (PreH2 : (nbr_tasks < 255)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state_2) (node_2))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (mbox_pend_abort_output_address error_addr perr )) (PreH7 : (option = 1)) (PreH8 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH9 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (event_task_rdy_post sg (TskState (state_3)) eid node_3 tid_2 old_2 0 2 2 (q_post_sched_group (state_3)) (q_post_sched_rows (state_3)) retval )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 state_3 node_3 processed_2 nbr_tasks tid_2 old_2 )
  **  ((perr) # UChar  |->_)
|--
  EX (priority: Z)  (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState)  (processed: (@list Z))  (tid: Z)  (old: TaskAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr ) ” 
  &&  “ (option = 1) ” 
  &&  “ (0 <= nbr_tasks) ” 
  &&  “ (nbr_tasks < 255) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed nbr_tasks tid old )
  **  (event_task_rdy_post sg (TskState (state)) eid node tid old 0 2 2 (q_post_sched_group (state)) (q_post_sched_rows (state)) priority )
  **  ((perr) # UChar  |->_)
.

Definition OSMboxPendAbort_entail_wit_4 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (perr: Z) (nbr_tasks: Z) (cpu_sr: Z) (active_2: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (next: UCOS2_Verify_State) (next_node: OSEventAbstractState) (next_processed: (@list Z)) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (0 <= nbr_tasks)) (PreH3 : (nbr_tasks < 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (mbox_pend_abort_output_address error_addr perr )) (PreH7 : (option = 1)) (PreH8 : (0 <= nbr_tasks)) (PreH9 : (nbr_tasks < 255)) (PreH10 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH11 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 next next_node next_processed (nbr_tasks + 1 ) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (next) (next_node)))
  **  ((perr) # UChar  |->_)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState)  (processed: (@list Z)) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr ) ” 
  &&  “ (option = 1) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed (nbr_tasks + 1 ) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
.

Definition OSMboxPendAbort_entail_wit_5_1 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (initial_3: OSEventAbstractState) (tid_2: Z) (old_2: TaskAbstractState) (retval_2: Z) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired_2) (initial_2))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (mbox_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH20 : (opt_pre = option)) (PreH21 : (mbox_post_profile sg )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH24 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH25 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (1 <> opt_pre)) (PreH28 : (0 = opt_pre)) ,
  (event_task_rdy_post sg (TskState (acquired_3)) eid initial_3 tid_2 old_2 0 2 2 (q_post_sched_group (acquired_3)) (q_post_sched_rows (acquired_3)) retval_2 )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active_2 mask retval before acquired_3 eid observed initial_3 acquired_3 initial_3 (@nil Z) 0 tid_2 old_2 )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  EX (priority: Z)  (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (option <> 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask retval before acquired eid observed initial acquired initial (@nil Z) 0 tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid initial tid old 0 2 2 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPendAbort_entail_wit_5_2 := 
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (initial_3: OSEventAbstractState) (tid_2: Z) (old_2: TaskAbstractState) (retval_2: Z) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired_2) (initial_2))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (mbox_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH20 : (opt_pre = option)) (PreH21 : (mbox_post_profile sg )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH24 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH25 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (1 <> opt_pre)) (PreH28 : (0 <> opt_pre)) ,
  (event_task_rdy_post sg (TskState (acquired_3)) eid initial_3 tid_2 old_2 0 2 2 (q_post_sched_group (acquired_3)) (q_post_sched_rows (acquired_3)) retval_2 )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active_2 mask retval before acquired_3 eid observed initial_3 acquired_3 initial_3 (@nil Z) 0 tid_2 old_2 )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  EX (priority: Z)  (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (option <> 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask retval before acquired eid observed initial acquired initial (@nil Z) 0 tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid initial tid old 0 2 2 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired_2) (initial_2))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (mbox_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH20 : (opt_pre = option)) (PreH21 : (mbox_post_profile sg )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH24 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH25 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (1 <> opt_pre)) (PreH28 : (0 <> opt_pre)) ,
  TT && emp 
|--
  “ (opt_pre <= 255) ” 
  &&  “ (0 <= opt_pre) ”
  &&  emp
).

Definition OSMboxPendAbort_entail_wit_5_2_split_goal_1 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired_2) (initial_2))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (mbox_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH20 : (opt_pre = option)) (PreH21 : (mbox_post_profile sg )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH24 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH25 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (1 <> opt_pre)) (PreH28 : (0 <> opt_pre)) ,
  (opt_pre <= 255)
.

Definition OSMboxPendAbort_entail_wit_5_2_split_goal_2 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired_2) (initial_2))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (mbox_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH20 : (opt_pre = option)) (PreH21 : (mbox_post_profile sg )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH24 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH25 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH27 : (1 <> opt_pre)) (PreH28 : (0 <> opt_pre)) ,
  (0 <= opt_pre)
.

Definition OSMboxPendAbort_entail_wit_6_1 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (nbr_tasks: Z) (perr: Z) (active_2: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (released_2: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (mbox_pend_abort_output_address error_addr perr )) (PreH5 : (option = 1)) (PreH6 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH7 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_abort_restore_pre environment critical saved_local sg caller active_2 mask cpu_sr pe eid option before acquired_2 released_2 nbr_tasks 14 1 )
  **  ((perr) # UChar  |->_)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  “ (mbox_pend_abort_output_address error_addr perr ) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_pend_abort_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid option before acquired released nbr_tasks 14 1 )
  **  ((perr) # UChar  |->_)
.

Definition OSMboxPendAbort_entail_wit_6_2 := 
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (perr: Z) (nbr_tasks: Z) (cpu_sr: Z) (active_2: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (released_2: UCOS2_Verify_State) (PreH1 : (0 = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (mbox_pend_abort_output_address error_addr perr )) (PreH5 : (option <> 1)) (PreH6 : (nbr_tasks = 0)) (PreH7 : (0 <= option)) (PreH8 : (option <= 255)) (PreH9 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH10 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_abort_restore_pre environment critical saved_local sg caller active_2 mask cpu_sr pe eid option before acquired_2 released_2 1 14 1 )
  **  ((perr) # UChar  |->_)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  “ (mbox_pend_abort_output_address error_addr perr ) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_pend_abort_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid option before acquired released (0 + 1 ) 14 1 )
  **  ((perr) # UChar  |->_)
) \/
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (perr: Z) (nbr_tasks: Z) (cpu_sr: Z) (active_2: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (released_2: UCOS2_Verify_State) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (mbox_pend_abort_output_address error_addr perr )) (PreH4 : (option <> 1)) (PreH5 : (nbr_tasks = 0)) (PreH6 : (0 <= option)) (PreH7 : (option <= 255)) (PreH8 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH9 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_abort_restore_pre environment critical saved_local sg caller active_2 mask cpu_sr pe eid option before acquired_2 released_2 1 14 1 )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  “ (mbox_pend_abort_output_address error_addr perr ) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_pend_abort_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid option before acquired released (0 + 1 ) 14 1 )
).

Definition OSMboxPendAbort_return_wit_1 := 
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (mbox_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH20 : (opt_pre = option)) (PreH21 : (mbox_post_profile sg )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH24 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH25 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_abort_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid option before 0 0 0 )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (mbox_pend_abort_post environment critical saved_local sg caller mask pe eid option before error_addr 0 X )
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (mbox_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH20 : (opt_pre = option)) (PreH21 : (mbox_post_profile sg )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH24 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH25 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_abort_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid option before 0 0 0 )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (mbox_pend_abort_post environment critical saved_local sg caller mask pe eid option before error_addr 0 X )
).

Definition OSMboxPendAbort_return_wit_1_split_goal_spatial := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (mbox_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH20 : (opt_pre = option)) (PreH21 : (mbox_post_profile sg )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH24 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH25 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_abort_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid option before 0 0 0 )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (mbox_pend_abort_post environment critical saved_local sg caller mask pe eid option before error_addr 0 X )
.

Definition OSMboxPendAbort_return_wit_2 := 
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (perr: Z) (nbr_tasks: Z) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (mbox_pend_abort_prefix_result environment critical sg caller mask pe eid option before nbr_tasks 14 1 returned restored )) (PreH2 : (mbox_pend_abort_output_address error_addr perr )) (PreH3 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH4 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  ((perr) # UChar  |-> 14)
|--
  (mbox_pend_abort_post environment critical saved_local sg caller mask pe eid option before error_addr nbr_tasks X )
) \/
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (perr: Z) (nbr_tasks: Z) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (mbox_pend_abort_prefix_result environment critical sg caller mask pe eid option before nbr_tasks 14 1 returned restored )) (PreH2 : (mbox_pend_abort_output_address error_addr perr )) (PreH3 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH4 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  ((perr) # UChar  |-> 14)
|--
  (mbox_pend_abort_post environment critical saved_local sg caller mask pe eid option before error_addr nbr_tasks X )
).

Definition OSMboxPendAbort_return_wit_2_split_goal_spatial := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (perr: Z) (nbr_tasks: Z) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (mbox_pend_abort_prefix_result environment critical sg caller mask pe eid option before nbr_tasks 14 1 returned restored )) (PreH2 : (mbox_pend_abort_output_address error_addr perr )) (PreH3 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH4 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  ((perr) # UChar  |-> 14)
|--
  (mbox_pend_abort_post environment critical saved_local sg caller mask pe eid option before error_addr nbr_tasks X )
.

Definition OSMboxPendAbort_return_wit_3 := 
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (mbox_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH15 : (opt_pre = option)) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH20 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH21 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_pend_abort_type_context environment saved_local sg caller mask before eid )
  **  ((perr_pre) # UChar  |-> 1)
|--
  (mbox_pend_abort_post environment critical saved_local sg caller mask pe eid option before error_addr 0 X )
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (mbox_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH15 : (opt_pre = option)) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH20 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH21 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_pend_abort_type_context environment saved_local sg caller mask before eid )
  **  ((perr_pre) # UChar  |-> 1)
|--
  (mbox_pend_abort_post environment critical saved_local sg caller mask pe eid option before error_addr 0 X )
).

Definition OSMboxPendAbort_return_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (mbox_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH15 : (opt_pre = option)) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH20 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH21 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_pend_abort_type_context environment saved_local sg caller mask before eid )
  **  ((perr_pre) # UChar  |-> 1)
|--
  (mbox_pend_abort_post environment critical saved_local sg caller mask pe eid option before error_addr 0 X )
.

Definition OSMboxPendAbort_return_wit_4 := 
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH4 : (opt_pre = option)) (PreH5 : (mbox_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH8 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH9 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((perr_pre) # UChar  |-> 4)
|--
  (mbox_pend_abort_post environment critical saved_local sg caller mask pe eid option before error_addr 0 X )
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH4 : (opt_pre = option)) (PreH5 : (mbox_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH8 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH9 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((perr_pre) # UChar  |-> 4)
|--
  (mbox_pend_abort_post environment critical saved_local sg caller mask pe eid option before error_addr 0 X )
).

Definition OSMboxPendAbort_return_wit_4_split_goal_spatial := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH4 : (opt_pre = option)) (PreH5 : (mbox_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH8 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH9 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((perr_pre) # UChar  |-> 4)
|--
  (mbox_pend_abort_post environment critical saved_local sg caller mask pe eid option before error_addr 0 X )
.

Definition OSMboxPendAbort_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH4 : (opt_pre = option)) (PreH5 : (mbox_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH8 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH9 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "nbr_tasks" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ”
.

Definition OSMboxPendAbort_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH4 : (opt_pre = option)) (PreH5 : (mbox_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH8 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH9 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (opt_pre = option) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPendAbort_partial_solve_wit_1 := OSMboxPendAbort_partial_solve_wit_1_pure -> OSMboxPendAbort_partial_solve_wit_1_aux.

Definition OSMboxPendAbort_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (mbox_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH15 : (opt_pre = option)) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH20 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH21 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_pend_abort_type_context environment saved_local sg caller mask before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "nbr_tasks" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ”
.

Definition OSMboxPendAbort_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (mbox_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH15 : (opt_pre = option)) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH20 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH21 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_pend_abort_type_context environment saved_local sg caller mask before eid )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (opt_pre = option) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_pend_abort_type_context environment saved_local sg caller mask before eid )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPendAbort_partial_solve_wit_2 := OSMboxPendAbort_partial_solve_wit_2_pure -> OSMboxPendAbort_partial_solve_wit_2_aux.

Definition OSMboxPendAbort_partial_solve_wit_3 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (mbox_post_profile sg )) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH6 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (0 >= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (mbox_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH19 : (opt_pre = option)) (PreH20 : (mbox_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH23 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH24 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH25 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_abort_save_pre environment critical saved_local sg caller mask before pe eid observed )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (opt_pre = option) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_pend_abort_save_pre environment critical saved_local sg caller mask before (event_addr (sg) (eid)) eid observed )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPendAbort_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (mbox_post_profile sg )) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH6 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (0 >= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (mbox_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH19 : (opt_pre = option)) (PreH20 : (mbox_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH23 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH24 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH25 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_abort_save_result environment critical saved_local sg caller mask retval before eid observed )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "nbr_tasks" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ”
.

Definition OSMboxPendAbort_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (mbox_post_profile sg )) (PreH5 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH6 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH8 : (0 <= UINT_MAX)) (PreH9 : (0 >= 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (mbox_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH16 : (pevent_pre <> 0)) (PreH17 : (pevent_pre = pe)) (PreH18 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH19 : (opt_pre = option)) (PreH20 : (mbox_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH23 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH24 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH25 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_abort_save_result environment critical saved_local sg caller mask retval before eid observed )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (opt_pre = option) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_pend_abort_save_result environment critical saved_local sg caller mask retval before eid observed )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPendAbort_partial_solve_wit_4 := OSMboxPendAbort_partial_solve_wit_4_pure -> OSMboxPendAbort_partial_solve_wit_4_aux.

Definition OSMboxPendAbort_partial_solve_wit_5_pure := 
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (mbox_post_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (mbox_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH21 : (opt_pre = option)) (PreH22 : (mbox_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH25 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH26 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_group_context environment critical saved_local sg caller active mask retval before acquired eid observed initial )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (initial)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> 0)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((q_post_group (acquired) (initial)) <> 0) ”
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_group_context environment critical saved_local sg caller active mask retval before acquired eid observed initial )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (initial)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> 0)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((q_post_group (acquired) (initial)) <> 0) ”
).

Definition OSMboxPendAbort_partial_solve_wit_5_pure_split_goal_1 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_group_context environment critical saved_local sg caller active mask retval before acquired eid observed initial )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (initial)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> 0)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((q_post_group (acquired) (initial)) <> 0) ”
.

Definition OSMboxPendAbort_partial_solve_wit_5_aux := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (mbox_post_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (mbox_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH21 : (opt_pre = option)) (PreH22 : (mbox_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH25 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH26 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_abort_group_context environment critical saved_local sg caller active mask retval before acquired eid observed initial )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (initial)))
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((q_post_group (acquired) (initial)) <> 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (opt_pre = option) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_pend_abort_group_context environment critical saved_local sg caller active mask retval before acquired eid observed initial )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (initial)))
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPendAbort_partial_solve_wit_5 := OSMboxPendAbort_partial_solve_wit_5_pure -> OSMboxPendAbort_partial_solve_wit_5_aux.

Definition OSMboxPendAbort_partial_solve_wit_6_pure := 
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (processed: (@list Z)) (nbr_tasks: Z) (perr: Z) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (mbox_pend_abort_output_address error_addr perr )) (PreH5 : (option = 1)) (PreH6 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH7 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> nbr_tasks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed nbr_tasks )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (state) (node)) <> 0) ”
) \/
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (processed: (@list Z)) (nbr_tasks: Z) (perr: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (mbox_pend_abort_output_address error_addr perr )) (PreH7 : (option = 1)) (PreH8 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH9 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> nbr_tasks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed nbr_tasks )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
|--
  “ ((q_post_group (state) (node)) <> 0) ”
).

Definition OSMboxPendAbort_partial_solve_wit_6_pure_split_goal_1 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (processed: (@list Z)) (nbr_tasks: Z) (perr: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (mbox_pend_abort_output_address error_addr perr )) (PreH7 : (option = 1)) (PreH8 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH9 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> nbr_tasks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed nbr_tasks )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
|--
  “ ((q_post_group (state) (node)) <> 0) ”
.

Definition OSMboxPendAbort_partial_solve_wit_6_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (processed: (@list Z)) (nbr_tasks: Z) (perr: Z) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (mbox_pend_abort_output_address error_addr perr )) (PreH5 : (option = 1)) (PreH6 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH7 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed nbr_tasks )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (state) (node)) <> 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr ) ” 
  &&  “ (option = 1) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed nbr_tasks )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
.

Definition OSMboxPendAbort_partial_solve_wit_6 := OSMboxPendAbort_partial_solve_wit_6_pure -> OSMboxPendAbort_partial_solve_wit_6_aux.

Definition OSMboxPendAbort_partial_solve_wit_7_pure := 
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (nbr_tasks: Z) (perr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (0 <= nbr_tasks)) (PreH3 : (nbr_tasks < 255)) (PreH4 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (mbox_pend_abort_output_address error_addr perr )) (PreH8 : (option = 1)) (PreH9 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH10 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> nbr_tasks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed nbr_tasks tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 2 2 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((perr) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
) \/
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (nbr_tasks: Z) (perr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (tid: Z) (old: TaskAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (0 <= nbr_tasks)) (PreH4 : (nbr_tasks < 255)) (PreH5 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (mbox_pend_abort_output_address error_addr perr )) (PreH9 : (option = 1)) (PreH10 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH11 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> nbr_tasks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed nbr_tasks tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 2 2 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((perr) # UChar  |->_)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
).

Definition OSMboxPendAbort_partial_solve_wit_7_pure_split_goal_1 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (nbr_tasks: Z) (perr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (tid: Z) (old: TaskAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (0 <= nbr_tasks)) (PreH4 : (nbr_tasks < 255)) (PreH5 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (mbox_pend_abort_output_address error_addr perr )) (PreH9 : (option = 1)) (PreH10 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH11 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> nbr_tasks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed nbr_tasks tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 2 2 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((perr) # UChar  |->_)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
.

Definition OSMboxPendAbort_partial_solve_wit_7_pure_split_goal_2 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (nbr_tasks: Z) (perr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (tid: Z) (old: TaskAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (0 <= nbr_tasks)) (PreH4 : (nbr_tasks < 255)) (PreH5 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (mbox_pend_abort_output_address error_addr perr )) (PreH9 : (option = 1)) (PreH10 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH11 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> nbr_tasks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed nbr_tasks tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 2 2 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((perr) # UChar  |->_)
|--
  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ”
.

Definition OSMboxPendAbort_partial_solve_wit_7_pure_split_goal_3 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (nbr_tasks: Z) (perr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (tid: Z) (old: TaskAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (0 <= nbr_tasks)) (PreH4 : (nbr_tasks < 255)) (PreH5 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (mbox_pend_abort_output_address error_addr perr )) (PreH9 : (option = 1)) (PreH10 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH11 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> nbr_tasks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed nbr_tasks tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 2 2 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((perr) # UChar  |->_)
|--
  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
.

Definition OSMboxPendAbort_partial_solve_wit_7_pure_split_goal_4 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (nbr_tasks: Z) (perr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (tid: Z) (old: TaskAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (0 <= nbr_tasks)) (PreH4 : (nbr_tasks < 255)) (PreH5 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (mbox_pend_abort_output_address error_addr perr )) (PreH9 : (option = 1)) (PreH10 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH11 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> nbr_tasks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed nbr_tasks tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 2 2 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((perr) # UChar  |->_)
|--
  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
.

Definition OSMboxPendAbort_partial_solve_wit_7_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (nbr_tasks: Z) (perr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (0 <= nbr_tasks)) (PreH3 : (nbr_tasks < 255)) (PreH4 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (mbox_pend_abort_output_address error_addr perr )) (PreH8 : (option = 1)) (PreH9 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH10 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed nbr_tasks tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 2 2 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((perr) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (0 <= nbr_tasks) ” 
  &&  “ (nbr_tasks < 255) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr ) ” 
  &&  “ (option = 1) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 2 2 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed nbr_tasks tid old )
  **  ((perr) # UChar  |->_)
.

Definition OSMboxPendAbort_partial_solve_wit_7 := OSMboxPendAbort_partial_solve_wit_7_pure -> OSMboxPendAbort_partial_solve_wit_7_aux.

Definition OSMboxPendAbort_partial_solve_wit_8_pure := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (state: UCOS2_Verify_State) (initial: OSEventAbstractState) (node: OSEventAbstractState) (processed: (@list Z)) (tid: Z) (old: TaskAbstractState) (priority: Z) (perr: Z) (nbr_tasks: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (mbox_pend_abort_output_address error_addr perr )) (PreH4 : (option = 1)) (PreH5 : (0 <= nbr_tasks)) (PreH6 : (nbr_tasks < 255)) (PreH7 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH8 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> nbr_tasks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed nbr_tasks tid old )
  **  (event_task_rdy_post sg (TskState (state)) eid node tid old 0 2 2 (q_post_sched_group (state)) (q_post_sched_rows (state)) priority )
  **  ((perr) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= nbr_tasks) ” 
  &&  “ (nbr_tasks < 255) ”
.

Definition OSMboxPendAbort_partial_solve_wit_8_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (state: UCOS2_Verify_State) (initial: OSEventAbstractState) (node: OSEventAbstractState) (processed: (@list Z)) (tid: Z) (old: TaskAbstractState) (priority: Z) (perr: Z) (nbr_tasks: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (mbox_pend_abort_output_address error_addr perr )) (PreH4 : (option = 1)) (PreH5 : (0 <= nbr_tasks)) (PreH6 : (nbr_tasks < 255)) (PreH7 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH8 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed nbr_tasks tid old )
  **  (event_task_rdy_post sg (TskState (state)) eid node tid old 0 2 2 (q_post_sched_group (state)) (q_post_sched_rows (state)) priority )
  **  ((perr) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= nbr_tasks) ” 
  &&  “ (nbr_tasks < 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr ) ” 
  &&  “ (option = 1) ” 
  &&  “ (0 <= nbr_tasks) ” 
  &&  “ (nbr_tasks < 255) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed nbr_tasks tid old )
  **  (event_task_rdy_post sg (TskState (state)) eid node tid old 0 2 2 (q_post_sched_group (state)) (q_post_sched_rows (state)) priority )
  **  ((perr) # UChar  |->_)
.

Definition OSMboxPendAbort_partial_solve_wit_8 := OSMboxPendAbort_partial_solve_wit_8_pure -> OSMboxPendAbort_partial_solve_wit_8_aux.

Definition OSMboxPendAbort_partial_solve_wit_9_pure := 
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (processed: (@list Z)) (nbr_tasks: Z) (perr: Z) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (mbox_pend_abort_output_address error_addr perr )) (PreH5 : (option = 1)) (PreH6 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH7 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> nbr_tasks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed nbr_tasks )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (option = 1) ” 
  &&  “ ((q_post_group (state) (node)) = 0) ”
) \/
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (processed: (@list Z)) (nbr_tasks: Z) (perr: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (mbox_pend_abort_output_address error_addr perr )) (PreH7 : (option = 1)) (PreH8 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH9 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> nbr_tasks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed nbr_tasks )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
|--
  “ ((q_post_group (state) (node)) = 0) ”
).

Definition OSMboxPendAbort_partial_solve_wit_9_pure_split_goal_1 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (processed: (@list Z)) (nbr_tasks: Z) (perr: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (mbox_pend_abort_output_address error_addr perr )) (PreH7 : (option = 1)) (PreH8 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH9 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> nbr_tasks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed nbr_tasks )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
|--
  “ ((q_post_group (state) (node)) = 0) ”
.

Definition OSMboxPendAbort_partial_solve_wit_9_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (processed: (@list Z)) (nbr_tasks: Z) (perr: Z) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (mbox_pend_abort_output_address error_addr perr )) (PreH5 : (option = 1)) (PreH6 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH7 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed nbr_tasks )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (option = 1) ” 
  &&  “ ((q_post_group (state) (node)) = 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr ) ” 
  &&  “ (option = 1) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed nbr_tasks )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
.

Definition OSMboxPendAbort_partial_solve_wit_9 := OSMboxPendAbort_partial_solve_wit_9_pure -> OSMboxPendAbort_partial_solve_wit_9_aux.

Definition OSMboxPendAbort_partial_solve_wit_10_pure := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (priority: Z) (perr: Z) (nbr_tasks: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (mbox_pend_abort_output_address error_addr perr )) (PreH4 : (option <> 1)) (PreH5 : (nbr_tasks = 0)) (PreH6 : (0 <= option)) (PreH7 : (option <= 255)) (PreH8 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH9 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> nbr_tasks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial acquired initial (@nil Z) 0 tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid initial tid old 0 2 2 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
  **  ((perr) # UChar  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (option <> 1) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (0 = 0) ”
.

Definition OSMboxPendAbort_partial_solve_wit_10_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (priority: Z) (perr: Z) (nbr_tasks: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (mbox_pend_abort_output_address error_addr perr )) (PreH4 : (option <> 1)) (PreH5 : (nbr_tasks = 0)) (PreH6 : (0 <= option)) (PreH7 : (option <= 255)) (PreH8 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH9 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "nbr_tasks" ) )) # UChar  |-> nbr_tasks)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial acquired initial (@nil Z) 0 tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid initial tid old 0 2 2 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
  **  ((perr) # UChar  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (option <> 1) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (0 = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr ) ” 
  &&  “ (option <> 1) ” 
  &&  “ (nbr_tasks = 0) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "nbr_tasks" ) )) # UChar  |-> 0)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial acquired initial (@nil Z) 0 tid old )
  **  (event_task_rdy_post sg (TskState (acquired)) eid initial tid old 0 2 2 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) priority )
  **  ((perr) # UChar  |->_)
.

Definition OSMboxPendAbort_partial_solve_wit_10 := OSMboxPendAbort_partial_solve_wit_10_pure -> OSMboxPendAbort_partial_solve_wit_10_aux.

Definition OSMboxPendAbort_partial_solve_wit_11_pure := 
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (0 = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (1 <> opt_pre)) (PreH30 : (0 = opt_pre)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid initial_2 tid old 2 2 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (1 <> opt_pre)) (PreH30 : (0 = opt_pre)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid initial_2 tid old 2 2 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
).

Definition OSMboxPendAbort_partial_solve_wit_11_pure_split_goal_1 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (1 <> opt_pre)) (PreH30 : (0 = opt_pre)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid initial_2 tid old 2 2 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
.

Definition OSMboxPendAbort_partial_solve_wit_11_pure_split_goal_2 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (1 <> opt_pre)) (PreH30 : (0 = opt_pre)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid initial_2 tid old 2 2 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ”
.

Definition OSMboxPendAbort_partial_solve_wit_11_pure_split_goal_3 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (1 <> opt_pre)) (PreH30 : (0 = opt_pre)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid initial_2 tid old 2 2 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
.

Definition OSMboxPendAbort_partial_solve_wit_11_pure_split_goal_4 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (1 <> opt_pre)) (PreH30 : (0 = opt_pre)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid initial_2 tid old 2 2 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
.

Definition OSMboxPendAbort_partial_solve_wit_11_aux := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (0 = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (1 <> opt_pre)) (PreH30 : (0 = opt_pre)) ,
  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid initial_2 tid old 2 2 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (opt_pre = option) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (1 <> opt_pre) ” 
  &&  “ (0 = opt_pre) ”
  &&  (event_task_rdy_pre sg (TskState (acquired_2)) eid initial_2 tid old 2 2 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 tid old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPendAbort_partial_solve_wit_11 := OSMboxPendAbort_partial_solve_wit_11_pure -> OSMboxPendAbort_partial_solve_wit_11_aux.

Definition OSMboxPendAbort_partial_solve_wit_12_pure := 
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (0 = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (1 <> opt_pre)) (PreH30 : (0 <> opt_pre)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid initial_2 tid old 2 2 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (1 <> opt_pre)) (PreH30 : (0 <> opt_pre)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid initial_2 tid old 2 2 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
).

Definition OSMboxPendAbort_partial_solve_wit_12_pure_split_goal_1 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (1 <> opt_pre)) (PreH30 : (0 <> opt_pre)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid initial_2 tid old 2 2 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
.

Definition OSMboxPendAbort_partial_solve_wit_12_pure_split_goal_2 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (1 <> opt_pre)) (PreH30 : (0 <> opt_pre)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid initial_2 tid old 2 2 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ”
.

Definition OSMboxPendAbort_partial_solve_wit_12_pure_split_goal_3 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (1 <> opt_pre)) (PreH30 : (0 <> opt_pre)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid initial_2 tid old 2 2 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
.

Definition OSMboxPendAbort_partial_solve_wit_12_pure_split_goal_4 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (1 <> opt_pre)) (PreH30 : (0 <> opt_pre)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid initial_2 tid old 2 2 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
.

Definition OSMboxPendAbort_partial_solve_wit_12_aux := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (0 = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (1 <> opt_pre)) (PreH30 : (0 <> opt_pre)) ,
  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired_2)) eid initial_2 tid old 2 2 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (opt_pre = option) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (1 <> opt_pre) ” 
  &&  “ (0 <> opt_pre) ”
  &&  (event_task_rdy_pre sg (TskState (acquired_2)) eid initial_2 tid old 2 2 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) )
  **  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 tid old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPendAbort_partial_solve_wit_12 := OSMboxPendAbort_partial_solve_wit_12_pure -> OSMboxPendAbort_partial_solve_wit_12_aux.

Definition OSMboxPendAbort_partial_solve_wit_13_pure := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (0 = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (1 <> opt_pre)) (PreH30 : (0 <> opt_pre)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (0 = 0) ”
.

Definition OSMboxPendAbort_partial_solve_wit_13_aux := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (0 = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (1 <> opt_pre)) (PreH30 : (0 <> opt_pre)) ,
  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (opt_pre = option) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (1 <> opt_pre) ” 
  &&  “ (0 <> opt_pre) ”
  &&  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPendAbort_partial_solve_wit_13 := OSMboxPendAbort_partial_solve_wit_13_pure -> OSMboxPendAbort_partial_solve_wit_13_aux.

Definition OSMboxPendAbort_partial_solve_wit_14_pure := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (0 = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (1 <> opt_pre)) (PreH30 : (0 = opt_pre)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (0 = 0) ”
.

Definition OSMboxPendAbort_partial_solve_wit_14_aux := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (0 = 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH29 : (1 <> opt_pre)) (PreH30 : (0 = opt_pre)) ,
  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (opt_pre = option) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (1 <> opt_pre) ” 
  &&  “ (0 = opt_pre) ”
  &&  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask retval before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPendAbort_partial_solve_wit_14 := OSMboxPendAbort_partial_solve_wit_14_pure -> OSMboxPendAbort_partial_solve_wit_14_aux.

Definition OSMboxPendAbort_partial_solve_wit_15_pure := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (perr: Z) (nbr_tasks: Z) (cpu_sr: Z) (PreH1 : (mbox_pend_abort_output_address error_addr perr )) (PreH2 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH3 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> nbr_tasks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mbox_pend_abort_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid option before acquired released nbr_tasks 14 1 )
  **  ((perr) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSMboxPendAbort_partial_solve_wit_15_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (perr: Z) (nbr_tasks: Z) (cpu_sr: Z) (PreH1 : (mbox_pend_abort_output_address error_addr perr )) (PreH2 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH3 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_abort_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid option before acquired released nbr_tasks 14 1 )
  **  ((perr) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr ) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_pend_abort_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid option before acquired released nbr_tasks 14 1 )
  **  ((perr) # UChar  |->_)
.

Definition OSMboxPendAbort_partial_solve_wit_15 := OSMboxPendAbort_partial_solve_wit_15_pure -> OSMboxPendAbort_partial_solve_wit_15_aux.

Definition OSMboxPendAbort_partial_solve_wit_16_pure := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (perr: Z) (nbr_tasks: Z) (cpu_sr: Z) (PreH1 : (mbox_pend_abort_output_address error_addr perr )) (PreH2 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH3 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_abort_restore_post environment critical saved_local sg caller mask pe eid option before nbr_tasks 14 1 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "nbr_tasks" ) )) # UChar  |-> nbr_tasks)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((perr) # UChar  |->_)
|--
  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ”
.

Definition OSMboxPendAbort_partial_solve_wit_16_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (perr: Z) (nbr_tasks: Z) (PreH1 : (mbox_pend_abort_output_address error_addr perr )) (PreH2 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH3 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_abort_restore_post environment critical saved_local sg caller mask pe eid option before nbr_tasks 14 1 )
  **  ((perr) # UChar  |->_)
|--
  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr ) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_pend_abort_restore_post environment critical saved_local sg caller mask pe eid option before nbr_tasks 14 1 )
  **  ((perr) # UChar  |->_)
.

Definition OSMboxPendAbort_partial_solve_wit_16 := OSMboxPendAbort_partial_solve_wit_16_pure -> OSMboxPendAbort_partial_solve_wit_16_aux.

Definition OSMboxPendAbort_partial_solve_wit_17_pure := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (perr: Z) (nbr_tasks: Z) (cpu_sr: Z) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (mbox_pend_abort_prefix_result environment critical sg caller mask pe eid option before nbr_tasks 14 1 returned restored )) (PreH2 : (mbox_pend_abort_output_address error_addr perr )) (PreH3 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH4 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "nbr_tasks" ) )) # UChar  |-> nbr_tasks)
  **  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((perr) # UChar  |->_)
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSMboxPendAbort_partial_solve_wit_17_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (perr: Z) (nbr_tasks: Z) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (PreH1 : (mbox_pend_abort_prefix_result environment critical sg caller mask pe eid option before nbr_tasks 14 1 returned restored )) (PreH2 : (mbox_pend_abort_output_address error_addr perr )) (PreH3 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH4 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  ((perr) # UChar  |->_)
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (mbox_pend_abort_prefix_result environment critical sg caller mask pe eid option before nbr_tasks 14 1 returned restored ) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr ) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  ((perr) # UChar  |->_)
.

Definition OSMboxPendAbort_partial_solve_wit_17 := OSMboxPendAbort_partial_solve_wit_17_pure -> OSMboxPendAbort_partial_solve_wit_17_aux.

Definition OSMboxPendAbort_partial_solve_wit_18_pure := 
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) = 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (mbox_post_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (mbox_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH21 : (opt_pre = option)) (PreH22 : (mbox_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH25 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH26 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_group_context environment critical saved_local sg caller active mask retval before acquired eid observed initial )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (initial)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ ((q_post_group (acquired) (initial)) = 0) ”
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_group_context environment critical saved_local sg caller active mask retval before acquired eid observed initial )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (initial)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((q_post_group (acquired) (initial)) = 0) ”
).

Definition OSMboxPendAbort_partial_solve_wit_18_pure_split_goal_1 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (mbox_post_profile sg )) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH9 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (pe = (event_addr (sg) (eid)))) (PreH14 : (pe <> 0)) (PreH15 : (valid_event_id sg eid )) (PreH16 : (mbox_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH19 : (pevent_pre <> 0)) (PreH20 : (pevent_pre = pe)) (PreH21 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH22 : (opt_pre = option)) (PreH23 : (mbox_post_profile sg )) (PreH24 : (UCOS2_state_inv sg before )) (PreH25 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH26 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH27 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH28 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_group_context environment critical saved_local sg caller active mask retval before acquired eid observed initial )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (initial)))
  **  ((( &( "nbr_tasks" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((q_post_group (acquired) (initial)) = 0) ”
.

Definition OSMboxPendAbort_partial_solve_wit_18_aux := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) = 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (mbox_post_profile sg )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH8 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH10 : (0 <= UINT_MAX)) (PreH11 : (0 >= 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (mbox_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH18 : (pevent_pre <> 0)) (PreH19 : (pevent_pre = pe)) (PreH20 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH21 : (opt_pre = option)) (PreH22 : (mbox_post_profile sg )) (PreH23 : (UCOS2_state_inv sg before )) (PreH24 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH25 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH26 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH27 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (mbox_pend_abort_group_context environment critical saved_local sg caller active mask retval before acquired eid observed initial )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (initial)))
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ ((q_post_group (acquired) (initial)) = 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (opt_pre = option) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (mbox_pend_abort_group_context environment critical saved_local sg caller active mask retval before acquired eid observed initial )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (initial)))
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPendAbort_partial_solve_wit_18 := OSMboxPendAbort_partial_solve_wit_18_pure -> OSMboxPendAbort_partial_solve_wit_18_aux.

Definition OSMboxPendAbort_partial_solve_wit_19_pure := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (mbox_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH20 : (opt_pre = option)) (PreH21 : (mbox_post_profile sg )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH24 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH25 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  (mbox_pend_abort_restore_pre environment critical saved_local sg caller active mask retval pe eid option before acquired_2 acquired_2 0 0 0 )
  **  ((( &( "nbr_tasks" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (retval = retval) ”
.

Definition OSMboxPendAbort_partial_solve_wit_19_aux := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (mbox_post_profile sg )) (PreH6 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) (PreH7 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH8 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (mbox_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH17 : (pevent_pre <> 0)) (PreH18 : (pevent_pre = pe)) (PreH19 : (mbox_pend_abort_output_address error_addr perr_pre )) (PreH20 : (opt_pre = option)) (PreH21 : (mbox_post_profile sg )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH24 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) (PreH25 : (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X )) (PreH26 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (mbox_pend_abort_restore_pre environment critical saved_local sg caller active mask retval pe eid option before acquired_2 acquired_2 0 0 0 )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (retval = retval) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (acquired) (initial))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 1) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (mbox_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (opt_pre = option) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before ) ” 
  &&  “ (mbox_pend_abort_safe environment critical sg caller mask pe eid option before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (mbox_pend_abort_restore_pre environment critical saved_local sg caller active mask retval (event_addr (sg) (eid)) eid option before acquired_2 acquired_2 0 0 0 )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSMboxPendAbort_partial_solve_wit_19 := OSMboxPendAbort_partial_solve_wit_19_pure -> OSMboxPendAbort_partial_solve_wit_19_aux.

Definition OSMboxPendAbort_which_implies_wit_1 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (mbox_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (mbox_pend_abort_call_input critical sg caller pe before eid observed ) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_pend_abort_type_context environment saved_local sg caller mask before eid )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (mbox_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (valid_event_id sg eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_pend_abort_type_context environment saved_local sg caller mask before eid )
).

Definition OSMboxPendAbort_which_implies_wit_1_split_goal_1 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (mbox_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (valid_event_id sg eid ) ”
.

Definition OSMboxPendAbort_which_implies_wit_1_split_goal_2 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (mbox_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSMboxPendAbort_which_implies_wit_1_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (mbox_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_pend_abort_type_context environment saved_local sg caller mask before eid )
.

Definition OSMboxPendAbort_which_implies_wit_2 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (mbox_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_pend_abort_type_context environment saved_local sg caller mask before eid )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (mbox_post_profile sg ) ”
  &&  (mbox_pend_abort_save_pre environment critical saved_local sg caller mask before pe eid observed )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (mbox_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_pend_abort_type_context environment saved_local sg caller mask before eid )
|--
  (mbox_pend_abort_save_pre environment critical saved_local sg caller mask before pe eid observed )
).

Definition OSMboxPendAbort_which_implies_wit_2_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (mbox_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (mbox_pend_abort_call_input critical sg caller pe before eid observed )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 1)) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (mbox_pend_abort_type_context environment saved_local sg caller mask before eid )
|--
  (mbox_pend_abort_save_pre environment critical saved_local sg caller mask before pe eid observed )
.

Definition OSMboxPendAbort_which_implies_wit_3 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (valid_event_id sg eid )) (PreH3 : (mbox_post_profile sg )) ,
  (mbox_pend_abort_save_result environment critical saved_local sg caller mask cpu_sr before eid observed )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (mbox_pend_abort_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (initial)))
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (valid_event_id sg eid )) (PreH3 : (mbox_post_profile sg )) ,
  (mbox_pend_abort_save_result environment critical saved_local sg caller mask cpu_sr before eid observed )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (mbox_pend_abort_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (initial)))
).

Definition OSMboxPendAbort_which_implies_wit_4 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (initial_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (nbr_tasks: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (acquired_2) (initial_2)) <> 0)) (PreH3 : (nbr_tasks = 0)) ,
  (mbox_pend_abort_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (nbr_tasks = 0) ”
  &&  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial acquired initial (@nil Z) 0 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (initial)))
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (initial_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (nbr_tasks: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (acquired_2) (initial_2)) <> 0)) (PreH3 : (nbr_tasks = 0)) ,
  (mbox_pend_abort_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState) ,
  “ ((q_post_group (acquired_2) (initial_2)) = (q_post_group (acquired) (initial))) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (nbr_tasks = 0) ”
  &&  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial acquired initial (@nil Z) 0 )
).

Definition OSMboxPendAbort_which_implies_wit_5 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (processed_2: (@list Z)) (node_2: OSEventAbstractState) (initial_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (nbr_tasks: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (state_2) (node_2)) <> 0)) ,
  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 state_2 node_2 processed_2 nbr_tasks )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state_2) (node_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState)  (processed: (@list Z))  (tid: Z)  (old: TaskAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= nbr_tasks) ” 
  &&  “ (nbr_tasks < 255) ”
  &&  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed nbr_tasks tid old )
  **  (event_task_rdy_pre sg (TskState (state)) eid node tid old 2 2 (q_post_sched_group (state)) (q_post_sched_rows (state)) )
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (processed_2: (@list Z)) (node_2: OSEventAbstractState) (initial_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (nbr_tasks: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (state_2) (node_2)) <> 0)) ,
  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 state_2 node_2 processed_2 nbr_tasks )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state_2) (node_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState)  (processed: (@list Z))  (tid: Z)  (old: TaskAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= nbr_tasks) ” 
  &&  “ (nbr_tasks < 255) ”
  &&  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed nbr_tasks tid old )
  **  (event_task_rdy_pre sg (TskState (state)) eid node tid old 2 2 (q_post_sched_group (state)) (q_post_sched_rows (state)) )
).

Definition OSMboxPendAbort_which_implies_wit_6 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (priority: Z) (old: TaskAbstractState) (tid: Z) (processed: (@list Z)) (node: OSEventAbstractState) (initial_2: OSEventAbstractState) (state: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (nbr_tasks: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (0 <= nbr_tasks)) (PreH3 : (nbr_tasks < 255)) ,
  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 state node processed nbr_tasks tid old )
  **  (event_task_rdy_post sg (TskState (state)) eid node tid old 0 2 2 (q_post_sched_group (state)) (q_post_sched_rows (state)) priority )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (next: UCOS2_Verify_State)  (next_node: OSEventAbstractState)  (next_processed: (@list Z)) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= nbr_tasks) ” 
  &&  “ (nbr_tasks < 255) ”
  &&  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial next next_node next_processed (nbr_tasks + 1 ) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (next) (next_node)))
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (priority: Z) (old: TaskAbstractState) (tid: Z) (processed: (@list Z)) (node: OSEventAbstractState) (initial_2: OSEventAbstractState) (state: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (nbr_tasks: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (0 <= nbr_tasks)) (PreH3 : (nbr_tasks < 255)) ,
  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 state node processed nbr_tasks tid old )
  **  (event_task_rdy_post sg (TskState (state)) eid node tid old 0 2 2 (q_post_sched_group (state)) (q_post_sched_rows (state)) priority )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (next: UCOS2_Verify_State)  (next_node: OSEventAbstractState)  (next_processed: (@list Z)) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= nbr_tasks) ” 
  &&  “ (nbr_tasks < 255) ”
  &&  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial next next_node next_processed (nbr_tasks + 1 ) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (next) (next_node)))
).

Definition OSMboxPendAbort_which_implies_wit_7 := 
(
forall (option: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (processed: (@list Z)) (node: OSEventAbstractState) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (nbr_tasks: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (option = 1)) (PreH4 : ((q_post_group (state) (node)) = 0)) ,
  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial state node processed nbr_tasks )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (mbox_pend_abort_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid option before acquired released nbr_tasks 14 1 )
) \/
(
forall (option: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (processed: (@list Z)) (node: OSEventAbstractState) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (nbr_tasks: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (option = 1)) (PreH4 : ((q_post_group (state) (node)) = 0)) ,
  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial state node processed nbr_tasks )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  (mbox_pend_abort_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid option before acquired released nbr_tasks 14 1 )
).

Definition OSMboxPendAbort_which_implies_wit_8 := 
(
forall (option: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (priority: Z) (old: TaskAbstractState) (tid: Z) (initial: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (nbr_tasks: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (option <> 1)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (nbr_tasks = 0)) ,
  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial acquired_2 initial (@nil Z) 0 tid old )
  **  (event_task_rdy_post sg (TskState (acquired_2)) eid initial tid old 0 2 2 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) priority )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  “ (nbr_tasks = 0) ”
  &&  (mbox_pend_abort_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid option before acquired released 1 14 1 )
) \/
(
forall (option: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (priority: Z) (old: TaskAbstractState) (tid: Z) (initial: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (nbr_tasks: Z) (cpu_sr: Z) (PreH1 : (pe <> 0)) (PreH2 : (option <> 1)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (nbr_tasks = 0)) ,
  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial acquired_2 initial (@nil Z) 0 tid old )
  **  (event_task_rdy_post sg (TskState (acquired_2)) eid initial tid old 0 2 2 (q_post_sched_group (acquired_2)) (q_post_sched_rows (acquired_2)) priority )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State) ,
  “ (nbr_tasks = 0) ”
  &&  (mbox_pend_abort_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid option before acquired released 1 14 1 )
).

Definition OSMboxPendAbort_which_implies_wit_9 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (initial_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (nbr_tasks: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (nbr_tasks = 0)) ,
  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (nbr_tasks = 0) ”
  &&  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial acquired initial (@nil Z) 0 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired)) eid initial tid old 2 2 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) )
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (initial_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (nbr_tasks: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (nbr_tasks = 0)) ,
  (mbox_pend_abort_loop_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) 0 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (tid: Z)  (old: TaskAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (nbr_tasks = 0) ”
  &&  (mbox_pend_abort_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial acquired initial (@nil Z) 0 tid old )
  **  (event_task_rdy_pre sg (TskState (acquired)) eid initial tid old 2 2 (q_post_sched_group (acquired)) (q_post_sched_rows (acquired)) )
).

Definition OSMboxPendAbort_which_implies_wit_10 := 
(
forall (option: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (nbr_tasks: Z) (PreH1 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) ,
  (mbox_pend_abort_restore_post environment critical saved_local sg caller mask pe eid option before nbr_tasks 14 1 )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (mbox_pend_abort_prefix_result environment critical sg caller mask pe eid option before nbr_tasks 14 1 returned restored ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
) \/
(
forall (option: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (nbr_tasks: Z) (PreH1 : (mbox_pend_abort_schedule_protocol environment critical sg caller mask pe eid option before )) ,
  (mbox_pend_abort_restore_post environment critical saved_local sg caller mask pe eid option before nbr_tasks 14 1 )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State) ,
  “ (mbox_pend_abort_prefix_result environment critical sg caller mask pe eid option before nbr_tasks 14 1 returned restored ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
).

Definition OSMboxPendAbort_which_implies_wit_11 := 
(
forall (option: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (initial: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : ((q_post_group (acquired_2) (initial)) = 0)) ,
  (mbox_pend_abort_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State) ,
  (mbox_pend_abort_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid option before acquired acquired 0 0 0 )
) \/
(
forall (option: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (initial: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : ((q_post_group (acquired_2) (initial)) = 0)) ,
  (mbox_pend_abort_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State) ,
  (mbox_pend_abort_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid option before acquired acquired 0 0 0 )
).

Module Type VC_Correct.


Axiom proof_of_OSMboxPendAbort_safety_wit_1 : OSMboxPendAbort_safety_wit_1.
Axiom proof_of_OSMboxPendAbort_safety_wit_2 : OSMboxPendAbort_safety_wit_2.
Axiom proof_of_OSMboxPendAbort_safety_wit_3 : OSMboxPendAbort_safety_wit_3.
Axiom proof_of_OSMboxPendAbort_safety_wit_4 : OSMboxPendAbort_safety_wit_4.
Axiom proof_of_OSMboxPendAbort_safety_wit_5 : OSMboxPendAbort_safety_wit_5.
Axiom proof_of_OSMboxPendAbort_safety_wit_6 : OSMboxPendAbort_safety_wit_6.
Axiom proof_of_OSMboxPendAbort_safety_wit_7 : OSMboxPendAbort_safety_wit_7.
Axiom proof_of_OSMboxPendAbort_entail_wit_1 : OSMboxPendAbort_entail_wit_1.
Axiom proof_of_OSMboxPendAbort_entail_wit_2 : OSMboxPendAbort_entail_wit_2.
Axiom proof_of_OSMboxPendAbort_entail_wit_3 : OSMboxPendAbort_entail_wit_3.
Axiom proof_of_OSMboxPendAbort_entail_wit_4 : OSMboxPendAbort_entail_wit_4.
Axiom proof_of_OSMboxPendAbort_entail_wit_5_1 : OSMboxPendAbort_entail_wit_5_1.
Axiom proof_of_OSMboxPendAbort_entail_wit_5_2 : OSMboxPendAbort_entail_wit_5_2.
Axiom proof_of_OSMboxPendAbort_entail_wit_6_1 : OSMboxPendAbort_entail_wit_6_1.
Axiom proof_of_OSMboxPendAbort_entail_wit_6_2 : OSMboxPendAbort_entail_wit_6_2.
Axiom proof_of_OSMboxPendAbort_return_wit_1 : OSMboxPendAbort_return_wit_1.
Axiom proof_of_OSMboxPendAbort_return_wit_2 : OSMboxPendAbort_return_wit_2.
Axiom proof_of_OSMboxPendAbort_return_wit_3 : OSMboxPendAbort_return_wit_3.
Axiom proof_of_OSMboxPendAbort_return_wit_4 : OSMboxPendAbort_return_wit_4.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_1_pure : OSMboxPendAbort_partial_solve_wit_1_pure.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_1 : OSMboxPendAbort_partial_solve_wit_1.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_2_pure : OSMboxPendAbort_partial_solve_wit_2_pure.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_2 : OSMboxPendAbort_partial_solve_wit_2.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_3 : OSMboxPendAbort_partial_solve_wit_3.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_4_pure : OSMboxPendAbort_partial_solve_wit_4_pure.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_4 : OSMboxPendAbort_partial_solve_wit_4.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_5_pure : OSMboxPendAbort_partial_solve_wit_5_pure.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_5 : OSMboxPendAbort_partial_solve_wit_5.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_6_pure : OSMboxPendAbort_partial_solve_wit_6_pure.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_6 : OSMboxPendAbort_partial_solve_wit_6.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_7_pure : OSMboxPendAbort_partial_solve_wit_7_pure.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_7 : OSMboxPendAbort_partial_solve_wit_7.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_8_pure : OSMboxPendAbort_partial_solve_wit_8_pure.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_8 : OSMboxPendAbort_partial_solve_wit_8.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_9_pure : OSMboxPendAbort_partial_solve_wit_9_pure.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_9 : OSMboxPendAbort_partial_solve_wit_9.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_10_pure : OSMboxPendAbort_partial_solve_wit_10_pure.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_10 : OSMboxPendAbort_partial_solve_wit_10.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_11_pure : OSMboxPendAbort_partial_solve_wit_11_pure.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_11 : OSMboxPendAbort_partial_solve_wit_11.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_12_pure : OSMboxPendAbort_partial_solve_wit_12_pure.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_12 : OSMboxPendAbort_partial_solve_wit_12.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_13_pure : OSMboxPendAbort_partial_solve_wit_13_pure.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_13 : OSMboxPendAbort_partial_solve_wit_13.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_14_pure : OSMboxPendAbort_partial_solve_wit_14_pure.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_14 : OSMboxPendAbort_partial_solve_wit_14.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_15_pure : OSMboxPendAbort_partial_solve_wit_15_pure.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_15 : OSMboxPendAbort_partial_solve_wit_15.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_16_pure : OSMboxPendAbort_partial_solve_wit_16_pure.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_16 : OSMboxPendAbort_partial_solve_wit_16.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_17_pure : OSMboxPendAbort_partial_solve_wit_17_pure.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_17 : OSMboxPendAbort_partial_solve_wit_17.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_18_pure : OSMboxPendAbort_partial_solve_wit_18_pure.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_18 : OSMboxPendAbort_partial_solve_wit_18.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_19_pure : OSMboxPendAbort_partial_solve_wit_19_pure.
Axiom proof_of_OSMboxPendAbort_partial_solve_wit_19 : OSMboxPendAbort_partial_solve_wit_19.
Axiom proof_of_OSMboxPendAbort_which_implies_wit_1 : OSMboxPendAbort_which_implies_wit_1.
Axiom proof_of_OSMboxPendAbort_which_implies_wit_2 : OSMboxPendAbort_which_implies_wit_2.
Axiom proof_of_OSMboxPendAbort_which_implies_wit_3 : OSMboxPendAbort_which_implies_wit_3.
Axiom proof_of_OSMboxPendAbort_which_implies_wit_4 : OSMboxPendAbort_which_implies_wit_4.
Axiom proof_of_OSMboxPendAbort_which_implies_wit_5 : OSMboxPendAbort_which_implies_wit_5.
Axiom proof_of_OSMboxPendAbort_which_implies_wit_6 : OSMboxPendAbort_which_implies_wit_6.
Axiom proof_of_OSMboxPendAbort_which_implies_wit_7 : OSMboxPendAbort_which_implies_wit_7.
Axiom proof_of_OSMboxPendAbort_which_implies_wit_8 : OSMboxPendAbort_which_implies_wit_8.
Axiom proof_of_OSMboxPendAbort_which_implies_wit_9 : OSMboxPendAbort_which_implies_wit_9.
Axiom proof_of_OSMboxPendAbort_which_implies_wit_10 : OSMboxPendAbort_which_implies_wit_10.
Axiom proof_of_OSMboxPendAbort_which_implies_wit_11 : OSMboxPendAbort_which_implies_wit_11.

End VC_Correct.
