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
Require Import Ucos2Verify.VC.code.queue.spec.q_del_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.
Local Open Scope sac.

(*----- Function OSQDel -----*)

Definition OSQDel_safety_wit_1 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = pe)) (PreH2 : (q_pend_abort_output_address error_addr perr_pre )) (PreH3 : (opt_pre = choice)) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH8 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH11 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQDel_safety_wit_2 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : ((q_del_int_nesting (before)) <= 0)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : ((q_del_int_nesting (before)) <= 0)) (PreH8 : (0 <= (q_del_int_nesting (before)))) (PreH9 : ((q_del_int_nesting (before)) <= 255)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (q_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_post_call_input critical sg caller pe before eid observed )) (PreH16 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH19 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (pe <> 0)) (PreH25 : (valid_event_id sg eid )) (PreH26 : (q_post_profile sg )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (q_post_call_input critical sg caller pe before eid observed )) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (q_pend_abort_output_address error_addr perr_pre )) (PreH32 : (opt_pre = choice)) (PreH33 : (q_post_profile sg )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : (q_post_call_input critical sg caller pe before eid observed )) (PreH36 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH37 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH38 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH39 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH40 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_post_save_result environment critical saved_local sg caller mask retval before eid observed )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQDel_safety_wit_3 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (q: QueueFields) (q_2: QueueFields) (buffer: QDelBuffer) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH3 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH4 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (choice = 0)) (PreH8 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe <> 0)) (PreH11 : (q_pend_abort_output_address error_addr perr )) (PreH12 : ((q_del_int_nesting (before)) <= 0)) (PreH13 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH14 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH15 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH18 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH19 : (0 = choice)) ,
  (q_del_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid 0 before 0 0 0 buffer )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_buffer_rep buffer )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQDel_safety_wit_4 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (q: QueueFields) (q_2: QueueFields) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH3 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH4 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (choice = 0)) (PreH8 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe <> 0)) (PreH11 : (q_pend_abort_output_address error_addr perr )) (PreH12 : ((q_del_int_nesting (before)) <= 0)) (PreH13 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH14 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH15 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH18 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH19 : (0 = choice)) ,
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before 0 0 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |-> 0)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQDel_safety_wit_5 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (q_pend_abort_output_address error_addr perr )) (PreH5 : ((q_del_int_nesting (before)) <= 0)) (PreH6 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH7 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH8 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH11 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH12 : (0 = choice)) ,
  (q_del_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid 0 before (event_addr (sg) (eid)) 73 0 QDelNoBuffer )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_buffer_rep QDelNoBuffer )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQDel_safety_wit_6 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (q_pend_abort_output_address error_addr perr )) (PreH6 : (choice = 1)) (PreH7 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH8 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH11 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed tasks_waiting tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 4 2 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQDel_safety_wit_7 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (q: QueueFields) (q_2: QueueFields) (buffer: QDelBuffer) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH3 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH4 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (choice = 1)) (PreH8 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe <> 0)) (PreH11 : (q_pend_abort_output_address error_addr perr )) (PreH12 : (choice = 1)) (PreH13 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH14 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH15 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH17 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid 1 before 0 0 tasks_waiting buffer )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_buffer_rep buffer )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQDel_safety_wit_8 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (perr: Z) (tasks_waiting: Z) (pq_addr_v: Z) (PreH1 : (q_pend_abort_output_address error_addr perr )) (PreH2 : (q_del_safe environment critical sg caller mask pe eid choice before X )) ,
  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before 0 0 )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((perr) # UChar  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |-> pq_addr_v)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQDel_safety_wit_9 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (q_pend_abort_output_address error_addr perr )) (PreH4 : ((q_del_int_nesting (before)) <= 0)) (PreH5 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH6 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH7 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH10 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH11 : (0 <> choice)) (PreH12 : (1 <> choice)) ,
  (q_del_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid choice before (event_addr (sg) (eid)) 7 0 QDelNoBuffer )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_buffer_rep QDelNoBuffer )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSQDel_entail_wit_1 := 
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : (pevent_pre <> 0)) (PreH8 : (pevent_pre = pe)) (PreH9 : (q_pend_abort_output_address error_addr perr_pre )) (PreH10 : (opt_pre = choice)) (PreH11 : (q_post_profile sg )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (q_post_call_input critical sg caller pe before eid observed )) (PreH14 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH15 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH18 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
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
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (q_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (opt_pre = choice) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (q_post_call_input critical sg caller pe before eid observed )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (q_pend_abort_output_address error_addr perr_pre )) (PreH12 : (opt_pre = choice)) (PreH13 : (q_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_post_call_input critical sg caller pe before eid observed )) (PreH16 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH17 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH20 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  TT && emp 
|--
  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ”
  &&  emp
).

Definition OSQDel_entail_wit_1_split_goal_1 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (q_post_call_input critical sg caller pe before eid observed )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (q_pend_abort_output_address error_addr perr_pre )) (PreH12 : (opt_pre = choice)) (PreH13 : (q_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_post_call_input critical sg caller pe before eid observed )) (PreH16 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH17 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH20 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((event_slot_type_value ((EventState (before))) (eid)) <= 255)
.

Definition OSQDel_entail_wit_1_split_goal_2 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : (UCOS2_state_inv sg before )) (PreH8 : (q_post_call_input critical sg caller pe before eid observed )) (PreH9 : (pevent_pre <> 0)) (PreH10 : (pevent_pre = pe)) (PreH11 : (q_pend_abort_output_address error_addr perr_pre )) (PreH12 : (opt_pre = choice)) (PreH13 : (q_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_post_call_input critical sg caller pe before eid observed )) (PreH16 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH17 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH20 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (0 <= (event_slot_type_value ((EventState (before))) (eid)))
.

Definition OSQDel_entail_wit_2 := 
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (q_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (q_post_call_input critical sg caller pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (q_pend_abort_output_address error_addr perr_pre )) (PreH23 : (opt_pre = choice)) (PreH24 : (q_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (q_post_call_input critical sg caller pe before eid observed )) (PreH27 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH28 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH31 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_del_int_nesting (before)))
  **  (q_del_interrupt_context environment saved_local sg caller mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= (q_del_int_nesting (before))) ” 
  &&  “ ((q_del_int_nesting (before)) <= 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (q_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (opt_pre = choice) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_del_int_nesting (before)))
  **  (q_del_interrupt_context environment saved_local sg caller mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (q_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (q_post_call_input critical sg caller pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (q_pend_abort_output_address error_addr perr_pre )) (PreH23 : (opt_pre = choice)) (PreH24 : (q_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (q_post_call_input critical sg caller pe before eid observed )) (PreH27 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH28 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH31 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  TT && emp 
|--
  “ ((q_del_int_nesting (before)) <= 255) ” 
  &&  “ (0 <= (q_del_int_nesting (before))) ”
  &&  emp
).

Definition OSQDel_entail_wit_2_split_goal_1 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (q_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (q_post_call_input critical sg caller pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (q_pend_abort_output_address error_addr perr_pre )) (PreH23 : (opt_pre = choice)) (PreH24 : (q_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (q_post_call_input critical sg caller pe before eid observed )) (PreH27 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH28 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH31 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((q_del_int_nesting (before)) <= 255)
.

Definition OSQDel_entail_wit_2_split_goal_2 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH10 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH11 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH12 : (0 <= UINT_MAX)) (PreH13 : (0 >= 0)) (PreH14 : (pe = (event_addr (sg) (eid)))) (PreH15 : (pe <> 0)) (PreH16 : (valid_event_id sg eid )) (PreH17 : (q_post_profile sg )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (q_post_call_input critical sg caller pe before eid observed )) (PreH20 : (pevent_pre <> 0)) (PreH21 : (pevent_pre = pe)) (PreH22 : (q_pend_abort_output_address error_addr perr_pre )) (PreH23 : (opt_pre = choice)) (PreH24 : (q_post_profile sg )) (PreH25 : (UCOS2_state_inv sg before )) (PreH26 : (q_post_call_input critical sg caller pe before eid observed )) (PreH27 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH28 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH29 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH30 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH31 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (0 <= (q_del_int_nesting (before)))
.

Definition OSQDel_entail_wit_3_1 := 
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active_2: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired_2) (initial_2))) (32)) <> 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : ((q_del_int_nesting (before)) <= 0)) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : ((q_del_int_nesting (before)) <= 0)) (PreH10 : (0 <= (q_del_int_nesting (before)))) (PreH11 : ((q_del_int_nesting (before)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH21 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH22 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (pe = (event_addr (sg) (eid)))) (PreH26 : (pe <> 0)) (PreH27 : (valid_event_id sg eid )) (PreH28 : (q_post_profile sg )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (q_post_call_input critical sg caller pe before eid observed )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (q_pend_abort_output_address error_addr perr_pre )) (PreH34 : (opt_pre = choice)) (PreH35 : (q_post_profile sg )) (PreH36 : (UCOS2_state_inv sg before )) (PreH37 : (q_post_call_input critical sg caller pe before eid observed )) (PreH38 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH39 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH40 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH41 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH42 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_post_group_context environment critical saved_local sg caller active_2 mask retval before acquired_2 eid observed initial_2 )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (1 = (q_del_waiting (acquired) (initial))) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed initial )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (initial)))
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired_2) (initial_2))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (q_post_profile sg )) (PreH6 : ((q_del_int_nesting (before)) <= 0)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : ((q_del_int_nesting (before)) <= 0)) (PreH9 : (0 <= (q_del_int_nesting (before)))) (PreH10 : ((q_del_int_nesting (before)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (q_post_call_input critical sg caller pe before eid observed )) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (pe <> 0)) (PreH26 : (valid_event_id sg eid )) (PreH27 : (q_post_profile sg )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (q_post_call_input critical sg caller pe before eid observed )) (PreH30 : (pevent_pre <> 0)) (PreH31 : (pevent_pre = pe)) (PreH32 : (q_pend_abort_output_address error_addr perr_pre )) (PreH33 : (opt_pre = choice)) (PreH34 : (q_post_profile sg )) (PreH35 : (UCOS2_state_inv sg before )) (PreH36 : (q_post_call_input critical sg caller pe before eid observed )) (PreH37 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH38 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH39 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH40 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH41 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  TT && emp 
|--
  “ (1 = (q_del_waiting (acquired_2) (initial_2))) ”
  &&  emp
).

Definition OSQDel_entail_wit_3_1_split_goal_1 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired_2) (initial_2))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (q_post_profile sg )) (PreH6 : ((q_del_int_nesting (before)) <= 0)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : ((q_del_int_nesting (before)) <= 0)) (PreH9 : (0 <= (q_del_int_nesting (before)))) (PreH10 : ((q_del_int_nesting (before)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (q_post_call_input critical sg caller pe before eid observed )) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (pe <> 0)) (PreH26 : (valid_event_id sg eid )) (PreH27 : (q_post_profile sg )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (q_post_call_input critical sg caller pe before eid observed )) (PreH30 : (pevent_pre <> 0)) (PreH31 : (pevent_pre = pe)) (PreH32 : (q_pend_abort_output_address error_addr perr_pre )) (PreH33 : (opt_pre = choice)) (PreH34 : (q_post_profile sg )) (PreH35 : (UCOS2_state_inv sg before )) (PreH36 : (q_post_call_input critical sg caller pe before eid observed )) (PreH37 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH38 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH39 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH40 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH41 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (1 = (q_del_waiting (acquired_2) (initial_2)))
.

Definition OSQDel_entail_wit_3_2 := 
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (active_2: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired_2) (initial_2))) (32)) = 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (valid_event_id sg eid )) (PreH6 : (q_post_profile sg )) (PreH7 : ((q_del_int_nesting (before)) <= 0)) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : ((q_del_int_nesting (before)) <= 0)) (PreH10 : (0 <= (q_del_int_nesting (before)))) (PreH11 : ((q_del_int_nesting (before)) <= 255)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (valid_event_id sg eid )) (PreH15 : (q_post_profile sg )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (q_post_call_input critical sg caller pe before eid observed )) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH19 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH21 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH22 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH23 : (0 <= UINT_MAX)) (PreH24 : (0 >= 0)) (PreH25 : (pe = (event_addr (sg) (eid)))) (PreH26 : (pe <> 0)) (PreH27 : (valid_event_id sg eid )) (PreH28 : (q_post_profile sg )) (PreH29 : (UCOS2_state_inv sg before )) (PreH30 : (q_post_call_input critical sg caller pe before eid observed )) (PreH31 : (pevent_pre <> 0)) (PreH32 : (pevent_pre = pe)) (PreH33 : (q_pend_abort_output_address error_addr perr_pre )) (PreH34 : (opt_pre = choice)) (PreH35 : (q_post_profile sg )) (PreH36 : (UCOS2_state_inv sg before )) (PreH37 : (q_post_call_input critical sg caller pe before eid observed )) (PreH38 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH39 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH40 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH41 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH42 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_post_group_context environment critical saved_local sg caller active_2 mask retval before acquired_2 eid observed initial_2 )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (0 = (q_del_waiting (acquired) (initial))) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  (q_post_group_context environment critical saved_local sg caller active mask retval before acquired eid observed initial )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (initial)))
  **  ((perr_pre) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired_2) (initial_2))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (q_post_profile sg )) (PreH6 : ((q_del_int_nesting (before)) <= 0)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : ((q_del_int_nesting (before)) <= 0)) (PreH9 : (0 <= (q_del_int_nesting (before)))) (PreH10 : ((q_del_int_nesting (before)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (q_post_call_input critical sg caller pe before eid observed )) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (pe <> 0)) (PreH26 : (valid_event_id sg eid )) (PreH27 : (q_post_profile sg )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (q_post_call_input critical sg caller pe before eid observed )) (PreH30 : (pevent_pre <> 0)) (PreH31 : (pevent_pre = pe)) (PreH32 : (q_pend_abort_output_address error_addr perr_pre )) (PreH33 : (opt_pre = choice)) (PreH34 : (q_post_profile sg )) (PreH35 : (UCOS2_state_inv sg before )) (PreH36 : (q_post_call_input critical sg caller pe before eid observed )) (PreH37 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH38 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH39 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH40 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH41 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  TT && emp 
|--
  “ (0 = (q_del_waiting (acquired_2) (initial_2))) ”
  &&  emp
).

Definition OSQDel_entail_wit_3_2_split_goal_1 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_post_group (acquired_2) (initial_2))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (valid_event_id sg eid )) (PreH5 : (q_post_profile sg )) (PreH6 : ((q_del_int_nesting (before)) <= 0)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : ((q_del_int_nesting (before)) <= 0)) (PreH9 : (0 <= (q_del_int_nesting (before)))) (PreH10 : ((q_del_int_nesting (before)) <= 255)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (valid_event_id sg eid )) (PreH14 : (q_post_profile sg )) (PreH15 : (UCOS2_state_inv sg before )) (PreH16 : (q_post_call_input critical sg caller pe before eid observed )) (PreH17 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH20 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH21 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH22 : (0 <= UINT_MAX)) (PreH23 : (0 >= 0)) (PreH24 : (pe = (event_addr (sg) (eid)))) (PreH25 : (pe <> 0)) (PreH26 : (valid_event_id sg eid )) (PreH27 : (q_post_profile sg )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (q_post_call_input critical sg caller pe before eid observed )) (PreH30 : (pevent_pre <> 0)) (PreH31 : (pevent_pre = pe)) (PreH32 : (q_pend_abort_output_address error_addr perr_pre )) (PreH33 : (opt_pre = choice)) (PreH34 : (q_post_profile sg )) (PreH35 : (UCOS2_state_inv sg before )) (PreH36 : (q_post_call_input critical sg caller pe before eid observed )) (PreH37 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH38 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH39 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH40 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH41 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (0 = (q_del_waiting (acquired_2) (initial_2)))
.

Definition OSQDel_entail_wit_4 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active_2: TaskResumeCaller) (acquired_3: UCOS2_Verify_State) (initial_3: OSEventAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (q_pend_abort_output_address error_addr perr )) (PreH5 : ((q_del_int_nesting (before)) <= 0)) (PreH6 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH7 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH8 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH11 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH12 : (0 <> choice)) (PreH13 : (1 = choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_del_loop_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_3 eid observed initial_3 acquired_3 initial_3 (@nil Z) (q_del_waiting (acquired) (initial)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_3) (initial_3)))
  **  ((perr) # UChar  |->_)
|--
  EX (active: TaskResumeCaller)  (acquired_2: UCOS2_Verify_State)  (initial_2: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState)  (processed: (@list Z)) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ (choice = 1) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 state node processed (q_del_waiting (acquired) (initial)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_entail_wit_5 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (active_2: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (state_3: UCOS2_Verify_State) (node_3: OSEventAbstractState) (processed_2: (@list Z)) (tid_2: Z) (old_2: TaskAbstractState) (retval: Z) (PreH1 : ((unsigned_last_nbits ((q_post_group (state_2) (node_2))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (q_pend_abort_output_address error_addr perr )) (PreH5 : (choice = 1)) (PreH6 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH7 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH10 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (event_task_rdy_post sg (TskState (state_3)) eid node_3 tid_2 old_2 0 4 2 (q_post_sched_group (state_3)) (q_post_sched_rows (state_3)) retval )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_del_loop_wake_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 state_3 node_3 processed_2 tasks_waiting tid_2 old_2 )
  **  ((perr) # UChar  |->_)
|--
  EX (priority: Z)  (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState)  (processed: (@list Z))  (tid: Z)  (old: TaskAbstractState) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ (choice = 1) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_del_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed tasks_waiting tid old )
  **  (event_task_rdy_post sg (TskState (state)) eid node tid old 0 4 2 (q_post_sched_group (state)) (q_post_sched_rows (state)) priority )
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_entail_wit_6 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active_2: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (next: UCOS2_Verify_State) (next_node: OSEventAbstractState) (next_processed: (@list Z)) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (q_pend_abort_output_address error_addr perr )) (PreH5 : (choice = 1)) (PreH6 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH7 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH10 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_del_loop_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 next next_node next_processed tasks_waiting )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (next) (next_node)))
  **  ((perr) # UChar  |->_)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState)  (processed: (@list Z)) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ (choice = 1) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed tasks_waiting )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_entail_wit_7_1 := 
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (q: QueueFields) (q_2: QueueFields) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (buffer: QDelBuffer) (PreH1 : (q_del_prefix_result environment critical sg caller mask pe eid choice before 0 0 1 returned restored buffer )) (PreH2 : ((unsigned_last_nbits (tasks_waiting) (32)) = 1)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH5 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH6 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (choice = 1)) (PreH10 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (q_pend_abort_output_address error_addr perr )) (PreH14 : (choice = 1)) (PreH15 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH16 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH19 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before 0 0 )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((perr) # UChar  |->_)
|--
  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ”
  &&  (q_del_after_schedule_context environment critical saved_local sg caller mask pe eid choice before tasks_waiting )
  **  ((perr) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
) \/
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (q: QueueFields) (q_2: QueueFields) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (buffer: QDelBuffer) (PreH1 : (q_del_prefix_result environment critical sg caller mask pe eid choice before 0 0 1 returned restored buffer )) (PreH2 : ((unsigned_last_nbits (tasks_waiting) (32)) = 1)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH5 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH6 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (choice = 1)) (PreH10 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (q_pend_abort_output_address error_addr perr )) (PreH14 : (choice = 1)) (PreH15 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH16 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH19 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before 0 0 )
|--
  (q_del_after_schedule_context environment critical saved_local sg caller mask pe eid choice before tasks_waiting )
).

Definition OSQDel_entail_wit_7_1_split_goal_spatial := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (q: QueueFields) (q_2: QueueFields) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (buffer: QDelBuffer) (PreH1 : (q_del_prefix_result environment critical sg caller mask pe eid choice before 0 0 1 returned restored buffer )) (PreH2 : ((unsigned_last_nbits (tasks_waiting) (32)) = 1)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH5 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH6 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (choice = 1)) (PreH10 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (q_pend_abort_output_address error_addr perr )) (PreH14 : (choice = 1)) (PreH15 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH16 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH19 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before 0 0 )
|--
  (q_del_after_schedule_context environment critical saved_local sg caller mask pe eid choice before tasks_waiting )
.

Definition OSQDel_entail_wit_7_2 := 
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (q: QueueFields) (q_2: QueueFields) (buffer: QDelBuffer) (PreH1 : ((unsigned_last_nbits (tasks_waiting) (32)) <> 1)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH4 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH5 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (choice = 1)) (PreH9 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (q_pend_abort_output_address error_addr perr )) (PreH13 : (choice = 1)) (PreH14 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH15 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH18 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid 1 before 0 0 tasks_waiting buffer )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_buffer_rep buffer )
  **  ((perr) # UChar  |->_)
|--
  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ”
  &&  (q_del_after_schedule_context environment critical saved_local sg caller mask pe eid choice before tasks_waiting )
  **  ((perr) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
) \/
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (q: QueueFields) (q_2: QueueFields) (buffer: QDelBuffer) (PreH1 : ((unsigned_last_nbits (tasks_waiting) (32)) <> 1)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH4 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH5 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (choice = 1)) (PreH9 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (q_pend_abort_output_address error_addr perr )) (PreH13 : (choice = 1)) (PreH14 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH15 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH18 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid 1 before 0 0 tasks_waiting buffer )
  **  (q_del_buffer_rep buffer )
|--
  (q_del_after_schedule_context environment critical saved_local sg caller mask pe eid choice before tasks_waiting )
).

Definition OSQDel_entail_wit_7_2_split_goal_spatial := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (q: QueueFields) (q_2: QueueFields) (buffer: QDelBuffer) (PreH1 : ((unsigned_last_nbits (tasks_waiting) (32)) <> 1)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH4 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH5 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (choice = 1)) (PreH9 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (q_pend_abort_output_address error_addr perr )) (PreH13 : (choice = 1)) (PreH14 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH15 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH18 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid 1 before 0 0 tasks_waiting buffer )
  **  (q_del_buffer_rep buffer )
|--
  (q_del_after_schedule_context environment critical saved_local sg caller mask pe eid choice before tasks_waiting )
.

Definition OSQDel_entail_wit_8_1 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (q: QueueFields) (q_2: QueueFields) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH3 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH4 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (choice = 0)) (PreH8 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe <> 0)) (PreH11 : (q_pend_abort_output_address error_addr perr )) (PreH12 : ((q_del_int_nesting (before)) <= 0)) (PreH13 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH14 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH15 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH18 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH19 : (0 = choice)) ,
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before 0 0 )
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((perr) # UChar  |-> 0)
|--
  EX (error: Z) ,
  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ”
  &&  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before 0 error )
  **  ((perr) # UChar  |-> error)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
.

Definition OSQDel_entail_wit_8_2 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (q_pend_abort_output_address error_addr perr )) (PreH5 : ((q_del_int_nesting (before)) <= 0)) (PreH6 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH7 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH8 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH11 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH12 : (0 = choice)) ,
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before pe 73 )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((perr) # UChar  |-> 73)
|--
  EX (error: Z) ,
  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ”
  &&  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before pe error )
  **  ((perr) # UChar  |-> error)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
.

Definition OSQDel_entail_wit_8_3 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (perr: Z) (tasks_waiting: Z) (pq_addr_v: Z) (PreH1 : (q_pend_abort_output_address error_addr perr )) (PreH2 : (q_del_safe environment critical sg caller mask pe eid choice before X )) ,
  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before 0 0 )
  **  ((perr) # UChar  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |-> pq_addr_v)
|--
  EX (error: Z) ,
  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ”
  &&  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before 0 error )
  **  ((perr) # UChar  |-> error)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
.

Definition OSQDel_entail_wit_8_4 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (q_pend_abort_output_address error_addr perr )) (PreH4 : ((q_del_int_nesting (before)) <= 0)) (PreH5 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH6 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH7 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH10 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH11 : (0 <> choice)) (PreH12 : (1 <> choice)) ,
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before pe 7 )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((perr) # UChar  |-> 7)
|--
  EX (error: Z) ,
  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ”
  &&  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before pe error )
  **  ((perr) # UChar  |-> error)
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
.

Definition OSQDel_return_wit_1 := 
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (error: Z) (perr: Z) (pevent_return: Z) (PreH1 : (q_pend_abort_output_address error_addr perr )) (PreH2 : (q_del_safe environment critical sg caller mask pe eid choice before X )) ,
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before pevent_return error )
  **  ((perr) # UChar  |-> error)
|--
  (q_del_post environment critical saved_local sg caller mask pe eid choice before error_addr pevent_return X )
) \/
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (error: Z) (perr: Z) (pevent_return: Z) (PreH1 : (q_pend_abort_output_address error_addr perr )) (PreH2 : (q_del_safe environment critical sg caller mask pe eid choice before X )) ,
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before pevent_return error )
  **  ((perr) # UChar  |-> error)
|--
  (q_del_post environment critical saved_local sg caller mask pe eid choice before error_addr pevent_return X )
).

Definition OSQDel_return_wit_1_split_goal_spatial := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (error: Z) (perr: Z) (pevent_return: Z) (PreH1 : (q_pend_abort_output_address error_addr perr )) (PreH2 : (q_del_safe environment critical sg caller mask pe eid choice before X )) ,
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before pevent_return error )
  **  ((perr) # UChar  |-> error)
|--
  (q_del_post environment critical saved_local sg caller mask pe eid choice before error_addr pevent_return X )
.

Definition OSQDel_return_wit_2 := 
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((q_del_int_nesting (before)) > 0)) (PreH2 : (0 <= (q_del_int_nesting (before)))) (PreH3 : ((q_del_int_nesting (before)) <= 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (q_post_call_input critical sg caller pe before eid observed )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH13 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH14 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (pe = (event_addr (sg) (eid)))) (PreH18 : (pe <> 0)) (PreH19 : (valid_event_id sg eid )) (PreH20 : (q_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (q_post_call_input critical sg caller pe before eid observed )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (q_pend_abort_output_address error_addr perr_pre )) (PreH26 : (opt_pre = choice)) (PreH27 : (q_post_profile sg )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (q_post_call_input critical sg caller pe before eid observed )) (PreH30 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH31 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH33 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH34 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_del_int_nesting (before)))
  **  (q_del_interrupt_context environment saved_local sg caller mask before )
  **  ((perr_pre) # UChar  |-> 15)
|--
  (q_del_post environment critical saved_local sg caller mask pe eid choice before error_addr pe X )
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((q_del_int_nesting (before)) > 0)) (PreH2 : (0 <= (q_del_int_nesting (before)))) (PreH3 : ((q_del_int_nesting (before)) <= 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (q_post_call_input critical sg caller pe before eid observed )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH13 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH14 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (pe = (event_addr (sg) (eid)))) (PreH18 : (pe <> 0)) (PreH19 : (valid_event_id sg eid )) (PreH20 : (q_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (q_post_call_input critical sg caller pe before eid observed )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (q_pend_abort_output_address error_addr perr_pre )) (PreH26 : (opt_pre = choice)) (PreH27 : (q_post_profile sg )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (q_post_call_input critical sg caller pe before eid observed )) (PreH30 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH31 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH33 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH34 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_del_int_nesting (before)))
  **  (q_del_interrupt_context environment saved_local sg caller mask before )
  **  ((perr_pre) # UChar  |-> 15)
|--
  (q_del_post environment critical saved_local sg caller mask pe eid choice before error_addr pe X )
).

Definition OSQDel_return_wit_2_split_goal_spatial := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((q_del_int_nesting (before)) > 0)) (PreH2 : (0 <= (q_del_int_nesting (before)))) (PreH3 : ((q_del_int_nesting (before)) <= 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (q_post_call_input critical sg caller pe before eid observed )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH13 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH14 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (pe = (event_addr (sg) (eid)))) (PreH18 : (pe <> 0)) (PreH19 : (valid_event_id sg eid )) (PreH20 : (q_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (q_post_call_input critical sg caller pe before eid observed )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (q_pend_abort_output_address error_addr perr_pre )) (PreH26 : (opt_pre = choice)) (PreH27 : (q_post_profile sg )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (q_post_call_input critical sg caller pe before eid observed )) (PreH30 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH31 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH33 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH34 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_del_int_nesting (before)))
  **  (q_del_interrupt_context environment saved_local sg caller mask before )
  **  ((perr_pre) # UChar  |-> 15)
|--
  (q_del_post environment critical saved_local sg caller mask pe eid choice before error_addr pe X )
.

Definition OSQDel_return_wit_3 := 
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (q_post_call_input critical sg caller pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (q_pend_abort_output_address error_addr perr_pre )) (PreH15 : (opt_pre = choice)) (PreH16 : (q_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (q_post_call_input critical sg caller pe before eid observed )) (PreH19 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH20 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH21 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH23 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
  **  ((perr_pre) # UChar  |-> 1)
|--
  (q_del_post environment critical saved_local sg caller mask pe eid choice before error_addr pe X )
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (q_post_call_input critical sg caller pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (q_pend_abort_output_address error_addr perr_pre )) (PreH15 : (opt_pre = choice)) (PreH16 : (q_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (q_post_call_input critical sg caller pe before eid observed )) (PreH19 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH20 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH21 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH23 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
  **  ((perr_pre) # UChar  |-> 1)
|--
  (q_del_post environment critical saved_local sg caller mask pe eid choice before error_addr pe X )
).

Definition OSQDel_return_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) <> 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (q_post_call_input critical sg caller pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (q_pend_abort_output_address error_addr perr_pre )) (PreH15 : (opt_pre = choice)) (PreH16 : (q_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (q_post_call_input critical sg caller pe before eid observed )) (PreH19 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH20 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH21 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH23 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
  **  ((perr_pre) # UChar  |-> 1)
|--
  (q_del_post environment critical saved_local sg caller mask pe eid choice before error_addr pe X )
.

Definition OSQDel_return_wit_4 := 
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (q_pend_abort_output_address error_addr perr_pre )) (PreH4 : (opt_pre = choice)) (PreH5 : (q_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (q_post_call_input critical sg caller pe before eid observed )) (PreH8 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH9 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH12 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((perr_pre) # UChar  |-> 4)
|--
  (q_del_post environment critical saved_local sg caller mask pe eid choice before error_addr pevent_pre X )
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (q_pend_abort_output_address error_addr perr_pre )) (PreH4 : (opt_pre = choice)) (PreH5 : (q_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (q_post_call_input critical sg caller pe before eid observed )) (PreH8 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH9 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH12 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((perr_pre) # UChar  |-> 4)
|--
  (q_del_post environment critical saved_local sg caller mask pe eid choice before error_addr pevent_pre X )
).

Definition OSQDel_return_wit_4_split_goal_spatial := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre = 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (q_pend_abort_output_address error_addr perr_pre )) (PreH4 : (opt_pre = choice)) (PreH5 : (q_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (q_post_call_input critical sg caller pe before eid observed )) (PreH8 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH9 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH12 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((perr_pre) # UChar  |-> 4)
|--
  (q_del_post environment critical saved_local sg caller mask pe eid choice before error_addr pevent_pre X )
.

Definition OSQDel_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (q_pend_abort_output_address error_addr perr_pre )) (PreH4 : (opt_pre = choice)) (PreH5 : (q_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (q_post_call_input critical sg caller pe before eid observed )) (PreH8 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH9 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH12 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ”
.

Definition OSQDel_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pevent_pre = pe)) (PreH3 : (q_pend_abort_output_address error_addr perr_pre )) (PreH4 : (opt_pre = choice)) (PreH5 : (q_post_profile sg )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (q_post_call_input critical sg caller pe before eid observed )) (PreH8 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH9 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH12 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe <> 0) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (q_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (opt_pre = choice) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_post_closed environment critical saved_local sg caller mask before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_1 := OSQDel_partial_solve_wit_1_pure -> OSQDel_partial_solve_wit_1_aux.

Definition OSQDel_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (q_post_call_input critical sg caller pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (q_pend_abort_output_address error_addr perr_pre )) (PreH15 : (opt_pre = choice)) (PreH16 : (q_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (q_post_call_input critical sg caller pe before eid observed )) (PreH19 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH20 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH21 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH23 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSQDel_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH2 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH3 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (valid_event_id sg eid )) (PreH9 : (q_post_profile sg )) (PreH10 : (UCOS2_state_inv sg before )) (PreH11 : (q_post_call_input critical sg caller pe before eid observed )) (PreH12 : (pevent_pre <> 0)) (PreH13 : (pevent_pre = pe)) (PreH14 : (q_pend_abort_output_address error_addr perr_pre )) (PreH15 : (opt_pre = choice)) (PreH16 : (q_post_profile sg )) (PreH17 : (UCOS2_state_inv sg before )) (PreH18 : (q_post_call_input critical sg caller pe before eid observed )) (PreH19 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH20 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH21 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH23 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (q_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (opt_pre = choice) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_2 := OSQDel_partial_solve_wit_2_pure -> OSQDel_partial_solve_wit_2_aux.

Definition OSQDel_partial_solve_wit_3_pure := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((q_del_int_nesting (before)) <= 0)) (PreH2 : (0 <= (q_del_int_nesting (before)))) (PreH3 : ((q_del_int_nesting (before)) <= 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (q_post_call_input critical sg caller pe before eid observed )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH13 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH14 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (pe = (event_addr (sg) (eid)))) (PreH18 : (pe <> 0)) (PreH19 : (valid_event_id sg eid )) (PreH20 : (q_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (q_post_call_input critical sg caller pe before eid observed )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (q_pend_abort_output_address error_addr perr_pre )) (PreH26 : (opt_pre = choice)) (PreH27 : (q_post_profile sg )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (q_post_call_input critical sg caller pe before eid observed )) (PreH30 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH31 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH33 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH34 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_del_int_nesting (before)))
  **  (q_del_interrupt_context environment saved_local sg caller mask before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSQDel_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : ((q_del_int_nesting (before)) <= 0)) (PreH2 : (0 <= (q_del_int_nesting (before)))) (PreH3 : ((q_del_int_nesting (before)) <= 255)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (valid_event_id sg eid )) (PreH7 : (q_post_profile sg )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (q_post_call_input critical sg caller pe before eid observed )) (PreH10 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH13 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH14 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH15 : (0 <= UINT_MAX)) (PreH16 : (0 >= 0)) (PreH17 : (pe = (event_addr (sg) (eid)))) (PreH18 : (pe <> 0)) (PreH19 : (valid_event_id sg eid )) (PreH20 : (q_post_profile sg )) (PreH21 : (UCOS2_state_inv sg before )) (PreH22 : (q_post_call_input critical sg caller pe before eid observed )) (PreH23 : (pevent_pre <> 0)) (PreH24 : (pevent_pre = pe)) (PreH25 : (q_pend_abort_output_address error_addr perr_pre )) (PreH26 : (opt_pre = choice)) (PreH27 : (q_post_profile sg )) (PreH28 : (UCOS2_state_inv sg before )) (PreH29 : (q_post_call_input critical sg caller pe before eid observed )) (PreH30 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH31 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH32 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH33 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH34 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_del_int_nesting (before)))
  **  (q_del_interrupt_context environment saved_local sg caller mask before )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (0 <= (q_del_int_nesting (before))) ” 
  &&  “ ((q_del_int_nesting (before)) <= 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (q_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (opt_pre = choice) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_del_int_nesting (before)))
  **  (q_del_interrupt_context environment saved_local sg caller mask before )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_3 := OSQDel_partial_solve_wit_3_pure -> OSQDel_partial_solve_wit_3_aux.

Definition OSQDel_partial_solve_wit_4 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : ((q_del_int_nesting (before)) <= 0)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : ((q_del_int_nesting (before)) <= 0)) (PreH8 : (0 <= (q_del_int_nesting (before)))) (PreH9 : ((q_del_int_nesting (before)) <= 255)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (q_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_post_call_input critical sg caller pe before eid observed )) (PreH16 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH19 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (pe <> 0)) (PreH25 : (valid_event_id sg eid )) (PreH26 : (q_post_profile sg )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (q_post_call_input critical sg caller pe before eid observed )) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (q_pend_abort_output_address error_addr perr_pre )) (PreH32 : (opt_pre = choice)) (PreH33 : (q_post_profile sg )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : (q_post_call_input critical sg caller pe before eid observed )) (PreH36 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH37 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH38 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH39 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH40 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_post_save_pre environment critical saved_local sg caller mask before pe eid observed )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (0 <= (q_del_int_nesting (before))) ” 
  &&  “ ((q_del_int_nesting (before)) <= 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (q_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (opt_pre = choice) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  (q_post_save_pre environment critical saved_local sg caller mask before (event_addr (sg) (eid)) eid observed )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_5_pure := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : ((q_del_int_nesting (before)) <= 0)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : ((q_del_int_nesting (before)) <= 0)) (PreH8 : (0 <= (q_del_int_nesting (before)))) (PreH9 : ((q_del_int_nesting (before)) <= 255)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (q_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_post_call_input critical sg caller pe before eid observed )) (PreH16 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH19 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (pe <> 0)) (PreH25 : (valid_event_id sg eid )) (PreH26 : (q_post_profile sg )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (q_post_call_input critical sg caller pe before eid observed )) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (q_pend_abort_output_address error_addr perr_pre )) (PreH32 : (opt_pre = choice)) (PreH33 : (q_post_profile sg )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : (q_post_call_input critical sg caller pe before eid observed )) (PreH36 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH37 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH38 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH39 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH40 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_post_save_result environment critical saved_local sg caller mask retval before eid observed )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ”
.

Definition OSQDel_partial_solve_wit_5_aux := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (retval: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : ((q_del_int_nesting (before)) <= 0)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : ((q_del_int_nesting (before)) <= 0)) (PreH8 : (0 <= (q_del_int_nesting (before)))) (PreH9 : ((q_del_int_nesting (before)) <= 255)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (valid_event_id sg eid )) (PreH13 : (q_post_profile sg )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (q_post_call_input critical sg caller pe before eid observed )) (PreH16 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH19 : (0 <= (event_slot_type_value ((EventState (before))) (eid)))) (PreH20 : ((event_slot_type_value ((EventState (before))) (eid)) <= 255)) (PreH21 : (0 <= UINT_MAX)) (PreH22 : (0 >= 0)) (PreH23 : (pe = (event_addr (sg) (eid)))) (PreH24 : (pe <> 0)) (PreH25 : (valid_event_id sg eid )) (PreH26 : (q_post_profile sg )) (PreH27 : (UCOS2_state_inv sg before )) (PreH28 : (q_post_call_input critical sg caller pe before eid observed )) (PreH29 : (pevent_pre <> 0)) (PreH30 : (pevent_pre = pe)) (PreH31 : (q_pend_abort_output_address error_addr perr_pre )) (PreH32 : (opt_pre = choice)) (PreH33 : (q_post_profile sg )) (PreH34 : (UCOS2_state_inv sg before )) (PreH35 : (q_post_call_input critical sg caller pe before eid observed )) (PreH36 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH37 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH38 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH39 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH40 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_post_save_result environment critical saved_local sg caller mask retval before eid observed )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (0 <= (q_del_int_nesting (before))) ” 
  &&  “ ((q_del_int_nesting (before)) <= 255) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (0 <= (event_slot_type_value ((EventState (before))) (eid))) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (q_pend_abort_output_address error_addr perr_pre ) ” 
  &&  “ (opt_pre = choice) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_post_save_result environment critical saved_local sg caller mask retval before eid observed )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_5 := OSQDel_partial_solve_wit_5_pure -> OSQDel_partial_solve_wit_5_aux.

Definition OSQDel_partial_solve_wit_6_pure := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (q_pend_abort_output_address error_addr perr )) (PreH4 : ((q_del_int_nesting (before)) <= 0)) (PreH5 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH6 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH7 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH10 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_post_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (initial)))
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ ((q_del_waiting (acquired) (initial)) = (q_del_waiting (acquired) (initial))) ”
.

Definition OSQDel_partial_solve_wit_6_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (q_pend_abort_output_address error_addr perr )) (PreH4 : ((q_del_int_nesting (before)) <= 0)) (PreH5 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH6 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH7 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH10 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  (q_post_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (initial)))
  **  ((perr) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ ((q_del_waiting (acquired) (initial)) = (q_del_waiting (acquired) (initial))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (tasks_waiting = (q_del_waiting (acquired) (initial))) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  (q_post_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (initial)))
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_6 := OSQDel_partial_solve_wit_6_pure -> OSQDel_partial_solve_wit_6_aux.

Definition OSQDel_partial_solve_wit_7_pure := 
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (q_pend_abort_output_address error_addr perr )) (PreH6 : ((q_del_int_nesting (before)) <= 0)) (PreH7 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH8 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH9 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH12 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH13 : (0 = choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice = 0) ” 
  &&  “ ((q_del_waiting (acquired) (initial)) <= 0) ” 
  &&  “ (tasks_waiting <= 0) ”
) \/
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (q_pend_abort_output_address error_addr perr )) (PreH7 : ((q_del_int_nesting (before)) <= 0)) (PreH8 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH9 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH10 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH13 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH14 : (0 = choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (tasks_waiting <= 0) ” 
  &&  “ (tasks_waiting <= 0) ”
).

Definition OSQDel_partial_solve_wit_7_pure_split_goal_1 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (q_pend_abort_output_address error_addr perr )) (PreH7 : ((q_del_int_nesting (before)) <= 0)) (PreH8 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH9 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH10 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH13 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH14 : (0 = choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (tasks_waiting <= 0) ”
.

Definition OSQDel_partial_solve_wit_7_pure_split_goal_2 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (q_pend_abort_output_address error_addr perr )) (PreH7 : ((q_del_int_nesting (before)) <= 0)) (PreH8 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH9 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH10 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH13 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH14 : (0 = choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (tasks_waiting <= 0) ”
.

Definition OSQDel_partial_solve_wit_7_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (q_pend_abort_output_address error_addr perr )) (PreH6 : ((q_del_int_nesting (before)) <= 0)) (PreH7 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH8 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH9 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH12 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH13 : (0 = choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((perr) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice = 0) ” 
  &&  “ ((q_del_waiting (acquired) (initial)) <= 0) ” 
  &&  “ (tasks_waiting <= 0) ” 
  &&  “ ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (tasks_waiting = (q_del_waiting (acquired) (initial))) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (0 = choice) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_7 := OSQDel_partial_solve_wit_7_pure -> OSQDel_partial_solve_wit_7_aux.

Definition OSQDel_partial_solve_wit_8_pure := 
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (q: QueueFields) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (choice = 0)) (PreH4 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (q_pend_abort_output_address error_addr perr )) (PreH8 : ((q_del_int_nesting (before)) <= 0)) (PreH9 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH10 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH11 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH14 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH15 : (0 = choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_pointer_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) choice q )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q)))) (qcb_addr (sg) ((qID (q)))) ) ”
) \/
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (q: QueueFields) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (choice = 0)) (PreH6 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (q_pend_abort_output_address error_addr perr )) (PreH10 : ((q_del_int_nesting (before)) <= 0)) (PreH11 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH12 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH13 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH16 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH17 : (0 = choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_pointer_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) choice q )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q)))) (qcb_addr (sg) ((qID (q)))) ) ”
).

Definition OSQDel_partial_solve_wit_8_pure_split_goal_1 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (q: QueueFields) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (choice = 0)) (PreH6 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (q_pend_abort_output_address error_addr perr )) (PreH10 : ((q_del_int_nesting (before)) <= 0)) (PreH11 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH12 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH13 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH14 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH16 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH17 : (0 = choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_pointer_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) choice q )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q)))) (qcb_addr (sg) ((qID (q)))) ) ”
.

Definition OSQDel_partial_solve_wit_8_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (q: QueueFields) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (choice = 0)) (PreH4 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (q_pend_abort_output_address error_addr perr )) (PreH8 : ((q_del_int_nesting (before)) <= 0)) (PreH9 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH10 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH11 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH12 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH14 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH15 : (0 = choice)) ,
  (q_del_pointer_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) choice q )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((perr) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q)))) (qcb_addr (sg) ((qID (q)))) ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice = 0) ” 
  &&  “ ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (tasks_waiting = (q_del_waiting (acquired) (initial))) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (0 = choice) ”
  &&  (q_del_pointer_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) choice q )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_8 := OSQDel_partial_solve_wit_8_pure -> OSQDel_partial_solve_wit_8_aux.

Definition OSQDel_partial_solve_wit_9_pure := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (q: QueueFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (q_2: QueueFields) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH3 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH4 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (choice = 0)) (PreH8 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe <> 0)) (PreH11 : (q_pend_abort_output_address error_addr perr )) (PreH12 : ((q_del_int_nesting (before)) <= 0)) (PreH13 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH14 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH15 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH18 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH19 : (0 = choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_recycle_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) choice q_2 free slots )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (free)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (q_del_event_free_head (sg) (acquired_2)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
.

Definition OSQDel_partial_solve_wit_9_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (q: QueueFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (free: (@list Z)) (slots: (@list (@option Z))) (q_2: QueueFields) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH3 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH4 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (choice = 0)) (PreH8 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe <> 0)) (PreH11 : (q_pend_abort_output_address error_addr perr )) (PreH12 : ((q_del_int_nesting (before)) <= 0)) (PreH13 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH14 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH15 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH18 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH19 : (0 = choice)) ,
  (q_del_recycle_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) choice q_2 free slots )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (free)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (q_del_event_free_head (sg) (acquired_2)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pe)
  **  ((perr) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice = 0) ” 
  &&  “ ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (tasks_waiting = (q_del_waiting (acquired) (initial))) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (0 = choice) ”
  &&  (q_del_recycle_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) choice q_2 free slots )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (free)))
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (q_del_event_free_head (sg) (acquired_2)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pe)
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_9 := OSQDel_partial_solve_wit_9_pure -> OSQDel_partial_solve_wit_9_aux.

Definition OSQDel_partial_solve_wit_10_pure := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (q: QueueFields) (q_2: QueueFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (released: UCOS2_Verify_State) (buffer: QDelBuffer) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH3 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH4 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (choice = 0)) (PreH8 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe <> 0)) (PreH11 : (q_pend_abort_output_address error_addr perr )) (PreH12 : ((q_del_int_nesting (before)) <= 0)) (PreH13 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH14 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH15 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH18 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH19 : (0 = choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid choice before acquired_2 released 0 0 0 buffer )
  **  (q_del_buffer_rep buffer )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSQDel_partial_solve_wit_10_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (q: QueueFields) (q_2: QueueFields) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (released: UCOS2_Verify_State) (buffer: QDelBuffer) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH3 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH4 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (choice = 0)) (PreH8 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe <> 0)) (PreH11 : (q_pend_abort_output_address error_addr perr )) (PreH12 : ((q_del_int_nesting (before)) <= 0)) (PreH13 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH14 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH15 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH18 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH19 : (0 = choice)) ,
  (q_del_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid choice before acquired_2 released 0 0 0 buffer )
  **  (q_del_buffer_rep buffer )
  **  ((perr) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice = 0) ” 
  &&  “ ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (tasks_waiting = (q_del_waiting (acquired) (initial))) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (0 = choice) ”
  &&  (q_del_restore_pre environment critical saved_local sg caller active mask cpu_sr (event_addr (sg) (eid)) eid 0 before acquired_2 released 0 0 0 buffer )
  **  (q_del_buffer_rep buffer )
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_10 := OSQDel_partial_solve_wit_10_pure -> OSQDel_partial_solve_wit_10_aux.

Definition OSQDel_partial_solve_wit_11 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (q: QueueFields) (q_2: QueueFields) (buffer: QDelBuffer) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH3 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH4 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (choice = 0)) (PreH8 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe <> 0)) (PreH11 : (q_pend_abort_output_address error_addr perr )) (PreH12 : ((q_del_int_nesting (before)) <= 0)) (PreH13 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH14 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH15 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH18 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH19 : (0 = choice)) ,
  (q_del_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid 0 before 0 0 0 buffer )
  **  (q_del_buffer_rep buffer )
  **  ((perr) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice = 0) ” 
  &&  “ ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (tasks_waiting = (q_del_waiting (acquired) (initial))) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (0 = choice) ”
  &&  (q_del_restore_post environment critical saved_local sg caller mask pe eid choice before 0 0 0 buffer )
  **  (q_del_buffer_rep buffer )
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_12_pure := 
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) <> 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (q_pend_abort_output_address error_addr perr )) (PreH6 : ((q_del_int_nesting (before)) <= 0)) (PreH7 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH8 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH9 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH12 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH13 : (0 = choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice = 0) ” 
  &&  “ ((q_del_waiting (acquired) (initial)) <> 0) ” 
  &&  “ (tasks_waiting <> 0) ”
) \/
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (q_pend_abort_output_address error_addr perr )) (PreH7 : ((q_del_int_nesting (before)) <= 0)) (PreH8 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH9 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH10 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH13 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH14 : (0 = choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (tasks_waiting <> 0) ” 
  &&  “ (tasks_waiting <> 0) ”
).

Definition OSQDel_partial_solve_wit_12_pure_split_goal_1 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (q_pend_abort_output_address error_addr perr )) (PreH7 : ((q_del_int_nesting (before)) <= 0)) (PreH8 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH9 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH10 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH13 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH14 : (0 = choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (tasks_waiting <> 0) ”
.

Definition OSQDel_partial_solve_wit_12_pure_split_goal_2 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (q_pend_abort_output_address error_addr perr )) (PreH7 : ((q_del_int_nesting (before)) <= 0)) (PreH8 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH9 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH10 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH13 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH14 : (0 = choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (tasks_waiting <> 0) ”
.

Definition OSQDel_partial_solve_wit_12_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) <> 0)) (PreH2 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (q_pend_abort_output_address error_addr perr )) (PreH6 : ((q_del_int_nesting (before)) <= 0)) (PreH7 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH8 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH9 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH12 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH13 : (0 = choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((perr) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice = 0) ” 
  &&  “ ((q_del_waiting (acquired) (initial)) <> 0) ” 
  &&  “ (tasks_waiting <> 0) ” 
  &&  “ ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (tasks_waiting = (q_del_waiting (acquired) (initial))) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (0 = choice) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_12 := OSQDel_partial_solve_wit_12_pure -> OSQDel_partial_solve_wit_12_aux.

Definition OSQDel_partial_solve_wit_13_pure := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (q_pend_abort_output_address error_addr perr )) (PreH5 : ((q_del_int_nesting (before)) <= 0)) (PreH6 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH7 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH8 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH11 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH12 : (0 = choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid choice before acquired_2 acquired_2 pe 73 0 QDelNoBuffer )
  **  (q_del_buffer_rep QDelNoBuffer )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSQDel_partial_solve_wit_13_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (q_pend_abort_output_address error_addr perr )) (PreH5 : ((q_del_int_nesting (before)) <= 0)) (PreH6 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH7 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH8 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH11 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH12 : (0 = choice)) ,
  (q_del_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid choice before acquired_2 acquired_2 pe 73 0 QDelNoBuffer )
  **  (q_del_buffer_rep QDelNoBuffer )
  **  ((perr) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (tasks_waiting = (q_del_waiting (acquired) (initial))) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (0 = choice) ”
  &&  (q_del_restore_pre environment critical saved_local sg caller active mask cpu_sr (event_addr (sg) (eid)) eid 0 before acquired_2 acquired_2 (event_addr (sg) (eid)) 73 0 QDelNoBuffer )
  **  (q_del_buffer_rep QDelNoBuffer )
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_13 := OSQDel_partial_solve_wit_13_pure -> OSQDel_partial_solve_wit_13_aux.

Definition OSQDel_partial_solve_wit_14 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (PreH1 : ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (q_pend_abort_output_address error_addr perr )) (PreH5 : ((q_del_int_nesting (before)) <= 0)) (PreH6 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH7 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH8 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH11 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH12 : (0 = choice)) ,
  (q_del_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid 0 before (event_addr (sg) (eid)) 73 0 QDelNoBuffer )
  **  (q_del_buffer_rep QDelNoBuffer )
  **  ((perr) # UChar  |->_)
|--
  “ ((unsigned_last_nbits ((q_del_waiting (acquired) (initial))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (tasks_waiting = (q_del_waiting (acquired) (initial))) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (0 = choice) ”
  &&  (q_del_restore_post environment critical saved_local sg caller mask pe eid choice before pe 73 0 QDelNoBuffer )
  **  (q_del_buffer_rep QDelNoBuffer )
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_15_pure := 
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (processed: (@list Z)) (tasks_waiting: Z) (perr: Z) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (q_pend_abort_output_address error_addr perr )) (PreH5 : (choice = 1)) (PreH6 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH7 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH10 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed tasks_waiting )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (state) (node)) <> 0) ”
) \/
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (processed: (@list Z)) (tasks_waiting: Z) (perr: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (q_pend_abort_output_address error_addr perr )) (PreH7 : (choice = 1)) (PreH8 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH9 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH12 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed tasks_waiting )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ ((q_post_group (state) (node)) <> 0) ”
).

Definition OSQDel_partial_solve_wit_15_pure_split_goal_1 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (processed: (@list Z)) (tasks_waiting: Z) (perr: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (q_pend_abort_output_address error_addr perr )) (PreH7 : (choice = 1)) (PreH8 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH9 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH12 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed tasks_waiting )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ ((q_post_group (state) (node)) <> 0) ”
.

Definition OSQDel_partial_solve_wit_15_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (processed: (@list Z)) (tasks_waiting: Z) (perr: Z) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (q_pend_abort_output_address error_addr perr )) (PreH5 : (choice = 1)) (PreH6 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH7 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH10 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed tasks_waiting )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ ((q_post_group (state) (node)) <> 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ (choice = 1) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed tasks_waiting )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_15 := OSQDel_partial_solve_wit_15_pure -> OSQDel_partial_solve_wit_15_aux.

Definition OSQDel_partial_solve_wit_16_pure := 
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (q_pend_abort_output_address error_addr perr )) (PreH6 : (choice = 1)) (PreH7 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH8 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH11 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed tasks_waiting tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 4 2 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
) \/
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (tid: Z) (old: TaskAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (q_pend_abort_output_address error_addr perr )) (PreH7 : (choice = 1)) (PreH8 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH9 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH12 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed tasks_waiting tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 4 2 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
).

Definition OSQDel_partial_solve_wit_16_pure_split_goal_1 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (tid: Z) (old: TaskAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (q_pend_abort_output_address error_addr perr )) (PreH7 : (choice = 1)) (PreH8 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH9 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH12 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed tasks_waiting tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 4 2 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ”
.

Definition OSQDel_partial_solve_wit_16_pure_split_goal_2 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (tid: Z) (old: TaskAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (q_pend_abort_output_address error_addr perr )) (PreH7 : (choice = 1)) (PreH8 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH9 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH12 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed tasks_waiting tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 4 2 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ”
.

Definition OSQDel_partial_solve_wit_16_pure_split_goal_3 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (tid: Z) (old: TaskAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (q_pend_abort_output_address error_addr perr )) (PreH7 : (choice = 1)) (PreH8 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH9 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH12 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed tasks_waiting tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 4 2 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
.

Definition OSQDel_partial_solve_wit_16_pure_split_goal_4 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (tid: Z) (old: TaskAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (q_pend_abort_output_address error_addr perr )) (PreH7 : (choice = 1)) (PreH8 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH9 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH12 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed tasks_waiting tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 4 2 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
.

Definition OSQDel_partial_solve_wit_16_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (tid: Z) (old: TaskAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (q_pend_abort_output_address error_addr perr )) (PreH6 : (choice = 1)) (PreH7 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH8 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH11 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed tasks_waiting tid old )
  **  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 4 2 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  ((perr) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSTCBPrioTbl" ) ) = (g_OSTCBPrioTbl (sg))) ” 
  &&  “ (( &( "OSUnMapTbl" ) ) = (g_OSUnMapTbl (sg))) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ (choice = 1) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  (event_task_rdy_pre sg (TskState (state_2)) eid node_2 tid old 4 2 (q_post_sched_group (state_2)) (q_post_sched_rows (state_2)) )
  **  (q_del_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed tasks_waiting tid old )
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_16 := OSQDel_partial_solve_wit_16_pure -> OSQDel_partial_solve_wit_16_aux.

Definition OSQDel_partial_solve_wit_17_pure := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (state: UCOS2_Verify_State) (initial: OSEventAbstractState) (node: OSEventAbstractState) (processed: (@list Z)) (tid: Z) (old: TaskAbstractState) (priority: Z) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (q_pend_abort_output_address error_addr perr )) (PreH4 : (choice = 1)) (PreH5 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH6 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH9 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed tasks_waiting tid old )
  **  (event_task_rdy_post sg (TskState (state)) eid node tid old 0 4 2 (q_post_sched_group (state)) (q_post_sched_rows (state)) priority )
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ”
.

Definition OSQDel_partial_solve_wit_17_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (state: UCOS2_Verify_State) (initial: OSEventAbstractState) (node: OSEventAbstractState) (processed: (@list Z)) (tid: Z) (old: TaskAbstractState) (priority: Z) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (q_pend_abort_output_address error_addr perr )) (PreH4 : (choice = 1)) (PreH5 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH6 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH9 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_del_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed tasks_waiting tid old )
  **  (event_task_rdy_post sg (TskState (state)) eid node tid old 0 4 2 (q_post_sched_group (state)) (q_post_sched_rows (state)) priority )
  **  ((perr) # UChar  |->_)
|--
  “ ((event_addr (sg) (eid)) = (event_addr (sg) (eid))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ (choice = 1) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_del_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed tasks_waiting tid old )
  **  (event_task_rdy_post sg (TskState (state)) eid node tid old 0 4 2 (q_post_sched_group (state)) (q_post_sched_rows (state)) priority )
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_17 := OSQDel_partial_solve_wit_17_pure -> OSQDel_partial_solve_wit_17_aux.

Definition OSQDel_partial_solve_wit_18_pure := 
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (processed: (@list Z)) (tasks_waiting: Z) (perr: Z) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (q_pend_abort_output_address error_addr perr )) (PreH5 : (choice = 1)) (PreH6 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH7 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH10 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed tasks_waiting )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice = 1) ” 
  &&  “ ((q_post_group (state) (node)) = 0) ”
) \/
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (processed: (@list Z)) (tasks_waiting: Z) (perr: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (q_pend_abort_output_address error_addr perr )) (PreH7 : (choice = 1)) (PreH8 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH9 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH12 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed tasks_waiting )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ ((q_post_group (state) (node)) = 0) ”
).

Definition OSQDel_partial_solve_wit_18_pure_split_goal_1 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (processed: (@list Z)) (tasks_waiting: Z) (perr: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (pe <> 0)) (PreH6 : (q_pend_abort_output_address error_addr perr )) (PreH7 : (choice = 1)) (PreH8 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH9 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH12 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed tasks_waiting )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ ((q_post_group (state) (node)) = 0) ”
.

Definition OSQDel_partial_solve_wit_18_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (active: TaskResumeCaller) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (processed: (@list Z)) (tasks_waiting: Z) (perr: Z) (PreH1 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (q_pend_abort_output_address error_addr perr )) (PreH5 : (choice = 1)) (PreH6 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH7 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH10 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed tasks_waiting )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice = 1) ” 
  &&  “ ((q_post_group (state) (node)) = 0) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ (choice = 1) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed tasks_waiting )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state) (node)))
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_18 := OSQDel_partial_solve_wit_18_pure -> OSQDel_partial_solve_wit_18_aux.

Definition OSQDel_partial_solve_wit_19_pure := 
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (q: QueueFields) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (choice = 1)) (PreH4 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (q_pend_abort_output_address error_addr perr )) (PreH8 : (choice = 1)) (PreH9 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH10 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH13 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_pointer_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed tasks_waiting choice q )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q)))) (qcb_addr (sg) ((qID (q)))) ) ”
) \/
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (q: QueueFields) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (choice = 1)) (PreH6 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (q_pend_abort_output_address error_addr perr )) (PreH10 : (choice = 1)) (PreH11 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH12 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH13 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH15 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_pointer_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed tasks_waiting choice q )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q)))) (qcb_addr (sg) ((qID (q)))) ) ”
).

Definition OSQDel_partial_solve_wit_19_pure_split_goal_1 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (q: QueueFields) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (choice = 1)) (PreH6 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (q_pend_abort_output_address error_addr perr )) (PreH10 : (choice = 1)) (PreH11 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH12 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH13 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH14 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH15 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_pointer_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed tasks_waiting choice q )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q)))) (qcb_addr (sg) ((qID (q)))) ) ”
.

Definition OSQDel_partial_solve_wit_19_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (q: QueueFields) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (choice = 1)) (PreH4 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (q_pend_abort_output_address error_addr perr )) (PreH8 : (choice = 1)) (PreH9 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH10 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH13 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_pointer_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed tasks_waiting choice q )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((perr) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q)))) (qcb_addr (sg) ((qID (q)))) ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice = 1) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ (choice = 1) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  (q_del_pointer_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed tasks_waiting choice q )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_19 := OSQDel_partial_solve_wit_19_pure -> OSQDel_partial_solve_wit_19_aux.

Definition OSQDel_partial_solve_wit_20_pure := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (q: QueueFields) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (free: (@list Z)) (slots: (@list (@option Z))) (q_2: QueueFields) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH3 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH4 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (choice = 1)) (PreH8 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe <> 0)) (PreH11 : (q_pend_abort_output_address error_addr perr )) (PreH12 : (choice = 1)) (PreH13 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH14 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH15 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH17 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_recycle_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed tasks_waiting choice q_2 free slots )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (free)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (q_del_event_free_head (sg) (state_2)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pe)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
.

Definition OSQDel_partial_solve_wit_20_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (q: QueueFields) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (state_2: UCOS2_Verify_State) (node_2: OSEventAbstractState) (processed: (@list Z)) (free: (@list Z)) (slots: (@list (@option Z))) (q_2: QueueFields) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH3 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH4 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (choice = 1)) (PreH8 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe <> 0)) (PreH11 : (q_pend_abort_output_address error_addr perr )) (PreH12 : (choice = 1)) (PreH13 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH14 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH15 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH17 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_recycle_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed tasks_waiting choice q_2 free slots )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (free)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (q_del_event_free_head (sg) (state_2)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pe)
  **  ((perr) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice = 1) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ (choice = 1) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  (q_del_recycle_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state_2 node_2 processed tasks_waiting choice q_2 free slots )
  **  ((&(((qcb_addr (sg) ((qID (q)))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (free)))
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (q_del_event_free_head (sg) (state_2)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pe)
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_20 := OSQDel_partial_solve_wit_20_pure -> OSQDel_partial_solve_wit_20_aux.

Definition OSQDel_partial_solve_wit_21_pure := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (q: QueueFields) (q_2: QueueFields) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (buffer: QDelBuffer) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH3 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH4 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (choice = 1)) (PreH8 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe <> 0)) (PreH11 : (q_pend_abort_output_address error_addr perr )) (PreH12 : (choice = 1)) (PreH13 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH14 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH15 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH17 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid choice before acquired released 0 0 tasks_waiting buffer )
  **  (q_del_buffer_rep buffer )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSQDel_partial_solve_wit_21_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (q: QueueFields) (q_2: QueueFields) (active: TaskResumeCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (buffer: QDelBuffer) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH3 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH4 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (pe <> 0)) (PreH7 : (choice = 1)) (PreH8 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH9 : (pe = (event_addr (sg) (eid)))) (PreH10 : (pe <> 0)) (PreH11 : (q_pend_abort_output_address error_addr perr )) (PreH12 : (choice = 1)) (PreH13 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH14 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH15 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH17 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid choice before acquired released 0 0 tasks_waiting buffer )
  **  (q_del_buffer_rep buffer )
  **  ((perr) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice = 1) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ (choice = 1) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  (q_del_restore_pre environment critical saved_local sg caller active mask cpu_sr (event_addr (sg) (eid)) eid 1 before acquired released 0 0 tasks_waiting buffer )
  **  (q_del_buffer_rep buffer )
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_21 := OSQDel_partial_solve_wit_21_pure -> OSQDel_partial_solve_wit_21_aux.

Definition OSQDel_partial_solve_wit_22_pure := 
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (q: QueueFields) (q_2: QueueFields) (buffer: QDelBuffer) (PreH1 : ((unsigned_last_nbits (tasks_waiting) (32)) = 1)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH4 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH5 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (choice = 1)) (PreH9 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (q_pend_abort_output_address error_addr perr )) (PreH13 : (choice = 1)) (PreH14 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH15 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH18 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid 1 before 0 0 tasks_waiting buffer )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_buffer_rep buffer )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (1 <= tasks_waiting) ”
) \/
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (q: QueueFields) (q_2: QueueFields) (buffer: QDelBuffer) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits (tasks_waiting) (32)) = 1)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH6 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH7 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe <> 0)) (PreH10 : (choice = 1)) (PreH11 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (q_pend_abort_output_address error_addr perr )) (PreH15 : (choice = 1)) (PreH16 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH17 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH20 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid 1 before 0 0 tasks_waiting buffer )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_buffer_rep buffer )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (1 <= tasks_waiting) ”
).

Definition OSQDel_partial_solve_wit_22_pure_split_goal_1 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (q: QueueFields) (q_2: QueueFields) (buffer: QDelBuffer) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : ((unsigned_last_nbits (tasks_waiting) (32)) = 1)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH6 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH7 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (pe <> 0)) (PreH10 : (choice = 1)) (PreH11 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH12 : (pe = (event_addr (sg) (eid)))) (PreH13 : (pe <> 0)) (PreH14 : (q_pend_abort_output_address error_addr perr )) (PreH15 : (choice = 1)) (PreH16 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH17 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH18 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH19 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH20 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid 1 before 0 0 tasks_waiting buffer )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_buffer_rep buffer )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (1 <= tasks_waiting) ”
.

Definition OSQDel_partial_solve_wit_22_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (q: QueueFields) (q_2: QueueFields) (buffer: QDelBuffer) (PreH1 : ((unsigned_last_nbits (tasks_waiting) (32)) = 1)) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH4 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH5 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (pe <> 0)) (PreH8 : (choice = 1)) (PreH9 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (pe <> 0)) (PreH12 : (q_pend_abort_output_address error_addr perr )) (PreH13 : (choice = 1)) (PreH14 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH15 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH16 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH18 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid 1 before 0 0 tasks_waiting buffer )
  **  (q_del_buffer_rep buffer )
  **  ((perr) # UChar  |->_)
|--
  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (1 <= tasks_waiting) ” 
  &&  “ ((unsigned_last_nbits (tasks_waiting) (32)) = 1) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice = 1) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ (choice = 1) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  (q_del_restore_post environment critical saved_local sg caller mask pe eid choice before 0 0 tasks_waiting buffer )
  **  (q_del_buffer_rep buffer )
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_22 := OSQDel_partial_solve_wit_22_pure -> OSQDel_partial_solve_wit_22_aux.

Definition OSQDel_partial_solve_wit_23_pure := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (q: QueueFields) (q_2: QueueFields) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (buffer: QDelBuffer) (PreH1 : (q_del_prefix_result environment critical sg caller mask pe eid choice before 0 0 1 returned restored buffer )) (PreH2 : ((unsigned_last_nbits (tasks_waiting) (32)) = 1)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH5 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH6 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (choice = 1)) (PreH10 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (q_pend_abort_output_address error_addr perr )) (PreH14 : (choice = 1)) (PreH15 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH16 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH19 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  (q_del_buffer_rep buffer )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSQDel_partial_solve_wit_23_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (q: QueueFields) (q_2: QueueFields) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (buffer: QDelBuffer) (PreH1 : (q_del_prefix_result environment critical sg caller mask pe eid choice before 0 0 1 returned restored buffer )) (PreH2 : ((unsigned_last_nbits (tasks_waiting) (32)) = 1)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH5 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH6 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (choice = 1)) (PreH10 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (q_pend_abort_output_address error_addr perr )) (PreH14 : (choice = 1)) (PreH15 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH16 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH19 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  (q_del_buffer_rep buffer )
  **  ((perr) # UChar  |->_)
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (q_del_prefix_result environment critical sg caller mask pe eid choice before 0 0 1 returned restored buffer ) ” 
  &&  “ ((unsigned_last_nbits (tasks_waiting) (32)) = 1) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice = 1) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ (choice = 1) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  (q_del_buffer_rep buffer )
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_23 := OSQDel_partial_solve_wit_23_pure -> OSQDel_partial_solve_wit_23_aux.

Definition OSQDel_partial_solve_wit_24_pure := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (q: QueueFields) (q_2: QueueFields) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (buffer: QDelBuffer) (PreH1 : (q_del_prefix_result environment critical sg caller mask pe eid choice before 0 0 1 returned restored buffer )) (PreH2 : ((unsigned_last_nbits (tasks_waiting) (32)) = 1)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH5 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH6 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (choice = 1)) (PreH10 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (q_pend_abort_output_address error_addr perr )) (PreH14 : (choice = 1)) (PreH15 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH16 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH19 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  (q_post_extra_tables sg returned )
  **  (q_del_buffer_rep buffer )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "pq" ) )) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (q_del_prefix_result environment critical sg caller mask pe eid choice before 0 0 1 returned restored buffer ) ”
.

Definition OSQDel_partial_solve_wit_24_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (state: UCOS2_Verify_State) (node: OSEventAbstractState) (tasks_waiting: Z) (perr: Z) (q: QueueFields) (q_2: QueueFields) (returned: TaskResumeCaller) (restored: UCOS2_Verify_State) (buffer: QDelBuffer) (PreH1 : (q_del_prefix_result environment critical sg caller mask pe eid choice before 0 0 1 returned restored buffer )) (PreH2 : ((unsigned_last_nbits (tasks_waiting) (32)) = 1)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) )) (PreH5 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH6 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (pe <> 0)) (PreH9 : (choice = 1)) (PreH10 : ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0)) (PreH11 : (pe = (event_addr (sg) (eid)))) (PreH12 : (pe <> 0)) (PreH13 : (q_pend_abort_output_address error_addr perr )) (PreH14 : (choice = 1)) (PreH15 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH16 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH17 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH19 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  (q_del_buffer_rep buffer )
  **  ((perr) # UChar  |->_)
|--
  “ (q_del_prefix_result environment critical sg caller mask pe eid choice before 0 0 1 returned restored buffer ) ” 
  &&  “ (q_del_prefix_result environment critical sg caller mask pe eid choice before 0 0 1 returned restored buffer ) ” 
  &&  “ ((unsigned_last_nbits (tasks_waiting) (32)) = 1) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) (qcb_addr (sg) ((qID (q)))) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice = 1) ” 
  &&  “ ((unsigned_last_nbits ((q_post_group (state) (node))) (32)) = 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ (choice = 1) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  (q_del_buffer_rep buffer )
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_24 := OSQDel_partial_solve_wit_24_pure -> OSQDel_partial_solve_wit_24_aux.

Definition OSQDel_partial_solve_wit_25 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (perr: Z) (tasks_waiting: Z) (PreH1 : (q_pend_abort_output_address error_addr perr )) (PreH2 : (q_del_safe environment critical sg caller mask pe eid choice before X )) ,
  (q_del_after_schedule_context environment critical saved_local sg caller mask pe eid choice before tasks_waiting )
  **  ((perr) # UChar  |->_)
|--
  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ”
  &&  (q_del_after_schedule_context environment critical saved_local sg caller mask pe eid choice before tasks_waiting )
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_26 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (q_pend_abort_output_address error_addr perr )) (PreH4 : ((q_del_int_nesting (before)) <= 0)) (PreH5 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH6 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH7 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH10 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH11 : (0 <> choice)) (PreH12 : (1 <> choice)) ,
  (q_del_restore_post environment critical saved_local sg caller mask (event_addr (sg) (eid)) eid choice before (event_addr (sg) (eid)) 7 0 QDelNoBuffer )
  **  (q_del_buffer_rep QDelNoBuffer )
  **  ((perr) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (tasks_waiting = (q_del_waiting (acquired) (initial))) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (0 <> choice) ” 
  &&  “ (1 <> choice) ”
  &&  (q_del_restore_post environment critical saved_local sg caller mask pe eid choice before pe 7 0 QDelNoBuffer )
  **  (q_del_buffer_rep QDelNoBuffer )
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_27_pure := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (q_pend_abort_output_address error_addr perr )) (PreH4 : ((q_del_int_nesting (before)) <= 0)) (PreH5 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH6 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH7 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH10 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH11 : (0 <> choice)) (PreH12 : (1 <> choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid choice before acquired_2 acquired_2 pe 7 0 QDelNoBuffer )
  **  (q_del_buffer_rep QDelNoBuffer )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSQDel_partial_solve_wit_27_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (q_pend_abort_output_address error_addr perr )) (PreH4 : ((q_del_int_nesting (before)) <= 0)) (PreH5 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH6 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH7 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH10 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH11 : (0 <> choice)) (PreH12 : (1 <> choice)) ,
  (q_del_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid choice before acquired_2 acquired_2 pe 7 0 QDelNoBuffer )
  **  (q_del_buffer_rep QDelNoBuffer )
  **  ((perr) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (tasks_waiting = (q_del_waiting (acquired) (initial))) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (0 <> choice) ” 
  &&  “ (1 <> choice) ”
  &&  (q_del_restore_pre environment critical saved_local sg caller active mask cpu_sr (event_addr (sg) (eid)) eid choice before acquired_2 acquired_2 (event_addr (sg) (eid)) 7 0 QDelNoBuffer )
  **  (q_del_buffer_rep QDelNoBuffer )
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_27 := OSQDel_partial_solve_wit_27_pure -> OSQDel_partial_solve_wit_27_aux.

Definition OSQDel_partial_solve_wit_28_pure := 
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (q_pend_abort_output_address error_addr perr )) (PreH5 : ((q_del_int_nesting (before)) <= 0)) (PreH6 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH7 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH8 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH11 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH12 : (0 <> choice)) (PreH13 : (1 <> choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice <> 0) ” 
  &&  “ (choice <> 1) ” 
  &&  “ (choice <= 255) ” 
  &&  “ (0 <= choice) ”
) \/
(
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (q_pend_abort_output_address error_addr perr )) (PreH6 : ((q_del_int_nesting (before)) <= 0)) (PreH7 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH8 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH9 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH12 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH13 : (0 <> choice)) (PreH14 : (1 <> choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (0 <= choice) ” 
  &&  “ (choice <= 255) ”
).

Definition OSQDel_partial_solve_wit_28_pure_split_goal_1 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (q_pend_abort_output_address error_addr perr )) (PreH6 : ((q_del_int_nesting (before)) <= 0)) (PreH7 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH8 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH9 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH12 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH13 : (0 <> choice)) (PreH14 : (1 <> choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (0 <= choice) ”
.

Definition OSQDel_partial_solve_wit_28_pure_split_goal_2 := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (pe = (event_addr (sg) (eid)))) (PreH4 : (pe <> 0)) (PreH5 : (q_pend_abort_output_address error_addr perr )) (PreH6 : ((q_del_int_nesting (before)) <= 0)) (PreH7 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH8 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH9 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH12 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH13 : (0 <> choice)) (PreH14 : (1 <> choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> (q_del_waiting (acquired) (initial)))
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "opt" ) )) # UChar  |-> choice)
  **  ((perr) # UChar  |->_)
  **  ((( &( "pq" ) )) # Ptr  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
|--
  “ (choice <= 255) ”
.

Definition OSQDel_partial_solve_wit_28_aux := 
forall (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (choice: Z) (error_addr: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (acquired: UCOS2_Verify_State) (initial: OSEventAbstractState) (perr: Z) (tasks_waiting: Z) (cpu_sr: Z) (active: TaskResumeCaller) (acquired_2: UCOS2_Verify_State) (initial_2: OSEventAbstractState) (PreH1 : ((event_addr (sg) (eid)) = (event_addr (sg) (eid)))) (PreH2 : (pe = (event_addr (sg) (eid)))) (PreH3 : (pe <> 0)) (PreH4 : (q_pend_abort_output_address error_addr perr )) (PreH5 : ((q_del_int_nesting (before)) <= 0)) (PreH6 : (tasks_waiting = (q_del_waiting (acquired) (initial)))) (PreH7 : (q_del_safe environment critical sg caller mask pe eid choice before X )) (PreH8 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH11 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) (PreH12 : (0 <> choice)) (PreH13 : (1 <> choice)) ,
  ((( &( "pevent" ) )) # Ptr  |-> (event_addr (sg) (eid)))
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) )
  **  ((&(((event_addr (sg) (eid)))  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((perr) # UChar  |->_)
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice <> 0) ” 
  &&  “ (choice <> 1) ” 
  &&  “ (choice <= 255) ” 
  &&  “ (0 <= choice) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (q_pend_abort_output_address error_addr perr ) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (tasks_waiting = (q_del_waiting (acquired) (initial))) ” 
  &&  “ (q_del_safe environment critical sg caller mask pe eid choice before X ) ” 
  &&  “ (q_del_schedule_protocol environment critical sg caller mask pe eid choice before ) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ” 
  &&  “ (0 <> choice) ” 
  &&  “ (1 <> choice) ”
  &&  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) (q_del_waiting (acquired) (initial)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
  **  ((perr) # UChar  |->_)
.

Definition OSQDel_partial_solve_wit_28 := OSQDel_partial_solve_wit_28_pure -> OSQDel_partial_solve_wit_28_aux.

Definition OSQDel_which_implies_wit_1 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (q_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (q_post_call_input critical sg caller pe before eid observed )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (q_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (q_post_call_input critical sg caller pe before eid observed )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (valid_event_id sg eid ) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ”
  &&  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
).

Definition OSQDel_which_implies_wit_1_split_goal_1 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (q_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (q_post_call_input critical sg caller pe before eid observed )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (valid_event_id sg eid ) ”
.

Definition OSQDel_which_implies_wit_1_split_goal_2 := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (q_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (q_post_call_input critical sg caller pe before eid observed )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ”
.

Definition OSQDel_which_implies_wit_1_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe <> 0)) (PreH2 : (q_post_profile sg )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (q_post_call_input critical sg caller pe before eid observed )) ,
  (q_post_closed environment critical saved_local sg caller mask before )
|--
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
.

Definition OSQDel_which_implies_wit_2 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (q_post_call_input critical sg caller pe before eid observed ) ” 
  &&  “ ((event_slot_type_value ((EventState (before))) (eid)) = 2) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_del_int_nesting (before)))
  **  (q_del_interrupt_context environment saved_local sg caller mask before )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_del_int_nesting (before)))
  **  (q_del_interrupt_context environment saved_local sg caller mask before )
).

Definition OSQDel_which_implies_wit_2_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> (event_slot_type_value ((EventState (before))) (eid)))
  **  (q_post_type_context environment saved_local sg caller mask before eid )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_del_int_nesting (before)))
  **  (q_del_interrupt_context environment saved_local sg caller mask before )
.

Definition OSQDel_which_implies_wit_3 := 
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : ((q_del_int_nesting (before)) <= 0)) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_del_int_nesting (before)))
  **  (q_del_interrupt_context environment saved_local sg caller mask before )
|--
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (valid_event_id sg eid ) ” 
  &&  “ (q_post_profile sg ) ” 
  &&  “ ((q_del_int_nesting (before)) <= 0) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (q_post_save_pre environment critical saved_local sg caller mask before pe eid observed )
) \/
(
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : ((q_del_int_nesting (before)) <= 0)) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_del_int_nesting (before)))
  **  (q_del_interrupt_context environment saved_local sg caller mask before )
|--
  (q_post_save_pre environment critical saved_local sg caller mask before pe eid observed )
).

Definition OSQDel_which_implies_wit_3_split_goal_spatial := 
forall (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (valid_event_id sg eid )) (PreH4 : (q_post_profile sg )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (q_post_call_input critical sg caller pe before eid observed )) (PreH7 : ((event_slot_type_value ((EventState (before))) (eid)) = 2)) (PreH8 : ((q_del_int_nesting (before)) <= 0)) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (q_del_int_nesting (before)))
  **  (q_del_interrupt_context environment saved_local sg caller mask before )
|--
  (q_post_save_pre environment critical saved_local sg caller mask before pe eid observed )
.

Definition OSQDel_which_implies_wit_4 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (valid_event_id sg eid )) (PreH3 : (q_post_profile sg )) ,
  (q_post_save_result environment critical saved_local sg caller mask cpu_sr before eid observed )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_post_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (initial)))
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (pevent: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (valid_event_id sg eid )) (PreH3 : (q_post_profile sg )) ,
  (q_post_save_result environment critical saved_local sg caller mask cpu_sr before eid observed )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_post_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (initial)))
).

Definition OSQDel_which_implies_wit_5 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (initial_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_del_int_nesting (before)) <= 0)) (PreH3 : (tasks_waiting = (q_del_waiting (acquired_2) (initial_2)))) ,
  (q_post_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial acquired initial (@nil Z) tasks_waiting )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired) (initial)))
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (initial_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_del_int_nesting (before)) <= 0)) (PreH3 : (tasks_waiting = (q_del_waiting (acquired_2) (initial_2)))) ,
  (q_post_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState) ,
  “ ((q_post_group (acquired_2) (initial_2)) = (q_post_group (acquired) (initial))) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial acquired initial (@nil Z) tasks_waiting )
).

Definition OSQDel_which_implies_wit_6 := 
(
forall (choice: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (initial_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (choice = 0)) (PreH4 : (tasks_waiting <= 0)) ,
  (q_del_loop_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) tasks_waiting )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (q: QueueFields) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice = 0) ”
  &&  (q_del_pointer_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial acquired initial (@nil Z) tasks_waiting choice q )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
) \/
(
forall (choice: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (initial_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (choice = 0)) (PreH4 : (tasks_waiting <= 0)) ,
  (q_del_loop_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) tasks_waiting )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (q: QueueFields) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice = 0) ”
  &&  (q_del_pointer_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial acquired initial (@nil Z) tasks_waiting choice q )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
).

Definition OSQDel_which_implies_wit_7 := 
(
forall (choice: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (q_2: QueueFields) (initial_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) pq )) (PreH3 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH4 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_pointer_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) tasks_waiting choice q_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pq)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q)))) pq ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  (q_del_recycle_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial acquired initial (@nil Z) tasks_waiting choice q free slots )
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 2)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pq)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (q_del_event_count (initial)))
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (free)))
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (q_del_event_free_head (sg) (acquired)))
) \/
(
forall (choice: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (q_2: QueueFields) (initial_2: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) pq )) (PreH3 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH4 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_pointer_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 acquired_2 initial_2 (@nil Z) tasks_waiting choice q_2 )
|--
  EX (x: Z)  (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (free: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q)))) pq ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> x)
  **  (q_del_recycle_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial acquired initial (@nil Z) tasks_waiting choice q free slots )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 2)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (q_del_event_count (initial)))
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (free)))
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (q_del_event_free_head (sg) (acquired)))
).

Definition OSQDel_which_implies_wit_8 := 
(
forall (choice: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (slots: (@list (@option Z))) (free: (@list Z)) (q: QueueFields) (initial: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q)))) pq )) (PreH4 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH5 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_recycle_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial acquired_2 initial (@nil Z) tasks_waiting choice q free slots )
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (free)))
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> pq)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (q_del_event_free_head (sg) (acquired_2)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pe)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State)  (buffer: QDelBuffer) ,
  (q_del_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid choice before acquired released 0 0 0 buffer )
  **  (q_del_buffer_rep buffer )
) \/
(
forall (choice: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (slots: (@list (@option Z))) (free: (@list Z)) (q: QueueFields) (initial: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q)))) pq )) (PreH4 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH5 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_recycle_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial acquired_2 initial (@nil Z) tasks_waiting choice q free slots )
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (free)))
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> pq)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (q_del_event_free_head (sg) (acquired_2)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pe)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State)  (buffer: QDelBuffer) ,
  (q_del_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid choice before acquired released 0 0 0 buffer )
  **  (q_del_buffer_rep buffer )
).

Definition OSQDel_which_implies_wit_9 := 
(
forall (choice: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (buffer: QDelBuffer) ,
  (q_del_restore_post environment critical saved_local sg caller mask pe eid choice before 0 0 0 buffer )
  **  (q_del_buffer_rep buffer )
|--
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before 0 0 )
) \/
(
forall (choice: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (buffer: QDelBuffer) ,
  (q_del_restore_post environment critical saved_local sg caller mask pe eid choice before 0 0 0 buffer )
  **  (q_del_buffer_rep buffer )
|--
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before 0 0 )
).

Definition OSQDel_which_implies_wit_9_split_goal_spatial := 
forall (choice: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (buffer: QDelBuffer) ,
  (q_del_restore_post environment critical saved_local sg caller mask pe eid choice before 0 0 0 buffer )
  **  (q_del_buffer_rep buffer )
|--
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before 0 0 )
.

Definition OSQDel_which_implies_wit_10 := 
(
forall (choice: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (initial: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (choice = 0)) (PreH4 : (tasks_waiting <> 0)) ,
  (q_del_loop_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial acquired_2 initial (@nil Z) tasks_waiting )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State) ,
  (q_del_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid choice before acquired acquired pe 73 0 QDelNoBuffer )
  **  (q_del_buffer_rep QDelNoBuffer )
) \/
(
forall (choice: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (initial: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (choice = 0)) (PreH4 : (tasks_waiting <> 0)) ,
  (q_del_loop_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial acquired_2 initial (@nil Z) tasks_waiting )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State) ,
  (q_del_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid choice before acquired acquired pe 73 0 QDelNoBuffer )
  **  (q_del_buffer_rep QDelNoBuffer )
).

Definition OSQDel_which_implies_wit_11 := 
(
forall (choice: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (buffer: QDelBuffer) ,
  (q_del_restore_post environment critical saved_local sg caller mask pe eid choice before pe 73 0 buffer )
  **  (q_del_buffer_rep buffer )
|--
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before pe 73 )
) \/
(
forall (choice: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (buffer: QDelBuffer) ,
  (q_del_restore_post environment critical saved_local sg caller mask pe eid choice before pe 73 0 buffer )
  **  (q_del_buffer_rep buffer )
|--
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before pe 73 )
).

Definition OSQDel_which_implies_wit_11_split_goal_spatial := 
forall (choice: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (buffer: QDelBuffer) ,
  (q_del_restore_post environment critical saved_local sg caller mask pe eid choice before pe 73 0 buffer )
  **  (q_del_buffer_rep buffer )
|--
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before pe 73 )
.

Definition OSQDel_which_implies_wit_12 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (processed_2: (@list Z)) (node_2: OSEventAbstractState) (initial_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (state_2) (node_2)) <> 0)) ,
  (q_del_loop_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 state_2 node_2 processed_2 tasks_waiting )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state_2) (node_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState)  (processed: (@list Z))  (tid: Z)  (old: TaskAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_del_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed tasks_waiting tid old )
  **  (event_task_rdy_pre sg (TskState (state)) eid node tid old 4 2 (q_post_sched_group (state)) (q_post_sched_rows (state)) )
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (processed_2: (@list Z)) (node_2: OSEventAbstractState) (initial_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((q_post_group (state_2) (node_2)) <> 0)) ,
  (q_del_loop_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 state_2 node_2 processed_2 tasks_waiting )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state_2) (node_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState)  (processed: (@list Z))  (tid: Z)  (old: TaskAbstractState) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_del_loop_wake_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed tasks_waiting tid old )
  **  (event_task_rdy_pre sg (TskState (state)) eid node tid old 4 2 (q_post_sched_group (state)) (q_post_sched_rows (state)) )
).

Definition OSQDel_which_implies_wit_13 := 
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (priority: Z) (old: TaskAbstractState) (tid: Z) (processed: (@list Z)) (node: OSEventAbstractState) (initial_2: OSEventAbstractState) (state: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) ,
  (q_del_loop_wake_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 state node processed tasks_waiting tid old )
  **  (event_task_rdy_post sg (TskState (state)) eid node tid old 0 4 2 (q_post_sched_group (state)) (q_post_sched_rows (state)) priority )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (next: UCOS2_Verify_State)  (next_node: OSEventAbstractState)  (next_processed: (@list Z)) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial next next_node next_processed tasks_waiting )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (next) (next_node)))
) \/
(
forall (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (priority: Z) (old: TaskAbstractState) (tid: Z) (processed: (@list Z)) (node: OSEventAbstractState) (initial_2: OSEventAbstractState) (state: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pevent: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) ,
  (q_del_loop_wake_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 state node processed tasks_waiting tid old )
  **  (event_task_rdy_post sg (TskState (state)) eid node tid old 0 4 2 (q_post_sched_group (state)) (q_post_sched_rows (state)) priority )
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (next: UCOS2_Verify_State)  (next_node: OSEventAbstractState)  (next_processed: (@list Z)) ,
  “ (pevent = (event_addr (sg) (eid))) ”
  &&  (q_del_loop_group_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial next next_node next_processed tasks_waiting )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (next) (next_node)))
).

Definition OSQDel_which_implies_wit_14 := 
(
forall (choice: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (processed_2: (@list Z)) (node_2: OSEventAbstractState) (initial_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (choice = 1)) (PreH4 : ((q_post_group (state_2) (node_2)) = 0)) ,
  (q_del_loop_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 state_2 node_2 processed_2 tasks_waiting )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state_2) (node_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState)  (processed: (@list Z))  (q: QueueFields) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice = 1) ”
  &&  (q_del_pointer_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed tasks_waiting choice q )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
) \/
(
forall (choice: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (processed_2: (@list Z)) (node_2: OSEventAbstractState) (initial_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (choice = 1)) (PreH4 : ((q_post_group (state_2) (node_2)) = 0)) ,
  (q_del_loop_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 state_2 node_2 processed_2 tasks_waiting )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (state_2) (node_2)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState)  (processed: (@list Z))  (q: QueueFields) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (choice = 1) ”
  &&  (q_del_pointer_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed tasks_waiting choice q )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (qcb_addr (sg) ((qID (q)))))
).

Definition OSQDel_which_implies_wit_15 := 
(
forall (choice: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (q_2: QueueFields) (processed_2: (@list Z)) (node_2: OSEventAbstractState) (initial_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) pq )) (PreH3 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH4 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_pointer_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 state_2 node_2 processed_2 tasks_waiting choice q_2 )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pq)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState)  (processed: (@list Z))  (free: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q)))) pq ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  (q_del_recycle_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed tasks_waiting choice q free slots )
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |->_)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 2)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> pq)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (q_del_event_count (node)))
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (free)))
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (q_del_event_free_head (sg) (state)))
) \/
(
forall (choice: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (q_2: QueueFields) (processed_2: (@list Z)) (node_2: OSEventAbstractState) (initial_2: OSEventAbstractState) (state_2: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q_2)))) pq )) (PreH3 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH4 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_pointer_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial_2 state_2 node_2 processed_2 tasks_waiting choice q_2 )
|--
  EX (x: Z)  (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (initial: OSEventAbstractState)  (state: UCOS2_Verify_State)  (node: OSEventAbstractState)  (processed: (@list Z))  (free: (@list Z))  (slots: (@list (@option Z)))  (q: QueueFields) ,
  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (q_pend_abort_output_address (qcb_addr (sg) ((qID (q)))) pq ) ” 
  &&  “ (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg))) ” 
  &&  “ (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg))) ”
  &&  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> x)
  **  (q_del_recycle_context environment critical saved_local sg caller active mask cpu_sr before acquired eid observed initial state node processed tasks_waiting choice q free slots )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 2)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> (q_del_event_count (node)))
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> (queue_free_head (sg) (free)))
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (q_del_event_free_head (sg) (state)))
).

Definition OSQDel_which_implies_wit_16 := 
(
forall (choice: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (slots: (@list (@option Z))) (free: (@list Z)) (q: QueueFields) (processed: (@list Z)) (node: OSEventAbstractState) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q)))) pq )) (PreH4 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH5 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_recycle_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial state node processed tasks_waiting choice q free slots )
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (free)))
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> pq)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (q_del_event_free_head (sg) (state)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pe)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State)  (buffer: QDelBuffer) ,
  (q_del_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid choice before acquired released 0 0 tasks_waiting buffer )
  **  (q_del_buffer_rep buffer )
) \/
(
forall (choice: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (slots: (@list (@option Z))) (free: (@list Z)) (q: QueueFields) (processed: (@list Z)) (node: OSEventAbstractState) (initial: OSEventAbstractState) (state: UCOS2_Verify_State) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (pq: Z) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (q_pend_abort_output_address (qcb_addr (sg) ((qID (q)))) pq )) (PreH4 : (( &( "OSQFreeList" ) ) = (g_OSQFreeList (sg)))) (PreH5 : (( &( "OSEventFreeList" ) ) = (g_OSEventFreeList (sg)))) ,
  (q_del_recycle_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial state node processed tasks_waiting choice q free slots )
  **  ((&((pq)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (queue_free_head (sg) (free)))
  **  ((( &( "OSQFreeList" ) )) # Ptr  |-> pq)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (q_del_event_free_head (sg) (state)))
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pe)
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State)  (released: UCOS2_Verify_State)  (buffer: QDelBuffer) ,
  (q_del_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid choice before acquired released 0 0 tasks_waiting buffer )
  **  (q_del_buffer_rep buffer )
).

Definition OSQDel_which_implies_wit_17 := 
(
forall (choice: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (buffer_2: QDelBuffer) (tasks_waiting: Z) (PreH1 : (1 <= tasks_waiting)) (PreH2 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) ,
  (q_del_restore_post environment critical saved_local sg caller mask pe eid choice before 0 0 tasks_waiting buffer_2 )
  **  (q_del_buffer_rep buffer_2 )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State)  (buffer: QDelBuffer) ,
  “ (q_del_prefix_result environment critical sg caller mask pe eid choice before 0 0 1 returned restored buffer ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  (q_del_buffer_rep buffer )
) \/
(
forall (choice: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (buffer_2: QDelBuffer) (tasks_waiting: Z) (PreH1 : (1 <= tasks_waiting)) (PreH2 : (q_del_schedule_protocol environment critical sg caller mask pe eid choice before )) ,
  (q_del_restore_post environment critical saved_local sg caller mask pe eid choice before 0 0 tasks_waiting buffer_2 )
  **  (q_del_buffer_rep buffer_2 )
|--
  EX (returned: TaskResumeCaller)  (restored: UCOS2_Verify_State)  (buffer: QDelBuffer) ,
  “ (q_del_prefix_result environment critical sg caller mask pe eid choice before 0 0 1 returned restored buffer ) ”
  &&  (task_resume_sched_pre environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  (q_del_buffer_rep buffer )
).

Definition OSQDel_which_implies_wit_18 := 
(
forall (choice: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (buffer: QDelBuffer) (restored: UCOS2_Verify_State) (returned: TaskResumeCaller) (PreH1 : (q_del_prefix_result environment critical sg caller mask pe eid choice before 0 0 1 returned restored buffer )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  (q_del_buffer_rep buffer )
|--
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before 0 0 )
) \/
(
forall (choice: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (buffer: QDelBuffer) (restored: UCOS2_Verify_State) (returned: TaskResumeCaller) (PreH1 : (q_del_prefix_result environment critical sg caller mask pe eid choice before 0 0 1 returned restored buffer )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  (q_del_buffer_rep buffer )
|--
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before 0 0 )
).

Definition OSQDel_which_implies_wit_18_split_goal_spatial := 
forall (choice: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (buffer: QDelBuffer) (restored: UCOS2_Verify_State) (returned: TaskResumeCaller) (PreH1 : (q_del_prefix_result environment critical sg caller mask pe eid choice before 0 0 1 returned restored buffer )) ,
  (task_resume_sched_post environment critical saved_local sg returned mask restored )
  **  (q_post_extra_tables sg returned )
  **  (q_del_buffer_rep buffer )
|--
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before 0 0 )
.

Definition OSQDel_which_implies_wit_19 := 
(
forall (choice: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (tasks_waiting: Z) ,
  (q_del_after_schedule_context environment critical saved_local sg caller mask pe eid choice before tasks_waiting )
|--
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before 0 0 )
) \/
(
forall (choice: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (tasks_waiting: Z) ,
  (q_del_after_schedule_context environment critical saved_local sg caller mask pe eid choice before tasks_waiting )
|--
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before 0 0 )
).

Definition OSQDel_which_implies_wit_19_split_goal_spatial := 
forall (choice: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (tasks_waiting: Z) ,
  (q_del_after_schedule_context environment critical saved_local sg caller mask pe eid choice before tasks_waiting )
|--
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before 0 0 )
.

Definition OSQDel_which_implies_wit_20 := 
(
forall (choice: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (buffer: QDelBuffer) ,
  (q_del_restore_post environment critical saved_local sg caller mask pe eid choice before pe 7 0 buffer )
  **  (q_del_buffer_rep buffer )
|--
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before pe 7 )
) \/
(
forall (choice: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (buffer: QDelBuffer) ,
  (q_del_restore_post environment critical saved_local sg caller mask pe eid choice before pe 7 0 buffer )
  **  (q_del_buffer_rep buffer )
|--
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before pe 7 )
).

Definition OSQDel_which_implies_wit_20_split_goal_spatial := 
forall (choice: Z) (pe: Z) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (buffer: QDelBuffer) ,
  (q_del_restore_post environment critical saved_local sg caller mask pe eid choice before pe 7 0 buffer )
  **  (q_del_buffer_rep buffer )
|--
  (q_del_finish_context environment critical saved_local sg caller mask pe eid choice before pe 7 )
.

Definition OSQDel_which_implies_wit_21 := 
(
forall (choice: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (initial: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (choice <> 0)) (PreH4 : (choice <> 1)) (PreH5 : (0 <= choice)) (PreH6 : (choice <= 255)) ,
  (q_del_loop_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial acquired_2 initial (@nil Z) tasks_waiting )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State) ,
  (q_del_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid choice before acquired acquired pe 7 0 QDelNoBuffer )
  **  (q_del_buffer_rep QDelNoBuffer )
) \/
(
forall (choice: Z) (pe: Z) (observed: OSEventAbstractState) (eid: Z) (before: UCOS2_Verify_State) (mask: Z) (caller: TaskResumeCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (saved_local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (initial: OSEventAbstractState) (acquired_2: UCOS2_Verify_State) (active_2: TaskResumeCaller) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (pe = (event_addr (sg) (eid)))) (PreH2 : (pe <> 0)) (PreH3 : (choice <> 0)) (PreH4 : (choice <> 1)) (PreH5 : (0 <= choice)) (PreH6 : (choice <= 255)) ,
  (q_del_loop_group_context environment critical saved_local sg caller active_2 mask cpu_sr before acquired_2 eid observed initial acquired_2 initial (@nil Z) tasks_waiting )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (q_post_group (acquired_2) (initial)))
|--
  EX (active: TaskResumeCaller)  (acquired: UCOS2_Verify_State) ,
  (q_del_restore_pre environment critical saved_local sg caller active mask cpu_sr pe eid choice before acquired acquired pe 7 0 QDelNoBuffer )
  **  (q_del_buffer_rep QDelNoBuffer )
).

Module Type VC_Correct.


Axiom proof_of_OSQDel_safety_wit_1 : OSQDel_safety_wit_1.
Axiom proof_of_OSQDel_safety_wit_2 : OSQDel_safety_wit_2.
Axiom proof_of_OSQDel_safety_wit_3 : OSQDel_safety_wit_3.
Axiom proof_of_OSQDel_safety_wit_4 : OSQDel_safety_wit_4.
Axiom proof_of_OSQDel_safety_wit_5 : OSQDel_safety_wit_5.
Axiom proof_of_OSQDel_safety_wit_6 : OSQDel_safety_wit_6.
Axiom proof_of_OSQDel_safety_wit_7 : OSQDel_safety_wit_7.
Axiom proof_of_OSQDel_safety_wit_8 : OSQDel_safety_wit_8.
Axiom proof_of_OSQDel_safety_wit_9 : OSQDel_safety_wit_9.
Axiom proof_of_OSQDel_entail_wit_1 : OSQDel_entail_wit_1.
Axiom proof_of_OSQDel_entail_wit_2 : OSQDel_entail_wit_2.
Axiom proof_of_OSQDel_entail_wit_3_1 : OSQDel_entail_wit_3_1.
Axiom proof_of_OSQDel_entail_wit_3_2 : OSQDel_entail_wit_3_2.
Axiom proof_of_OSQDel_entail_wit_4 : OSQDel_entail_wit_4.
Axiom proof_of_OSQDel_entail_wit_5 : OSQDel_entail_wit_5.
Axiom proof_of_OSQDel_entail_wit_6 : OSQDel_entail_wit_6.
Axiom proof_of_OSQDel_entail_wit_7_1 : OSQDel_entail_wit_7_1.
Axiom proof_of_OSQDel_entail_wit_7_2 : OSQDel_entail_wit_7_2.
Axiom proof_of_OSQDel_entail_wit_8_1 : OSQDel_entail_wit_8_1.
Axiom proof_of_OSQDel_entail_wit_8_2 : OSQDel_entail_wit_8_2.
Axiom proof_of_OSQDel_entail_wit_8_3 : OSQDel_entail_wit_8_3.
Axiom proof_of_OSQDel_entail_wit_8_4 : OSQDel_entail_wit_8_4.
Axiom proof_of_OSQDel_return_wit_1 : OSQDel_return_wit_1.
Axiom proof_of_OSQDel_return_wit_2 : OSQDel_return_wit_2.
Axiom proof_of_OSQDel_return_wit_3 : OSQDel_return_wit_3.
Axiom proof_of_OSQDel_return_wit_4 : OSQDel_return_wit_4.
Axiom proof_of_OSQDel_partial_solve_wit_1_pure : OSQDel_partial_solve_wit_1_pure.
Axiom proof_of_OSQDel_partial_solve_wit_1 : OSQDel_partial_solve_wit_1.
Axiom proof_of_OSQDel_partial_solve_wit_2_pure : OSQDel_partial_solve_wit_2_pure.
Axiom proof_of_OSQDel_partial_solve_wit_2 : OSQDel_partial_solve_wit_2.
Axiom proof_of_OSQDel_partial_solve_wit_3_pure : OSQDel_partial_solve_wit_3_pure.
Axiom proof_of_OSQDel_partial_solve_wit_3 : OSQDel_partial_solve_wit_3.
Axiom proof_of_OSQDel_partial_solve_wit_4 : OSQDel_partial_solve_wit_4.
Axiom proof_of_OSQDel_partial_solve_wit_5_pure : OSQDel_partial_solve_wit_5_pure.
Axiom proof_of_OSQDel_partial_solve_wit_5 : OSQDel_partial_solve_wit_5.
Axiom proof_of_OSQDel_partial_solve_wit_6_pure : OSQDel_partial_solve_wit_6_pure.
Axiom proof_of_OSQDel_partial_solve_wit_6 : OSQDel_partial_solve_wit_6.
Axiom proof_of_OSQDel_partial_solve_wit_7_pure : OSQDel_partial_solve_wit_7_pure.
Axiom proof_of_OSQDel_partial_solve_wit_7 : OSQDel_partial_solve_wit_7.
Axiom proof_of_OSQDel_partial_solve_wit_8_pure : OSQDel_partial_solve_wit_8_pure.
Axiom proof_of_OSQDel_partial_solve_wit_8 : OSQDel_partial_solve_wit_8.
Axiom proof_of_OSQDel_partial_solve_wit_9_pure : OSQDel_partial_solve_wit_9_pure.
Axiom proof_of_OSQDel_partial_solve_wit_9 : OSQDel_partial_solve_wit_9.
Axiom proof_of_OSQDel_partial_solve_wit_10_pure : OSQDel_partial_solve_wit_10_pure.
Axiom proof_of_OSQDel_partial_solve_wit_10 : OSQDel_partial_solve_wit_10.
Axiom proof_of_OSQDel_partial_solve_wit_11 : OSQDel_partial_solve_wit_11.
Axiom proof_of_OSQDel_partial_solve_wit_12_pure : OSQDel_partial_solve_wit_12_pure.
Axiom proof_of_OSQDel_partial_solve_wit_12 : OSQDel_partial_solve_wit_12.
Axiom proof_of_OSQDel_partial_solve_wit_13_pure : OSQDel_partial_solve_wit_13_pure.
Axiom proof_of_OSQDel_partial_solve_wit_13 : OSQDel_partial_solve_wit_13.
Axiom proof_of_OSQDel_partial_solve_wit_14 : OSQDel_partial_solve_wit_14.
Axiom proof_of_OSQDel_partial_solve_wit_15_pure : OSQDel_partial_solve_wit_15_pure.
Axiom proof_of_OSQDel_partial_solve_wit_15 : OSQDel_partial_solve_wit_15.
Axiom proof_of_OSQDel_partial_solve_wit_16_pure : OSQDel_partial_solve_wit_16_pure.
Axiom proof_of_OSQDel_partial_solve_wit_16 : OSQDel_partial_solve_wit_16.
Axiom proof_of_OSQDel_partial_solve_wit_17_pure : OSQDel_partial_solve_wit_17_pure.
Axiom proof_of_OSQDel_partial_solve_wit_17 : OSQDel_partial_solve_wit_17.
Axiom proof_of_OSQDel_partial_solve_wit_18_pure : OSQDel_partial_solve_wit_18_pure.
Axiom proof_of_OSQDel_partial_solve_wit_18 : OSQDel_partial_solve_wit_18.
Axiom proof_of_OSQDel_partial_solve_wit_19_pure : OSQDel_partial_solve_wit_19_pure.
Axiom proof_of_OSQDel_partial_solve_wit_19 : OSQDel_partial_solve_wit_19.
Axiom proof_of_OSQDel_partial_solve_wit_20_pure : OSQDel_partial_solve_wit_20_pure.
Axiom proof_of_OSQDel_partial_solve_wit_20 : OSQDel_partial_solve_wit_20.
Axiom proof_of_OSQDel_partial_solve_wit_21_pure : OSQDel_partial_solve_wit_21_pure.
Axiom proof_of_OSQDel_partial_solve_wit_21 : OSQDel_partial_solve_wit_21.
Axiom proof_of_OSQDel_partial_solve_wit_22_pure : OSQDel_partial_solve_wit_22_pure.
Axiom proof_of_OSQDel_partial_solve_wit_22 : OSQDel_partial_solve_wit_22.
Axiom proof_of_OSQDel_partial_solve_wit_23_pure : OSQDel_partial_solve_wit_23_pure.
Axiom proof_of_OSQDel_partial_solve_wit_23 : OSQDel_partial_solve_wit_23.
Axiom proof_of_OSQDel_partial_solve_wit_24_pure : OSQDel_partial_solve_wit_24_pure.
Axiom proof_of_OSQDel_partial_solve_wit_24 : OSQDel_partial_solve_wit_24.
Axiom proof_of_OSQDel_partial_solve_wit_25 : OSQDel_partial_solve_wit_25.
Axiom proof_of_OSQDel_partial_solve_wit_26 : OSQDel_partial_solve_wit_26.
Axiom proof_of_OSQDel_partial_solve_wit_27_pure : OSQDel_partial_solve_wit_27_pure.
Axiom proof_of_OSQDel_partial_solve_wit_27 : OSQDel_partial_solve_wit_27.
Axiom proof_of_OSQDel_partial_solve_wit_28_pure : OSQDel_partial_solve_wit_28_pure.
Axiom proof_of_OSQDel_partial_solve_wit_28 : OSQDel_partial_solve_wit_28.
Axiom proof_of_OSQDel_which_implies_wit_1 : OSQDel_which_implies_wit_1.
Axiom proof_of_OSQDel_which_implies_wit_2 : OSQDel_which_implies_wit_2.
Axiom proof_of_OSQDel_which_implies_wit_3 : OSQDel_which_implies_wit_3.
Axiom proof_of_OSQDel_which_implies_wit_4 : OSQDel_which_implies_wit_4.
Axiom proof_of_OSQDel_which_implies_wit_5 : OSQDel_which_implies_wit_5.
Axiom proof_of_OSQDel_which_implies_wit_6 : OSQDel_which_implies_wit_6.
Axiom proof_of_OSQDel_which_implies_wit_7 : OSQDel_which_implies_wit_7.
Axiom proof_of_OSQDel_which_implies_wit_8 : OSQDel_which_implies_wit_8.
Axiom proof_of_OSQDel_which_implies_wit_9 : OSQDel_which_implies_wit_9.
Axiom proof_of_OSQDel_which_implies_wit_10 : OSQDel_which_implies_wit_10.
Axiom proof_of_OSQDel_which_implies_wit_11 : OSQDel_which_implies_wit_11.
Axiom proof_of_OSQDel_which_implies_wit_12 : OSQDel_which_implies_wit_12.
Axiom proof_of_OSQDel_which_implies_wit_13 : OSQDel_which_implies_wit_13.
Axiom proof_of_OSQDel_which_implies_wit_14 : OSQDel_which_implies_wit_14.
Axiom proof_of_OSQDel_which_implies_wit_15 : OSQDel_which_implies_wit_15.
Axiom proof_of_OSQDel_which_implies_wit_16 : OSQDel_which_implies_wit_16.
Axiom proof_of_OSQDel_which_implies_wit_17 : OSQDel_which_implies_wit_17.
Axiom proof_of_OSQDel_which_implies_wit_18 : OSQDel_which_implies_wit_18.
Axiom proof_of_OSQDel_which_implies_wit_19 : OSQDel_which_implies_wit_19.
Axiom proof_of_OSQDel_which_implies_wit_20 : OSQDel_which_implies_wit_20.
Axiom proof_of_OSQDel_which_implies_wit_21 : OSQDel_which_implies_wit_21.

End VC_Correct.
