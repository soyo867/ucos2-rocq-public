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
Require Import Ucos2Verify.VC.code.time.spec.time_dly_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSTimeDly -----*)

Definition OSTimeDly_safety_wit_1 := 
forall (ticks_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (retval: Z) (PreH1 : (ticks_pre > 0)) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : ((os_sched_locks (before)) <= 0)) (PreH4 : ((os_sched_ints (before)) <= 0)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (time_dly_entry_facts environment critical sg caller mask request before )) (PreH7 : (0 <= (os_sched_ints (before)))) (PreH8 : ((os_sched_ints (before)) <= 255)) (PreH9 : (0 <= (os_sched_locks (before)))) (PreH10 : ((os_sched_locks (before)) <= 255)) (PreH11 : (ticks_pre = request)) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (time_dly_safe environment critical sg caller mask request before X )) ,
  (task_suspend_save_history_post environment critical saved_local sg caller mask retval before )
  **  (frame )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "ticks" ) )) # UInt  |-> ticks_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeDly_safety_wit_2 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (cpu_sr: Z) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (time_dly_safe environment critical sg caller mask request before X )) (PreH3 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) ,
  (task_suspend_restore_history_post environment critical saved_local sg active cpu_sr (time_dly_state (acquired) (tid) (target) (request)) )
  **  ((( &( "ticks" ) )) # UInt  |-> request)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (frame )
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTimeDly_entail_wit_1 := 
(
forall (ticks_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (retval: Z) (PreH1 : (ticks_pre > 0)) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : ((os_sched_locks (before)) <= 0)) (PreH4 : ((os_sched_ints (before)) <= 0)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (time_dly_entry_facts environment critical sg caller mask request before )) (PreH7 : (0 <= (os_sched_ints (before)))) (PreH8 : ((os_sched_ints (before)) <= 255)) (PreH9 : (0 <= (os_sched_locks (before)))) (PreH10 : ((os_sched_locks (before)) <= 255)) (PreH11 : (ticks_pre = request)) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (time_dly_safe environment critical sg caller mask request before X )) ,
  (task_suspend_save_history_post environment critical saved_local sg caller mask retval before )
  **  (frame )
  **  ((( &( "ticks" ) )) # UInt  |-> ticks_pre)
|--
  EX (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State)  (target: TaskAbstractState)  (tid: Z)  (pointer: Z) ,
  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg caller mask request before X ) ” 
  &&  “ (time_dly_acquired_facts environment critical sg caller mask request before retval active acquired tid target ) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ”
  &&  ((( &( "ticks" ) )) # UInt  |-> request)
  **  (task_suspend_tokens environment critical saved_local sg active retval acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
) \/
(
forall (ticks_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (retval: Z) (PreH1 : (ticks_pre > 0)) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : ((os_sched_locks (before)) <= 0)) (PreH4 : ((os_sched_ints (before)) <= 0)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (time_dly_entry_facts environment critical sg caller mask request before )) (PreH7 : (0 <= (os_sched_ints (before)))) (PreH8 : ((os_sched_ints (before)) <= 255)) (PreH9 : (0 <= (os_sched_locks (before)))) (PreH10 : ((os_sched_locks (before)) <= 255)) (PreH11 : (ticks_pre = request)) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (time_dly_safe environment critical sg caller mask request before X )) ,
  (task_suspend_save_history_post environment critical saved_local sg caller mask retval before )
  **  (frame )
|--
  EX (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State)  (target: TaskAbstractState)  (tid: Z) ,
  “ (ticks_pre = request) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg caller mask request before X ) ” 
  &&  “ (time_dly_acquired_facts environment critical sg caller mask request before retval active acquired tid target ) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ”
  &&  (task_suspend_tokens environment critical saved_local sg active retval acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (task_slot_addr (sg) (tid)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
).

Definition OSTimeDly_entail_wit_2_1 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : (time_dly_target_facts sg acquired tid target )) (PreH4 : (pointer = (task_slot_addr (sg) (tid)))) (PreH5 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH6 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH7 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH8 : (time_dly_target_facts sg acquired tid target )) (PreH9 : (pointer = (task_slot_addr (sg) (tid)))) (PreH10 : (time_dly_target_facts sg acquired tid target )) (PreH11 : (pointer = (task_slot_addr (sg) (tid)))) (PreH12 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH13 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH14 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH16 : (time_dly_target_facts sg acquired tid target )) (PreH17 : (pointer = (task_slot_addr (sg) (tid)))) (PreH18 : (time_dly_target_facts sg acquired tid target )) (PreH19 : (pointer = (task_slot_addr (sg) (tid)))) (PreH20 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH21 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH22 : (pointer = (task_slot_addr (sg) (tid)))) (PreH23 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (time_dly_safe environment critical sg caller mask request before X )) (PreH25 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH26 : (time_dly_target_facts sg acquired tid target )) ,
  (task_public_storage sg (TskState (acquired)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land (os_sched_group (acquired)) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((curPrio (target)))))) (8))))
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) = (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg caller mask request before X ) ” 
  &&  “ (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target ) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ”
  &&  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_dly_updated_group (acquired) (target)))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (target)))) * sizeof(UCHAR)))) # UChar  |-> (time_dly_cleared_row (acquired) (target)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : (time_dly_target_facts sg acquired tid target )) (PreH4 : (pointer = (task_slot_addr (sg) (tid)))) (PreH5 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH6 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH7 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH8 : (time_dly_target_facts sg acquired tid target )) (PreH9 : (pointer = (task_slot_addr (sg) (tid)))) (PreH10 : (time_dly_target_facts sg acquired tid target )) (PreH11 : (pointer = (task_slot_addr (sg) (tid)))) (PreH12 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH13 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH14 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH16 : (time_dly_target_facts sg acquired tid target )) (PreH17 : (pointer = (task_slot_addr (sg) (tid)))) (PreH18 : (time_dly_target_facts sg acquired tid target )) (PreH19 : (pointer = (task_slot_addr (sg) (tid)))) (PreH20 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH21 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH22 : (pointer = (task_slot_addr (sg) (tid)))) (PreH23 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (time_dly_safe environment critical sg caller mask request before X )) (PreH25 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH26 : (time_dly_target_facts sg acquired tid target )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ ((Z.land (os_sched_group (acquired)) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((curPrio (target)))))) (8))) = (time_dly_updated_group (acquired) (target))) ” 
  &&  “ ((time_dly_cleared_row (acquired) (target)) = (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) ”
  &&  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
).

Definition OSTimeDly_entail_wit_2_1_split_goal_1 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : (time_dly_target_facts sg acquired tid target )) (PreH4 : (pointer = (task_slot_addr (sg) (tid)))) (PreH5 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH6 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH7 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH8 : (time_dly_target_facts sg acquired tid target )) (PreH9 : (pointer = (task_slot_addr (sg) (tid)))) (PreH10 : (time_dly_target_facts sg acquired tid target )) (PreH11 : (pointer = (task_slot_addr (sg) (tid)))) (PreH12 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH13 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH14 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH16 : (time_dly_target_facts sg acquired tid target )) (PreH17 : (pointer = (task_slot_addr (sg) (tid)))) (PreH18 : (time_dly_target_facts sg acquired tid target )) (PreH19 : (pointer = (task_slot_addr (sg) (tid)))) (PreH20 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH21 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH22 : (pointer = (task_slot_addr (sg) (tid)))) (PreH23 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (time_dly_safe environment critical sg caller mask request before X )) (PreH25 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH26 : (time_dly_target_facts sg acquired tid target )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ ((Z.land (os_sched_group (acquired)) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((curPrio (target)))))) (8))) = (time_dly_updated_group (acquired) (target))) ”
.

Definition OSTimeDly_entail_wit_2_1_split_goal_2 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : (time_dly_target_facts sg acquired tid target )) (PreH4 : (pointer = (task_slot_addr (sg) (tid)))) (PreH5 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH6 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH7 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH8 : (time_dly_target_facts sg acquired tid target )) (PreH9 : (pointer = (task_slot_addr (sg) (tid)))) (PreH10 : (time_dly_target_facts sg acquired tid target )) (PreH11 : (pointer = (task_slot_addr (sg) (tid)))) (PreH12 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH13 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH14 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH16 : (time_dly_target_facts sg acquired tid target )) (PreH17 : (pointer = (task_slot_addr (sg) (tid)))) (PreH18 : (time_dly_target_facts sg acquired tid target )) (PreH19 : (pointer = (task_slot_addr (sg) (tid)))) (PreH20 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH21 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH22 : (pointer = (task_slot_addr (sg) (tid)))) (PreH23 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (time_dly_safe environment critical sg caller mask request before X )) (PreH25 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH26 : (time_dly_target_facts sg acquired tid target )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ ((time_dly_cleared_row (acquired) (target)) = (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) ”
.

Definition OSTimeDly_entail_wit_2_1_split_goal_spatial := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : (time_dly_target_facts sg acquired tid target )) (PreH4 : (pointer = (task_slot_addr (sg) (tid)))) (PreH5 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH6 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH7 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH8 : (time_dly_target_facts sg acquired tid target )) (PreH9 : (pointer = (task_slot_addr (sg) (tid)))) (PreH10 : (time_dly_target_facts sg acquired tid target )) (PreH11 : (pointer = (task_slot_addr (sg) (tid)))) (PreH12 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH13 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH14 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH16 : (time_dly_target_facts sg acquired tid target )) (PreH17 : (pointer = (task_slot_addr (sg) (tid)))) (PreH18 : (time_dly_target_facts sg acquired tid target )) (PreH19 : (pointer = (task_slot_addr (sg) (tid)))) (PreH20 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH21 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH22 : (pointer = (task_slot_addr (sg) (tid)))) (PreH23 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH24 : (time_dly_safe environment critical sg caller mask request before X )) (PreH25 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH26 : (time_dly_target_facts sg acquired tid target )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
.

Definition OSTimeDly_entail_wit_2_2 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) <> 0)) (PreH2 : (time_dly_target_facts sg acquired tid target )) (PreH3 : (pointer = (task_slot_addr (sg) (tid)))) (PreH4 : (time_dly_target_facts sg acquired tid target )) (PreH5 : (pointer = (task_slot_addr (sg) (tid)))) (PreH6 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH8 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH10 : (time_dly_target_facts sg acquired tid target )) (PreH11 : (pointer = (task_slot_addr (sg) (tid)))) (PreH12 : (time_dly_target_facts sg acquired tid target )) (PreH13 : (pointer = (task_slot_addr (sg) (tid)))) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH16 : (pointer = (task_slot_addr (sg) (tid)))) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (time_dly_safe environment critical sg caller mask request before X )) (PreH19 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH20 : (time_dly_target_facts sg acquired tid target )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) = (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg caller mask request before X ) ” 
  &&  “ (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target ) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ”
  &&  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_dly_updated_group (acquired) (target)))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (target)))) * sizeof(UCHAR)))) # UChar  |-> (time_dly_cleared_row (acquired) (target)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) <> 0)) (PreH2 : (time_dly_target_facts sg acquired tid target )) (PreH3 : (pointer = (task_slot_addr (sg) (tid)))) (PreH4 : (time_dly_target_facts sg acquired tid target )) (PreH5 : (pointer = (task_slot_addr (sg) (tid)))) (PreH6 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH8 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH10 : (time_dly_target_facts sg acquired tid target )) (PreH11 : (pointer = (task_slot_addr (sg) (tid)))) (PreH12 : (time_dly_target_facts sg acquired tid target )) (PreH13 : (pointer = (task_slot_addr (sg) (tid)))) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH16 : (pointer = (task_slot_addr (sg) (tid)))) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (time_dly_safe environment critical sg caller mask request before X )) (PreH19 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH20 : (time_dly_target_facts sg acquired tid target )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ ((os_sched_group (acquired)) = (time_dly_updated_group (acquired) (target))) ” 
  &&  “ ((time_dly_cleared_row (acquired) (target)) = (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) ”
  &&  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
).

Definition OSTimeDly_entail_wit_2_2_split_goal_1 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) <> 0)) (PreH2 : (time_dly_target_facts sg acquired tid target )) (PreH3 : (pointer = (task_slot_addr (sg) (tid)))) (PreH4 : (time_dly_target_facts sg acquired tid target )) (PreH5 : (pointer = (task_slot_addr (sg) (tid)))) (PreH6 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH8 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH10 : (time_dly_target_facts sg acquired tid target )) (PreH11 : (pointer = (task_slot_addr (sg) (tid)))) (PreH12 : (time_dly_target_facts sg acquired tid target )) (PreH13 : (pointer = (task_slot_addr (sg) (tid)))) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH16 : (pointer = (task_slot_addr (sg) (tid)))) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (time_dly_safe environment critical sg caller mask request before X )) (PreH19 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH20 : (time_dly_target_facts sg acquired tid target )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ ((os_sched_group (acquired)) = (time_dly_updated_group (acquired) (target))) ”
.

Definition OSTimeDly_entail_wit_2_2_split_goal_2 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) <> 0)) (PreH2 : (time_dly_target_facts sg acquired tid target )) (PreH3 : (pointer = (task_slot_addr (sg) (tid)))) (PreH4 : (time_dly_target_facts sg acquired tid target )) (PreH5 : (pointer = (task_slot_addr (sg) (tid)))) (PreH6 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH8 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH10 : (time_dly_target_facts sg acquired tid target )) (PreH11 : (pointer = (task_slot_addr (sg) (tid)))) (PreH12 : (time_dly_target_facts sg acquired tid target )) (PreH13 : (pointer = (task_slot_addr (sg) (tid)))) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH16 : (pointer = (task_slot_addr (sg) (tid)))) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (time_dly_safe environment critical sg caller mask request before X )) (PreH19 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH20 : (time_dly_target_facts sg acquired tid target )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ ((time_dly_cleared_row (acquired) (target)) = (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) ”
.

Definition OSTimeDly_entail_wit_2_2_split_goal_spatial := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) <> 0)) (PreH2 : (time_dly_target_facts sg acquired tid target )) (PreH3 : (pointer = (task_slot_addr (sg) (tid)))) (PreH4 : (time_dly_target_facts sg acquired tid target )) (PreH5 : (pointer = (task_slot_addr (sg) (tid)))) (PreH6 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH8 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH10 : (time_dly_target_facts sg acquired tid target )) (PreH11 : (pointer = (task_slot_addr (sg) (tid)))) (PreH12 : (time_dly_target_facts sg acquired tid target )) (PreH13 : (pointer = (task_slot_addr (sg) (tid)))) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH16 : (pointer = (task_slot_addr (sg) (tid)))) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (time_dly_safe environment critical sg caller mask request before X )) (PreH19 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH20 : (time_dly_target_facts sg acquired tid target )) ,
  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
.

Definition OSTimeDly_entail_wit_3 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (y: Z) (cpu_sr: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : (pointer = (task_slot_addr (sg) (tid)))) (PreH4 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (time_dly_safe environment critical sg caller mask request before X )) (PreH7 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH8 : (time_dly_target_facts sg acquired tid target )) ,
  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> request)
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBDly)) )
  **  ((( &( "y" ) )) # UChar  |-> y)
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_dly_updated_group (acquired) (target)))
  **  (((( &( "OSRdyTbl" ) ) + (y * sizeof(UCHAR)))) # UChar  |-> (time_dly_cleared_row (acquired) (target)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) y 0 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg caller mask request before X ) ” 
  &&  “ (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target ) ”
  &&  (task_suspend_masked environment critical saved_local sg active cpu_sr acquired (time_dly_state (acquired) (tid) (target) (request)) )
  **  (frame )
  **  ((( &( "y" ) )) # UChar  |->_)
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (y: Z) (cpu_sr: Z) (PreH1 : (request <= UINT_MAX)) (PreH2 : (request >= 0)) (PreH3 : (time_dly_target_facts sg acquired tid target )) (PreH4 : (pointer = (task_slot_addr (sg) (tid)))) (PreH5 : (pointer = (task_slot_addr (sg) (tid)))) (PreH6 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH7 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_dly_safe environment critical sg caller mask request before X )) (PreH9 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH10 : (time_dly_target_facts sg acquired tid target )) ,
  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> request)
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBDly)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_dly_updated_group (acquired) (target)))
  **  (((( &( "OSRdyTbl" ) ) + (y * sizeof(UCHAR)))) # UChar  |-> (time_dly_cleared_row (acquired) (target)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) y 0 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  (task_suspend_masked environment critical saved_local sg active cpu_sr acquired (time_dly_state (acquired) (tid) (target) (request)) )
  **  (frame )
).

Definition OSTimeDly_entail_wit_3_split_goal_spatial := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (y: Z) (cpu_sr: Z) (PreH1 : (request <= UINT_MAX)) (PreH2 : (request >= 0)) (PreH3 : (time_dly_target_facts sg acquired tid target )) (PreH4 : (pointer = (task_slot_addr (sg) (tid)))) (PreH5 : (pointer = (task_slot_addr (sg) (tid)))) (PreH6 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH7 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (time_dly_safe environment critical sg caller mask request before X )) (PreH9 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH10 : (time_dly_target_facts sg acquired tid target )) ,
  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> request)
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBDly)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_dly_updated_group (acquired) (target)))
  **  (((( &( "OSRdyTbl" ) ) + (y * sizeof(UCHAR)))) # UChar  |-> (time_dly_cleared_row (acquired) (target)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) y 0 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  (task_suspend_masked environment critical saved_local sg active cpu_sr acquired (time_dly_state (acquired) (tid) (target) (request)) )
  **  (frame )
.

Definition OSTimeDly_entail_wit_4 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (cpu_sr: Z) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (time_dly_safe environment critical sg caller mask request before X )) (PreH3 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) ,
  (task_suspend_restore_history_post environment critical saved_local sg active cpu_sr (time_dly_state (acquired) (tid) (target) (request)) )
  **  (frame )
|--
  EX (checkpoint_call: TaskSuspendCaller)  (checkpoint: UCOS2_Verify_State) ,
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target ) ” 
  &&  “ (time_dly_prefix_step environment critical sg caller mask request before checkpoint_call checkpoint ) ” 
  &&  “ (time_dly_scheduler_source sg checkpoint_call checkpoint ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (time_dly_scheduler_safe environment critical sg checkpoint_call mask checkpoint X ) ”
  &&  (task_suspend_closed environment critical saved_local sg checkpoint_call mask checkpoint )
  **  (frame )
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (cpu_sr: Z) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (time_dly_safe environment critical sg caller mask request before X )) (PreH3 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) ,
  (task_suspend_restore_history_post environment critical saved_local sg active cpu_sr (time_dly_state (acquired) (tid) (target) (request)) )
  **  (frame )
|--
  EX (checkpoint_call: TaskSuspendCaller)  (checkpoint: UCOS2_Verify_State) ,
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target ) ” 
  &&  “ (time_dly_prefix_step environment critical sg caller mask request before checkpoint_call checkpoint ) ” 
  &&  “ (time_dly_scheduler_source sg checkpoint_call checkpoint ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (time_dly_scheduler_safe environment critical sg checkpoint_call mask checkpoint X ) ”
  &&  (task_suspend_closed environment critical saved_local sg checkpoint_call mask checkpoint )
  **  (frame )
).

Definition OSTimeDly_return_wit_1 := 
(
forall (ticks_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : ((os_sched_locks (before)) > 0)) (PreH2 : ((os_sched_ints (before)) <= 0)) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_entry_facts environment critical sg caller mask request before )) (PreH5 : (0 <= (os_sched_ints (before)))) (PreH6 : ((os_sched_ints (before)) <= 255)) (PreH7 : (0 <= (os_sched_locks (before)))) (PreH8 : ((os_sched_locks (before)) <= 255)) (PreH9 : (ticks_pre = request)) (PreH10 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (time_dly_safe environment critical sg caller mask request before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (before)))
  **  (time_dly_prefix_frame environment saved_local sg caller mask before )
  **  (frame )
|--
  (time_dly_call_post environment critical saved_local sg caller mask request before frame X )
) \/
(
forall (ticks_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : ((os_sched_locks (before)) > 0)) (PreH2 : ((os_sched_ints (before)) <= 0)) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_entry_facts environment critical sg caller mask request before )) (PreH5 : (0 <= (os_sched_ints (before)))) (PreH6 : ((os_sched_ints (before)) <= 255)) (PreH7 : (0 <= (os_sched_locks (before)))) (PreH8 : ((os_sched_locks (before)) <= 255)) (PreH9 : (ticks_pre = request)) (PreH10 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (time_dly_safe environment critical sg caller mask request before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (before)))
  **  (time_dly_prefix_frame environment saved_local sg caller mask before )
  **  (frame )
|--
  (time_dly_call_post environment critical saved_local sg caller mask request before frame X )
).

Definition OSTimeDly_return_wit_1_split_goal_spatial := 
forall (ticks_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : ((os_sched_locks (before)) > 0)) (PreH2 : ((os_sched_ints (before)) <= 0)) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_entry_facts environment critical sg caller mask request before )) (PreH5 : (0 <= (os_sched_ints (before)))) (PreH6 : ((os_sched_ints (before)) <= 255)) (PreH7 : (0 <= (os_sched_locks (before)))) (PreH8 : ((os_sched_locks (before)) <= 255)) (PreH9 : (ticks_pre = request)) (PreH10 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (time_dly_safe environment critical sg caller mask request before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (before)))
  **  (time_dly_prefix_frame environment saved_local sg caller mask before )
  **  (frame )
|--
  (time_dly_call_post environment critical saved_local sg caller mask request before frame X )
.

Definition OSTimeDly_return_wit_2 := 
(
forall (ticks_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : ((os_sched_ints (before)) > 0)) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (time_dly_entry_facts environment critical sg caller mask request before )) (PreH4 : (0 <= (os_sched_ints (before)))) (PreH5 : ((os_sched_ints (before)) <= 255)) (PreH6 : (0 <= (os_sched_locks (before)))) (PreH7 : ((os_sched_locks (before)) <= 255)) (PreH8 : (ticks_pre = request)) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (time_dly_safe environment critical sg caller mask request before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (before)))
  **  (time_dly_prefix_frame environment saved_local sg caller mask before )
  **  (frame )
|--
  (time_dly_call_post environment critical saved_local sg caller mask request before frame X )
) \/
(
forall (ticks_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : ((os_sched_ints (before)) > 0)) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (time_dly_entry_facts environment critical sg caller mask request before )) (PreH4 : (0 <= (os_sched_ints (before)))) (PreH5 : ((os_sched_ints (before)) <= 255)) (PreH6 : (0 <= (os_sched_locks (before)))) (PreH7 : ((os_sched_locks (before)) <= 255)) (PreH8 : (ticks_pre = request)) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (time_dly_safe environment critical sg caller mask request before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (before)))
  **  (time_dly_prefix_frame environment saved_local sg caller mask before )
  **  (frame )
|--
  (time_dly_call_post environment critical saved_local sg caller mask request before frame X )
).

Definition OSTimeDly_return_wit_2_split_goal_spatial := 
forall (ticks_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : ((os_sched_ints (before)) > 0)) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (time_dly_entry_facts environment critical sg caller mask request before )) (PreH4 : (0 <= (os_sched_ints (before)))) (PreH5 : ((os_sched_ints (before)) <= 255)) (PreH6 : (0 <= (os_sched_locks (before)))) (PreH7 : ((os_sched_locks (before)) <= 255)) (PreH8 : (ticks_pre = request)) (PreH9 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (time_dly_safe environment critical sg caller mask request before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (before)))
  **  (time_dly_prefix_frame environment saved_local sg caller mask before )
  **  (frame )
|--
  (time_dly_call_post environment critical saved_local sg caller mask request before frame X )
.

Definition OSTimeDly_return_wit_3 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (cpu_sr: Z) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH4 : (time_dly_prefix_step environment critical sg caller mask request before checkpoint_call checkpoint )) (PreH5 : (time_dly_scheduler_source sg checkpoint_call checkpoint )) (PreH6 : (kernel_sched_ready_clients critical )) (PreH7 : (time_dly_scheduler_safe environment critical sg checkpoint_call mask checkpoint X )) ,
  (time_dly_scheduler_post environment critical saved_local sg checkpoint_call mask checkpoint X )
  **  (frame )
|--
  (time_dly_call_post environment critical saved_local sg caller mask request before frame X )
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (cpu_sr: Z) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH4 : (time_dly_prefix_step environment critical sg caller mask request before checkpoint_call checkpoint )) (PreH5 : (time_dly_scheduler_source sg checkpoint_call checkpoint )) (PreH6 : (kernel_sched_ready_clients critical )) (PreH7 : (time_dly_scheduler_safe environment critical sg checkpoint_call mask checkpoint X )) ,
  (time_dly_scheduler_post environment critical saved_local sg checkpoint_call mask checkpoint X )
  **  (frame )
|--
  (time_dly_call_post environment critical saved_local sg caller mask request before frame X )
).

Definition OSTimeDly_return_wit_3_split_goal_spatial := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (cpu_sr: Z) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH4 : (time_dly_prefix_step environment critical sg caller mask request before checkpoint_call checkpoint )) (PreH5 : (time_dly_scheduler_source sg checkpoint_call checkpoint )) (PreH6 : (kernel_sched_ready_clients critical )) (PreH7 : (time_dly_scheduler_safe environment critical sg checkpoint_call mask checkpoint X )) ,
  (time_dly_scheduler_post environment critical saved_local sg checkpoint_call mask checkpoint X )
  **  (frame )
|--
  (time_dly_call_post environment critical saved_local sg caller mask request before frame X )
.

Definition OSTimeDly_return_wit_4 := 
(
forall (ticks_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : (ticks_pre <= 0)) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : ((os_sched_locks (before)) <= 0)) (PreH4 : ((os_sched_ints (before)) <= 0)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (time_dly_entry_facts environment critical sg caller mask request before )) (PreH7 : (0 <= (os_sched_ints (before)))) (PreH8 : ((os_sched_ints (before)) <= 255)) (PreH9 : (0 <= (os_sched_locks (before)))) (PreH10 : ((os_sched_locks (before)) <= 255)) (PreH11 : (ticks_pre = request)) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (time_dly_safe environment critical sg caller mask request before X )) ,
  (task_suspend_closed environment critical saved_local sg caller mask before )
  **  (frame )
|--
  (time_dly_call_post environment critical saved_local sg caller mask request before frame X )
) \/
(
forall (ticks_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : (ticks_pre <= 0)) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : ((os_sched_locks (before)) <= 0)) (PreH4 : ((os_sched_ints (before)) <= 0)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (time_dly_entry_facts environment critical sg caller mask request before )) (PreH7 : (0 <= (os_sched_ints (before)))) (PreH8 : ((os_sched_ints (before)) <= 255)) (PreH9 : (0 <= (os_sched_locks (before)))) (PreH10 : ((os_sched_locks (before)) <= 255)) (PreH11 : (ticks_pre = request)) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (time_dly_safe environment critical sg caller mask request before X )) ,
  (task_suspend_closed environment critical saved_local sg caller mask before )
  **  (frame )
|--
  (time_dly_call_post environment critical saved_local sg caller mask request before frame X )
).

Definition OSTimeDly_return_wit_4_split_goal_spatial := 
forall (ticks_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : (ticks_pre <= 0)) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : ((os_sched_locks (before)) <= 0)) (PreH4 : ((os_sched_ints (before)) <= 0)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (time_dly_entry_facts environment critical sg caller mask request before )) (PreH7 : (0 <= (os_sched_ints (before)))) (PreH8 : ((os_sched_ints (before)) <= 255)) (PreH9 : (0 <= (os_sched_locks (before)))) (PreH10 : ((os_sched_locks (before)) <= 255)) (PreH11 : (ticks_pre = request)) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (time_dly_safe environment critical sg caller mask request before X )) ,
  (task_suspend_closed environment critical saved_local sg caller mask before )
  **  (frame )
|--
  (time_dly_call_post environment critical saved_local sg caller mask request before frame X )
.

Definition OSTimeDly_partial_solve_wit_1_pure := 
forall (ticks_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : (ticks_pre = request)) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (time_dly_safe environment critical sg caller mask request before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "ticks" ) )) # UInt  |-> ticks_pre)
  **  (time_dly_call_pre environment critical saved_local sg caller mask request before frame )
|--
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTimeDly_partial_solve_wit_1_aux := 
forall (ticks_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : (ticks_pre = request)) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (time_dly_safe environment critical sg caller mask request before X )) ,
  (time_dly_call_pre environment critical saved_local sg caller mask request before frame )
|--
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (ticks_pre = request) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg caller mask request before X ) ”
  &&  (time_dly_call_pre environment critical saved_local sg caller mask request before frame )
.

Definition OSTimeDly_partial_solve_wit_1 := OSTimeDly_partial_solve_wit_1_pure -> OSTimeDly_partial_solve_wit_1_aux.

Definition OSTimeDly_partial_solve_wit_2_pure := 
forall (ticks_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : ((os_sched_locks (before)) <= 0)) (PreH2 : ((os_sched_ints (before)) <= 0)) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_entry_facts environment critical sg caller mask request before )) (PreH5 : (0 <= (os_sched_ints (before)))) (PreH6 : ((os_sched_ints (before)) <= 255)) (PreH7 : (0 <= (os_sched_locks (before)))) (PreH8 : ((os_sched_locks (before)) <= 255)) (PreH9 : (ticks_pre = request)) (PreH10 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (time_dly_safe environment critical sg caller mask request before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (before)))
  **  (time_dly_prefix_frame environment saved_local sg caller mask before )
  **  (frame )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "ticks" ) )) # UInt  |-> ticks_pre)
|--
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTimeDly_partial_solve_wit_2_aux := 
forall (ticks_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : ((os_sched_locks (before)) <= 0)) (PreH2 : ((os_sched_ints (before)) <= 0)) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_entry_facts environment critical sg caller mask request before )) (PreH5 : (0 <= (os_sched_ints (before)))) (PreH6 : ((os_sched_ints (before)) <= 255)) (PreH7 : (0 <= (os_sched_locks (before)))) (PreH8 : ((os_sched_locks (before)) <= 255)) (PreH9 : (ticks_pre = request)) (PreH10 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (time_dly_safe environment critical sg caller mask request before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (before)))
  **  (time_dly_prefix_frame environment saved_local sg caller mask before )
  **  (frame )
|--
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((os_sched_locks (before)) <= 0) ” 
  &&  “ ((os_sched_ints (before)) <= 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_entry_facts environment critical sg caller mask request before ) ” 
  &&  “ (0 <= (os_sched_ints (before))) ” 
  &&  “ ((os_sched_ints (before)) <= 255) ” 
  &&  “ (0 <= (os_sched_locks (before))) ” 
  &&  “ ((os_sched_locks (before)) <= 255) ” 
  &&  “ (ticks_pre = request) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg caller mask request before X ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (before)))
  **  (time_dly_prefix_frame environment saved_local sg caller mask before )
  **  (frame )
.

Definition OSTimeDly_partial_solve_wit_2 := OSTimeDly_partial_solve_wit_2_pure -> OSTimeDly_partial_solve_wit_2_aux.

Definition OSTimeDly_partial_solve_wit_3 := 
forall (ticks_pre: Z) (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (PreH1 : (ticks_pre > 0)) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : ((os_sched_locks (before)) <= 0)) (PreH4 : ((os_sched_ints (before)) <= 0)) (PreH5 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (time_dly_entry_facts environment critical sg caller mask request before )) (PreH7 : (0 <= (os_sched_ints (before)))) (PreH8 : ((os_sched_ints (before)) <= 255)) (PreH9 : (0 <= (os_sched_locks (before)))) (PreH10 : ((os_sched_locks (before)) <= 255)) (PreH11 : (ticks_pre = request)) (PreH12 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (time_dly_safe environment critical sg caller mask request before X )) ,
  (task_suspend_closed environment critical saved_local sg caller mask before )
  **  (frame )
|--
  “ (ticks_pre > 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((os_sched_locks (before)) <= 0) ” 
  &&  “ ((os_sched_ints (before)) <= 0) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_entry_facts environment critical sg caller mask request before ) ” 
  &&  “ (0 <= (os_sched_ints (before))) ” 
  &&  “ ((os_sched_ints (before)) <= 255) ” 
  &&  “ (0 <= (os_sched_locks (before))) ” 
  &&  “ ((os_sched_locks (before)) <= 255) ” 
  &&  “ (ticks_pre = request) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg caller mask request before X ) ”
  &&  (task_suspend_closed environment critical saved_local sg caller mask before )
  **  (frame )
.

Definition OSTimeDly_partial_solve_wit_4_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (pointer = (task_slot_addr (sg) (tid)))) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (time_dly_safe environment critical sg caller mask request before X )) (PreH4 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH5 : (time_dly_target_facts sg acquired tid target )) ,
  ((( &( "ticks" ) )) # UInt  |-> request)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ”
.

Definition OSTimeDly_partial_solve_wit_4_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (pointer = (task_slot_addr (sg) (tid)))) (PreH2 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (time_dly_safe environment critical sg caller mask request before X )) (PreH4 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH5 : (time_dly_target_facts sg acquired tid target )) ,
  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg caller mask request before X ) ” 
  &&  “ (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target ) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ”
  &&  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
.

Definition OSTimeDly_partial_solve_wit_4 := OSTimeDly_partial_solve_wit_4_pure -> OSTimeDly_partial_solve_wit_4_aux.

Definition OSTimeDly_partial_solve_wit_5_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH5 : (pointer = (task_slot_addr (sg) (tid)))) (PreH6 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (time_dly_safe environment critical sg caller mask request before X )) (PreH8 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH9 : (time_dly_target_facts sg acquired tid target )) ,
  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBY)) )
  **  ((( &( "ticks" ) )) # UInt  |-> request)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ”
.

Definition OSTimeDly_partial_solve_wit_5_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH5 : (pointer = (task_slot_addr (sg) (tid)))) (PreH6 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (time_dly_safe environment critical sg caller mask request before X )) (PreH8 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH9 : (time_dly_target_facts sg acquired tid target )) ,
  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBY)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg caller mask request before X ) ” 
  &&  “ (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target ) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ”
  &&  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBY)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
.

Definition OSTimeDly_partial_solve_wit_5 := OSTimeDly_partial_solve_wit_5_pure -> OSTimeDly_partial_solve_wit_5_aux.

Definition OSTimeDly_partial_solve_wit_6_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : (time_dly_target_facts sg acquired tid target )) (PreH4 : (pointer = (task_slot_addr (sg) (tid)))) (PreH5 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH6 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH7 : (pointer = (task_slot_addr (sg) (tid)))) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (time_dly_safe environment critical sg caller mask request before X )) (PreH10 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH11 : (time_dly_target_facts sg acquired tid target )) ,
  (task_public_storage sg (TskState (acquired)) )
  **  ((( &( "ticks" ) )) # UInt  |-> request)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) = (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ”
.

Definition OSTimeDly_partial_solve_wit_6_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : (time_dly_target_facts sg acquired tid target )) (PreH4 : (pointer = (task_slot_addr (sg) (tid)))) (PreH5 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH6 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH7 : (pointer = (task_slot_addr (sg) (tid)))) (PreH8 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (time_dly_safe environment critical sg caller mask request before X )) (PreH10 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH11 : (time_dly_target_facts sg acquired tid target )) ,
  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) = (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg caller mask request before X ) ” 
  &&  “ (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target ) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ”
  &&  (task_public_storage sg (TskState (acquired)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
.

Definition OSTimeDly_partial_solve_wit_6 := OSTimeDly_partial_solve_wit_6_pure -> OSTimeDly_partial_solve_wit_6_aux.

Definition OSTimeDly_partial_solve_wit_7 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : ((tcb_y_of_prio ((curPrio (target)))) = (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH8 : (time_dly_target_facts sg acquired tid target )) (PreH9 : (pointer = (task_slot_addr (sg) (tid)))) (PreH10 : (time_dly_target_facts sg acquired tid target )) (PreH11 : (pointer = (task_slot_addr (sg) (tid)))) (PreH12 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH13 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH14 : (pointer = (task_slot_addr (sg) (tid)))) (PreH15 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH16 : (time_dly_safe environment critical sg caller mask request before X )) (PreH17 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH18 : (time_dly_target_facts sg acquired tid target )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) )
  **  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg caller mask request before X ) ” 
  &&  “ (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target ) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (target)))) * sizeof(UCHAR)))) # UChar  |-> (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) )
  **  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
.

Definition OSTimeDly_partial_solve_wit_8 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH5 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH6 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH7 : (time_dly_target_facts sg acquired tid target )) (PreH8 : (pointer = (task_slot_addr (sg) (tid)))) (PreH9 : (time_dly_target_facts sg acquired tid target )) (PreH10 : (pointer = (task_slot_addr (sg) (tid)))) (PreH11 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH12 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH13 : (pointer = (task_slot_addr (sg) (tid)))) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (time_dly_safe environment critical sg caller mask request before X )) (PreH16 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH17 : (time_dly_target_facts sg acquired tid target )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) )
  **  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg caller mask request before X ) ” 
  &&  “ (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target ) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (target)))) * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) )
  **  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
.

Definition OSTimeDly_partial_solve_wit_9_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH5 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH6 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH7 : (time_dly_target_facts sg acquired tid target )) (PreH8 : (pointer = (task_slot_addr (sg) (tid)))) (PreH9 : (time_dly_target_facts sg acquired tid target )) (PreH10 : (pointer = (task_slot_addr (sg) (tid)))) (PreH11 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH12 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH13 : (pointer = (task_slot_addr (sg) (tid)))) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (time_dly_safe environment critical sg caller mask request before X )) (PreH16 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH17 : (time_dly_target_facts sg acquired tid target )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  ((( &( "ticks" ) )) # UInt  |-> request)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ”
.

Definition OSTimeDly_partial_solve_wit_9_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH5 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH6 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH7 : (time_dly_target_facts sg acquired tid target )) (PreH8 : (pointer = (task_slot_addr (sg) (tid)))) (PreH9 : (time_dly_target_facts sg acquired tid target )) (PreH10 : (pointer = (task_slot_addr (sg) (tid)))) (PreH11 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH12 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH13 : (pointer = (task_slot_addr (sg) (tid)))) (PreH14 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH15 : (time_dly_safe environment critical sg caller mask request before X )) (PreH16 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH17 : (time_dly_target_facts sg acquired tid target )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg caller mask request before X ) ” 
  &&  “ (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target ) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ”
  &&  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
.

Definition OSTimeDly_partial_solve_wit_9 := OSTimeDly_partial_solve_wit_9_pure -> OSTimeDly_partial_solve_wit_9_aux.

Definition OSTimeDly_partial_solve_wit_10 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : (time_dly_target_facts sg acquired tid target )) (PreH4 : (pointer = (task_slot_addr (sg) (tid)))) (PreH5 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH6 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH7 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH8 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH9 : (time_dly_target_facts sg acquired tid target )) (PreH10 : (pointer = (task_slot_addr (sg) (tid)))) (PreH11 : (time_dly_target_facts sg acquired tid target )) (PreH12 : (pointer = (task_slot_addr (sg) (tid)))) (PreH13 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH14 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH15 : (pointer = (task_slot_addr (sg) (tid)))) (PreH16 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (time_dly_safe environment critical sg caller mask request before X )) (PreH18 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH19 : (time_dly_target_facts sg acquired tid target )) ,
  (task_public_storage sg (TskState (acquired)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg caller mask request before X ) ” 
  &&  “ (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target ) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (target)))) * sizeof(UCHAR)))) # UChar  |-> (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio ((curPrio (target)))) 0 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
.

Definition OSTimeDly_partial_solve_wit_11_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH2 : (time_dly_target_facts sg acquired tid target )) (PreH3 : (pointer = (task_slot_addr (sg) (tid)))) (PreH4 : (time_dly_target_facts sg acquired tid target )) (PreH5 : (pointer = (task_slot_addr (sg) (tid)))) (PreH6 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH8 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH10 : (time_dly_target_facts sg acquired tid target )) (PreH11 : (pointer = (task_slot_addr (sg) (tid)))) (PreH12 : (time_dly_target_facts sg acquired tid target )) (PreH13 : (pointer = (task_slot_addr (sg) (tid)))) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH16 : (pointer = (task_slot_addr (sg) (tid)))) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (time_dly_safe environment critical sg caller mask request before X )) (PreH19 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH20 : (time_dly_target_facts sg acquired tid target )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  ((( &( "ticks" ) )) # UInt  |-> request)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ”
.

Definition OSTimeDly_partial_solve_wit_11_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH2 : (time_dly_target_facts sg acquired tid target )) (PreH3 : (pointer = (task_slot_addr (sg) (tid)))) (PreH4 : (time_dly_target_facts sg acquired tid target )) (PreH5 : (pointer = (task_slot_addr (sg) (tid)))) (PreH6 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH7 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH8 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH9 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH10 : (time_dly_target_facts sg acquired tid target )) (PreH11 : (pointer = (task_slot_addr (sg) (tid)))) (PreH12 : (time_dly_target_facts sg acquired tid target )) (PreH13 : (pointer = (task_slot_addr (sg) (tid)))) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH16 : (pointer = (task_slot_addr (sg) (tid)))) (PreH17 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH18 : (time_dly_safe environment critical sg caller mask request before X )) (PreH19 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH20 : (time_dly_target_facts sg acquired tid target )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg caller mask request before X ) ” 
  &&  “ (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target ) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ”
  &&  (task_public_storage sg (TskState (acquired)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (os_sched_group (acquired)))
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
.

Definition OSTimeDly_partial_solve_wit_11 := OSTimeDly_partial_solve_wit_11_pure -> OSTimeDly_partial_solve_wit_11_aux.

Definition OSTimeDly_partial_solve_wit_12_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH5 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH6 : (time_dly_target_facts sg acquired tid target )) (PreH7 : (pointer = (task_slot_addr (sg) (tid)))) (PreH8 : (time_dly_target_facts sg acquired tid target )) (PreH9 : (pointer = (task_slot_addr (sg) (tid)))) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH13 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH14 : (time_dly_target_facts sg acquired tid target )) (PreH15 : (pointer = (task_slot_addr (sg) (tid)))) (PreH16 : (time_dly_target_facts sg acquired tid target )) (PreH17 : (pointer = (task_slot_addr (sg) (tid)))) (PreH18 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH19 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH20 : (pointer = (task_slot_addr (sg) (tid)))) (PreH21 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (time_dly_safe environment critical sg caller mask request before X )) (PreH23 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH24 : (time_dly_target_facts sg acquired tid target )) ,
  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitY)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  ((( &( "ticks" ) )) # UInt  |-> request)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land (os_sched_group (acquired)) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((curPrio (target)))))) (8))))
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ”
.

Definition OSTimeDly_partial_solve_wit_12_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (cpu_sr: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : (0 <= (tcb_bit_y_of_prio ((curPrio (target)))))) (PreH4 : ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255)) (PreH5 : ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0)) (PreH6 : (time_dly_target_facts sg acquired tid target )) (PreH7 : (pointer = (task_slot_addr (sg) (tid)))) (PreH8 : (time_dly_target_facts sg acquired tid target )) (PreH9 : (pointer = (task_slot_addr (sg) (tid)))) (PreH10 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH11 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH12 : (0 <= (tcb_bit_x_of_prio ((curPrio (target)))))) (PreH13 : ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255)) (PreH14 : (time_dly_target_facts sg acquired tid target )) (PreH15 : (pointer = (task_slot_addr (sg) (tid)))) (PreH16 : (time_dly_target_facts sg acquired tid target )) (PreH17 : (pointer = (task_slot_addr (sg) (tid)))) (PreH18 : (0 <= (tcb_y_of_prio ((curPrio (target)))))) (PreH19 : ((tcb_y_of_prio ((curPrio (target)))) < 8)) (PreH20 : (pointer = (task_slot_addr (sg) (tid)))) (PreH21 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (time_dly_safe environment critical sg caller mask request before X )) (PreH23 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH24 : (time_dly_target_facts sg acquired tid target )) ,
  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitY)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land (os_sched_group (acquired)) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((curPrio (target)))))) (8))))
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ ((unsigned_last_nbits ((Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) 0)) (32)) = 0) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg caller mask request before X ) ” 
  &&  “ (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target ) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ”
  &&  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitY)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Z.land (Znth (tcb_y_of_prio ((curPrio (target)))) (replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))) 0) (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((curPrio (target)))))) (8)))) ((replace_Znth ((tcb_y_of_prio ((curPrio (target))))) ((Znth ((tcb_y_of_prio ((curPrio (target))))) ((os_sched_rows (acquired))) (0))) ((os_sched_rows (acquired)))))) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land (os_sched_group (acquired)) (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((curPrio (target)))))) (8))))
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
.

Definition OSTimeDly_partial_solve_wit_12 := OSTimeDly_partial_solve_wit_12_pure -> OSTimeDly_partial_solve_wit_12_aux.

Definition OSTimeDly_partial_solve_wit_13_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (y: Z) (cpu_sr: Z) (PreH1 : (pointer = (task_slot_addr (sg) (tid)))) (PreH2 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_safe environment critical sg caller mask request before X )) (PreH5 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH6 : (time_dly_target_facts sg acquired tid target )) ,
  ((( &( "ticks" ) )) # UInt  |-> request)
  **  ((( &( "y" ) )) # UChar  |-> y)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_dly_updated_group (acquired) (target)))
  **  (((( &( "OSRdyTbl" ) ) + (y * sizeof(UCHAR)))) # UChar  |-> (time_dly_cleared_row (acquired) (target)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) y 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ”
.

Definition OSTimeDly_partial_solve_wit_13_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (y: Z) (cpu_sr: Z) (PreH1 : (pointer = (task_slot_addr (sg) (tid)))) (PreH2 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH3 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (time_dly_safe environment critical sg caller mask request before X )) (PreH5 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH6 : (time_dly_target_facts sg acquired tid target )) ,
  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_dly_updated_group (acquired) (target)))
  **  (((( &( "OSRdyTbl" ) ) + (y * sizeof(UCHAR)))) # UChar  |-> (time_dly_cleared_row (acquired) (target)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) y 0 8 (os_sched_rows (acquired)) )
  **  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (y = (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg caller mask request before X ) ” 
  &&  “ (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target ) ” 
  &&  “ (time_dly_target_facts sg acquired tid target ) ”
  &&  (task_public_storage sg (TskState (acquired)) )
  **  (task_suspend_tokens environment critical saved_local sg active cpu_sr acquired acquired )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> pointer)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (time_dly_updated_group (acquired) (target)))
  **  (((( &( "OSRdyTbl" ) ) + (y * sizeof(UCHAR)))) # UChar  |-> (time_dly_cleared_row (acquired) (target)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) y 0 8 (os_sched_rows (acquired)) )
  **  (task_suspend_work_frame sg acquired )
  **  (frame )
.

Definition OSTimeDly_partial_solve_wit_13 := OSTimeDly_partial_solve_wit_13_pure -> OSTimeDly_partial_solve_wit_13_aux.

Definition OSTimeDly_partial_solve_wit_14_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (cpu_sr: Z) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (time_dly_safe environment critical sg caller mask request before X )) (PreH3 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) ,
  ((( &( "ticks" ) )) # UInt  |-> request)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_masked environment critical saved_local sg active cpu_sr acquired (time_dly_state (acquired) (tid) (target) (request)) )
  **  (frame )
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSTimeDly_partial_solve_wit_14_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (cpu_sr: Z) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (time_dly_safe environment critical sg caller mask request before X )) (PreH3 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) ,
  (task_suspend_masked environment critical saved_local sg active cpu_sr acquired (time_dly_state (acquired) (tid) (target) (request)) )
  **  (frame )
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_safe environment critical sg caller mask request before X ) ” 
  &&  “ (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target ) ”
  &&  (task_suspend_masked environment critical saved_local sg active cpu_sr acquired (time_dly_state (acquired) (tid) (target) (request)) )
  **  (frame )
.

Definition OSTimeDly_partial_solve_wit_14 := OSTimeDly_partial_solve_wit_14_pure -> OSTimeDly_partial_solve_wit_14_aux.

Definition OSTimeDly_partial_solve_wit_15_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (cpu_sr: Z) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH3 : (time_dly_prefix_step environment critical sg caller mask request before checkpoint_call checkpoint )) (PreH4 : (time_dly_scheduler_source sg checkpoint_call checkpoint )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (time_dly_scheduler_safe environment critical sg checkpoint_call mask checkpoint X )) ,
  ((( &( "ticks" ) )) # UInt  |-> request)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (task_suspend_closed environment critical saved_local sg checkpoint_call mask checkpoint )
  **  (frame )
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (time_dly_scheduler_source sg checkpoint_call checkpoint ) ”
.

Definition OSTimeDly_partial_solve_wit_15_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (cpu_sr: Z) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH3 : (time_dly_prefix_step environment critical sg caller mask request before checkpoint_call checkpoint )) (PreH4 : (time_dly_scheduler_source sg checkpoint_call checkpoint )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (time_dly_scheduler_safe environment critical sg checkpoint_call mask checkpoint X )) ,
  (task_suspend_closed environment critical saved_local sg checkpoint_call mask checkpoint )
  **  (frame )
|--
  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (time_dly_scheduler_source sg checkpoint_call checkpoint ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target ) ” 
  &&  “ (time_dly_prefix_step environment critical sg caller mask request before checkpoint_call checkpoint ) ” 
  &&  “ (time_dly_scheduler_source sg checkpoint_call checkpoint ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (time_dly_scheduler_safe environment critical sg checkpoint_call mask checkpoint X ) ”
  &&  (task_suspend_closed environment critical saved_local sg checkpoint_call mask checkpoint )
  **  (frame )
.

Definition OSTimeDly_partial_solve_wit_15 := OSTimeDly_partial_solve_wit_15_pure -> OSTimeDly_partial_solve_wit_15_aux.

Definition OSTimeDly_partial_solve_wit_16_pure := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (cpu_sr: Z) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH3 : (time_dly_prefix_step environment critical sg caller mask request before checkpoint_call checkpoint )) (PreH4 : (time_dly_scheduler_source sg checkpoint_call checkpoint )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (time_dly_scheduler_safe environment critical sg checkpoint_call mask checkpoint X )) ,
  (task_suspend_scheduler_pre environment critical saved_local sg checkpoint_call mask checkpoint )
  **  ((( &( "ticks" ) )) # UInt  |-> request)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (frame )
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_scheduler_safe environment critical sg checkpoint_call mask checkpoint X ) ”
.

Definition OSTimeDly_partial_solve_wit_16_aux := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (X: (unit -> (UCOS2_Verify_State -> Prop))) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (cpu_sr: Z) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target )) (PreH3 : (time_dly_prefix_step environment critical sg caller mask request before checkpoint_call checkpoint )) (PreH4 : (time_dly_scheduler_source sg checkpoint_call checkpoint )) (PreH5 : (kernel_sched_ready_clients critical )) (PreH6 : (time_dly_scheduler_safe environment critical sg checkpoint_call mask checkpoint X )) ,
  (task_suspend_scheduler_pre environment critical saved_local sg checkpoint_call mask checkpoint )
  **  (frame )
|--
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_scheduler_safe environment critical sg checkpoint_call mask checkpoint X ) ” 
  &&  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_acquired_facts environment critical sg caller mask request before cpu_sr active acquired tid target ) ” 
  &&  “ (time_dly_prefix_step environment critical sg caller mask request before checkpoint_call checkpoint ) ” 
  &&  “ (time_dly_scheduler_source sg checkpoint_call checkpoint ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (time_dly_scheduler_safe environment critical sg checkpoint_call mask checkpoint X ) ”
  &&  (task_suspend_scheduler_pre environment critical saved_local sg checkpoint_call mask checkpoint )
  **  (frame )
.

Definition OSTimeDly_partial_solve_wit_16 := OSTimeDly_partial_solve_wit_16_pure -> OSTimeDly_partial_solve_wit_16_aux.

Definition OSTimeDly_which_implies_wit_1 := 
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_dly_call_pre environment critical saved_local sg caller mask request before frame )
|--
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (time_dly_entry_facts environment critical sg caller mask request before ) ” 
  &&  “ (0 <= (os_sched_ints (before))) ” 
  &&  “ ((os_sched_ints (before)) <= 255) ” 
  &&  “ (0 <= (os_sched_locks (before))) ” 
  &&  “ ((os_sched_locks (before)) <= 255) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (before)))
  **  (time_dly_prefix_frame environment saved_local sg caller mask before )
  **  (frame )
) \/
(
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_dly_call_pre environment critical saved_local sg caller mask request before frame )
|--
  “ ((os_sched_locks (before)) <= 255) ” 
  &&  “ (0 <= (os_sched_locks (before))) ” 
  &&  “ ((os_sched_ints (before)) <= 255) ” 
  &&  “ (0 <= (os_sched_ints (before))) ” 
  &&  “ (time_dly_entry_facts environment critical sg caller mask request before ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (before)))
  **  (time_dly_prefix_frame environment saved_local sg caller mask before )
  **  (frame )
).

Definition OSTimeDly_which_implies_wit_1_split_goal_1 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_dly_call_pre environment critical saved_local sg caller mask request before frame )
|--
  “ ((os_sched_locks (before)) <= 255) ”
.

Definition OSTimeDly_which_implies_wit_1_split_goal_2 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_dly_call_pre environment critical saved_local sg caller mask request before frame )
|--
  “ (0 <= (os_sched_locks (before))) ”
.

Definition OSTimeDly_which_implies_wit_1_split_goal_3 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_dly_call_pre environment critical saved_local sg caller mask request before frame )
|--
  “ ((os_sched_ints (before)) <= 255) ”
.

Definition OSTimeDly_which_implies_wit_1_split_goal_4 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_dly_call_pre environment critical saved_local sg caller mask request before frame )
|--
  “ (0 <= (os_sched_ints (before))) ”
.

Definition OSTimeDly_which_implies_wit_1_split_goal_5 := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_dly_call_pre environment critical saved_local sg caller mask request before frame )
|--
  “ (time_dly_entry_facts environment critical sg caller mask request before ) ”
.

Definition OSTimeDly_which_implies_wit_1_split_goal_spatial := 
forall (frame: Assertion) (before: UCOS2_Verify_State) (request: Z) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (time_dly_call_pre environment critical saved_local sg caller mask request before frame )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (before)))
  **  (time_dly_prefix_frame environment saved_local sg caller mask before )
  **  (frame )
.

Definition OSTimeDly_which_implies_wit_2 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (before)))
  **  (time_dly_prefix_frame environment saved_local sg caller mask before )
|--
  “ (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (task_suspend_closed environment critical saved_local sg caller mask before )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (before)))
  **  (time_dly_prefix_frame environment saved_local sg caller mask before )
|--
  (task_suspend_closed environment critical saved_local sg caller mask before )
).

Definition OSTimeDly_which_implies_wit_2_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (task_suspend_addresses sg ( &( "OSTCBCur" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> (os_sched_locks (before)))
  **  (time_dly_prefix_frame environment saved_local sg caller mask before )
|--
  (task_suspend_closed environment critical saved_local sg caller mask before )
.

Definition OSTimeDly_which_implies_wit_3 := 
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ”
  &&  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBY)) )
) \/
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ”
  &&  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBY)) )
).

Definition OSTimeDly_which_implies_wit_3_split_goal_1 := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ ((tcb_y_of_prio ((curPrio (target)))) < 8) ”
.

Definition OSTimeDly_which_implies_wit_3_split_goal_2 := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ (0 <= (tcb_y_of_prio ((curPrio (target))))) ”
.

Definition OSTimeDly_which_implies_wit_3_split_goal_spatial := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBY)) )
.

Definition OSTimeDly_which_implies_wit_4 := 
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBY)) )
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ”
  &&  (task_public_storage sg (TskState (acquired)) )
) \/
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBY)) )
|--
  (task_public_storage sg (TskState (acquired)) )
).

Definition OSTimeDly_which_implies_wit_4_split_goal_spatial := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBY)) )
|--
  (task_public_storage sg (TskState (acquired)) )
.

Definition OSTimeDly_which_implies_wit_5 := 
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (y: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : (0 <= y)) (PreH5 : (y < 8)) ,
  (task_public_storage sg (TskState (acquired)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (os_sched_rows (acquired)) )
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (y = (tcb_y_of_prio ((curPrio (target))))) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ”
  &&  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
  **  (((( &( "OSRdyTbl" ) ) + (y * sizeof(UCHAR)))) # UChar  |-> (Znth (y) ((os_sched_rows (acquired))) (0)))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) y 0 8 (os_sched_rows (acquired)) )
) \/
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (y: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : (0 <= y)) (PreH5 : (y < 8)) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ”
  &&  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
).

Definition OSTimeDly_which_implies_wit_5_split_goal_1 := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (y: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : (0 <= y)) (PreH5 : (y < 8)) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ ((tcb_bit_x_of_prio ((curPrio (target)))) <= 255) ”
.

Definition OSTimeDly_which_implies_wit_5_split_goal_2 := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (y: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : (0 <= y)) (PreH5 : (y < 8)) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ (0 <= (tcb_bit_x_of_prio ((curPrio (target))))) ”
.

Definition OSTimeDly_which_implies_wit_5_split_goal_spatial := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (y: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) (PreH3 : (y = (tcb_y_of_prio ((curPrio (target)))))) (PreH4 : (0 <= y)) (PreH5 : (y < 8)) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
.

Definition OSTimeDly_which_implies_wit_6 := 
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ”
  &&  (task_public_storage sg (TskState (acquired)) )
) \/
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
|--
  (task_public_storage sg (TskState (acquired)) )
).

Definition OSTimeDly_which_implies_wit_6_split_goal_spatial := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitX)) )
|--
  (task_public_storage sg (TskState (acquired)) )
.

Definition OSTimeDly_which_implies_wit_7 := 
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((curPrio (target))))) ” 
  &&  “ ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255) ”
  &&  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitY)) )
) \/
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((curPrio (target))))) ”
  &&  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitY)) )
).

Definition OSTimeDly_which_implies_wit_7_split_goal_1 := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ ((tcb_bit_y_of_prio ((curPrio (target)))) <= 255) ”
.

Definition OSTimeDly_which_implies_wit_7_split_goal_2 := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ (0 <= (tcb_bit_y_of_prio ((curPrio (target))))) ”
.

Definition OSTimeDly_which_implies_wit_7_split_goal_spatial := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitY)) )
.

Definition OSTimeDly_which_implies_wit_8 := 
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitY)) )
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ”
  &&  (task_public_storage sg (TskState (acquired)) )
) \/
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitY)) )
|--
  (task_public_storage sg (TskState (acquired)) )
).

Definition OSTimeDly_which_implies_wit_8_split_goal_spatial := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (target)))))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBBitY)) )
|--
  (task_public_storage sg (TskState (acquired)) )
.

Definition OSTimeDly_which_implies_wit_9 := 
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  “ (time_dly_target_facts sg acquired tid target ) ” 
  &&  “ (pointer = (task_slot_addr (sg) (tid))) ”
  &&  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (dly (target)))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBDly)) )
) \/
(
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (dly (target)))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBDly)) )
).

Definition OSTimeDly_which_implies_wit_9_split_goal_spatial := 
forall (sg: StableGlobVars) (acquired: UCOS2_Verify_State) (tid: Z) (target: TaskAbstractState) (pointer: Z) (PreH1 : (time_dly_target_facts sg acquired tid target )) (PreH2 : (pointer = (task_slot_addr (sg) (tid)))) ,
  (task_public_storage sg (TskState (acquired)) )
|--
  ((&((pointer)  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (dly (target)))
  **  (task_public_storage_without_field sg (TskState (acquired)) tid target (TCBCommonField (TCBDly)) )
.

Definition OSTimeDly_which_implies_wit_10 := 
(
forall (mask: Z) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : (kernel_sched_ready_clients critical )) (PreH2 : (time_dly_scheduler_source sg checkpoint_call checkpoint )) ,
  (task_suspend_closed environment critical saved_local sg checkpoint_call mask checkpoint )
|--
  (task_suspend_scheduler_pre environment critical saved_local sg checkpoint_call mask checkpoint )
) \/
(
forall (mask: Z) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : (kernel_sched_ready_clients critical )) (PreH2 : (time_dly_scheduler_source sg checkpoint_call checkpoint )) ,
  (task_suspend_closed environment critical saved_local sg checkpoint_call mask checkpoint )
|--
  (task_suspend_scheduler_pre environment critical saved_local sg checkpoint_call mask checkpoint )
).

Definition OSTimeDly_which_implies_wit_10_split_goal_spatial := 
forall (mask: Z) (sg: StableGlobVars) (saved_local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (checkpoint_call: TaskSuspendCaller) (checkpoint: UCOS2_Verify_State) (PreH1 : (kernel_sched_ready_clients critical )) (PreH2 : (time_dly_scheduler_source sg checkpoint_call checkpoint )) ,
  (task_suspend_closed environment critical saved_local sg checkpoint_call mask checkpoint )
|--
  (task_suspend_scheduler_pre environment critical saved_local sg checkpoint_call mask checkpoint )
.

Module Type VC_Correct.


Axiom proof_of_OSTimeDly_safety_wit_1 : OSTimeDly_safety_wit_1.
Axiom proof_of_OSTimeDly_safety_wit_2 : OSTimeDly_safety_wit_2.
Axiom proof_of_OSTimeDly_entail_wit_1 : OSTimeDly_entail_wit_1.
Axiom proof_of_OSTimeDly_entail_wit_2_1 : OSTimeDly_entail_wit_2_1.
Axiom proof_of_OSTimeDly_entail_wit_2_2 : OSTimeDly_entail_wit_2_2.
Axiom proof_of_OSTimeDly_entail_wit_3 : OSTimeDly_entail_wit_3.
Axiom proof_of_OSTimeDly_entail_wit_4 : OSTimeDly_entail_wit_4.
Axiom proof_of_OSTimeDly_return_wit_1 : OSTimeDly_return_wit_1.
Axiom proof_of_OSTimeDly_return_wit_2 : OSTimeDly_return_wit_2.
Axiom proof_of_OSTimeDly_return_wit_3 : OSTimeDly_return_wit_3.
Axiom proof_of_OSTimeDly_return_wit_4 : OSTimeDly_return_wit_4.
Axiom proof_of_OSTimeDly_partial_solve_wit_1_pure : OSTimeDly_partial_solve_wit_1_pure.
Axiom proof_of_OSTimeDly_partial_solve_wit_1 : OSTimeDly_partial_solve_wit_1.
Axiom proof_of_OSTimeDly_partial_solve_wit_2_pure : OSTimeDly_partial_solve_wit_2_pure.
Axiom proof_of_OSTimeDly_partial_solve_wit_2 : OSTimeDly_partial_solve_wit_2.
Axiom proof_of_OSTimeDly_partial_solve_wit_3 : OSTimeDly_partial_solve_wit_3.
Axiom proof_of_OSTimeDly_partial_solve_wit_4_pure : OSTimeDly_partial_solve_wit_4_pure.
Axiom proof_of_OSTimeDly_partial_solve_wit_4 : OSTimeDly_partial_solve_wit_4.
Axiom proof_of_OSTimeDly_partial_solve_wit_5_pure : OSTimeDly_partial_solve_wit_5_pure.
Axiom proof_of_OSTimeDly_partial_solve_wit_5 : OSTimeDly_partial_solve_wit_5.
Axiom proof_of_OSTimeDly_partial_solve_wit_6_pure : OSTimeDly_partial_solve_wit_6_pure.
Axiom proof_of_OSTimeDly_partial_solve_wit_6 : OSTimeDly_partial_solve_wit_6.
Axiom proof_of_OSTimeDly_partial_solve_wit_7 : OSTimeDly_partial_solve_wit_7.
Axiom proof_of_OSTimeDly_partial_solve_wit_8 : OSTimeDly_partial_solve_wit_8.
Axiom proof_of_OSTimeDly_partial_solve_wit_9_pure : OSTimeDly_partial_solve_wit_9_pure.
Axiom proof_of_OSTimeDly_partial_solve_wit_9 : OSTimeDly_partial_solve_wit_9.
Axiom proof_of_OSTimeDly_partial_solve_wit_10 : OSTimeDly_partial_solve_wit_10.
Axiom proof_of_OSTimeDly_partial_solve_wit_11_pure : OSTimeDly_partial_solve_wit_11_pure.
Axiom proof_of_OSTimeDly_partial_solve_wit_11 : OSTimeDly_partial_solve_wit_11.
Axiom proof_of_OSTimeDly_partial_solve_wit_12_pure : OSTimeDly_partial_solve_wit_12_pure.
Axiom proof_of_OSTimeDly_partial_solve_wit_12 : OSTimeDly_partial_solve_wit_12.
Axiom proof_of_OSTimeDly_partial_solve_wit_13_pure : OSTimeDly_partial_solve_wit_13_pure.
Axiom proof_of_OSTimeDly_partial_solve_wit_13 : OSTimeDly_partial_solve_wit_13.
Axiom proof_of_OSTimeDly_partial_solve_wit_14_pure : OSTimeDly_partial_solve_wit_14_pure.
Axiom proof_of_OSTimeDly_partial_solve_wit_14 : OSTimeDly_partial_solve_wit_14.
Axiom proof_of_OSTimeDly_partial_solve_wit_15_pure : OSTimeDly_partial_solve_wit_15_pure.
Axiom proof_of_OSTimeDly_partial_solve_wit_15 : OSTimeDly_partial_solve_wit_15.
Axiom proof_of_OSTimeDly_partial_solve_wit_16_pure : OSTimeDly_partial_solve_wit_16_pure.
Axiom proof_of_OSTimeDly_partial_solve_wit_16 : OSTimeDly_partial_solve_wit_16.
Axiom proof_of_OSTimeDly_which_implies_wit_1 : OSTimeDly_which_implies_wit_1.
Axiom proof_of_OSTimeDly_which_implies_wit_2 : OSTimeDly_which_implies_wit_2.
Axiom proof_of_OSTimeDly_which_implies_wit_3 : OSTimeDly_which_implies_wit_3.
Axiom proof_of_OSTimeDly_which_implies_wit_4 : OSTimeDly_which_implies_wit_4.
Axiom proof_of_OSTimeDly_which_implies_wit_5 : OSTimeDly_which_implies_wit_5.
Axiom proof_of_OSTimeDly_which_implies_wit_6 : OSTimeDly_which_implies_wit_6.
Axiom proof_of_OSTimeDly_which_implies_wit_7 : OSTimeDly_which_implies_wit_7.
Axiom proof_of_OSTimeDly_which_implies_wit_8 : OSTimeDly_which_implies_wit_8.
Axiom proof_of_OSTimeDly_which_implies_wit_9 : OSTimeDly_which_implies_wit_9.
Axiom proof_of_OSTimeDly_which_implies_wit_10 : OSTimeDly_which_implies_wit_10.

End VC_Correct.
